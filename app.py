from __future__ import annotations
import argparse
import logging
import os
import re
import shutil
import subprocess
import threading
import time
import sys
import webbrowser
from datetime import date
from pathlib import Path
from typing import Optional

import requests
from flask import Flask, Response, jsonify, render_template_string, request, send_file
from playwright.sync_api import Browser, Page, sync_playwright, TimeoutError as PWTimeout
from pypdf import PdfReader, PdfWriter

# ── PyInstaller Playwright Path Configuration ────────────────────────────────
# 指示程式在打包成 .exe 後，去邊度搵內置嘅 Chromium 瀏覽器
if getattr(sys, 'frozen', False):
    bundle_dir = sys._MEIPASS
    os.environ["PLAYWRIGHT_BROWSERS_PATH"] = os.path.join(bundle_dir, 'ms-playwright')
else:
    bundle_dir = os.path.dirname(os.path.abspath(__file__))

# ── Logging and Memory Buffer Setup ──────────────────────────────────────────
app_log_buffer: list[str] = []

class WebLogHandler(logging.Handler):
    def emit(self, record):
        try:
            log_message = self.format(record)
            app_log_buffer.append(log_message)
        except Exception:
            self.handleError(record)

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s", datefmt="%H:%M:%S")
log = logging.getLogger(__name__)
log.addHandler(WebLogHandler())

# ── Configuration ─────────────────────────────────────────────────────────────
BASE_URL = "https://www.smg.gov.mo"
SOURCES: list[dict] = [
    {"name": "news",            "url": f"{BASE_URL}/zh/news"},
    {"name": "activity",        "url": f"{BASE_URL}/zh/activity"},
    {"name": "holiday_weather", "url": f"{BASE_URL}/zh/news/Holiday_weather"},
    {"name": "chat_info",       "url": f"{BASE_URL}/zh/chat-info"},
    {"name": "seasonal",        "url": f"{BASE_URL}/zh/seasonal"},
    {"name": "climate",         "url": f"{BASE_URL}/zh/climate"},
]

NAV_TIMEOUT   = 60_000   # ms — page navigation
RENDER_WAIT   = 5_000    # ms — after navigation, wait for Vue to render data
MAX_PAGES     = 50       # safety cap on pagination depth

# ── Compression Config ─────────────────────────────────────────────────────
PDF_SIZE_LIMIT = 5 * 1024 * 1024   # 5 MB hard limit
_COMPRESS_ATTEMPTS = [
    ("ebook",  150),
    ("screen",  96),
    ("screen",  72),
]

# ── Regex Configuration (Date Parsing Fix) ──────────────────────────────────
DATE_RE = re.compile(
    r"(20\d{2})"                   # year
    r"[\s\-\/年\.]+"
    r"(1[0-2]|0?[1-9])"            # month — two-digit first
    r"[\s\-\/月\.]+"
    r"([12]\d|3[01]|0?[1-9])"      # day   — two-digit first
)
_JS_DATE_RE = r"(20\d{{2}})[\s\-/年.]+(1[0-2]|0?[1-9])[\s\-/月.]+([12]\d|3[01]|0?[1-9])"

ARTICLE_LINK_SELECTOR = "a[href*='-detail'], a[href*='chat-info/']"
PDF_LINK_SELECTORS = ["a[href$='.pdf']", "a[href*='.pdf?']", "a[href*='/pdf/']", "a[href*='download']", "a[href*='attach']", "a[href*='file']"]
NO_CONTENT_MARKERS = ["no related content", "nenhum conteúdo relacionado", "nenhum conteudo relacionado", "404", "not found", "page not found"]

# ── State Control Variables ─────────────────────────────────────────────────
scraper_running_status: bool = False
scraper_execution_result: dict = {"success": False, "filename": "", "message": "Idle"}

# ── Helper Utility Functions ────────────────────────────────────────────────
def get_target_month() -> tuple[int, int]:
    today = date.today()
    if today.month > 1: return today.year, today.month - 1
    return today.year - 1, 12

def sanitize_filename(name: str, max_len: int = 100) -> str:
    name = re.sub(r"\s+", " ", name).strip()
    return re.sub(r'[\\/*?:"<>|]', "", name)[:max_len] or "Untitled"

def switch_lang(url: str, target_lang: str) -> str:
    for lang in ["zh", "en", "pt"]:
        if f"/{lang}/" in url: return url.replace(f"/{lang}/", f"/{target_lang}/", 1)
    return url

def resolve_url(href: str) -> str:
    return href if href.startswith("http") else BASE_URL + href if href.startswith("/") else BASE_URL + "/" + href

# ── JavaScript Injections for Playwright ────────────────────────────────────
_EXTRACT_JS = """
() => {
    const DATE_RE = /(20\\d{2})[\\s\\-\\/年.]+(1[0-2]|0?[1-9])[\\s\\-\\/月.]+([12]\\d|3[01]|0?[1-9])/;
    const found = [];
    const seen  = new Set();

    function abs(href) {
        if (!href) return null;
        if (href.startsWith('http')) return href;
        if (href.startsWith('/'))   return '""" + BASE_URL + """' + href;
        return '""" + BASE_URL + """/' + href;
    }

    const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
    let node;
    while (node = walker.nextNode()) {
        const text  = node.nodeValue.trim();
        const match = text.match(DATE_RE);
        if (!match) continue;

        const dateStr = match[1] + '-' + match[2].padStart(2, '0') + '-' + match[3].padStart(2, '0');
        let container = node.parentElement;
        let links = [];
        for (let i = 0; i < 8; i++) {
            if (!container || container.tagName === 'BODY') break;
            links = Array.from(container.querySelectorAll('a[href]:not([href="#"]):not([href^="javascript"]), [data-url], [onclick]'));
            if (links.length > 0 && links.length <= 20) break;
            container = container.parentElement;
        }

        links.forEach(el => {
            let href = el.getAttribute('href') || el.getAttribute('data-url');
            if (!href) {
                const oc = el.getAttribute('onclick') || '';
                const m2 = oc.match(/['"](\\/[^'"]+)['"]/);
                if (m2) href = m2[1];
            }
            if (!href || /\\/page\\/\\d+/.test(href) || href.includes('?page=')) return;

            const url = abs(href);
            if (!url || seen.has(url)) return;
            seen.add(url);

            let title = (el.innerText || '').trim();
            if (title.length < 3 && container) title = (container.innerText || '').split('\\n')[0].trim();
            found.push({ url, date_str: dateStr, text: title.substring(0, 80) });
        });
    }

    if (found.length === 0 && window.location.href.includes('Holiday_weather')) {
        const m = document.body.innerText.match(DATE_RE);
        if (m) found.push({ url: window.location.href, date_str: m[1] + '-' + m[2].padStart(2,'0') + '-' + m[3].padStart(2,'0'), text: document.title });
    }
    return found;
}
"""

_MAX_PAGE_JS = """
() => {
    let max = 1;
    const pgSelectors = ['.pagination a', '.pagination button', '.pagination li a', '.page-list a', '.page-bar a', '[class*="pagin"] a', '[class*="pagin"] button', '[class*="page-num"]', '[class*="pageNum"]'];
    pgSelectors.forEach(sel => {
        document.querySelectorAll(sel).forEach(el => {
            const n = parseInt((el.innerText || el.textContent || '').trim(), 10);
            if (!isNaN(n) && n > max) max = n;
        });
    });
    const bodyText = document.body.innerText;
    const m = bodyText.match(/共\\s*(\\d+)\\s*頁/) || bodyText.match(/of\\s+(\\d+)\\s+page/i);
    if (m) max = Math.max(max, parseInt(m[1], 10));
    return max;
}
"""

_CLICK_PAGE_JS = """
(pageNum) => {
    const label = String(pageNum);
    const selectors = ['.pagination a', '.pagination button', '.pagination li a', '.pagination li button', '.page-list a', '.page-bar a', '[class*="pagin"] a', '[class*="pagin"] button', '[class*="page-num"]', '[class*="pageNum"]'];
    for (const sel of selectors) {
        for (const el of document.querySelectorAll(sel)) {
            if ((el.innerText || el.textContent || '').trim() === label) {
                el.click();
                return true;
            }
        }
    }
    return false;
}
"""

_ARTICLE_FINGERPRINT_JS = """
() => {
    const texts = [];
    document.querySelectorAll('a[href], [class*="title"], [class*="date"]').forEach(el => {
        const t = (el.innerText || '').trim();
        if (t.length > 5) texts.push(t);
        if (texts.length >= 10) return;
    });
    return texts.join('|');
}
"""

# ── Core Operations ─────────────────────────────────────────────────────────
def _wait_for_content_change(page: Page, old_fingerprint: str, timeout_ms: int = 10_000) -> bool:
    deadline = time.monotonic() + timeout_ms / 1000
    while time.monotonic() < deadline:
        try:
            new_fp = page.evaluate(_ARTICLE_FINGERPRINT_JS)
            if new_fp and new_fp != old_fingerprint: return True
        except Exception: pass
        time.sleep(0.3)
    return False

def navigate_and_wait(page: Page, url: str) -> bool:
    try:
        page.goto(url, wait_until="networkidle", timeout=NAV_TIMEOUT)
        page.wait_for_timeout(RENDER_WAIT)
        return True
    except Exception as e:
        log.warning(f"  Navigation failed ({url}): {e}")
        return False

def extract_page_articles(page: Page) -> list[dict]:
    try: return page.evaluate(_EXTRACT_JS) or []
    except Exception as e: log.warning(f"  DOM extraction failed: {e}"); return []

def collect_source(page: Page, src: dict, year: int, month: int) -> dict[str, dict]:
    all_items: dict[str, dict] = {}
    source_name = src["name"]
    base_url = src["url"].rstrip("/")

    log.info(f"  Loading: {base_url}")
    if not navigate_and_wait(page, base_url): return {}

    try: max_page = max(1, int(page.evaluate(_MAX_PAGE_JS)))
    except Exception: max_page = 1
    log.info(f"  Pagination: {max_page} page(s) detected")

    for page_num in range(1, min(max_page, MAX_PAGES) + 1):
        if page_num > 1:
            old_fp = page.evaluate(_ARTICLE_FINGERPRINT_JS)
            clicked = page.evaluate(_CLICK_PAGE_JS, page_num)
            if not clicked: log.warning(f"  Could not find page-{page_num} button — stopping"); break
            changed = _wait_for_content_change(page, old_fp, timeout_ms=12_000)
            if not changed: log.warning(f"  Content did not change after clicking page {page_num} — stopping"); break
            page.wait_for_load_state("networkidle", timeout=15_000)

        articles = extract_page_articles(page)
        if not articles: log.info(f"  Page {page_num}: no articles found — stopping"); break

        added = 0
        found_older = False
        for item in articles:
            ds = item.get("date_str", "")
            if len(ds) < 10: continue
            try: ly, lm = int(ds[:4]), int(ds[5:7])
            except ValueError: continue

            if (ly, lm) < (year, month): found_older = True
            elif (ly, lm) == (year, month):
                url = item["url"]
                if url not in all_items:
                    all_items[url] = {**item, "source": source_name}
                    added += 1

        log.info(f"  Page {page_num}/{max_page}: {len(articles)} articles, +{added} matched {year}-{month:02d}" + (" [older found → stop]" if found_older else ""))
        if found_older: break

    return all_items

def download_pdf_robust(url: str, dest: Path, page: Page) -> bool:
    try:
        with page.context.expect_download(timeout=45_000) as dl:
            page.evaluate(f"window.open('{url}', '_blank')")
        dl.value.save_as(dest)
        return dest.exists() and dest.stat().st_size > 2_000
    except Exception as e:
        log.warning(f"  PDF download failed ({url}): {e}")
        return False

def process_article(page: Page, item: dict, tmp_dir: Path, seq: int) -> Optional[Path]:
    safe = item["text"][:30].replace("/", "-")
    dest = tmp_dir / sanitize_filename(f"{seq:03d}_{item['date_str']}_{safe}.pdf")

    try:
        page.goto(item["url"], wait_until="networkidle", timeout=NAV_TIMEOUT)
        page.wait_for_timeout(2_000)

        pdf_links = page.evaluate("() => Array.from(document.querySelectorAll('a[href$=\".pdf\"],a[href*=\"download\"]')).map(a=>a.href)")
        if pdf_links and download_pdf_robust(pdf_links[0], dest, page): return dest

        page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
        page.wait_for_timeout(1_000)
        page.evaluate("""() => { ['header','nav','footer','#header','#footer','#nav','.site-header','.breadcrumb','.cookie-bar','.back-to-top','.navbar-top','.sticky-header'].forEach(s => document.querySelectorAll(s).forEach(el => el.remove())); }""")
        page.add_style_tag(content="@media print{body{-webkit-print-color-adjust:exact !important;print-color-adjust:exact !important}}")
        page.pdf(path=str(dest), format="A4", print_background=True)

        if dest.exists() and dest.stat().st_size > 2_000: return dest
        log.warning(f"  PDF too small, skipping: {dest.name}")
        return None
    except Exception as e:
        log.warning(f"  Failed processing {item['url']}: {e}")
        return None

def compress_pdf(input_path: Path, output_path: Path) -> bool:
    input_size = input_path.stat().st_size
    if input_size <= PDF_SIZE_LIMIT:
        log.info(f"  PDF is {input_size / 1_048_576:.2f} MB — already under limit, skipping compression")
        shutil.copy2(input_path, output_path)
        return True

    log.info(f"  PDF is {input_size / 1_048_576:.2f} MB — compressing…")
    for gs_setting, img_dpi in _COMPRESS_ATTEMPTS:
        cmd = [
            "gs", "-dBATCH", "-dNOPAUSE", "-dQUIET", "-sDEVICE=pdfwrite",
            "-dCompatibilityLevel=1.5", f"-dPDFSETTINGS=/{gs_setting}",
            "-dDownsampleColorImages=true", "-dDownsampleGrayImages=true", "-dDownsampleMonoImages=true",
            f"-dColorImageResolution={img_dpi}", f"-dGrayImageResolution={img_dpi}", f"-dMonoImageResolution={min(img_dpi * 2, 300)}",
            "-dCompressFonts=true", "-dEmbedAllFonts=true",
            f"-sOutputFile={output_path}", str(input_path)
        ]
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            if result.returncode != 0: log.warning(f"  gs /{gs_setting} failed: {result.stderr[:200]}"); continue
        except FileNotFoundError:
            log.warning("  Ghostscript (gs) not found — skipping compression")
            shutil.copy2(input_path, output_path)
            return False
        except subprocess.TimeoutExpired:
            log.warning(f"  gs /{gs_setting} timed out"); continue

        out_size = output_path.stat().st_size if output_path.exists() else 0
        log.info(f"  /{gs_setting} @{img_dpi}dpi → {out_size / 1_048_576:.2f} MB" + (" ✅" if out_size <= PDF_SIZE_LIMIT else " (still large)"))
        if out_size <= PDF_SIZE_LIMIT: return True

    if output_path.exists() and output_path.stat().st_size > 0: return False
    shutil.copy2(input_path, output_path)
    return False

# ── Main Execution Worker (Background Task) ─────────────────────────────────
def execute_scraping_worker(year: Optional[int], month: Optional[int]):
    global scraper_running_status, scraper_execution_result
    try:
        if not year or not month: year, month = get_target_month()
        log.info(f"🚀 SMG Monthly Scraper — Target: {year}-{month:02d}")
        
        current_dir = Path(os.getcwd())
        tmp_dir = current_dir / f"smg_tmp_{year}_{month:02d}"
        tmp_dir.mkdir(exist_ok=True)
        
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            ctx = browser.new_context(viewport={"width": 1920, "height": 1080}, accept_downloads=True)
            page, all_items = ctx.new_page(), {}
            
            for src in SOURCES:
                log.info(f"\n📋 Source: {src['name']}")
                items = collect_source(page, src, year, month)
                before = len(all_items)
                all_items.update(items)
                log.info(f"  ✔ {src['name']}: {len(items)} found, {len(all_items)-before} new unique")
                
            if not all_items:
                log.warning(f"❌ No articles found for {year}-{month:02d}. Exiting.")
                scraper_execution_result = {"success": False, "filename": "", "message": "No matching articles found."}
                browser.close()
                return

            sorted_items = sorted(all_items.values(), key=lambda x: x["date_str"])
            log.info(f"\n📦 Total unique articles to render: {len(sorted_items)}")
            
            writer = PdfWriter()
            for i, item in enumerate(sorted_items, 1):
                log.info(f"\n⚙  ({i}/{len(sorted_items)}) [{item['date_str']}] {item['text'][:50]}")
                pdf_path = process_article(page, item, tmp_dir, i)
                if pdf_path:
                    try: writer.append(str(pdf_path))
                    except Exception as e: log.warning(f"  Could not append {pdf_path.name}: {e}")

            raw_output = current_dir / f"SMG_Monthly_Report_{year}_{month:02d}_raw.pdf"
            with raw_output.open("wb") as fh: writer.write(fh)
            log.info(f"\n📄 Raw merged PDF: {raw_output.name}  ({raw_output.stat().st_size / 1_048_576:.2f} MB)")

            final_filename = f"SMG_Monthly_Report_{year}_{month:02d}.pdf"
            output = current_dir / final_filename
            log.info(f"🗜  Compressing → {output.name} (target ≤ 5 MB)…")
            compress_pdf(raw_output, output)
            log.info(f"\n✅ Done: {output.name}  ({output.stat().st_size / 1_048_576:.2f} MB)")

            raw_output.unlink(missing_ok=True)
            browser.close()
            
        scraper_execution_result = {"success": True, "filename": final_filename, "message": "Report generated successfully!"}
        
    except Exception as e:
        log.error(f"❌ Execution error: {e}")
        scraper_execution_result = {"success": False, "filename": "", "message": str(e)}
    finally:
        scraper_running_status = False

# ── Flask Web App & UI ──────────────────────────────────────────────────────
CONTROL_PANEL_UI_TEMPLATE = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8"><title>SMG Report Engine Portal</title>
    <style>
        body { font-family: sans-serif; background: #eef2f3; padding: 30px; }
        .container { max-width: 900px; margin: auto; background: #fff; padding: 25px; border-radius: 10px; box-shadow: 0 4px 15px rgba(0,0,0,0.05); }
        input, select, button { padding: 10px; margin-bottom: 15px; width: 100%; box-sizing: border-box; font-size: 14px; }
        button { background: #3498db; color: #fff; border: none; cursor: pointer; font-weight: bold; border-radius: 4px; transition: background 0.2s; }
        button:hover { background: #2980b9; }
        button:disabled { background: #95a5a6; cursor: not-allowed; }
        .console-box { background: #1e272e; color: #ced6e0; padding: 15px; height: 350px; overflow-y: scroll; font-family: monospace; white-space: pre-wrap; border-radius: 5px; }
        .status-banner { padding: 12px; background: #f1f2f6; font-weight: bold; margin-bottom: 20px; border-radius: 4px; border-left: 5px solid #ced6e0; }
        .status-running { background-color: #eccc68; border-left-color: #ffa502; color: #5d4037; }
        .status-success { background-color: #2ed573; border-left-color: #2f3542; color: #fff; }
    </style>
</head>
<body>
<div class="container">
    <h2 style="margin-top: 0; color: #2c3e50; border-bottom: 2px solid #3498db; padding-bottom: 10px;">SMG Monthly PDF Scraper Console</h2>
    <label style="font-weight: bold;">Target Year:</label> <input type="number" id="inputYear" placeholder="Leave blank for default (last month)">
    <label style="font-weight: bold;">Target Month:</label> 
    <select id="inputMonth">
        <option value="">-- Default Last Month --</option>
        <option value="1">01</option><option value="2">02</option><option value="3">03</option><option value="4">04</option>
        <option value="5">05</option><option value="6">06</option><option value="7">07</option><option value="8">08</option>
        <option value="9">09</option><option value="10">10</option><option value="11">11</option><option value="12">12</option>
    </select>
    <button id="btnAction" onclick="triggerTask()">Launch Scraper Engine</button>
    <div id="statusBanner" class="status-banner">System Engine Status: Idle</div>
    <div id="downloadSection" style="display: none; padding:15px; background:#e8f4fd; border: 1px solid #b3d7f7; border-radius: 4px; margin-bottom:15px; display: flex; justify-content: space-between; align-items: center;">
        <div style="font-weight: bold; color: #1e3799;" id="downloadMsg">Compilation Completed!</div>
        <a id="linkDownload" href="#" style="background:#2ed573; color:#fff; padding:10px 20px; text-decoration:none; border-radius: 4px; font-weight: bold;">Download PDF Report</a>
    </div>
    <div id="consoleLog" class="console-box">System localized log window initiated. Waiting for process invocation...</div>
</div>
<script>
    let offset = 0, interval = null;
    document.getElementById('downloadSection').style.display = 'none';

    function checkStatus() {
        fetch('/engine-status').then(r=>r.json()).then(d=>{
            const banner = document.getElementById('statusBanner');
            if (d.running) {
                banner.className = "status-banner status-running";
                banner.innerText = "System Engine Status: Active - Scraping Portal in Progress...";
                document.getElementById('btnAction').disabled = true;
            } else {
                document.getElementById('btnAction').disabled = false;
                if(d.result.filename) {
                    banner.className = "status-banner status-success";
                    banner.innerText = "System Engine Status: Ready - " + d.result.message;
                    document.getElementById('downloadSection').style.display = 'flex';
                    document.getElementById('linkDownload').href = "/retrieve-file?file=" + encodeURIComponent(d.result.filename);
                    clearInterval(interval);
                } else if(d.result.message !== "Idle") {
                    banner.className = "status-banner";
                    banner.style.borderLeftColor = "#ff4757";
                    banner.innerText = "System Engine Status: Terminated - " + d.result.message;
                    clearInterval(interval);
                }
            }
        });
    }

    function fetchLogs() {
        fetch('/poll-logs?offset='+offset).then(r=>r.json()).then(d=>{
            if(d.logs.length) {
                const c = document.getElementById('consoleLog');
                d.logs.forEach(m => c.innerText += m + "\\n");
                offset += d.logs.length;
                c.scrollTop = c.scrollHeight;
            }
        });
    }

    function triggerTask() {
        offset = 0; 
        document.getElementById('consoleLog').innerText = "Warming up engine thread environment...\\n";
        document.getElementById('downloadSection').style.display = 'none';
        
        fetch('/trigger-execution', {
            method: 'POST', headers: {'Content-Type': 'application/json'},
            body: JSON.stringify({year: document.getElementById('inputYear').value, month: document.getElementById('inputMonth').value})
        }).then(()=>{ 
            clearInterval(interval); 
            interval = setInterval(()=>{checkStatus(); fetchLogs();}, 1500); 
        });
    }
    checkStatus();
</script>
</body>
</html>
"""

app = Flask(__name__)
@app.route('/')
def serve_index_portal(): return render_template_string(CONTROL_PANEL_UI_TEMPLATE)
@app.route('/trigger-execution', methods=['POST'])
def trigger_execution_endpoint():
    global scraper_running_status, scraper_execution_result, app_log_buffer
    if scraper_running_status: return jsonify({"status": "rejected"}), 400
    p = request.json or {}
    app_log_buffer.clear()
    scraper_execution_result = {"success": False, "filename": "", "message": "Started"}
    scraper_running_status = True
    threading.Thread(target=execute_scraping_worker, args=(int(p.get('year')) if p.get('year') else None, int(p.get('month')) if p.get('month') else None)).start()
    return jsonify({"status": "initiated"})
@app.route('/engine-status')
def get_engine_status_endpoint(): return jsonify({"running": scraper_running_status, "result": scraper_execution_result})
@app.route('/poll-logs')
def poll_logs_endpoint(): return jsonify({"logs": app_log_buffer[request.args.get('offset', 0, type=int):]})
@app.route('/retrieve-file')
def retrieve_file_endpoint(): 
    file_path = Path(os.getcwd()) / request.args.get('file', '')
    return send_file(file_path, as_attachment=True)

if __name__ == "__main__":
    print("Starting server and opening browser...")
    threading.Timer(1.5, lambda: webbrowser.open("http://127.0.0.1:5000")).start()
    app.run(host="127.0.0.1", port=5000, debug=False, use_reloader=False)
