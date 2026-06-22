from __future__ import annotations
import argparse
import logging
import re
import os
import subprocess
import time
from datetime import date
from pathlib import Path
from typing import Optional

# ── BUG-FIX: 強制 Playwright 使用當前目錄下的瀏覽器 (打包 exe 必備) ──
os.environ["PLAYWRIGHT_BROWSERS_PATH"] = "0"

from playwright.sync_api import Page, sync_playwright
from pypdf import PdfWriter
import fitz  # PyMuPDF (用來取代 Ghostscript 進行 PDF 壓縮)

# ── Logging ────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)

# ── Config ─────────────────────────────────────────────────────────────────
BASE_URL = "https://www.smg.gov.mo"

SOURCES = [
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

# ── Compression ────────────────────────────────────────────────────────────
PDF_SIZE_LIMIT = 5 * 1024 * 1024   # 5 MB hard limit

# ── BUG-FIX 1: Date regex ──────────────────────────────────────────────────
DATE_RE = re.compile(
    r"(20\d{2})"                   # year
    r"[\s\-\/年\.]+"
    r"(1[0-2]|0?[1-9])"            # month — two-digit first
    r"[\s\-\/月\.]+"
    r"([12]\d|3[01]|0?[1-9])"      # day   — two-digit first
)

_JS_DATE_RE = r"(20\d{{2}})[\s\-/年.]+(1[0-2]|0?[1-9])[\s\-/月.]+([12]\d|3[01]|0?[1-9])"

def get_target_month() -> tuple[int, int]:
    today = date.today()
    return (today.year, today.month - 1) if today.month > 1 else (today.year - 1, 12)

def sanitize_filename(name: str, max_len: int = 100) -> str:
    name = re.sub(r"\s+", " ", name).strip()
    return re.sub(r'[\\/*?:"<>|]', "", name)[:max_len] or "Untitled"

def parse_date_str(raw: str) -> Optional[str]:
    m = DATE_RE.search(raw)
    if not m:
        return None
    return f"{m.group(1)}-{m.group(2).zfill(2)}-{m.group(3).zfill(2)}"

# ── Core: extract article links from current page DOM ─────────────────────
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

        const dateStr = match[1] + '-'
            + match[2].padStart(2, '0') + '-'
            + match[3].padStart(2, '0');

        let container = node.parentElement;
        let links = [];
        for (let i = 0; i < 8; i++) {
            if (!container || container.tagName === 'BODY') break;
            links = Array.from(container.querySelectorAll(
                'a[href]:not([href="#"]):not([href^="javascript"]), [data-url], [onclick]'
            ));
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
            if (title.length < 3 && container)
                title = (container.innerText || '').split('\\n')[0].trim();

            found.push({ url, date_str: dateStr, text: title.substring(0, 80) });
        });
    }

    if (found.length === 0 && window.location.href.includes('Holiday_weather')) {
        const m = document.body.innerText.match(DATE_RE);
        if (m) found.push({
            url:      window.location.href,
            date_str: m[1] + '-' + m[2].padStart(2,'0') + '-' + m[3].padStart(2,'0'),
            text:     document.title,
        });
    }
    return found;
}
"""

_MAX_PAGE_JS = """
() => {
    let max = 1;
    const pgSelectors = [
        '.pagination a', '.pagination button', '.pagination li a',
        '.page-list a',  '.page-bar a',
        '[class*="pagin"] a', '[class*="pagin"] button',
        '[class*="page-num"]', '[class*="pageNum"]',
    ];
    pgSelectors.forEach(sel => {
        document.querySelectorAll(sel).forEach(el => {
            const n = parseInt((el.innerText || el.textContent || '').trim(), 10);
            if (!isNaN(n) && n > max) max = n;
        });
    });

    const bodyText = document.body.innerText;
    const m = bodyText.match(/共\\s*(\\d+)\\s*頁/) ||
              bodyText.match(/of\\s+(\\d+)\\s+page/i);
    if (m) max = Math.max(max, parseInt(m[1], 10));

    return max;
}
"""

_CLICK_PAGE_JS = """
(pageNum) => {
    const label = String(pageNum);
    const selectors = [
        '.pagination a', '.pagination button', '.pagination li a', '.pagination li button',
        '.page-list a',  '.page-bar a',
        '[class*="pagin"] a', '[class*="pagin"] button',
        '[class*="page-num"]', '[class*="pageNum"]',
    ];
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

def _wait_for_content_change(page: Page, old_fingerprint: str, timeout_ms: int = 10_000) -> bool:
    deadline = time.monotonic() + timeout_ms / 1000
    while time.monotonic() < deadline:
        try:
            new_fp = page.evaluate(_ARTICLE_FINGERPRINT_JS)
            if new_fp and new_fp != old_fingerprint:
                return True
        except Exception:
            pass
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
    try:
        return page.evaluate(_EXTRACT_JS) or []
    except Exception as e:
        log.warning(f"  DOM extraction failed: {e}")
        return []

def collect_source(page: Page, src: dict, year: int, month: int) -> dict[str, dict]:
    all_items: dict[str, dict] = {}
    source_name = src["name"]
    base_url = src["url"].rstrip("/")

    log.info(f"  Loading: {base_url}")
    if not navigate_and_wait(page, base_url):
        return {}

    try:
        max_page = max(1, int(page.evaluate(_MAX_PAGE_JS)))
    except Exception:
        max_page = 1
    log.info(f"  Pagination: {max_page} page(s) detected")

    for page_num in range(1, min(max_page, MAX_PAGES) + 1):
        if page_num > 1:
            old_fp = page.evaluate(_ARTICLE_FINGERPRINT_JS)
            clicked = page.evaluate(_CLICK_PAGE_JS, page_num)

            if not clicked:
                break

            changed = _wait_for_content_change(page, old_fp, timeout_ms=12_000)
            if not changed:
                break
            page.wait_for_load_state("networkidle", timeout=15_000)

        articles = extract_page_articles(page)
        if not articles:
            break

        added       = 0
        found_older = False

        for item in articles:
            ds = item.get("date_str", "")
            if len(ds) < 10:
                continue
            try:
                ly, lm = int(ds[:4]), int(ds[5:7])
            except ValueError:
                continue

            if (ly, lm) < (year, month):
                found_older = True
            elif (ly, lm) == (year, month):
                url = item["url"]
                if url not in all_items:
                    all_items[url] = {**item, "source": source_name}
                    added += 1

        log.info(
            f"  Page {page_num}/{max_page}: {len(articles)} articles, "
            f"+{added} matched {year}-{month:02d}"
            + (" [older found → stop]" if found_older else "")
        )

        if found_older:
            break

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

        pdf_links: list[str] = page.evaluate(
            "() => Array.from(document.querySelectorAll('a[href$=\".pdf\"],a[href*=\"download\"]'))"
            ".map(a=>a.href)"
        )
        if pdf_links and download_pdf_robust(pdf_links[0], dest, page):
            return dest

        page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
        page.wait_for_timeout(1_000)
        page.evaluate("""() => {
            ['header','nav','footer','#header','#footer','#nav',
             '.site-header','.breadcrumb','.cookie-bar','.back-to-top',
             '.navbar-top','.sticky-header']
            .forEach(s => document.querySelectorAll(s).forEach(el => el.remove()));
        }""")
        page.add_style_tag(content=(
            "@media print{body{-webkit-print-color-adjust:exact !important;"
            "print-color-adjust:exact !important}}"
        ))
        page.pdf(path=str(dest), format="A4", print_background=True)

        if dest.exists() and dest.stat().st_size > 2_000:
            return dest
        return None

    except Exception as e:
        log.warning(f"  Failed processing {item['url']}: {e}")
        return None


# ── PDF compression (完全取代 Ghostscript 邏輯，使用 PyMuPDF) ──────────────
def compress_pdf_native(input_path: Path, output_path: Path) -> bool:
    """
    使用 PyMuPDF 進行無損壓縮，自動清理冗餘結構與資料流。
    優點：不需安裝任何外部工具（如 gs），同事拿到 exe 就能用。
    """
    input_size = input_path.stat().st_size
    input_mb   = input_size / 1_048_576

    if input_size <= PDF_SIZE_LIMIT:
        log.info(f"  PDF 大小為 {input_mb:.2f} MB — 已經小於 5 MB，跳過壓縮。")
        import shutil
        shutil.copy2(input_path, output_path)
        return True

    log.info(f"  PDF 大小為 {input_mb:.2f} MB — 正在使用內建壓縮引擎優化...")

    try:
        # 使用 fitz (PyMuPDF) 打開 PDF
        doc = fitz.open(input_path)
        
        # garbage=4: 最大程度清理無用物件
        # deflate=True: 壓縮資料流
        # clean=True: 清理和合併繪圖指令
        doc.save(output_path, garbage=4, deflate=True, clean=True)
        doc.close()

        out_size = output_path.stat().st_size
        out_mb   = out_size / 1_048_576
        log.info(f"  壓縮完成 → {out_mb:.2f} MB"
                 + (" ✅" if out_size <= PDF_SIZE_LIMIT else " (已達極限，但仍略大於 5 MB)"))

        return out_size <= PDF_SIZE_LIMIT

    except Exception as e:
        log.error(f"  內部壓縮失敗: {e} — 退回保留原始檔案。")
        import shutil
        shutil.copy2(input_path, output_path)
        return False


# ── Entry point ────────────────────────────────────────────────────────────

def main(year: int, month: int) -> None:
    log.info(f"🚀 SMG Monthly Scraper — Target: {year}-{month:02d}")

    tmp_dir = Path(f"smg_tmp_{year}_{month:02d}")
    tmp_dir.mkdir(exist_ok=True)

    with sync_playwright() as pw:
        browser = pw.chromium.launch(headless=True)
        ctx  = browser.new_context(
            viewport={"width": 1920, "height": 1080},
            accept_downloads=True,
        )
        page = ctx.new_page()

        all_items: dict[str, dict] = {}

        for src in SOURCES:
            log.info(f"\n📋 Source: {src['name']}")
            items = collect_source(page, src, year, month)
            before = len(all_items)
            all_items.update(items)
            log.info(f"  ✔ {src['name']}: {len(items)} found, "
                     f"{len(all_items)-before} new unique")

        if not all_items:
            log.warning(f"❌ No articles found for {year}-{month:02d}. Exiting.")
            browser.close()
            return

        sorted_items = sorted(all_items.values(), key=lambda x: x["date_str"])
        log.info(f"\n📦 Total unique articles to render: {len(sorted_items)}")

        writer = PdfWriter()
        for i, item in enumerate(sorted_items, 1):
            log.info(f"\n⚙  ({i}/{len(sorted_items)}) [{item['date_str']}] {item['text'][:50]}")
            pdf_path = process_article(page, item, tmp_dir, i)
            if pdf_path:
                try:
                    writer.append(str(pdf_path))
                except Exception as e:
                    log.warning(f"  Could not append {pdf_path.name}: {e}")

        # Write uncompressed merge first
        raw_output = Path(f"SMG_Monthly_Report_{year}_{month:02d}_raw.pdf")
        with raw_output.open("wb") as fh:
            writer.write(fh)

        raw_mb = raw_output.stat().st_size / 1_048_576
        log.info(f"\n📄 原始合併完成 PDF: {raw_output.name}  ({raw_mb:.2f} MB)")

        # 使用 Python 內建方式壓縮到最終輸出
        output = Path(f"SMG_Monthly_Report_{year}_{month:02d}.pdf")
        compress_pdf_native(raw_output, output)

        final_mb = output.stat().st_size / 1_048_576
        log.info(f"\n✅ 執行結束: {output.name}  ({final_mb:.2f} MB)")

        # 清理暫存檔與原始大檔案
        raw_output.unlink(missing_ok=True)
        browser.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--year",  type=int, default=get_target_month()[0])
    parser.add_argument("--month", type=int, default=get_target_month()[1])
    args = parser.parse_args()
    main(args.year, args.month)
