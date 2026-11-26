"""令和8年医科点数表の指定区分を抽出し、ローカルで型検査したLean草案を作る。"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

from .fee_lean_draft import build_draft
from .fee_sections import select_section
from .local_pdf import extract_pages, verified_pdf_pages
from .pdf_sources import LOCAL, NOTICE_PDF, NOTICE_SOURCE, PRIMARY_SOURCE, require_source


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PDF = LOCAL / "mhlw/r08/ika-primary.pdf"
DOCUMENT = PRIMARY_SOURCE["id"]
EDITION = PRIMARY_SOURCE["edition"]
URL = PRIMARY_SOURCE["url"]
SHA256 = PRIMARY_SOURCE["sha256"]


def verified_pages(pdf: Path) -> list[str]:
    if hashlib.sha256(pdf.read_bytes()).hexdigest() != SHA256:
        raise ValueError("本文PDFのSHA-256が登録版と異なります。対象版と取得元を確認してください。")
    return extract_pages(pdf)


def notice_excerpt(code: str, index: dict, pages: list[str]) -> dict:
    chapter = 1 if code.startswith("A") else 2
    blocks = []
    for block in index["blocks"]:
        if code not in block["codes"] or block["chapter"] != chapter or block["kind"] == "deleted":
            continue
        start, end = block["start"], block["end"]
        records = []
        for page in range(start["page"], end["page"] + 1):
            lines = pages[page - 1].splitlines()
            first = start["line"] if page == start["page"] else 1
            last = end["line"] if page == end["page"] else len(lines)
            if not (1 <= first <= last <= len(lines)):
                raise ValueError("通知索引の行範囲が原本の抽出行と一致しません")
            records.extend({"page": page, "line": line, "text": lines[line - 1]}
                           for line in range(first, last + 1))
        blocks.append({**block, "records": records})
    return {"status": "found" if blocks else "not_found", "source": index["source"], "blocks": blocks}


def save_draft(section, local: Path, notice: dict | None = None) -> tuple[Path, int, int]:
    draft = build_draft(section, identifier=DOCUMENT, edition=EDITION, url=URL)
    report = {
        "status": "needs_review",
        "code": section.code,
        "source": {"id": DOCUMENT, "edition": EDITION, "url": URL, "sha256": SHA256},
        "pages": [section.start_page, section.end_page],
        "records": draft.records,
    }
    if notice is not None:
        report["notice"] = notice
    review = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    files = {"Draft.lean": draft.lean, "review.json": review}

    # 原文を含む報告と草案をGit管理外の同じ場所に保存する。
    parent = local / "drafts" / section.code
    if parent.resolve() != parent or local.resolve() != local:
        raise ValueError("草案の保存先にシンボリックリンクがあります。")
    parent.mkdir(parents=True, exist_ok=True)
    revision = hashlib.sha256((review + "\0" + draft.lean).encode()).hexdigest()[:16]
    destination = parent / revision
    with TemporaryDirectory(prefix=".checking-", dir=parent) as tmp:
        bundle = Path(tmp) / "bundle"
        bundle.mkdir()
        for name, content in files.items():
            (bundle / name).write_text(content, encoding="utf-8")
        subprocess.run(["lake", "env", "lean", str(bundle / "Draft.lean")], cwd=ROOT, check=True)
        try:
            bundle.rename(destination)
        except OSError:
            # 同一結果の再実行を許し、手直しした草案は保持する。
            if not destination.is_dir() or destination.is_symlink():
                raise
            for name, content in files.items():
                path = destination / name
                if path.is_symlink() or not path.is_file() or path.read_text(encoding="utf-8") != content:
                    raise ValueError(f"既存の草案が変更されています。手直し分を退避してください: {destination}") from None
    rules = sum(record["kind"] in ("base_points", "patient_monthly_cap") for record in draft.records)
    unresolved = sum(record["kind"] == "unresolved" for record in draft.records)
    return destination, rules, unresolved


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("codes", nargs="+", metavar="区分番号", help="例: D216-2 D007")
    parser.add_argument("--pdf", type=Path, default=DEFAULT_PDF, help="資料台帳と同じ版の本文PDF")
    args = parser.parse_args()
    try:
        pages = verified_pages(args.pdf)
        sections = [select_section(pages, code) for code in args.codes]
        notice_path = LOCAL / "inventory/notice-index.json"
        notice_index = None
        notice_pages = []
        if notice_path.exists():
            if notice_path.resolve() != notice_path:
                raise ValueError("通知索引のパスにシンボリックリンクがあります")
            notice_index = json.loads(notice_path.read_text(encoding="utf-8"))
            require_source(notice_index["source"], NOTICE_SOURCE)
            require_source(notice_index["fee_source"], PRIMARY_SOURCE)
            notice_pages = verified_pdf_pages(NOTICE_PDF, NOTICE_SOURCE["sha256"])
            if len(notice_pages) != notice_index["source"]["page_count"]:
                raise ValueError("通知索引とPDFの頁数が異なります")
        subprocess.run(["lake", "build", "Sanri.Logic"], cwd=ROOT, check=True)
        for section in sections:
            notice = (notice_excerpt(section.code, notice_index, notice_pages) if notice_index is not None
                      else {"status": "index_missing", "blocks": []})
            folder, rules, unresolved = save_draft(section, LOCAL, notice)
            notice_status = {"found": "通知を抽出", "not_found": "通知索引に該当なし",
                             "index_missing": "通知索引なし（tools.notice_inventory で生成）"}[notice["status"]]
            print(f"{section.code} (PDF {section.start_page}–{section.end_page}頁) "
                  f"草案の規則 {rules} 件、未変換 {unresolved} 行、{notice_status}、要レビュー\n  {folder.relative_to(ROOT)}")
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"草案生成エラー: {error}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
