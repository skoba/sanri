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
from .local_pdf import extract_pages


ROOT = Path(__file__).resolve().parents[1]
LOCAL = ROOT / "tensuhyo"
DEFAULT_PDF = LOCAL / "mhlw/r08/ika-primary.pdf"
# 資料台帳の確認版。異なる版・通知PDFを同じ出典として処理しない。
DOCUMENT = "令和8年厚生労働省告示第69号・別表第一"
EDITION = "令和8年度改定・2026-10-22取得版"
URL = "https://www.mhlw.go.jp/content/12400000/001686842.pdf"
SHA256 = "1b72d3cc1d0006f0e8f91afd2c3a49f21272e3ba376b8d24a6dffda63092e2d6"


def verified_pages(pdf: Path) -> list[str]:
    if hashlib.sha256(pdf.read_bytes()).hexdigest() != SHA256:
        raise ValueError("本文PDFのSHA-256が登録版と異なります。対象版と取得元を確認してください。")
    return extract_pages(pdf)


def save_draft(section, local: Path) -> tuple[Path, int, int]:
    draft = build_draft(section, identifier=DOCUMENT, edition=EDITION, url=URL)
    report = {
        "status": "needs_review",
        "code": section.code,
        "source": {"id": DOCUMENT, "edition": EDITION, "url": URL, "sha256": SHA256},
        "pages": [section.start_page, section.end_page],
        "records": draft.records,
    }
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
        subprocess.run(["lake", "build", "Sanri.Logic"], cwd=ROOT, check=True)
        for section in sections:
            folder, rules, unresolved = save_draft(section, LOCAL)
            print(f"{section.code} (PDF {section.start_page}–{section.end_page}頁) "
                  f"草案の規則 {rules} 件、未変換 {unresolved} 行、要レビュー\n  {folder.relative_to(ROOT)}")
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"草案生成エラー: {error}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
