"""ローカルの登録版・医科点数表の見出しを、紙面順・物理頁順に棚卸しする。"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory
import unicodedata

from .draft_fee import DEFAULT_PDF, DOCUMENT, EDITION, LOCAL, SHA256, URL, verified_pages


LEVELS = {"章": "chapter", "部": "part", "節": "section", "款": "subsection"}
DIVISION = re.compile(r"第([0-9]+)([章部節款])\s+(.+)")
CODE = r"[A-Z][0-9]{3}(?:-[0-9]+)*"
SINGLE = re.compile(rf"({CODE})[ \t]+([^\s-].*)")
DELETION = re.compile(rf"(({CODE})(?:から({CODE})まで|及び({CODE})))\s+削除")


def normalized(text: str) -> str:
    return unicodedata.normalize("NFKC", text).replace("−", "-")


def build_inventory(pages: list[str]) -> dict:
    """Return anchored entries, including TOC-checked divisions and non-code tasks.

    A heading is an index into the source (first physical line, possibly wrapped).
    A grouped deletion stays as printed: its endpoints need not identify the
    intervening historical branch numbers. No cross-reference creates a fee row.
    """
    toc: list[str] = []
    body_divisions: list[str] = []
    in_body = False
    previous = ""
    scope = dict.fromkeys(LEVELS.values())
    sections: list[dict] = []
    general_rules: list[dict] = []
    noncode_rows: list[dict] = []
    rows: list[dict] = []

    for page, content in enumerate(pages, 1):
        if not content.strip():
            raise ValueError(f"PDF {page}頁の文字が空です")
        for line, raw in enumerate(content.splitlines(), 1):
            text = normalized(raw).rstrip()
            if not text:
                continue
            trimmed = text.strip()
            division = DIVISION.fullmatch(trimmed)
            if division:
                key = " ".join(trimmed.split())
                # 登録版では目次の次（同じ物理頁）で第1章の見出しが再登場する。
                if not in_body and toc and key == toc[0]:
                    in_body = True
                if not in_body:
                    toc.append(key)
                    continue
                body_divisions.append(key)
                level = division[2]
                ordered = list(LEVELS.values())
                for child in ordered[ordered.index(LEVELS[level]) + 1:]:
                    scope[child] = None
                scope[LEVELS[level]] = int(division[1])
                sections.append({**scope, "page": page, "line": line,
                                 "heading": raw.strip(), "level": level})
            elif in_body:
                anchor = {**scope, "page": page, "line": line, "heading": raw.strip()}
                if trimmed == "通則":
                    general_rules.append({**anchor, "heading": previous})
                elif (group := DELETION.fullmatch(text)):
                    rows.append({**anchor, "code": group[1], "status": "deleted_group",
                                 "first_code": group[2], "last_code": group[3] or group[4]})
                elif (entry := SINGLE.fullmatch(text)):
                    rows.append({**anchor, "code": entry[1],
                                 "status": "deleted" if entry[2] == "削除" else "listed"})
                elif (re.match(r"^[A-Z][0-9]{3}", text)
                      or SINGLE.fullmatch(trimmed) or DELETION.fullmatch(trimmed)):
                    raise ValueError(f"PDF {page}頁 {line}行の番号見出しは要確認です")
                elif scope["chapter"] in (3, 4) and (item := re.match(r"^([0-9]+)\s+\S", text)):
                    noncode_rows.append({**anchor, "number": int(item[1]), "kind": "numbered_item"})
            previous = raw.strip()
    if not toc or not in_body or toc != body_divisions:
        raise ValueError("目次と本文の章・部・節・款の見出し列が一致しません")
    return {"rows": rows, "noncode_rows": noncode_rows, "divisions": sections,
            "general_rules": general_rules}


def write_local(report: dict, local: Path = LOCAL) -> Path:
    target = local / "inventory" / "fee-index.json"
    if target.resolve() != target:
        raise ValueError("出力先にシンボリックリンクがあります")
    target.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=target.parent) as staging:
        tmp = Path(staging) / target.name
        tmp.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        tmp.replace(target)
    return target


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", type=Path, default=DEFAULT_PDF, help="登録版の医科本文PDF")
    args = parser.parse_args()
    try:
        pages = verified_pages(args.pdf)
        report = build_inventory(pages)
        report["source"] = {"id": DOCUMENT, "edition": EDITION, "sha256": SHA256,
                            "url": URL, "page_count": len(pages)}
        path = write_local(report)
    except (OSError, ValueError) as exc:
        parser.exit(1, f"棚卸しエラー: {exc}\n")
    counts = Counter(row["status"] for row in report["rows"])
    print(f"区分見出し {counts['listed']}、単独削除 {counts['deleted']}、"
          f"一括削除見出し {counts['deleted_group']}、第3・4章の番号項 {len(report['noncode_rows'])}、"
          f"通則見出し {len(report['general_rules'])}\n{path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
