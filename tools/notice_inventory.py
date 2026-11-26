"""登録版の留意事項通知を区分・段落と物理頁・抽出行へ対応付ける。"""

import argparse
from collections import Counter
import json
import re

from .fee_inventory import CODE, LEVELS, normalized, write_local
from .local_pdf import verified_pdf_pages
from .pdf_sources import LOCAL, NOTICE_PDF, NOTICE_SOURCE, PRIMARY_SOURCE, require_source

CODE_GROUP = rf"{CODE}(?:(?:、|及び){CODE})*(?:から{CODE}まで)?"
HEADING = re.compile(rf"({CODE_GROUP})(\s+)(\S.*)")
DIVISION = re.compile(r"第\s*([0-9]+)\s*([章部節款])(\s+)(\S.*)")
PARAGRAPH = re.compile(r"\(([1-9][0-9]*)\)(?:\s|$)")
TIGHT_MARKER = re.compile(r"\(([1-9][0-9]*)\)(?=\S)")
PARAGRAPH_REFERENCE = re.compile(r"\([1-9][0-9]*\)(?:から|まで|の|に|と|及び|又は|を|が|で|は|も)")
GENERAL = re.compile(r"([1-9][0-9]*)\s{2,}\S")
KANA = dict(zip("アイウエオカキクケコサシスセソタチツテトナニヌネノハヒフヘホマミムメモ",
                "a i u e o ka ki ku ke ko sa shi su se so ta chi tsu te to na ni nu ne no ha hi fu he ho ma mi mu me mo".split()))
CHILD = re.compile(r"([ァ-ヶへ])\s{2,}\S")
FOOTER = re.compile(r"-\s*[0-9]+\s*-")
# 別添1の2および末尾の別表は本文の区分見出しと異なる帳票レイアウト。
APPENDIX = re.compile(r"別添\s*1\s*の\s*2")


def build_notice(pages: list[str], fee_index: dict) -> dict:
    scope = dict.fromkeys(LEVELS.values())
    blocks, general, issues = [], [], []
    excluded = None
    block = paragraph = child = None
    last = None
    lines = [(page, line, normalized(raw).rstrip()) for page, content in enumerate(pages, 1)
             for line, raw in enumerate(content.splitlines(), 1)
             if raw.strip() and not FOOTER.fullmatch(normalized(raw).strip())]

    def close_span(entry):
        if entry is not None:
            entry["end"] = last

    def close_paragraph():
        nonlocal paragraph, child
        close_span(child)
        close_span(paragraph)
        paragraph = child = None

    def open_block(kind, position, codes=()):
        nonlocal block
        close_paragraph()
        close_span(block)
        block = {**scope, "kind": kind, "start": position, "paragraphs": [], "issues": []}
        if codes:
            block["codes"] = list(codes)
            blocks.append(block)
        else:
            general.append(block)

    for index, (page, line, text) in enumerate(lines):
        label = text.lstrip()
        indent = len(text) - len(label)
        position = {"page": page, "line": line}
        if APPENDIX.fullmatch(label):
            excluded = position
            break
        division = DIVISION.fullmatch(label)
        heading = HEADING.match(label)
        mark = PARAGRAPH.match(label)
        tight = TIGHT_MARKER.match(label)
        if mark is None and indent <= 4 and tight and not PARAGRAPH_REFERENCE.match(label):
            mark = tight
        next_label = lines[index + 1][2].strip() if index + 1 < len(lines) else ""
        if division and indent <= 5 and (len(division[3]) >= 2 or indent == 0):
            level = LEVELS[division[2]]
            ordered = list(LEVELS.values())
            for key in ordered[ordered.index(level) + 1:]:
                scope[key] = None
            scope[level] = int(division[1])
            open_block("division", position)
        elif heading and indent <= 4:
            codes = tuple(re.findall(CODE, heading[1]))
            kind = "deleted" if heading[3] == "削除" else "code" if len(codes) == 1 else "group"
            open_block(kind, position, codes)
            if "から" in heading[1]:
                block["issues"].append({**position, "kind": "range_endpoints_only"})
        elif re.match(CODE, label):
            issues.append({**position, "kind": "unparsed_heading"})
            open_block("unparsed_heading", position)
        elif label == "<通則>" or (block is not None and "codes" not in block
                                  and (paragraph is None or scope["subsection"] == 1 and scope["part"] == 3) and indent <= 3 and PARAGRAPH.match(next_label)
                                  and len(label) <= 32 and re.fullmatch(r"[\w（）()・、 ]+", label)
                                  and not mark and not GENERAL.match(label)
                                  and not CHILD.match(label) and not label.endswith(("こと", "する", "ない"))):
            open_block("general_heading", position)
        elif block is not None:
            is_general = "codes" not in block
            number = GENERAL.match(label) if is_general and indent <= 3 else None
            subnumber = mark and is_general and paragraph and paragraph["style"] == "decimal"
            if number or (mark and not subnumber and indent <= 7):
                close_paragraph()
                marker = number or mark
                paragraph = {"number": int(marker[1]), "start": position, "children": [],
                             "style": "decimal" if number else "parenthesized"}
                block["paragraphs"].append(paragraph)
            elif subnumber or (paragraph and (kana := CHILD.match(label)) and indent <= 15):
                close_span(child)
                token = int(mark[1]) if subnumber else kana[1]
                child = {"number": token, "start": position}
                if token in KANA:
                    child["id_suffix"] = KANA[token]
                paragraph["children"].append(child)
            elif (candidate := mark or tight) and not is_general and not PARAGRAPH_REFERENCE.match(label):
                block["issues"].append({**position, "kind": "unclassified_paragraph_marker",
                                        "number": int(candidate[1])})
            elif paragraph is None:
                paragraph = {"number": None, "start": position, "children": [], "style": "unnumbered"}
                block["paragraphs"].append(paragraph)
        last = position
    close_paragraph()
    close_span(block)

    for entry in blocks + general:
        for collection in [entry["paragraphs"], *(p["children"] for p in entry["paragraphs"])]:
            counts = Counter(p["number"] for p in collection)
            duplicates = [n for n, count in counts.items() if count > 1]
            numbers = sorted(n for n in counts if isinstance(n, int))
            gaps = sorted(set(range(1, numbers[-1] + 1)) - set(numbers)) if numbers else []
            kana = [n for n in counts if isinstance(n, str)]
            kana_order = list(KANA)
            kana_gaps = []
            if kana and all(n in KANA for n in kana):
                kana_gaps = [n for n in kana_order[:max(kana_order.index(n) for n in kana)] if n not in counts]
            if duplicates or gaps or kana_gaps:
                entry["issues"].append({"kind": "numbering", "start": collection[0]["start"],
                                        "duplicates": duplicates, "missing": gaps + kana_gaps})

    by_code = Counter((b["chapter"], code) for b in blocks if b["kind"] != "deleted" for code in b["codes"])
    primary = {(r["chapter"], r["code"]) for r in fee_index["rows"] if r["status"] == "listed"}
    observed = set(by_code)

    def keys(values):
        return [{"chapter": chapter, "code": code}
                for chapter, code in sorted(values, key=lambda key: (key[0] or 0, key[1]))]

    return {"blocks": blocks, "general": general, "issues": issues,
            "empty_pages": [i for i, p in enumerate(pages, 1) if not p.strip()],
            "appendix_start": excluded,
            "primary_only": keys(primary - observed), "notice_only": keys(observed - primary),
            "notice_deleted": keys((b["chapter"], c) for b in blocks if b["kind"] == "deleted" for c in b["codes"]),
            "duplicate_codes": keys(key for key, count in by_code.items() if count > 1)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    fee = json.loads((LOCAL / "inventory/fee-index.json").read_text(encoding="utf-8"))
    require_source(fee["source"], PRIMARY_SOURCE)
    pages = verified_pdf_pages(NOTICE_PDF, NOTICE_SOURCE["sha256"])
    report = build_notice(pages, fee)
    if report["appendix_start"] is None:
        raise ValueError("通知の別添境界を特定できません")
    report.update(source={**NOTICE_SOURCE, "page_count": len(pages)}, fee_source=fee["source"])
    print(write_local(report, name="notice-index.json"))
    blocks = [block for block in report["blocks"] if block["kind"] != "deleted"]
    codes = {(block["chapter"], code) for block in blocks for code in block["codes"]}
    numbered = sum(p["number"] is not None for block in blocks for p in block["paragraphs"])
    print(f"通知の区分 {len(codes)}、番号段落 {numbered}、通則等のブロック {len(report['general'])}")
    print(f"未抽出見出し {len(report['issues'])}、本文のみ {len(report['primary_only'])}、"
          f"通知のみ {len(report['notice_only'])}")


if __name__ == "__main__":
    main()
