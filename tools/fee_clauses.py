"""登録版本文の欄位置から、項と注の開始位置を抽出する。"""

import re

from .fee_sections import _normalized

NUMBER = re.compile(r"([1-9][0-9]*)\s+\S")
NOTE = re.compile(r"注\s*([1-9][0-9]*)?(?=\s|$)\s*")
KANA = "イロハニホヘトチリヌルヲワカヨタレソツネナラムウヰノオクヤマケフコエテアサキユメミシヱヒモセス"
# 条項IDで使う慣用表記。
KANA_IDS = dict(zip(KANA, ("i ro ha ni ho he to chi ri nu ru wo wa ka yo ta re so tsu ne na ra mu "
                          "u wi no o ku ya ma ke fu ko e te a sa ki yu me mi shi we hi mo se su").split()))


def index_clauses(lines: list[tuple[int, int, str]]) -> dict:
    items, notes, issues = [], [], []
    item_indent = note_indent = note_body_indent = None
    item_number = None
    in_note = False
    note_context = None
    last_item_page = None
    last_note_page = None
    for offset, (page, line, raw) in enumerate(lines):
        text = _normalized(raw).rstrip()
        label = text.lstrip()
        indent = len(text) - len(label)
        position = {"page": page, "line": line}
        if match := NOTE.match(label):
            number = int(match[1]) if match[1] else None
            # 項欄が通頁でずれる場合は、当該頁の次の項も欄位置の手掛かりにする。
            next_item_indent = None
            for next_page, _, value in lines[offset + 1:]:
                if next_page != page:
                    break
                later = _normalized(value).rstrip()
                candidate = NUMBER.match(later.lstrip())
                if candidate and int(candidate[1]) == len(items) + 1:
                    next_item_indent = len(later) - len(later.lstrip())
                    break
            column = item_indent if last_item_page == page else next_item_indent
            nested = (column is not None and indent > column
                      and (next_item_indent is not None or not in_note))
            note_context = item_number if nested else None
            notes.append({**position, "number": number, "item": note_context})
            note_indent, last_note_page = indent, page
            note_body_indent = indent + match.end()
            in_note = True
        elif match := NUMBER.match(label):
            number = int(match[1])
            item_position = (indent == item_indent or
                             (last_item_page != page and number == len(items) + 1))
            if item_indent is None and not in_note and number == 1:
                item_position = True
            if item_position and (not in_note or note_context is not None):
                if number != len(items) + 1:
                    issues.append({**position, "kind": "item_sequence", "number": number})
                items.append({**position, "number": number, "path": f"item/{number}"})
                item_number, item_indent, last_item_page = number, indent, page
                in_note = False
            elif in_note and notes[-1]["number"] is not None and (
                (last_note_page == page and (indent in range(note_indent + 2, note_indent + 7)
                                             or (indent > note_indent and
                                                 indent + match.end() - 1 == note_body_indent)))
                or (last_note_page != page and number == notes[-1]["number"] + 1)
            ):
                if number != notes[-1]["number"] + 1:
                    issues.append({**position, "kind": "note_sequence", "number": number})
                notes.append({**position, "number": number, "item": note_context})
            elif not in_note and (item_indent is None or indent <= item_indent):
                issues.append({**position, "kind": "unresolved_number", "number": number})
        elif in_note and (match := re.match(r"([ァ-ヶ])\s+\S", label)):
            if match[1] in KANA_IDS:
                notes[-1].setdefault("children", []).append({
                    **position, "number": match[1],
                })

    unnumbered = 0
    for note in notes:
        prefix = "note" if note["item"] is None else f"item/{note['item']}/note"
        if note["number"] is not None:
            note["path"] = f"{prefix}/{note['number']}"
        elif note["item"] is not None:
            note["path"] = prefix
        else:
            unnumbered += 1
            note["path"] = f"note/unnumbered/{unnumbered}"
        # 従来の無番号注の枝IDを維持する。番号付きの注は親番号も識別子に含める。
        child_prefix = "note" if note["number"] is None else note["path"]
        for child in note.get("children", []):
            child["path"] = f"{child_prefix}/{KANA_IDS[child['number']]}"
    for item in {note["item"] for note in notes}:
        numbered = [note["number"] for note in notes if note["item"] == item and note["number"] is not None]
        if numbered != list(range(1, len(numbered) + 1)):
            issues.append({"kind": "note_sequence", "item": item, "numbers": numbered})
    paths = [entry["path"] for entry in items + notes]
    if len(paths) != len(set(paths)):
        issues.append({"kind": "duplicate_paths"})
    return {"items": items, "notes": notes, "clause_issues": issues,
            "item_note_paths": None if issues else paths}
