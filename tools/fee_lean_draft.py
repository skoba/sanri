"""Translate a few printed fee-table forms into independent, unreviewed Lean projections."""

from dataclasses import dataclass
import re
import unicodedata

from .fee_sections import FeeSection


@dataclass
class Draft:
    lean: str
    records: list[dict]


# An integer at the end of a flat row. Refuse malformed thousands separators.
_POINTS = r"(0|[1-9][0-9]*|[1-9][0-9]{0,2}(?:,[0-9]{3})+)\s*点"
_NUMBERED_ROW = re.compile(r"([1-9][0-9]*)\s+(.+?)\s+" + _POINTS)
_HEADING_FEE = re.compile(r"(.+?)\s+" + _POINTS)


def _simple_label(text: str) -> bool:
    # Points derived from another section, multiple amounts and composite or
    # conditional rows require human interpretation. Only draft plain labels.
    return bool(re.fullmatch(r"[\w\sー・－-]+", text)) and not re.search(
        r"点|場合|限[りる]|除[くき]|ただし|算定|加算|減算|につき|当たり|以上|以下|未満", text
    )


def _lean_string(value: str) -> str:
    """Escape metadata as a Lean literal; refuse unsupported control characters."""
    escapes = {'"': r'\"', "\\": r"\\", "\n": r"\n", "\r": r"\r", "\t": r"\t"}
    if any(not char.isprintable() and char not in escapes for char in value):
        raise ValueError("資料情報に使用できない制御文字があります")
    return '"' + "".join(escapes.get(char, char) for char in value) + '"'


def build_draft(
    section: FeeSection, *, identifier: str, edition: str, url: str | None = None
) -> Draft:
    """Always returns draft-only rule declarations and one review record per line."""
    if not re.fullmatch(r"[A-Z][0-9]{3}(?:-[0-9]+)*", section.code):
        raise ValueError("区分番号を確認してください")
    if not section.lines or not identifier.strip() or not edition.strip():
        raise ValueError("区分本文・資料識別子・版を指定してください")
    texts = [unicodedata.normalize("NFKC", line.text).strip() for line in section.lines]
    heading = re.fullmatch(re.escape(section.code) + r"\s+(.+)", texts[0].replace("−", "-"))
    if not heading:
        raise ValueError("区分番号と見出しが一致しません")
    records = [
        {"page": line.page, "line": line.number, "text": line.text, "kind": "unresolved"}
        for line in section.lines
    ]

    title = heading[1]
    fee = _HEADING_FEE.fullmatch(title)
    if fee and _simple_label(fee[1]):
        title = fee[1]
        records[0].update(kind="base_points", item=None, points=int(fee[2].replace(",", "")))
    elif _simple_label(title):
        records[0]["kind"] = "heading"

    # Restrict the grammar to sequential, top-level items before the first
    # note or unknown body line. Note continuations can also start with digits.
    if records[0]["kind"] == "heading":
        for number, row in enumerate(texts[1:], 1):
            item = _NUMBERED_ROW.fullmatch(row)
            if not item or int(item[1]) != number or not _simple_label(item[2]):
                break
            records[number].update(
                kind="base_points", item=number, points=int(item[3].replace(",", ""))
            )

    # Only a single, complete final note naming the whole section can yield
    # a shared cap. An unparsed exception before or after it invalidates this match.
    if (len(records) > 1 and any(r["kind"] == "base_points" for r in records)
            and all(r["kind"] != "unresolved" for r in records[:-1])):
        subject = re.escape("".join(title.split()))
        cap = re.fullmatch(
            rf"注{subject}は、患者1人につき月(?:に)?([1-9][0-9]*)回に限り算定する。",
            "".join(texts[-1].split()),
        )
        if cap:
            records[-1].update(kind="patient_monthly_cap", limit=int(cap[1]))
    return Draft(_render(section.code, identifier, edition, url, records), records)


def _render(code: str, identifier: str, edition: str, url: str | None, records: list[dict]) -> str:
    namespace = "Sanri.Draft." + code.replace("-", "_")
    link = f"some {_lean_string(url)}" if url is not None else "none"
    blocks = [
        f"""import Sanri.Logic

-- 未レビューの機械生成草案。所定点数欄と回数上限だけを表す。
-- 各項の選択条件、他条項による例外、通知等の確認は別途必要。
namespace {namespace}

open Sanri.Logic

private def source (location : String) : SourceRef where
  kind := .primaryText
  identifier := {_lean_string(identifier)}
  edition := {_lean_string(edition)}
  location := location
  verification := .unchecked
  url := {link}"""
    ]
    unresolved = []
    for record in records:
        location = _lean_string(f"{code} PDF p.{record['page']} 抽出行{record['line']}")
        if record["kind"] == "base_points":
            item = record["item"]
            suffix = f"item{item}" if item is not None else "section"
            selector = f"some {item}" if item is not None else "none"
            blocks.append(f"""/-- 選択した欄の所定点数。some は項番号、none は区分本体。 -/
def {suffix}BasePoints : Rule (Option Nat) Nat where
  id := "{code}.{suffix}.basePoints"
  source := source {location}
  holds := fun selected points => selected = {selector} → points = {record['points']}""")
        elif record["kind"] == "patient_monthly_cap":
            blocks.append(f"""/-- 同一患者・一暦月の本区分の算定候補。各要素は1回分の項の識別子。 -/
def patientMonthlyCap : Rule Unit (List Nat) where
  id := "{code}.patientMonthlyCap"
  source := source {location}
  holds := fun _ claims => claims.length ≤ {record['limit']}""")
        elif record["kind"] == "unresolved":
            unresolved.append(location)
    blocks.append("/-- 自動変換できなかった原文の位置。 -/\n"
                  + "def unresolvedLocations : List String := [" + ", ".join(unresolved) + "]")
    blocks.append(f"end {namespace}")
    return "\n\n".join(blocks) + "\n"
