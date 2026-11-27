"""選択・別算定制限のレビュー候補をローカルに出力する。"""

import csv
import re
from collections import defaultdict

from .fee_ledger import ROOT, load_lean
from .local_pdf import verified_pdf_pages
from .pdf_sources import NOTICE_PDF, NOTICE_SOURCE

MODULE = re.compile(
    r"D(?:00\d|01\d|02[0-3]|4\d\d).*|BloodMorphology|BloodChemistry.*|"
    r"GlycemicTests|UrineSediment|UrineFecalTests|Specimen(?:NeedleSelection|Collection.*)"
)
INDICATOR = re.compile(
    r"principal|selection|choice|exclu|conflict|prefer|billed|separate|together|"
    r"selected|simultaneous|compet|combin|onsame",
    re.IGNORECASE,
)
FIELD = re.compile(r"^  (\w+) *: *([^\n]+)", re.MULTILINE)
DEFINITION = re.compile(
    r"^(?:private )?def ([\w.]+)\b.*?(?=^\S|\Z)", re.MULTILINE | re.DOTALL
)
NOTICE_INDICATOR = re.compile(r"主たる|いずれか一方|併せて算定|別に算定できない")
OUTPUT = ROOT / "tensuhyo" / "audits"


def write_table(name: str, header: tuple[str, ...], rows: set[tuple]) -> None:
    with (OUTPUT / name).open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t")
        writer.writerow(header)
        writer.writerows(sorted(rows))


def main() -> None:
    sources = sorted(p for p in (ROOT / "Sanri").glob("*.lean") if MODULE.fullmatch(p.stem))
    rule_rows = defaultdict(list)
    for row in load_lean()["rules"]:
        if row["id"]:
            rule_rows[row["module"]].append(row)
    inputs = set()
    rules = set()
    for path in sources:
        source = path.read_text(encoding="utf-8")
        definitions = {m[1]: m[0] for m in DEFINITION.finditer(source)}
        for name, annotation in FIELD.findall(source):
            if INDICATOR.search(name) and annotation.startswith(("Option ", "Bool", "Prop", "Nat ", "List ")):
                inputs.add((path.stem, name, annotation.split(" :=")[0]))
        for row in rule_rows[f"Sanri.{path.stem}"]:
            name = row["definition"]
            short = name.split("/")[0].rsplit(".", 1)[-1]
            if INDICATOR.search(name) or INDICATOR.search(definitions.get(short, "")):
                rules.add((path.stem, name, row["id"]))

    OUTPUT.mkdir(parents=True, exist_ok=True)
    write_table("3a-4-selection-input-candidates.tsv", ("module", "field", "type"), inputs)
    write_table("3a-4-selection-rule-candidates.tsv", ("module", "definition", "rule_id"), rules)
    pages = verified_pdf_pages(NOTICE_PDF, NOTICE_SOURCE["sha256"])
    notice = {
        (page, line, text.strip())
        for page in range(329, 450)
        for line, text in enumerate(pages[page - 1].splitlines(), 1)
        if NOTICE_INDICATOR.search(text)
    }
    write_table("3a-4-selection-notice-candidates.tsv", ("page", "line", "text"), notice)
    print(f"対象 {len(sources)} モジュール、入力候補 {len(inputs)}、規則候補 {len(rules)}、通知候補 {len(notice)}")


if __name__ == "__main__":
    main()
