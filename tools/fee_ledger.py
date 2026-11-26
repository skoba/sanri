"""公開Leanモデルの条項・点数を登録版のローカル索引と比較する。"""

from collections import Counter, defaultdict
import csv
from datetime import date
from decimal import Decimal
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from .draft_fee import DOCUMENT, EDITION, LOCAL, SHA256
from .fee_coverage import clause_paths, coverage_for, source_modules
from .procedure_master import ARCHIVE_SHA256, INDEX_COLUMNS

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = LOCAL / "inventory"


def load_lean() -> dict:
    return json.loads(subprocess.check_output(
        ["lake", "env", "lean", "tools/FeeLedger.lean"], cwd=ROOT, text=True,
    ))


def clause_coverage(index: dict, rules: list[dict]) -> dict:
    modules = source_modules(rules)
    represented = defaultdict(lambda: defaultdict(set))
    unclassified = []
    distinct_paths = set()
    for rule in rules:
        paths = clause_paths(rule)
        distinct_paths.update(paths)
        if not paths:
            unclassified.append(rule)
        for path in paths:
            if path[0] in {"primary", "notice"} and path[1][0].isupper():
                represented[path[1]][path[0]].add("/".join(path[2:]))
    rows = []
    for heading in index["rows"]:
        if heading["status"] != "listed":
            continue
        code, chapter = heading["code"], heading["chapter"]
        coverage = coverage_for(code, chapter, modules)
        status = {"source": "出典付き制約あり", "model": "旧来の計算モデルのみ",
                  "reference": "未着手", "new": "未着手"}[coverage.status]
        paths = represented.get(code, {}) if (chapter, code) in modules else {}
        modeled = sorted(paths.get("primary", ()))
        # 現行の見出し索引には項・注の一覧がない。将来の列は完全列挙時だけ付ける。
        indexed = heading.get("item_note_paths")
        rows.append({
            "chapter": chapter, "division": code, "status": status, "module": coverage.module,
            "primary_paths": modeled, "notice_paths": sorted(paths.get("notice", ())),
            "item_note_total": None if indexed is None else len(set(indexed)),
            "item_note_matched": None if indexed is None else len(set(indexed) & set(modeled)),
        })
    return {
        "division_counts": dict(Counter(row["status"] for row in rows)),
        "clause_paths_by_kind": dict(Counter(
            path[0] for path in sorted(distinct_paths)
        )),
        "divisions_with_item_note_total": sum(row["item_note_total"] is not None for row in rows),
        "divisions": rows,
        "paths_without_division": ["/".join(path) for path in sorted(distinct_paths)
                                   if path[0] == "clarification" or not path[1][0].isupper()],
        "unclassified": unclassified,
    }


def compare_points(points: list[dict], master: list[dict]) -> dict:
    """比較単位は区分・項番・種別内の点数集合。コードや枝・検査種類の同一性は別途確認する。"""
    divisions = {row["division"] for row in points}
    lean_groups = defaultdict(list)
    master_groups = defaultdict(list)
    separate = defaultdict(list)
    for row in points:
        if row["kind"] == "reference":
            separate["lean_reference"].append(row)
        else:
            lean_groups[row["division"], row["number"], row["kind"]].append(row)

    for row in master:
        if row["区分"] not in divisions or row["基準日に使用可能"] != "1":
            continue
        if row["準用元区分"]:
            separate["master_reference"].append(row)
            continue
        if row["点数識別"] != "3":
            separate["master_non_point"].append(row)
            continue
        if row["告示等識別区分1"] in {"7", "9"} or row["告示等識別区分2"] == "7":
            kind = "note"
        elif row["告示等識別区分1"] == "1" and row["告示等識別区分2"] == "1":
            kind = "base"
        else:
            separate["master_other"].append(row)
            continue
        master_groups[row["区分"], int(row["項番"]), kind].append(row)

    rows = []
    counts = defaultdict(Counter)
    for key in sorted(lean_groups.keys() | master_groups.keys()):
        lean_rows, master_rows = lean_groups.get(key, []), master_groups.get(key, [])
        left = {Decimal(row["points"]) for row in lean_rows if row["points"] is not None}
        right = {Decimal(row["新又は現点数"]) for row in master_rows}
        if not lean_rows:
            status = "master_only"
        elif not master_rows:
            status = "lean_only"
        elif any(row["points"] is None for row in lean_rows):
            status = "unknown_points"
        elif left == right:
            status = "match"
        else:
            status = "mismatch"
        counts[key[2]][status] += 1
        rows.append({
            "division": key[0], "number": key[1], "kind": key[2], "status": status,
            "matched_points": [format(price.normalize(), "f") for price in sorted(left & right)],
            "lean_only_points": [format(price.normalize(), "f") for price in sorted(left - right)],
            "master_only_points": [format(price.normalize(), "f") for price in sorted(right - left)],
            "lean": lean_rows, "master": master_rows,
        })
    return {"counts": {kind: dict(stat) for kind, stat in counts.items()},
            "separate_counts": {kind: len(group) for kind, group in separate.items()},
            "comparisons": rows, "separate": dict(separate)}


def read_index(name: str) -> dict:
    return json.loads((INVENTORY / name).read_text(encoding="utf-8"))


def main() -> None:
    if INVENTORY.resolve() != INVENTORY:
        raise ValueError("入出力は tensuhyo/inventory 内に限ります。")
    index = read_index("fee-index.json")
    source = index["source"]
    if (source["id"], source["edition"], source["sha256"]) != (DOCUMENT, EDITION, SHA256):
        raise ValueError("本文索引が登録版と異なります。")
    master_source = read_index("master-coverage.json")
    if (master_source["as_of"] != "2026-10-22" or
            master_source["source"]["archive_sha256"] != ARCHIVE_SHA256):
        raise ValueError("診療行為マスター索引が対象の版・基準日と異なります。")
    with (INVENTORY / "master-index.tsv").open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if tuple(reader.fieldnames or ()) != INDEX_COLUMNS:
            raise ValueError("診療行為マスター索引の列が異なります。")
        master = list(reader)
    day = date.fromisoformat(master_source["as_of"]).strftime("%Y%m%d")
    if any(row["基準日に使用可能"] != str(int(row["変更年月日"] <= day <= row["廃止年月日"]))
           for row in master):
        raise ValueError("診療行為マスター索引の使用可否が基準日と異なります。")
    lean = load_lean()
    clauses = clause_coverage(index, lean["rules"])
    prices = compare_points(lean["points"], master)
    report = {"fee_source": source, "master_source": master_source["source"],
              "as_of": master_source["as_of"], "clauses": clauses, "points": prices}
    path = INVENTORY / "clause-ledger.json"
    with TemporaryDirectory(dir=INVENTORY) as directory:
        temporary = Path(directory) / path.name
        temporary.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        temporary.replace(path)
    print(path)
    print(clauses["division_counts"], clauses["clause_paths_by_kind"])
    print(f"項・注の分母を取得できる区分 {clauses['divisions_with_item_note_total']} / {len(clauses['divisions'])}")
    print(prices["counts"], prices["separate_counts"])


if __name__ == "__main__":
    main()
