"""登録版監査の入力から、Lean の検体検査事例へ射影する。"""

from collections import Counter, defaultdict
from itertools import product
import json
import subprocess

from .procedure_master import require


PAIR_GROUPS = {
    "glycemic_pairs": "notice/D005/paragraph/9",
    "coagulation": "notice/D006/paragraph/8/i",
    "d014": "notice/D014/paragraph/7/i",
    "electrophoresis": "notice/D015/paragraph/4/i",
    "pf4": "notice/D011/paragraph/4/u",
}
ABSENCE_GROUPS = {
    "d014_missing": ("notice/D014/paragraph/7/i", 7),
    "pancreatic_missing": ("notice/D001/paragraph/4/i", 1),
    "pneumococcus_missing": ("notice/D012/paragraph/31/i", 1),
    "pertussis_missing": ("notice/D012/paragraph/43/i", 2),
    "electrophoresis": ("notice/D015/paragraph/4/i", 2),
    "respiratory_missing": ("notice/D023/paragraph/37/u", 6),
}
FREQUENCY_GROUPS = {
    "glycemic_frequency": (("D005", "hemoglobinA1c"), ("D007", "glycatedAlbumin"),
                           ("D007", "anhydroglucitol")),
    "renal_frequency": tuple(("D001", item) for item in
                             ("transferrin", "albuminQuantitative", "typeIVCollagen")),
}
FREQUENCY_UNITS = {"131": "month", "144": "threeMonths"}


def point_key(point):
    return point["division"], point["item"].rsplit(".", 1)[-1]


def pair_index(tables):
    result = defaultdict(list)
    for table, rows in tables.items():
        if table == "inclusion" or table.startswith("exclusion_"):
            for row in rows:
                result[frozenset(row["codes"])].append((table, row))
    return result


def normalized_pair(left, right, unit, direction, special):
    if right < left:
        left, right = right, left
        direction = {1: 2, 2: 1}.get(direction, direction)
    return left, right, unit, direction, special


def abstract_pair(table, row, keys):
    left, right = (keys[c][1] for c in row["codes"])
    if table == "inclusion":
        # 親・子の方向を保つ。背反の優先方向とは別の単位。
        return normalized_pair(left, right, "inclusion/" + row["unit"], 1, row["special"])
    return normalized_pair(left, right, table.removeprefix("exclusion_"),
                           int(row["direction"]), row["special"])


def selected_pairs(group, inverse):
    result = set()
    for candidate in group["pairs"]:
        left, right = map(tuple, candidate["items"])
        require(inverse[left] and inverse[right], "射影対象対のコード対応が不足")
        result.update(frozenset((a, b)) for a, b in product(inverse[left], inverse[right]) if a != b)
    require(result, "射影対象対が空")
    return result


def observed_pairs(pairs, index, keys):
    return {abstract_pair(table, row, keys) for pair in pairs for table, row in index.get(pair, ())}


def project(tables, mapping, presence, records, day, absence):
    inverse = defaultdict(set)
    keys = {}
    for code, entry in mapping.items():
        if entry["lean"] and entry["master"]["入外適用区分"] != "1":
            keys[code] = point_key(entry["lean"])
            inverse[keys[code]].add(code)
    index = pair_index(tables)
    projected = {}
    for case, clause in PAIR_GROUPS.items():
        codes = selected_pairs(presence[clause], inverse)
        require(all(len(inverse[keys[c]]) == 1 for pair in codes for c in pair),
                f"{case} の項目対に複数のコードが対応")
        projected[case] = observed_pairs(codes, index, keys)

    require(set(absence) == set(ABSENCE_GROUPS), "欠落対レビューの群が異なる")
    reviewed = set()
    found = {}
    for case, (clause, expected) in ABSENCE_GROUPS.items():
        pairs = {frozenset(pair) for pair in absence[case]}
        candidates = selected_pairs(presence[clause], inverse)
        require(len(pairs) == len(absence[case]) == expected and pairs <= candidates,
                f"{case} の欠落対レビューと現在の対応が異なる")
        reviewed.update(pairs)
        found[case] = sum(pair in index for pair in pairs)
        projected.setdefault(case, set()).update(observed_pairs(pairs, index, keys))
    require(len(reviewed) == 18, "欠落対レビューの重複除外後の件数が異なる")

    for case, items in FREQUENCY_GROUPS.items():
        require(all(len(inverse[item]) == 1 for item in items), f"{case} のコード対応が一意でない")
        codes = set().union(*(inverse[item] for item in items))
        projected[case] = Counter(
            (keys[code][1], FREQUENCY_UNITS.get(row["unit"], row["unit"]), row["limit"], row["special"])
            for row in tables["frequency"] for code in row["codes"] if code in codes)

    base = inverse["D402", "suboccipitalPuncture"]
    require(len(base) == 1 and len(inverse["D401", "infant"]) == 1, "年齢加算のコード対応が一意でない")
    projected["puncture_age"] = Counter()
    for lower, upper, code in records[next(iter(base))].age_additions:
        if not code:
            continue
        target = records.get(str(code))
        if (target and target.usable_on(day) and target.point_kind == "3"
                and str(code) in inverse["D401", "infant"] and lower.isdecimal() and upper.isdecimal()):
            projected["puncture_age"]["d401Infant", int(lower), int(upper), target.points] += 1
        else:
            projected["puncture_age"]["unresolved"] += 1
    return projected, found


def compare(projected, expected, found):
    require(set(projected) == set(expected), "Lean と Python の事例名が異なる")
    result = {}
    for case, rows in expected.items():
        actual = projected[case]
        if isinstance(actual, set):
            same = actual == {normalized_pair(*row) for row in rows}
        else:
            same = actual == Counter(map(tuple, rows))
        result[case] = "一致" if same and found.get(case, 0) == 0 else "不一致"
    return result


def check(tables, mapping, presence, records, day, review_path):
    with review_path.open(encoding="utf-8") as stream:
        absence = json.load(stream)
    projected, found = project(tables, mapping, presence, records, day, absence)
    lean = subprocess.run(["lake", "env", "lean", "tools/SpecimenProjection.lean"],
                          check=True, capture_output=True, text=True)
    return {"as_of": day.isoformat(), "cases": compare(projected, json.loads(lean.stdout), found),
            "reviewed_absence_hits": found}
