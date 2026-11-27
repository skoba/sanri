"""公式行を使わずに検体検査照合の境界を検査する。"""

from dataclasses import replace
import unittest

from test_procedure_master import synthetic
from tools.audit_specimen import (
    collection_inclusion, compare_count_attributes, compare_tables, correspondence, exclusion_key,
    pack_inclusion, relation_scope, table_rows, grade, MATCH, REPRESENTATION, UNKNOWN,
)
from tools.procedure_master import parse_row


class SpecimenAuditTests(unittest.TestCase):
    def test_name_resolves_only_an_existing_structural_point_candidate(self):
        record = parse_row(synthetic())
        point = {"item": "syntheticA", "points": 12}
        other = {"item": "syntheticB", "points": 12}
        candidates = {("D901", 1, "base"): [point, other]}
        review = {("D901", 1): {"合成検査": "syntheticB"}}
        self.assertEqual(correspondence(record, candidates, review)[::2], (other, "名称による"))
        self.assertIsNone(correspondence(record, candidates)[0])
        self.assertIsNone(correspondence(replace(record, item=2), candidates, review)[0])
        self.assertIsNone(correspondence(replace(record, points_text="13.00"), candidates, review)[0])

    def test_exclusion_scope_keeps_unmapped_and_external_apart(self):
        mapped = {"lean": {"item": "synthetic"}, "master": {"入外適用区分": "0"}}
        unmapped = {**mapped, "lean": None}
        inpatient = {**mapped, "master": {"入外適用区分": "1"}}
        mapping = {"a": mapped, "b": unmapped, "c": inpatient}
        locations = {"outside": (2, 1, "B999")}
        self.assertEqual(relation_scope(["a", "a"], mapping, locations), "両端対応済み")
        self.assertEqual(relation_scope(["a", "b"], mapping, locations), "検体検査のコード未対応")
        self.assertEqual(relation_scope(["a", "c"], mapping, locations), "対象範囲外（入院のみ）")
        self.assertEqual(relation_scope(["b", "outside"], mapping, locations),
                         "対象範囲外（相手が検体検査外）")
        self.assertEqual(relation_scope(["a", "missing"], mapping, locations), "相手の区分未同定")

    def test_general_day_projection_preserves_direction_and_special(self):
        mapping = {
            code: {"lean": {"division": "D000", "kind": "general", "item": name},
                   "master": {"入外適用区分": "0"}}
            for code, name in (("a", "emergencyAddition"), ("b", "rapidAddition"))
        }
        rows = [{"codes": ["a", "b"], "direction": direction, "special": special, "rows": []}
                for direction, special in (("1", False), ("2", False), ("1", True))]
        compare_tables({"exclusion_day": rows, "frequency": [], "inclusion": []}, mapping, {})
        self.assertEqual([r["classification"] for r in rows], [MATCH, UNKNOWN, UNKNOWN])

    def test_collection_inclusion_leaves_special_or_different_unit_open(self):
        parent = {"division": "D412", "kind": "base"}
        location = (2, 3, "D215")
        row = {"unit": "3", "special": False}
        self.assertEqual(collection_inclusion(parent, location, row)["classification"], REPRESENTATION)
        self.assertIsNone(collection_inclusion(parent, location, {**row, "special": True}))
        self.assertIsNone(collection_inclusion(parent, location, {**row, "unit": "1"}))

    def test_master_count_projection_leaves_error_handling_open(self):
        record = replace(parse_row(synthetic()), max_count=1)
        attributes = {field: grade(UNKNOWN, "合成例") for field in ("max_count", "max_count_handling")}
        frequency = {"codes": ["a"], "limit": 1, "classification": MATCH,
                     "clauses": ["test"], "rows": [{"line": 2}]}
        compare_count_attributes({"a": {"attributes": attributes}}, [frequency], {"a": record})
        self.assertEqual(attributes["max_count"]["classification"], REPRESENTATION)
        self.assertEqual(attributes["max_count_handling"]["classification"], UNKNOWN)
        self.assertEqual(attributes["max_count"]["frequency_lines"], [2])

    def test_master_layout_addition_fields(self):
        record = parse_row(synthetic(cells={38: "6033", 39: "B", 72: "42", 81: "448",
                                           100: "00", 101: "04", 102: "199000111",
                                           109: "06", 110: "17", 111: "199000112"}))
        self.assertEqual(record.addition_key, (6033, "B"))
        self.assertEqual(record.facility_codes, (42, *([0] * 8), 448))
        self.assertEqual(record.age_additions[0], ("00", "04", 199000111))
        self.assertEqual(record.age_additions[-1], ("06", "17", 199000112))

    def test_exclusion_normalization_preserves_priority_and_flag(self):
        row = ["0", "199000111", "", "199000112", "", "1", "1", "0", "20260801", "99999999"]
        self.assertEqual(exclusion_key(row), exclusion_key(
            [*row[:1], *row[3:5], *row[1:3], "2", *row[6:]]))
        self.assertNotEqual(exclusion_key(row), exclusion_key(
            [*row[:1], *row[3:5], *row[1:3], "1", *row[6:]]))

    def test_inclusion_joins_both_directions_with_valid_parent_child_positions(self):
        a, b, c = "199000111", "199000112", "199000113"
        def entry(line, fields, active=True):
            return {"line": line, "fields": fields, "active_as_of": active}

        parents = [entry(11, ["0", a, "", "3", "TST0001", "0", "0", "0", "0"]),
                   entry(12, ["0", b, "", "0", "0", "1", "TST0001", "0", "0"]),
                   entry(13, ["0", c, "", "2", "TST0001", "0", "0", "0", "0"], False)]
        children = [entry(21, ["0", "TST0001", c, "", "1"]),
                    entry(22, ["0", "TST0001", a, "", "0"]),
                    entry(23, ["0", "TST0001", c, "", "0"], False)]
        tables, lines = table_rows({"evidence": {"auxiliary": parents, "inclusion": children,
                                                "frequency": []}}, {a})
        self.assertEqual(lines, {21, 22})
        self.assertEqual([rel["codes"] for rel in tables["inclusion"]], [[a, c], [a, a], [b, a]])
        for rel in tables["inclusion"]:
            rel.update(grade(UNKNOWN, "合成条件"))
        packed = pack_inclusion(tables["inclusion"])
        self.assertEqual(packed["rows"][-1], [b, a, "1", False, 12, 6, 22, 0])
        self.assertEqual(len(packed["results"]), 1)
