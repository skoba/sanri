"""公式行を使わずに検体検査照合の境界を検査する。"""

from dataclasses import replace
import unittest
from unittest.mock import patch

from test_procedure_master import synthetic
from tools.audit_specimen import (
    bundle_membership, collection_inclusion, compare_count_attributes, compare_tables,
    correspondence, exclusion_key, matches_choice_direction, reviewed_alternatives,
    pack_inclusion, pair_coverage, reference_candidates, reference_rate_projection, relation_scope, reviewed_point,
    table_rows, grade, MATCH, REPRESENTATION, SOURCE_CONFLICT, UNKNOWN, UNMODELED,
)
from tools.procedure_master import parse_row
from tools.specimen_audit_groups import BUNDLE_IDS, SELECTION_IDS, choice_review, group_pair_presence


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

    def test_reviewed_reverse_pairs_preserve_direction_units_and_specials(self):
        mapping = {
            code: {"lean": {"division": division, "kind": "base", "item": item, "number": number},
                   "master": {"入外適用区分": "0"},
                   "attributes": {"bundle_group": {"classification": UNKNOWN}}}
            for code, division, item, number in (
                ("a", "D012", "gonococcusAntigen", 42), ("b", "D018", "respiratory", 1),
                ("c", "D008", "hcgQualitative", 1), ("d", "D008", "hcgQuantitative", 19),
                ("e", "D012", "rapidGroupAStrep", 18),
            )
        }
        rows = [{"codes": list(codes), "direction": direction, "special": special, "rows": []}
                for codes, direction, special in (
                    ("ab", "2", False), ("ab", "1", False), ("ab", "2", True),
                    ("be", "2", False), ("cd", "3", False), ("cd", "3", True),
                )]
        compare_tables({"exclusion_simultaneous": rows, "frequency": [], "inclusion": []}, mapping, {})
        self.assertEqual([row["classification"] for row in rows],
                         [MATCH, UNKNOWN, UNKNOWN, REPRESENTATION, REPRESENTATION, UNKNOWN])

    def test_reviewed_tumor_frequency_applies_to_the_normal_patient_limit(self):
        mapping = {"a": {"lean": {"division": "D004-2", "kind": "base", "item": "drugAid", "number": 1},
                         "master": {"入外適用区分": "0"}}}
        rows = [{"codes": ["a"], "unit": unit, "limit": limit, "special": special, "rows": []}
                for unit, limit, special in (
                    ("53", 1, False), ("131", 1, False), ("53", 2, False), ("53", 1, True),
                )]
        compare_tables({"frequency": rows, "inclusion": []}, mapping, {})
        self.assertEqual([row["classification"] for row in rows],
                         [REPRESENTATION, UNKNOWN, UNKNOWN, UNKNOWN])

    def test_collection_inclusion_leaves_special_or_different_unit_open(self):
        parent = {"division": "D412", "kind": "base"}
        location = (2, 3, "D215")
        row = {"unit": "3", "special": False}
        self.assertEqual(collection_inclusion(parent, location, row)["classification"], REPRESENTATION)
        self.assertIsNone(collection_inclusion(parent, location, {**row, "special": True}))
        self.assertIsNone(collection_inclusion(parent, location, {**row, "unit": "1"}))

    def test_master_count_projection_excludes_claim_handling(self):
        record = replace(parse_row(synthetic()), max_count=1)
        attributes = {field: grade(UNKNOWN, "合成例") for field in ("max_count", "max_count_handling")}
        frequency = {"codes": ["a"], "limit": 1, "classification": MATCH,
                     "clauses": ["test"], "rows": [{"line": 2}]}
        compare_count_attributes({"a": {"attributes": attributes}}, [frequency], {"a": record})
        self.assertEqual(attributes["max_count"]["classification"], REPRESENTATION)
        self.assertEqual(attributes["max_count_handling"]["classification"], UNMODELED)
        self.assertEqual(attributes["max_count_handling"]["value"], record.max_count_handling)
        self.assertEqual(attributes["max_count"]["frequency_lines"], [2])

    def test_review_distinguishes_equal_price_branches(self):
        points = [{"item": "x", "branch": i, "points": 12} for i in (1, 2)]
        self.assertIsNone(reviewed_point(points, "x", 12))
        self.assertEqual(reviewed_point(points, {"item": "x", "branch": 2}, 12), points[1])
        self.assertIsNone(reviewed_point(points, {"item": "x", "branch": 2}, 13))

    def test_reference_candidates_include_cross_division_notice(self):
        record = replace(parse_row(synthetic()), ref_alpha="D", ref_number="901", ref_item=1)
        blocks = {("D902", 1): [(12, 12, "D901の「1」の所定点数により算定する。")],
                  ("D903", 1): [(13, 13, "D901の「1」の所定点数により算定する。")]}
        candidates = reference_candidates(record, blocks, {"D901", "D902"})
        self.assertEqual([e["clause"] for e in candidates], ["notice/D902/paragraph/1"])

    def test_reference_rate_does_not_map_the_originating_performance(self):
        record = replace(parse_row(synthetic()), ref_alpha="D", ref_number="901",
                         ref_chapter=2, ref_part=3, ref_item=2)
        point = {"item": "rate", "number": 1, "points": 12}
        by_key = {("D901", 1, "base"): [point]}
        evidence = {"reference_rate": {"division": "D901", "master_item": 2,
                                       "number": 1, "item": "rate"}}
        projection = reference_rate_projection(record, by_key, evidence)
        self.assertEqual(projection["item_status"], "項番差・由来未確定")
        self.assertIsNone(reference_rate_projection(replace(record, ref_part=4), by_key, evidence))
        self.assertIsNone(correspondence(record, by_key)[0])

    def test_pair_coverage_requires_all_cross_code_pairs_and_matching_scope(self):
        observed = [{"codes": ["a", "c"], "same_projection": True, "table": "exclusion_simultaneous",
                     "direction": "3", "special": False},
                    {"codes": ["b", "c"], "same_projection": False, "table": "exclusion_simultaneous",
                     "direction": "1", "special": False}]
        coverage = pair_coverage({"a", "b"}, {"c"}, observed)
        self.assertEqual(coverage, {"status": "一部のみ", "expected": 2, "matching": 1})
        pair = {"mapping_sizes": [2, 1], "electronic_rows": observed,
                "reason_type": "単位違い", "coverage": coverage}
        self.assertEqual(choice_review([pair], False)["status"], "一部のみ")
        self.assertEqual(pair_coverage(set(), {"c"}, observed)["status"], "コード未対応")
        self.assertEqual(pair_coverage({"c"}, {"c"}, [])["status"], "同一コードへ縮約")
        self.assertEqual(len(set(SELECTION_IDS)), 89)
        self.assertEqual(len(set(BUNDLE_IDS)), 22)

    def test_group_presence_tracks_item_and_code_pairs_independently(self):
        a, b, c, d = (("D901", name) for name in ("A", "B", "C", "D"))
        inverse = {a: {"a1", "a2"}, b: {"b"}, c: {"c"}}
        observed = {
            "exclusion_day": [{"codes": ["a1", "b"], "direction": "2", "special": True,
                               "rows": [{"line": 10}]}],
            "inclusion": [{"codes": ["c", "b"], "unit": "3", "special": False,
                           "auxiliary_line": 11, "line": 12}],
            "frequency": [{"codes": ["a2"], "unit": "121", "limit": 1, "special": False}],
        }
        groups = {"partial": {(a, b), (b, c)}, "none": {(a, c)},
                  "unmapped": {(a, d)}, "full": {(b, c)}}
        result = group_pair_presence(groups, inverse, observed)
        self.assertEqual(result["partial"]["item_pairs"]["status"], "全対あり")
        self.assertEqual(result["partial"]["code_pairs"],
                         {"status": "一部のみ", "expected": 3, "missing": 1})
        self.assertEqual(result["partial"]["pairs"][0]["missing_code_pairs"], [("a2", "b")])
        self.assertTrue(result["partial"]["pairs"][0]["rows"][0]["special"])
        self.assertEqual(result["partial"]["pairs"][1]["rows"][0]["codes"], ["c", "b"])
        self.assertEqual(result["none"]["code_pairs"]["status"], "全対なし")
        self.assertEqual(result["full"]["code_pairs"]["status"], "全対あり")
        self.assertEqual(result["unmapped"]["code_pairs"]["status"], "比較対象なし")
        self.assertEqual(result["unmapped"]["unmapped_items"], [d])

    def test_unit_difference_stays_unresolved(self):
        group = choice_review([{"mapping_sizes": [1, 1], "electronic_rows": [
            {"table": "exclusion_simultaneous", "direction": "3", "special": False}],
            "coverage": {"expected": 1, "matching": 0}, "reason_type": "単位違い"}], False)
        self.assertEqual((group["status"], group["reason_type"]), ("未判定", "単位違い"))

    def test_choice_direction_keeps_the_preferred_side_after_normalization(self):
        clause = "notice/D901/paragraph/1"
        first = ("D901", "syntheticA")
        second = ("D902", "syntheticB")
        with patch.dict("tools.audit_specimen.CHOICE_PRIORITIES", {clause: second}):
            self.assertTrue(matches_choice_direction("2", [first, second], clause))
            self.assertTrue(matches_choice_direction("1", [second, first], clause))
            self.assertFalse(matches_choice_direction("1", [first, second], clause))
            self.assertFalse(matches_choice_direction("3", [first, second], clause))

    def test_reviewed_pair_gap_requires_two_mapped_endpoints_and_no_related_rows(self):
        clause = "notice/D901/paragraph/1"
        first = ("D901", "syntheticA")
        second = ("D902", "syntheticB")
        mapping = {code: {"lean": {"division": item[0], "item": item[1], "kind": "base"},
                          "master": {"入外適用区分": "0"}}
                   for code, item in (("a", first), ("b", second))}
        candidate = f"{clause}/syntheticA/syntheticB"
        row = {"codes": ["a", "b"], "direction": "3", "special": True, "rows": []}
        with patch("tools.audit_specimen.CHOICES", (("syntheticRule", clause, None, first, second),)):
            with patch.dict("tools.audit_specimen.REVIEWED_PAIR_GAPS", {clause: {first}}):
                incomplete = {**mapping, "b": {**mapping["b"], "lean": None}}
                for records, related, expected in (
                    (mapping, [], SOURCE_CONFLICT),
                    (mapping, [row], UNKNOWN),
                    (incomplete, [], UNKNOWN),
                ):
                    reverse = compare_tables(
                        {"exclusion_simultaneous": related, "frequency": [], "inclusion": []}, records, {})
                    self.assertEqual(reverse[candidate]["classification"], expected)

    def test_bundle_membership_compares_both_directions(self):
        self.assertEqual(bundle_membership({"a", "b"}, {"a", "c", "d"}, {"a", "b", "c"}), {
            "both": ["a"], "lean_only": ["b"],
            "master_only_mapped": ["c"], "master_only_unresolved": ["d"],
        })

    def test_alternatives_keep_multiple_items_at_the_reviewed_price(self):
        points = [{"division": "D901", "item": item, "points": price}
                  for item, price in (("a", 12), ("b", 12), ("c", 15))]
        self.assertEqual(reviewed_alternatives(points, {"items": ["a", "b"]}, 12)["points"],
                         points[:2])
        with self.assertRaises(ValueError):
            reviewed_alternatives(points, {"items": ["a", "c"]}, 12)

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
