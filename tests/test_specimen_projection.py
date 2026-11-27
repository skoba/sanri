from datetime import date
import unittest

from tools.audit_residual_urine import active
from tools.audit_specimen import table_rows
from tools.specimen_projection import compare, observed_pairs, pair_index


class SpecimenProjectionTest(unittest.TestCase):
    def projection(self, *, table="exclusion_simultaneous", direction="1",
                   start="20261001", end="99999999", include=True):
        # 架空のコードと項目。抽出結果を比較する前に基準日の有効性を評価する。
        first, second = "900000001", "900000002"
        row = ["0", first, "", second, "", direction, "0", "0", start, end]
        evidence = {table: [{"fields": row, "line": 1,
                             "active_as_of": active(row, date(2026, 10, 22))}] if include else [],
                    "auxiliary": [], "inclusion": [], "frequency": []}
        tables, _ = table_rows({"evidence": evidence}, {first, second})
        index = pair_index(tables)
        pair = frozenset((first, second))
        return observed_pairs({pair}, index, {first: ("D999", "b"), second: ("D999", "a")})

    def status(self, observed, rows=None):
        if rows is None:
            rows = [["b", "a", "simultaneous", 1, False]]
        return compare({"synthetic": observed}, {"synthetic": rows}, {})["synthetic"]

    def test_matches_after_normalizing_priority(self):
        self.assertEqual(self.status(self.projection()), "一致")

    def test_missing_pair(self):
        self.assertEqual(self.status(self.projection(include=False)), "不一致")

    def test_changed_unit_and_direction(self):
        self.assertEqual(self.status(self.projection(table="exclusion_day")), "不一致")
        self.assertEqual(self.status(self.projection(direction="2")), "不一致")

    def test_rows_outside_validity_are_ignored(self):
        for kwargs in ({"start": "20261023"}, {"end": "20261021"}):
            with self.subTest(**kwargs):
                self.assertEqual(self.status(self.projection(**kwargs), []), "一致")
                self.assertEqual(self.status(self.projection(**kwargs)), "不一致")

    def test_expected_absence_fails_even_if_pair_was_already_in_projected_set(self):
        actual = self.projection()
        expected = [["b", "a", "simultaneous", 1, False]]
        self.assertEqual(compare({"synthetic": actual}, {"synthetic": expected}, {"synthetic": 1}),
                         {"synthetic": "不一致"})
