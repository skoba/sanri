"""Check the mapping of our Lean definitions independently of any official data."""

import unittest

from tools.fee_coverage import coverage_for


class CoverageTests(unittest.TestCase):
    def test_same_code_in_another_chapter(self):
        self.assertEqual(coverage_for("A000", 1).status, "model")
        self.assertEqual(coverage_for("A000", 3).status, "new")

    def test_no_inheritance_from_parent_or_neighbour(self):
        self.assertEqual(coverage_for("D221-2", 2).status, "model")
        self.assertEqual(coverage_for("D221", 2).status, "new")
        self.assertEqual(coverage_for("D221-99", 2).status, "new")

    def test_reference_does_not_imply_individual_model(self):
        self.assertEqual(coverage_for("D026", 2).status, "model")
        self.assertEqual(coverage_for("D027", 2).status, "reference")
        self.assertEqual(coverage_for("D006-9", 2).module, "Sanri/SpecimenJudgment.lean")
        self.assertEqual(coverage_for("D006-10", 2).status, "new")
