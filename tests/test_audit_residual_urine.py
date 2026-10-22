"""Synthetic fixtures only; no official records or patient data are distributed."""

import csv
from datetime import date
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location("audit_residual_urine", Path(__file__).resolve().parents[1] / "tools/audit_residual_urine.py")
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)
LEFT, RIGHT = "900000001", "900000002"
AS_OF = date(2026, 10, 22)


def auxiliary(code):
    return ["0", code, "synthetic method", "0", "0", "0", "0", "0", "0", "1", "0", "0", "0", "0", "0", "0", "", "0", "0", "000", "1", "0", "0", "0", "0", "20260101", "99999999"]


def frequency(code, unit="131", limit="2", exception="0"):
    return ["0", code, "synthetic method", unit, {"121": "日", "131": "月"}.get(unit, "synthetic unit"), limit, exception, "0", "0", "0", "0", "0", "20260101", "99999999"]


def exclusion(left=LEFT, right=RIGHT):
    return ["0", left, "synthetic method A", right, "synthetic method B", "3", "0", "0", "20260101", "99999999"]


def synthetic_tables():
    rows = {kind: [] for kind in audit.FILES}
    rows["auxiliary"] = [auxiliary(LEFT), auxiliary(RIGHT)]
    rows["frequency"] = [frequency(LEFT), frequency(RIGHT)]
    rows["exclusion_day"] = [exclusion(), exclusion(RIGHT, LEFT)]
    return rows


def write_snapshot(path, tables):
    (path / "tables").mkdir()
    manifest = {
        "table_published_on": "2026-10-13", "guide_published_on": "2026-07-24",
        "downloaded_at": "2026-10-22T15:00:00+09:00",
        "reference_encoding": "utf-8", "reference_newline": "LF",
        "source_page": "https://example.invalid/synthetic", "extracted_files": [],
    }
    for kind, (name, width) in audit.FILES.items():
        content = io.StringIO(newline="")
        csv.writer(content, lineterminator="\n").writerows(tables[kind])
        data = content.getvalue().encode("utf-8")
        relative = f"tables/{name}"
        (path / relative).write_bytes(data)
        manifest["extracted_files"].append({"path": relative, "bytes": len(data), "sha256": audit.digest(data), "rows": len(tables[kind]), "column_counts": [width]})
    (path / "sources.json").write_text(json.dumps(manifest), encoding="utf-8")


class AuditTests(unittest.TestCase):
    def load(self, tables=None, as_of=AS_OF):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)
            write_snapshot(path, synthetic_tables() if tables is None else tables)
            return audit.load_snapshot(path, {LEFT, RIGHT}, as_of)

    def comparison(self, tables=None):
        return audit.projection_witness(self.load(tables), LEFT, RIGHT, 2, AS_OF)

    def test_distinct_days_witness_is_only_projection(self):
        result = self.comparison()
        self.assertEqual(result["status"], "bounded_projection_witness")
        self.assertEqual(len({r["date"] for r in result["events"]}), 3)
        self.assertEqual(result["per_code_month_counts"], {LEFT: 2, RIGHT: 1})
        self.assertFalse(result["caller_supplied_text_limit_satisfied"])
        self.assertTrue(result["projection_constraints_satisfied"])
        self.assertTrue(result["assumptions"])

    def test_evidence_retains_source_lines_and_all_frequency_rows(self):
        tables = synthetic_tables()
        tables["frequency"].append(frequency(LEFT, unit="121", limit="1"))
        snapshot = self.load(tables)
        self.assertEqual(len(snapshot["evidence"]["frequency"]), 3)
        self.assertEqual(snapshot["evidence"]["frequency"][2]["line"], 3)
        self.assertEqual(len(snapshot["manifest_sha256"]), 64)
        self.assertEqual(len(snapshot["files"]), 8)
        self.assertEqual(audit.projection_witness(snapshot, LEFT, RIGHT, 2, AS_OF)["status"], "bounded_projection_witness")

    def test_monthly_pair_blocks_the_bounded_history(self):
        tables = synthetic_tables()
        tables["exclusion_month"] = [exclusion()]
        for row in tables["auxiliary"]:
            row[10] = "1"
        self.assertEqual(self.comparison(tables)["status"], "no_witness_in_bounded_projection")

    def test_daily_zero_cap_is_unknown_without_documented_semantics(self):
        tables = synthetic_tables()
        tables["frequency"] += [frequency(LEFT, "121", "0"), frequency(RIGHT, "121", "0")]
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_per_code_limit_one_has_no_three_event_witness(self):
        tables = synthetic_tables()
        for row in tables["frequency"]:
            row[5] = "1"
        self.assertEqual(self.comparison(tables)["status"], "no_witness_in_bounded_projection")

    def test_unknown_frequency_exception(self):
        tables = synthetic_tables()
        tables["frequency"][0][6] = "1"
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_unknown_exclusion_exception(self):
        tables = synthetic_tables()
        tables["exclusion_day"][0][6] = "1"
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_unknown_unit_is_not_ignored(self):
        tables = synthetic_tables()
        tables["frequency"].append(frequency(LEFT, "141"))
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_unknown_weekly_exclusion(self):
        tables = synthetic_tables()
        tables["exclusion_week"] = [exclusion()]
        for row in tables["auxiliary"]:
            row[12] = "1"
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_missing_monthly_row_is_unknown(self):
        tables = synthetic_tables()
        tables["frequency"].pop()
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_future_row_is_not_used(self):
        tables = synthetic_tables()
        tables["frequency"][0][-2] = "20270601"
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_history_validity_boundary_is_unknown(self):
        tables = synthetic_tables()
        tables["frequency"][0][-2] = "20261021"
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_expired_frequency_constraint_is_not_dropped(self):
        tables = synthetic_tables()
        earlier = frequency(LEFT, limit="1")
        earlier[-1] = "20261021"
        tables["frequency"].append(earlier)
        snapshot = self.load(tables)
        self.assertFalse(snapshot["evidence"]["frequency"][-1]["active_as_of"])
        result = audit.projection_witness(snapshot, LEFT, RIGHT, 2, AS_OF)
        self.assertEqual(result["status"], "unknown")
        self.assertIn("row validity changes", result["unknown_reasons"][-1])

    def test_expired_monthly_exclusion_is_not_dropped(self):
        tables = synthetic_tables()
        earlier = exclusion()
        earlier[-1] = "20261021"
        tables["exclusion_month"].append(earlier)
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_expired_auxiliary_constraint_is_not_dropped(self):
        tables = synthetic_tables()
        earlier = auxiliary(LEFT)
        earlier[-1] = "20261021"
        tables["auxiliary"].append(earlier)
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_row_expired_before_entire_candidate_is_irrelevant(self):
        tables = synthetic_tables()
        earlier = frequency(LEFT, limit="1")
        earlier[-1] = "20261019"
        tables["frequency"].append(earlier)
        self.assertEqual(self.comparison(tables)["status"], "bounded_projection_witness")

    def test_unsupported_deletion_and_abolition_are_explicit_errors(self):
        for kind in ("auxiliary", "frequency", "exclusion_day"):
            for change in ("1", "9"):
                tables = synthetic_tables()
                tables[kind][0][0] = change
                with self.subTest(kind=kind, change=change), self.assertRaisesRegex(audit.AuditError, "deletion/abolition"):
                    self.load(tables)

    def test_history_before_snapshot_is_unknown(self):
        day = date(2026, 10, 14)
        result = audit.projection_witness(self.load(as_of=day), LEFT, RIGHT, 2, day)
        self.assertEqual(result["status"], "unknown")

    def test_same_code_exclusion_is_unknown(self):
        tables = synthetic_tables()
        tables["exclusion_day"].append(exclusion(LEFT, LEFT))
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_unknown_auxiliary_relationship_flag(self):
        tables = synthetic_tables()
        tables["auxiliary"][0][9] = "0"
        self.assertEqual(self.comparison(tables)["status"], "unknown")

    def test_invalid_enum_date_and_column_are_rejected(self):
        for index, value in ((0, "7"), (-2, "20260230"), (6, "9")):
            tables = synthetic_tables()
            tables["frequency"][0][index] = value
            with self.subTest(index=index), self.assertRaises(audit.AuditError):
                self.load(tables)
        tables = synthetic_tables()
        tables["frequency"][0].pop()
        with self.assertRaises(audit.AuditError):
            self.load(tables)

    def test_hash_mismatch_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)
            write_snapshot(path, synthetic_tables())
            target = path / "tables" / audit.FILES["frequency"][0]
            target.write_bytes(target.read_bytes().replace(b",2,", b",3,", 1))
            with self.assertRaisesRegex(audit.AuditError, "SHA-256 mismatch"):
                audit.load_snapshot(path, {LEFT, RIGHT}, AS_OF)

    def test_unknown_version_and_historical_asof_rejected(self):
        with self.assertRaises(audit.AuditError):
            self.load(as_of=date(2026, 10, 12))
        with self.assertRaises(audit.AuditError):
            self.load(as_of=date(2026, 10, 23))
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)
            write_snapshot(path, synthetic_tables())
            manifest_path = path / "sources.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["table_published_on"] = "2027-01-01"
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(audit.AuditError, "unsupported snapshot"):
                audit.load_snapshot(path, {LEFT, RIGHT}, AS_OF)


if __name__ == "__main__":
    unittest.main()
