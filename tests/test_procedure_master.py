"""合成した行だけで、診療行為マスターの取込と区分索引を検査する。"""

from datetime import date
from fractions import Fraction
import hashlib
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
import zipfile

from tools.procedure_master import (
    MasterError, WIDTH, coverage, index_rows, load_registered, parse_master, parse_row,
)


def synthetic(code="199000110", cells=None) -> list[str]:
    """仕様の項番（1始まり）で上書きできる、実在しない診療行為の1行。"""
    row = ["0"] * WIDTH
    defaults = {1: "0", 2: "S", 3: code, 5: "合成検査", 11: "3", 12: "12.00", 13: "0",
                68: "1", 69: "1", 85: "D", 86: "", 87: "20260601", 88: "99999999",
                90: "2", 91: "03", 92: "901", 93: "00", 94: "001",
                95: "0", 96: "00", 97: "000", 98: "00", 99: "00",
                **{i + offset: "00" for i in range(100, 112, 3) for offset in (0, 1)}}
    for number, value in {**defaults, **(cells or {})}.items():
        row[number - 1] = value
    return row


def encoded(*rows: list[str]) -> bytes:
    return "".join(",".join(row) + "\r\n" for row in rows).encode("cp932")


class ProcedureMasterTests(unittest.TestCase):
    def test_typed_fields_and_division_keys(self):
        record = parse_row(synthetic(cells={12: "1010.50", 16: "1", 36: "2", 51: "3", 93: "04", 94: "012"}))
        self.assertEqual(record.points, Fraction(2021, 2))
        self.assertEqual((record.division, record.item, record.bundle_group, record.max_count,
                          record.judgment_group), ("D901-4", 12, 1, 2, 3))
        self.assertIsNone(record.ref_division)
        # 第3章・医療観察・食事等は区分欄を持たない。
        self.assertIsNone(parse_row(synthetic(cells={85: "-", 90: "8"})).division)
        self.assertIsNone(parse_row(synthetic(cells={85: "*"})).division)
        applied = parse_row(synthetic(cells={68: "5", 86: "D", 95: "2", 96: "03", 97: "902", 98: "02", 99: "07"}))
        self.assertEqual((applied.ref_division, applied.ref_item), ("D902-2", 7))

    def test_rejects_rows_outside_the_layout(self):
        for cells in ({2: "T"}, {3: "299000110"}, {11: "2"}, {12: "12"}, {12: "-1.00"}, {13: "3"},
                      {68: "2"}, {85: "d"}, {87: "20260631"}, {88: "20260531"}, {92: "7"}):
            with self.subTest(cells=cells), self.assertRaises(MasterError):
                parse_row(synthetic(cells=cells))
        with self.assertRaises(MasterError):
            parse_row(synthetic()[:-1])

    def test_validity_does_not_reconstruct_earlier_or_removed_content(self):
        current = parse_row(synthetic())
        self.assertFalse(current.usable_on(date(2026, 5, 31)))
        self.assertTrue(current.usable_on(date(2026, 6, 1)))
        ended = parse_row(synthetic(cells={88: "20261031"}))
        self.assertTrue(ended.usable_on(date(2026, 10, 31)))
        self.assertFalse(ended.usable_on(date(2026, 11, 1)))
        with self.assertRaises(MasterError):
            parse_row(synthetic(cells={1: "9"})).usable_on(date(2026, 10, 22))

    def test_file_level_checks(self):
        data = encoded(synthetic("199000110"), synthetic("199000210"))
        self.assertEqual([r.code for r in parse_master(data)], ["199000110", "199000210"])
        for broken in (encoded(synthetic(), synthetic()), b"", data.replace(b"S", b"S\0", 1),
                       "合成検査".encode("utf-8")):
            with self.subTest(broken=broken[:20]), self.assertRaises(MasterError):
                parse_master(broken)

    def test_registered_archive_is_checked_before_reading(self):
        with TemporaryDirectory() as folder:
            archive = Path(folder) / "master.zip"
            with zipfile.ZipFile(archive, "w") as bundle:
                bundle.writestr("master.csv", encoded(synthetic()))
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            self.assertEqual(len(load_registered(archive, digest, "master.csv")), 1)
            with self.assertRaises(MasterError):
                load_registered(archive, "0" * 64, "master.csv")
            with self.assertRaises(MasterError):
                load_registered(archive, digest, "other.csv")
            with self.assertRaises(MasterError):
                load_registered(Path(folder) / "missing.zip", digest, "master.csv")

    def test_index_and_heading_coverage(self):
        records = parse_master(encoded(
            synthetic("199000110"),
            synthetic("199000210", {93: "02", 94: "003", 87: "20261101", 1: "3"}),
            synthetic("199000310", {92: "903"}),
            synthetic("199000410", {85: "-", 90: "8", 92: "000"}),
        ))
        rows = index_rows(records, date(2026, 10, 22))
        self.assertEqual([(r[0], r[1], r[2], r[21]) for r in rows], [
            ("199000110", "D901", 1, 1), ("199000210", "D901-2", 3, 0),
            ("199000310", "D903", 1, 1), ("199000410", "", 1, 1)])
        report = coverage(records, date(2026, 10, 22), ["D901", "D901-2", "D902", "D904-1-2"])
        self.assertEqual((report["records"], report["usable"], report["without_division"]), (4, 3, 1))
        self.assertEqual(report["not_yet_effective"], ["199000210"])
        self.assertEqual(report["changed_in_this_edition"], ["199000210"])
        self.assertEqual((report["matched"], report["headings_without_records"],
                          report["headings_second_level_branch"], report["divisions_without_heading"]),
                         (1, ["D901-2", "D902"], ["D904-1-2"], ["D903"]))


if __name__ == "__main__":
    unittest.main()
