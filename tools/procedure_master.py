"""Load the registered medical procedure master and index it by fee division.

The master (医科診療行為マスター) is distributed separately from the electronic
fee table. It is read from the ignored local folder, checked against the
registered archive hash and the published 150-column layout, and never bundled.
Passing these checks shows consistency with the registered snapshot. It does not
certify the snapshot, a code-to-text correspondence, or billing eligibility.
Requires Python 3.10+ and only the standard library.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from datetime import date
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import re
import sys
from tempfile import TemporaryDirectory
import zipfile


ROOT = Path(__file__).resolve().parents[1]
LOCAL = ROOT / "tensuhyo"
# 資料台帳の登録版。別の公開日の全件ファイルを同じ版として処理しない。
PUBLISHED_ON = date(2026, 11, 2)
DEFAULT_ARCHIVE = LOCAL / "master/2026-11-02/s_ALL20261102.zip"
ARCHIVE_SHA256 = "8f17cc03e2a2adab234bbe8162f11398706e6b5b3f0fda2073e5da35154ea7f2"
MEMBER = "s_ALL20261102.csv"
WIDTH = 150

INDEX_COLUMNS = (
    "診療行為コード", "区分", "項番", "章", "部", "告示等識別区分1", "告示等識別区分2",
    "点数識別", "新又は現点数", "入外適用区分", "包括対象検査", "検査等実施判断区分",
    "検査等実施判断グループ区分", "逓減対象区分", "上限回数", "上限回数エラー処理",
    "準用元区分", "準用元項番", "変更区分", "変更年月日", "廃止年月日", "基準日に使用可能",
    "省略漢字名称",
)


class MasterError(ValueError):
    """Invalid or unsupported input; never reinterpret it as a usable record."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise MasterError(message)


def _day(value: str, *, end: bool = False) -> date:
    if end and value == "99999999":
        return date.max
    require(bool(re.fullmatch(r"[0-9]{8}", value)), "年月日は8桁の数字で指定されていません")
    try:
        return date(int(value[:4]), int(value[4:6]), int(value[6:]))
    except ValueError as error:
        raise MasterError("暦にない年月日です") from error


def _division(alpha: str, number: str, branch: str) -> str | None:
    """区分番号と第1階層の枝番号。マスターは第2階層以降の枝番号を持たない。"""
    if not re.fullmatch(r"[A-Z]", alpha):
        return None
    return alpha + number + (f"-{int(branch)}" if branch != "00" else "")


@dataclass(frozen=True)
class Record:
    code: str
    name: str
    change: str
    point_kind: str
    points_text: str
    in_out: str
    bundle_group: int
    max_count: int
    max_count_handling: str
    judgment_kind: str
    judgment_group: int
    reduction: str
    notice_kind: str
    schedule_kind: str
    alpha: str
    chapter: int
    part: int
    number: str
    branch: str
    item: int
    ref_alpha: str
    ref_number: str
    ref_branch: str
    ref_item: int
    changed_on: date
    abolished_on: date

    @property
    def points(self) -> Fraction:
        return Fraction(self.points_text)

    @property
    def division(self) -> str | None:
        return _division(self.alpha, self.number, self.branch)

    @property
    def ref_division(self) -> str | None:
        return _division(self.ref_alpha, self.ref_number, self.ref_branch)

    def usable_on(self, day: date) -> bool:
        """この版の行が示す内容を、その日の診療に使えるか。変更前の内容は復元しない。"""
        require(self.change not in {"1", "9"}, "抹消・廃止の行から過去の内容は判定できません")
        return self.changed_on <= day <= self.abolished_on


def parse_row(row: list[str]) -> Record:
    """仕様説明書のファイルレイアウト（項番は1始まり）に従って1行を検査する。"""
    require(len(row) == WIDTH, f"列数が{WIDTH}ではありません")

    def cell(number: int, pattern: str) -> str:
        value = row[number - 1]
        require(bool(re.fullmatch(pattern, value)), f"項番{number}の値が仕様の形式と異なります")
        return value

    changed = _day(cell(87, r"[0-9]{8}"))
    abolished = _day(cell(88, r"[0-9]{8}"), end=True)
    require(changed <= abolished, "廃止年月日が変更年月日より前です")
    cell(2, "S")
    return Record(
        code=cell(3, r"1[0-9]{8}"),
        name=row[4],
        change=cell(1, r"[012359]"),
        point_kind=cell(11, r"[1345678]"),
        points_text=cell(12, r"[0-9]{1,7}\.[0-9]{2}"),
        in_out=cell(13, r"[012]"),
        bundle_group=int(cell(16, r"[0-9]{1,2}")),
        max_count=int(cell(36, r"[0-9]{1,3}")),
        max_count_handling=cell(37, r"[01]"),
        judgment_kind=cell(50, r"[012]"),
        judgment_group=int(cell(51, r"[0-9]{1,2}")),
        reduction=cell(52, r"[01]"),
        notice_kind=cell(68, r"[13579]"),
        schedule_kind=cell(69, r"[137]"),
        alpha=cell(85, r"[A-Z*-]"),
        chapter=int(cell(90, r"[0-9]")),
        part=int(cell(91, r"[0-9]{2}")),
        number=cell(92, r"[0-9]{3}"),
        branch=cell(93, r"[0-9]{2}"),
        item=int(cell(94, r"[0-9]{3}")),
        ref_alpha=cell(86, r"[A-Z]?"),
        ref_number=cell(97, r"[0-9]{3}"),
        ref_branch=cell(98, r"[0-9]{2}"),
        ref_item=int(cell(99, r"[0-9]{2}")),
        changed_on=changed,
        abolished_on=abolished,
    )


def parse_master(data: bytes) -> list[Record]:
    """配布時のバイト列（CP932・CRLF・ヘッダーなし）を全行検査して読む。"""
    require(b"\0" not in data, "NULを含むファイルは読みません")
    try:
        text = data.decode("cp932")
    except UnicodeDecodeError as error:
        raise MasterError("CP932として復号できません") from error
    reader = csv.reader(io.StringIO(text, newline=""), strict=True)
    records: list[Record] = []
    seen: set[str] = set()
    try:
        for line, row in enumerate(reader, 1):
            require(reader.line_num == line, f"{line}行: 複数行にまたがるレコードは扱いません")
            try:
                record = parse_row(row)
            except MasterError as error:
                raise MasterError(f"{line}行: {error}") from error
            require(record.code not in seen, f"{line}行: 診療行為コードが重複しています")
            seen.add(record.code)
            records.append(record)
    except csv.Error as error:
        raise MasterError(f"CSVとして読めません: {error}") from error
    require(bool(records), "レコードがありません")
    return records


def load_registered(archive: Path = DEFAULT_ARCHIVE, sha256: str = ARCHIVE_SHA256,
                    member: str = MEMBER) -> list[Record]:
    if not archive.is_file():
        raise MasterError(f"全件ファイルが見つかりません: {archive}")
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == sha256,
            "全件ファイルのSHA-256が登録版と異なります。公開日と取得元を確認してください。")
    with zipfile.ZipFile(archive) as bundle:
        require(bundle.namelist() == [member], "ZIP内のファイル構成が登録版と異なります")
        return parse_master(bundle.read(member))


def index_rows(records: list[Record], as_of: date) -> list[tuple]:
    """区分・項番・コード順の一覧。区分欄のない行（第3章、医療観察、食事等）は空欄にする。"""
    def text(day: date) -> str:
        return "99999999" if day == date.max else day.strftime("%Y%m%d")

    rows = [
        (r.code, r.division or "", r.item, r.chapter, r.part, r.notice_kind, r.schedule_kind,
         r.point_kind, r.points_text, r.in_out, r.bundle_group, r.judgment_kind,
         r.judgment_group, r.reduction, r.max_count, r.max_count_handling,
         r.ref_division or "", r.ref_item if r.ref_division else "", r.change,
         text(r.changed_on), text(r.abolished_on), int(r.usable_on(as_of)), r.name)
        for r in records
    ]
    return sorted(rows, key=lambda row: (row[1] == "", row[1], row[2], row[0]))


def coverage(records: list[Record], as_of: date, listed: list[str]) -> dict:
    """本文の区分見出しと、基準日に使用可能な行の区分欄とを突き合わせる。

    区分欄の一致は名称によらない対応の手がかりであり、項・注との対応や
    点数の一致は別に照合する。第2階層の枝番号を持つ区分は区分欄だけでは特定できない。
    """
    usable = [r for r in records if r.usable_on(as_of)]
    divisions = {r.division for r in usable if r.division}
    headings = set(listed)
    missing = sorted(headings - divisions)
    return {
        "as_of": as_of.isoformat(),
        "records": len(records),
        "usable": len(usable),
        "not_yet_effective": sorted(r.code for r in records if r.changed_on > as_of),
        "changed_in_this_edition": sorted(r.code for r in records if r.change != "0"),
        "without_division": sum(1 for r in usable if not r.division),
        "divisions": len(divisions),
        "headings": len(headings),
        "matched": len(headings & divisions),
        "headings_second_level_branch": [c for c in missing if c.count("-") >= 2],
        "headings_without_records": [c for c in missing if c.count("-") < 2],
        "divisions_without_heading": sorted(divisions - headings),
    }


def _write(path: Path, content: str) -> None:
    require(path.resolve() == path and path.is_relative_to(LOCAL) and path != LOCAL / "README.md",
            "出力先はGit管理外の tensuhyo 内に限ります")
    path.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=path.parent) as staging:
        tmp = Path(staging) / path.name
        tmp.write_text(content, encoding="utf-8", newline="")
        tmp.replace(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=DEFAULT_ARCHIVE, help="登録版の全件ZIP")
    parser.add_argument("--as-of", required=True, type=date.fromisoformat,
                        help="基準とする診療日 YYYY-MM-DD。公開日より後の日付は扱わない")
    args = parser.parse_args(argv)
    try:
        require(args.as_of <= PUBLISHED_ON, "公開日より後の変更はこの版から分かりません")
        records = load_registered(args.archive)
        out = io.StringIO(newline="")
        writer = csv.writer(out, delimiter="\t", lineterminator="\n")
        writer.writerow(INDEX_COLUMNS)
        writer.writerows(index_rows(records, args.as_of))
        index_path = LOCAL / "inventory" / "master-index.tsv"
        _write(index_path, out.getvalue())

        inventory = LOCAL / "inventory" / "fee-index.json"
        if inventory.is_file():
            rows = json.loads(inventory.read_text(encoding="utf-8"))["rows"]
            listed = [r["code"] for r in rows if r["status"] == "listed" and r["chapter"] in (1, 2)]
        else:
            listed = []
        report = coverage(records, args.as_of, listed)
        report["source"] = {"published_on": PUBLISHED_ON.isoformat(), "archive_sha256": ARCHIVE_SHA256}
        report_path = LOCAL / "inventory" / "master-coverage.json"
        _write(report_path, json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    except (MasterError, OSError, zipfile.BadZipFile, json.JSONDecodeError, KeyError) as error:
        parser.exit(1, f"マスター取込エラー: {error}\n")
    print(f"全{report['records']}行、{report['as_of']}に使用可能 {report['usable']}行、"
          f"未適用 {len(report['not_yet_effective'])}行、この版で異動 {len(report['changed_in_this_edition'])}行")
    if listed:
        print(f"本文の区分見出し {report['headings']} のうち区分欄が一致 {report['matched']}、"
              f"第2階層の枝番号 {len(report['headings_second_level_branch'])}、"
              f"該当行なし {len(report['headings_without_records'])}、"
              f"見出しのない区分欄 {len(report['divisions_without_heading'])}")
    else:
        print("本文の区分索引がないため、区分見出しとの突合せは省略しました（tools.fee_inventory を先に実行）")
    print(f"{index_path.relative_to(ROOT)}\n{report_path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
