"""版を固定した医科点数表と既存Leanの対応から、区分ごとの残作業表を生成する。"""

import csv
from pathlib import Path
from tempfile import TemporaryDirectory

from .draft_fee import DEFAULT_PDF, LOCAL, verified_pages
from .fee_coverage import coverage_for
from .fee_inventory import build_inventory


COLUMNS = ("章", "部", "節", "款", "種別", "識別子", "見出し（抽出行）", "PDF頁", "抽出行",
           "既存実装との対応", "主なLeanモジュール", "着手工程", "残作業")
STATUS = {"model": "個別モデルあり", "reference": "参照のみ", "new": "新規"}
OUTPATIENT_CASE = {"A000", "D000", "D005", "D007", "D026", "D208", "D400", "F400"}
INPATIENT_BUNDLES = {"D025", "D027", "E004"}


def work_stage(chapter: int, part: int | None, code: str = "") -> str:
    """作業を始める工程。一つの区分が関わる後続工程は実装計画側で扱う。"""
    if code in OUTPATIENT_CASE:
        return "2 外来の一症例"
    if code in INPATIENT_BUNDLES or (chapter, part) == (1, 2):
        return "4 出来高入院"
    if (chapter, part) == (1, 1) or (chapter == 2 and part in (1, 2, 3, 4, 5)):
        return "3 外来・在宅各部"
    if (chapter == 2 and part in range(6, 15)) or chapter in (3, 4):
        return "5 各部・章横断"
    raise ValueError(f"工程未割当 第{chapter}章 第{part}部 {code}")


def backlog_rows(inventory: dict) -> list[tuple]:
    rows = []

    def append(row, kind, key, status, module, stage, task):
        rows.append((row["chapter"], row["part"], row["section"], row["subsection"],
                     kind, key, row["heading"], row["page"], row["line"],
                     status, module, stage, task))

    for row in inventory["rows"]:
        code = row["code"]
        if row["status"] in ("deleted", "deleted_group"):
            kind = "削除" if row["status"] == "deleted" else "一括削除表記"
            append(row, kind, code, "削除表記", "", "1 版・条項確認",
                   "旧版・経過措置から参照される場合に、対象時点の規定を確認する。")
        elif row["status"] == "listed":
            coverage = coverage_for(code, row["chapter"])
            append(row, "区分", code, STATUS[coverage.status], coverage.module,
                   work_stage(row["chapter"], row["part"], code), coverage.remaining)
        else:
            raise ValueError(f"未対応の区分状態 {code} {row['status']}")

    for row in inventory["noncode_rows"]:
        chapter, part = row["chapter"], row["part"]
        key = f"第{chapter}章" + (f"第{part}部" if part is not None else "") + f"第{row['number']}項"
        task = ("併設・非併設の適用、準用先、給付調整を照合する。" if chapter == 3
                else "適用日、入院履歴、旧規定と現行区分の関係を照合する。")
        append(row, "番号のない区分・経過措置", key, "新規", "",
               work_stage(chapter, part), task)

    for row in inventory["divisions"]:
        if row["level"] == "章" and row["chapter"] == 3:
            append(row, "章前文", "第3章前文", "新規", "", work_stage(3, None),
                   "章の適用対象と、第1部・第2部への振分けを形式化する。")

    for row in inventory["general_rules"]:
        key = f"通則 p{row['page']} l{row['line']}"
        append(row, "通則見出し", key, "条項別に要照合", "", "1 版・条項確認",
               "各号・ただし書を識別し、支配する区分と既存の通則モデルを結ぶ。")

    return sorted(rows, key=lambda r: (r[7], r[8]))


def main() -> None:
    inventory = build_inventory(verified_pages(DEFAULT_PDF))
    rows = backlog_rows(inventory)
    folder = LOCAL / "inventory"
    if folder.resolve() != folder:
        raise ValueError("保存先は tensuhyo/inventory 内に限ります。")
    folder.mkdir(exist_ok=True, parents=True)
    path = folder / "medical-backlog.tsv"
    with TemporaryDirectory(dir=folder) as temp:
        tmp = Path(temp) / path.name
        with tmp.open("w", encoding="utf-8", newline="") as out:
            writer = csv.writer(out, delimiter="\t", lineterminator="\n")
            writer.writerow(COLUMNS)
            writer.writerows(rows)
        tmp.replace(path)
    print(f"{len(rows)}行 {path}")


if __name__ == "__main__":
    main()
