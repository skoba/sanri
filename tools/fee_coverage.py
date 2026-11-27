"""Map an R8 primary-schedule heading to evidence in the public Lean models.

Keys are whole fee divisions, including suffixes. A model entry means that at
least part of the division has its own calculation. It does not certify source
review, all items, applicability on a given date, or an equivalence proof.
Reference entries record identified cross-references or externally priced inputs.
The authoritative inventory of active headings is supplied by the caller.
"""

import re
from collections import defaultdict
from dataclasses import dataclass


@dataclass(frozen=True)
class Coverage:
    status: str
    module: str
    remaining: str


# Register exact numbers: an implementation for a parent or neighbour does not
# automatically cover a newly inserted branch. Descriptions refer to our code.
_GROUPS = [
    ("model", "InitialConsultation", "A000", "施設届出の限定事例と初診料本体の各条件を結び、条項別に検証する"),
    ("model", "RevisitConsultation", "A001", "各注の条件、同日・月内履歴と診療形態を条項別に検証する"),
    ("model", "OutpatientConsultation", "A002", "包括項目を検査・処置の本体モデルと接続し、各注を検証する"),
    ("model", "SpecificDiseaseManagement", "B000", "施設・指定疾患・期間の外部入力と包括先の条項を照合する"),
    ("model", "UrineFecalTests", "D000 D001 D002 D002-2 D003",
     "検体・実施場所・準用先に関する該当条件を項ごとに照合する"),
    ("model", "SpecimenRules",
     "D009 D010 D011 D012 D013 D014 D015 D016 D017 D018 D019 D019-2 D020 D021 D022 D023 D023-2",
     "SpecimenCatalogの項・枝・検査種類と算定規則を原文へ対応付け、包括・施設要件を照合する"),
    ("model", "SpecimenJudgment", "D026", "外来モデルを入院限定加算とD027の算定へ接続する"),
    ("model", "Cardiorespiratory",
     "D200 D201 D202 D203 D204 D205 D206 D207 D208 D209 D210 D210-2 D210-3 D210-4 "
     "D211 D211-2 D211-3 D211-4 D212 D212-2 D213 D214 D214-2",
     "実施単位、同月の減額、加算・包括について各区分に適用される条件を検証する"),
    ("model", "UltrasoundMonitoring",
     "D215 D215-2 D215-3 D215-4 D216 D216-3 D217 D218 D219 D220 D221-2 D222 D222-2 "
     "D223 D223-2 D224 D225 D225-2 D225-3 D225-4 D226 D227 D228 D229 D230 D231 D231-2 D232 D233 D234",
     "日次・一連・期間上限と包括を該当する条項ごとに検証する"),
    ("model", "UltrasoundMonitoring", "D216-2",
     "CaseStudies/ResidualUrineの月上限・同日制約の証明に、対象疾患等の前提と改訂履歴のレビューを加える"),
    ("model", "SpecimenCollection",
     "D400 D401 D402 D403 D404 D404-2 D405 D406 D406-2 D407 D408 D409 D409-2 D410 D411 "
     "D412 D412-2 D412-3 D413 D414 D414-2 D415 D415-2 D415-3 D415-4 D415-5 D415-6 D416 D417 D418 D419 D419-2",
     "診断穿刺・採取の単位、手術・処置との関係、各注を原文と照合する"),
    ("model", "ExaminationDrugsMaterials", "D500 D600", "価格の適用版と計算式の前提を検証する"),
    ("model", "NuclearMedicine", "E100 E101 E101-2 E101-3 E101-4 E101-5 E102",
     "同一アイソトープ・一連・施設要件・診断の月上限を該当する条項と照合する"),
    ("model", "ComputedTomography", "E200 E200-2 E201 E202 E203",
     "各入力の根拠を確認し、主撮影・月内減額・施設要件と加算の適用順を検証する"),
    ("model", "ImagingDrugsMaterials", "E300 E400 E401", "価格の適用版と薬剤・フィルム・材料の各計算式を検証する"),
    ("model", "MedicalFee", "F400", "PrescriptionFeeの各条件を原文・参照先の加算・施設基準と照合する"),
    ("reference", "MedicalFee", "A250 B008-2", "F400の併算定制約から参照される区分本体を形式化する"),
    ("reference", "MedicalManagement", "A254 I012", "医学管理通則から参照される施設基準・加算と区分本体を形式化する"),
    ("reference", "SpecificDiseaseManagement", "B001",
     "B000の包括先や検査との併算定で参照される項を含め、項別の算定を形式化する"),
    ("reference", "MedicalManagement", "B001-2 B001-2-7 B001-2-8 B001-2-9 B001-2-11 B001-2-12 B006 B007-2",
     "医学管理通則の感染対策加算の対象として識別済みの項目に、個別料金と要件を追加する"),
    ("reference", "MedicalManagement", "B200", "第3節材料の外部点数を、区分固有の算定式と接続する"),
    ("reference", "SpecimenJudgment",
     "D004-2 D006-2 D006-3 D006-4 D006-5 D006-6 D006-7 D006-8 D006-9 "
     "D006-11 D006-12 D006-13 D006-14 D006-15 D006-16 D006-17 D006-18 D006-19 D006-20 "
     "D006-22 D006-23 D006-24 D006-25 D006-26",
     "D026の遺伝子判断料への振分けとは別に、実施料の項別算定を追加する"),
    ("model", "D006PlasmaPanel", "D006-27", "組織検査等との併施調査を既存の実施記録と結ぶ"),
    ("model", "D006Late", "D006-28 D006-29 D006-30 D006-31", "施設基準と指針の参照を解決する"),
    ("model", "D008", "D008", "適格な検体・併施選択から上位通則への接続を検証する"),
    ("reference", "Examinations", "D025", "特定機能病院の入院検査で入力する基本実施料を形式化する"),
    ("reference", "SpecimenJudgment", "D027", "D026が参照する入院判断料の本体と加算を形式化する"),
    ("reference", "PhysiologicalExaminations",
     "D235 D235-2 D235-3 D236 D236-2 D236-3 D237 D237-2 D237-3 D238 D239 D239-2 D239-3 "
     "D239-4 D239-5 D240 D241 D242 D306 D308 D310 D312 D313 D317 D325",
     "年齢加算の通則に渡す所定点数と各区分の注を形式化する"),
    ("reference", "NuclearMedicine", "D292 D293", "核医学の主検査選択で参照する個別検査の算定を追加する"),
    ("reference", "Xray", "E000 E001 E002 E003",
     "エックス線通則に渡す点数、例外となる項・注を区分ごとに形式化する"),
    ("reference", "Xray", "E004", "特定機能病院の入院時に未解決としている基本診断料を形式化する"),
    ("reference", "Medication", "F000 F100 F200 F300 F500", "投薬通則に入力する個別点数の算定規則を追加する"),
    ("reference", "OutpatientConsultation",
     "J000 J053 J060 J072 J086 J089 J095 J096 J097 J098 J099 J114 J115 J118 J119",
     "A002の包括判定に対応する処置の個別要件と料金を形式化する"),
    ("reference", "UltrasoundMonitoring", "J045 L008", "監視検査等との包括・例外で参照する個別料金を形式化する"),
    ("reference", "SpecimenRules", "K867 K867-3 K867-4 K898", "検査の既往・対象手術として参照する手術本体を形式化する"),
]

_NEW = Coverage("new", "", "区分の項・枝・注と上位通則を抽出し、出典付きの制約を新設する")


def _index() -> dict[tuple[int, str], Coverage]:
    result = {}
    for status, module, codes, remaining in _GROUPS:
        coverage = Coverage(status, f"Sanri/{module}.lean", remaining)
        for code in codes.split():
            # Each reviewed model above belongs to the main schedule (chapters 1 and 2).
            key = (1 if code.startswith("A") else 2, code)
            if key in result:
                raise ValueError(f"区分の実装対応が重複しています: {key}")
            result[key] = coverage
    return result


_INDEX = _index()


def coverage_for(code: str, chapter: int,
                 modules: dict[tuple[int, str], set[str]] | None = None) -> Coverage:
    """Look up an exact canonical heading in the specified chapter, including homonyms."""
    key = (chapter, code)
    if modules and key in modules:
        return Coverage("source", "・".join(sorted(modules[key])),
                        "出典付き制約を項・注・通知の索引と照合し、未対応条項を確認する")
    return _INDEX.get(key, _NEW)


_KIND_PREFIX = {"primaryText": "primary", "notification": "notice", "clarification": "clarification"}


def clause_paths(rule: dict) -> list[tuple[str, ...]]:
    """構造化IDを正規化し、複合IDと項の範囲を展開する。"""
    identifier = rule["id"]
    if rule.get("classification") == "parameterized" or identifier.startswith("unclassified/"):
        return []
    expected = _KIND_PREFIX.get(rule.get("kind"))
    result = []
    for reference in identifier.split("+"):
        parts = tuple(reference.split("/"))
        if not expected or parts[0] != expected:
            raise ValueError(f"出典種別と条項IDが対応しません: {identifier}")
        division = r"[A-Z][0-9]{3}(?:-[0-9]+)*"
        number = r"[1-9][0-9]*"
        kana = r"[a-z]+"
        patterns = {
            "primary": (rf"{division}/(?:heading|item/{number}(?:/{kana}|/note(?:/{number}(?:/{kana})?)?)?|note/(?:{number}(?:/{kana})?|{kana}|unnumbered/{number}))",
                        rf"ch{number}-part{number}(?:-section{number})?(?:-subsection{number})?/general/(?:{number}(?:/{kana})?|unnumbered)"),
            "notice": (rf"{division}/paragraph/(?:{number}(?:/{kana}(?:/{number}|/{kana}(?:/{number})?)?)?|unnumbered)",
                       rf"ch{number}-part{number}(?:-section{number})?(?:-subsection{number})?/(?:general|emergency|rapid)/{number}(?:/{number}(?:/{kana}(?:/{kana})?)?)?"),
            "clarification": (rf"[a-z0-9-]+/question/{number}",),
        }
        tail = "/".join(parts[1:])
        if parts[0] == "primary" and (match := re.fullmatch(
            rf"({division})/item/({number})\.\.({number})", tail
        )):
            first, last = int(match[2]), int(match[3])
            if first > last:
                raise ValueError(f"条項IDの項範囲が逆順です: {reference}")
            result.extend(("primary", match[1], "item", str(i)) for i in range(first, last + 1))
        elif any(re.fullmatch(pattern, tail) for pattern in patterns[parts[0]]):
            result.append(parts)
        else:
            raise ValueError(f"条項IDの形式が異なります: {reference}")
    return result


def source_modules(rules: list[dict]) -> dict[tuple[int, str], set[str]]:
    result = defaultdict(set)
    for rule in rules:
        for kind, code, *_ in clause_paths(rule):
            if kind in {"primary", "notice"} and code[0].isupper():
                result[(1 if code.startswith("A") else 2, code)].add(
                    rule["module"].replace(".", "/") + ".lean"
                )
    return dict(result)
