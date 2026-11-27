"""原本頁と既存の制約を突き合わせた検体検査の特例レビュー。"""

# 区分、項目、回数単位を固定する。集約先が同じ別の検査種類は個別に同定する。
FREQUENCY = {
    ("D003", "calprotectin", "144"): ("4/i", "333–334", "D003.monitoringRule", "医学的必要性による月次経路"),
    ("D004", "amyloidRatio", "53"): ("13/a", "334–335", "D004.amyloidClaimLimit", "投与中止後の再開条件"),
    ("D004", "phosphoTauAmyloidRatio", "53"): ("13/a", "334–335", "D004.amyloidClaimLimit", "投与中止後の再開条件"),
    ("D004", "cxcl10", "147"): ("15", "2", "D004.cxcl10Rule", "医学的必要性による年内追加"),
    ("D006", "plateletDifferential", "53"): ("10/a", "340", "D006.plateletDifferentialRule", "医学的必要性による反復"),
    ("D006-5", "fish", "53"): ("3", "344", "D006Chromosome.FishFrequency", "対象疾患の診断確定前の追加"),
    ("D006-11", "fip1l1Pdgfra", "53"): ("1", "345", "D006GeneTests.Fusion.Eligible", "所見変化による治療再選択"),
    ("D006-14", "flt3", "53"): ("1", "345–346", "D006Oncology.Flt3.Indication", "治療再選択時の追加"),
    ("D006-22", "plasmaRas", "53"): ("1", "349–350", "D006Targeted.PlasmaRas.Indication", "治療再選択時の追加"),
    ("D006-29", "breastRecurrence", "53"): ("1", "355", "D006Late.breastRule", "医学的必要性による反復"),
    ("D007", "mdaLdl", "144"): ("39", "359", "BloodChemistryLate.rules", "術前に独立した経路"),
    ("D007", "vitaminD125", "144"): ("50", "360", "BloodChemistryLate.rules", "治療初月と以後の枠"),
    ("D007", "vitaminD25", "144"): ("24/i", "357", "BloodChemistryAdditional.vitaminDDeficiencyRule", "診断時と以後の枠"),
    ("D007", "totalCarnitine", "146"): ("17/i", "356–357", "BloodChemistryFurther.CarnitineContext.eligible", "適応別の月次経路"),
    ("D007", "freeCarnitine", "146"): ("17/i", "356–357", "BloodChemistryFurther.CarnitineContext.eligible", "適応別の月次経路"),
    ("D008", "ucOc", "146"): ("11", "362", "D008.ucOcRule", "治療前と治療後の枠"),
    ("D008", "ntx", "146"): ("12", "362", "D008.ntxDpdRule", "診療目的・治療変更別の枠"),
    ("D008", "tracp5b", "146"): ("15", "362–363", "D008.tracpRule", "治療前・経過観察・治療変更別の枠"),
    ("D008", "urineBetaCtx", "146"): ("17", "363", "D008.urineBetaCtxRule", "治療前と治療後の枠"),
    ("D008", "betaCtx", "146"): ("18", "363", "D008.betaCtxRule", "治療前と治療後の枠"),
    ("D009", "3", "53"): ("1/e", "364–365", "D009.exceptionE", "別算定を認める診療目的"),
    ("D009", "8", "53"): ("1/a", "364–365", "D009.exceptionA", "別算定を認める診療目的"),
    ("D009", "2", "53"): ("1/i", "364–365", "D009.exceptionI", "診療目的別の月次経路"),
    ("D009", "10", "53"): ("1/i", "364–365", "D009.exceptionI", "診療目的別の月次経路"),
    ("D009", "11", "53"): ("1/u", "364–365", "D009.exceptionU", "診断・治療前後の枠"),
    ("D009", "28", "53"): ("1/u", "364–365", "D009.exceptionU", "診断・治療前後の枠"),
    ("D009", "9", "53"): ("4", "365", "D009.psaRule", "確定診断に至らない場合の追加"),
    ("D009", "31", "53"): ("20/i", "367", "D009.s23Repeat", "確定診断に至らない場合の追加"),
    ("D009", "32", "53"): ("21/i", "367", "D009.phiRepeat", "確定診断に至らない場合の追加"),
    ("D012", "toxoplasmaAvidity", "141"): ("56", "378", "D012.toxoplasmaAvidityRule", "医学的必要性による一連内の追加"),
    ("D012", "aav9", "53"): ("62", "378–379", "D012.aav9Rule", "医学的必要性による反復"),
    ("D012", "aavRh74", "53"): ("63", "379", "D012.aavRh74Rule", "医学的必要性による反復"),
    ("D014", "rnaPolymerase", "144"): ("4", "380", "D014.rnaPolymerase", "初回陽性後の目的別の枠"),
    ("D014", "hlaIdentify", "147"): ("32", "383", "D014.hlaIdentify", "経過観察・治療後の年内の枠"),
    ("D015", "sfltPlgf", "149"): ("14/i", "385", "D015.pregnancyClinical", "一妊娠のリスク別の例外"),
}

# 告示項に集約される検査種類を、ローカルの原本レビューで固定する。
VARIANTS = {
    "tumor_reselection": ("D004-2", "drugAid", "53",
        ("1", "335", "D004Tumor.GeneFrequency", "再発・増悪時の治療再選択")),
    "sars_repeat": ("D023", "viralOrMethicillinGroup", "53",
        ("23/u", "392", "D023.sarsIndication", "発症後の条件を満たす場合の追加")),
    "hbv_purpose": ("D023", "viralOrMethicillinGroup", "53",
        ("21/i", "392", "D023.hbvAcute", "急性期の一回枠と慢性期の適格条件")),
}

SIMULTANEOUS = {
    "primary/D017/note/unnumbered/1": (
        ("primary/D017/note/unnumbered/1", "notice/D017/paragraph/3"), "188–189, 386",
        "SpecimenCrossDivision.sedimentBacteriaGroup", "同一検体の場合の主検査と別検体の同日記載"),
    "notice/D005/paragraph/3": (
        ("notice/D005/paragraph/3",), "338", "BloodMorphology.eosinophilRule", "同一検体での併施に限定"),
    "notice/D005/paragraph/7": (
        ("notice/D005/paragraph/7",), "338", "BloodMorphology.malariaRule", "同一診療目的で併施した場合の主検査"),
    "notice/D007/paragraph/26": (
        ("notice/D007/paragraph/26",), "357", "BloodChemistryFurther.Pair.rule", "相手の測定目的と検体を限定した併施"),
    "notice/D012/paragraph/36": (
        ("notice/D012/paragraph/36",), "374–375", "D012.glucanRule", "二病態の併存を疑う場合の例外"),
    "notice/D014/paragraph/23/i": (
        ("notice/D014/paragraph/23/i",), "382", "D014.skinComboChoice", "鑑別診断目的で併測した場合の主検査"),
}

CULTURE_PROJECTIONS = {
    "gonococcus": (("notice/D023/paragraph/2/a",), "388",
                    "D023.gonococcusChoice", "培養の対象を通知指定の感染疑いに限定"),
    "gonococcusTrachomatis": (("notice/D023/paragraph/5/a",), "389",
                             "D023.combinedGenitourinaryIndication", "培養の対象を通知指定の感染疑いに限定"),
}


def simultaneous_review(row, mapping):
    clauses = row.get("clauses", [])
    if row["structure"] != "両端対応済み":
        return None
    points = [mapping[code]["lean"] for code in row["codes"]]
    keys = [(point["division"], point["item"].rsplit(".", 1)[-1]) for point in points]
    by_division = dict(keys)
    direction = row["direction"]
    if direction == "3":
        if set(by_division) == {"D018", "D023"}:
            return CULTURE_PROJECTIONS.get(by_division["D023"])
        if set(clauses) == {"notice/D014/paragraph/16/i", "notice/D014/paragraph/19/i"}:
            return (tuple(clauses), "381–382", "D014.vulgarisChoice / D014.foliaceusChoice",
                    "病態別の経過観察で併測した場合の主検査")
        if set(keys) == {("D023", "hcvDetection"), ("D023", "hcvQuantity")}:
            return (("notice/D023/paragraph/9/i",), "390", "D023.hcvDetectionIndication",
                    "治療法選択と治療経過観察で条件が異なる")
        if len(clauses) == 1:
            return SIMULTANEOUS.get(clauses[0])
    if direction not in {"1", "2"}:
        return None
    preferred, excluded = keys[int(direction) - 1], keys[2 - int(direction)]
    if preferred[0] == "D018" and excluded == ("D018", "simple") and preferred != excluded:
        return (("notice/D018/paragraph/1/u",), "387", "D018.perSpecimen",
                "同一検体で通常培養を優先")
    if preferred == ("D007", "bloodGas") and excluded == ("D007", "bicarbonate"):
        return (("notice/D007/paragraph/12",), "356", "BloodChemistryFurther.Pair.rule",
                "同一検体で血液ガス分析を優先")
    return None


def frequency_review(key, row, selected):
    if row["limit"] != 1 or not row["special"]:
        return None
    signature = (*key, row["unit"])
    review = FREQUENCY.get(signature)
    variant = VARIANTS.get(selected)
    if variant and signature == variant[:3]:
        review = variant[3]
    if key == ("D006-7", "ugtPolymorphism"):
        return {"reason_type": "通知に通常上限あり・追加条件未特定",
                "clauses": ["notice/D006-7/paragraph/unnumbered"], "pdf_pages": "344"}
    if not review:
        return None
    clause, pages, definition, condition = review
    clauses = [f"notice/{key[0]}/paragraph/{clause}"]
    if selected == "hbv_purpose":
        clauses.append("notice/D023/paragraph/21/u")
    source = "保医発0930第2号別添1" if key == ("D004", "cxcl10") else "保医発0305第6号別添1"
    return {"classification": "表現の差", "reason_type": "通知の例外・目的別の枠とコード別枠の差",
            "reason": condition, "clauses": clauses, "pdf_pages": pages, "review_source": source,
            "lean_definition": definition, "unreadable": ["電子表の特例発動条件"]}


def review_remaining(tables, mapping, variants):
    for row in tables["frequency"]:
        if row["classification"] != "情報不足で判定できない":
            continue
        code = row["codes"][0]
        entry = mapping[code]
        point = entry["lean"]
        if point is None:
            row["mapping_reason_type"] = entry["reason_type"]
            continue
        key = (point["division"], point["item"].rsplit(".", 1)[-1])
        if details := frequency_review(key, row, variants.get(code)):
            row.update(details)
        elif row["reason_type"] == "対応する条項・適用単位未確認":
            row["review_reason_type"] = ("回数単位と適用範囲の対応未確定"
                                        if key[0] in {"D011", "D414", "D006-21"} else "当該上限の根拠条項未特定")
        elif row["special"]:
            row["review_reason_type"] = "通常枠と通知の例外の個別対応未確定"

    for row in tables["exclusion_simultaneous"]:
        if row["classification"] != "情報不足で判定できない" or not row["special"]:
            continue
        if row["reason_type"].startswith("対象範囲外"):
            continue
        clauses = row.get("clauses", [])
        review = simultaneous_review(row, mapping)
        if review:
            ids, pages, definition, condition = review
            row.update(classification="表現の差", reason_type="通知・告示で限定した適用条件との射影差",
                       reason=condition, clauses=list(ids), pdf_pages=pages, lean_definition=definition,
                       unreadable=["電子表の特例発動条件"])
        else:
            divisions = {mapping[code]["master"]["区分"] for code in row["codes"] if code in mapping}
            if divisions == {"D012"}:
                row["review_candidates"] = ["notice/D012/paragraph/36"]
                row["review_reason_type"] = "通知の列挙相手同士に背反を定める条項未特定"
            elif divisions == {"D005"}:
                row["review_candidates"] = ["notice/D005/paragraph/2", "notice/D005/paragraph/3"]
                row["review_reason_type"] = "測定方式間の背反を定める条項未特定"
            elif divisions == {"D007"}:
                row["review_candidates"] = ["notice/D007/paragraph/26"]
                row["review_reason_type"] = "相手コードと通知指定の測定目的の対応未確定"
            else:
                row["review_reason_type"] = ("条項候補あり・特例又は優先方向の根拠未確定" if clauses else
                                             "両端の対応未確定" if row["structure"] != "両端対応済み" else
                                             "特例を与える条項未特定")
