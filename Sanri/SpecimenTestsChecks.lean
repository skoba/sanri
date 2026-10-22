import Sanri.SpecimenRules

namespace Sanri.MedicalFee.SpecimenTests

private def req (code : Code) (number : Nat) : Request := { code := code, number := number }
private def tumor (number : Nat) : Request :=
  { code := .d009
    number := number
    conditions := { malignancyStronglySuspectedFromCareAndNonMarkerTests := true } }
private def rapid (number variant : Nat) : Request :=
  { code := .d023
    number := number
    variant := variant
    conditions := { resultsExplainedOnTestDay := true, writtenResultsProvided := true } }
private def counted (code : Code) (number count : Nat) : List Request :=
  (List.range count).map (fun id => { code := code, number := number, analyteId := id })

-- 追記で確定した点数と、未収載区分の扱い。
example : (lookup .d014 7).bind Entry.points = some 110 := by decide
example : (lookup .d016 7 1).bind Entry.points = some 345 := by decide
example : assessOne (tumor 1) = some (.charged 80 0) := by decide
example : assessOne (req .d012 18) = some (.charged 121 0) := by decide
example : assessOne { code := .d010, number := 8, branch := 4, conditions := { facilityNotified := true, performedInsideInstitution := true } } =
    some (.charged 1074 0) := by decide
example : points [req .d015 1, req .d012 18] = some 137 := by decide
example : assess [req .d015 1, req .d012 71] = some (.missingSource [(.d012, 71, 0)]) := by decide
example : (lookup .d012 70).bind Entry.points = some 12850 := by decide
example : (lookup .d014 49).bind Entry.points = some 4850 := by decide
example : (lookup .d023 27).bind Entry.points = some 2000 := by decide
example : (lookup .d023 10).bind Entry.points = some 347 := by decide
example : assessOne { code := .d012, number := 56, variant := 3 } = none := by decide

-- Ｄ００９：元の点数より低い場合も包括点数へ置換する。
example : points [tumor 13] = some 140 := by decide
example : points [tumor 13, tumor 14] = some 230 := by decide
example : points [tumor 13, tumor 14, tumor 15] = some 290 := by decide
example : points [tumor 13, tumor 14, tumor 15, tumor 16] = some 385 := by decide
example : points [tumor 13, tumor 13] = some 140 := by decide
example : points [req .d009 13] = none := by decide
example : points [{ tumor 13 with conditions := {
    malignancyStronglySuspectedFromCareAndNonMarkerTests := true, claimsB001_3 := true } }] = none := by decide
example : points [{ tumor 13 with conditions := {
    malignancyStronglySuspectedFromCareAndNonMarkerTests := true, tumorMarkerAlreadyClaimed := true } }] =
    none := by decide

-- Ｄ０１３：項１・２を包括の数に含めず、採血１回ごとに計算する。
example : points [req .d013 3, req .d013 4] = some 186 := by decide
example : points [req .d013 3, req .d013 4, req .d013 5] = some 290 := by decide
example : points [req .d013 3, req .d013 4, req .d013 5, req .d013 6] = some 360 := by decide
example : points [req .d013 3, req .d013 4, req .d013 5, req .d013 6, req .d013 7] = some 425 := by decide
example : points [req .d013 1, req .d013 2, req .d013 3] = some 149 := by decide
example : points [req .d013 3, req .d013 4, { req .d013 5 with collectionId := 1 }] = some 288 := by decide
example : points [req .d014 10, req .d014 11] = some 320 := by decide
example : points [req .d014 10, req .d014 11, req .d014 12] = some 490 := by decide
example : points [req .d014 10, req .d014 17] = some 295 := by decide
example : points [req .d014 10, { req .d014 11 with collectionId := 1 }] = some 320 := by decide

example : points (counted .d012 11 9) = some 632 := by decide
example : points (counted .d012 46 3) = some 400 := by decide
example : points (counted .d015 13 12) = some 1320 := by decide
example : points (counted .d015 13 13) = some 1430 := by decide
example : points (counted .d015 13 14) = some 1430 := by decide
example : points (counted .d015 13 14 ++
    (counted .d015 13 14).map (fun r => { r with collectionId := 1 })) = some 2860 := by decide

-- 同じ項番号でも対象検査だけに基準・加算を適用する。
example : points [req .d012 56] = none := by decide
example : points [{ req .d012 56 with variant := 2 }] = some 233 := by decide
example : points [{ req .d012 56 with conditions := { facilityStandardMet := true } }] = some 233 := by decide
example : points [req .d012 70] = none := by decide
example : points [{ req .d012 70 with conditions := { facilityNotified := true } }] = some 12850 := by decide
example : points [req .d014 47] = none := by decide
example : points [{ req .d014 49 with conditions := { facilityNotified := true } }] = some 4850 := by decide
example : points [req .d011 4] = none := by decide
example : points [{ req .d011 4 with conditions := { surgery := .k898EtcWithinPart10Section11 } }] =
    some 174 := by decide
example : points [{ code := .d010, number := 4, branch := 1, quantity := 4 }] = some 1116 := by decide
example : points [{ code := .d010, number := 4, branch := 2, quantity := 5 }] = some 1074 := by decide
example : points [{ code := .d010, number := 4, branch := 1, quantity := 5 }] = none := by decide
example : points [{ code := .d010, number := 8, branch := 1, conditions := { facilityNotified := true } }] = some 1141 := by decide
example : points [{ code := .d010, number := 8, branch := 1, conditions := { facilityNotified := true, claimsThisMonth := 1 } }] = none := by decide
example : points [{ code := .d016, number := 7, branch := 3, quantity := 3 }] = some 700 := by decide
example : points [req .d016 4, { req .d016 4 with collectionId := 1, analyteId := 1 }] = some 200 := by decide
example : points [req .d021 1, { req .d021 1 with collectionId := 1, analyteId := 1 }] = some 376 := by decide
example : points [{ req .d022 1 with quantity := 3 }] = none := by decide
example : points [{ req .d022 1 with quantity := 4 }] = some 415 := by decide

example : points [{ req .d017 1 with conditions := { concentrationSmear := true } }] = some 100 := by decide
example : points [{ req .d017 3 with conditions := { concentrationSmear := true } }] = some 67 := by decide
example : points [{ req .d018 1 with conditions := {
    generalCulture := true, anaerobicCulture := true, fungalCulture := true } }] = some 439 := by decide
example : points [{ req .d018 1 with conditions := {
    anaerobicCulture := true, fungalCulture := true } }] = some 180 := by decide
example : points [{ req .d018 1 with conditions := {
    massSpectrometricIdentification := true } }] = some 180 := by decide
example : points [{ req .d018 1 with conditions := {
    inpatient := true, massSpectrometricIdentification := true } }] = some 220 := by decide
example : points [{ req .d023 18 with conditions := {
    ultracentrifugalConcentration := true } }] = some 650 := by decide
example : points [rapid 6 0] = some 391 := by decide
example : points [rapid 6 1] = some 291 := by decide
example : points [rapid 13 0] = some 460 := by decide
example : points [rapid 13 1] = some 360 := by decide
example : points [rapid 13 2] = some 460 := by decide
example : points [rapid 14 0] = some 410 := by decide
example : points [rapid 14 1] = some 510 := by decide
example : points [{ rapid 7 0 with conditions := { resultsExplainedOnTestDay := true } }] = some 296 := by decide
example : points [req .d023 10] = none := by decide
example : points [{ req .d023 10 with conditions := {
    facilityNotified := true, ascUsCytology := true } }] = some 347 := by decide
example : points [{ req .d023 11 with conditions := {
    facilityNotified := true, historyK867_4 := true } }] = some 347 := by decide
example : points [{ req .d023 24 with conditions := { facilityNotified := true } }] = none := by decide
example : points [{ req .d023 24 with conditions := {
    facilityNotified := true, designatedPatient := true } }] = some 1273 := by decide
example : points [{ req .d023 26 with conditions := { facilityStandardMet := true } }] = some 1700 := by decide
example : points [{ req .d023 26 with variant := 1, conditions := { facilityStandardMet := true } }] = none := by decide
example : points [{ req .d023 26 with variant := 1, conditions := { facilityStandardMet := true, facilityNotified := true } }] = some 1700 := by decide
example : points [req .d023_2 5] = none := by decide
example : points [{ req .d023_2 5 with conditions := { facilityStandardMet := true } }] = some 450 := by decide

example : assessSedimentPair
    { item := .urineSedimentMicroscopy, performedInsideInstitution := true }
    (req .d017 3) .urineSediment =
    some (.charged ⟨27, 0⟩, .suppressedByMainUrineSediment) := by decide
example : assessSedimentPair
    { item := .urineSedimentFlowCytometry, performedInsideInstitution := true }
    (req .d017 3) .d017BacterialMicroscopy =
    some (.onlyMainD017, .charged 67 0) := by decide

example : assessUrineByReference { item := .specialUrine .proteinImmunology }
    [req .d015 7] = some (.charged ⟨60, 0⟩) := by decide
example : assessUrineByReference { item := .specialUrine (.other .d009) }
    [tumor 13, tumor 14] = some (.charged ⟨230, 0⟩) := by decide
example : assessUrineByReference { item := .specialUrine (.other .d009) }
    [req .d009 13] = none := by decide
example : assessUrineByReference { item := .specialUrine (.other .d009) }
    [req .d015 7] = none := by decide
example : assessUrineByReference { item := .specialUrine (.other .d010) }
    [{ code := .d010, number := 8, branch := 4, conditions := { facilityNotified := true, performedInsideInstitution := true } }] =
    some (.charged ⟨1074, 0⟩) := by decide
example : Examinations.executionPoints {
    items := [executionItem [{ members := [], base := 230, additions := 0 }] 9] } = some 230 := by decide

-- Ｄ００９の１は注２の包括対象外。２〜36は通常点数より高くても置換する。
example : points [tumor 2, tumor 3] = some 230 := by decide
example : points [tumor 1, tumor 2, tumor 3] = some 310 := by decide
example : points [tumor 1, tumor 2] = some 178 := by decide
example : points [tumor 2, tumor 3, tumor 4] = some 290 := by decide
example : points [tumor 2, tumor 3, tumor 4, tumor 5] = some 385 := by decide
example : points [{ tumor 6 with variant := 1 }] = some 112 := by decide
example : points [{ tumor 12 with variant := 1 }] = some 139 := by decide
example : assessOne { code := .d010, number := 8, branch := 4, conditions := { facilityNotified := true } } = none := by decide
example : assessOne { code := .d010, number := 8, branch := 4, conditions := { performedInsideInstitution := true } } = none := by decide
example : assessOne { code := .d010, number := 8, branch := 4, conditions := { facilityNotified := true, performedInsideInstitution := true, claimsThisMonth := 1 } } = none := by decide
set_option maxRecDepth 2048 in
example : catalog.length = 287 := by decide
set_option maxRecDepth 2048 in
example : catalog.all (fun e => e.points.isSome) = true := by decide

-- Ｄ０２３の10：届出と患者条件は両方必要。手術歴は３区分のいずれかでよい。
example : points [{ req .d023 10 with conditions := {
    facilityNotified := true } }] = none := by decide
example : points [{ req .d023 10 with conditions := {
    ascUsCytology := true } }] = none := by decide
example : points [{ req .d023 10 with conditions := {
    facilityNotified := true, historyK867 := true } }] = some 347 := by decide
example : points [{ req .d023 10 with conditions := {
    facilityNotified := true, historyK867_3 := true } }] = some 347 := by decide
example : points [{ req .d023 10 with conditions := {
    facilityNotified := true, historyK867_4 := true } }] = some 347 := by decide

end Sanri.MedicalFee.SpecimenTests
