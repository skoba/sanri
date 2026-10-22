import Sanri.Examinations

namespace Sanri.MedicalFee.SpecimenCollection

/-! 第４節通則１・２、Ｄ４００〜Ｄ４１９－２。
片側・臓器・日次・一連の実施と履歴は同一患者について呼出元が管理する。
第３節の率による年齢加算は使わず、この節の各注の固定点数を用いる。 -/

inductive Item where
  | venousBlood | otherBlood | ventricularPuncture | suboccipitalPuncture
  | lumbarPuncture | thoracicPuncture | cervicalPuncture
  | sternalMarrowPuncture | otherMarrowPuncture | marrowBiopsy
  | jointPuncture | maxillarySinusPuncture | peritonsillarTrialPuncture | renalCystHydronephrosisPuncture
  | douglasPuncture | lymphNodeNeedleBiopsy | sentinelCombined | sentinelSingle
  | breastBiopsyNeedle | breastOther | thyroidNeedleBiopsy | percutaneousNeedleBiopsy
  | percutaneousRenalBiopsy | transjugularLiverBiopsy | prostateMriUltrasoundFusion | prostateOther
  | endoscopicBiopsy | eusFna | transbronchialLungBiopsy | ebusTbna | navigatedLungBiopsy
  | virtualBronchoscopyBiopsy | transbronchialCryobiopsy | parietalPleuralCryobiopsy
  | thoracotomyTissue | laparotomyTissue
  | skinTissue | muscleTissue | bonePelvisSpineTissue | posteriorEyeTissue | otherEyeTissue
  | earTissue | nasalSinusTissue | oralTissue | pharyngolaryngealTissue | thyroidTissue
  | breastTissue | rectalTissue | testisEpididymisTissue | peripheralNerveTissue | myocardiumTissue
  | cervicalMucus | vaginalCervicalTissue | endometrialTissue
  | gastricDuodenalFluid | pleuralAsciticFluid | arterialBlood | anteriorChamberFluid
  | adrenalVenousSampling | nasalPharyngealSwab | intraocularFluidExamination
  deriving DecidableEq, Repr

def basePoints : Item → Nat
  | .venousBlood => 40
  | .otherBlood => 6
  | .ventricularPuncture => 600
  | .suboccipitalPuncture => 300
  | .lumbarPuncture | .thoracicPuncture | .cervicalPuncture => 312
  | .sternalMarrowPuncture => 260
  | .otherMarrowPuncture => 300
  | .marrowBiopsy => 730
  | .jointPuncture => 100
  | .maxillarySinusPuncture => 60
  | .peritonsillarTrialPuncture => 180
  | .renalCystHydronephrosisPuncture | .douglasPuncture | .lymphNodeNeedleBiopsy => 240
  | .sentinelCombined => 5000
  | .sentinelSingle => 3000
  | .breastBiopsyNeedle => 690
  | .breastOther => 200
  | .thyroidNeedleBiopsy => 150
  | .percutaneousNeedleBiopsy => 1920
  | .percutaneousRenalBiopsy => 2400
  | .transjugularLiverBiopsy => 13000
  | .prostateMriUltrasoundFusion => 8210
  | .prostateOther => 1848
  | .endoscopicBiopsy => 310
  | .eusFna => 5760
  | .transbronchialLungBiopsy => 4800
  | .ebusTbna | .navigatedLungBiopsy | .transbronchialCryobiopsy => 5500
  | .virtualBronchoscopyBiopsy => 5000
  | .parietalPleuralCryobiopsy => 15800
  | .thoracotomyTissue => 9070
  | .laparotomyTissue => 5550
  | .skinTissue => 500
  | .muscleTissue => 1500
  | .bonePelvisSpineTissue => 4600
  | .posteriorEyeTissue | .pharyngolaryngealTissue | .thyroidTissue | .breastTissue => 650
  | .otherEyeTissue => 350
  | .earTissue | .nasalSinusTissue | .oralTissue | .testisEpididymisTissue => 400
  | .rectalTissue => 780
  | .peripheralNerveTissue => 1620
  | .myocardiumTissue => 6000
  | .cervicalMucus => 40
  | .vaginalCervicalTissue => 200
  | .endometrialTissue => 370
  | .gastricDuodenalFluid => 210
  | .pleuralAsciticFluid => 220
  | .arterialBlood => 60
  | .anteriorChamberFluid => 504
  | .adrenalVenousSampling => 4800
  | .nasalPharyngealSwab => 25
  | .intraocularFluidExamination => 1000

def isD400 (i : Item) : Bool := decide (i = .venousBlood ∨ i = .otherBlood)
def isDaily (i : Item) : Bool := isD400 i || decide (i = .arterialBlood)
def isSeries (i : Item) : Bool := decide (i = .gastricDuodenalFluid ∨ i = .adrenalVenousSampling)
def isUnilateral (i : Item) : Bool := decide (i ∈
  [.jointPuncture, .maxillarySinusPuncture, .peritonsillarTrialPuncture,
   .sentinelCombined, .sentinelSingle, .breastBiopsyNeedle, .breastOther])
def isD417 (i : Item) : Bool := decide (i ∈
  [.skinTissue, .muscleTissue, .bonePelvisSpineTissue, .posteriorEyeTissue, .otherEyeTissue,
   .earTissue, .nasalSinusTissue, .oralTissue, .pharyngolaryngealTissue, .thyroidTissue,
   .breastTissue, .rectalTissue, .testisEpididymisTissue, .peripheralNerveTissue, .myocardiumTissue])

def infantPoints (i : Item) (ageYears : Nat) : Nat :=
  if i = .jointPuncture then if ageYears < 3 then 100 else 0
  else if ageYears ≥ 6 then 0
  else if isD400 i || decide (i = .arterialBlood) then 35
  else if isD417 i || decide (i ∈ [.ventricularPuncture, .suboccipitalPuncture,
      .lumbarPuncture, .thoracicPuncture, .cervicalPuncture, .sternalMarrowPuncture,
      .otherMarrowPuncture, .marrowBiopsy, .renalCystHydronephrosisPuncture]) then 100
  else match i with
    | .thoracotomyTissue | .laparotomyTissue => 2000
    | .pleuralAsciticFluid => 60
    | .anteriorChamberFluid => 90
    | .adrenalVenousSampling => 1000
    | _ => 0

inductive Sides where
  | one | both
  deriving DecidableEq, Repr

structure Context where
  item : Item
  insuranceMedicalInstitution : Bool := true
  performed : Bool := true
  ageYears : Nat := 20
  inpatient : Bool := false
  duringSurgery : Bool := false
  /-- 処置の部にもある共通項目で、同一日にその処置を算定するか。 -/
  commonProcedureClaimedSameDay : Bool := false
  dailyAlreadyClaimed : Bool := false
  seriesAlreadyClaimed : Bool := false
  seriesId : Nat := 0
  bloodCircuitSampling : Bool := false
  sides : Sides := .one
  /-- Ｄ４１４の実際に採取した臓器の識別子。同じ臓器を重複して数えない。 -/
  organs : List Nat := [0]
  facilityStandardNotified : Bool := false
  breastCancerPatient : Bool := false
  radioisotopeUsed : Bool := false
  dyeUsed : Bool := false
  designatedProstatePatient : Bool := false
  guideSheathUltrasoundPerformed : Bool := false
  ctFluoroscopicBronchoscopy : Bool := false
  ctFluoroscopyStandardNotified : Bool := false
  probeConfocalEndomicroscopy : Bool := false
  /-- Ｄ４１９の５：Ｅ４００の規定で解決した、使用フィルムの点数。 -/
  filmPoints : Nat := 0
  deriving DecidableEq, Repr

inductive NotSeparateReason where
  | duringSurgery | commonProcedureSameDay | inpatientBloodCollection | bloodCircuit
  | dailyAlreadyClaimed | seriesAlreadyClaimed
  deriving DecidableEq, Repr

def notSeparateReason (c : Context) : Option NotSeparateReason :=
  if c.duringSurgery then some .duringSurgery
  else if c.commonProcedureClaimedSameDay then some .commonProcedureSameDay
  else if isD400 c.item && c.inpatient then some .inpatientBloodCollection
  else if (isD400 c.item || decide (c.item = .arterialBlood)) && c.bloodCircuitSampling then some .bloodCircuit
  else if isDaily c.item && c.dailyAlreadyClaimed then some .dailyAlreadyClaimed
  else if isSeries c.item && c.seriesAlreadyClaimed then some .seriesAlreadyClaimed
  else none

def eligible (c : Context) : Bool :=
  c.insuranceMedicalInstitution && c.performed &&
  (decide (c.item ∉ [.transjugularLiverBiopsy, .transbronchialCryobiopsy, .parietalPleuralCryobiopsy]) ||
    c.facilityStandardNotified) &&
  (decide (c.item ≠ .prostateMriUltrasoundFusion) || (c.facilityStandardNotified && c.designatedProstatePatient)) &&
  (decide (c.item ≠ .sentinelCombined) ||
    (c.facilityStandardNotified && c.breastCancerPatient && c.radioisotopeUsed && c.dyeUsed)) &&
  (decide (c.item ≠ .sentinelSingle) ||
    (c.facilityStandardNotified && c.breastCancerPatient &&
      ((c.radioisotopeUsed && !c.dyeUsed) || (!c.radioisotopeUsed && c.dyeUsed)))) &&
  (decide (c.item ≠ .endoscopicBiopsy) || !c.organs.isEmpty) &&
  (decide (c.item ≠ .transbronchialLungBiopsy) ||
    !c.ctFluoroscopicBronchoscopy || c.ctFluoroscopyStandardNotified)

structure Assessment where
  notSeparate : Option NotSeparateReason
  units : Nat := 0
  base : Nat := 0
  infant : Nat := 0
  guideSheath : Nat := 0
  ctFluoroscopy : Nat := 0
  endomicroscopy : Nat := 0
  film : Nat := 0
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Nat :=
  a.base + a.infant + a.guideSheath + a.ctFluoroscopy + a.endomicroscopy + a.film

def assess (c : Context) : Option Assessment :=
  if !c.insuranceMedicalInstitution || !c.performed then none else
    match notSeparateReason c with
    | some reason => some { notSeparate := some reason }
    | none =>
      if !eligible c then none else
        let units := if c.item = .endoscopicBiopsy then c.organs.eraseDups.length
          else if isUnilateral c.item && decide (c.sides = .both) then 2 else 1
        let isD415 := decide (c.item = .transbronchialLungBiopsy)
        let micro := isD415 && c.probeConfocalEndomicroscopy
        some {
          notSeparate := none
          units := units
          base := units * basePoints c.item
          infant := units * infantPoints c.item c.ageYears
          guideSheath := if c.guideSheathUltrasoundPerformed &&
            ((isD415 && !micro) || decide (c.item = .virtualBronchoscopyBiopsy)) then 500 else 0
          ctFluoroscopy := if isD415 && c.ctFluoroscopicBronchoscopy then 1000 else 0
          endomicroscopy := if micro then 1500 else 0
          film := if c.item = .adrenalVenousSampling then c.filmPoints else 0 }

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-- 同一日・同一患者の一覧。Ｄ４００の静脈／その他は日次履歴を共有する。 -/
def assessDay (contexts : List Context) : Option (List Assessment) := do
  let result ← contexts.foldlM (fun (state : List Context × List Assessment) original => do
    let c := { original with
      dailyAlreadyClaimed := original.dailyAlreadyClaimed || state.1.any (fun x =>
        (isD400 original.item && isD400 x.item) || decide (x.item = original.item))
      seriesAlreadyClaimed := original.seriesAlreadyClaimed || state.1.any (fun x =>
        decide (x.item = original.item ∧ x.seriesId = original.seriesId)) }
    let a ← assess c
    let charged := if a.notSeparate.isNone then state.1 ++ [c] else state.1
    some (charged, state.2 ++ [a])) ([], [])
  some result.2

/-- 検査通則の第４節に引き渡す。別算定しない採取を種類数に含めない。
Ｅ４００のフィルムは第４節の置換対象に混ぜず、呼出元で別に合算する。 -/
def Assessment.toCollection (a : Assessment) (kind : Nat) : Option Examinations.TestCharge :=
  if a.notSeparate.isSome then none else some { kind := kind, scheduledPoints := a.total - a.film }

inductive IncludedService where
  | cerebrospinalPressure | fluoroscopy | ecg | ultrasound | simpleFluidTest
  | contrastInjection | contrastImaging | xrayDiagnosis | sentinelDye
  deriving DecidableEq, Repr

/-- 包括範囲。false だけでは当該費用の別算定可否を決定しない。 -/
def serviceIncluded (c : Context) (s : IncludedService) : Bool :=
  match s with
  | .cerebrospinalPressure => decide (c.item ∈ [.lumbarPuncture, .thoracicPuncture, .cervicalPuncture])
  | .fluoroscopy => decide (c.item = .percutaneousNeedleBiopsy ∨ c.item = .adrenalVenousSampling)
  | .ecg | .ultrasound => decide (c.item = .percutaneousNeedleBiopsy)
  | .simpleFluidTest => decide (c.item = .pleuralAsciticFluid)
  | .contrastInjection | .contrastImaging | .xrayDiagnosis => decide (c.item = .adrenalVenousSampling)
  | .sentinelDye => decide (c.item = .sentinelCombined ∨ c.item = .sentinelSingle)

private def req (item : Item) : Context := { item := item }
example : points (req .venousBlood) = some 40 := by decide
example : points { req .venousBlood with ageYears := 5 } = some 75 := by decide
example : points { req .venousBlood with ageYears := 6 } = some 40 := by decide
example : points { req .otherBlood with ageYears := 5 } = some 41 := by decide
example : points { req .venousBlood with inpatient := true } = some 0 := by decide
example : points { req .arterialBlood with bloodCircuitSampling := true } = some 0 := by decide
example : points { req .lymphNodeNeedleBiopsy with duringSurgery := true } = some 0 := by decide
example : points { req .jointPuncture with commonProcedureClaimedSameDay := true } = some 0 := by decide
example : points { req .jointPuncture with ageYears := 2 } = some 200 := by decide
example : points { req .jointPuncture with ageYears := 3 } = some 100 := by decide
example : points { req .jointPuncture with sides := .both, ageYears := 2 } = some 400 := by decide
example : points { req .ventricularPuncture with ageYears := 5 } = some 700 := by decide
example : points { req .lumbarPuncture with ageYears := 5 } = some 412 := by decide
example : points { req .marrowBiopsy with ageYears := 5 } = some 830 := by decide
example : points (req .sentinelCombined) = none := by decide
example : points { req .sentinelCombined with facilityStandardNotified := true, breastCancerPatient := true, radioisotopeUsed := true, dyeUsed := true } = some 5000 := by decide
example : points { req .sentinelSingle with facilityStandardNotified := true, breastCancerPatient := true, dyeUsed := true } = some 3000 := by decide
example : points { req .sentinelSingle with facilityStandardNotified := true, breastCancerPatient := true, radioisotopeUsed := true, dyeUsed := true } = none := by decide
example : points (req .transjugularLiverBiopsy) = none := by decide
example : points { req .transjugularLiverBiopsy with facilityStandardNotified := true } = some 13000 := by decide
example : points { req .prostateMriUltrasoundFusion with facilityStandardNotified := true } = none := by decide
example : points { req .prostateMriUltrasoundFusion with facilityStandardNotified := true, designatedProstatePatient := true } = some 8210 := by decide
example : points { req .endoscopicBiopsy with organs := [1, 1, 2] } = some 620 := by decide
example : points { req .endoscopicBiopsy with organs := [] } = none := by decide
example : points { req .transbronchialLungBiopsy with guideSheathUltrasoundPerformed := true } = some 5300 := by decide
example : points { req .transbronchialLungBiopsy with guideSheathUltrasoundPerformed := true, probeConfocalEndomicroscopy := true } = some 6300 := by decide
example : points { req .transbronchialLungBiopsy with ctFluoroscopicBronchoscopy := true } = none := by decide
example : points { req .transbronchialLungBiopsy with ctFluoroscopicBronchoscopy := true, ctFluoroscopyStandardNotified := true, probeConfocalEndomicroscopy := true } = some 7300 := by decide
example : points { req .virtualBronchoscopyBiopsy with guideSheathUltrasoundPerformed := true } = some 5500 := by decide
example : points (req .transbronchialCryobiopsy) = none := by decide
example : points { req .parietalPleuralCryobiopsy with facilityStandardNotified := true } = some 15800 := by decide
example : points { req .thoracotomyTissue with ageYears := 5 } = some 11070 := by decide
example : points { req .myocardiumTissue with ageYears := 5 } = some 6100 := by decide
example : points { req .pleuralAsciticFluid with ageYears := 5 } = some 280 := by decide
example : points { req .anteriorChamberFluid with ageYears := 5 } = some 594 := by decide
example : points { req .adrenalVenousSampling with ageYears := 5, filmPoints := 25 } = some 5825 := by decide
example : points { req .gastricDuodenalFluid with seriesAlreadyClaimed := true } = some 0 := by decide
example : (assessDay [req .venousBlood, req .otherBlood]).map
    (fun xs => (xs.map Assessment.total).sum) = some 40 := by decide
example : ((assess { req .venousBlood with duringSurgery := true }).bind
    (fun a => a.toCollection 400)) = none := by decide
example : ((assess { req .adrenalVenousSampling with filmPoints := 25 }).bind
    (fun a => a.toCollection 419)).map Examinations.TestCharge.scheduledPoints = some 4800 := by decide
example : serviceIncluded (req .sentinelSingle) .sentinelDye = true := by decide
example : serviceIncluded (req .percutaneousNeedleBiopsy) .ultrasound = true := by decide

end Sanri.MedicalFee.SpecimenCollection
