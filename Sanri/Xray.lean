import Sanri.Imaging

namespace Sanri.MedicalFee.Xray

/-! 第１節 エックス線診断料 通則１〜５。個別区分の点数は入力する。
同一患者の部位・同時実施・方法・一連の撮影の同定は呼出元で行う。
通則５の特定機能病院の入院算定は外来優先方針により未実装として区別する。 -/

inductive ExceptionReference where
  | e001_2 | e001_4 | e002_2 | e002_4 | e002Note4 | e002Note5
  deriving DecidableEq, Repr

inductive Pricing where
  | ordinary (pointsPerFilm : Nat)
  /-- 通則３の除外。対象区分・注で解決した総点数を入力する。 -/
  | filmRuleException (reference : ExceptionReference) (resolvedPoints : Option Nat)
  deriving DecidableEq, Repr

structure Acquisition where
  siteId : Nat
  simultaneousId : Nat
  methodId : Nat
  filmCount : Nat
  diagnosis : Pricing
  photography : Option Pricing := none
  contrastInjectionPoints : Option Nat := none
  deriving DecidableEq, Repr

inductive ImageKind where
  | plain | special | contrast | mammography
  deriving DecidableEq, Repr

def electronicPoints : ImageKind → Nat
  | .plain => 57
  | .special => 58
  | .contrast => 66
  | .mammography => 54

structure Series where
  acquisitions : List Acquisition
  kind : ImageKind
  digitizedManagedAndStored : Bool := false
  electronicAdditionAlreadyClaimedForSeries : Bool := false
  /-- 実際に使用したフィルムの費用。個別規定で解決した点数。 -/
  filmPoints : Nat := 0
  deriving DecidableEq, Repr

structure Context where
  insuranceMedicalInstitution : Bool := true
  fluoroscopyPoints : List Nat := []
  series : List Series := []
  advancedTreatmentHospital : Bool := false
  inpatient : Bool := false
  deriving DecidableEq, Repr

structure Assessment where
  fluoroscopyHalves : Nat
  diagnosisHalves : Nat
  photographyHalves : Nat
  injectionHalves : Nat
  electronicHalves : Nat
  filmHalves : Nat
  deriving DecidableEq, Repr

def Assessment.totalHalves (a : Assessment) : Nat :=
  a.fluoroscopyHalves + a.diagnosisHalves + a.photographyHalves +
  a.injectionHalves + a.electronicHalves + a.filmHalves

inductive Result where
  | calculated (details : Assessment)
  | requiresIndividualRules (references : List ExceptionReference)
  | requiresInpatientBasicXrayRule
  deriving DecidableEq, Repr

/-- 通則２と３は50％を重ね掛けせず、各診断について該当する50％を用いる。
通則３の通常計算：１枚目は全額、２〜５枚目は半額、６枚目以降は０。
firstDiagnosisFull は通則２における最初の診断かどうか。 -/
def filmChargeHalves (points count : Nat) (firstDiagnosisFull : Bool) : Nat :=
  if count = 0 then 0 else
    points * ((if firstDiagnosisFull then 2 else 1) + min 4 (count - 1))

def missingReference : Pricing → Option ExceptionReference
  | .ordinary _ => none
  | .filmRuleException reference none => some reference
  | .filmRuleException _ (some _) => none

/-- 例外の総点数に通則３の枚数倍率をかけない。通則２の診断減額は別に適用する。 -/
def priceHalves (p : Pricing) (films : Nat) (firstDiagnosisFull : Bool) (diagnosis : Bool) : Nat :=
  match p with
  | .ordinary points => filmChargeHalves points films (if diagnosis then firstDiagnosisFull else true)
  | .filmRuleException _ resolved => resolved.getD 0 *
      (if diagnosis && !firstDiagnosisFull then 1 else 2)

def validPricing (diagnosis : Bool) : Pricing → Bool
  | .ordinary _ => true
  | .filmRuleException reference _ =>
      if diagnosis then decide (reference = .e001_2 ∨ reference = .e001_4)
      else decide (reference ∈ [.e002_2, .e002_4, .e002Note4, .e002Note5])

def sameMethodKey (a b : Acquisition) : Bool :=
  decide (a.siteId = b.siteId ∧ a.simultaneousId = b.simultaneousId ∧ a.methodId = b.methodId)

def assess (c : Context) : Option Result :=
  if !c.insuranceMedicalInstitution then none
  else if c.inpatient && c.advancedTreatmentHospital then some .requiresInpatientBasicXrayRule
  else Id.run do
    let acquisitions := c.series.flatMap Series.acquisitions
    if c.fluoroscopyPoints.isEmpty && acquisitions.isEmpty then return none
    if c.series.any (fun s => s.acquisitions.isEmpty || (s.digitizedManagedAndStored && decide (s.filmPoints > 0))) then
      return none
    if acquisitions.any (fun a => decide (a.filmCount = 0) ||
        !validPricing true a.diagnosis || a.photography.any (fun p => !validPricing false p) ||
        (a.contrastInjectionPoints.isSome && a.photography.isNone)) then return none
    -- 同じ部位・時刻・方法を分割して、６枚目以降の上限を回避する入力を認めない。
    let mut seen : List Acquisition := []
    let mut diagnosis := 0
    let mut photography := 0
    let mut injection := 0
    let mut missing : List ExceptionReference := []
    for a in acquisitions do
      if seen.any (sameMethodKey a) then return none
      let first := !seen.any (fun b => decide (a.siteId = b.siteId ∧ a.simultaneousId = b.simultaneousId))
      diagnosis := diagnosis + priceHalves a.diagnosis a.filmCount first true
      photography := photography + (a.photography.map (fun p => priceHalves p a.filmCount true false)).getD 0
      injection := injection + 2 * a.contrastInjectionPoints.getD 0
      missing := missing ++ (missingReference a.diagnosis).toList ++
        (a.photography.bind missingReference).toList
      seen := seen ++ [a]
    if !missing.isEmpty then return some (.requiresIndividualRules missing.eraseDups)
    return some (.calculated {
      fluoroscopyHalves := 2 * c.fluoroscopyPoints.sum
      diagnosisHalves := diagnosis
      photographyHalves := photography
      injectionHalves := injection
      electronicHalves := 2 * ((c.series.filter (fun s =>
        s.digitizedManagedAndStored && !s.electronicAdditionAlreadyClaimedForSeries)).map
          (fun s => electronicPoints s.kind)).sum
      filmHalves := 2 * ((c.series.filter (fun s => !s.digitizedManagedAndStored)).map Series.filmPoints).sum })

/-- 第４部通則との接続用。半点を整数へ丸めず、一般通則の算定分と別に保持する。 -/
structure CombinedAssessment where
  xray : Assessment
  general : Imaging.Assessment
  deriving DecidableEq, Repr

def CombinedAssessment.totalHalves (a : CombinedAssessment) : Nat :=
  a.xray.totalHalves + 2 * a.general.total

inductive CombinedResult where
  | calculated (details : CombinedAssessment)
  | requiresIndividualRules (references : List ExceptionReference)
  | requiresInpatientBasicXrayRule
  deriving DecidableEq, Repr

/-- existing に今回のＥ０００〜Ｅ００３やフィルムを二重登録しない。
管理加算・緊急加算・第４節・第５節は第４部通則側で評価する。 -/
def assessWithGeneralRules (c : Context) (existing : Imaging.Context)
    (management : Option Imaging.Management := none) : Option CombinedResult := do
  match ← assess c with
  | .requiresIndividualRules refs => some (.requiresIndividualRules refs)
  | .requiresInpatientBasicXrayRule => some .requiresInpatientBasicXrayRule
  | .calculated xray =>
    let hasPhoto := c.series.any (fun s => !s.acquisitions.isEmpty)
    let entries := (if hasPhoto then [Imaging.Entry.mk .e001 .section1 0 management] else []) ++
      (if !c.fluoroscopyPoints.isEmpty then [Imaging.Entry.mk .other .section1 0 none] else [])
    let general ← Imaging.assess { existing with
      insuranceMedicalInstitution := existing.insuranceMedicalInstitution && c.insuranceMedicalInstitution
      inpatient := c.inpatient
      entries := existing.entries ++ entries }
    some (.calculated ⟨xray, general⟩)

/-! 個別区分の点数は通則検証用の仮入力。 -/
private def photo : Acquisition :=
  { siteId := 1, simultaneousId := 1, methodId := 1, filmCount := 1, diagnosis := .ordinary 101, photography := some (.ordinary 60) }
private def ordinary : Context :=
  { series := [{ acquisitions := [photo], kind := .plain }] }
private def total (c : Context) : Option Nat := do
  match ← assess c with
  | .calculated a => some a.totalHalves
  | _ => none

example : total ordinary = some 322 := by decide
example : total { fluoroscopyPoints := [20] } = some 40 := by decide
example : total { series := [{ acquisitions := [{ photo with photography := none }], kind := .plain }] } =
    some 202 := by decide
example : total { ordinary with fluoroscopyPoints := [20] } = some 362 := by decide
example : total { series := [{ acquisitions := [{ photo with contrastInjectionPoints := some 30 }], kind := .contrast }] } = some 382 := by decide
example : assess { series := [{ acquisitions := [{ photo with photography := none, contrastInjectionPoints := some 30 }], kind := .plain }] } = none := by decide
example : (List.map (fun n => filmChargeHalves 100 n true) [0, 1, 2, 5, 6, 7]) =
    [0, 200, 300, 600, 600, 600] := by decide
example : total { series := [{ acquisitions := [photo, { photo with methodId := 2 }], kind := .plain }] } =
    some 543 := by decide -- 161 + (50.5 + 60) = 271.5点
example : total { series := [{ acquisitions := [photo, { photo with siteId := 2 }], kind := .plain }] } =
    some 644 := by decide
example : total { series := [{ acquisitions := [photo, { photo with simultaneousId := 2 }], kind := .plain }] } =
    some 644 := by decide
example : assess { series := [{ acquisitions := [photo, photo], kind := .plain }] } = none := by decide
example : (List.map electronicPoints [.plain, .special, .contrast, .mammography]) = [57, 58, 66, 54] := rfl
example : total { series := [{ acquisitions := [photo], kind := .plain, digitizedManagedAndStored := true }] } = some 436 := by decide
example : total { series := [{ acquisitions := [photo], kind := .plain, filmPoints := 12 }] } = some 346 := by decide
example : assess { series := [{ acquisitions := [photo], kind := .plain, digitizedManagedAndStored := true, filmPoints := 12 }] } = none := by decide
example : total { series := [{ acquisitions := [photo], kind := .plain, digitizedManagedAndStored := true, electronicAdditionAlreadyClaimedForSeries := true }] } =
    some 322 := by decide
example : assess { series := [{ acquisitions := [{ photo with diagnosis := .filmRuleException .e001_2 none }], kind := .special }] } = some (.requiresIndividualRules [.e001_2]) := by decide
example : total { series := [{ acquisitions := [{ photo with filmCount := 6, diagnosis := .filmRuleException .e001_2 (some 300) }], kind := .special }] } = some 960 := by decide
example : assess { series := [{ acquisitions := [{ photo with diagnosis := .filmRuleException .e002_2 (some 300) }], kind := .special }] } = none := by decide
example : assess { ordinary with advancedTreatmentHospital := true, inpatient := true } =
    some .requiresInpatientBasicXrayRule := by decide
example : total { ordinary with advancedTreatmentHospital := true } = some 322 := by decide
example : (assessWithGeneralRules ordinary {
    entries := [], localStandards := { one := true }, localDedicatedFullTimeDoctorWrittenReport := true } (some .one)) =
    some (.calculated ⟨⟨0, 202, 120, 0, 0, 0⟩, ⟨0, 0, 0, 0, [⟨.e001OrE004, .one, 70⟩]⟩⟩) := by decide

end Sanri.MedicalFee.Xray
