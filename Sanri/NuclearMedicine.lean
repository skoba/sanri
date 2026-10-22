import Sanri.Imaging
import Sanri.PhysiologicalExaminations

namespace Sanri.MedicalFee.NuclearMedicine

/-! 第２節 核医学診断料の通則１〜３、Ｅ１００〜Ｅ１０２。
ラジオアイソトープの同一性、一連・月次履歴、別に定める施設基準は入力する。
ＰＥＴの注２（算定要件）と注３（満額／80％）は異なる基準として別に管理する。 -/

inductive Agent where
  | oxygen15 | fdg18 | ammonia13 | fluciclovine18 | amyloidSynthesis | amyloidOther | psma
  deriving DecidableEq, Repr

inductive Item where
  | scintigraphyStatic | scintigraphyDynamic | scintigraphyWholeBody | spect
  | pet (agent : Agent)
  | petCt (agent : Agent)
  | petMri (agent : Agent)
  | breastPet
  /-- Ｄ２９２・Ｄ２９３は点数と当該区分の要件を解決済みの入力としてだけ扱う。 -/
  | d292 (resolvedPoints : Nat)
  | d293 (resolvedPoints : Nat)
  deriving DecidableEq, Repr

def basePoints : Item → Option Nat
  | .scintigraphyStatic => some 1300
  | .scintigraphyDynamic => some 1800
  | .scintigraphyWholeBody => some 2200
  | .spect => some 1800
  | .pet .oxygen15 => some 7000
  | .pet .fdg18 => some 7500
  | .pet .ammonia13 => some 9000
  | .pet .fluciclovine18 => some 2500
  | .pet .amyloidSynthesis => some 12500
  | .pet .amyloidOther => some 2600
  | .pet .psma => some 2780
  | .petCt .oxygen15 => some 7625
  | .petCt .fdg18 => some 8625
  | .petCt .fluciclovine18 => some 3625
  | .petCt .amyloidSynthesis => some 13625
  | .petCt .amyloidOther => some 3725
  | .petCt .psma => some 3905
  | .petMri .fdg18 => some 9160
  | .petMri .fluciclovine18 => some 4160
  | .petMri .amyloidSynthesis => some 14160
  | .petMri .amyloidOther => some 4260
  | .petMri .psma => some 4440
  | .breastPet => some 4000
  | .d292 n | .d293 n => some n
  | _ => none

def isPet : Item → Bool
  | .pet _ | .petCt _ | .petMri _ | .breastPet => true
  | _ => false

def isNuclear : Item → Bool
  | .d292 _ | .d293 _ => false
  | _ => true

/-- 通則１の列挙にＥ１０１－５を追加しない。 -/
def principalRuleApplies : Item → Bool
  | .breastPet => false
  | _ => true

def fixedAgeAdditionApplies : Item → Bool
  | .pet .oxygen15 | .pet .fdg18 | .pet .ammonia13 | .pet .fluciclovine18
  | .petCt .oxygen15 | .petCt .fdg18 | .petCt .fluciclovine18
  | .petMri .fdg18 | .petMri .fluciclovine18 => true
  | _ => false

structure Examination where
  id : Nat
  item : Item
  isotopeId : Nat
  seriesId : Nat
  performed : Bool := true
  eligibleUnderIndividualRule : Bool := true
  seriesAlreadyCharged : Bool := false
  petFacilityStandardNotified : Bool := false
  fullRateFacilityStandardMet : Bool := false
  thyroidScintigraphy : Bool := false
  thyroidUptakeMeasured : Bool := false
  spectLoadTestPerformed : Bool := false
  deriving DecidableEq, Repr

structure Principal where
  isotopeId : Nat
  examinationId : Nat
  deriving DecidableEq, Repr

structure ImageSeries where
  id : Nat
  digitizedManagedAndStored : Bool := false
  electronicAdditionAlreadyClaimed : Bool := false
  filmPoints : Nat := 0
  deriving DecidableEq, Repr

structure Context where
  insuranceMedicalInstitution : Bool := true
  examinations : List Examination
  principals : List Principal := []
  imageSeries : List ImageSeries := []
  completedYears : Nat := 20
  newborn : Bool := false
  diagnosisClaimedThisMonth : Bool := false
  deriving DecidableEq, Repr

inductive Exclusion where
  | principalExamination | alreadyChargedSeries
  deriving DecidableEq, Repr

structure Charge where
  examinationId : Nat
  exclusion : Option Exclusion := none
  baseTenths : Nat := 0
  ageTenths : Nat := 0
  thyroidTenths : Nat := 0
  loadTenths : Nat := 0
  deriving DecidableEq, Repr

def Charge.totalTenths (a : Charge) : Nat := a.baseTenths + a.ageTenths + a.thyroidTenths + a.loadTenths

/-- Ｅ１００・Ｅ１０１の年齢率とＰＥＴの固定額を区別する。 -/
def ageAdditionTenths (e : Examination) (age : PhysiologicalExaminations.AgeGroup) (base : Nat) : Nat :=
  if fixedAgeAdditionApplies e.item then
    let amount := match age with
      | .newborn => 1600
      | .underThreeNonNewborn => 1000
      | .threeToUnderSix => 600
      | .sixOrOlder => 0
    amount * (if e.fullRateFacilityStandardMet then 10 else 8)
  else if isPet e.item || !isNuclear e.item then 0
  else base * (match age with
    | .newborn => 8
    | .underThreeNonNewborn => 5
    | .threeToUnderSix => 3
    | .sixOrOlder => 0)

structure Assessment where
  examinations : List Charge
  diagnosis : Nat
  electronic : Nat
  film : Nat
  deriving DecidableEq, Repr

def Assessment.totalTenths (a : Assessment) : Nat :=
  (a.examinations.map Charge.totalTenths).sum + 10 * (a.diagnosis + a.electronic + a.film)

/-- 同じアイソトープの複数検査は主たる１件を明示する。最大点数を自動選択しない。
Ｅ１００の複数部位・反復も同じ選択で一連にまとめる。 -/
def assess (c : Context) : Option Assessment := do
  if !c.insuranceMedicalInstitution || c.examinations.isEmpty then none else
    let age ← PhysiologicalExaminations.ageGroup c.completedYears c.newborn
    if (c.examinations.map Examination.id).eraseDups.length != c.examinations.length ||
        (c.imageSeries.map ImageSeries.id).eraseDups.length != c.imageSeries.length ||
        (c.principals.map Principal.isotopeId).eraseDups.length != c.principals.length then none
    else if c.principals.any (fun p => !c.examinations.any (fun e =>
        e.id == p.examinationId && e.isotopeId == p.isotopeId && e.performed && principalRuleApplies e.item)) then none
    else
      let eligible := c.examinations.filter (fun e => e.performed)
      let charges ← eligible.mapM (fun e => do
        if !e.eligibleUnderIndividualRule || (isPet e.item && !e.petFacilityStandardNotified) then none else
          let base ← basePoints e.item
          let peers := eligible.filter (fun other => other.isotopeId == e.isotopeId && principalRuleApplies other.item)
          let principal := c.principals.find? (fun p => p.isotopeId == e.isotopeId)
          if principalRuleApplies e.item && decide (peers.length ≥ 2) && principal.isNone then none
          else if principalRuleApplies e.item && decide (peers.length ≥ 2) &&
              principal.any (fun p => p.examinationId != e.id) then
            some { examinationId := e.id, exclusion := some .principalExamination }
          else if e.seriesAlreadyCharged then
            some { examinationId := e.id, exclusion := some .alreadyChargedSeries }
          else
            some {
              examinationId := e.id
              baseTenths := base * (if isPet e.item && !e.fullRateFacilityStandardMet then 8 else 10)
              ageTenths := ageAdditionTenths e age base
              thyroidTenths := if !isPet e.item && isNuclear e.item &&
                e.thyroidScintigraphy && e.thyroidUptakeMeasured then 1000 else 0
              loadTenths := if e.item = .spect && e.spectLoadTestPerformed then 5 * base else 0 })
      let selected := eligible.filter (fun e => charges.any (fun a => a.examinationId == e.id && a.exclusion.isNone))
      let nuclear := selected.filter (fun e => isNuclear e.item)
      let seriesIds := (nuclear.map Examination.seriesId).eraseDups
      let series := c.imageSeries.filter (fun s => seriesIds.contains s.id)
      if series.any (fun s => s.digitizedManagedAndStored && decide (s.filmPoints > 0)) then none else
        some {
          examinations := charges
          diagnosis := if c.diagnosisClaimedThisMonth || nuclear.isEmpty then 0
            else if nuclear.any (fun e => isPet e.item) then 450 else 370
          electronic := 120 * (series.filter (fun s => s.digitizedManagedAndStored && !s.electronicAdditionAlreadyClaimed)).length
          film := ((series.filter (fun s => !s.digitizedManagedAndStored)).map ImageSeries.filmPoints).sum }

/-- 第４部通則への接続。Ｅ１０２を０点の参照として加え、半端な点数を丸めず合算する。 -/
structure CombinedAssessment where
  nuclear : Assessment
  general : Imaging.Assessment
  deriving DecidableEq, Repr

def CombinedAssessment.totalTenths (a : CombinedAssessment) : Nat :=
  a.nuclear.totalTenths + 10 * a.general.total

def assessWithGeneralRules (c : Context) (existing : Imaging.Context)
    (management : Option Imaging.Management := none) : Option CombinedAssessment := do
  let nuclear ← assess c
  let hasNuclear := c.examinations.any (fun e => isNuclear e.item &&
    nuclear.examinations.any (fun a => a.examinationId == e.id && a.exclusion.isNone))
  if !hasNuclear then
    -- Ｄ２９２・Ｄ２９３だけが主検査の場合、Ｅ１０２管理加算の根拠にしない。
    if management.isSome then none
    else if existing.entries.isEmpty then
      if existing.section4Points.isEmpty && existing.section5MaterialPoints.isEmpty then
        some ⟨nuclear, ⟨0, 0, 0, 0, []⟩⟩
      else none
    else
      let general ← Imaging.assess existing
      some ⟨nuclear, general⟩
  else
    let general ← Imaging.assess { existing with
      entries := existing.entries ++ [⟨.e102, .section2, 0, management⟩] }
    some ⟨nuclear, general⟩

inductive IncludedService where
  | injection | synthesis | inhalation | preparation
  deriving DecidableEq, Repr

/-- 各注に明記された手技費用の包括。薬剤そのものの価格とは区別する。 -/
def serviceIncluded (item : Item) (service : IncludedService) : Bool :=
  match service with
  | .injection => isNuclear item && decide (item ≠ .pet .oxygen15 ∧ item ≠ .petCt .oxygen15)
  | .inhalation => decide (item = .pet .oxygen15 ∨ item = .petCt .oxygen15)
  | .preparation => decide (item ∈ [.pet .psma, .petCt .psma, .petMri .psma])
  | .synthesis => decide (item ∈ [.pet .oxygen15, .pet .fdg18, .pet .ammonia13,
      .pet .amyloidSynthesis, .petCt .oxygen15, .petCt .fdg18, .petCt .amyloidSynthesis,
      .petMri .fdg18, .petMri .amyloidSynthesis, .breastPet])

private def exam (item : Item) : Examination :=
  { id := 1, item := item, isotopeId := 1, seriesId := 1 }
private def pet : Examination :=
  { exam (.pet .fdg18) with petFacilityStandardNotified := true, fullRateFacilityStandardMet := true }
private def total (c : Context) : Option Nat := (assess c).map Assessment.totalTenths

example : (List.map basePoints [.scintigraphyStatic, .scintigraphyDynamic, .scintigraphyWholeBody, .spect, .pet .oxygen15, .pet .fdg18, .pet .ammonia13, .pet .fluciclovine18, .pet .amyloidSynthesis, .pet .amyloidOther, .pet .psma]) =
    [some 1300, some 1800, some 2200, some 1800, some 7000, some 7500, some 9000, some 2500, some 12500, some 2600, some 2780] := by decide
example : (List.map basePoints [.petCt .oxygen15, .petCt .fdg18, .petCt .fluciclovine18, .petCt .amyloidSynthesis, .petCt .amyloidOther, .petCt .psma, .petMri .fdg18, .petMri .fluciclovine18, .petMri .amyloidSynthesis, .petMri .amyloidOther, .petMri .psma, .breastPet]) =
    [some 7625, some 8625, some 3625, some 13625, some 3725, some 3905, some 9160, some 4160, some 14160, some 4260, some 4440, some 4000] := by decide
example : basePoints (.petCt .ammonia13) = none := rfl
example : basePoints (.petMri .oxygen15) = none := rfl
example : total { examinations := [exam .scintigraphyStatic] } = some 16700 := by decide
example : total { examinations := [exam .scintigraphyStatic], diagnosisClaimedThisMonth := true } = some 13000 := by decide
example : total { examinations := [exam .scintigraphyStatic], completedYears := 0, newborn := true } = some 27100 := by decide
example : total { examinations := [exam .scintigraphyStatic], completedYears := 2 } = some 23200 := by decide
example : total { examinations := [exam .scintigraphyStatic], completedYears := 3 } = some 20600 := by decide
example : total { examinations := [{ exam .spect with thyroidScintigraphy := true, thyroidUptakeMeasured := true, spectLoadTestPerformed := true }] } = some 31700 := by decide
example : total { examinations := [exam (.pet .fdg18)] } = none := by decide
example : total { examinations := [pet] } = some 79500 := by decide
example : total { examinations := [{ pet with fullRateFacilityStandardMet := false }] } = some 64500 := by decide
example : total { examinations := [pet], completedYears := 0, newborn := true } = some 95500 := by decide
example : total { examinations := [{ pet with fullRateFacilityStandardMet := false }], completedYears := 0, newborn := true } = some 77300 := by decide
example : total { examinations := [pet], completedYears := 2 } = some 89500 := by decide
example : total { examinations := [{ pet with fullRateFacilityStandardMet := false }], completedYears := 2 } = some 72500 := by decide
example : total { examinations := [pet], completedYears := 5 } = some 85500 := by decide
example : total { examinations := [{ pet with item := .pet .amyloidOther }], completedYears := 2 } = some 30500 := by decide
example : total { examinations := [{ pet with item := .pet .psma }], completedYears := 2 } = some 32300 := by decide
example : total { examinations := [exam .scintigraphyStatic, { exam .spect with id := 2 }] } = none := by decide
example : total { examinations := [exam .scintigraphyStatic, { exam .spect with id := 2 }], principals := [⟨1, 2⟩] } = some 21700 := by decide
example : total { examinations := [exam .scintigraphyStatic, { exam .scintigraphyWholeBody with id := 2 }], principals := [⟨1, 1⟩] } = some 16700 := by decide
example : total { examinations := [exam .scintigraphyStatic, { exam (.d292 100) with id := 2 }], principals := [⟨1, 2⟩] } = some 1000 := by decide
example : total { examinations := [exam .scintigraphyStatic, { exam .spect with id := 2, isotopeId := 2 }] } =
    some 34700 := by decide
example : total { examinations := [pet, { pet with id := 2, item := .breastPet }] } = some 119500 := by decide
example : total { examinations := [exam .scintigraphyStatic], imageSeries := [⟨1, true, false, 0⟩] } = some 17900 := by decide
example : total { examinations := [exam .scintigraphyStatic], imageSeries := [⟨1, true, false, 10⟩] } = none := by decide
example : total { examinations := [exam .scintigraphyStatic], imageSeries := [⟨1, false, false, 10⟩] } = some 16800 := by decide
example : total { examinations := [{ exam .spect with seriesAlreadyCharged := true }] } = some 0 := by decide
example : total { examinations := [pet], diagnosisClaimedThisMonth := true } = some 75000 := by decide
example : (assessWithGeneralRules { examinations := [pet] } {
    entries := [], localStandards := { two := true }, localDedicatedFullTimeDoctorWrittenReport := true } (some .two)).map CombinedAssessment.totalTenths =
    some 81250 := by decide
example : serviceIncluded (.pet .psma) .preparation = true := rfl
example : serviceIncluded (.pet .amyloidOther) .synthesis = false := rfl

end Sanri.MedicalFee.NuclearMedicine
