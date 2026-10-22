import Sanri.Examinations

namespace Sanri.MedicalFee.UrineFecalTests

/-! Ｄ０００〜Ｄ００３。準用区分の点数・注は当該区分の仕様で解決して入力する。
院内実施条件を課すのは、提示本文で明示されたＤ０００・Ｄ００２・Ｄ００２－２。
委託する場合の第３部通則６は Examinations.SpecimenSource.outsourcedで別途扱う。 -/

inductive OtherReference where
  | d007
  | d008
  | d009
  | d010
  deriving DecidableEq, Repr

inductive ReferenceSection where
  | d015
  | other (target : OtherReference)
  deriving DecidableEq, Repr

inductive UrineSpecial where
  | protein
  | vmaQualitative
  | glucose
  | urobilinogen
  | congenitalMetabolicScreening
  | osmolality
  | porphyriaScreening
  | nag
  | albuminQualitative
  | lhQualitative
  | fdp
  | transferrin
  | albuminQuantitative
  | uroporphyrin
  | trypsinogen2
  | deltaAla
  | polyamines
  | myoinositol
  | coproporphyrin
  | typeIVCollagen
  | totalIodine
  | porphobilinogen
  | prostaglandinEMajorMetabolite
  | oxalate
  | lFabp
  | ngal
  | proteinImmunology
  | other (target : OtherReference)
  deriving DecidableEq, Repr

inductive Fecal where
  | concentratedOvaDetection
  | urobilin
  | smearMicroscopy
  | parasiteDetection
  | lipids
  | hemoglobinQualitative
  | ovaCulture
  | hemoglobin
  | hemoglobinAndTransferrinQualitativeQuantitative
  | calprotectin
  deriving DecidableEq, Repr

inductive Item where
  | generalUrine -- Ｄ０００
  | specialUrine (test : UrineSpecial) -- Ｄ００１
  | urineSedimentMicroscopy -- Ｄ００２
  | urineSedimentFlowCytometry -- Ｄ００２－２
  | fecal (test : Fecal) -- Ｄ００３
  deriving DecidableEq, Repr

inductive PointRule where
  | fixed (points : Nat)
  | reference (target : ReferenceSection) (applySectionNotes : Bool)
  deriving DecidableEq, Repr

def urineSpecialPointRule : UrineSpecial → PointRule
  | .protein => .fixed 7
  | .vmaQualitative | .glucose => .fixed 9
  | .urobilinogen | .congenitalMetabolicScreening | .osmolality => .fixed 16
  | .porphyriaScreening => .fixed 17
  | .nag => .fixed 41
  | .albuminQualitative => .fixed 49
  | .lhQualitative => .fixed 72
  | .fdp => .fixed 77
  | .transferrin => .fixed 98
  | .albuminQuantitative => .fixed 99
  | .uroporphyrin | .trypsinogen2 => .fixed 105
  | .deltaAla => .fixed 106
  | .polyamines => .fixed 115
  | .myoinositol => .fixed 120
  | .coproporphyrin => .fixed 131
  | .typeIVCollagen => .fixed 179
  | .totalIodine | .porphobilinogen => .fixed 186
  | .prostaglandinEMajorMetabolite => .fixed 187
  | .oxalate => .fixed 200
  | .lFabp | .ngal => .fixed 210
  | .proteinImmunology => .reference .d015 false
  | .other target => .reference (.other target) true

def fecalPoints : Fecal → Nat
  | .concentratedOvaDetection | .urobilin => 15
  | .smearMicroscopy => 20
  | .parasiteDetection => 23
  | .lipids => 25
  | .hemoglobinQualitative => 37
  | .ovaCulture => 40
  | .hemoglobin => 41
  | .hemoglobinAndTransferrinQualitativeQuantitative => 56
  | .calprotectin => 268

def pointRule : Item → PointRule
  | .generalUrine => .fixed 26
  | .specialUrine t => urineSpecialPointRule t
  | .urineSedimentMicroscopy => .fixed 27
  | .urineSedimentFlowCytometry => .fixed 24
  | .fecal t => .fixed (fecalPoints t)

def requiresInHouse : Item → Bool
  | .generalUrine | .urineSedimentMicroscopy | .urineSedimentFlowCytometry => true
  | _ => false

def isSediment : Item → Bool
  | .urineSedimentMicroscopy | .urineSedimentFlowCytometry => true
  | _ => false

structure ReferenceResolution where
  target : ReferenceSection
  points : Nat
  /-- Ｄ００７〜Ｄ０１０の点数準用時は、その注も適用して算定要件を満たしたこと。 -/
  sectionNotesAppliedAndSatisfied : Bool := false
  deriving DecidableEq, Repr

inductive MainTest where
  | urineSediment
  | d017BacterialMicroscopy
  deriving DecidableEq, Repr

structure Context where
  item : Item
  insuranceMedicalInstitution : Bool := true
  testPerformed : Bool := true
  performedInsideInstitution : Bool := false
  /-- 同じ検体にＤ０１７の対象細菌顕微鏡検査を併施した場合に限る。 -/
  sameSpecimenD017Performed : Bool := false
  mainTest : MainTest := .urineSediment
  stainedSpecimenExamined : Bool := false
  referenceResolution : Option ReferenceResolution := none
  deriving DecidableEq, Repr

structure Charge where
  base : Nat
  stainedSpecimenAddition : Nat := 0
  deriving DecidableEq, Repr

def Charge.total (c : Charge) : Nat := c.base + c.stainedSpecimenAddition

inductive Assessment where
  | charged (charge : Charge)
  /-- Ｄ００２・Ｄ００２－２は算定せず、主たるＤ０１７をその区分で算定する。 -/
  | onlyMainD017
  | requiresReference (target : ReferenceSection) (applySectionNotes : Bool)
  deriving DecidableEq, Repr

/-- 別区分の準用が未解決の場合は明示し、０点や算定不可と区別する。 -/
def assess (c : Context) : Option Assessment :=
  if !(c.insuranceMedicalInstitution && c.testPerformed) ||
      (requiresInHouse c.item && !c.performedInsideInstitution) then none
  else if isSediment c.item && c.sameSpecimenD017Performed &&
      decide (c.mainTest = .d017BacterialMicroscopy) then some .onlyMainD017
  else
    let stain := if c.item = .urineSedimentMicroscopy && c.stainedSpecimenExamined then 9 else 0
    match pointRule c.item with
    | .fixed base => some (.charged ⟨base, stain⟩)
    | .reference target notes =>
      match c.referenceResolution with
      | none => some (.requiresReference target notes)
      | some resolution =>
        if resolution.target = target && (!notes || resolution.sectionNotesAppliedAndSatisfied) then
          some (.charged ⟨resolution.points, 0⟩)
        else none

/-- 点数が解決した検査のみを通則の入力へ変換する。
Ｄ０１７側が主の場合は検体検査項目を追加せず、迅速加算の項目数にも数えない。
kind は通則の他の入力と共通の検査識別子を呼出元が割り当てる。 -/
def Assessment.toSpecimenItem (a : Assessment) (kind : Nat) : Option Examinations.SpecimenItem :=
  match a with
  | .charged charge => some { kind := kind, executionPoints := charge.total }
  | _ => none

/-- Ａ００２注６の包括範囲へ接続する。対象外という結果だけで別算定可能とはしない。 -/
def outpatientService : Item → OutpatientConsultation.Service
  | .fecal .calprotectin => .fecalD003 .calprotectin
  | .fecal _ => .fecalD003 .otherD003
  | _ => .urineD000ThroughD002_2

private def sediment : Context :=
  { item := .urineSedimentMicroscopy
    performedInsideInstitution := true }
private def referenceUrine : Context :=
  { item := .specialUrine (.other .d007) }

example : (List.map urineSpecialPointRule
    [.protein, .vmaQualitative, .glucose, .urobilinogen, .congenitalMetabolicScreening,
     .osmolality, .porphyriaScreening, .nag, .albuminQualitative, .lhQualitative, .fdp,
     .transferrin, .albuminQuantitative, .uroporphyrin, .trypsinogen2, .deltaAla,
     .polyamines, .myoinositol, .coproporphyrin, .typeIVCollagen, .totalIodine,
     .porphobilinogen, .prostaglandinEMajorMetabolite, .oxalate, .lFabp, .ngal]) =
    (List.map PointRule.fixed
      [7, 9, 9, 16, 16, 16, 17, 41, 49, 72, 77, 98, 99, 105, 105, 106,
       115, 120, 131, 179, 186, 186, 187, 200, 210, 210]) := by decide
example : (List.map fecalPoints
    [.concentratedOvaDetection, .urobilin, .smearMicroscopy, .parasiteDetection, .lipids,
     .hemoglobinQualitative, .ovaCulture, .hemoglobin, .hemoglobinAndTransferrinQualitativeQuantitative,
     .calprotectin]) = [15, 15, 20, 23, 25, 37, 40, 41, 56, 268] := by decide
example : assess { item := .generalUrine } = none := by decide
example : assess { item := .generalUrine, performedInsideInstitution := true } =
    some (.charged ⟨26, 0⟩) := by decide
example : assess sediment = some (.charged ⟨27, 0⟩) := by decide
example : assess { sediment with performedInsideInstitution := false } = none := by decide
example : assess { sediment with insuranceMedicalInstitution := false } = none := by decide
example : assess { sediment with testPerformed := false } = none := by decide
example : assess { sediment with stainedSpecimenExamined := true } =
    some (.charged ⟨27, 9⟩) := by decide
example : assess { sediment with
    item := .urineSedimentFlowCytometry
    stainedSpecimenExamined := true } = some (.charged ⟨24, 0⟩) := by decide
example : assess { sediment with
    item := .urineSedimentFlowCytometry
    performedInsideInstitution := false } = none := by decide
example : assess { sediment with
    sameSpecimenD017Performed := true
    mainTest := .d017BacterialMicroscopy
    stainedSpecimenExamined := true } = some .onlyMainD017 := by decide
example : assess { sediment with
    item := .urineSedimentFlowCytometry
    sameSpecimenD017Performed := true
    mainTest := .d017BacterialMicroscopy } = some .onlyMainD017 := by decide
example : assess { sediment with
    sameSpecimenD017Performed := true
    stainedSpecimenExamined := true } = some (.charged ⟨27, 9⟩) := by decide
example : assess { sediment with mainTest := .d017BacterialMicroscopy } =
    some (.charged ⟨27, 0⟩) := by decide
example : assess { item := .specialUrine .protein } = some (.charged ⟨7, 0⟩) := by decide
example : assess { item := .fecal .calprotectin } = some (.charged ⟨268, 0⟩) := by decide
example : assess { item := .specialUrine .proteinImmunology } =
    some (.requiresReference .d015 false) := by decide
example : (List.map (fun t => pointRule (.specialUrine (.other t))) [.d007, .d008, .d009, .d010]) =
    [.reference (.other .d007) true, .reference (.other .d008) true,
     .reference (.other .d009) true, .reference (.other .d010) true] := by decide
example : assess referenceUrine = some (.requiresReference (.other .d007) true) := by decide
-- 準用点数123点は検証用の仮の値。
example : assess { referenceUrine with
    referenceResolution := some ⟨.other .d007, 123, false⟩ } = none := by decide
example : assess { referenceUrine with
    referenceResolution := some ⟨.other .d008, 123, true⟩ } = none := by decide
example : assess { referenceUrine with
    referenceResolution := some ⟨.other .d007, 123, true⟩ } = some (.charged ⟨123, 0⟩) := by decide
example : assess {
    item := .specialUrine .proteinImmunology
    referenceResolution := some ⟨.d015, 123, false⟩ } = some (.charged ⟨123, 0⟩) := by decide
example : Assessment.toSpecimenItem (.charged ⟨27, 9⟩) 2 =
    some { kind := 2, executionPoints := 36 } := rfl
example : Assessment.toSpecimenItem .onlyMainD017 2 = none := rfl
example : Assessment.toSpecimenItem (.requiresReference (.other .d007) true) 2 = none := rfl
example : OutpatientConsultation.includedByNote6 (outpatientService .generalUrine) = true := rfl
example : OutpatientConsultation.includedByNote6 (outpatientService (.specialUrine .proteinImmunology)) =
    true := rfl
example : OutpatientConsultation.includedByNote6 (outpatientService (.fecal .hemoglobin)) = true := rfl
example : OutpatientConsultation.includedByNote6 (outpatientService (.fecal .calprotectin)) = false := rfl

/-- 尿・糞便項目の基本点数を検体検査通則の実施料へ引き渡せる。 -/
example : Examinations.assessSpecimen {
    items := [{ kind := 2, executionPoints := 36 }]
    judgmentPoints := 0 } = some ⟨36, 0, 0, 0⟩ := by decide

end Sanri.MedicalFee.UrineFecalTests
