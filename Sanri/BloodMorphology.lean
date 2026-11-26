import Sanri.Logic
import Sanri.SpecimenJudgment
import Sanri.OutpatientConsultation

namespace Sanri.MedicalFee.BloodMorphology

open Sanri.Logic

inductive Item where
  | esr | reticulocytes | bloodOsmolality | nasalOrSputumEosinophils | automatedDifferential
  | eosinophilCount | completeBloodCount | microscopicDifferential
  | bloodMicroorganisms | dnaContainingRedCellCount | redCellResistance | hemoglobinA1c
  | autohemolysis | bloodViscosity | hemoglobinF | thymidineKinaseActivity
  | terminalDeoxynucleotidylTransferase | boneMarrowPicture | tumorCellAntigens
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .esr => 1
  | .reticulocytes => 2
  | .bloodOsmolality | .nasalOrSputumEosinophils | .automatedDifferential => 3
  | .eosinophilCount => 4
  | .completeBloodCount => 5
  | .microscopicDifferential => 6
  | .bloodMicroorganisms | .dnaContainingRedCellCount => 7
  | .redCellResistance => 8
  | .hemoglobinA1c => 9
  | .autohemolysis | .bloodViscosity => 10
  | .hemoglobinF => 11
  | .thymidineKinaseActivity => 12
  | .terminalDeoxynucleotidylTransferase => 13
  | .boneMarrowPicture => 14
  | .tumorCellAntigens => 15

def Item.basePoints : Item → Nat
  | .esr => 9
  | .reticulocytes => 12
  | .bloodOsmolality | .nasalOrSputumEosinophils | .automatedDifferential => 15
  | .eosinophilCount => 17
  | .completeBloodCount => 21
  | .microscopicDifferential => 25
  | .bloodMicroorganisms | .dnaContainingRedCellCount => 40
  | .redCellResistance => 45
  | .hemoglobinA1c => 49
  | .autohemolysis | .bloodViscosity => 50
  | .hemoglobinF => 60
  | .thymidineKinaseActivity => 233
  | .terminalDeoxynucleotidylTransferase => 250
  | .boneMarrowPicture => 788
  | .tumorCellAntigens => 1882

inductive BloodCountItem where
  | redCells | whiteCells | hemoglobin | hematocrit | platelets
  deriving DecidableEq, Repr

def bloodCountPoints (items : List BloodCountItem) : Nat :=
  if items.isEmpty then 0 else Item.completeBloodCount.basePoints

inductive CellClass where
  | lymphocyte | monocyte | neutrophil | eosinophil | basophil
  deriving DecidableEq, Repr

inductive Stain where
  | oxidase | peroxidase | alkalinePhosphatase | pas | iron | supravital | lipid | esterase
  deriving DecidableEq, Repr

inductive ResistanceMethod where
  | sugarWater | ham | crossBeet | parpart | sanford | other
  deriving DecidableEq, Repr

structure Context where
  item : Item
  /-- ESRの実施形態。委託の場合には院内実施と速やかな結果報告を確認する。 -/
  esrInHouse : Option Bool := none
  esrContracted : Option Bool := none
  esrPromptReport : Option Bool := none
  /-- 同定と比率計算の両方を行った分類。 -/
  cellClasses : Option (List CellClass) := none
  counts : Option (List BloodCountItem) := none
  /-- 通知(6)の染色の種類。記録上の同じ種類の重複は数えない。 -/
  stains : Option (List Stain) := none
  resistanceMethod : Option ResistanceMethod := none
  /-- 通知(7)の疑い・診断目的・装置・定性判定をすべて確認した外部入力。 -/
  meetsMalariaTestRequirements : Option Bool := none
  /-- 通知(10)・(11)の疾病と診断／治療効果判定目的を確認した外部入力。 -/
  meetsDiseaseAndPurpose : Option Bool := none
  /-- 通知(12)の対象、抗体承認、検査手法、病型分類を確認した外部入力。 -/
  meetsTumorAntigenRequirements : Option Bool := none
  /-- D007の2検査も含めた月内規則・例外を適用した上で今回を算定できるか。 -/
  a1cMonthlyAllowance : Option Bool := none
  deriving DecidableEq, Repr

def eligible (c : Context) : Option Bool :=
  match c.item with
  | .esr => do
    if !(← c.esrInHouse) then return false
    if ← c.esrContracted then c.esrPromptReport else return true
  | .automatedDifferential | .microscopicDifferential | .boneMarrowPicture =>
    c.cellClasses.map (fun classes => [.lymphocyte, .monocyte, .neutrophil, .eosinophil,
      .basophil].all classes.contains)
  | .completeBloodCount => c.counts.map (fun counts => !counts.isEmpty)
  | .dnaContainingRedCellCount => c.meetsMalariaTestRequirements
  | .redCellResistance => c.resistanceMethod.map (· != .other)
  | .hemoglobinA1c => c.a1cMonthlyAllowance
  | .thymidineKinaseActivity | .terminalDeoxynucleotidylTransferase => c.meetsDiseaseAndPurpose
  | .tumorCellAntigens => c.meetsTumorAntigenRequirements
  | _ => some true

def Item.stainRate : Item → Nat
  | .microscopicDifferential => 52
  | .boneMarrowPicture => 60
  | _ => 0

def stainAddition (c : Context) : Option Nat :=
  -- 通知(5)の鏡検方式・赤血球直径測定による点数変更はない。
  if c.item.stainRate = 0 then some 0
  else c.stains.map (fun stains => c.item.stainRate * stains.eraseDups.length)

inductive Assessment where
  | payable (base stain : Nat)
  | ineligible
  | unresolved
  deriving DecidableEq, Repr

/-- 実施済みの一件について、他の検査との組合せや上位の包括を適用する前の評価。
D005の15は一連を一件として与える。 -/
def assess (c : Context) : Assessment :=
  match eligible c with
  | none => .unresolved
  | some false => .ineligible
  | some true =>
    match stainAddition c with
    | none => .unresolved
    | some stain => .payable c.item.basePoints stain

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "2026-10-22取得版",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def baseRule : Rule Context (Nat × Nat) :=
  ⟨"D005.base", primary "PDF175–176頁 D005の1〜15",
    fun c r => r.1 = c.item.basePoints⟩

def stainRule : Rule Context (Nat × Nat) :=
  ⟨"D005.stains", primary "PDF176頁 D005の6・14の注",
    fun c r => stainAddition c = some r.2⟩

def esrLocationRule : Rule Context (Nat × Nat) :=
  ⟨"D005.1-note", primary "PDF175頁 D005の1の注",
    fun c _ => c.item = .esr → c.esrInHouse = some true⟩

def eligibilityRule : Rule Context (Nat × Nat) :=
  ⟨"D005.eligibility", notice "PDF338–339頁 D005(1)・(2)・(4)・(6)〜(12)",
    fun c _ => eligible c = some true⟩

def individualRules := [baseRule, stainRule, eligibilityRule, esrLocationRule]

private theorem eligible_esr_in_house (c : Context) (h : eligible c = some true)
    (esr : c.item = .esr) : c.esrInHouse = some true := by
  cases location : c.esrInHouse with
  | none => simp [eligible, esr, location] at h
  | some inside =>
    cases inside
    · simp [eligible, esr, location] at h
    · rfl

theorem payable_iff (c : Context) (base stain : Nat) :
    Satisfies individualRules c (base, stain) ↔ assess c = .payable base stain := by
  simp only [individualRules, satisfies_cons, satisfies_nil, and_true,
    baseRule, stainRule, eligibilityRule, esrLocationRule]
  cases h : eligible c with
  | none => simp [assess, h]
  | some value =>
    cases value
    · simp [assess, h]
    · have location := eligible_esr_in_house c h
      cases hs : stainAddition c with
      | none => simp [assess, h, hs]
      | some value =>
        simp [assess, h, hs]
        exact ⟨fun ⟨hb, hs, _⟩ => ⟨hb.symm, hs⟩, fun ⟨hb, hs⟩ => ⟨hb.symm, hs, location⟩⟩

theorem individual_determines (c : Context) (base stain : Nat)
    (h : assess c = .payable base stain) : DeterminesAt individualRules c := by
  refine ⟨⟨(base, stain), (payable_iff c base stain).2 h⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨x, y⟩ first second
  have eq := ((payable_iff c a b).1 first).symm.trans ((payable_iff c x y).1 second)
  cases eq
  rfl

/-- 同一患者・機関について、個別要件を確認済みの二件を組み合わせる。
通知でいう同一検体と、マラリア診断目的での併施を別々に入力する。 -/
structure PairContext where
  first : Item
  second : Item
  sameSpecimen : Bool
  performedTogetherForMalariaDiagnosis : Bool
  principal : Option Item
  deriving DecidableEq, Repr

def PairContext.categoryConflict (c : PairContext) : Bool :=
  let differential := fun item : Item => item == .automatedDifferential || item == .microscopicDifferential
  c.sameSpecimen && ((c.first == .eosinophilCount && differential c.second) ||
    (c.second == .eosinophilCount && differential c.first))

def PairContext.malariaConflict (c : PairContext) : Bool :=
  c.performedTogetherForMalariaDiagnosis &&
    ((c.first == .bloodMicroorganisms && c.second == .dnaContainingRedCellCount) ||
      (c.second == .bloodMicroorganisms && c.first == .dnaContainingRedCellCount))

def PairContext.principalOnly (c : PairContext) (charged : List Item) : Prop :=
  ∃ item, c.principal = some item ∧ (item = c.first ∨ item = c.second) ∧ charged = [item]

def eosinophilRule : Rule PairContext (List Item) :=
  ⟨"D005.3-notice", notice "PDF338頁 D005(3)",
    fun c charged => c.categoryConflict = true → c.principalOnly charged⟩

def malariaRule : Rule PairContext (List Item) :=
  ⟨"D005.7-notice", notice "PDF338頁 D005(7)",
    fun c charged => c.malariaConflict = true → c.principalOnly charged⟩

def Item.outpatientService (item : Item) : OutpatientConsultation.Service :=
  .bloodD005 (match item with
    | .hemoglobinA1c => .hemoglobinA1c
    | .thymidineKinaseActivity => .thymidineKinaseActivity
    | .terminalDeoxynucleotidylTransferase => .terminalDeoxynucleotidylTransferase
    | .boneMarrowPicture => .boneMarrowPicture
    | .tumorCellAntigens => .hematopoieticTumorCellAntigenSeries
    | _ => .otherD005)

def Item.judgmentTest (item : Item) (writtenBySpecialist : Bool) : SpecimenJudgment.Test :=
  { major := 5, number := item.number, ordinaryCategory := .hematological,
    specialistWrittenReport := writtenBySpecialist }

private def differential : Context :=
  { item := .microscopicDifferential
    cellClasses := some [.lymphocyte, .monocyte, .neutrophil, .eosinophil, .basophil]
    stains := some [.iron, .pas] }

example : assess differential = .payable 25 104 := by decide
example : assess { differential with item := .boneMarrowPicture } = .payable 788 120 := by decide
example : assess { differential with
    cellClasses := some [.lymphocyte, .monocyte, .neutrophil, .eosinophil, .eosinophil] } =
    .ineligible := by decide
example : assess { differential with stains := none } = .unresolved := by decide
example : assess { item := .esr, esrInHouse := some false } = .ineligible := by decide
example : assess { item := .hemoglobinA1c } = .unresolved := by decide
example : DeterminesAt individualRules differential := individual_determines _ 25 104 rfl

example : OutpatientConsultation.includedByNote6 Item.completeBloodCount.outpatientService = true := rfl
example : OutpatientConsultation.includedByNote6 Item.boneMarrowPicture.outpatientService = false := rfl
example : SpecimenJudgment.boneMarrowEligible (Item.boneMarrowPicture.judgmentTest true) = true := rfl

private def sameSpecimenPair : PairContext :=
  ⟨.eosinophilCount, .automatedDifferential, true, false, some .automatedDifferential⟩

example : Satisfies [eosinophilRule, malariaRule] sameSpecimenPair [.automatedDifferential] := by
  simp only [satisfies_cons, satisfies_nil, eosinophilRule, malariaRule]
  refine ⟨fun _ => ⟨_, rfl, Or.inr rfl, rfl⟩, ?_, trivial⟩
  intro h
  cases h

example : ¬ Satisfies [eosinophilRule] sameSpecimenPair [.eosinophilCount, .automatedDifferential] := by
  simp only [satisfies_cons, satisfies_nil, and_true, eosinophilRule]
  intro h
  obtain ⟨item, _, _, eq⟩ := h rfl
  cases eq

private def malariaPair : PairContext :=
  ⟨.bloodMicroorganisms, .dnaContainingRedCellCount, false, true, some .bloodMicroorganisms⟩

example : Satisfies [malariaRule] malariaPair [.bloodMicroorganisms] := by
  rw [satisfies_cons]
  exact ⟨fun _ => ⟨_, rfl, Or.inl rfl, rfl⟩, satisfies_nil _ _⟩

end Sanri.MedicalFee.BloodMorphology
