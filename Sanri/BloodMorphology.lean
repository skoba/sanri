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

def microscopicStainRule : Rule Context Nat :=
  ⟨"D005.6-stain", primary "PDF176頁 D005の6の注", fun c p =>
    c.item = .microscopicDifferential → ∃ stains, c.stains = some stains ∧
      p = Item.microscopicDifferential.stainRate * stains.eraseDups.length⟩

def marrowStainRule : Rule Context Nat :=
  ⟨"D005.14-stain", primary "PDF176頁 D005の14の注", fun c p =>
      c.item = .boneMarrowPicture → ∃ stains, c.stains = some stains ∧
      p = Item.boneMarrowPicture.stainRate * stains.eraseDups.length⟩

/-- D005の個別実施料モデルでは、6・14の注で扱う染色加算だけを集計する。
その対象外の加算成分を0とする閉世界仮定であり、独立した条項の転記ではない。 -/
def ClosedWorldStainPoints (c : Context) (p : Nat) : Prop :=
  c.item ≠ .microscopicDifferential → c.item ≠ .boneMarrowPicture → p = 0

/-- 通知(6)の染色種類は入力型 Stain で固定する。 -/
def StainPoints (c : Context) (p : Nat) : Prop :=
  Satisfies [microscopicStainRule, marrowStainRule] c p ∧
    ClosedWorldStainPoints c p

theorem stainPoints_iff (c : Context) (p : Nat) :
    StainPoints c p ↔ stainAddition c = some p := by
  cases hi : c.item <;> cases hc : c.stains <;>
    simp [StainPoints, ClosedWorldStainPoints, satisfies_cons, satisfies_nil, microscopicStainRule, marrowStainRule,
      stainAddition, Item.stainRate, hi, hc, eq_comm]

/-- モデルで確認する通知の個別要件。ESRの院内要件も保持する。 -/
def esrPerformanceRule : Rule Context Unit :=
  ⟨"D005(1)-esrPerformance", notice "PDF338頁 D005(1)", fun c _ =>
    c.item = .esr → c.esrInHouse = some true ∧
      (c.esrContracted = some false ∨
        c.esrContracted = some true ∧ c.esrPromptReport = some true)⟩

def cellClassRule : Rule Context Unit :=
  ⟨"D005(2)-cellClass", notice "PDF338頁 D005(2)", fun c _ =>
    c.item = .automatedDifferential ∨ c.item = .microscopicDifferential ∨
    c.item = .boneMarrowPicture →
      ∃ classes, c.cellClasses = some classes ∧
        ∀ k ∈ ([.lymphocyte, .monocyte, .neutrophil, .eosinophil, .basophil] :
          List CellClass), k ∈ classes⟩

def bloodCountRule : Rule Context Unit :=
  ⟨"D005(4)-bloodCount", notice "PDF338頁 D005(4)", fun c _ =>
    c.item = .completeBloodCount → ∃ counts, c.counts = some counts ∧ counts ≠ []⟩

def malariaMethodRule : Rule Context Unit :=
  ⟨"D005(7)-malariaMethod", notice "PDF338頁 D005(7)", fun c _ =>
    c.item = .dnaContainingRedCellCount → c.meetsMalariaTestRequirements = some true⟩

def resistanceMethodRule : Rule Context Unit :=
  ⟨"D005(8)-resistanceMethod", notice "PDF338頁 D005(8)", fun c _ =>
    c.item = .redCellResistance →
      ∃ method, c.resistanceMethod = some method ∧ method ≠ .other⟩

def a1cMonthlyRule : Rule Context Unit :=
  ⟨"D005(9)-a1cMonthly", notice "PDF339頁 D005(9)", fun c _ =>
    c.item = .hemoglobinA1c → c.a1cMonthlyAllowance = some true⟩

def thymidineKinaseRule : Rule Context Unit :=
  ⟨"D005(10)-thymidineKinase", notice "PDF339頁 D005(10)", fun c _ =>
    c.item = .thymidineKinaseActivity → c.meetsDiseaseAndPurpose = some true⟩

def terminalTransferaseRule : Rule Context Unit :=
  ⟨"D005(11)-terminalTransferase", notice "PDF339頁 D005(11)", fun c _ =>
    c.item = .terminalDeoxynucleotidylTransferase → c.meetsDiseaseAndPurpose = some true⟩

def tumorAntigenRule : Rule Context Unit :=
  ⟨"D005(12)-tumorAntigen", notice "PDF339頁 D005(12)", fun c _ =>
    c.item = .tumorCellAntigens → c.meetsTumorAntigenRequirements = some true⟩

def eligibilityRules : List (Rule Context Unit) :=
  [esrPerformanceRule, cellClassRule, bloodCountRule,
    malariaMethodRule, resistanceMethodRule, a1cMonthlyRule,
    thymidineKinaseRule, terminalTransferaseRule, tumorAntigenRule]

def Eligibility (c : Context) : Prop :=
  Satisfies eligibilityRules c ()

theorem eligibility_iff (c : Context) : Eligibility c ↔ eligible c = some true := by
  cases hi : c.item <;> simp [Eligibility, eligibilityRules, satisfies_cons, satisfies_nil,
    esrPerformanceRule, cellClassRule, bloodCountRule,
    malariaMethodRule, resistanceMethodRule, a1cMonthlyRule, thymidineKinaseRule,
    terminalTransferaseRule, tumorAntigenRule, eligible, hi]
  all_goals (try split <;> simp_all)
  all_goals (try cases hc : c.cellClasses <;> simp_all [List.all_eq_true])
  all_goals (try cases hc : c.counts <;> simp_all)
  all_goals (try cases hc : c.resistanceMethod <;> simp_all)
  all_goals
    cases h₁ : c.esrInHouse <;> cases h₂ : c.esrContracted <;>
      simp_all <;> rename_i a b <;> cases a <;> cases b <;> simp_all

def stainRule : Rule Context (Nat × Nat) :=
  ⟨"D005.stains", primary "PDF176頁 D005の6・14の注",
    fun c r => StainPoints c r.2⟩

def esrLocationRule : Rule Context (Nat × Nat) :=
  ⟨"D005.1-note", primary "PDF175頁 D005の1の注",
    fun c _ => c.item = .esr → c.esrInHouse = some true⟩

def eligibilityRule : Rule Context (Nat × Nat) :=
  ⟨"D005.eligibility", notice "PDF338–339頁 D005(1)・(2)・(4)・(6)〜(12)",
    fun c _ => Eligibility c⟩

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
    baseRule, stainRule, eligibilityRule, esrLocationRule, eligibility_iff, stainPoints_iff]
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

theorem determines_individual_on :
    DeterminesOn (fun c => Eligibility c ∧ ∃ p, StainPoints c p) individualRules := by
  rintro c ⟨he, p, hp⟩
  exact individual_determines c c.item.basePoints p
    (by simp [assess, (eligibility_iff c).mp he, (stainPoints_iff c p).mp hp])

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

example : Eligibility differential ∧ ∃ p, StainPoints differential p :=
  ⟨(eligibility_iff _).mpr rfl, 104, (stainPoints_iff _ _).mpr rfl⟩

example : ¬ ∃ p, StainPoints { differential with stains := none } p := by
  simp [stainPoints_iff, differential, stainAddition, Item.stainRate]

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
