import Sanri.D004Tumor

namespace Sanri.MedicalFee.D006GeneTests

open Sanri.Logic Sanri.History

private def primary (code : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF178頁 " ++ code, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (page : Nat) (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF" ++ toString page ++ "頁 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private theorem determines_fixed {C : Type} (rules : List (Rule C Nat)) (scope : C → Prop)
    (points : Nat) (spec : ∀ c p, Satisfies rules c p ↔ p = points ∧ scope c) :
    DeterminesOn scope rules := by
  intro c eligible
  exact ⟨⟨points, (spec _ _).mpr ⟨rfl, eligible⟩⟩,
    fun a b ha hb => ((spec _ _).mp ha).1.trans ((spec _ _).mp hb).1.symm⟩

inductive Item where
  | immuneRearrangement | ugtPolymorphism | krt19 | wt1
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.immuneRearrangement, .ugtPolymorphism, .krt19, .wt1]

def Item.suffix : Item → Nat
  | .immuneRearrangement => 6
  | .ugtPolymorphism => 7
  | .krt19 => 8
  | .wt1 => 9

def Item.number (_ : Item) : Option Nat := none

theorem modeled_number (i : Item) : i.number = none ∧ 6 ≤ i.suffix ∧ i.suffix ≤ 9 := by
  cases i <;> decide

def Item.points : Item → Nat
  | .immuneRearrangement => 2362
  | .ugtPolymorphism => 2004
  | .krt19 => 2400
  | .wt1 => 2520

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := i.suffix, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := by
  cases i <;> rfl

inductive Method where
  | pcr | lcr | southernBlot | invader | osna | realtimeRtPcr | other
  deriving DecidableEq

inductive Disease where
  | malignantLymphoma | acuteLymphoblasticLeukemia | chronicLymphocyticLeukemia
  | acuteMyeloidLeukemia | myelodysplasticSyndrome
  | breastCancer | gastricCancer | colorectalCancer | nonSmallCellLungCancer | other
  deriving DecidableEq

inductive Purpose where
  | diagnosis | doseDetermination | nodalDiagnosisAndTreatmentPlanning
  | diagnosticSupport | followup | other
  deriving DecidableEq

/-- 個別区分で起算点が未確定の照会。履歴は当該候補以前の算定分に限る。 -/
structure ClaimWindow (item : Item) where
  period : Period
  history : ClaimHistory Item

def ClaimWindow.prior (window : ClaimWindow item) (site : Site) : Option Nat :=
  if window.period.Contains site.date then
    count window.history ⟨site.patient, none, window.period⟩ (· == item)
  else none

namespace Immune

structure Context where
  site : Site
  method : Option Method := none
  disease : Option Disease := none
  purpose : Option Purpose := none
  sixMonthWindow : Option (ClaimWindow .immuneRearrangement) := none
  monthlySelection : Option D004Tumor.MonthlySelection := none

def MethodAndFrequency (c : Context) : Prop :=
  (∃ m ∈ [Method.pcr, .lcr, .southernBlot], c.method = some m) ∧
  (∃ d ∈ [Disease.malignantLymphoma, .acuteLymphoblasticLeukemia,
      .chronicLymphocyticLeukemia], c.disease = some d) ∧
  c.purpose = some .diagnosis ∧
  (c.sixMonthWindow.bind (·.prior c.site)) = some 0

def Principal (c : Context) : Prop :=
  ∃ s, c.monthlySelection = some s ∧
    s.Allows c.site [.d004_2_1, .d006_2, .d006_14, .d006_16]

def Eligible (c : Context) : Prop := MethodAndFrequency c ∧ Principal c

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-6/heading", primary "D006-6", fun _ p => p = 2362⟩

def frequencyRule : Rule Context Nat :=
  ⟨"notice/D006-6/paragraph/1", notice 344 "D006-6(1)", fun c _ => MethodAndFrequency c⟩

def combinationRule : Rule Context Nat :=
  ⟨"notice/D006-6/paragraph/2", notice 344 "D006-6(2)", fun c _ => Principal c⟩

def rules := [headingRule, frequencyRule, combinationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.immuneRearrangement.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, frequencyRule, combinationRule,
    Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

end Immune

namespace Ugt

structure Context where
  site : Site
  irinotecanCandidate : Option Bool := none
  purpose : Option Purpose := none
  method : Option Method := none
  beforeTreatmentDecision : Option Bool := none
  decisionWindow : Option (ClaimWindow .ugtPolymorphism) := none

def Eligible (c : Context) : Prop :=
  c.irinotecanCandidate = some true ∧ c.purpose = some .doseDetermination ∧
  (c.method = some .invader ∨ c.method = some .pcr) ∧
  c.beforeTreatmentDecision = some true ∧
  (c.decisionWindow.bind (·.prior c.site)) = some 0

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-7/heading", primary "D006-7", fun _ p => p = 2004⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-7/paragraph/unnumbered", notice 344 "D006-7", fun c _ => Eligible c⟩

def rules := [headingRule, indicationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.ugtPolymorphism.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, Item.points]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

end Ugt

namespace Krt19

structure Context where
  performance : Performance Item
  disease : Option Disease := none
  /-- 視触診等または術前画像で転移陽性が明らかかの確認済み評価。 -/
  nodalMetastasisEvident : Option Bool := none
  excisedRegionalNode : Option Bool := none
  purpose : Option Purpose := none
  method : Option Method := none
  seriesPeriod : Option Period := none
  priorPerformances : Option (Snapshot (Performance Item)) := none
  priorClaims : Option (ClaimHistory Item) := none

/-- 網羅性を確認した実施一覧と算定記録を実施IDで結ぶ。どちらかが不足すれば未確定。 -/
def priorInSeries (c : Context) : Option Nat := do
  let _ ← c.performance.series
  let period ← c.seriesPeriod
  let performances ← c.priorPerformances
  let claims ← c.priorClaims
  let site := c.performance.site
  let query : Scope := ⟨site.patient, some site.institution, period⟩
  let performed ← performances.select Performance.site query (·.item == .krt19)
  let charged ← claims.toSnapshot.select Claim.site query (·.item == .krt19)
  let sameSeries ← charged.mapM fun claim => do
    let id ← claim.performance
    let p ← performed.find? (·.id == id)
    c.performance.sameSeries p
  return (sameSeries.filter id).length

def Eligible (c : Context) : Prop :=
  c.performance.item = .krt19 ∧
  (∃ d ∈ [Disease.breastCancer, .gastricCancer, .colorectalCancer, .nonSmallCellLungCancer],
    c.disease = some d) ∧
  c.nodalMetastasisEvident = some false ∧ c.excisedRegionalNode = some true ∧
  c.purpose = some .nodalDiagnosisAndTreatmentPlanning ∧ c.method = some .osna ∧
  priorInSeries c = some 0

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-8/heading", primary "D006-8", fun _ p => p = 2400⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-8/paragraph/unnumbered", notice 344 "D006-8", fun c _ => Eligible c⟩

def rules := [headingRule, indicationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.krt19.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, Item.points]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

end Krt19

namespace Wt1

structure Context where
  site : Site
  method : Option Method := none
  disease : Option Disease := none
  purpose : Option Purpose := none
  priorClaims : Option (ClaimHistory Item) := none

def priorInMonth (c : Context) : Option Nat :=
  c.priorClaims.bind fun h =>
    count h ⟨c.site.patient, none, Period.month c.site.date.month⟩ (· == .wt1)

def Eligible (c : Context) : Prop :=
  c.method = some .realtimeRtPcr ∧
  (∃ d ∈ [Disease.acuteMyeloidLeukemia, .acuteLymphoblasticLeukemia,
      .myelodysplasticSyndrome], c.disease = some d) ∧
  (c.purpose = some .diagnosticSupport ∨ c.purpose = some .followup) ∧
  priorInMonth c = some 0

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-9/heading", primary "D006-9", fun _ p => p = 2520⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-9/paragraph/unnumbered", notice 344 "D006-9", fun c _ => Eligible c⟩

def rules := [headingRule, indicationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.wt1.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, Item.points]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

end Wt1

private def site : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def emptyClaims (scope : Scope) : ClaimHistory Item := ⟨⟨scope, []⟩, by simp⟩

private def emptyWindow (i : Item) : ClaimWindow i :=
  ⟨Period.through site.date, emptyClaims ⟨site.patient, none, Period.through site.date⟩⟩

private def sixMonthExample : Period :=
  ⟨⟨⟨2026, 4⟩, ⟨0, by decide⟩⟩, site.date, by decide⟩

private def immuneExample : Immune.Context :=
  { site, method := some .pcr, disease := some .malignantLymphoma, purpose := some .diagnosis
    sixMonthWindow := some ⟨sixMonthExample,
      emptyClaims ⟨site.patient, none, sixMonthExample⟩⟩
    monthlySelection := some ⟨⟨⟨site.patient, none, Period.month site.date.month⟩, []⟩, none,
      fun _ _ => none⟩ }

example : Satisfies Immune.rules immuneExample 2362 := by
  apply (Immune.satisfies_iff _ _).mpr
  refine ⟨rfl, ⟨⟨.pcr, by simp, rfl⟩, ⟨.malignantLymphoma, by simp, rfl⟩, rfl, rfl⟩, ?_⟩
  exact ⟨_, rfl, [], rfl, Or.inl rfl, by simp⟩

example : ¬ SatisfiableAt Immune.rules { immuneExample with monthlySelection := none } := by
  rintro ⟨p, hp⟩
  have h := ((Immune.satisfies_iff _ _).mp hp).2.2
  simp [Immune.Principal] at h

example : ¬ SatisfiableAt Immune.rules { immuneExample with method := some .other } := by
  rintro ⟨p, hp⟩
  have h := ((Immune.satisfies_iff _ _).mp hp).2.1
  simp [Immune.MethodAndFrequency, immuneExample] at h

private def ugtExample : Ugt.Context :=
  { site, irinotecanCandidate := some true, purpose := some .doseDetermination,
    method := some .invader, beforeTreatmentDecision := some true,
    decisionWindow := some (emptyWindow .ugtPolymorphism) }

example : Satisfies Ugt.rules ugtExample 2004 :=
  (Ugt.satisfies_iff _ _).mpr ⟨rfl, rfl, rfl, Or.inl rfl, rfl, rfl⟩

example : ¬ SatisfiableAt Ugt.rules { ugtExample with decisionWindow := none } := by
  rintro ⟨p, hp⟩
  have h := ((Ugt.satisfies_iff _ _).mp hp).2
  simp [Ugt.Eligible] at h

example : ¬ SatisfiableAt Ugt.rules { ugtExample with beforeTreatmentDecision := some false } := by
  rintro ⟨p, hp⟩
  have h := ((Ugt.satisfies_iff _ _).mp hp).2
  simp [Ugt.Eligible, ugtExample] at h

private def krtExample : Krt19.Context :=
  { performance := ⟨1, site, .krt19, none, none, some 1, none⟩
    disease := some .breastCancer, nodalMetastasisEvident := some false
    excisedRegionalNode := some true, purpose := some .nodalDiagnosisAndTreatmentPlanning
    method := some .osna, seriesPeriod := some (Period.day site.date)
    priorPerformances := some ⟨⟨site.patient, some site.institution, Period.day site.date⟩, []⟩
    priorClaims := some (emptyClaims ⟨site.patient, some site.institution, Period.day site.date⟩) }

example : Satisfies Krt19.rules krtExample 2400 :=
  (Krt19.satisfies_iff _ _).mpr ⟨rfl, rfl, ⟨.breastCancer, by simp, rfl⟩,
    rfl, rfl, rfl, rfl, rfl⟩

example : ¬ SatisfiableAt Krt19.rules { krtExample with priorPerformances := none } := by
  rintro ⟨p, hp⟩
  have h := ((Krt19.satisfies_iff _ _).mp hp).2
  simp [Krt19.Eligible, Krt19.priorInSeries, krtExample] at h

example : ¬ SatisfiableAt Krt19.rules { krtExample with nodalMetastasisEvident := some true } := by
  rintro ⟨p, hp⟩
  have h := ((Krt19.satisfies_iff _ _).mp hp).2
  simp [Krt19.Eligible] at h

private def wt1Example : Wt1.Context :=
  { site, method := some .realtimeRtPcr, disease := some .acuteMyeloidLeukemia
    purpose := some .followup
    priorClaims := some (emptyClaims ⟨site.patient, none, Period.month site.date.month⟩) }

example : Satisfies Wt1.rules wt1Example 2520 :=
  (Wt1.satisfies_iff _ _).mpr ⟨rfl, rfl, ⟨.acuteMyeloidLeukemia, by simp, rfl⟩,
    Or.inr rfl, rfl⟩

example : ¬ SatisfiableAt Wt1.rules { wt1Example with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((Wt1.satisfies_iff _ _).mp hp).2
  simp [Wt1.Eligible, Wt1.priorInMonth] at h

example : ¬ SatisfiableAt Wt1.rules { wt1Example with purpose := some .other } := by
  rintro ⟨p, hp⟩
  have h := ((Wt1.satisfies_iff _ _).mp hp).2
  simp [Wt1.Eligible] at h

namespace Ccr4

inductive Item where
  | ccr4
  deriving DecidableEq

def Item.number (_ : Item) : Option Nat := none

theorem no_number (i : Item) : i.number = none := rfl

/-- N002項5を同一目的で実施した場合の選択。N002の実施料自体は外部参照。 -/
inductive Combination where
  | noSamePurpose
  | flowOnly
  | tissueOnly
  | both
  deriving DecidableEq

structure Context where
  flowCytometry : Option Bool := none
  combination : Option Combination := none
  bothMedicallyNecessary : Option Bool := none

def Eligible (c : Context) : Prop :=
  c.flowCytometry = some true ∧
  (c.combination = some .noSamePurpose ∨ c.combination = some .flowOnly ∨
    (c.combination = some .both ∧ c.bothMedicallyNecessary = some true))

def points : Nat := 10000

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-10/heading", primary "D006-10", fun c p =>
    c.flowCytometry = some true ∧ p = 10000⟩

def combinationRule : Rule Context Nat :=
  ⟨"notice/D006-10/paragraph/unnumbered", notice 344 "D006-10", fun c _ =>
    c.combination = some .noSamePurpose ∨ c.combination = some .flowOnly ∨
    (c.combination = some .both ∧ c.bothMedicallyNecessary = some true)⟩

inductive Entry where
  | combinationReason | medicalNecessity

def entryRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-10/paragraph/unnumbered", notice 344 "D006-10 摘要", fun c r =>
    c.combination = some .both → r .combinationReason ∧ r .medicalNecessity⟩

def rules := [headingRule, combinationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, combinationRule, points, Eligible]
  grind

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

def judgmentTest : SpecimenJudgment.Test :=
  { major := 6, suffix := 10, ordinaryCategory := .hematological }

theorem judgment_category :
    SpecimenJudgment.categoryFor judgmentTest = some .hematological := rfl

example : Satisfies rules ⟨some true, some .flowOnly, none⟩ 10000 :=
  (satisfies_iff _ _).mpr ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩

example : ¬ SatisfiableAt rules ⟨some true, some .both, some false⟩ := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2
  simp [Eligible] at h

example : ¬ SatisfiableAt rules ⟨some true, none, none⟩ := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2
  simp [Eligible] at h

end Ccr4

namespace Fusion

inductive Item where
  | fip1l1Pdgfra
  deriving DecidableEq

def Item.number (_ : Item) : Option Nat := none

theorem no_number (i : Item) : i.number = none := rfl

inductive Diagnosis where
  | chronicEosinophilicLeukemia | hypereosinophilicSyndrome | other
  deriving DecidableEq

structure Context where
  site : Site
  fishUsed : Option Bool := none
  secondaryEosinophiliaExcluded : Option Bool := none
  diagnosis : Option Diagnosis := none
  treatmentPlanning : Option Bool := none
  symptomsOrFindingsChanged : Option Bool := none
  treatmentReselectionNecessary : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none

def priorCount (c : Context) : Option Nat :=
  c.priorClaims.bind fun h => count h ⟨c.site.patient, none, Period.through c.site.date⟩
    (· == .fip1l1Pdgfra)

def Eligible (c : Context) : Prop :=
  c.fishUsed = some true ∧ c.secondaryEosinophiliaExcluded = some true ∧
  (c.diagnosis = some .chronicEosinophilicLeukemia ∨
    c.diagnosis = some .hypereosinophilicSyndrome) ∧
  c.treatmentPlanning = some true ∧
  (priorCount c = some 0 ∨
    ∃ n, priorCount c = some n ∧ 0 < n ∧ c.symptomsOrFindingsChanged = some true ∧
      c.treatmentReselectionNecessary = some true)

def points : Nat := 3105

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-11/heading", primary "D006-11", fun _ p => p = 3105⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-11/paragraph/1", notice 345 "D006-11(1)", fun c _ => Eligible c⟩

inductive Reason where
  | initial | repeat

structure Documentation where
  chart : Reason → Prop
  abstract : Reason → Prop

def documentationRule : Rule Context Documentation :=
  ⟨"notice/D006-11/paragraph/2", notice 345 "D006-11(2)", fun c r =>
    (priorCount c = some 0 → r.chart .initial ∧ r.abstract .initial) ∧
    (∀ n, priorCount c = some n → 0 < n → r.chart .repeat ∧ r.abstract .repeat)⟩

def rules := [headingRule, indicationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, points]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

def judgmentTest : SpecimenJudgment.Test :=
  { major := 6, suffix := 11, ordinaryCategory := .hematological }

theorem judgment_category :
    SpecimenJudgment.categoryFor judgmentTest = some .geneticChromosomal := rfl

private def exampleContext : Context :=
  { site, fishUsed := some true, secondaryEosinophiliaExcluded := some true
    diagnosis := some .hypereosinophilicSyndrome, treatmentPlanning := some true
    priorClaims := some ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩ }

example : Satisfies rules exampleContext 3105 :=
  (satisfies_iff _ _).mpr ⟨rfl, rfl, rfl, Or.inr rfl, rfl, Or.inl rfl⟩

example : ¬ SatisfiableAt rules { exampleContext with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2
  simp [Eligible, priorCount] at h

example : ¬ SatisfiableAt rules { exampleContext with secondaryEosinophiliaExcluded := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2
  simp [Eligible] at h

end Fusion

namespace Egfr

inductive Item where
  | plasmaEgfr
  deriving DecidableEq

def Item.number (_ : Item) : Option Nat := none

theorem no_number (i : Item) : i.number = none := rfl

inductive Purpose where
  | initialSelection | reselection
  deriving DecidableEq

inductive Method where
  | realtimePcr | nextGenerationSequencing | other
  deriving DecidableEq

structure Context where
  performance : Performance Purpose
  plasma : Option Bool := none
  method : Option Method := none
  lungCancer : Option Bool := none
  recurrenceOrProgression : Option Bool := none
  suspectedSecondaryMutation : Option Bool := none
  tissueTestingMedicallyDifficult : Option Bool := none
  priorClaims : Option (ClaimHistory Purpose) := none
  priorPerformances : Option (Snapshot (Performance Purpose)) := none
  monthlySelection : Option D004Tumor.MonthlySelection := none
  tissueContexts : Nat → Option D004Tumor.Context := fun _ => none

def priorInMonth (c : Context) : Option Nat := do
  let h ← c.priorPerformances
  let site := c.performance.site
  return (← h.select Performance.site ⟨site.patient, none, Period.month site.date.month⟩
    (fun _ => true)).length

def priorForPurpose (c : Context) : Option Nat :=
  let site := c.performance.site
  c.priorClaims.bind fun h => count h ⟨site.patient, none, Period.through site.date⟩
    (· == c.performance.item)

def MethodAndSpecimen (c : Context) : Prop :=
  c.plasma = some true ∧ (c.method = some .realtimePcr ∨ c.method = some .nextGenerationSequencing)

def Indication (c : Context) : Prop :=
  c.lungCancer = some true ∧ c.tissueTestingMedicallyDifficult = some true ∧
  match c.performance.item with
  | .initialSelection => priorForPurpose c = some 0
  | .reselection => c.recurrenceOrProgression = some true ∧
    c.suspectedSecondaryMutation = some true ∧ ∃ n, priorForPurpose c = some n ∧ n < 2

/-- D004-2側の射影は処理が容易な肺癌の組織EGFR薬剤適応補助に限る。 -/
def tissueCounterpart (c : D004Tumor.Context) : Prop :=
  c.item = .drugAid ∧ c.cancer = .lung ∧ c.assay = some .egfr ∧ c.tumorCells = some true

def Principal (c : Context) : Prop :=
  ∃ s, c.monthlySelection = some s ∧
    s.Allows c.performance.site [.d004_2_1, .d006_24] ∧
    ∀ p ∈ s.survey.entries, p.item = .d004_2_1 →
      ∃ d, c.tissueContexts p.id = some d ∧ d.performance.id = p.id ∧
        d.performance.site = p.site ∧ tissueCounterpart d

structure Result where
  base : Nat
  total : Nat

def points : Nat := 2100

def headingRule : Rule Context Result :=
  ⟨"primary/D006-12/heading", primary "D006-12", fun _ r => r.base = 2100⟩

def monthlyReductionRule : Rule Context Result :=
  ⟨"primary/D006-12/note/unnumbered/1", primary "D006-12 注", fun c r =>
    ∃ n, priorInMonth c = some n ∧
      (n = 0 → r.total = r.base) ∧ (0 < n → 100 * r.total = 90 * r.base)⟩

def methodRule : Rule Context Result :=
  ⟨"notice/D006-12/paragraph/1", notice 345 "D006-12(1)", fun c _ => MethodAndSpecimen c⟩

def indicationRule : Rule Context Result :=
  ⟨"notice/D006-12/paragraph/2", notice 345 "D006-12(2)", fun c _ => Indication c⟩

def documentationRule : Rule Context (Bool × Bool) :=
  ⟨"notice/D006-12/paragraph/3", notice 345 "D006-12(3)",
    fun _ r => r.1 = true ∧ r.2 = true⟩

def combinationRule : Rule Context Result :=
  ⟨"notice/D006-12/paragraph/4", notice 345 "D006-12(4)", fun c _ => Principal c⟩

def rules := [headingRule, monthlyReductionRule, methodRule, indicationRule, combinationRule]

def Eligible (c : Context) : Prop :=
  (∃ n, priorInMonth c = some n) ∧ MethodAndSpecimen c ∧ Indication c ∧ Principal c

def scheduled (c : Context) : Option Result :=
  (priorInMonth c).map fun n => ⟨points, if n = 0 then points else 90 * points / 100⟩

theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ Eligible c ∧ scheduled c = some r := by
  obtain ⟨base, total⟩ := r
  cases h : priorInMonth c with
  | none =>
    simp [rules, satisfies_cons, satisfies_nil, headingRule, monthlyReductionRule, methodRule,
      indicationRule, combinationRule, Eligible, scheduled, h]
  | some n =>
    cases n <;>
      simp [rules, satisfies_cons, satisfies_nil, headingRule, monthlyReductionRule, methodRule,
        indicationRule, combinationRule, Eligible, scheduled, h, points] <;> grind

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  obtain ⟨n, hn⟩ := h.1
  let r : Result := ⟨points, if n = 0 then points else 90 * points / 100⟩
  have hr : scheduled c = some r := by simp [scheduled, hn, r]
  exact ⟨⟨r, (satisfies_iff _ _).mpr ⟨h, hr⟩⟩,
    fun a b ha hb => Option.some.inj (((satisfies_iff _ _).mp ha).2.symm.trans
      ((satisfies_iff _ _).mp hb).2)⟩

def judgmentTest : SpecimenJudgment.Test :=
  { major := 6, suffix := 12, ordinaryCategory := .hematological }

theorem judgment_category :
    SpecimenJudgment.categoryFor judgmentTest = some .geneticChromosomal := rfl

private def monthScope : Scope := ⟨site.patient, none, Period.month site.date.month⟩

private def exampleContext : Context :=
  { performance := ⟨2, site, .reselection, none, none, none, none⟩
    plasma := some true, method := some .realtimePcr, lungCancer := some true
    recurrenceOrProgression := some true, suspectedSecondaryMutation := some true
    tissueTestingMedicallyDifficult := some true
    priorClaims := some ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩
    priorPerformances := some ⟨monthScope, [⟨1, site, .initialSelection, none, none, none, none⟩]⟩
    monthlySelection := some ⟨⟨monthScope, []⟩, none, fun _ _ => none⟩ }

example : Satisfies rules exampleContext ⟨2100, 1890⟩ := by
  refine (satisfies_iff _ _).mpr ⟨⟨⟨1, rfl⟩, ⟨rfl, Or.inl rfl⟩, ?_, ?_⟩, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, 0, rfl, by decide⟩
  · exact ⟨_, rfl, ⟨[], rfl, Or.inl rfl, by simp⟩, by simp [exampleContext]⟩

example : ¬ SatisfiableAt rules { exampleContext with priorPerformances := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).1.1
  simp [priorInMonth] at h

example : ¬ SatisfiableAt rules { exampleContext with tissueTestingMedicallyDifficult := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).1.2.2.1
  simp [Indication] at h

end Egfr

namespace ResidualDisease

inductive Item where
  | identification | monitoring
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.identification, .monitoring]

def Item.number : Item → Nat
  | .identification => 1
  | .monitoring => 2

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem modeled_number (i : Item) : 1 ≤ i.number ∧ i.number ≤ 2 := by cases i <;> decide

def Item.points : Item → Nat
  | .identification => 3294
  | .monitoring => 2100

inductive Episode where
  | initial | relapse
  deriving DecidableEq

structure Context where
  performance : Performance Item
  episode : Option Episode := none
  episodePeriod : Option Period := none
  pcr : Option Bool := none
  acuteLymphoblasticLeukemia : Option Bool := none
  purpose : Option Purpose := none
  diagnosedOrRelapsed : Option Bool := none
  rearrangementIdentified : Option Bool := none
  primerPrepared : Option Bool := none
  priorIdentification : Option (Performance Item) := none
  facilityComplies : Option Bool := none
  facilityNotified : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none

def priorInEpisode (c : Context) : Option Nat := do
  let _ ← c.episode
  let p ← c.episodePeriod
  let h ← c.priorClaims
  let site := c.performance.site
  if p.Contains site.date then
    count h ⟨site.patient, none, p⟩ (· == c.performance.item)
  else none

def Facility (c : Context) : Prop :=
  c.facilityComplies = some true ∧ c.facilityNotified = some true

def MethodAndPurpose (c : Context) : Prop :=
  c.pcr = some true ∧ c.acuteLymphoblasticLeukemia = some true ∧
  (c.purpose = some .diagnosticSupport ∨ c.purpose = some .followup)

def Identification (c : Context) : Prop :=
  c.performance.item = .identification → c.diagnosedOrRelapsed = some true ∧
    c.rearrangementIdentified = some true ∧ c.primerPrepared = some true ∧
    priorInEpisode c = some 0

def Monitoring (c : Context) : Prop :=
  c.performance.item = .monitoring → c.purpose = some .followup ∧
    (∃ p, c.priorIdentification = some p ∧ p.item = .identification ∧
      p.site.patient = c.performance.site.patient ∧ p.id ≠ c.performance.id ∧
      p.site.date.key ≤ c.performance.site.date.key) ∧
    ∃ n, priorInEpisode c = some n ∧ n < 2

def identificationRule : Rule Context Nat :=
  ⟨"primary/D006-13/item/1", primary "D006-13 1",
    fun c p => c.performance.item = .identification → p = 3294⟩

def monitoringRule : Rule Context Nat :=
  ⟨"primary/D006-13/item/2", primary "D006-13 2",
    fun c p => c.performance.item = .monitoring → p = 2100⟩

def facilityRule : Rule Context Nat :=
  ⟨"primary/D006-13/note/unnumbered/1", primary "D006-13 注", fun c _ => Facility c⟩

def methodRule : Rule Context Nat :=
  ⟨"notice/D006-13/paragraph/1", notice 345 "D006-13(1)", fun c _ => MethodAndPurpose c⟩

def identificationNoticeRule : Rule Context Nat :=
  ⟨"notice/D006-13/paragraph/2", notice 345 "D006-13(2)", fun c _ => Identification c⟩

def monitoringNoticeRule : Rule Context Nat :=
  ⟨"notice/D006-13/paragraph/3", notice 345 "D006-13(3)", fun c _ => Monitoring c⟩

def Eligible (c : Context) : Prop :=
  Facility c ∧ MethodAndPurpose c ∧ Identification c ∧ Monitoring c

def rules := [identificationRule, monitoringRule, facilityRule, methodRule,
  identificationNoticeRule, monitoringNoticeRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = c.performance.item.points ∧ Eligible c := by
  cases h : c.performance.item <;>
    simp [rules, satisfies_cons, satisfies_nil, identificationRule, monitoringRule,
      facilityRule, methodRule, identificationNoticeRule, monitoringNoticeRule, Eligible,
      h, Item.points]

theorem determines : DeterminesOn Eligible rules := by
  intro c eligible
  exact ⟨⟨_, (satisfies_iff _ _).mpr ⟨rfl, eligible⟩⟩,
    fun a b ha hb => ((satisfies_iff _ _).mp ha).1.trans ((satisfies_iff _ _).mp hb).1.symm⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 13, number := i.number, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

private def exampleContext : Context :=
  { performance := ⟨1, site, .identification, none, none, none, none⟩
    episode := some .initial, episodePeriod := some (Period.day site.date)
    pcr := some true, acuteLymphoblasticLeukemia := some true, purpose := some .diagnosticSupport
    diagnosedOrRelapsed := some true, rearrangementIdentified := some true, primerPrepared := some true
    facilityComplies := some true, facilityNotified := some true
    priorClaims := some ⟨⟨⟨site.patient, none, Period.day site.date⟩, []⟩, by simp⟩ }

example : Satisfies rules exampleContext 3294 :=
  (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl, Or.inl rfl⟩,
    fun _ => ⟨rfl, rfl, rfl, rfl⟩, by simp [Monitoring, exampleContext]⟩

example : ¬ SatisfiableAt rules { exampleContext with episodePeriod := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.2.1 rfl
  simp [priorInEpisode, exampleContext] at h

example : ¬ SatisfiableAt rules { exampleContext with primerPrepared := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.2.1 rfl
  simp at h

end ResidualDisease

end Sanri.MedicalFee.D006GeneTests
