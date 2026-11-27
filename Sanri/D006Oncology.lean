import Sanri.D004Tumor

namespace Sanri.MedicalFee.D006Oncology

open Sanri.Logic Sanri.History

private def primary (code : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF178頁 " ++ code, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private theorem determines_fixed {C : Type} (rules : List (Rule C Nat)) (scope : C → Prop)
    (points : Nat) (spec : ∀ c p, Satisfies rules c p ↔ p = points ∧ scope c) :
    DeterminesOn scope rules := by
  intro c eligible
  exact ⟨⟨points, (spec _ _).mpr ⟨rfl, eligible⟩⟩,
    fun a b ha hb => ((spec _ _).mp ha).1.trans ((spec _ _).mp hb).1.symm⟩

inductive Item where
  | flt3 | bladder | jak2
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.flt3, .bladder, .jak2]

def Item.suffix : Item → Nat
  | .flt3 => 14
  | .bladder => 15
  | .jak2 => 16

def Item.number (_ : Item) : Option Nat := none

theorem modeled_number (i : Item) : i.number = none ∧ 14 ≤ i.suffix ∧ i.suffix ≤ 16 := by
  cases i <;> decide

def Item.points : Item → Nat
  | .flt3 => 4200
  | .bladder => 1597
  | .jak2 => 2504

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := i.suffix, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := by
  cases i <;> rfl

inductive Specimen where
  | boneMarrow | peripheralBlood | other
  deriving DecidableEq

private def BloodOrMarrow (s : Option Specimen) : Prop :=
  s = some .boneMarrow ∨ s = some .peripheralBlood

private def priorThrough (site : Site) (item : Item) (history : Option (ClaimHistory Item)) :
    Option Nat :=
  history.bind fun h => count h ⟨site.patient, none, Period.through site.date⟩ (· == item)

private def site : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def monthScope : Scope := ⟨site.patient, none, Period.month site.date.month⟩
private def emptyMonthly : D004Tumor.MonthlySelection :=
  ⟨⟨monthScope, []⟩, none, fun _ _ => none⟩

private def emptyClaims (p : Period) : ClaimHistory Item := ⟨⟨⟨site.patient, none, p⟩, []⟩, by simp⟩

namespace Flt3

structure Context where
  site : Site
  aml : Option Bool := none
  acutePromyelocyticLeukemia : Option Bool := none
  specimen : Option Specimen := none
  pcr : Option Bool := none
  capillaryElectrophoresis : Option Bool := none
  antineoplasticSelection : Option Bool := none
  itdEvaluated : Option Bool := none
  tkdEvaluated : Option Bool := none
  treatmentReselectionNecessary : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none
  monthlySelection : Option D004Tumor.MonthlySelection := none

def Indication (c : Context) : Prop :=
  c.aml = some true ∧ c.acutePromyelocyticLeukemia = some false ∧ BloodOrMarrow c.specimen ∧
  c.pcr = some true ∧ c.capillaryElectrophoresis = some true ∧
  c.antineoplasticSelection = some true ∧ c.itdEvaluated = some true ∧ c.tkdEvaluated = some true ∧
  (priorThrough c.site .flt3 c.priorClaims = some 0 ∨
    (priorThrough c.site .flt3 c.priorClaims = some 1 ∧ c.treatmentReselectionNecessary = some true))

def Principal (c : Context) : Prop :=
  ∃ s, c.monthlySelection = some s ∧ s.Allows c.site [.d004_2_1, .d006_2, .d006_6, .d006_16]

def Eligible (c : Context) : Prop := Indication c ∧ Principal c

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-14/heading", primary "D006-14", fun _ p => p = 4200⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-14/paragraph/1", notice "PDF345–346頁 D006-14(1)", fun c _ => Indication c⟩

def documentationRule : Rule Context Bool :=
  ⟨"notice/D006-14/paragraph/1", notice "PDF346頁 D006-14(1) 摘要",
    fun c written => priorThrough c.site .flt3 c.priorClaims = some 1 → written = true⟩

def combinationRule : Rule Context Nat :=
  ⟨"notice/D006-14/paragraph/2", notice "PDF346頁 D006-14(2)", fun c _ => Principal c⟩

def rules := [headingRule, indicationRule, combinationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.flt3.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, combinationRule,
    Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def exampleContext : Context :=
  { site, aml := some true, acutePromyelocyticLeukemia := some false, specimen := some .boneMarrow
    pcr := some true, capillaryElectrophoresis := some true, antineoplasticSelection := some true
    itdEvaluated := some true, tkdEvaluated := some true
    priorClaims := some (emptyClaims (Period.through site.date)), monthlySelection := some emptyMonthly }

example : Satisfies rules exampleContext 4200 := by
  refine (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl, Or.inl rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩, ?_⟩
  exact ⟨_, rfl, [], rfl, Or.inl rfl, by simp⟩

example : ¬ SatisfiableAt rules { exampleContext with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  simp [Indication, priorThrough] at h

example : ¬ SatisfiableAt rules { exampleContext with tkdEvaluated := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  simp [Indication] at h

end Flt3

namespace Bladder

/-- K803項6の実施確認と、術後２年の境界を照合した記録。 -/
structure Surgery where
  site : Site
  postoperativeEnd : Date
  precedesExamination : Bool

inductive Related where
  | bladderGeneTest | cystoscopy | cytology
  deriving DecidableEq

structure Context where
  performance : Performance Related
  bladderCancer : Option Bool := none
  cis : Option Bool := none
  surgery : Option Surgery := none
  fishUsed : Option Bool := none
  recurrenceDiagnosisSupport : Option Bool := none
  cystoscopy : Option (Performance Related) := none
  noRecurrenceFindings : Option Bool := none
  /-- N004項2の同時実施一覧。空なら同時実施なしを確認済み。 -/
  simultaneousCytology : Option (List (Performance Related)) := none
  principalOverCytology : Nat → Option Bool := fun _ => none
  priorClaims : Option (ClaimHistory Item) := none

def Context.prior (c : Context) : Option (List (Sanri.History.Claim Item)) := do
  let _ ← c.surgery
  let h ← c.priorClaims
  let t := c.performance.site
  h.toSnapshot.select Claim.site ⟨t.patient, none, Period.through t.date⟩ (·.item == .bladder)

def Indication (c : Context) : Prop :=
  c.performance.item = .bladderGeneTest ∧ c.bladderCancer = some true ∧ c.cis = some true ∧ c.fishUsed = some true ∧
  c.recurrenceDiagnosisSupport = some true ∧
  (∃ s, c.surgery = some s ∧ s.site.patient = c.performance.site.patient ∧
    s.precedesExamination = true ∧ s.site.date.key ≤ c.performance.site.date.key ∧
    c.performance.site.date.key ≤ s.postoperativeEnd.key) ∧
  (∃ p, c.cystoscopy = some p ∧ p.item = .cystoscopy ∧
    c.performance.simultaneousWith p = some true ∧ c.noRecurrenceFindings = some true) ∧
  ∃ claims, c.prior = some claims ∧ claims.length < 2

def Principal (c : Context) : Prop :=
  ∃ tests, c.simultaneousCytology = some tests ∧
    ∀ p ∈ tests, p.item = .cytology ∧ c.performance.simultaneousWith p = some true ∧
      c.principalOverCytology p.id = some true

def Eligible (c : Context) : Prop := Indication c ∧ Principal c

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-15/heading", primary "D006-15", fun _ p => p = 1597⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-15/paragraph/1", notice "PDF346頁 D006-15(1)", fun c _ => Indication c⟩

inductive Entry where
  | pathology | surgeryDate (d : Date) | priorClaimDate (d : Date)

def documentationRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-15/paragraph/2", notice "PDF346頁 D006-15(2)", fun c written =>
    written .pathology ∧
    (∀ s, c.surgery = some s → written (.surgeryDate s.site.date)) ∧
    (∀ claims, c.prior = some claims →
      ∀ claim ∈ claims, written (.priorClaimDate claim.site.date))⟩

def combinationRule : Rule Context Nat :=
  ⟨"notice/D006-15/paragraph/3", notice "PDF346頁 D006-15(3)", fun c _ => Principal c⟩

def rules := [headingRule, indicationRule, combinationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.bladder.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, combinationRule,
    Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def exampleContext : Context :=
  { performance := ⟨1, site, .bladderGeneTest, none, none, none, some 1⟩
    bladderCancer := some true, cis := some true, fishUsed := some true
    recurrenceDiagnosisSupport := some true
    surgery := some ⟨⟨site.patient, 1, ⟨⟨2025, 9⟩, ⟨21, by decide⟩⟩⟩,
      ⟨⟨2027, 9⟩, ⟨21, by decide⟩⟩, true⟩
    cystoscopy := some ⟨2, site, .cystoscopy, none, none, none, some 1⟩
    noRecurrenceFindings := some true, simultaneousCytology := some []
    priorClaims := some (emptyClaims (Period.through site.date)) }

example : Satisfies rules exampleContext 1597 := by
  refine (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, [], rfl, by decide⟩, ?_⟩
  · exact ⟨_, rfl, rfl, rfl, by decide, by decide⟩
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · exact ⟨[], rfl, by simp⟩

example : ¬ SatisfiableAt rules { exampleContext with simultaneousCytology := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2
  simp [Principal] at h

example : ¬ SatisfiableAt rules { exampleContext with noRecurrenceFindings := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  simp [Indication] at h

end Bladder

namespace Jak2

inductive Disease where
  | polycythemiaVera | essentialThrombocythemia | primaryMyelofibrosis | other
  deriving DecidableEq

structure Context where
  site : Site
  specimen : Option Specimen := none
  alleleSpecificQuantitativePcr : Option Bool := none
  disease : Option Disease := none
  diagnosticSupport : Option Bool := none
  v617fFractionMeasured : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none
  monthlySelection : Option D004Tumor.MonthlySelection := none

def Indication (c : Context) : Prop :=
  BloodOrMarrow c.specimen ∧ c.alleleSpecificQuantitativePcr = some true ∧
  (∃ d ∈ [Disease.polycythemiaVera, .essentialThrombocythemia, .primaryMyelofibrosis],
    c.disease = some d) ∧ c.diagnosticSupport = some true ∧ c.v617fFractionMeasured = some true ∧
  priorThrough c.site .jak2 c.priorClaims = some 0

def Principal (c : Context) : Prop :=
  ∃ s, c.monthlySelection = some s ∧ s.Allows c.site [.d004_2_1, .d006_2, .d006_6, .d006_14]

def Eligible (c : Context) : Prop := Indication c ∧ Principal c

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-16/heading", primary "D006-16", fun _ p => p = 2504⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-16/paragraph/1", notice "PDF346頁 D006-16(1)", fun c _ => Indication c⟩

def combinationRule : Rule Context Nat :=
  ⟨"notice/D006-16/paragraph/2", notice "PDF346頁 D006-16(2)", fun c _ => Principal c⟩

def rules := [headingRule, indicationRule, combinationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.jak2.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, combinationRule,
    Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def exampleContext : Context :=
  { site, specimen := some .peripheralBlood, alleleSpecificQuantitativePcr := some true
    disease := some .primaryMyelofibrosis, diagnosticSupport := some true
    v617fFractionMeasured := some true, priorClaims := some (emptyClaims (Period.through site.date))
    monthlySelection := some emptyMonthly }

example : Satisfies rules exampleContext 2504 := by
  refine (satisfies_iff _ _).mpr ⟨rfl, ⟨Or.inr rfl, rfl, ⟨.primaryMyelofibrosis, by simp, rfl⟩, rfl, rfl, rfl⟩, ?_⟩
  exact ⟨_, rfl, [], rfl, Or.inl rfl, by simp⟩

example : ¬ SatisfiableAt rules { exampleContext with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  simp [Indication, priorThrough] at h

example : ¬ SatisfiableAt rules { exampleContext with disease := some .other } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  simp [Indication, exampleContext] at h

end Jak2
namespace Pharmacogenetics

inductive Item where
  | nudt15 | apoe
  deriving DecidableEq, Repr

/-- APOEは通知による準用。本文に番号付きの項はない。 -/
def Item.number (_ : Item) : Option Nat := none

theorem no_number (i : Item) : i.number = none := rfl

inductive Disease where
  | refractoryInflammatoryBowelDisease | acuteLymphoblasticLeukemia
  | resistantSystemicVasculitis | resistantLupus | resistantPolymyositis
  | resistantDermatomyositis | resistantScleroderma | resistantMixedConnectiveTissueDisease
  | otherRefractoryRheumaticDisease | autoimmuneHepatitis | other
  deriving DecidableEq

structure Context where
  site : Site
  item : Item
  realtimePcr : Option Bool := none
  disease : Option Disease := none
  thiopurineCandidate : Option Bool := none
  decisionOnThiopurineUseOrDose : Option Bool := none
  beforeThiopurineStart : Option Bool := none
  thiopurineWindow : Option Period := none
  drugIndicationIncludesEarlyAlzheimerProgression : Option Bool := none
  guidelinePatient : Option Bool := none
  guidelineFacility : Option Bool := none
  decisionOnAlzheimerTreatment : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none

def prior (c : Context) (period : Period) (item : Item) : Option Nat :=
  c.priorClaims.bind fun h => count h ⟨c.site.patient, none, period⟩ (· == item)

def Nudt15Indication (c : Context) : Prop :=
  c.realtimePcr = some true ∧
  (∃ disease ∈ [Disease.refractoryInflammatoryBowelDisease, .acuteLymphoblasticLeukemia,
    .resistantSystemicVasculitis, .resistantLupus, .resistantPolymyositis,
    .resistantDermatomyositis, .resistantScleroderma, .resistantMixedConnectiveTissueDisease,
    .otherRefractoryRheumaticDisease, .autoimmuneHepatitis], c.disease = some disease) ∧
  c.thiopurineCandidate = some true ∧ c.decisionOnThiopurineUseOrDose = some true ∧
  c.beforeThiopurineStart = some true ∧
  ∃ p, c.thiopurineWindow = some p ∧ p.Contains c.site.date ∧ prior c p .nudt15 = some 0

def ApoeIndication (c : Context) : Prop :=
  c.realtimePcr = some true ∧ c.drugIndicationIncludesEarlyAlzheimerProgression = some true ∧
  c.guidelinePatient = some true ∧ c.guidelineFacility = some true ∧
  c.decisionOnAlzheimerTreatment = some true ∧
  prior c (Period.through c.site.date) .apoe = some 0

def points : Nat := 2274

private def amendment (loc : String) : SourceRef :=
  ⟨.notification, "保医発0630第7号・別添1", "2026-07-01適用",
    "PDF2頁 D006-17 " ++ loc, .checkedAgainstSource,
    some "https://kouseikyoku.mhlw.go.jp/kantoshinetsu/080701_015.pdf"⟩

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-17/heading", primary "D006-17", fun c p => c.item = .nudt15 → p = 2274⟩

def nudt15Rule : Rule Context Nat :=
  ⟨"notice/D006-17/paragraph/1", amendment "(1)",
    fun c _ => c.item = .nudt15 → Nudt15Indication c⟩

def apoeRule : Rule Context Nat :=
  ⟨"notice/D006-17/paragraph/2", amendment "(2)",
    fun c p => c.item = .apoe → ApoeIndication c ∧ headingRule.holds { c with item := .nudt15 } p⟩

def rules := [headingRule, nudt15Rule, apoeRule]

def Eligible (c : Context) : Prop :=
  match c.item with
  | .nudt15 => Nudt15Indication c
  | .apoe => ApoeIndication c

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  cases h : c.item <;>
    simp [rules, satisfies_cons, satisfies_nil, headingRule, nudt15Rule, apoeRule,
      Eligible, points, h, and_comm]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 17, variant := if i = .apoe then 1 else 0, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

private def apoeExample : Context :=
  { site, item := .apoe, realtimePcr := some true
    drugIndicationIncludesEarlyAlzheimerProgression := some true, guidelinePatient := some true
    guidelineFacility := some true, decisionOnAlzheimerTreatment := some true
    priorClaims := some ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩ }

example : Satisfies rules apoeExample 2274 :=
  (satisfies_iff _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example : ¬ SatisfiableAt rules { apoeExample with guidelineFacility := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2
  simp [Eligible, ApoeIndication, apoeExample] at h

example : ¬ SatisfiableAt rules { apoeExample with decisionOnAlzheimerTreatment := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2
  simp [Eligible, ApoeIndication, apoeExample] at h

private def nudt15Example : Context :=
  { apoeExample with
    item := .nudt15, disease := some .autoimmuneHepatitis
    thiopurineCandidate := some true, decisionOnThiopurineUseOrDose := some true
    beforeThiopurineStart := some true, thiopurineWindow := some (Period.through site.date) }

example : Satisfies rules nudt15Example 2274 :=
  (satisfies_iff _ _).mpr ⟨rfl, rfl, ⟨.autoimmuneHepatitis, by simp, rfl⟩, rfl, rfl, rfl,
    _, rfl, Period.contains_last _, rfl⟩

end Pharmacogenetics
namespace Brca

inductive Item where
  | tumorCells | blood
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.tumorCells, .blood]

def Item.number : Item → Nat
  | .tumorCells => 1
  | .blood => 2

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem modeled_number (i : Item) : 1 ≤ i.number ∧ i.number ≤ 2 := by cases i <;> decide

def points : Nat := 20200

inductive Disease where
  | newlyDiagnosedAdvancedOvarian | metastaticCastrationResistantProstate
  | metastaticBreast | recurrentBreast | eligibleHer2NegativePostoperativeBreast
  | unresectablePancreatic | otherBreast | otherOvarian | other
  deriving DecidableEq

inductive Relation where
  | parent | child | sibling | other
  deriving DecidableEq

inductive Purpose where
  | antineoplasticSelection | hbocDiagnosis | other
  deriving DecidableEq

inductive Method where
  | nextGenerationSequencing | pcr | otherConfirmedUnderNotice | other
  deriving DecidableEq

structure Context where
  item : Item
  specimen : Option Item := none
  disease : Option Disease := none
  suspectedHboc : Option Bool := none
  relation : Option Relation := none
  relativeDiagnosedByBloodBrca : Option Bool := none
  purpose : Option Purpose := none
  method : Option Method := none
  brca1Evaluated : Option Bool := none
  brca2Evaluated : Option Bool := none
  facilityComplies : Option Bool := none
  facilityNotified : Option Bool := none
  handbookReferenced : Option Bool := none

def tumorDiseases : List Disease :=
  [.newlyDiagnosedAdvancedOvarian, .metastaticCastrationResistantProstate,
   .metastaticBreast, .recurrentBreast, .eligibleHer2NegativePostoperativeBreast]

def HbocSubject (c : Context) : Prop :=
  c.suspectedHboc = some true ∧
  ((∃ d ∈ [Disease.newlyDiagnosedAdvancedOvarian, .otherOvarian, .metastaticBreast,
      .recurrentBreast, .eligibleHer2NegativePostoperativeBreast, .otherBreast], c.disease = some d) ∨
    (c.relativeDiagnosedByBloodBrca = some true ∧
      ∃ r ∈ [Relation.parent, .child, .sibling], c.relation = some r))

def Facility (c : Context) : Prop := c.facilityComplies = some true ∧ c.facilityNotified = some true

def Tumor (c : Context) : Prop :=
  c.item = .tumorCells → c.specimen = some .tumorCells ∧ c.method = some .nextGenerationSequencing ∧
    (∃ d ∈ tumorDiseases, c.disease = some d) ∧ c.purpose = some .antineoplasticSelection ∧
    c.brca1Evaluated = some true ∧ c.brca2Evaluated = some true

def Blood (c : Context) : Prop :=
  c.item = .blood → c.specimen = some .blood ∧
    (c.method = some .pcr ∨ c.method = some .otherConfirmedUnderNotice) ∧
    ((∃ d ∈ .unresectablePancreatic :: tumorDiseases, c.disease = some d) ∨ HbocSubject c) ∧
    (c.purpose = some .antineoplasticSelection ∨ c.purpose = some .hbocDiagnosis) ∧
    c.brca1Evaluated = some true ∧ c.brca2Evaluated = some true

def Handbook (c : Context) : Prop :=
  c.item = .blood → c.purpose = some .hbocDiagnosis → c.handbookReferenced = some true

def tumorRule : Rule Context Nat :=
  ⟨"primary/D006-18/item/1", primary "D006-18 1",
    fun c p => c.item = .tumorCells → p = 20200⟩

def bloodRule : Rule Context Nat :=
  ⟨"primary/D006-18/item/2", primary "D006-18 2", fun c p => c.item = .blood → p = 20200⟩

def facilityRule : Rule Context Nat :=
  ⟨"primary/D006-18/note/unnumbered/1", primary "D006-18 注", fun c _ => Facility c⟩

def tumorNoticeRule : Rule Context Nat :=
  ⟨"notice/D006-18/paragraph/1", notice "PDF346頁 D006-18(1)", fun c _ => Tumor c⟩

def bloodNoticeRule : Rule Context Nat :=
  ⟨"notice/D006-18/paragraph/2", notice "PDF346–347頁 D006-18(2)", fun c _ => Blood c⟩

def handbookRule : Rule Context Nat :=
  ⟨"notice/D006-18/paragraph/3", notice "PDF347頁 D006-18(3)", fun c _ => Handbook c⟩

def documentationRule : Rule Context Bool :=
  ⟨"notice/D006-18/paragraph/3", notice "PDF347頁 D006-18(3) 摘要", fun c documented =>
    c.item = .blood → c.purpose = some .hbocDiagnosis → documented = true⟩

def Eligible (c : Context) : Prop := Facility c ∧ Tumor c ∧ Blood c ∧ Handbook c
def rules := [tumorRule, bloodRule, facilityRule, tumorNoticeRule, bloodNoticeRule, handbookRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  cases h : c.item <;>
    simp [rules, satisfies_cons, satisfies_nil, tumorRule, bloodRule, facilityRule,
      tumorNoticeRule, bloodNoticeRule, handbookRule, Eligible, points, h]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 18, number := i.number, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

/-- D004-2(11)の照会に渡す側。比較対象の測定と主たる検査の選択はD004Tumor側で評価する。 -/
def d004Counterpart (c : Context) : Option D004Tumor.OtherTest :=
  match c.item with
  | .tumorCells => some .d006_18_1
  | .blood => none

private def exampleContext : Context :=
  { item := .tumorCells, specimen := some .tumorCells, method := some .nextGenerationSequencing
    disease := some .newlyDiagnosedAdvancedOvarian, purpose := some .antineoplasticSelection
    brca1Evaluated := some true, brca2Evaluated := some true
    facilityComplies := some true, facilityNotified := some true }

example : Satisfies rules exampleContext 20200 :=
  (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl, ⟨.newlyDiagnosedAdvancedOvarian, by simp [tumorDiseases], rfl⟩,
      rfl, rfl, rfl⟩,
    by simp [Blood, exampleContext], by simp [Handbook, exampleContext]⟩

example : ¬ SatisfiableAt rules { exampleContext with facilityNotified := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  simp [Facility] at h

example : ¬ SatisfiableAt rules { exampleContext with brca2Evaluated := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.1 rfl
  simp at h

end Brca
end Sanri.MedicalFee.D006Oncology
