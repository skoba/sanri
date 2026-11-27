import Sanri.D006GeneTests

namespace Sanri.MedicalFee.D006Targeted

open Sanri.Logic Sanri.History

inductive Item where
  | cornealDystrophy | viscoelastic | plasmaRas | homologousRecombination | lungPanel | cyp2c9 | structuralVariation
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.cornealDystrophy, .viscoelastic, .plasmaRas, .homologousRecombination, .lungPanel, .cyp2c9, .structuralVariation]

def Item.suffix : Item → Nat
  | .cornealDystrophy => 20
  | .viscoelastic => 21
  | .plasmaRas => 22
  | .homologousRecombination => 23
  | .lungPanel => 24
  | .cyp2c9 => 25
  | .structuralVariation => 26

def Item.number (_ : Item) : Option Nat := none

theorem modeled_number (i : Item) : i.number = none ∧ 20 ≤ i.suffix ∧ i.suffix ≤ 26 := by
  cases i <;> decide

def Item.points : Item → Nat
  | .cornealDystrophy => 1200
  | .viscoelastic => 600
  | .plasmaRas => 7500
  | .homologousRecombination => 32200
  | .lungPanel => 12500
  | .cyp2c9 => 1976
  | .structuralVariation => 8000

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := i.suffix, ordinaryCategory := .hematological }

theorem judgment_viscoelastic :
    SpecimenJudgment.categoryFor (judgmentTest .viscoelastic) = some .hematological := rfl

theorem judgment_genetic (i : Item) (h : i ≠ .viscoelastic) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := by
  cases i <;> simp_all [judgmentTest, Item.suffix, SpecimenJudgment.categoryFor,
    SpecimenJudgment.geneRouting]

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF178頁 " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def priorCount {I : Type} (site : Site) (claims : Option (ClaimHistory I))
    (accepts : I → Bool) : Option Nat :=
  claims.bind fun h => count h ⟨site.patient, none, Period.through site.date⟩ accepts

private theorem determines_fixed {C : Type} (rules : List (Rule C Nat)) (scope : C → Prop)
    (points : Nat) (spec : ∀ c p, Satisfies rules c p ↔ p = points ∧ scope c) :
    DeterminesOn scope rules := by
  intro c eligible
  exact ⟨⟨points, (spec _ _).mpr ⟨rfl, eligible⟩⟩,
    fun a b ha hb => ((spec _ _).mp ha).1.trans ((spec _ _).mp hb).1.symm⟩

private def site : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def emptyClaims {I : Type} : ClaimHistory I :=
  ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩

namespace Corneal

structure Context where
  site : Site
  priorClaims : Option (ClaimHistory Unit) := none
  facilityComplies : Option Bool := none
  facilityNotified : Option Bool := none
  anteriorSegmentLesion : Option Bool := none
  clinicalDiagnosisOrSuspicion : Option Bool := none
  treatmentPlanDecision : Option Bool := none
  privacyGuidanceFollowed : Option Bool := none
  geneticTestingGuidelinesFollowed : Option Bool := none

def FacilityAndCount (c : Context) : Prop :=
  c.facilityComplies = some true ∧ c.facilityNotified = some true ∧
  priorCount c.site c.priorClaims (fun _ => true) = some 0

def Indication (c : Context) : Prop :=
  c.anteriorSegmentLesion = some true ∧ c.clinicalDiagnosisOrSuspicion = some true ∧
  c.treatmentPlanDecision = some true

def Guidance (c : Context) : Prop :=
  c.privacyGuidanceFollowed = some true ∧ c.geneticTestingGuidelinesFollowed = some true

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-20/heading", primary "D006-20", fun _ p => p = 1200⟩

def noteRule : Rule Context Nat :=
  ⟨"primary/D006-20/note/unnumbered/1", primary "D006-20 注", fun c _ => FacilityAndCount c⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-20/paragraph/1", notice "PDF349頁 D006-20(1)", fun c _ => Indication c⟩

def documentationRule : Rule Context Bool :=
  ⟨"notice/D006-20/paragraph/1", notice "PDF349頁 D006-20(1) 摘要",
    fun _ reasonWritten => reasonWritten = true⟩

def guidanceRule : Rule Context Nat :=
  ⟨"notice/D006-20/paragraph/2", notice "PDF349頁 D006-20(2)", fun c _ => Guidance c⟩

def rules := [headingRule, noteRule, indicationRule, guidanceRule]

def Eligible (c : Context) : Prop := FacilityAndCount c ∧ Indication c ∧ Guidance c

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.cornealDystrophy.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, noteRule, indicationRule,
    guidanceRule, Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def sample : Context :=
  { site, priorClaims := some emptyClaims, facilityComplies := some true, facilityNotified := some true
    anteriorSegmentLesion := some true, clinicalDiagnosisOrSuspicion := some true
    treatmentPlanDecision := some true, privacyGuidanceFollowed := some true
    geneticTestingGuidelinesFollowed := some true }

example : Satisfies rules sample 1200 :=
  (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩

example : ¬ SatisfiableAt rules { sample with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1.2.2
  cases h

example : ¬ SatisfiableAt rules { sample with anteriorSegmentLesion := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.1.1
  cases h

end Corneal

namespace Viscoelastic

inductive Phase where
  | preoperative | intraoperative | postoperative
  deriving DecidableEq

inductive Purpose where
  | assessNeedForBloodProducts | assessAfterBloodProducts
  deriving DecidableEq

/-- 手術IDは患者内で一意と確認されたもの。実施の一連IDは History の局所ID。 -/
structure SurgeryPhase where
  surgeryId : Nat
  phase : Phase
  deriving DecidableEq

structure Context where
  performance : Performance Unit
  surgeryPhase : Option SurgeryPhase := none
  priorClaims : Option (ClaimHistory SurgeryPhase) := none
  cardiovascularSurgery : Option Bool := none
  cardiopulmonaryBypass : Option Bool := none
  purpose : Option Purpose := none
  anesthesiaGuidanceFollowed : Option Bool := none
  appropriateTransfusionManagement : Option Bool := none

def Series (c : Context) : Prop :=
  ∃ group, c.performance.series = some group

def Indication (c : Context) : Prop :=
  c.cardiovascularSurgery = some true ∧ c.cardiopulmonaryBypass = some true ∧
  ∃ purpose, c.purpose = some purpose

def PhaseLimit (c : Context) : Prop :=
  ∃ phase, c.surgeryPhase = some phase ∧ priorCount c.performance.site c.priorClaims (· == phase) = some 0

def Guidance (c : Context) : Prop :=
  c.anesthesiaGuidanceFollowed = some true ∧ c.appropriateTransfusionManagement = some true

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-21/heading", primary "D006-21 一連", fun c p => p = 600 ∧ Series c⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-21/paragraph/1", notice "PDF349頁 D006-21(1)", fun c _ => Indication c⟩

def phaseRule : Rule Context Nat :=
  ⟨"notice/D006-21/paragraph/2", notice "PDF349頁 D006-21(2)", fun c _ => PhaseLimit c⟩

def guidanceRule : Rule Context Nat :=
  ⟨"notice/D006-21/paragraph/3", notice "PDF349頁 D006-21(3)", fun c _ => Guidance c⟩

def rules := [headingRule, indicationRule, phaseRule, guidanceRule]

def Eligible (c : Context) : Prop := Series c ∧ Indication c ∧ PhaseLimit c ∧ Guidance c

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.viscoelastic.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, phaseRule,
    guidanceRule, Item.points, Eligible, and_assoc]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def sample : Context :=
  { performance := { id := 1, site, item := (), series := some 2 }
    surgeryPhase := some ⟨1, .preoperative⟩, priorClaims := some emptyClaims
    cardiovascularSurgery := some true, cardiopulmonaryBypass := some true
    purpose := some .assessNeedForBloodProducts, anesthesiaGuidanceFollowed := some true
    appropriateTransfusionManagement := some true }

example : Satisfies rules sample 600 :=
  (satisfies_iff _ _).mpr ⟨rfl, ⟨2, rfl⟩, ⟨rfl, rfl, .assessNeedForBloodProducts, rfl⟩,
    ⟨⟨1, .preoperative⟩, rfl, rfl⟩, rfl, rfl⟩

example : ¬ SatisfiableAt rules { sample with surgeryPhase := none } := by
  rintro ⟨p, hp⟩
  obtain ⟨phase, h, _⟩ := ((satisfies_iff _ _).mp hp).2.2.2.1
  cases h

example : ¬ SatisfiableAt rules { sample with cardiopulmonaryBypass := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.1.2.1
  cases h

end Viscoelastic

namespace PlasmaRas

/-- D004-2の実施から通知(3)の大腸癌組織検査を選び出す。 -/
def tissueCounterpart (c : D004Tumor.Context) : Option Bool := do
  if c.cancer != .colorectal then return false
  match c.performance.item with
  | .drugAid | .otherSimple =>
    let assay ← c.assay
    if (c.performance.item == .drugAid && assay == .ras) ||
        (c.performance.item == .otherSimple && assay == .kras) then c.tumorCells
    else some false
  | _ => some false

structure Context where
  site : Site
  priorClaims : Option (ClaimHistory Unit) := none
  colorectalCancer : Option Bool := none
  plasma : Option Bool := none
  antineoplasticSelection : Option Bool := none
  highSensitivityDigitalPcr : Option Bool := none
  flowCytometry : Option Bool := none
  tissueTestingMedicallyDifficult : Option Bool := none
  treatmentReselectionNecessary : Option Bool := none
  /-- 通知(3)に該当する実施を `tissueCounterpart` で確認した履歴。 -/
  tissueSurvey : Option (Snapshot (Performance D004Tumor.Item)) := none
  principal : Nat → Nat → Option Bool := fun _ _ => none

def Indication (c : Context) : Prop :=
  c.colorectalCancer = some true ∧ c.plasma = some true ∧ c.antineoplasticSelection = some true ∧
  c.highSensitivityDigitalPcr = some true ∧ c.flowCytometry = some true ∧
  c.tissueTestingMedicallyDifficult = some true ∧
  ∃ n, priorCount c.site c.priorClaims (fun _ => true) = some n ∧
    (n = 0 ∨ c.treatmentReselectionNecessary = some true)

def Principal (c : Context) : Prop :=
  ∃ h, c.tissueSurvey = some h ∧
    ∃ tests, h.select Performance.site ⟨c.site.patient, none, Period.month c.site.date.month⟩
      (fun _ => true) = some tests ∧
      ∀ p ∈ tests, c.principal p.site.institution p.id = some true

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-22/heading", primary "D006-22", fun _ p => p = 7500⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-22/paragraph/1", notice "PDF349–350頁 D006-22(1)", fun c _ => Indication c⟩

structure Documentation where
  chart : Bool
  claim : Bool

def documentationRule : Rule Context Documentation :=
  ⟨"notice/D006-22/paragraph/2", notice "PDF350頁 D006-22(2)",
    fun _ d => d.chart = true ∧ d.claim = true⟩

def principalRule : Rule Context Nat :=
  ⟨"notice/D006-22/paragraph/3", notice "PDF350頁 D006-22(3)", fun c _ => Principal c⟩

def rules := [headingRule, indicationRule, principalRule]

def Eligible (c : Context) : Prop := Indication c ∧ Principal c

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.plasmaRas.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, principalRule,
    Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def sample : Context :=
  { site, priorClaims := some emptyClaims, colorectalCancer := some true, plasma := some true
    antineoplasticSelection := some true, highSensitivityDigitalPcr := some true
    flowCytometry := some true, tissueTestingMedicallyDifficult := some true
    tissueSurvey := some ⟨⟨site.patient, none, Period.month site.date.month⟩, []⟩ }

example : Satisfies rules sample 7500 :=
  (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, 0, rfl, Or.inl rfl⟩,
    ⟨_, rfl, [], rfl, by simp⟩⟩

example : ¬ SatisfiableAt rules { sample with tissueSurvey := none } := by
  rintro ⟨p, hp⟩
  obtain ⟨_, h, _⟩ := ((satisfies_iff _ _).mp hp).2.2
  cases h

example : ¬ SatisfiableAt rules { sample with flowCytometry := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1.2.2.2.2.1
  cases h

end PlasmaRas

namespace HomologousRecombination

structure Context where
  site : Site
  priorClaims : Option (ClaimHistory Unit) := none
  facilityComplies : Option Bool := none
  ovarianCancer : Option Bool := none
  tumorTissue : Option Bool := none
  antineoplasticSelection : Option Bool := none
  nextGenerationSequencing : Option Bool := none
  homologousRecombinationDeficiencyEvaluated : Option Bool := none

def Indication (c : Context) : Prop :=
  c.ovarianCancer = some true ∧ c.tumorTissue = some true ∧ c.antineoplasticSelection = some true ∧
  c.nextGenerationSequencing = some true ∧ c.homologousRecombinationDeficiencyEvaluated = some true ∧
  priorCount c.site c.priorClaims (fun _ => true) = some 0

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-23/heading", primary "D006-23", fun _ p => p = 32200⟩

def facilityRule : Rule Context Nat :=
  ⟨"primary/D006-23/note/unnumbered/1", primary "D006-23 注",
    fun c _ => c.facilityComplies = some true⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-23/paragraph/unnumbered", notice "PDF350頁 D006-23",
    fun c _ => Indication c⟩

def rules := [headingRule, facilityRule, indicationRule]

def Eligible (c : Context) : Prop := c.facilityComplies = some true ∧ Indication c

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.homologousRecombination.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, facilityRule, indicationRule,
    Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def sample : Context :=
  { site, priorClaims := some emptyClaims, facilityComplies := some true, ovarianCancer := some true
    tumorTissue := some true, antineoplasticSelection := some true, nextGenerationSequencing := some true
    homologousRecombinationDeficiencyEvaluated := some true }

example : Satisfies rules sample 32200 :=
  (satisfies_iff _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example : ¬ SatisfiableAt rules { sample with facilityComplies := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  cases h

example : ¬ SatisfiableAt rules { sample with ovarianCancer := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.1
  cases h

end HomologousRecombination

namespace LungPanel

inductive Assay where
  | egfr | ros1 | alk | braf | metEx14 | kras | ret
  deriving DecidableEq

inductive Counterpart where
  | tissue (item : D004Tumor.Item) (assay : D004Tumor.Assay) (method : D004Tumor.Method)
  | plasmaEgfr (purpose : D006GeneTests.Egfr.Purpose)
  | d006_27Ros1 | d006_27Alk | d006_27MetEx14 | n002Egfr | n002Alk | n005_2

def tissueCounterpart (c : D004Tumor.Context) : Option Counterpart := do
  let assay ← c.assay
  let method ← c.method
  if c.cancer == .lung && c.tumorCells == some true then
    return .tissue c.performance.item assay method
  else none

def egfrCounterpart (c : D006GeneTests.Egfr.Context) : Counterpart :=
  .plasmaEgfr c.performance.item

def Relevant : Counterpart → Prop
  | .tissue .drugAid assay method =>
    assay ∈ [.egfr, .ros1Fusion, .alkFusion, .krasG12c] ∨
    (assay ∈ [.braf, .metEx14] ∧ method ≠ .ngs)
  | .tissue .complex assay method =>
    assay = .retFusion ∨ (assay ∈ [.braf, .metEx14] ∧ method = .ngs)
  | .tissue _ _ _ => False
  | _ => True

structure Context where
  performance : Performance Unit
  lungCancer : Option Bool := none
  tumorTissue : Option Bool := none
  realtimePcr : Option Bool := none
  components : Option (List (Performance Assay)) := none
  priorClaims : Option (ClaimHistory Unit) := none
  /-- 確認された併施実施の一覧。参照先や時間幅の同定は外部確認。 -/
  performedTogether : Option (List (Performance Counterpart)) := none
  principal : Nat → Nat → Option Bool := fun _ _ => none

def Indication (c : Context) : Prop :=
  c.lungCancer = some true ∧ c.tumorTissue = some true ∧ c.realtimePcr = some true ∧
  priorCount c.performance.site c.priorClaims (fun _ => true) = some 0 ∧
  ∃ tests, c.components = some tests ∧
    ∀ a ∈ [Assay.egfr, .ros1, .alk, .braf, .metEx14, .kras, .ret],
      ∃ p ∈ tests, p.item = a ∧ c.performance.simultaneousWith
        { id := p.id, site := p.site, item := (), simultaneous := p.simultaneous } = some true

def Principal (c : Context) : Prop :=
  ∃ tests, c.performedTogether = some tests ∧
  ∀ p ∈ tests, Relevant p.item →
    p.site.patient = c.performance.site.patient ∧ c.principal p.site.institution p.id = some true

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-24/heading", primary "D006-24", fun _ p => p = 12500⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-24/paragraph/1", notice "PDF350頁 D006-24(1)", fun c _ => Indication c⟩

def principalRule : Rule Context Nat :=
  ⟨"notice/D006-24/paragraph/2", notice "PDF350頁 D006-24(2)", fun c _ => Principal c⟩

def rules := [headingRule, indicationRule, principalRule]

def Eligible (c : Context) : Prop := Indication c ∧ Principal c

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.lungPanel.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, principalRule,
    Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

def d004Counterpart (_ : Context) : D004Tumor.OtherTest := .d006_24

private def component (n : Nat) (a : Assay) : Performance Assay :=
  { id := n, site, item := a, simultaneous := some 1 }

private def sample : Context :=
  { performance := { id := 1, site, item := (), simultaneous := some 1 }
    lungCancer := some true, tumorTissue := some true, realtimePcr := some true
    priorClaims := some emptyClaims, performedTogether := some []
    components := some [component 2 .egfr, component 3 .ros1, component 4 .alk,
      component 5 .braf, component 6 .metEx14, component 7 .kras, component 8 .ret] }

example : Satisfies rules sample 12500 := by
  refine (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl, rfl, rfl, _, rfl, ?_⟩, [], rfl, by simp⟩
  intro a ha
  cases a
  · exact ⟨component 2 .egfr, by simp, rfl, rfl⟩
  · exact ⟨component 3 .ros1, by simp, rfl, rfl⟩
  · exact ⟨component 4 .alk, by simp, rfl, rfl⟩
  · exact ⟨component 5 .braf, by simp, rfl, rfl⟩
  · exact ⟨component 6 .metEx14, by simp, rfl, rfl⟩
  · exact ⟨component 7 .kras, by simp, rfl, rfl⟩
  · exact ⟨component 8 .ret, by simp, rfl, rfl⟩

example : ¬ SatisfiableAt rules { sample with performedTogether := none } := by
  rintro ⟨p, hp⟩
  obtain ⟨_, h, _⟩ := ((satisfies_iff _ _).mp hp).2.2
  cases h

example : ¬ SatisfiableAt rules { sample with realtimePcr := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1.2.2.1
  cases h

end LungPanel

namespace Cyp2c9

inductive Specimen where
  | wholeBlood | oralMucosa
  deriving DecidableEq

inductive Purpose where
  | siponimodEligibility | siponimodDose
  deriving DecidableEq

structure Context where
  site : Site
  priorClaims : Option (ClaimHistory Unit) := none
  specimen : Option Specimen := none
  purpose : Option Purpose := none
  secondaryProgressiveMultipleSclerosis : Option Bool := none
  realtimePcr : Option Bool := none
  extractedGenomicDna : Option Bool := none
  cyp2c9Polymorphism : Option Bool := none

def Indication (c : Context) : Prop :=
  c.secondaryProgressiveMultipleSclerosis = some true ∧ c.realtimePcr = some true ∧
  c.extractedGenomicDna = some true ∧ c.cyp2c9Polymorphism = some true ∧
  (∃ specimen, c.specimen = some specimen) ∧ (∃ purpose, c.purpose = some purpose) ∧
  priorCount c.site c.priorClaims (fun _ => true) = some 0

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-25/heading", primary "D006-25", fun _ p => p = 1976⟩

def indicationRule : Rule Context Nat :=
  ⟨"notice/D006-25/paragraph/unnumbered", notice "PDF350–351頁 D006-25",
    fun c _ => Indication c⟩

def documentationRule : Rule Context Bool :=
  ⟨"notice/D006-25/paragraph/unnumbered", notice "PDF351頁 D006-25 摘要",
    fun _ written => written = true⟩

def rules := [headingRule, indicationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.cyp2c9.points ∧ Indication c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, indicationRule, Item.points]

theorem determines : DeterminesOn Indication rules := determines_fixed rules Indication _ satisfies_iff

private def sample : Context :=
  { site, priorClaims := some emptyClaims, specimen := some .oralMucosa, purpose := some .siponimodDose
    secondaryProgressiveMultipleSclerosis := some true, realtimePcr := some true
    extractedGenomicDna := some true, cyp2c9Polymorphism := some true }

example : Satisfies rules sample 1976 :=
  (satisfies_iff _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl, ⟨.oralMucosa, rfl⟩, ⟨.siponimodDose, rfl⟩, rfl⟩

example : ¬ SatisfiableAt rules { sample with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.2.2.2.2.2
  cases h

example : ¬ SatisfiableAt rules { sample with secondaryProgressiveMultipleSclerosis := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1
  cases h

end Cyp2c9

namespace StructuralVariation

inductive Disease where
  | del12q14 | del15q13_3 | del15q24 | overgrowth15q26 | dup16p11_2
  | del16p11_2_p12_2 | dup16p11_2_p12_2 | del16p13_11 | dup16p13_11 | del17q21_31
  | del1p36 | del1q21_1 | dup1q21_1 | thrombocytopeniaAbsentRadius1q21_1
  | del22q11_2 | dup22q11 | distalDel22q11_2 | del22q13
  | del2p15_p16_1 | del2p21 | del2q33_1 | monosomy2q37 | del3q29 | dup3q29
  | dup7q11_23 | del8p23_1 | dup8p23_1 | del8q21_11 | del9q34
  | angelman | atr16 | tetrasomy22q | charcotMarieTooth | del5p | hnpp | leriWeill
  | millerDieker | nf1Deletion | pelizaeusMerzbacher | potockiLupski | potockiShaffer
  | praderWilli | renalCystsAndDiabetes | del16p12_1 | rubinsteinTaybi | smithMagenis
  | sotos | splitHandFoot1 | steroidSulfataseDeficiency | wagr | williams | wolfHirschhorn
  | intellectualDisabilityXp11_22 | dupXp11_22_p11_23 | mecp2Duplication
  | beckwithWiedemann | silverRussell | paternalDisomy14 | maternalDisomy14OrRelated
  deriving DecidableEq

structure Context where
  site : Site
  priorClaims : Option (ClaimHistory Unit) := none
  facilityComplies : Option Bool := none
  approvedDiagnosticReagent : Option Bool := none
  arrayCgh : Option Bool := none
  chromosomalGenomicDna : Option Bool := none
  measuredCopyNumberChange : Option Bool := none
  measuredLossOfHeterozygosity : Option Bool := none
  suspectedDisease : Option Disease := none
  societyGuidelinesFollowed : Option Bool := none

def Indication (c : Context) : Prop :=
  c.approvedDiagnosticReagent = some true ∧ c.arrayCgh = some true ∧
  c.chromosomalGenomicDna = some true ∧ c.measuredCopyNumberChange = some true ∧
  c.measuredLossOfHeterozygosity = some true ∧
  priorCount c.site c.priorClaims (fun _ => true) = some 0

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-26/heading", primary "D006-26", fun _ p => p = 8000⟩

def facilityRule : Rule Context Nat :=
  ⟨"primary/D006-26/note/unnumbered/1", primary "D006-26 注",
    fun c _ => c.facilityComplies = some true⟩

def measurementRule : Rule Context Nat :=
  ⟨"notice/D006-26/paragraph/1", notice "PDF351頁 D006-26(1)", fun c _ => Indication c⟩

def diseaseRule : Rule Context Nat :=
  ⟨"notice/D006-26/paragraph/2", notice "PDF351頁 D006-26(2)",
    fun c _ => ∃ disease, c.suspectedDisease = some disease⟩

def guidanceRule : Rule Context Nat :=
  ⟨"notice/D006-26/paragraph/3", notice "PDF351頁 D006-26(3)",
    fun c _ => c.societyGuidelinesFollowed = some true⟩

def documentationRule : Rule Context Bool :=
  ⟨"notice/D006-26/paragraph/3", notice "PDF351頁 D006-26(3) 摘要",
    fun _ reasonWritten => reasonWritten = true⟩

def rules := [headingRule, facilityRule, measurementRule, diseaseRule, guidanceRule]

def Eligible (c : Context) : Prop :=
  c.facilityComplies = some true ∧ Indication c ∧
  (∃ disease, c.suspectedDisease = some disease) ∧ c.societyGuidelinesFollowed = some true

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = Item.structuralVariation.points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, facilityRule, measurementRule,
    diseaseRule, guidanceRule, Item.points, Eligible]

theorem determines : DeterminesOn Eligible rules := determines_fixed rules Eligible _ satisfies_iff

private def sample : Context :=
  { site, priorClaims := some emptyClaims, facilityComplies := some true
    approvedDiagnosticReagent := some true, arrayCgh := some true, chromosomalGenomicDna := some true
    measuredCopyNumberChange := some true, measuredLossOfHeterozygosity := some true
    suspectedDisease := some .wagr, societyGuidelinesFollowed := some true }

example : Satisfies rules sample 8000 :=
  (satisfies_iff _ _).mpr ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨.wagr, rfl⟩, rfl⟩

example : ¬ SatisfiableAt rules { sample with suspectedDisease := none } := by
  rintro ⟨p, hp⟩
  obtain ⟨_, h⟩ := ((satisfies_iff _ _).mp hp).2.2.2.1
  cases h

example : ¬ SatisfiableAt rules { sample with arrayCgh := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.1.2.1
  cases h

end StructuralVariation
end Sanri.MedicalFee.D006Targeted
