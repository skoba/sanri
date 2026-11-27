import Sanri.History
import Sanri.SpecimenJudgment

/-! D006-28〜D006-31の2026-10-22外来実施料。 -/
namespace Sanri.MedicalFee.D006Late

open Sanri.Logic Sanri.History

inductive Item where
  | yDeletion | breastRecurrence | retinalDystrophy | idh1
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.yDeletion, .breastRecurrence, .retinalDystrophy, .idh1]

def Item.suffix : Item → Nat
  | .yDeletion => 28
  | .breastRecurrence => 29
  | .retinalDystrophy => 30
  | .idh1 => 31

def Item.number (_ : Item) : Option Nat := none

theorem no_number (i : Item) : i.number = none := rfl

theorem suffix_range (n : Nat) : (∃ i : Item, i.suffix = n) ↔ 28 ≤ n ∧ n ≤ 31 := by
  constructor
  · rintro ⟨i, rfl⟩
    cases i <;> decide
  · intro h
    have values : n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 := by omega
    rcases values with rfl | rfl | rfl | rfl
    · exact ⟨.yDeletion, rfl⟩
    · exact ⟨.breastRecurrence, rfl⟩
    · exact ⟨.retinalDystrophy, rfl⟩
    · exact ⟨.idh1, rfl⟩

def Item.points : Item → Nat
  | .yDeletion => 3770
  | .breastRecurrence => 43500
  | .retinalDystrophy => 23500
  | .idh1 => 2500

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := i.suffix, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := by
  cases i <;> rfl

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF179頁 " ++ loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

inductive Method where
  | pcrRsso | ngs | realTimePcr
  deriving DecidableEq

inductive Sample where
  | tumorTissue | blood | marrow | peripheralBlood
  deriving DecidableEq

inductive Nodes where
  | negative | micrometastasis | positive (number : Nat)
  deriving DecidableEq

structure Context where
  performance : Performance Item
  claims : Option (ClaimHistory Item) := none
  priorPerformances : Option (Snapshot (Performance Item)) := none
  facilityComplies : Option Bool := none
  /-- 施設基準通知で指定された関連区分の届出を診療日時点で確認した。 -/
  relatedFacilityFilingConfirmed : Option Bool := none
  method : Option Method := none
  sample : Option Sample := none
  infertile : Option Bool := none
  assistedReproduction : Option Bool := none
  assessesTesticularSpermExtraction : Option Bool := none
  earlyInvasiveBreastCancer : Option Bool := none
  hormoneReceptorPositive : Option Bool := none
  her2Negative : Option Bool := none
  nodes : Option Nodes := none
  rnaGenesQuantified : Option Nat := none
  assessesDistantRecurrence : Option Bool := none
  determinesNeedForChemotherapy : Option Bool := none
  repeatMedicallyNecessary : Option Bool := none
  suspectedRpe65Dystrophy : Option Bool := none
  sufficientViableRetinalCells : Option Bool := none
  assistsVoretigeneEligibility : Option Bool := none
  deviceApprovedOrCertified : Option Bool := none
  deviceEvaluatesListedGenes : Option Bool := none
  followsIrdPanelGuideline : Option Bool := none
  aml : Option Bool := none
  assessesIdh1Variant : Option Bool := none
  assistsIvosidenibEligibility : Option Bool := none

def prior (c : Context) : Option Nat :=
  let site := c.performance.site
  c.claims.bind fun h => count h ⟨site.patient, none, Period.through site.date⟩
    (· == c.performance.item)

def headingRule (i : Item) : Rule Context Nat :=
  let code := "D006-" ++ toString i.suffix
  ⟨"primary/" ++ code ++ "/heading", primary code,
    fun c p => c.performance.item = i → p = i.points⟩

def facilityRule : Rule Context Unit :=
  ⟨"primary/D006-28/note/unnumbered/1", primary "D006-28 注",
    fun c _ => c.performance.item = .yDeletion →
      c.facilityComplies = some true ∧ c.relatedFacilityFilingConfirmed = some true⟩

def fertilityRule : Rule Context Unit :=
  ⟨"notice/D006-28/paragraph/unnumbered", notice "PDF354頁 D006-28",
    fun c _ => c.performance.item = .yDeletion →
      c.infertile = some true ∧ c.assistedReproduction = some true ∧
      c.method = some .pcrRsso ∧ c.assessesTesticularSpermExtraction = some true ∧
      prior c = some 0⟩

def BreastRepeat (c : Context) : Prop :=
  prior c = some 0 ∨ (∃ n, prior c = some n ∧ 0 < n ∧ c.repeatMedicallyNecessary = some true)

def breastRule : Rule Context Unit :=
  ⟨"notice/D006-29/paragraph/1", notice "PDF355頁 D006-29(1)",
    fun c _ => c.performance.item = .breastRecurrence →
      c.earlyInvasiveBreastCancer = some true ∧ c.hormoneReceptorPositive = some true ∧
      c.her2Negative = some true ∧ (c.nodes = some .negative ∨ c.nodes = some .micrometastasis ∨
        ∃ n, c.nodes = some (.positive n) ∧ 1 ≤ n ∧ n ≤ 3) ∧
      c.assessesDistantRecurrence = some true ∧ c.determinesNeedForChemotherapy = some true ∧
      c.sample = some .tumorTissue ∧ c.rnaGenesQuantified = some 21 ∧ BreastRepeat c⟩

def retinalRule : Rule Context Unit :=
  ⟨"notice/D006-30/paragraph/1", notice "PDF355頁 D006-30(1)",
    fun c _ => c.performance.item = .retinalDystrophy →
      c.suspectedRpe65Dystrophy = some true ∧ c.sufficientViableRetinalCells = some true ∧
      c.sample = some .blood ∧ c.method = some .ngs ∧
      c.assistsVoretigeneEligibility = some true ∧ prior c = some 0⟩

inductive IncludedCost where
  | multidisciplinaryInterpretation

def retinalCostRule : Rule Context (IncludedCost → Prop) :=
  ⟨"notice/D006-30/paragraph/1", notice "PDF355頁 D006-30(1) 費用",
    fun c included => c.performance.item = .retinalDystrophy → included .multidisciplinaryInterpretation⟩

def retinalDeviceRule : Rule Context Unit :=
  ⟨"notice/D006-30/paragraph/2", notice "PDF355頁 D006-30(2)",
    fun c _ => c.performance.item = .retinalDystrophy →
      c.deviceApprovedOrCertified = some true ∧ c.deviceEvaluatesListedGenes = some true⟩

def retinalApprovalRule : Rule Context Unit :=
  ⟨"notice/D006-30/paragraph/2/a", notice "PDF355頁 D006-30(2)ア",
    fun c _ => c.performance.item = .retinalDystrophy → c.deviceApprovedOrCertified = some true⟩

def retinalCoverageRule : Rule Context Unit :=
  ⟨"notice/D006-30/paragraph/2/i", notice "PDF355頁 D006-30(2)イ",
    fun c _ => c.performance.item = .retinalDystrophy → c.deviceEvaluatesListedGenes = some true⟩

def retinalGuidanceRule : Rule Context Unit :=
  ⟨"notice/D006-30/paragraph/3", notice "PDF355頁 D006-30(3)",
    fun c _ => c.performance.item = .retinalDystrophy → c.followsIrdPanelGuideline = some true⟩

def idh1Rule : Rule Context Unit :=
  ⟨"notice/D006-31/paragraph/unnumbered", notice "PDF355頁 D006-31",
    fun c _ => c.performance.item = .idh1 →
      c.aml = some true ∧ (c.sample = some .marrow ∨ c.sample = some .peripheralBlood) ∧
      c.method = some .realTimePcr ∧ c.assessesIdh1Variant = some true ∧
      c.assistsIvosidenibEligibility = some true ∧ prior c = some 0⟩

inductive Entry where
  | fertilityMedicalReason | breastRepeatReason | hormoneResult | her2Result | nodeStatus

structure Documentation where
  chart : Entry → Prop
  claimRemarks : Entry → Prop

def fertilityDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-28/paragraph/unnumbered", notice "PDF354頁 D006-28 記載",
    fun c d => c.performance.item = .yDeletion → d.chart .fertilityMedicalReason⟩

def priorPerformancesCount (c : Context) : Option Nat := do
  let h ← c.priorPerformances
  let site := c.performance.site
  let records ← h.select Performance.site ⟨site.patient, none, Period.through site.date⟩
    (fun p => p.item == c.performance.item)
  return records.length

def breastRepeatDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-29/paragraph/1", notice "PDF355頁 D006-29(1) 記載",
    fun c d => c.performance.item = .breastRecurrence →
      ∃ n, priorPerformancesCount c = some n ∧ (0 < n → d.claimRemarks .breastRepeatReason)⟩

def breastFindingsDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-29/paragraph/2", notice "PDF355頁 D006-29(2)",
    fun c d => c.performance.item = .breastRecurrence →
      d.claimRemarks .hormoneResult ∧ d.claimRemarks .her2Result ∧ d.claimRemarks .nodeStatus⟩

def eligibilityRules :=
  [facilityRule, fertilityRule, breastRule, retinalRule, retinalDeviceRule, retinalApprovalRule,
    retinalCoverageRule, retinalGuidanceRule, idh1Rule]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def rules : List (Rule Context Nat) := ledgerItems.map headingRule

def PermitsPoints (c : Context) (p : Nat) : Prop := Eligible c ∧ Satisfies rules c p

theorem permits_iff (c : Context) (p : Nat) :
    PermitsPoints c p ↔ Eligible c ∧ p = c.performance.item.points := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    exact h (headingRule c.performance.item)
      (List.mem_map.mpr ⟨_, by cases c.performance.item <;> simp [ledgerItems], rfl⟩) rfl
  · intro h r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    intro e
    simpa [e] using h

theorem determines : DeterminesOn Eligible rules := by
  intro c hc
  exact ⟨⟨c.performance.item.points, ((permits_iff _ _).mpr ⟨hc, rfl⟩).2⟩,
    fun _ _ ha hb => ((permits_iff _ _).mp ⟨hc, ha⟩).2.trans
      ((permits_iff _ _).mp ⟨hc, hb⟩).2.symm⟩

private def site : Site := ⟨1, 1, ⟨⟨2026, 10⟩, ⟨22, by decide⟩⟩⟩

private def exampleContext : Context :=
  { performance := { id := 1, site, item := .idh1 }
    claims := some ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩
    aml := some true, sample := some .marrow, method := some .realTimePcr
    assessesIdh1Variant := some true, assistsIvosidenibEligibility := some true }

example : PermitsPoints exampleContext 2500 := by
  apply (permits_iff _ _).mpr
  refine ⟨?_, rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, facilityRule, fertilityRule,
    breastRule, retinalRule, retinalDeviceRule, retinalApprovalRule, retinalCoverageRule,
    retinalGuidanceRule, idh1Rule, exampleContext, prior, count, Snapshot.select, Scope.Covers,
    Period.Within]

private def yExample : Context :=
  { exampleContext with
    performance := { exampleContext.performance with item := .yDeletion }
    infertile := some true, assistedReproduction := some true, method := some .pcrRsso
    assessesTesticularSpermExtraction := some true, facilityComplies := some true
    relatedFacilityFilingConfirmed := some true }

private def breastExample : Context :=
  { exampleContext with
    performance := { exampleContext.performance with item := .breastRecurrence }
    earlyInvasiveBreastCancer := some true, hormoneReceptorPositive := some true
    her2Negative := some true, nodes := some (.positive 3), sample := some .tumorTissue
    rnaGenesQuantified := some 21, assessesDistantRecurrence := some true
    determinesNeedForChemotherapy := some true }

private def retinalExample : Context :=
  { exampleContext with
    performance := { exampleContext.performance with item := .retinalDystrophy }
    suspectedRpe65Dystrophy := some true, sufficientViableRetinalCells := some true
    sample := some .blood, method := some .ngs, assistsVoretigeneEligibility := some true
    deviceApprovedOrCertified := some true, deviceEvaluatesListedGenes := some true
    followsIrdPanelGuideline := some true }

example : PermitsPoints yExample 3770 := by
  refine (permits_iff _ _).mpr ⟨?_, rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, facilityRule, fertilityRule,
    breastRule, retinalRule, retinalDeviceRule, retinalApprovalRule, retinalCoverageRule,
    retinalGuidanceRule, idh1Rule, yExample, exampleContext, prior, count, Snapshot.select,
    Scope.Covers, Period.Within]

example : PermitsPoints breastExample 43500 := by
  refine (permits_iff _ _).mpr ⟨?_, rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, facilityRule, fertilityRule,
    breastRule, retinalRule, retinalDeviceRule, retinalApprovalRule, retinalCoverageRule,
    retinalGuidanceRule, idh1Rule, breastExample, BreastRepeat, exampleContext, prior, count,
    Snapshot.select, Scope.Covers, Period.Within]

example : PermitsPoints retinalExample 23500 := by
  refine (permits_iff _ _).mpr ⟨?_, rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, facilityRule, fertilityRule,
    breastRule, retinalRule, retinalDeviceRule, retinalApprovalRule, retinalCoverageRule,
    retinalGuidanceRule, idh1Rule, retinalExample, exampleContext, prior, count, Snapshot.select,
    Scope.Covers, Period.Within]

example : ¬ Eligible { yExample with facilityComplies := none } := by
  intro h
  have hf := h facilityRule (by simp [eligibilityRules]) rfl
  cases hf.1

example : ¬ Eligible { breastExample with nodes := some (.positive 4) } := by
  intro h
  have hn := (h breastRule (by simp [eligibilityRules]) rfl).2.2.2.1
  simp at hn

example : ¬ Eligible { retinalExample with deviceApprovedOrCertified := some false } := by
  intro h
  have hd := h retinalApprovalRule (by simp [eligibilityRules]) rfl
  cases hd

example : ¬ Eligible { exampleContext with method := some .ngs } := by
  intro h
  have hm := (h idh1Rule (by simp [eligibilityRules]) rfl).2.2.1
  cases hm

example : ¬ Eligible { exampleContext with claims := none } := by
  intro h
  have hf := (h idh1Rule (by simp [eligibilityRules]) rfl).2.2.2.2.2
  cases hf

end Sanri.MedicalFee.D006Late
