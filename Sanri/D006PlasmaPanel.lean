import Sanri.D006Targeted

/-! D006-27、2026-10-22の外来。適格な項目の一採血単位の実施料。 -/
namespace Sanri.MedicalFee.D006PlasmaPanel

open Sanri.Logic Sanri.History
open D006GeneTests

inductive Item where
  | ros1 | alk | metEx14 | ntrk | ras | braf | colorectalHer2 | lungHer2
  | microsatellite | otherSolidHer2 | esr1
  deriving DecidableEq, Repr

def ledgerItems : List Item :=
  [.ros1, .alk, .metEx14, .ntrk, .ras, .braf, .colorectalHer2, .lungHer2,
    .microsatellite, .otherSolidHer2, .esr1]

def Item.number : Item → Nat
  | .ros1 => 1
  | .alk => 2
  | .metEx14 => 3
  | .ntrk => 4
  | .ras => 5
  | .braf => 6
  | .colorectalHer2 => 7
  | .lungHer2 => 8
  | .microsatellite => 9
  | .otherSolidHer2 => 10
  | .esr1 => 11

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem item_range (n : Nat) : (∃ i, ItemAt n i) ↔ 1 ≤ n ∧ n ≤ 11 := by
  constructor
  · rintro ⟨i, rfl⟩
    cases i <;> decide
  · intro h
    have casesN : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
    rcases casesN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.ros1, rfl⟩
    · exact ⟨.alk, rfl⟩
    · exact ⟨.metEx14, rfl⟩
    · exact ⟨.ntrk, rfl⟩
    · exact ⟨.ras, rfl⟩
    · exact ⟨.braf, rfl⟩
    · exact ⟨.colorectalHer2, rfl⟩
    · exact ⟨.lungHer2, rfl⟩
    · exact ⟨.microsatellite, rfl⟩
    · exact ⟨.otherSolidHer2, rfl⟩
    · exact ⟨.esr1, rfl⟩

def Item.points : Item → Nat
  | .ros1 => 2500
  | .alk => 2500
  | .metEx14 => 5000
  | .ntrk => 5000
  | .ras => 2500
  | .braf => 2500
  | .colorectalHer2 => 2500
  | .lungHer2 => 5000
  | .microsatellite => 2500
  | .otherSolidHer2 => 2500
  | .esr1 => 2500

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 27, number := i.number, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

inductive Cancer where
  | lung | colorectal | ovarian | breast | pancreatic | prostate | otherSolid
  deriving DecidableEq

inductive Sample where
  | blood | plasma
  deriving DecidableEq

/-- 同じ患者について通知が参照する検査。該当する目的・組織・項を確認して照合する。 -/
inductive Counterpart where
  | tissueRos1 | tissueAlk | tissueMetEx14 | tissueNtrk
  | colorectalTissueRas | colorectalTissueKras | lungTissueKrasG12c | lungTissueKras
  | lungPanel | colorectalTissueBraf | lungTissueHer2 | tissueMicrosatellite
  | n002Alk | n005_2 | brca | tumorBrca | plasmaRas
  deriving DecidableEq

/-- D004-2の項・枝とがん・検査種を照合する。実施目的の臨床判定は呼出元で確認する。 -/
def tissueCounterpart (d : D004Tumor.Context) (test : Counterpart) : Prop :=
  d.tumorCells = some true ∧
    match test with
    | .tissueRos1 => d.item = .drugAid ∧ d.cancer = .lung ∧ d.assay = some .ros1Fusion
    | .tissueAlk => d.item = .drugAid ∧ d.cancer = .lung ∧ d.assay = some .alkFusion
    | .tissueMetEx14 => d.item = .complex ∧ d.cancer = .lung ∧ d.assay = some .metEx14
    | .tissueNtrk => d.item = .complex ∧ d.cancer.solid = true ∧ d.assay = some .ntrkFusion
    | .colorectalTissueRas => d.item = .drugAid ∧ d.cancer = .colorectal ∧ d.assay = some .ras
    | .colorectalTissueKras => d.item = .otherSimple ∧ d.cancer = .colorectal ∧ d.assay = some .kras
    | .lungTissueKrasG12c => d.item = .drugAid ∧ d.cancer = .lung ∧ d.assay = some .krasG12c
    | .lungTissueKras => d.item = .otherSimple ∧ d.cancer = .lung ∧ d.assay = some .kras
    | .colorectalTissueBraf => d.item = .drugAid ∧ d.cancer = .colorectal ∧ d.assay = some .braf
    | .lungTissueHer2 => d.item = .complex ∧ d.cancer = .lung ∧ d.assay = some .her2
    | .tissueMicrosatellite => d.item = .drugAid ∧ d.cancer.solid = true ∧ d.assay = some .msi
    | _ => False

def lungPanelCounterpart : Item → Option D006Targeted.LungPanel.Counterpart
  | .ros1 => some .d006_27Ros1
  | .alk => some .d006_27Alk
  | .metEx14 => some .d006_27MetEx14
  | _ => none

structure Context where
  performance : Performance Item
  cancer : Option Cancer := none
  sample : Option Sample := none
  testedPatient : Option Nat := none
  detailedDiagnosis : Option Bool := none
  treatmentSelection : Option Bool := none
  antineoplasticSelection : Option Bool := none
  ngs : Option Bool := none
  history : Option (ClaimHistory Item) := none
  difficult : Counterpart → Option Bool := fun _ => none
  performedTogether : Counterpart → Option Bool := fun _ => none
  principal : Option Bool := none
  profileObtained : Option Bool := none

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def rateRule (i : Item) : Rule Item Nat :=
  ⟨"primary/D006-27/item/" ++ toString i.number,
    primary ((match i with
      | .ros1 | .alk | .metEx14 | .ntrk => "PDF178頁"
      | _ => "PDF179頁") ++ " D006-27 項" ++ toString i.number),
    fun item p => item = i → p = i.points⟩

def prior (c : Context) : Option Nat :=
  let site := c.performance.site
  c.history.bind fun h => count h ⟨site.patient, none, Period.through site.date⟩
    (· == c.performance.item)

def generalRule : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/1", notice "PDF351頁 D006-27(1)", fun c _ =>
    (∃ cancer, c.cancer = some cancer) ∧ (c.sample = some .blood ∨ c.sample = some .plasma) ∧
    c.testedPatient = some c.performance.site.patient ∧ c.detailedDiagnosis = some true ∧
    c.treatmentSelection = some true ∧ prior c = some 0⟩

def NgsSelection (c : Context) (s : Sample) : Prop :=
  c.sample = some s ∧ c.ngs = some true ∧ c.antineoplasticSelection = some true ∧ prior c = some 0

def DifficultAndSeparate (c : Context) (test : Counterpart) : Prop :=
  c.difficult test = some true ∧ c.performedTogether test = some false

def PrincipalIfTogether (c : Context) (test : Counterpart) : Prop :=
  c.performedTogether test = some false ∨
    (c.performedTogether test = some true ∧ c.principal = some true)

def BrcaCancer (c : Context) : Prop :=
  ∃ k ∈ [Cancer.ovarian, .breast, .pancreatic, .prostate], c.cancer = some k

inductive Reason where
  | tissueDifficulty | rasMedicalReason
  deriving DecidableEq

structure Documentation where
  chart : Reason → Prop
  claim : Reason → Prop
  /-- (4)ウは摘要欄への限定が原文にない。 -/
  statement : Reason → Prop

structure Disclosure where
  onlyTargetResultsProvided : Prop
  nonTargetResultsExcludedFromTreatment : Prop

def disclosureRule : Rule Context Disclosure :=
  ⟨"notice/D006-27/paragraph/11", notice "PDF354頁 D006-27(11)", fun c d =>
    c.ngs = some true → c.antineoplasticSelection = some true →
    c.profileObtained = some false ∨ (c.profileObtained = some true ∧
      d.onlyTargetResultsProvided ∧ d.nonTargetResultsExcludedFromTreatment)⟩

def ros1Paragraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/2", notice "PDF351–352頁 D006-27 2",
    fun c _ => c.performance.item = .ros1 →
      c.cancer = some .lung⟩

def ros1Method : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/2/a", notice "PDF351–352頁 D006-27 2/a",
    fun c _ => c.performance.item = .ros1 →
      NgsSelection c .blood⟩

def ros1Difficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/2/i", notice "PDF351–352頁 D006-27 2/i",
    fun c _ => c.performance.item = .ros1 →
      DifficultAndSeparate c .tissueRos1⟩

def ros1Documentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/2/u", notice "PDF351–352頁 D006-27 2/u",
    fun c d => c.performance.item = .ros1 →
      d.chart .tissueDifficulty ∧ d.claim .tissueDifficulty⟩

def alkParagraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/3", notice "PDF352頁 D006-27 3",
    fun c _ => c.performance.item = .alk →
      c.cancer = some .lung⟩

def alkMethod : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/3/a", notice "PDF352頁 D006-27 3/a",
    fun c _ => c.performance.item = .alk →
      NgsSelection c .blood⟩

def alkDifficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/3/i", notice "PDF352頁 D006-27 3/i",
    fun c _ => c.performance.item = .alk →
      DifficultAndSeparate c .tissueAlk⟩

def alkDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/3/u", notice "PDF352頁 D006-27 3/u",
    fun c d => c.performance.item = .alk →
      d.chart .tissueDifficulty ∧ d.claim .tissueDifficulty⟩

def alkPathology : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/3/e", notice "PDF352頁 D006-27 3/e",
    fun c _ => c.performance.item = .alk →
      PrincipalIfTogether c .n002Alk ∧ PrincipalIfTogether c .n005_2⟩

def metEx14Paragraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/4", notice "PDF352頁 D006-27 4",
    fun c _ => c.performance.item = .metEx14 →
      c.cancer = some .lung⟩

def metEx14Method : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/4/a", notice "PDF352頁 D006-27 4/a",
    fun c _ => c.performance.item = .metEx14 →
      NgsSelection c .plasma⟩

def metEx14Difficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/4/i", notice "PDF352頁 D006-27 4/i",
    fun c _ => c.performance.item = .metEx14 →
      DifficultAndSeparate c .tissueMetEx14⟩

def metEx14Documentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/4/u", notice "PDF352頁 D006-27 4/u",
    fun c d => c.performance.item = .metEx14 →
      d.chart .tissueDifficulty ∧ d.statement .tissueDifficulty⟩

def ntrkParagraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/5", notice "PDF352頁 D006-27 5",
    fun c _ => c.performance.item = .ntrk →
      (∃ k, c.cancer = some k)⟩

def ntrkMethod : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/5/a", notice "PDF352頁 D006-27 5/a",
    fun c _ => c.performance.item = .ntrk →
      NgsSelection c .blood⟩

def ntrkDifficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/5/i", notice "PDF352頁 D006-27 5/i",
    fun c _ => c.performance.item = .ntrk →
      DifficultAndSeparate c .tissueNtrk⟩

def ntrkDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/5/u", notice "PDF352頁 D006-27 5/u",
    fun c d => c.performance.item = .ntrk →
      d.chart .tissueDifficulty ∧ d.claim .tissueDifficulty⟩

def ntrkBrca : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/5/e", notice "PDF352頁 D006-27 5/e",
    fun c _ => c.performance.item = .ntrk →
      BrcaCancer c → PrincipalIfTogether c .brca⟩

def rasParagraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/6", notice "PDF352–353頁 D006-27 6",
    fun c _ => c.performance.item = .ras →
      (c.cancer = some .colorectal ∨ c.cancer = some .lung)⟩

def rasMethod : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/6/a", notice "PDF352頁 D006-27(6)ア",
    fun c _ => c.performance.item = .ras →
      NgsSelection c .blood ∨ (c.cancer = some .colorectal ∧ NgsSelection c .plasma)⟩

def brafParagraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/7", notice "PDF353頁 D006-27 7",
    fun c _ => c.performance.item = .braf →
      c.cancer = some .colorectal⟩

def brafMethod : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/7/a", notice "PDF353頁 D006-27 7/a",
    fun c _ => c.performance.item = .braf →
      NgsSelection c .blood⟩

def brafDifficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/7/i", notice "PDF353頁 D006-27 7/i",
    fun c _ => c.performance.item = .braf →
      DifficultAndSeparate c .colorectalTissueBraf⟩

def brafDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/7/u", notice "PDF353頁 D006-27 7/u",
    fun c d => c.performance.item = .braf →
      d.chart .tissueDifficulty ∧ d.claim .tissueDifficulty⟩

def colorectalHer2Paragraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/8", notice "PDF353頁 D006-27 8",
    fun c _ => c.performance.item = .colorectalHer2 →
      c.cancer = some .colorectal ∧ NgsSelection c .blood⟩

def lungHer2Paragraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/9", notice "PDF353–354頁 D006-27 9",
    fun c _ => c.performance.item = .lungHer2 →
      c.cancer = some .lung⟩

def lungHer2Method : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/9/a", notice "PDF353–354頁 D006-27 9/a",
    fun c _ => c.performance.item = .lungHer2 →
      NgsSelection c .blood⟩

def lungHer2Difficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/9/i", notice "PDF353–354頁 D006-27 9/i",
    fun c _ => c.performance.item = .lungHer2 →
      DifficultAndSeparate c .lungTissueHer2⟩

def lungHer2Documentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/9/u", notice "PDF353–354頁 D006-27 9/u",
    fun c d => c.performance.item = .lungHer2 →
      d.chart .tissueDifficulty ∧ d.claim .tissueDifficulty⟩

def microsatelliteParagraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/10", notice "PDF354頁 D006-27 10",
    fun c _ => c.performance.item = .microsatellite →
      (∃ k, c.cancer = some k)⟩

def microsatelliteMethod : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/10/a", notice "PDF354頁 D006-27 10/a",
    fun c _ => c.performance.item = .microsatellite →
      NgsSelection c .blood⟩

def microsatelliteDifficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/10/i", notice "PDF354頁 D006-27 10/i",
    fun c _ => c.performance.item = .microsatellite →
      DifficultAndSeparate c .tissueMicrosatellite⟩

def microsatelliteDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/10/e", notice "PDF354頁 D006-27 10/e",
    fun c d => c.performance.item = .microsatellite →
      d.chart .tissueDifficulty ∧ d.claim .tissueDifficulty⟩

def msiBrca : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/10/u", notice "PDF354頁 D006-27 10/u",
    fun c _ => c.performance.item = .microsatellite →
      BrcaCancer c → PrincipalIfTogether c .tumorBrca⟩

def otherSolidHer2Paragraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/12", notice "PDF354頁 D006-27 12",
    fun c _ => c.performance.item = .otherSolidHer2 →
      ∃ k, c.cancer = some k ∧ k ≠ .colorectal ∧ k ≠ .lung ∧ NgsSelection c .blood⟩

def esr1Paragraph : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/13", notice "PDF354頁 D006-27 13",
    fun c _ => c.performance.item = .esr1 →
      c.cancer = some .breast ∧ NgsSelection c .blood⟩


def colorectalRasRoute : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/6/i/i", notice "PDF353頁 D006-27(6)イ(イ)",
    fun c _ => c.cancer = some .colorectal ∧
      (c.difficult .colorectalTissueRas = some true ∨ c.difficult .colorectalTissueKras = some true) ∧
      c.performedTogether .colorectalTissueRas = some false ∧
      c.performedTogether .colorectalTissueKras = some false⟩

def lungRasRoute : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/6/i/ro", notice "PDF353頁 D006-27(6)イ(ロ)",
    fun c _ => c.cancer = some .lung ∧
      (c.difficult .lungTissueKrasG12c = some true ∨ c.difficult .lungTissueKras = some true) ∧
      c.performedTogether .lungTissueKrasG12c = some false ∧
      c.performedTogether .lungTissueKras = some false⟩

def lungPanelRoute : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/6/i/ha", notice "PDF353頁 D006-27(6)イ(ハ)",
    fun c _ => c.cancer = some .lung ∧ DifficultAndSeparate c .lungPanel⟩
def rasDifficulty : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/6/i", notice "PDF353頁 D006-27 6/i",
    fun c _ => c.performance.item = .ras →
      colorectalRasRoute.holds c () ∨ lungRasRoute.holds c () ∨ lungPanelRoute.holds c ()⟩

def rasDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-27/paragraph/6/u", notice "PDF353頁 D006-27 6/u",
    fun c d => c.performance.item = .ras →
      d.chart .rasMedicalReason ∧ d.claim .rasMedicalReason⟩

def rasPlasma : Rule Context Unit :=
  ⟨"notice/D006-27/paragraph/6/e", notice "PDF353頁 D006-27 6/e",
    fun c _ => c.performance.item = .ras →
      c.cancer = some .colorectal → c.sample = some .plasma →
        c.performedTogether .plasmaRas = some false⟩


def eligibilityRules : List (Rule Context Unit) :=
  [generalRule, ros1Paragraph, ros1Method, ros1Difficulty,
    alkParagraph, alkMethod, alkDifficulty, alkPathology,
    metEx14Paragraph, metEx14Method, metEx14Difficulty, ntrkParagraph,
    ntrkMethod, ntrkDifficulty, ntrkBrca, rasParagraph,
    rasMethod, brafParagraph, brafMethod, brafDifficulty,
    colorectalHer2Paragraph, lungHer2Paragraph, lungHer2Method, lungHer2Difficulty,
    microsatelliteParagraph, microsatelliteMethod, microsatelliteDifficulty, msiBrca,
    otherSolidHer2Paragraph, esr1Paragraph, rasDifficulty, rasPlasma]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def individualRules : List (Rule Item Nat) := ledgerItems.map rateRule

theorem individual_iff (i : Item) (p : Nat) :
    Satisfies individualRules i p ↔ p = i.points := by
  constructor
  · intro h
    exact h (rateRule i) (List.mem_map.mpr ⟨i, by cases i <;> simp [ledgerItems], rfl⟩) rfl
  · intro h r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro e
    simpa [e] using h

theorem determines_individual : DeterminesOn (fun _ => True) individualRules := by
  intro i _
  exact ⟨⟨i.points, (individual_iff _ _).mpr rfl⟩,
    fun a b ha hb => ((individual_iff _ _).mp ha).trans ((individual_iff _ _).mp hb).symm⟩

inductive DrawItem where
  | panel (item : Item)
  | egfr
  deriving DecidableEq

def DrawItem.higherGroup : DrawItem → Bool
  | .panel .metEx14 | .panel .ntrk | .panel .lungHer2 => true
  | _ => false

structure Draw where
  anchor : Performance DrawItem
  history : Snapshot (Performance DrawItem)
  period : Period
  panelContexts : Nat → Option Context
  egfrContexts : Nat → Option Egfr.Context

def Draw.members (d : Draw) : Option (List (Performance DrawItem)) := do
  let site := d.anchor.site
  let scope : Scope := ⟨site.patient, some site.institution, d.period⟩
  let entries ← d.history.select Performance.site scope (fun _ => true)
  if !entries.contains d.anchor then none else
    entries.filterM d.anchor.sameDraw

def Draw.MemberPoints (d : Draw) (p : Performance DrawItem) (n : Nat) : Prop :=
  match p.item with
  | .panel item =>
    ∃ c, d.panelContexts p.id = some c ∧ c.performance = { p with item := item } ∧
      Eligible c ∧ Satisfies individualRules item n
  | .egfr =>
    ∃ c r, d.egfrContexts p.id = some c ∧
      { c.performance with item := DrawItem.egfr } = p ∧
      Satisfies Egfr.rules c r ∧ n = r.total

structure Assessed where
  performance : Performance DrawItem
  points : Nat

def Draw.Assesses (d : Draw) (xs : List Assessed) : Prop :=
  d.members = some (xs.map Assessed.performance) ∧
  (xs.map (·.performance.item)).Nodup ∧
  ∀ x ∈ xs, d.MemberPoints x.performance x.points

theorem Draw.member_points_unique (d : Draw) (p : Performance DrawItem) (a b : Nat)
    (ha : d.MemberPoints p a) (hb : d.MemberPoints p b) : a = b := by
  cases h : p.item with
  | panel i =>
    rw [MemberPoints, h] at ha hb
    exact ((individual_iff _ _).mp ha.choose_spec.2.2.2).trans
      ((individual_iff _ _).mp hb.choose_spec.2.2.2).symm
  | egfr =>
    rw [MemberPoints, h] at ha hb
    obtain ⟨c, r, hc, _, hr, rfl⟩ := ha
    obtain ⟨c', r', hc', _, hr', rfl⟩ := hb
    have heq := Option.some.inj (hc.symm.trans hc')
    subst c'
    have h₁ := (Egfr.satisfies_iff _ _).mp hr
    have h₂ := (Egfr.satisfies_iff _ _).mp hr'
    rw [Option.some.inj (h₁.2.symm.trans h₂.2)]

private theorem assessments_eq (d : Draw) (a b : List Assessed)
    (performanceEq : a.map Assessed.performance = b.map Assessed.performance)
    (ha : ∀ x ∈ a, d.MemberPoints x.performance x.points)
    (hb : ∀ x ∈ b, d.MemberPoints x.performance x.points) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp at performanceEq
    | cons y ys =>
      obtain ⟨hp, hps⟩ := List.cons.inj performanceEq
      have hxa := ha x (by simp)
      have hyb := hb y (by simp)
      rw [← hp] at hyb
      have hpoints := d.member_points_unique x.performance x.points y.points hxa hyb
      have hxy : x = y := by cases x; cases y; simp_all
      rw [hxy, ih ys hps
        (fun z hz => ha z (List.mem_cons_of_mem _ hz))
        (fun z hz => hb z (List.mem_cons_of_mem _ hz))]

theorem Draw.assessed_unique (d : Draw) (a b : List Assessed)
    (ha : d.Assesses a) (hb : d.Assesses b) : a = b :=
  assessments_eq d a b (Option.some.inj (ha.1.symm.trans hb.1)) ha.2.2 hb.2.2

private def group (higher : Bool) (xs : List Assessed) : List Assessed :=
  xs.filter (fun x => x.performance.item.higherGroup == higher)

private def subtotal (xs : List Assessed) : Nat := (xs.map Assessed.points).sum

structure DrawPoints where
  ordinary : Nat
  higher : Nat
  deriving DecidableEq, Repr

def DrawPoints.total (p : DrawPoints) : Nat := p.ordinary + p.higher

def ordinaryBundleRule : Rule (List Assessed) DrawPoints :=
  ⟨"primary/D006-27/note/1", primary "PDF179頁 D006-27 注1", fun xs p =>
    let members := group false xs
    (members.length < 2 → p.ordinary = subtotal members) ∧
    (members.length = 2 → p.ordinary = 4000) ∧
    (members.length = 3 → p.ordinary = 6000) ∧
    (4 ≤ members.length → p.ordinary = 8000)⟩

def higherBundleRule : Rule (List Assessed) DrawPoints :=
  ⟨"primary/D006-27/note/2", primary "PDF179頁 D006-27 注2", fun xs p =>
    let members := group true xs
    (members.length < 2 → p.higher = subtotal members) ∧
    (members.length = 2 → p.higher = 8000) ∧
    (3 ≤ members.length → p.higher = 12000)⟩

def bundleRules := [ordinaryBundleRule, higherBundleRule]

def bundlePoints (xs : List Assessed) : DrawPoints :=
  let ordinary := group false xs
  let higher := group true xs
  ⟨match ordinary.length with
    | 0 | 1 => subtotal ordinary
    | 2 => 4000
    | 3 => 6000
    | _ => 8000,
   match higher.length with
    | 0 | 1 => subtotal higher
    | 2 => 8000
    | _ => 12000⟩

theorem bundle_iff (xs : List Assessed) (p : DrawPoints) :
    Satisfies bundleRules xs p ↔ p = bundlePoints xs := by
  obtain ⟨ordinary, higher⟩ := p
  generalize h₁ : (group false xs).length = n
  generalize h₂ : (group true xs).length = m
  rcases n with _ | _ | _ | _ | n <;> rcases m with _ | _ | _ | m <;>
    simp [bundleRules, satisfies_cons, satisfies_nil, ordinaryBundleRule, higherBundleRule,
      bundlePoints, h₁, h₂] <;> omega

theorem determines_draw (d : Draw) (xs : List Assessed) (_ : d.Assesses xs) :
    DeterminesAt bundleRules xs :=
  ⟨⟨bundlePoints xs, (bundle_iff _ _).mpr rfl⟩,
    fun _ _ ha hb => ((bundle_iff _ _).mp ha).trans ((bundle_iff _ _).mp hb).symm⟩

/-- 適格な一採血の評価が存在する範囲で、評価リストを選び直しても内訳は一意。 -/
theorem determines_assessed_draw (d : Draw) (h : ∃ xs, d.Assesses xs) :
    (∃ p, ∃ xs, d.Assesses xs ∧ Satisfies bundleRules xs p) ∧
    ∀ p q, (∃ xs, d.Assesses xs ∧ Satisfies bundleRules xs p) →
      (∃ ys, d.Assesses ys ∧ Satisfies bundleRules ys q) → p = q := by
  obtain ⟨xs, hx⟩ := h
  refine ⟨⟨bundlePoints xs, xs, hx, (bundle_iff _ _).mpr rfl⟩, ?_⟩
  rintro p q ⟨a, ha, hp⟩ ⟨b, hb, hq⟩
  rw [d.assessed_unique a b ha hb] at hp
  exact ((bundle_iff _ _).mp hp).trans ((bundle_iff _ _).mp hq).symm

private def site : Site := ⟨1, 1, ⟨⟨2026, 10⟩, ⟨22, by decide⟩⟩⟩

private def exampleContext : Context :=
  { performance := { id := 1, site, item := .colorectalHer2, draw := some 1 }
    cancer := some .colorectal, sample := some .blood, testedPatient := some 1
    detailedDiagnosis := some true, treatmentSelection := some true,
    antineoplasticSelection := some true, ngs := some true
    history := some ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩ }

private theorem example_eligible : Eligible exampleContext := by
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, generalRule,
    ros1Paragraph, ros1Method, ros1Difficulty, alkParagraph, alkMethod, alkDifficulty, alkPathology,
    metEx14Paragraph, metEx14Method, metEx14Difficulty, ntrkParagraph, ntrkMethod, ntrkDifficulty,
    ntrkBrca, rasParagraph, rasMethod, rasDifficulty, rasPlasma, brafParagraph, brafMethod,
    brafDifficulty, colorectalHer2Paragraph, lungHer2Paragraph, lungHer2Method, lungHer2Difficulty,
    microsatelliteParagraph, microsatelliteMethod, microsatelliteDifficulty, msiBrca,
    otherSolidHer2Paragraph, esr1Paragraph, NgsSelection, prior, exampleContext, count,
    Snapshot.select, Scope.Covers, Period.Within, site]

private def examplePerformance : Performance DrawItem :=
  { exampleContext.performance with item := .panel .colorectalHer2 }

private def exampleDraw : Draw :=
  ⟨examplePerformance, ⟨site.monthScope, [examplePerformance]⟩, site.monthScope.period,
    fun _ => some exampleContext, fun _ => none⟩

example : exampleDraw.Assesses [⟨examplePerformance, 2500⟩] := by
  refine ⟨by decide, by decide, ?_⟩
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  exact ⟨exampleContext, rfl, rfl, example_eligible, (individual_iff _ _).mpr rfl⟩

example : (bundlePoints [⟨examplePerformance, 2500⟩]).total = 2500 := rfl

example : (bundlePoints [⟨examplePerformance, 2500⟩,
    ⟨{ examplePerformance with id := 2, item := .egfr }, 1890⟩]).total = 4000 := rfl

private def egfrPerformance : Performance DrawItem :=
  { examplePerformance with id := 2, item := .egfr }

private def egfrContext : Egfr.Context :=
  { performance := { egfrPerformance with item := Egfr.Purpose.initialSelection }
    plasma := some true, method := some .realtimePcr, lungCancer := some true
    tissueTestingMedicallyDifficult := some true
    priorClaims := some ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩
    priorPerformances := some ⟨⟨site.patient, none, site.monthScope.period⟩, []⟩
    monthlySelection := some ⟨⟨⟨site.patient, none, site.monthScope.period⟩, []⟩,
      none, fun _ _ => none⟩ }

private def jointDraw : Draw :=
  { exampleDraw with
    history := ⟨site.monthScope, [examplePerformance, egfrPerformance]⟩
    egfrContexts := fun _ => some egfrContext }

private def jointAssessment : List Assessed :=
  [⟨examplePerformance, 2500⟩, ⟨egfrPerformance, 2100⟩]

example : jointDraw.Assesses jointAssessment ∧
    Satisfies bundleRules jointAssessment ⟨4000, 0⟩ := by
  refine ⟨⟨by decide, by decide, ?_⟩, (bundle_iff _ _).mpr rfl⟩
  intro x hx
  simp only [jointAssessment, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨exampleContext, rfl, rfl, example_eligible, (individual_iff _ _).mpr rfl⟩
  · refine ⟨egfrContext, ⟨2100, 2100⟩, rfl, rfl, ?_, rfl⟩
    apply (Egfr.satisfies_iff _ _).mpr
    refine ⟨⟨⟨0, rfl⟩, ⟨rfl, Or.inl rfl⟩, ⟨rfl, rfl, rfl⟩, ?_⟩, rfl⟩
    exact ⟨_, rfl, ⟨[], rfl, Or.inl rfl, by simp⟩, by simp [egfrContext]⟩

example : ¬ Eligible { exampleContext with ngs := some false } := by
  intro h
  have hm := h colorectalHer2Paragraph (by simp [eligibilityRules]) rfl
  cases hm.2.2.1

example : ¬ Eligible { exampleContext with history := none } := by
  intro h
  have hf := (h generalRule (by simp [eligibilityRules])).2.2.2.2.2
  cases hf

example : ({ exampleDraw with anchor := { examplePerformance with draw := none } } : Draw).members
    = none := by decide

end Sanri.MedicalFee.D006PlasmaPanel
