import Sanri.D004
import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment
import Sanri.ExaminationDrugsMaterials

namespace Sanri.MedicalFee.D010

open Sanri.Logic Sanri.History

inductive Item where
  | urinarySugar | calculus | tyrosine | aminoAcidPerKind | aminoAcidFiveOrMore
  | btr | qualitativeAminoAcid | fattyAcidFraction | organicAcids | veryLongChain
  | tandemMass | otherCongenital
  deriving DecidableEq

def Item.number : Item → Nat
  | .urinarySugar => 1 | .calculus => 2 | .tyrosine => 3
  | .aminoAcidPerKind | .aminoAcidFiveOrMore => 4
  | .btr => 5 | .qualitativeAminoAcid => 6 | .fattyAcidFraction => 7
  | _ => 8

def Item.branch : Item → Nat
  | .aminoAcidPerKind | .organicAcids => 1
  | .aminoAcidFiveOrMore | .veryLongChain => 2
  | .tandemMass => 3 | .otherCongenital => 4 | _ => 0

def Item.rate : Item → Nat
  | .urinarySugar => 38 | .calculus => 117 | .tyrosine => 200
  | .aminoAcidPerKind => 279 | .aminoAcidFiveOrMore => 1074
  | .btr => 283 | .qualitativeAminoAcid => 350 | .fattyAcidFraction => 389
  | .organicAcids | .veryLongChain => 1141
  | .tandemMass | .otherCongenital => 1074

def ledgerItems : List Item :=
  [.urinarySugar, .calculus, .tyrosine, .aminoAcidPerKind, .aminoAcidFiveOrMore,
    .btr, .qualitativeAminoAcid, .fattyAcidFraction, .organicAcids, .veryLongChain,
    .tandemMass, .otherCongenital]

inductive Method where
  | enzyme | gcms | tandemMs | celluloseAcetateElectrophoresis
  deriving DecidableEq

inductive Purpose where
  | diagnosis | followup
  deriving DecidableEq

inductive LoadDrug where
  | phenylalanine | histidine
  deriving DecidableEq

structure LoadMeasurement where
  administered : LoadDrug
  measured : LoadDrug
  serumOrUrine : Prop
  quantitative : Prop

structure Context where
  performance : Performance Item
  aminoAcidKinds : Option (List Nat) := none
  history : Option (ClaimHistory Unit) := none
  facilityStandardMet : Prop := False
  facilityNotified : Prop := False
  performedInsideInstitution : Prop := False
  purpose : Option Purpose := none
  method : Option Method := none
  congenitalMetabolicDisorderStronglySuspected : Prop := False
  organicAcidDisorderSuspected : Prop := False
  adrenalOrPeroxisomalDisorderSuspected : Prop := False
  fattyAcidDisorderSuspected : Prop := False
  mucopolysaccharidosisOrMucolipidosisSuspected : Prop := False
  urinaryOrganicAcidsAnalyzed : Prop := False
  veryLongChainFattyAcidsMeasuredInBlood : Prop := False
  freeAndAcylCarnitinesAnalyzed : Prop := False
  mucopolysaccharideFractionQuantifiedOrEquivalent : Prop := False
  /-- 当該実施に結び付く負荷測定。空リストは該当測定がないと確認した入力。 -/
  loadMeasurements : List LoadMeasurement

def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度・2026-06-01適用",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def Item.path (i : Item) : String :=
  let suffix := match i.branch with
    | 1 => "/i" | 2 => "/ro" | 3 => "/ha" | 4 => "/ni" | _ => ""
  toString i.number ++ suffix

def itemRule (i : Item) : Rule Context Nat :=
  ⟨"primary/D010/item/" ++ toString i.number, primary ("PDF183頁 D010 " ++ i.path), fun c p =>
    c.performance.item = i →
    match i with
    | .aminoAcidPerKind =>
      ∃ xs, c.aminoAcidKinds = some xs ∧ xs.Nodup ∧ 0 < xs.length ∧ xs.length < 5 ∧ p = 279 * xs.length
    | .aminoAcidFiveOrMore =>
      ∃ xs, c.aminoAcidKinds = some xs ∧ xs.Nodup ∧ 5 ≤ xs.length ∧ p = 1074
    | _ => p = i.rate⟩

def aminoAcidHeading : Rule Context Unit :=
  ⟨"primary/D010/item/4", primary "PDF183頁 D010 4", fun c _ =>
    c.performance.item.number = 4 → ∃ xs, c.aminoAcidKinds = some xs ∧ xs.Nodup ∧
      0 < xs.length ∧ (c.performance.item = .aminoAcidFiveOrMore ↔ 5 ≤ xs.length)⟩

def congenitalHeading : Rule Context Unit :=
  ⟨"primary/D010/item/8", primary "PDF183頁 D010 8", fun c _ =>
    c.performance.item.number = 8 → 1 ≤ c.performance.item.branch ∧ c.performance.item.branch ≤ 4⟩

def MonthAvailable (c : Context) : Prop :=
  ∃ h, c.history = some h ∧
    withinLimit h ⟨c.performance.site.patient, none, Period.month c.performance.site.date.month⟩
      (fun _ => true) 0 = some true

def congenitalNotice1 : Rule Context Unit :=
  ⟨"primary/D010/note/1", primary "PDF184頁 D010 8注1", fun c _ =>
    c.performance.item ∈ [.organicAcids, .veryLongChain, .tandemMass] →
      c.facilityStandardMet ∧ c.facilityNotified ∧ MonthAvailable c⟩

def congenitalNotice2 : Rule Context Unit :=
  ⟨"primary/D010/note/2", primary "PDF184頁 D010 8注2", fun c _ =>
    c.performance.item = .otherCongenital →
      c.facilityStandardMet ∧ c.facilityNotified ∧ c.performedInsideInstitution ∧ MonthAvailable c⟩

private def condition (id : String) (holds : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D010/paragraph/" ++ id, notice ("PDF369頁 D010(" ++ id ++ ")"), fun c _ => holds c⟩

def loadingRule : Rule Context Unit :=
  condition "1" fun c => ∀ m ∈ c.loadMeasurements,
    m.measured = m.administered → m.serumOrUrine → m.quantitative →
      c.performance.item = .aminoAcidPerKind ∧ ∃ xs, c.aminoAcidKinds = some xs ∧ xs.length = 1

def tyrosineRule : Rule Context Unit :=
  condition "2" fun c => c.performance.item = .tyrosine → c.method = some .enzyme

def btrRule : Rule Context Unit :=
  condition "3" fun c => c.performance.item = .btr → c.method = some .enzyme

def congenitalRule : Rule Context Unit :=
  condition "4" fun c => c.performance.item.number = 8 →
    c.congenitalMetabolicDisorderStronglySuspected ∧ c.purpose.isSome = true

def organicAcidRule : Rule Context Unit :=
  condition "4/a" fun c => c.performance.item = .organicAcids →
    c.organicAcidDisorderSuspected ∧ c.method = some .gcms ∧ c.urinaryOrganicAcidsAnalyzed

def veryLongChainRule : Rule Context Unit :=
  condition "4/i" fun c => c.performance.item = .veryLongChain →
    c.adrenalOrPeroxisomalDisorderSuspected ∧ c.method = some .gcms ∧ c.veryLongChainFattyAcidsMeasuredInBlood

def tandemMassRule : Rule Context Unit :=
  condition "4/u" fun c => c.performance.item = .tandemMass →
    (c.organicAcidDisorderSuspected ∨ c.fattyAcidDisorderSuspected) ∧
      c.method = some .tandemMs ∧ c.freeAndAcylCarnitinesAnalyzed

def otherRule : Rule Context Unit :=
  condition "4/e" fun c => c.performance.item = .otherCongenital →
    c.mucopolysaccharidosisOrMucolipidosisSuspected ∧ c.method = some .celluloseAcetateElectrophoresis ∧
      c.mucopolysaccharideFractionQuantifiedOrEquivalent

def eligibilityRules :=
  [aminoAcidHeading, congenitalHeading, congenitalNotice1, congenitalNotice2, loadingRule,
    tyrosineRule, btrRule, congenitalRule, organicAcidRule, veryLongChainRule, tandemMassRule, otherRule]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def rules : List (Rule Context Nat) := ledgerItems.map itemRule

def legacyRequest (c : Context) : SpecimenTests.Request :=
  let i := c.performance.item
  { code := .d010, number := i.number, branch := i.branch
    quantity := ((c.aminoAcidKinds.map List.length).getD 0)
    conditions := { facilityNotified := true, performedInsideInstitution := true } }

private theorem activeRule (c : Context) (p : Nat) :
    Satisfies rules c p ↔ (itemRule c.performance.item).holds c p := by
  constructor
  · intro h
    exact h _ (List.mem_map.mpr ⟨_, by cases c.performance.item <;> simp [ledgerItems], rfl⟩)
  · intro h _ hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    intro hi
    subst i
    exact h rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem legacy_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔
      (SpecimenTests.assessOne (legacyRequest c) = some (.charged p 0) ∧
        ∀ xs, c.performance.item.number = 4 → c.aminoAcidKinds = some xs → xs.Nodup) := by
  rw [activeRule]
  cases hi : c.performance.item <;>
    simp [itemRule, hi, legacyRequest, Item.number, Item.branch, Item.rate, SpecimenTests.assessOne,
      SpecimenTests.eligible, SpecimenTests.additions, SpecimenTests.rapidMicrobialEligible,
      SpecimenTests.lookup, SpecimenTests.catalog]
  all_goals
    cases c.aminoAcidKinds <;> simp [eq_comm, List.length_pos_iff] <;> grind

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  have quantity := h aminoAcidHeading (by simp [eligibilityRules])
  have active : ∃ p, (itemRule c.performance.item).holds c p := by
    cases hi : c.performance.item <;> simp [itemRule, hi, Item.rate]
    · obtain ⟨xs, hxs, distinct, positive, branch⟩ := quantity (by simp [hi, Item.number])
      have small : xs.length < 5 := by
        have excluded : ¬ 5 ≤ xs.length := fun large => Item.noConfusion (hi.symm.trans (branch.mpr large))
        omega
      exact ⟨279 * xs.length, xs, hxs, distinct, positive, small, rfl⟩
    · obtain ⟨xs, hxs, distinct, _, branch⟩ := quantity (by simp [hi, Item.number])
      exact ⟨1074, xs, hxs, distinct, branch.mp hi, rfl⟩
  obtain ⟨p, hp⟩ := active
  refine ⟨⟨p, (activeRule ..).mpr hp⟩, ?_⟩
  intro a b ha hb
  have ha' := ((legacy_iff c a).mp ha).1
  have hb' := ((legacy_iff c b).mp hb).1
  simpa using ha'.symm.trans hb'

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 10, number := i.number, ordinaryCategory := .biochemicalII }

def toSpecimenItem (kind points : Nat) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := points }

/-- 準用する検査種類が確定した個別点数を既存の準用入力へ渡す。 -/
def urineReference (c : Context) (p : Nat) (_ : Eligible c) (_ : Satisfies rules c p) :
    UrineFecalTests.ReferenceResolution :=
  ⟨.other .d010, p, true⟩

def fluidReference (c : Context) (p : Nat) (_ : Eligible c) (_ : Satisfies rules c p) :
    D004.ReferenceResolution :=
  ⟨.other .d010, p, true⟩

inductive DrugDestination where
  | d500

/-- 個別の負荷測定をD500へ振り分ける。薬価計算と振分けを分ける。 -/
def loadDrugRule : Rule LoadMeasurement (Option DrugDestination) :=
  ⟨"notice/D010/paragraph/1", notice "PDF369頁 D010(1)", fun m destination =>
    m.measured = m.administered → m.serumOrUrine → m.quantitative →
      destination = some .d500⟩

def DrugDestination.points : DrugDestination → ExaminationDrugsMaterials.Amount → Nat
  | .d500 => ExaminationDrugsMaterials.drugPoints

private def sampleDate : Date := ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩

private def sample : Context :=
  { performance := ⟨1, ⟨2, 3, sampleDate⟩, .aminoAcidPerKind, none, none, none, none⟩
    loadMeasurements := []
    aminoAcidKinds := some [1, 2, 3, 4] }

example : Eligible sample := by
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, sample, condition,
    aminoAcidHeading, congenitalHeading, congenitalNotice1, congenitalNotice2, loadingRule,
    tyrosineRule, btrRule, congenitalRule, organicAcidRule, veryLongChainRule, tandemMassRule,
    otherRule, Item.number]

example : Satisfies rules sample 1116 := by
  exact (legacy_iff ..).mpr ⟨rfl, by intro xs _ h; cases h; decide⟩

private def fiveKinds : Context :=
  { sample with
    aminoAcidKinds := some [1, 2, 3, 4, 5]
    performance := { sample.performance with item := .aminoAcidFiveOrMore } }

example : Satisfies rules fiveKinds 1074 := by
  exact (legacy_iff ..).mpr ⟨rfl, by intro xs _ h; cases h; decide⟩

example : ¬ SatisfiableAt rules { fiveKinds with performance := sample.performance } := by
  rintro ⟨p, hp⟩
  have charged := ((legacy_iff _ p).mp hp).1
  change none = some (SpecimenTests.ItemResult.charged p 0) at charged
  cases charged

end Sanri.MedicalFee.D010
