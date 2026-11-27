import Sanri.D004Tumor

namespace Sanri.MedicalFee.D006Leukemia

open Sanri.Logic Sanri.History

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF177頁 " ++ location, .checkedAgainstSource,
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

namespace D006_2

inductive Item where
  | hematopoieticTumorGene
  deriving DecidableEq, Repr

def Item.number : Item → Option Nat
  | .hematopoieticTumorGene => none

theorem no_number (item : Item) : item.number = none := by cases item <;> rfl

inductive Method where
  | pcr | lcr | southernBlot | other
  deriving DecidableEq, Repr

structure Context where
  site : Site
  method : Option Method := none
  facilityComplies : Option Bool := none
  managementII_III_IVNotified : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none
  monthlySelection : Option D004Tumor.MonthlySelection := none

def priorCount (c : Context) : Option Nat :=
  c.priorClaims.bind fun h =>
    count h ⟨c.site.patient, none, Period.month c.site.date.month⟩ (· == .hematopoieticTumorGene)

def FacilityEligible (c : Context) : Prop :=
  c.facilityComplies = some true ∧ c.managementII_III_IVNotified = some true

def MethodAndFrequency (c : Context) : Prop :=
  (∃ m ∈ [Method.pcr, .lcr, .southernBlot], c.method = some m) ∧ priorCount c = some 0

def Principal (c : Context) : Prop :=
  ∃ s, c.monthlySelection = some s ∧
    s.Allows c.site [.d004_2_1, .d006_6, .d006_14, .d006_16]

def Eligible (c : Context) : Prop := FacilityEligible c ∧ MethodAndFrequency c ∧ Principal c

def points : Nat := 2100

def headingRule : Rule Context Nat :=
  ⟨"primary/D006-2/heading", primary "D006-2", fun _ p => p = points⟩

def facilityRule : Rule Context Nat :=
  ⟨"primary/D006-2/note/unnumbered/1", primary "D006-2 注", fun c _ => FacilityEligible c⟩

def methodRule : Rule Context Nat :=
  ⟨"notice/D006-2/paragraph/1", notice "PDF340頁 D006-2(1)", fun c _ => MethodAndFrequency c⟩

def combinationRule : Rule Context Nat :=
  ⟨"notice/D006-2/paragraph/2", notice "PDF340頁 D006-2(2)", fun c _ => Principal c⟩

def rules := [headingRule, facilityRule, methodRule, combinationRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, facilityRule, methodRule, combinationRule, Eligible]

theorem determines : DeterminesOn Eligible rules :=
  determines_fixed rules Eligible points satisfies_iff

def judgmentTest (ordinary : SpecimenJudgment.Category) : SpecimenJudgment.Test :=
  { major := 6, suffix := 2, ordinaryCategory := ordinary }

theorem judgment_category (ordinary : SpecimenJudgment.Category) :
    SpecimenJudgment.categoryFor (judgmentTest ordinary) = some .geneticChromosomal := rfl

private def exampleSite : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def eligibleExample : Context :=
  { site := exampleSite, method := some .lcr, facilityComplies := some true
    managementII_III_IVNotified := some true
    priorClaims := some { coverage := ⟨1, none, Period.month exampleSite.date.month⟩
                          entries := [], distinctIds := List.nodup_nil }
    monthlySelection := some {
      scopeInstitution := some 1
      survey := ⟨exampleSite.monthScope, []⟩
      principal := fun _ _ => none } }

example : Satisfies rules eligibleExample 2100 :=
  (satisfies_iff _ _).mpr ⟨rfl, ⟨⟨rfl, rfl⟩, ⟨⟨.lcr, by simp, rfl⟩, rfl⟩,
    ⟨_, rfl, [], rfl, .inr rfl, by simp⟩⟩⟩

example : ¬ SatisfiableAt rules { eligibleExample with facilityComplies := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.1.1
  contradiction

example : ¬ SatisfiableAt rules { eligibleExample with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ _).mp hp).2.2.1.2
  contradiction

end D006_2

namespace D006_3

inductive Item where
  | majorInternational | majorQuantitative | minor
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .majorInternational => 1
  | .majorQuantitative => 2
  | .minor => 3

def ledgerItems : List Item := [.majorInternational, .majorQuantitative, .minor]

example : ledgerItems.map Item.number = [1, 2, 3] := by decide

inductive Purpose where
  | diagnosticAid | treatmentMonitoring
  deriving DecidableEq, Repr

inductive Disease where
  | chronicMyeloidLeukemia | philadelphiaPositiveAll | other
  deriving DecidableEq, Repr

structure Context where
  item : Item
  purpose : Option Purpose := none
  disease : Option Disease := none
  realTimeRtPcr : Option Bool := none

def points : Nat := 2520

private def baseRule (i : Item) : Rule Context Nat :=
  ⟨"primary/D006-3/item/" ++ toString i.number, primary ("D006-3 項" ++ toString i.number),
    fun c p => c.item = i → p = points⟩

def majorInternationalRule : Rule Context Nat :=
  ⟨"notice/D006-3/paragraph/1", notice "PDF341頁 D006-3(1)", fun c _ =>
    c.item = .majorInternational →
      c.disease = some .chronicMyeloidLeukemia ∧ c.purpose.isSome = true ∧ c.realTimeRtPcr = some true⟩

def majorQuantitativeRule : Rule Context Nat :=
  ⟨"notice/D006-3/paragraph/2", notice "PDF341頁 D006-3(2)", fun c _ =>
    c.item = .majorQuantitative →
      c.disease = some .philadelphiaPositiveAll ∧ c.purpose.isSome = true ∧ c.realTimeRtPcr = some true⟩

def minorRule : Rule Context Nat :=
  ⟨"notice/D006-3/paragraph/3", notice "PDF341頁 D006-3(3)", fun c _ =>
    c.item = .minor →
      c.disease = some .philadelphiaPositiveAll ∧ c.purpose.isSome = true ∧ c.realTimeRtPcr = some true⟩

def Eligible (c : Context) : Prop :=
  majorInternationalRule.holds c points ∧ majorQuantitativeRule.holds c points ∧ minorRule.holds c points

def rules : List (Rule Context Nat) :=
  [baseRule .majorInternational, baseRule .majorQuantitative, baseRule .minor,
    majorInternationalRule, majorQuantitativeRule, minorRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  cases c with
  | mk item purpose disease method =>
    cases item <;> simp [rules, satisfies_cons, satisfies_nil, baseRule, Eligible,
      majorInternationalRule, majorQuantitativeRule, minorRule]

theorem determines : DeterminesOn Eligible rules :=
  determines_fixed rules Eligible points satisfies_iff

def judgmentTest (i : Item) (ordinary : SpecimenJudgment.Category) : SpecimenJudgment.Test :=
  { major := 6, suffix := 3, number := i.number, ordinaryCategory := ordinary }

theorem judgment_category (i : Item) (ordinary : SpecimenJudgment.Category) :
    SpecimenJudgment.categoryFor (judgmentTest i ordinary) = some .geneticChromosomal := rfl

private def eligibleExample : Context :=
  ⟨.minor, some .treatmentMonitoring, some .philadelphiaPositiveAll, some true⟩

example : Satisfies rules eligibleExample 2520 := by
  simp [satisfies_iff, points, Eligible, eligibleExample, majorInternationalRule, majorQuantitativeRule, minorRule]

example : ¬ SatisfiableAt rules { eligibleExample with disease := some .chronicMyeloidLeukemia } := by
  simp [SatisfiableAt, satisfies_iff, Eligible, eligibleExample,
    majorInternationalRule, majorQuantitativeRule, minorRule]

example : ¬ SatisfiableAt rules { eligibleExample with realTimeRtPcr := none } := by
  simp [SatisfiableAt, satisfies_iff, Eligible, eligibleExample,
    majorInternationalRule, majorQuantitativeRule, minorRule]

end D006_3

end Sanri.MedicalFee.D006Leukemia
