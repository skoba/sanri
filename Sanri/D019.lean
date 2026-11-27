import Sanri.SpecimenJudgment
import Sanri.History

namespace Sanri.MedicalFee.D019

open Sanri.Logic Sanri.History

inductive Item where
  | one | two | threeOrMore | resistance | combination
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.one, .two, .threeOrMore, .resistance, .combination]

def Item.number : Item → Nat
  | .one => 1
  | .two => 2
  | .threeOrMore => 3
  | .resistance => 4
  | .combination => 5

def Item.points : Item → Nat
  | .one => 185
  | .two => 240
  | .threeOrMore => 310
  | .resistance => 50
  | .combination => 150

def Item.MatchesCount (i : Item) (n : Nat) : Prop :=
  match i with
  | .one => n = 1
  | .two => n = 2
  | .threeOrMore => 3 ≤ n
  | .resistance | .combination => True

structure Context where
  performance : Performance Item
  speciesCount : Nat
  treatmentHistory : Option (ClaimHistory (Nat × Item)) := none
  treatmentScope : Option Scope := none
  routineAntimicrobialNonSusceptibility : Option Bool := none
  needsRepeatForMultidrugResistantTreatment : Option Bool := none
  testPerformedOnDetectedOrganism : Option Bool := none
  checkedResistanceFactors : Option Bool := none
  detectedMultidrugResistantGramNegativeRod : Option Bool := none
  checkerboardCombinationTest : Option Bool := none

def prior (c : Context) : Option Nat := do
  let history ← c.treatmentHistory
  let scope ← c.treatmentScope
  let series ← c.performance.series
  if scope.institution = some c.performance.site.institution ∧
      scope.Includes c.performance.site = true then
    count history scope (fun item => item.1 == series)
  else none

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF189頁 D019 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def condition (n : Nat) (p : Context → Prop) : Rule Context Unit :=
  let location := "D019(" ++ toString n ++ ")"
  ⟨"notice/D019/paragraph/" ++ toString n,
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF387頁 " ++ location, .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c _ => p c⟩

def rate (i : Item) : Rule Context Nat :=
  ⟨"primary/D019/item/" ++ toString i.number, primary (toString i.number), fun c p =>
    c.performance.item = i → i.MatchesCount c.speciesCount ∧ p = i.points⟩

def treatmentLimit : Rule Context Unit :=
  condition 1 fun c => prior c = some 0 ∨
    (c.routineAntimicrobialNonSusceptibility = some true ∧
      c.needsRepeatForMultidrugResistantTreatment = some true)

def performed : Rule Context Unit :=
  condition 2 fun c => c.testPerformedOnDetectedOrganism = some true

def resistance : Rule Context Unit :=
  condition 3 fun c => c.performance.item = .resistance → c.checkedResistanceFactors = some true

def combination : Rule Context Unit :=
  condition 4 fun c => c.performance.item = .combination →
    c.detectedMultidrugResistantGramNegativeRod = some true ∧
    c.checkerboardCombinationTest = some true

def eligibilityRules := [treatmentLimit, performed, resistance, combination]
def InScope (c : Context) : Prop :=
  c.performance.item.MatchesCount c.speciesCount ∧ Satisfies eligibilityRules c ()

def rates : List (Rule Context Nat) := ledgerItems.map rate

theorem rates_iff (c : Context) (p : Nat) :
    Satisfies rates c p ↔
      c.performance.item.MatchesCount c.speciesCount ∧ p = c.performance.item.points := by
  cases h : c.performance.item <;>
    simp [rates, ledgerItems, satisfies_cons, satisfies_nil, rate, h, Item.points]

theorem determines : DeterminesOn InScope rates := by
  intro c h
  exact ⟨⟨_, (rates_iff _ _).mpr ⟨h.1, rfl⟩⟩, fun a b ha hb =>
    ((rates_iff _ _).mp ha).2.trans ((rates_iff _ _).mp hb).2.symm⟩

def legacyRequest (c : Context) : SpecimenTests.Request :=
  { code := .d019, number := c.performance.item.number, quantity := c.speciesCount }

theorem legacy_eval (c : Context) (h : c.performance.item.MatchesCount c.speciesCount) :
    SpecimenTests.assessOne (legacyRequest c) = some (.charged c.performance.item.points 0) := by
  unfold legacyRequest
  cases hi : c.performance.item <;> simp only [hi, Item.MatchesCount] at h <;> try rfl
  · rw [h]
    rfl
  · rw [h]
    rfl
  · change (if !decide (3 ≤ c.speciesCount) then none else some (SpecimenTests.ItemResult.charged 310 0)) = _
    simp [h, Item.points]

theorem legacy_iff (c : Context) (p : Nat) (h : InScope c) :
    Satisfies rates c p ↔ SpecimenTests.assessOne (legacyRequest c) = some (.charged p 0) := by
  rw [rates_iff, legacy_eval c h.1]
  simp [h.1, @eq_comm Nat c.performance.item.points p]

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 19, number := i.number, ordinaryCategory := .microbiological }

private def sample : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩,
      .threeOrMore, none, some 1, some 1, none⟩
    speciesCount := 3, routineAntimicrobialNonSusceptibility := some true
    needsRepeatForMultidrugResistantTreatment := some true
    testPerformedOnDetectedOrganism := some true }

example : InScope sample ∧ Satisfies rates sample 310 := by
  constructor
  · simp [InScope, sample, Item.MatchesCount, eligibilityRules, treatmentLimit, performed,
      resistance, combination, condition, satisfies_cons, satisfies_nil]
  · exact (rates_iff _ _).mpr ⟨by change 3 ≤ 3; omega, rfl⟩

example : ¬ InScope { sample with speciesCount := 2 } := by
  intro h
  have hc := h.1
  change 3 ≤ 2 at hc
  omega

end Sanri.MedicalFee.D019
