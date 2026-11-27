import Sanri.History
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D006Chromosome

open Sanri.Logic Sanri.History

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF177頁 D006-5 " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF344頁 D006-5 " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

inductive Item where
  | fish | chorionic | other
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.fish, .chorionic, .other]

def Item.number : Item → Nat
  | .fish => 1
  | .chorionic => 2
  | .other => 3

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem modeled_number (i : Item) : 1 ≤ i.number ∧ i.number ≤ 3 := by cases i <;> decide

def Item.points : Item → Nat
  | .fish => 2477
  | .chorionic => 4465
  | .other => 2444

def bandingPoints : Nat := 386

inductive FishPurpose where
  | diffuseLargeBCellLymphomaDiagnosis | multipleMyelomaDiagnosis | other
  deriving DecidableEq

structure Context where
  site : Site
  item : Item
  fishUsed : Option Bool := none
  miscarriageChorionicTest : Option Bool := none
  bandingUsed : Option Bool := none
  facilityComplies : Option Bool := none
  facilityNotified : Option Bool := none
  priorSpontaneousMiscarriage : Option Bool := none
  miscarriageSurgery : Option Bool := none
  giemsaBanding : Option Bool := none
  fishPurpose : Option FishPurpose := none
  beforeConfirmedDiagnosis : Option Bool := none
  diagnosticPeriod : Option Period := none
  priorClaims : Option (ClaimHistory Item) := none

def priorFish (c : Context) (p : Period) : Option Nat :=
  c.priorClaims.bind fun h => count h ⟨c.site.patient, none, p⟩ (· == .fish)

def FishFrequency (c : Context) : Prop :=
  c.item = .fish →
    (c.fishPurpose = some .other ∧ priorFish c (Period.through c.site.date) = some 0) ∨
    ((c.fishPurpose = some .diffuseLargeBCellLymphomaDiagnosis ∨
      c.fishPurpose = some .multipleMyelomaDiagnosis) ∧
      c.beforeConfirmedDiagnosis = some true ∧
      ∃ p n, c.diagnosticPeriod = some p ∧ p.Contains c.site.date ∧
        priorFish c p = some n ∧ n < 3)

def ChorionicProcedure (c : Context) : Prop :=
  c.item = .chorionic → c.priorSpontaneousMiscarriage = some true ∧
    c.miscarriageSurgery = some true ∧ c.giemsaBanding = some true ∧ c.bandingUsed = some true

structure Result where
  base : Nat
  bandingCount : Nat

def Result.total (r : Result) : Nat := r.base + r.bandingCount * bandingPoints

def fishRule : Rule Context Result :=
  ⟨"primary/D006-5/item/1", primary "1", fun c r => c.item = .fish →
    c.fishUsed = some true ∧ c.miscarriageChorionicTest = some false ∧ r.base = 2477⟩

def chorionicRule : Rule Context Result :=
  ⟨"primary/D006-5/item/2", primary "2", fun c r => c.item = .chorionic →
    c.fishUsed = some false ∧ c.miscarriageChorionicTest = some true ∧ r.base = 4465⟩

def otherRule : Rule Context Result :=
  ⟨"primary/D006-5/item/3", primary "3", fun c r => c.item = .other →
    c.fishUsed = some false ∧ c.miscarriageChorionicTest = some false ∧ r.base = 2444⟩

def bandingRule : Rule Context Result :=
  ⟨"primary/D006-5/note/1", primary "注1", fun c r =>
    (c.bandingUsed = some true ∧ 0 < r.bandingCount) ∨
    (c.bandingUsed = some false ∧ r.bandingCount = 0)⟩

def facilityRule : Rule Context Result :=
  ⟨"primary/D006-5/note/2", primary "注2", fun c _ => c.item = .chorionic →
    c.facilityComplies = some true ∧ c.facilityNotified = some true⟩

/-- 所定点数に含まれる費用の独立した射影。個々の費用を点数に再加算しない。 -/
inductive IncludedCost where
  | film | developing | enlargedPrint

def costRule : Rule Context (IncludedCost → Prop) :=
  ⟨"notice/D006-5/paragraph/1", notice "(1)", fun _ included =>
    included .film ∧ included .developing ∧ included .enlargedPrint⟩

def bandingCountRule : Rule Context Result :=
  ⟨"notice/D006-5/paragraph/2", notice "(2)", fun _ r => r.bandingCount ≤ 1⟩

def frequencyRule : Rule Context Result :=
  ⟨"notice/D006-5/paragraph/3", notice "(3)", fun c _ => FishFrequency c⟩

def procedureRule : Rule Context Result :=
  ⟨"notice/D006-5/paragraph/4", notice "(4)", fun c _ => ChorionicProcedure c⟩

def rules := [fishRule, chorionicRule, otherRule, bandingRule, facilityRule, bandingCountRule,
  frequencyRule, procedureRule]

def Eligible (c : Context) : Prop :=
  (match c.item with
    | .fish => c.fishUsed = some true ∧ c.miscarriageChorionicTest = some false
    | .chorionic => c.fishUsed = some false ∧ c.miscarriageChorionicTest = some true
    | .other => c.fishUsed = some false ∧ c.miscarriageChorionicTest = some false) ∧
  (∃ b, c.bandingUsed = some b) ∧
  (c.item = .chorionic → c.facilityComplies = some true ∧ c.facilityNotified = some true) ∧
  FishFrequency c ∧ ChorionicProcedure c

def scheduled (c : Context) : Result :=
  ⟨c.item.points, if c.bandingUsed = some true then 1 else 0⟩

theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ Eligible c ∧ r = scheduled c := by
  obtain ⟨base, banding⟩ := r
  cases hi : c.item <;> cases hb : c.bandingUsed <;>
    simp [rules, satisfies_cons, satisfies_nil, fishRule, chorionicRule, otherRule, bandingRule,
      facilityRule, bandingCountRule, frequencyRule, procedureRule, Eligible, scheduled,
      hi, hb, Item.points] <;> rename_i value <;> cases value <;> simp_all <;> grind

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  exact ⟨⟨scheduled c, (satisfies_iff _ _).mpr ⟨h, rfl⟩⟩,
    fun a b ha hb => ((satisfies_iff _ _).mp ha).2.trans ((satisfies_iff _ _).mp hb).2.symm⟩

def PermitsPoints (c : Context) (p : Nat) : Prop :=
  ∃ r, Satisfies rules c r ∧ r.total = p

theorem permits_points_iff (c : Context) (p : Nat) :
    PermitsPoints c p ↔ Eligible c ∧ (scheduled c).total = p := by
  constructor
  · rintro ⟨r, hr, hp⟩
    obtain ⟨eligible, rfl⟩ := (satisfies_iff _ _).mp hr
    exact ⟨eligible, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨scheduled c, (satisfies_iff _ _).mpr ⟨h, rfl⟩, hp⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 5, number := i.number, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

private def exampleContext : Context :=
  { site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, item := .chorionic
    fishUsed := some false, miscarriageChorionicTest := some true, bandingUsed := some true
    facilityComplies := some true, facilityNotified := some true
    priorSpontaneousMiscarriage := some true, miscarriageSurgery := some true
    giemsaBanding := some true }

example : Satisfies rules exampleContext ⟨4465, 1⟩ :=
  (satisfies_iff _ _).mpr ⟨by
    simp [Eligible, exampleContext, FishFrequency, ChorionicProcedure], rfl⟩

example : ¬ SatisfiableAt rules { exampleContext with facilityNotified := none } := by
  rintro ⟨r, hr⟩
  have h := (satisfies_iff _ _).mp hr
  simp [Eligible, exampleContext] at h

example : ¬ SatisfiableAt rules { exampleContext with priorSpontaneousMiscarriage := some false } := by
  rintro ⟨r, hr⟩
  have h := (satisfies_iff _ _).mp hr
  simp [Eligible, exampleContext, ChorionicProcedure] at h

end Sanri.MedicalFee.D006Chromosome
