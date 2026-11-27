import Sanri.History
import Sanri.Logic
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D004Methylation

open Sanri.Logic Sanri.History

inductive Item where
  | dnaMethylation
  deriving DecidableEq, Repr

/-- 告示の区分見出しに点数があり、項番はない。 -/
def Item.number : Item → Option Nat
  | .dnaMethylation => none

theorem no_number (item : Item) : item.number = none := by cases item <;> rfl

def points : Nat := 2500

structure Context where
  site : Site
  rasWildType : Option Bool := none
  unresectableForCure : Option Bool := none
  advancedOrRecurrentColorectalCancer : Option Bool := none
  approvedTreatmentSelectionReagent : Option Bool := none
  realTimePCR : Option Bool := none
  methylationDetectedInTumorExtract : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none

def priorCount (c : Context) : Option Nat :=
  c.priorClaims.bind fun history =>
    count history ⟨c.site.patient, none, Period.through c.site.date⟩ (· == .dnaMethylation)

def Eligible (c : Context) : Prop :=
  c.rasWildType = some true ∧ c.unresectableForCure = some true ∧
  c.advancedOrRecurrentColorectalCancer = some true ∧
  c.approvedTreatmentSelectionReagent = some true ∧ c.realTimePCR = some true ∧
  c.methylationDetectedInTumorExtract = some true ∧ priorCount c = some 0

def headingRule : Rule Context Nat :=
  ⟨"primary/D004-3/heading",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
      "PDF175頁 D004-3", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun _ p => p = points⟩

def noticeRule : Rule Context Nat :=
  ⟨"notice/D004-3/paragraph/unnumbered",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF338頁 D004-3", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c _ => Eligible c⟩

def rules : List (Rule Context Nat) := [headingRule, noticeRule]

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  simp [rules, satisfies_cons, satisfies_nil, headingRule, noticeRule]

theorem determines : DeterminesOn Eligible rules := by
  intro c eligible
  refine ⟨⟨points, (satisfies_iff _ _).mpr ⟨rfl, eligible⟩⟩, ?_⟩
  intro a b ha hb
  exact ((satisfies_iff _ _).mp ha).1.trans ((satisfies_iff _ _).mp hb).1.symm

def judgmentTest (ordinary : SpecimenJudgment.Category) : SpecimenJudgment.Test :=
  { major := 4, suffix := 3, ordinaryCategory := ordinary }

theorem judgment_category (ordinary : SpecimenJudgment.Category) :
    SpecimenJudgment.categoryFor (judgmentTest ordinary) = some .geneticChromosomal := rfl

private def exampleSite : Site :=
  ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def eligibleExample : Context :=
  { site := exampleSite
    rasWildType := some true
    unresectableForCure := some true
    advancedOrRecurrentColorectalCancer := some true
    approvedTreatmentSelectionReagent := some true
    realTimePCR := some true
    methylationDetectedInTumorExtract := some true
    priorClaims := some {
      coverage := ⟨1, none, Period.through exampleSite.date⟩
      entries := []
      distinctIds := List.nodup_nil } }

example : Satisfies rules eligibleExample 2500 :=
  (satisfies_iff _ _).mpr ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

example : ¬ SatisfiableAt rules { eligibleExample with rasWildType := some false } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ p).mp hp).2.1
  contradiction

example : ¬ SatisfiableAt rules { eligibleExample with priorClaims := none } := by
  rintro ⟨p, hp⟩
  have h := ((satisfies_iff _ p).mp hp).2.2.2.2.2.2.2
  contradiction

end Sanri.MedicalFee.D004Methylation
