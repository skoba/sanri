import Sanri.SpecimenJudgment
import Sanri.History

namespace Sanri.MedicalFee.D019Yeast

open Sanri.Logic Sanri.History

inductive Organism where
  | candida | cryptococcus | other
  deriving DecidableEq

structure Context where
  performance : Performance Unit
  deepMycosis : Option Bool := none
  isolatedCausativeOrganism : Option Organism := none

def points : Nat := 165

def rate : Rule Context Nat :=
  ⟨"primary/D019-2/heading",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
      "PDF189頁 D019-2", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun _ p => p = points⟩

def indication : Rule Context Unit :=
  ⟨"notice/D019-2/paragraph/unnumbered",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF387頁 D019-2", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c _ => c.deepMycosis = some true ∧
      c.isolatedCausativeOrganism ∈ [some .candida, some .cryptococcus]⟩

def InScope (c : Context) := indication.holds c ()
def rates := [rate]

theorem legacy_iff (c : Context) (p : Nat) :
    Satisfies rates c p ↔ SpecimenTests.assessOne { code := .d019_2, number := 1 } =
      some (.charged p 0) := by
  change Satisfies rates c p ↔ some (SpecimenTests.ItemResult.charged 165 0) = some (.charged p 0)
  simp [rates, satisfies_cons, satisfies_nil, rate, points, eq_comm]

theorem determines : DeterminesOn InScope rates := by
  intro c _
  simp [rates, satisfies_cons, satisfies_nil, rate, DeterminesAt, SatisfiableAt, UniqueAt]

def judgmentTest : SpecimenJudgment.Test :=
  { major := 19, suffix := 2, number := 1, ordinaryCategory := .microbiological }

private def sample : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, (), none, none, none, none⟩
    deepMycosis := some true
    isolatedCausativeOrganism := some .candida }

example : InScope sample ∧ Satisfies rates sample 165 := by
  simp [InScope, sample, indication, rates, satisfies_cons, satisfies_nil, rate, points]

example : ¬ InScope { sample with isolatedCausativeOrganism := none } := by
  simp [InScope, sample, indication]

end Sanri.MedicalFee.D019Yeast
