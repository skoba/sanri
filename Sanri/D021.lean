import Sanri.SpecimenJudgment
import Sanri.History

namespace Sanri.MedicalFee.D021

open Sanri.Logic Sanri.History

structure Context where
  performance : Performance Unit
  /-- 当該一連で確認した唯一の算定候補。 -/
  selected : Option (List (Performance Unit)) := none

def OneInSeries (c : Context) : Prop :=
  c.performance.sameSeries c.performance = some true ∧ c.selected = some [c.performance]

def points : Nat := 376

def rate : Rule Context Nat :=
  ⟨"primary/D021/heading",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
      "PDF189頁 D021", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun c p => OneInSeries c ∧ p = points⟩

def indication : Rule Context Unit :=
  ⟨"notice/D021/paragraph/unnumbered",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF388頁 D021", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c _ => OneInSeries c⟩

def InScope (c : Context) := indication.holds c ()
def rates := [rate]

theorem legacy_iff (c : Context) (p : Nat) (h : InScope c) :
    Satisfies rates c p ↔ SpecimenTests.assessOne { code := .d021, number := 1 } =
      some (.charged p 0) := by
  change Satisfies rates c p ↔ some (SpecimenTests.ItemResult.charged 376 0) = some (.charged p 0)
  have hs : OneInSeries c := h
  simp [rates, satisfies_cons, satisfies_nil, rate, points, hs, eq_comm]

theorem determines : DeterminesOn InScope rates := by
  intro c h
  have hs : OneInSeries c := h
  simp [rates, satisfies_cons, satisfies_nil, rate, hs, DeterminesAt, SatisfiableAt, UniqueAt]

def judgmentTest : SpecimenJudgment.Test :=
  { major := 21, number := 1, ordinaryCategory := .microbiological }

private def performed : Performance Unit :=
  ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, (), none, none, some 1, none⟩

private def sample : Context := ⟨performed, some [performed]⟩

example : InScope sample ∧ Satisfies rates sample 376 := by
  have hs : OneInSeries sample := ⟨rfl, rfl⟩
  simp [InScope, indication, rates, satisfies_cons, satisfies_nil, rate, points, hs]

example : ¬ InScope { sample with selected := none } := by
  simp [InScope, indication, OneInSeries]

end Sanri.MedicalFee.D021
