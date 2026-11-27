import Sanri.SpecimenJudgment
import Sanri.History

namespace Sanri.MedicalFee.D022

open Sanri.Logic Sanri.History

inductive Method where
  | direct | indirect | mixedDrugResistance | other
  deriving DecidableEq

structure Context where
  performance : Performance Unit
  method : Method
  /-- 使用薬剤を成分ごとに識別した一覧。 -/
  agents : List Nat

def Context.quantity (c : Context) := c.agents.eraseDups.length

def points : Nat := 415

def rate : Rule Context Nat :=
  ⟨"primary/D022/heading",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
      "PDF189頁 D022", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun _ p => p = points⟩

def minimumDrugs : Rule Context Unit :=
  ⟨"primary/D022/note/unnumbered/1",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
      "PDF189頁 D022 注", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun c _ => 4 ≤ c.quantity⟩

private def condition (n : Nat) (p : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D022/paragraph/" ++ toString n,
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF388頁 D022(" ++ toString n ++ ")", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c _ => p c⟩

def methodRule : Rule Context Unit := condition 1 fun c => 4 ≤ c.quantity

def mixedMethodRule : Rule Context Unit :=
  condition 2 fun c => c.method = .mixedDrugResistance → 4 ≤ c.quantity

def InScope (c : Context) := Satisfies [minimumDrugs, methodRule, mixedMethodRule] c ()
def rates := [rate]

theorem legacy_iff (c : Context) (p : Nat) (h : InScope c) :
    Satisfies rates c p ↔
      SpecimenTests.assessOne { code := .d022, number := 1, quantity := c.quantity } =
        some (.charged p 0) := by
  have hq := (satisfies_cons _ _ _ _).mp h |>.1
  change 4 ≤ c.quantity at hq
  change Satisfies rates c p ↔
    (if !decide (4 ≤ c.quantity) then none else some (SpecimenTests.ItemResult.charged 415 0)) =
      some (.charged p 0)
  simp [rates, satisfies_cons, satisfies_nil, rate, points, hq, eq_comm]

theorem determines : DeterminesOn InScope rates := by
  intro c _
  simp [rates, satisfies_cons, satisfies_nil, rate, DeterminesAt, SatisfiableAt, UniqueAt]

def judgmentTest : SpecimenJudgment.Test :=
  { major := 22, number := 1, ordinaryCategory := .microbiological }

private def sample : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, (), none, none, none, none⟩
    method := .mixedDrugResistance
    agents := [1, 2, 3, 4] }

example : InScope sample ∧ Satisfies rates sample 415 := by
  have h : 4 ≤ sample.quantity := by decide
  simp [InScope, satisfies_cons, satisfies_nil, minimumDrugs, methodRule, mixedMethodRule,
    condition, h, rates, rate, points]

example : ¬ InScope { sample with agents := [1, 2, 3, 3] } := by
  intro h
  have hm := (satisfies_cons _ _ _ _).mp h |>.1
  change 4 ≤ 3 at hm
  omega

end Sanri.MedicalFee.D022
