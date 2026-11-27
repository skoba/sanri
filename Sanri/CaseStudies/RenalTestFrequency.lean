import Sanri.D001

namespace Sanri.MedicalFee.CaseStudies.RenalTestFrequency

open Sanri.Logic

/-- D001(3)の三種類について、適格性と同じ患者・期間を確認した後の算定件数。 -/
structure Counts where
  first : Nat
  second : Nat
  third : Nat

def sharedLimit : Rule Unit Counts :=
  ⟨"notice/D001/paragraph/3",
    ⟨.notification, "保医発0305第6号別添1", "2026-10-07訂正後",
      "PDF331頁 D001(3)の共有枠としての読み", .checkedAgainstSource, none⟩,
    fun _ c => c.first + c.second + c.third ≤ 1⟩

def separateLimits : Rule Unit Counts :=
  ⟨"table/frequency/D001",
    ⟨.electronicTable, "電子点数表05", "2026-10-13公開版",
      "D001(3)に対応する三種類の各回数欄", .checkedAgainstSource, none⟩,
    fun _ c => c.first ≤ 1 ∧ c.second ≤ 1 ∧ c.third ≤ 1⟩

/-- 同じ三月枠へ射影した件数では、共有枠を満たす内訳は各コードの上限も満たす。
同時背反を避けて異なる日に行う場合にも、各コードの回数欄だけでは共有枠を表せない。 -/
theorem shared_refines_separate :
    RefinesOn (fun _ => True) [sharedLimit] [separateLimits] := by
  intro _ _ c h
  simp only [satisfies_cons, satisfies_nil, and_true] at h ⊢
  change c.first + c.second + c.third ≤ 1 at h
  change c.first ≤ 1 ∧ c.second ≤ 1 ∧ c.third ≤ 1
  omega

example : Satisfies [sharedLimit] () ⟨0, 1, 0⟩ := by
  simp [satisfies_cons, satisfies_nil, sharedLimit]

example : DisagreesAt [sharedLimit] [separateLimits] () := by
  refine ⟨⟨1, 1, 0⟩, Or.inr ⟨?_, ?_⟩⟩
  · simp [satisfies_cons, satisfies_nil, separateLimits]
  · simp [satisfies_cons, satisfies_nil, sharedLimit]

example : ¬ separateLimits.holds () ⟨0, 0, 2⟩ := by
  simp [separateLimits]

end Sanri.MedicalFee.CaseStudies.RenalTestFrequency
