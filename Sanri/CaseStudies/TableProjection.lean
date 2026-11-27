import Sanri.Logic

namespace Sanri.MedicalFee.CaseStudies.TableProjection

structure Pair (Item : Type) where
  left : Item
  right : Item
  unit : String
  direction : Nat
  special : Bool

def symmetric (unit : String) (special : Bool) (a b : Item) : Pair Item :=
  ⟨a, b, unit, 3, special⟩

def allPairs (unit : String) (special : Bool) : List Item → List (Pair Item)
  | [] => []
  | a :: rest => rest.map (symmetric unit special a) ++ allPairs unit special rest

/-- 二項目を共に採用することへの制約。時間軸と特例の適用は事例で固定する。 -/
def pairLimits (active : Pair Item → Prop) (picked : Item → Prop)
    (rows : List (Pair Item)) : Prop :=
  ∀ row ∈ rows, active row → picked row.left → picked row.right → False

def symmetricIn (unit : String) (ordinary : Prop) (row : Pair Item) : Prop :=
  row.unit = unit ∧ row.direction = 3 ∧ (row.special = true → ordinary)

theorem allPairs_iff (unit : String) (special : Bool) (active : Pair Item → Prop)
    (picked : Item → Prop) (items : List Item) (distinct : items.Nodup)
    (applies : ∀ a b, active (symmetric unit special a b)) :
    pairLimits active picked (allPairs unit special items) ↔
      ∀ a ∈ items, ∀ b ∈ items, picked a → picked b → a = b := by
  induction items with
  | nil => simp [allPairs, pairLimits]
  | cons a rest ih =>
    obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp distinct
    have splitRows :
        pairLimits active picked (allPairs unit special (a :: rest)) ↔
          (∀ b ∈ rest, picked a → picked b → False) ∧
          pairLimits active picked (allPairs unit special rest) := by
      simp only [allPairs, pairLimits, List.mem_append, List.mem_map]
      constructor
      · intro h
        exact ⟨fun b hb => h _ (Or.inl ⟨b, hb, rfl⟩) (applies _ _),
          fun row hr => h row (Or.inr hr)⟩
      · rintro ⟨head, tail⟩ row (⟨b, hb, rfl⟩ | hr)
        · exact fun _ => head b hb
        · exact tail row hr
    rw [splitRows, ih distinct]
    constructor
    · rintro ⟨head, tail⟩ x hx y hy px py
      rcases List.mem_cons.mp hx with ex | hx <;> rcases List.mem_cons.mp hy with ey | hy
      · exact ex.trans ey.symm
      · exact False.elim (head _ hy (ex ▸ px) py)
      · exact False.elim (head _ hx (ey ▸ py) px)
      · exact tail _ hx _ hy px py
    · intro h
      exact ⟨fun b hb pa pb => fresh ((h a (by simp) b (by simp [hb]) pa pb).symm ▸ hb),
        fun x hx y hy => h x (by simp [hx]) y (by simp [hy])⟩

structure Frequency (Item : Type) where
  item : Item
  unit : String
  limit : Nat
  special : Bool

/-- 履歴単位と特例の適用を固定した算定回数の制約。 -/
def frequencyLimits (unit : String) (ordinary : Prop) (count : Item → Nat)
    (rows : List (Frequency Item)) : Prop :=
  ∀ row ∈ rows, row.unit = unit → (row.special = true → ordinary) → count row.item ≤ row.limit

structure AgeAddition (Item : Type) where
  target : Item
  lower : Nat
  upper : Nat
  points : Nat

def AgeAddition.atAge (row : AgeAddition Item) (age : Nat) : Nat :=
  if row.lower ≤ age ∧ age < row.upper then row.points else 0

end Sanri.MedicalFee.CaseStudies.TableProjection
