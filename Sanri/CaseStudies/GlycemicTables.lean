import Sanri.GlycemicTests
import Sanri.CaseStudies.TableProjection

namespace Sanri.MedicalFee.CaseStudies.GlycemicTables

open Sanri.Logic GlycemicTests TableProjection

inductive Item where
  | hemoglobinA1c | glycatedAlbumin | anhydroglucitol
  deriving Repr

def frequencyObservation : List (Frequency Item) :=
  [.hemoglobinA1c, .glycatedAlbumin, .anhydroglucitol].map fun i => ⟨i, "month", 1, true⟩

def pairObservation : List (Pair Item) :=
  allPairs "month" true [.hemoglobinA1c, .glycatedAlbumin, .anhydroglucitol]

/-- 各コードの算定件数。同一患者・同一機関の一暦月へ射影する。 -/
structure Counts where
  a1c : Nat
  albumin : Nat
  anhydroglucitol : Nat

def Counts.total (c : Counts) : Nat := c.a1c + c.albumin + c.anhydroglucitol

def Counts.forItem (c : Counts) : Item → Nat
  | .hemoglobinA1c => c.a1c
  | .glycatedAlbumin => c.albumin
  | .anhydroglucitol => c.anhydroglucitol

structure Context where
  month : Month
  charged : List Performance

/-- 適用する方法や主たる実施の選択は別に確認する。二件以上実施した月が対象。 -/
def Ordinary (c : Context) : Prop :=
  c.month.exception = some .none ∧ 2 ≤ c.month.performed.length

def countByItem : List Performance → Counts
  | [] => ⟨0, 0, 0⟩
  | row :: rows =>
    let c := countByItem rows
    match row.item with
    | .a1c => { c with a1c := c.a1c + 1 }
    | .glycatedAlbumin _ => { c with albumin := c.albumin + 1 }
    | .anhydroglucitol => { c with anhydroglucitol := c.anhydroglucitol + 1 }

private theorem count_total (rows : List Performance) : (countByItem rows).total = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨id, item⟩
    cases item <;> simp [countByItem, Counts.total, List.length_cons] at * <;> omega

def sameClaims : Rule Context Counts :=
  ⟨"glycemic/count-projection",
   ⟨.manualInterpretation, "算定件数の射影", "", "実施を検査種類別に集計", .unchecked, none⟩,
   fun c r => r = countByItem c.charged⟩

def noticeRules : List (Rule Context Counts) :=
  sameClaims :: ordinaryRules.map fun rule =>
    ⟨rule.id, rule.source, fun c _ => rule.holds c.month (c.charged.map Performance.id)⟩

private def table (location : String) : SourceRef :=
  ⟨.electronicTable, "医科電子点数表", "2026-10-13公開版", location,
    .checkedAgainstSource, none⟩

/-- 特例に該当しないと確認した場合に適用する表の制約。 -/
def frequency : Rule Context Counts :=
  ⟨"glycemic/frequency", table "05 算定回数・糖代謝3検査",
    fun _ c => frequencyLimits "month" True c.forItem frequencyObservation⟩

def exclusion : Rule Context Counts :=
  ⟨"glycemic/monthly-exclusion", table "03-2 同一月内・糖代謝3検査",
    fun _ c => pairLimits (symmetricIn "month" True)
      (fun i => c.forItem i ≠ 0) pairObservation⟩

private theorem table_iff (c : Context) (r : Counts) :
    Satisfies [frequency, exclusion] c r ↔ r.total ≤ 1 := by
  simp [satisfies_cons, satisfies_nil, frequency, exclusion, Counts.total,
    frequencyLimits, frequencyObservation, pairLimits, pairObservation, allPairs, symmetricIn,
    symmetric, Counts.forItem]
  omega

private theorem notice_iff (c : Context) (h : Ordinary c) (r : Counts) :
    Satisfies noticeRules c r ↔ r = countByItem c.charged ∧ c.charged.length ≤ 1 := by
  simp [noticeRules, sameClaims, ordinaryRules, satisfies_cons, satisfies_nil, principalOnly, h.1, h.2]

/-- 同じ算定案の集計を与えたときの上限の同値性。 -/
theorem ordinary_equivalent :
    EquivalentOn Ordinary noticeRules
      [sameClaims, frequency, exclusion] := by
  apply equivalentOn_iff.mpr
  intro c h r
  rw [notice_iff c h r, satisfies_cons, table_iff]
  change (_ ∧ _) ↔ r = countByItem c.charged ∧ _
  constructor <;> rintro ⟨rfl, bound⟩ <;> exact ⟨rfl, by simpa [count_total] using bound⟩

private def ordinaryExample : Context :=
  ⟨⟨[⟨1, .a1c⟩, ⟨2, .anhydroglucitol⟩], some .none⟩, [⟨1, .a1c⟩]⟩

example : Ordinary ordinaryExample ∧ Satisfies [sameClaims, frequency, exclusion] ordinaryExample ⟨1, 0, 0⟩ := by
  simp [ordinaryExample, Ordinary, satisfies_cons, satisfies_nil, sameClaims, countByItem, frequency, exclusion,
    frequencyLimits, frequencyObservation, pairLimits, pairObservation, allPairs, symmetricIn, symmetric, Counts.forItem]

private def clinicalMonth : Month :=
  ⟨[⟨1, .a1c⟩, ⟨2, .anhydroglucitol⟩], some .clinical⟩

/-- 一般例外で許される追加を、表の無条件適用は除外する。 -/
theorem clinical_requires_exception :
    Selected (some clinicalMonth) ⟨1, some 2⟩ ⟨1, .a1c⟩ (some ⟨2, .anhydroglucitol⟩) ∧
      ¬ Satisfies [frequency, exclusion] ⟨clinicalMonth, clinicalMonth.performed⟩ ⟨1, 0, 1⟩ := by
  exact ⟨(selected_iff _ _ _ _).mpr rfl, fun h => by
    have bound := (table_iff _ _).mp h
    simp [Counts.total] at bound⟩

/-- 異種の追加例ではコード別の回数欄を満たし、同月背反に特例が必要となる。 -/
theorem clinical_pair_exception :
    frequency.holds ⟨clinicalMonth, clinicalMonth.performed⟩ ⟨1, 0, 1⟩ ∧
      ¬ exclusion.holds ⟨clinicalMonth, clinicalMonth.performed⟩ ⟨1, 0, 1⟩ := by
  simp [frequency, exclusion, frequencyLimits, frequencyObservation, pairLimits,
    pairObservation, allPairs, symmetricIn, symmetric, Counts.forItem]

/-- 同一コードを二回算定する例外は、背反がなくても回数行の特例が必要。 -/
theorem clozapine_requires_frequency_exception :
    let month : Month := ⟨[⟨1, .a1c⟩, ⟨2, .a1c⟩], some .clozapine⟩
    Selected (some month) ⟨1, some 2⟩ ⟨1, .a1c⟩ (some ⟨2, .a1c⟩) ∧
      exclusion.holds ⟨month, month.performed⟩ ⟨2, 0, 0⟩ ∧
      ¬ frequency.holds ⟨month, month.performed⟩ ⟨2, 0, 0⟩ := by
  exact ⟨(selected_iff _ _ _ _).mpr rfl, by simp [exclusion, pairLimits, pairObservation, allPairs, symmetricIn, symmetric, Counts.forItem], by simp [frequency, frequencyLimits, frequencyObservation, Counts.forItem]⟩

end Sanri.MedicalFee.CaseStudies.GlycemicTables
