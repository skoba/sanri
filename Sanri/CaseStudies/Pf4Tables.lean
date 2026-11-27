import Sanri.D011
import Sanri.CaseStudies.TableProjection

namespace Sanri.MedicalFee.CaseStudies.Pf4Tables

open Sanri.Logic Sanri.History TableProjection

def observation : List (Pair D011.Item) :=
  [symmetric "simultaneous" false .pf4IgG .pf4IgGmA]

structure Context where
  series : List (Performance D011.Item)
  simultaneous : Bool

def ThreeMeasured (c : Context) : Prop :=
  (∃ a ∈ c.series, a.item = .pf4IgG) ∧
  (∃ a ∈ c.series, a.item = .pf4IgGmA) ∧
  (∃ a ∈ c.series, a.item = .pf4Qualitative)

def ConfirmedSeries (c : Context) : Prop :=
  (c.series.map (·.id)).Nodup ∧
  ∀ p ∈ c.series, p.item.isPf4 = true ∧
    ∀ q ∈ c.series, p.sameSeries q = some true

def NoticeSelection (c : Context) (chosen : List (Performance D011.Item)) : Prop :=
  ∃ main : Nat, ∀ p ∈ chosen, ThreeMeasured c → main = p.id

/-- 確認済みの一連と採否について、D011(4)ウの三方式条件を取り出す。 -/
theorem notice_selection_iff (c : Context) (chosen : List (Performance D011.Item))
    (scope : ConfirmedSeries c) (within : ∀ p ∈ chosen, p ∈ c.series) :
    (∃ main : Nat, ∀ p ∈ chosen,
      D011.pf4Choice.holds { performance := p, pf4Series := some c.series, mainPf4 := some main } ()) ↔
    NoticeSelection c chosen := by
  constructor
  · rintro ⟨main, rule⟩
    refine ⟨main, ?_⟩
    intro p hp ⟨a, b, d⟩
    have valid := rule p hp
    change p.item.isPf4 = true → _ at valid
    obtain ⟨xs, equal, _, _, _, choice⟩ := valid (scope.2 p (within p hp)).1
    have same : xs = c.series := by simpa using equal.symm
    subst xs
    exact Option.some.inj (choice a b d)
  · rintro ⟨main, choice⟩
    refine ⟨main, ?_⟩
    intro p hp
    change p.item.isPf4 = true → _
    exact fun _ => ⟨c.series, rfl, within p hp, scope.1,
      fun q hq => ⟨(scope.2 q hq).1, (scope.2 p (within p hp)).2 q hq⟩,
      fun a b d => congrArg some (choice p hp ⟨a, b, d⟩)⟩

def table : Rule Context (List (Performance D011.Item)) :=
  ⟨"table/specimen/pf4/observed-pair",
    ⟨.electronicTable, "電子点数表", "2026-10-13公開版", "同時背反", .transcribed, none⟩,
    fun c chosen => pairLimits (fun pair => symmetricIn "simultaneous" False pair ∧ c.simultaneous = true)
      (fun i => ∃ p ∈ chosen, p.item = i) observation⟩

private def site : Site := ⟨1, 1, ⟨⟨2026, 10⟩, ⟨22, by decide⟩⟩⟩

private def igg : Performance D011.Item := ⟨1, site, .pf4IgG, none, none, some 1, some 1⟩
private def mixed : Performance D011.Item := ⟨2, site, .pf4IgGmA, none, none, some 1, some 1⟩
private def qualitative : Performance D011.Item := ⟨3, site, .pf4Qualitative, none, none, some 1, some 1⟩

private def two : Context := ⟨[igg, mixed], true⟩
private def three : Context := ⟨[igg, mixed, qualitative], true⟩

/-- 二方式だけの同時実施では、通知の三方式条件から表の二件背反は導けない。 -/
theorem notice_does_not_imply_pair :
    ConfirmedSeries two ∧
      NoticeSelection two [igg, mixed] ∧ ¬ table.holds two [igg, mixed] := by
  refine ⟨?_, ⟨1, ?_⟩, ?_⟩
  · simp [ConfirmedSeries, two, igg, mixed, Performance.sameSeries, Performance.sameGroup]
    decide
  · simp [ThreeMeasured, two, igg, mixed]
  · simp [table, pairLimits, symmetricIn, symmetric, observation, two, igg, mixed]

/-- 三方式を同時に実施すると、表の一対だけでは通知の主検査制約を含意しない。 -/
theorem pair_does_not_imply_notice :
    ConfirmedSeries three ∧
      table.holds three [igg, qualitative] ∧ ¬ NoticeSelection three [igg, qualitative] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ConfirmedSeries, three, igg, mixed, qualitative, Performance.sameSeries, Performance.sameGroup]
    decide
  · simp [table, pairLimits, symmetricIn, symmetric, observation, three, igg, qualitative]
  · intro h
    obtain ⟨main, choice⟩ := h
    have measured : ThreeMeasured three := by simp [ThreeMeasured, three, igg, mixed, qualitative]
    have first := choice igg (by simp) measured
    have last := choice qualitative (by simp) measured
    simp [igg, qualitative, first] at last

end Sanri.MedicalFee.CaseStudies.Pf4Tables
