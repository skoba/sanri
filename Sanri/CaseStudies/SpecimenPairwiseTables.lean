import Sanri.SpecimenCrossDivision

namespace Sanri.MedicalFee.CaseStudies.SpecimenPairwiseTables

open Sanri.History Sanri.Logic SpecimenCrossDivision

/-- 各項目一実施について個別の適格性を外部で確認した三実施の比較入力。
実施ID・患者・機関は固定し、最後の実施の同時IDと検体IDを動かせる。 -/
structure Comparison where
  eligible : Bool
  lastSimultaneous : Option Nat
  lastSpecimen : Option Nat

def SimultaneousScope (c : Comparison) : Prop :=
  c.eligible = true ∧ c.lastSimultaneous = some 1

def SpecimenScope (c : Comparison) : Prop :=
  SimultaneousScope c ∧ c.lastSpecimen = some 1

/-- 三実施それぞれの採否。空の選択も許し、算定義務は比較しない。 -/
structure Selection where
  first : Bool
  second : Bool
  third : Bool

def AtMostOne (a b c : Bool) : Prop :=
  a.toNat + b.toNat + c.toNat ≤ 1

private def site : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def performances (c : Comparison) (a b d : Item) : List (Performance Item) :=
  [⟨1, site, a, none, some 1, none, some 1⟩,
   ⟨2, site, b, none, some 1, none, some 1⟩,
   ⟨3, site, d, none, c.lastSpecimen, none, c.lastSimultaneous⟩]

private def selected (s : Selection) : List Nat :=
  (if s.first then [1] else []) ++ (if s.second then [2] else []) ++
    (if s.third then [3] else [])

private def coagulationRows (c : Comparison) :=
  performances c D006.Item.tat .prothrombinFragment .fibrinMonomer

private def electrophoresisRows (c : Comparison) :=
  performances c D015.Item.wholeAntiserum .specificAntiserum .drugImmunofixation

/-- 採用した各実施について、既存の併施群への入力変換を通して通知制約を適用する。 -/
def coagulationNotice : Rule Comparison Selection :=
  ⟨D006.markerCombinationRule.id, D006.markerCombinationRule.source, fun c s =>
    let rows := coagulationRows c
    match coagulationMarkerGroup rows with
    | none => False
    | some group =>
      ∀ p ∈ rows, p.id ∈ selected s →
        D006.markerCombinationRule.holds
          (coagulationMarkerInput { performance := p } rows ⟨group, selected s⟩) ()⟩

/-- 採否を既存の同一検体群に渡し、採用した各実施に通知のイを適用する。 -/
def electrophoresisNotice : Rule Comparison Selection :=
  ⟨D015.electrophoresisChoice.id, D015.electrophoresisChoice.source, fun c s =>
    let rows := electrophoresisRows c
    match electrophoresisGroup (rows.headD { id := 0, site := site, item := .wholeAntiserum }) rows with
    | none => False
    | some group =>
      ∀ p ∈ rows, p.id ∈ selected s →
        D015.electrophoresisChoice.holds
          (plasmaProteinSelectionInput { performance := p } [⟨group, selected s⟩] rows) ()⟩

def tableSource : SourceRef :=
  ⟨.electronicTable, "電子点数表", "2026-10-13公開版",
    "同時背反テーブル・優先方向3・特例なし", .transcribed, none⟩

/-- 同時が確認された二実施について、優先方向3の特例なし行の採否を表す。 -/
private def symmetricPair (simultaneous : Option Bool) (a b : Bool) : Prop :=
  simultaneous = some true → (a && b) = false

def coagulationTable : Rule Comparison Selection :=
  ⟨"table/specimen/coagulation/full-pairs", tableSource, fun c s =>
    symmetricPair (some true) s.first s.second ∧
    symmetricPair (c.lastSimultaneous.map (· == 1)) s.first s.third ∧
    symmetricPair (c.lastSimultaneous.map (· == 1)) s.second s.third⟩

def electrophoresisTable : Rule Comparison Selection :=
  ⟨"table/specimen/electrophoresis/partial-pairs", tableSource, fun _ s =>
    symmetricPair (some true) s.first s.second⟩

private theorem singleton_iff (rule : Rule Comparison Result) (c : Comparison)
    (s : Result) : Satisfies [rule] c s ↔ rule.holds c s := by
  simp [Satisfies]

private theorem coagulation_projection (c : Comparison) (h : SimultaneousScope c) (s : Selection) :
    coagulationNotice.holds c s ↔ AtMostOne s.first s.second s.third := by
  rcases c with ⟨eligible, time, specimen⟩
  obtain ⟨rfl, rfl⟩ := h
  rcases s with ⟨a, b, d⟩
  cases a <;> cases b <;> cases d <;>
    simp (config := { autoUnfold := true, decide := true }) [coagulationNotice, coagulationRows, performances, coagulationMarkerGroup, selected,
      D006.markerCombinationRule_holds, D006.MarkerSelection, D006.competingMarkers,
      D006.Context.item, coagulationMarkerInput, Performance.simultaneousWith,
      Performance.sameGroup, site, AtMostOne]

private theorem electrophoresis_projection (c : Comparison) (h : SpecimenScope c) (s : Selection) :
    electrophoresisNotice.holds c s ↔ AtMostOne s.first s.second s.third := by
  rcases c with ⟨eligible, time, specimen⟩
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rcases s with ⟨a, b, d⟩
  cases a <;> cases b <;> cases d <;>
    simp (config := { autoUnfold := true, decide := true }) [electrophoresisNotice, electrophoresisRows, performances, electrophoresisGroup,
      selected, D015.electrophoresisChoice_holds, D015.Excludes,
      D015.electrophoresisItems, D015.Context.item, plasmaProteinSelectionInput, retained,
      Performance.sameSpecimen, Performance.sameGroup, site, AtMostOne]

theorem coagulation_full_pairs :
    ∀ a b c : Bool, AtMostOne a b c ↔
      (a && b) = false ∧ (a && c) = false ∧ (b && c) = false := by
  intro a b c
  cases a <;> cases b <;> cases c <;> unfold AtMostOne <;> decide

theorem electrophoresis_partial_pairs :
    ∀ a b c : Bool, AtMostOne a b c → (a && b) = false := by
  intro a b c h
  exact (coagulation_full_pairs a b c |>.mp h).1

theorem electrophoresis_partial_pairs_has_extra_selection :
    ∃ a b c : Bool, (a && b) = false ∧ ¬ AtMostOne a b c := by
  exact ⟨true, false, true, rfl, by unfold AtMostOne; decide⟩

/-- 三対を収載した同時背反への射影は、確認済み範囲でD006(8)イと同値。 -/
theorem coagulation_equivalent :
    EquivalentOn SimultaneousScope [coagulationNotice] [coagulationTable] := by
  have compare (c : Comparison) (h : SimultaneousScope c) (s : Selection) :
      Satisfies [coagulationNotice] c s ↔ Satisfies [coagulationTable] c s := by
    rw [singleton_iff, singleton_iff, coagulation_projection c h]
    simpa [coagulationTable, symmetricPair, h.2] using
      coagulation_full_pairs s.first s.second s.third
  exact ⟨fun c h s => (compare c h s).mp, fun c h s => (compare c h s).mpr⟩

/-- 同一検体かつ同時の範囲では、D015(4)イが一対の同時背反を含意する。 -/
theorem electrophoresis_refines :
    RefinesOn SpecimenScope [electrophoresisNotice] [electrophoresisTable] := by
  intro c h s accepted
  rw [singleton_iff]
  exact fun _ => electrophoresis_partial_pairs _ _ _
    ((electrophoresis_projection c h s).mp ((singleton_iff _ _ _).mp accepted))

private def confirmed : Comparison := ⟨true, some 1, some 1⟩

theorem electrophoresis_disagrees :
    SpecimenScope confirmed ∧ DisagreesAt [electrophoresisNotice] [electrophoresisTable] confirmed := by
  have scope : SpecimenScope confirmed := ⟨⟨rfl, rfl⟩, rfl⟩
  refine ⟨scope, ⟨⟨true, false, true⟩, Or.inr ⟨?_, ?_⟩⟩⟩
  · exact (singleton_iff _ _ _).mpr (fun _ => rfl)
  · rw [singleton_iff, electrophoresis_projection _ scope]
    unfold AtMostOne; decide

/-- 適格な一実施を採用する結果が、双方の規則群で成立する。 -/
example : SimultaneousScope confirmed ∧
    SatisfiableAt [coagulationNotice, coagulationTable] confirmed := by
  have scope : SimultaneousScope confirmed := ⟨rfl, rfl⟩
  let result : Selection := ⟨true, false, false⟩
  have accepted : Satisfies [coagulationNotice] confirmed result := by
    rw [singleton_iff, coagulation_projection _ scope]
    unfold AtMostOne; decide
  have table := coagulation_equivalent.1 confirmed scope result accepted
  refine ⟨scope, ⟨result, ?_⟩⟩
  rw [satisfies_cons]
  exact ⟨(singleton_iff _ _ _).mp accepted, table⟩

/-- 同日でも同時IDが異なれば比較範囲外。同時でも検体ID不明ならD015の比較範囲外。 -/
example : ¬ SimultaneousScope ⟨true, some 2, some 1⟩ ∧
    ¬ SpecimenScope ⟨true, some 1, none⟩ := by
  simp [SimultaneousScope, SpecimenScope]


/-- D014(7)イの二項目事例。個別適格性と同時の併測を比較の入力で確認する。 -/
def D014Scope (c : Comparison) : Prop := SimultaneousScope c

def d014Notice : Rule Comparison (List D014.Item) :=
  ⟨D014.ccpChoice.id, D014.ccpChoice.source, fun c items =>
    let performed : List D014.Item := [.ccpQual, .c1q]
    (∀ i ∈ items, i ∈ performed) ∧
    ∀ p ∈ [⟨1, site, D014.Item.ccpQual, none, some 1, none, some 1⟩,
            ⟨2, site, .c1q, none, c.lastSpecimen, none, c.lastSimultaneous⟩],
      p.item ∈ items →
      D014.ccpChoice.holds { performance := p, combined := some (performed, items) } ()⟩

/-- 対象二件に適用できる背反行を観測しなかったときの表の射影。
表から行を抽出する処理と、他の算定規則の適用は定理の範囲外。 -/
def d014ObservedTable : Rule Comparison (List D014.Item) :=
  ⟨"table/specimen/d014/no-observed-pair",
    { tableSource with location := "同時・同日・同月・週背反の対象二件を検索" },
    fun _ items => ∀ i ∈ items, i = .ccpQual ∨ i = .c1q⟩

theorem d014_missing_pair_disagrees :
    D014Scope confirmed ∧ DisagreesAt [d014Notice] [d014ObservedTable] confirmed := by
  refine ⟨⟨rfl, rfl⟩, ⟨[.ccpQual, .c1q], Or.inr ⟨?_, ?_⟩⟩⟩
  · simp [Satisfies, d014ObservedTable]
  · intro h
    have hs := (singleton_iff d014Notice confirmed [.ccpQual, .c1q]).mp h
    have chosen := hs.2 ⟨1, site, .ccpQual, none, some 1, none, some 1⟩
      (by simp) (by simp)
    change D014.DistinctSelected _ _ 2 1 at chosen
    obtain ⟨performed, selected, equal, _, _, _, _, limit⟩ := chosen (by decide)
    have lists : [D014.Item.ccpQual, .c1q] = performed ∧
        [D014.Item.ccpQual, .c1q] = selected := by simpa using equal
    obtain ⟨rfl, rfl⟩ := lists
    exact (by decide : ¬ 2 ≤ 1) (limit (by decide))

end Sanri.MedicalFee.CaseStudies.SpecimenPairwiseTables
