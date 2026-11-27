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

theorem electrophoresis_all_extra_selections (c : Comparison) (scope : SpecimenScope c)
    (picked : Selection) (table : Satisfies [electrophoresisTable] c picked) :
    ¬ Satisfies [electrophoresisNotice] c picked ↔
      picked.third = true ∧ (picked.first = true ∨ picked.second = true) := by
  have pair := (singleton_iff _ _ _).mp table rfl
  rw [singleton_iff, electrophoresis_projection _ scope]
  rcases picked with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third <;> simp_all [AtMostOne]


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

private def rheumatoidCommon : List D014.Item :=
  [.galactoseQual, .galactoseQuant, .mmp3, .c1q, .rfComplex, .iggRf]

private def ccpGroup : List D014.Item := [.ccpQual, .ccpQuant] ++ rheumatoidCommon

/-- 一患者・一機関で適格性、同時性及び通知上の併測を確認し、
比較する八種類を各一回実施した事例。採否は実施済み項目の重複のない部分集合。 -/
def D014FullScope (c : Comparison) (picked : List D014.Item) : Prop :=
  D014Scope c ∧ picked.Nodup ∧ ∀ i ∈ picked, i ∈ ccpGroup

/-- 観測した21対は、八種類から一種類を除いた七種類の全対。 -/
def d014FullTable : Rule Comparison (List D014.Item) :=
  ⟨"table/specimen/d014/21-observed-pairs", tableSource, fun _ picked =>
    ∀ a ∈ picked, ∀ b ∈ picked, a ≠ .c1q → b ≠ .c1q → a = b⟩

def d014MissingPairs (picked : List D014.Item) : Prop :=
  .c1q ∈ picked → ∀ b ∈ picked, b = .c1q

/-- 既存の通知制約に全群の実施と採否を渡す。 -/
def d014FullNotice : Rule Comparison (List D014.Item) :=
  ⟨D014.ccpChoice.id, D014.ccpChoice.source, fun _ picked =>
    ∀ i ∈ picked, D014.ccpChoice.holds
      { performance := ⟨(.rf :: ccpGroup).idxOf i + 1, site, i, none, none, none, some 1⟩
        combined := some (ccpGroup, picked) } ()⟩

private theorem at_most_one_item {items : List D014.Item} (distinct : items.Nodup) :
    items.length ≤ 1 ↔ ∀ a ∈ items, ∀ b ∈ items, a = b := by
  rcases items with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp
  · simp
  · have different : a ≠ b := fun h => (List.nodup_cons.mp distinct).1 (by simp [h])
    constructor
    · simp
    · intro h
      exact False.elim (different (h a (by simp) b (by simp)))

private theorem d014_full_notice_iff (c : Comparison) (picked : List D014.Item)
    (scope : D014FullScope c picked) :
    d014FullNotice.holds c picked ↔ picked.length ≤ 1 := by
  have filtered : picked.filter (· ∈ ccpGroup) = picked :=
    List.filter_eq_self.mpr (by simpa using scope.2.2)
  constructor
  · intro h
    rcases picked with _ | ⟨i, rest⟩
    · simp
    · have member : i ∈ i :: rest := by simp
      have rule := h i member
      change D014.DistinctSelected _ ccpGroup 2 1 at rule
      obtain ⟨performed, selected, input, _, _, _, _, limit⟩ := rule (scope.2.2 i member)
      have lists : ccpGroup = performed ∧ i :: rest = selected := by simpa using input
      obtain ⟨rfl, rfl⟩ := lists
      simpa [filtered] using limit (by decide)
  · intro limit i member
    change D014.DistinctSelected _ ccpGroup 2 1
    exact fun _ => ⟨ccpGroup, picked, rfl, member, scope.2.1, by decide,
      scope.2.2, fun _ => by simpa [filtered] using limit⟩

theorem d014_full_notice_equivalent (c : Comparison) (picked : List D014.Item)
    (scope : D014FullScope c picked) :
    d014FullNotice.holds c picked ↔
      d014FullTable.holds c picked ∧ d014MissingPairs picked := by
  rw [d014_full_notice_iff c picked scope, at_most_one_item scope.2.1]
  constructor
  · intro h
    exact ⟨fun a ha b hb _ _ => h a ha b hb, fun hc b hb => h b hb .c1q hc⟩
  · rintro ⟨table, missing⟩ a ha b hb
    by_cases ac : a = .c1q
    · subst a
      exact (missing ha b hb).symm
    · by_cases bc : b = .c1q
      · subst b
        exact missing hb a ha
      · exact table a ha b hb ac bc

theorem d014_full_table_disagreement (c : Comparison) (picked : List D014.Item)
    (scope : D014FullScope c picked) (table : d014FullTable.holds c picked) :
    ¬ d014FullNotice.holds c picked ↔
      .c1q ∈ picked ∧ ∃ other ∈ picked, other ≠ .c1q := by
  rw [d014_full_notice_equivalent c picked scope]
  simp [table, d014MissingPairs]

example : D014FullScope confirmed [.ccpQual, .c1q] ∧
    d014FullTable.holds confirmed [.ccpQual, .c1q] ∧
    ¬ d014FullNotice.holds confirmed [.ccpQual, .c1q] := by
  have scope : D014FullScope confirmed [.ccpQual, .c1q] :=
    ⟨⟨rfl, rfl⟩, by decide, by simp [ccpGroup, rheumatoidCommon]⟩
  have table : d014FullTable.holds confirmed [.ccpQual, .c1q] := by
    simp [d014FullTable]
  exact ⟨scope, table, (d014_full_table_disagreement _ _ scope table).mpr
    ⟨by simp, .ccpQual, by simp, by decide⟩⟩

/-- 九種類を各一回実施し、両通知の併測範囲が確認済みの場合の採否制約。
RF定量は(1)に入る。採否は重複のない実施済み部分集合とする。 -/
def d014RheumatoidNotice : Rule Comparison (List D014.Item) :=
  ⟨D014.rheumatoidLimit.id, D014.rheumatoidLimit.source, fun _ picked =>
    ∀ i ∈ picked, D014.rheumatoidLimit.holds
      { performance := ⟨(.rf :: ccpGroup).idxOf i + 1, site, i, none, none, none, some 1⟩
        combined := some (.rf :: ccpGroup, picked) } ()⟩

private theorem rheumatoid_count_bound (picked : List D014.Item)
    (distinct : picked.Nodup) :
    (picked.filter (· ∈ ccpGroup)).length ≤ 1 →
    (picked.filter (· ∈ (.rf :: rheumatoidCommon))).length ≤ 2 := by
  have count_le (xs : List D014.Item) (h : xs.Nodup) :
      (xs.filter (· ∈ (.rf :: rheumatoidCommon))).length ≤
        (xs.filter (· ∈ ccpGroup)).length + (if .rf ∈ xs then 1 else 0) := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      obtain ⟨not_mem, tail⟩ := List.nodup_cons.mp h
      have bound := ih tail
      by_cases ha : a = .rf
      · subst a
        simp [ccpGroup, rheumatoidCommon, not_mem] at bound ⊢
        omega
      · have reverse : D014.Item.rf ≠ a := Ne.symm ha
        by_cases common : a ∈ rheumatoidCommon
        · simp [ha, reverse, common, ccpGroup] at bound ⊢
          omega
        · simp [List.filter_cons, ha, reverse, common, ccpGroup] at bound ⊢
          split <;> simp_all <;> omega
  have bound := count_le picked distinct
  split at bound <;> omega

theorem d014_ccp_limit_implies_rheumatoid (c : Comparison) (picked : List D014.Item)
    (distinct : picked.Nodup) (within : ∀ i ∈ picked, i ∈ .rf :: ccpGroup)
    (ccpLimit : (picked.filter (· ∈ ccpGroup)).length ≤ 1) :
    d014RheumatoidNotice.holds c picked := by
  intro i member
  change D014.DistinctSelected _ (.rf :: rheumatoidCommon) 3 2
  exact fun _ => ⟨.rf :: ccpGroup, picked, rfl, member, distinct, by decide,
    within, fun _ => rheumatoid_count_bound picked distinct ccpLimit⟩

/-- (7)イに(1)のみに属する一種類を加えた共通実施範囲。 -/
def d014OverlapCcpNotice : Rule Comparison (List D014.Item) :=
  ⟨D014.ccpChoice.id, D014.ccpChoice.source, fun _ picked =>
    ∀ i ∈ picked, D014.ccpChoice.holds
      { performance := ⟨(.rf :: ccpGroup).idxOf i + 1, site, i, none, none, none, some 1⟩
        combined := some (.rf :: ccpGroup, picked) } ()⟩

theorem d014_both_notices_iff (c : Comparison) (picked : List D014.Item)
    (_ : D014Scope c) (distinct : picked.Nodup) (within : ∀ i ∈ picked, i ∈ .rf :: ccpGroup) :
    Satisfies [d014OverlapCcpNotice, d014RheumatoidNotice] c picked ↔
      (picked.filter (· ∈ ccpGroup)).length ≤ 1 := by
  have ccp_iff : d014OverlapCcpNotice.holds c picked ↔
      (picked.filter (· ∈ ccpGroup)).length ≤ 1 := by
    constructor
    · intro hc
      by_cases empty : picked.filter (· ∈ ccpGroup) = []
      · simp [empty]
      · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ empty
        obtain ⟨inPicked, inGroup⟩ := List.mem_filter.mp hi
        have rule := hc i inPicked
        change D014.DistinctSelected _ ccpGroup 2 1 at rule
        have belongs : i ∈ ccpGroup := of_decide_eq_true inGroup
        obtain ⟨performed, selected, input, _, _, _, _, limit⟩ := rule belongs
        have lists : .rf :: ccpGroup = performed ∧ picked = selected := by simpa using input
        obtain ⟨rfl, rfl⟩ := lists
        exact limit (by decide)
    · intro limit i member
      change D014.DistinctSelected _ ccpGroup 2 1
      exact fun _ => ⟨.rf :: ccpGroup, picked, rfl, member, distinct, by decide,
        within, fun _ => limit⟩
  rw [satisfies_cons, singleton_iff, ccp_iff]
  exact ⟨And.left, fun h => ⟨h, d014_ccp_limit_implies_rheumatoid c picked distinct within h⟩⟩


example : Satisfies [d014OverlapCcpNotice, d014RheumatoidNotice] confirmed [.rf, .mmp3] :=
  (d014_both_notices_iff _ _ ⟨rfl, rfl⟩ (by decide) (by decide)).mpr (by decide)

example : d014RheumatoidNotice.holds confirmed [.mmp3, .c1q] ∧
    ¬ d014FullNotice.holds confirmed [.mmp3, .c1q] := by
  constructor
  · intro i member
    change D014.DistinctSelected _ (.rf :: rheumatoidCommon) 3 2
    exact fun _ => ⟨.rf :: ccpGroup, [.mmp3, .c1q], rfl, member, by decide, by decide,
      by decide, fun _ => by decide⟩
  · rw [d014_full_notice_iff _ _ ⟨⟨rfl, rfl⟩, by decide, by decide⟩]
    decide

private def pancreaticUrine : D001.Context :=
  { performance := ⟨1, site, .trypsinogen2, none, none, none, some 1⟩ }

private def pancreaticChemistry : Performance D007.Item :=
  ⟨2, site, ⟨.draw, .amylase⟩, none, none, none, some 1⟩

private def noticeFromGroup (id : String) (source : SourceRef) (observed : Option ChoiceGroup) :
    Rule Comparison (List Nat) :=
  ⟨id, source, fun _ picked =>
    ∃ group, observed = some group ∧ (GroupChoice.mk group picked).Valid⟩

/-- 採否を固定した二候補について、関連行を同定できなかった射影。 -/
private def noObservedPair (id : String) : Rule Comparison (List Nat) :=
  ⟨id, tableSource, fun _ picked => ∀ i ∈ picked, i = 1 ∨ i = 2⟩

private theorem single_group_missing_pair (id tableId : String) (source : SourceRef)
    (observed : Option ChoiceGroup) (identifies : observed = some ⟨source, [1, 2], 1⟩) :
    SimultaneousScope confirmed ∧
      DisagreesAt [noticeFromGroup id source observed] [noObservedPair tableId] confirmed := by
  refine ⟨⟨rfl, rfl⟩, ⟨[1, 2], Or.inr ⟨?_, ?_⟩⟩⟩
  · simp [Satisfies, noObservedPair]
  · intro h
    obtain ⟨group, eq, valid⟩ := (singleton_iff _ _ _).mp h
    rw [identifies] at eq
    obtain rfl := Option.some.inj eq
    have count := valid.2.2.1
    change 2 = 1 at count
    contradiction

/-- 二件の適格性と通知上の併施を確認した場合の差。 -/
theorem pancreatic_missing_pair_disagrees :
    SimultaneousScope confirmed ∧
      DisagreesAt
        [noticeFromGroup D001.pancreaticRule.id D001.pancreaticRule.source
          (pancreaticGroup pancreaticUrine [pancreaticChemistry] [])]
        [noObservedPair "table/specimen/pancreatic/no-observed-pair"] confirmed :=
  single_group_missing_pair _ _ _ _ rfl

private def infectionPair (a b : D012.RelatedTest) : D012.Combined :=
  { members := [⟨1, site, a, none, none, none, some 1⟩, ⟨2, site, b, none, none, none, some 1⟩] }

/-- D012(31)イの欠けた検体別コード対を、適格で併施された二種類へ射影する。 -/
theorem pneumococcus_missing_pair_disagrees :
    SimultaneousScope confirmed ∧
      DisagreesAt
        [noticeFromGroup D012.pneumococcusWallChoice.id D012.pneumococcusWallChoice.source
          (infectionGroup .pneumococcus
            (infectionPair (.local .pneumococcusWall) (.local .pneumococcusCapsule)))]
        [noObservedPair "table/specimen/pneumococcus/specimen-specific-gap"] confirmed :=
  single_group_missing_pair _ _ _ _ rfl

/-- D012(43)イの相手として通知で確認した一種類との併施に限る。 -/
theorem pertussis_missing_pair_disagrees :
    SimultaneousScope confirmed ∧
      DisagreesAt
        [noticeFromGroup D012.pertussisChoice.id D012.pertussisChoice.source
          (infectionGroup .pertussis (infectionPair (.local .pertussisAntigen) .pertussisD023_13))]
        [noObservedPair "table/specimen/pertussis/dual-assay-gap"] confirmed :=
  single_group_missing_pair _ _ _ _ rfl

private def respiratoryAnchor : Performance Unit :=
  ⟨1, site, (), none, none, some 1, some 1⟩

private def respiratoryPeer : Performance D023.SeriesTest :=
  ⟨2, site, .antibody .pertussisAntigen, none, none, some 1, some 1⟩

def respiratoryNotice : Rule Comparison Bool :=
  ⟨D023.panelWithCovidTa.id, D023.panelWithCovidTa.source, fun _ separate =>
    D023.SeriesExcludes respiratoryAnchor (if separate then [respiratoryPeer] else [])
      (fun test => some (test == respiratoryPeer.item))⟩

def respiratoryObservedTable : Rule Comparison Bool :=
  ⟨"table/specimen/respiratory/no-observed-pair", tableSource, fun _ _ => True⟩

/-- D023(37)ウ(タ)の代表一対。パネルを採用し、相手を別実施した状況に限る。
同じ一連であり、同時性も独立に確認する。結果は相手の別算定の採否。 -/
theorem respiratory_series_missing_pair_disagrees :
    SimultaneousScope confirmed ∧
      respiratoryAnchor.sameSeries { respiratoryPeer with item := () } = some true ∧
      respiratoryAnchor.simultaneousWith { respiratoryPeer with item := () } = some true ∧
      DisagreesAt [respiratoryNotice] [respiratoryObservedTable] confirmed := by
  refine ⟨⟨rfl, rfl⟩, rfl, rfl, ⟨true, Or.inr ⟨?_, ?_⟩⟩⟩
  · simp [Satisfies, respiratoryObservedTable]
  · intro h
    have excluded := (singleton_iff _ _ _).mp h
    change D023.SeriesExcludes respiratoryAnchor [respiratoryPeer]
      (fun test => some (test == respiratoryPeer.item)) at excluded
    rcases excluded respiratoryPeer (by simp) with test | series
    · change some true = some false at test
      contradiction
    · change some true = some false at series
      contradiction

example : Satisfies [respiratoryNotice, respiratoryObservedTable] confirmed false := by
  simp [Satisfies, respiratoryNotice, respiratoryObservedTable, D023.SeriesExcludes]

end Sanri.MedicalFee.CaseStudies.SpecimenPairwiseTables
