import Sanri.SpecimenSelectionInventory

namespace Sanri.MedicalFee.SpecimenRawDay

open Sanri.History Sanri.Logic SpecimenCrossDivision

inductive Item where
  | urine (context : D000.Context)
  | morphology (context : BloodMorphology.Context)
  | chemistry (item : BloodChemistry.Item)
  | other (key : SpecimenSelectionInventory.ItemKey)

def Item.supported : Item → Bool
  | .urine _ => true
  | .morphology c => [BloodMorphology.Item.completeBloodCount, .eosinophilCount,
      .automatedDifferential, .microscopicDifferential].contains c.item
  | .chemistry i => [BloodChemistry.Item.bun, .uricAcid, .glucose, .ast, .alt, .creatinine,
      .totalProtein, .albumin, .gammaGT, .calcium, .ionizedCalcium,
      .uibcColorimetric, .tibcColorimetric].contains i
  | .other _ => false

/-- 検査一覧と、その日を評価するための確認済みの入力。
判断料の対象一覧と加算の検査一覧は実施から組み立てる。採取条件・履歴は別入力。 -/
structure Input where
  judgment : SpecimenJudgment.OutpatientDay
  additions : SpecimenOutpatientDay.AdditionContext
  rows : List (Performance Item)
  collections : List SpecimenCollection.Context
  collectionHistoryConfirmed : Bool
  eligible : Nat → Option Bool
  chemistryFacts : Nat → BloodChemistry.Draw
  coverage : SpecimenJudgment.Test → SpecimenJudgment.IncludedTest
  excludedJudgmentCandidate : Option Bool
  /-- 当日の実施IDに対応する確認済みの加算条件。none は候補なしを確認済み。 -/
  emergency : Nat → Option SpecimenOutpatientDay.EmergencyTest
  rapid : Nat → Option SpecimenOutpatientDay.RapidTest

def Input.site (c : Input) : Site := c.judgment.day.site

def Input.Supported (c : Input) : Prop :=
  ∀ row ∈ c.rows, row.item.supported = true

private def Input.morphology (c : Input) : List (Performance BloodMorphology.Context) :=
  c.rows.filterMap fun p => match p.item with
    | .morphology ctx => some { p with item := ctx }
    | _ => none

private def Input.chemistry (c : Input) : List (Performance BloodChemistry.Item) :=
  c.rows.filterMap fun p => match p.item with
    | .chemistry i => some { p with item := i }
    | _ => none

private def Input.urine (c : Input) : List D000.Context :=
  c.rows.filterMap fun p => match p.item with
    | .urine ctx => some { ctx with performance := { p with item := () } }
    | _ => none

private def pairs (rows : List α) : List (α × α) :=
  rows.zipIdx.flatMap fun (a, i) => (rows.drop (i + 1)).map (a, ·)

private def indexedPair (id : String) (a b : Performance α) (key : α → String) (division : String)
    (existing : ChoiceGroup) : Option ChoiceGroup :=
  SpecimenSelectionInventory.checkedProjection id
    [{ a with item := (division, key a.item) }, { b with item := (division, key b.item) }] existing

private def morphologyKey : BloodMorphology.Item → String
  | .eosinophilCount => "eosinophilCount"
  | .automatedDifferential => "automatedDifferential"
  | .microscopicDifferential => "microscopicDifferential"
  | _ => ""

private def chemistryKey : BloodChemistry.Item → String
  | .calcium => "calcium"
  | .ionizedCalcium => "ionizedCalcium"
  | .uibcColorimetric => "uibcColorimetric"
  | .tibcColorimetric => "tibcColorimetric"
  | _ => ""

/-- 一つの項目が複数の二件群に入るD005(3)の読みはここでは未確定とする。 -/
def Input.groups (c : Input) : Option (List ChoiceGroup) := do
  let morphology ← (pairs c.morphology).mapM fun (left, right) => do
    let a : Performance BloodMorphology.Item := { left with item := left.item.item }
    let b : Performance BloodMorphology.Item := { right with item := right.item.item }
    let existing ← morphologyGroups a b false
    existing.mapM (indexedPair BloodMorphology.eosinophilRule.id a b morphologyKey "D005")
  if !(overlappingGroups morphology.flatten).isEmpty then none else
    let chemistry ← (pairs c.chemistry).mapM fun (a, b) => do
      let kind := if [a.item, b.item].isPerm BloodChemistry.calciumGroup then
          some ("notice/D007/paragraph/2", ChemistryCombination.calcium)
        else if [a.item, b.item].isPerm BloodChemistry.ironBindingGroup then
          some ("notice/D007/paragraph/3", ChemistryCombination.ironBinding)
        else none
      match kind with
      | none => return []
      | some (clause, kind) =>
        if !(← a.simultaneousWith b) then return []
        let existing ← chemistryCombinationGroup kind [a, b]
        let group ← indexedPair clause a b chemistryKey "D007" existing
        return [group]
    return morphology.flatten ++ chemistry.flatten

/-- 指定した採否が全群に共通し、各群の必要件数を満たす場合にだけ射影する。 -/
def resolveChoices (groups : List ChoiceGroup) (selected : Option (List Nat)) :
    Option (List GroupChoice) := do
  if groups.isEmpty then
    if selected.getD [] == [] then some [] else none
  else
    let ids ← selected
    if !(consistentSelections groups [] []).any (·.isPerm ids) then none else
      return groups.map fun g => ⟨g, g.members.filter ids.contains⟩

private def fixedCharge (points : Nat) : Charge :=
  ⟨(· = points), points, rfl, fun _ h => h⟩

private def Input.morphologyPoints (c : Input) (choices : List GroupChoice) : Option (List Nat) :=
  (c.morphology.filter fun p => retained choices p.id).mapM fun p =>
    match BloodMorphology.assess p.item with
    | .payable base stain => some (base + stain)
    | _ => none

private def Input.drawFacts (c : Input) (draw : Nat) : BloodChemistry.Draw :=
  { c.chemistryFacts draw with
    calcium := { together := some false }
    ironBinding := { together := some false } }

private def Input.chemistryDraws (c : Input) (choices : List GroupChoice) :
    Option (List (Nat × List BloodChemistry.Item)) := do
  let ids ← c.chemistry.mapM Performance.draw
  if !(c.chemistry.zip ids).all (fun (row, draw) =>
      (c.drawFacts draw).eligible row.item == some true) then none else
    ids.eraseDups.mapM fun draw => do
      let projected ← chemistryDraw choices c.chemistry c.site draw (c.drawFacts draw)
      let items ← BloodChemistry.billableItems projected
      if items.isEmpty then none else some (draw, items)

private def Input.test (c : Input) (id : Nat) (test : SpecimenJudgment.Test)
    (candidate : Option Bool) : DayTest :=
  ⟨id, c.site, { c.coverage test with test := test }, candidate, c.emergency id, c.rapid id⟩

private def Input.tests (c : Input) (choices : List GroupChoice) : List DayTest :=
  (c.urine.map fun p => c.test p.performance.id D000.judgmentTest (some false)) ++
  (c.morphology.map fun p => c.test p.id (p.item.item.judgmentTest false)
    (if retained choices p.id then some true else c.excludedJudgmentCandidate)) ++
  (c.chemistry.map fun p => c.test p.id (D007.Item.judgmentTest ⟨.draw, p.item⟩)
    (if retained choices p.id then
      p.draw.bind fun draw => chemistryJudgmentCandidate p c.chemistry choices (c.drawFacts draw)
    else c.excludedJudgmentCandidate))

/-- D007の包括キーは実施から求める。項目数に応じた包括額は採血ごとに一度合成する。 -/
def Input.assignment (p : Performance Item) : Option BundleKey :=
  match p.item with
  | .chemistry _ => bundleKey ⟨7, 0, .draw⟩ p
  | _ => none

theorem assignment_disjoint (c : Input) {row : Performance Item} {a b : BundleKey}
    (ha : row ∈ assignedMembers Input.assignment c.rows a)
    (hb : row ∈ assignedMembers Input.assignment c.rows b) : a = b :=
  assigned_members_disjoint _ _ ha hb

/-- 元の事実と選択を日次評価へ渡す。対応範囲外・確認不足はいずれも none。 -/
private def Input.prepareFacts (c : Input) (selected : Option (List Nat)) :
    Option (Day × List Nat) := do
  let ids := c.rows.map Performance.id
  if !c.collectionHistoryConfirmed || c.collections.length > 1 ||
      !c.collections.all (fun p => SpecimenCollection.isD400 p.item && !p.inpatient) ||
      !c.rows.all (fun p => p.item.supported && p.site == c.site &&
      c.eligible p.id == some true) || ids.eraseDups != ids || c.additions.site != c.site then none
  else
    let choices ← resolveChoices (← c.groups) selected
    if c.morphology.length != (c.morphology.map (·.item.item)).eraseDups.length ||
        c.urine.length > 1 then none else
      let urine ← c.urine.mapM fun p =>
        if p.performingInstitution == some p.performance.site.institution &&
            !p.analytes.isEmpty && p.method.isSome &&
            (p.arrangement == some .direct || p.arrangement == some (.contracted (some true)))
        then some D000.points else none
      let morphology ← c.morphologyPoints choices
      let draws ← c.chemistryDraws choices
      let execution := (draws.map fun (_, items) => BloodChemistry.pointsForItems items) ++
        morphology ++ urine
      let day ← Day.withTests ⟨[], [], c.judgment, c.additions⟩
        (c.tests choices)
      let _ ← day.judgment.points
      return (day, execution)

def Input.prepare (c : Input) (selected : Option (List Nat)) : Option (Day × List Nat) :=
  (c.prepareFacts selected).map fun (day, execution) =>
    ({ day with execution := execution.map fixedCharge }, execution)

private theorem prepare_execution {c : Input} {selected : Option (List Nat)} {prep : Day}
    {execution : List Nat} (h : c.prepare selected = some (prep, execution)) :
    prep.execution = execution.map fixedCharge := by
  unfold Input.prepare at h
  obtain ⟨⟨day, points⟩, _, eq⟩ := Option.map_eq_some_iff.mp h
  cases eq
  rfl

private theorem fixed_charges (points : List Nat) :
    ChargeList (points.map fixedCharge) points := by
  induction points with
  | nil => exact .nil
  | cons _ _ ih => exact .cons rfl ih

theorem morphology_projection (c : BloodMorphology.Context) (base stain : Nat)
    (h : BloodMorphology.assess c = .payable base stain) :
    Satisfies BloodMorphology.individualRules c (base, stain) :=
  (BloodMorphology.payable_iff c base stain).2 h

theorem chemistry_projection (c : Input) (choices : List GroupChoice) (draw : Nat)
    (projected : BloodChemistry.Draw) (points : Nat)
    (h : chemistryDraw choices c.chemistry c.site draw (c.drawFacts draw) = some projected) :
    BloodChemistry.DrawPoints projected points ↔
      (chemistryDraw choices c.chemistry c.site draw (c.drawFacts draw)).bind
        BloodChemistry.points = some points :=
  chemistryDraw_points choices c.chemistry c.site draw (c.drawFacts draw) projected points h

/-- 加算の選択と、その選択に必要な同一検査の証拠・当日の先行履歴。 -/
structure Confirmed (day : Day) : Prop where
  site : day.additions.site = day.judgment.day.site
  judgment : day.judgment.Eligible
  emergency : day.additions.selection = .emergency →
    SpecimenOutpatientDay.EmergencyConfirmed day.additions ∧
    day.additions.emergencyClaimed = some false ∧ day.additions.priorRapidItems = some [] ∧
    day.additions.nightEarlyMorningAddition = false
  rapid : day.additions.selection = .rapid → ∃ prior,
    day.additions.priorRapidItems = some prior ∧ prior.Nodup ∧ prior.length ≤ 5 ∧
    day.additions.emergencyClaimed = some false

def Input.Scope (c : Input) (selected : Option (List Nat)) : Prop :=
  c.Supported ∧ ∃ prep execution day,
    c.prepare selected = some (prep, execution) ∧
    prep.withCollectionContexts c.collections = some day ∧ Confirmed prep

def Input.Permits (c : Input) (selected : Option (List Nat)) (r : Breakdown) : Prop :=
  ∃ prep execution day, c.prepare selected = some (prep, execution) ∧
    prep.withCollectionContexts c.collections = some day ∧ day.Permits r

theorem determines (c : Input) (selected : Option (List Nat)) (scope : c.Scope selected) :
    ∃ r, c.Permits selected r ∧ ∀ other, c.Permits selected other → other = r := by
  obtain ⟨_, prep, execution, day, hp, hd, h⟩ := scope
  obtain ⟨r, hr, unique⟩ := day_determines_from_collection_contexts prep day c.collections hd
    h.site h.judgment h.emergency h.rapid
  refine ⟨r, ⟨prep, execution, day, hp, hd, hr⟩, ?_⟩
  rintro other ⟨prep', execution', day', hp', hd', ho⟩
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
  rw [hd] at hd'
  cases Option.some.inj hd'
  exact unique _ ho

def Input.Allowed (c : Input) (r : Breakdown) : Prop :=
  ∃ selected, c.Scope selected ∧ c.Permits selected r

/-- 加算なしの範囲で使う計算射影。判断料・採取の未確定は伝播する。 -/
def Input.withoutAdditions (c : Input) (selected : Option (List Nat)) : Option Breakdown := do
  let (prep, execution) ← c.prepare selected
  if prep.additions.selection != .none then none else
    let judgment ← prep.judgment.points
    let assessments ← SpecimenCollection.assessDay c.collections
    let collection := assessments.filterMap fun a => (a.toCollection 0).map (·.scheduledPoints)
    let total := SpecimenOutpatientDay.assess ⟨prep.judgment.day.site, execution.sum, judgment, collection, 0, 0⟩
    return ⟨execution, collection, judgment, ⟨0, 0⟩, total⟩

private theorem collection_charges (day : Day) (rows : List SpecimenCollection.Assessment) :
    ChargeList (day.withCollectionAssessments rows).collection
      (rows.filterMap fun a => (a.toCollection 0).map (·.scheduledPoints)) := by
  induction rows with
  | nil => exact .nil
  | cons a rest ih =>
    cases h : a.toCollection 0 with
    | none => simpa [Day.withCollectionAssessments, h] using ih
    | some charge =>
      simpa [Day.withCollectionAssessments, h, fixedCharge] using
        (ChargeList.cons (charge := fixedCharge charge.scheduledPoints) rfl ih)

theorem without_additions_sound (c : Input) (selected : Option (List Nat))
    (r : Breakdown) (h : c.withoutAdditions selected = some r)
    (eligible : ∀ prep execution, c.prepare selected = some (prep, execution) →
      prep.judgment.Eligible) :
    c.Permits selected r := by
  unfold Input.withoutAdditions at h
  cases hp : c.prepare selected with
  | none => simp [hp] at h
  | some pair =>
    obtain ⟨prep, execution⟩ := pair
    by_cases ha : prep.additions.selection = .none
    · cases hj : prep.judgment.points with
      | none => simp [hp, ha, hj] at h
      | some judgment =>
        cases hc : SpecimenCollection.assessDay c.collections with
        | none => simp [hp, hc] at h
        | some assessments =>
          simp [hp, ha, hj, hc] at h
          subst r
          refine ⟨prep, execution, prep.withCollectionAssessments assessments, hp, ?_, ?_⟩
          · simp [Day.withCollectionContexts, hc]
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · change ChargeList prep.execution execution
              rw [prepare_execution hp]
              exact fixed_charges execution
            · exact collection_charges prep assessments
            · exact (SpecimenJudgment.outpatient_day_iff _ (eligible _ _ hp) _).2 hj
            · simp [Day.withCollectionAssessments, SpecimenOutpatientDay.additionRules,
                satisfies_cons, satisfies_nil, SpecimenOutpatientDay.emergencyPrimary,
                SpecimenOutpatientDay.rapidPrimary, SpecimenOutpatientDay.emergencyOnce,
                SpecimenOutpatientDay.emergencyNightExclusion, SpecimenOutpatientDay.rapidBundle,
                SpecimenOutpatientDay.rapidDailyLimit, SpecimenOutpatientDay.rapidConsultationBundle, ha]
            · exact (SpecimenOutpatientDay.satisfies_iff ..).2 rfl
    · simp [hp, ha] at h

private def site : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def base : Input where
  judgment := ⟨⟨site, [], false, ⟨⟨site.monthScope, []⟩, by simp⟩, ⟨site.monthScope, []⟩⟩,
    true, .outpatient, none, none, none⟩
  additions := ⟨site, .none, [], [], some false, some [], false⟩
  rows := []
  collections := []
  collectionHistoryConfirmed := true
  eligible := fun _ => some true
  chemistryFacts := fun _ =>
    { performed := [], albuminByModifiedBCP := some true, creatinineByJaffe := some false }
  coverage := fun test => ⟨test, false, false, none, none⟩
  excludedJudgmentCandidate := some false
  emergency := fun _ => none
  rapid := fun _ => none

private def chemistryRows (items : List BloodChemistry.Item) : List (Performance Item) :=
  items.zipIdx.map fun (i, j) =>
    { id := j + 10, site, item := .chemistry i, draw := some 1, simultaneous := some 1 }

private def morphologyRow (id : Nat) (item : BloodMorphology.Item) : Performance Item :=
  { id, site, specimen := some 2, draw := some 1, item := .morphology {
      item
      counts := some [.redCells, .whiteCells, .hemoglobin, .hematocrit, .platelets]
      cellClasses := some [.lymphocyte, .monocyte, .neutrophil, .eosinophil, .basophil] } }

private def raw429 : Input :=
  { base with rows := morphologyRow 1 .completeBloodCount ::
      chemistryRows [.bun, .creatinine, .ast, .alt, .totalProtein, .albumin, .gammaGT, .uricAcid]
              collections := [{ item := .venousBlood, ageYears := 40 }] }

private def rawDifferential : Input :=
  let urine : D000.Context :=
    ⟨⟨3, site, (), none, none, none, none⟩, some site.institution, some .strip, [.ph], some .direct⟩
  { base with rows := [morphologyRow 1 .eosinophilCount, morphologyRow 2 .automatedDifferential,
    { id := 3, site, item := .urine urine }] ++ chemistryRows [.bun, .uricAcid, .glucose, .ast, .alt] }

private def total (c : Input) (selected : Option (List Nat)) : Option Nat :=
  (c.withoutAdditions selected).map (·.total.specimenWithCollection)

example : total raw429 none = some 429 := by decide
example : total rawDifferential (some [1]) = some 405 := by decide
example : total rawDifferential (some [2]) = some 403 := by decide
example : total rawDifferential none = none := by decide

example : total { raw429 with rows := raw429.rows.map fun p => { p with draw := none } } none =
    none := by decide

example : total { raw429 with judgment := { raw429.judgment with day :=
    { raw429.judgment.day with performances := ⟨{ site.monthScope with patient := 4 }, []⟩ } } }
    none = none := by decide

/-- 二つの選択群と採血包括、D026、D400を同じ原実施日から評価する。 -/
private def twoGroups : Input :=
  let rows : List (Performance Item) :=
    [{ id := 20, site, item := .chemistry .calcium, draw := some 1, simultaneous := some 1 },
     { id := 21, site, item := .chemistry .ionizedCalcium, draw := some 1, simultaneous := some 1 }]
  { rawDifferential with
    rows := rawDifferential.rows ++ rows
    collections := raw429.collections }

example : (twoGroups.groups.map List.length, total twoGroups (some [1, 20])) =
    (some 2, some 445) := by decide

example : raw429.Scope none := by
  refine ⟨?_, _, _, _, rfl, rfl, ?_⟩
  · exact fun _ membership => List.all_eq_true.mp (by decide :
      raw429.rows.all (fun p => p.item.supported) = true) _ membership
  · refine ⟨rfl, ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · unfold SpecimenJudgment.DailyJudgment.Known
      decide
    · intro f h
      cases h
    · intro e h
      cases h
    · intro e h
      cases h
    · intro h
      cases h
    · intro h
      cases h

end Sanri.MedicalFee.SpecimenRawDay
