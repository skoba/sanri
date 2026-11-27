import Sanri.SpecimenSelectionInventory

namespace Sanri.MedicalFee.SpecimenRawDay

open Sanri.History Sanri.Logic SpecimenCrossDivision

inductive Item where
  | urine (context : D000.Context)
  | morphology (context : BloodMorphology.Context)
  | chemistry (item : BloodChemistry.Item)
  | coagulation (item : D006.Item)
  | endocrine (item : D008.Item)
  | alpPag
  | tumorMarker (item : D009.Item)
  | hepatitis (item : D013.Item)
  | specificIge (antigen : Option Nat)
  | viralTiter (target : D012.Target)
  | classTiter (target : D012.Target) (antibody : D012.AntibodyClass)
  | autoantibody (item : D014.Item)
  | other (key : SpecimenSelectionInventory.ItemKey)

def Item.supported : Item → Bool
  | .urine _ => true
  | .morphology c => [BloodMorphology.Item.completeBloodCount, .eosinophilCount,
      .automatedDifferential, .microscopicDifferential].contains c.item
  | .chemistry i => [BloodChemistry.Item.bun, .uricAcid, .glucose, .ast, .alt, .creatinine,
      .totalProtein, .albumin, .gammaGT, .calcium, .ionizedCalcium,
      .uibcColorimetric, .tibcColorimetric].contains i
  | .coagulation i => [D006.Item.antithrombinActivity, .pic, .dDimer,
      .tat, .prothrombinFragment].contains i
  | .endocrine i => [D008.Item.fsh, .lh, .cortisol, .bap].contains i
  | .alpPag => true
  | .tumorMarker i => [4, 5, 13].contains i.number && i.variant == 0
  | .hepatitis i => [D013.Item.hbeAntigen, .hbeAntibody, .hcvAntibody].contains i
  | .specificIge _ => true
  | .viralTiter t => [D012.Target.rubella, .measles, .mumps, .cytomegalovirus].contains t
  | .classTiter t a =>
    [D012.Target.rubella, .measles, .mumps, .cytomegalovirus].contains t &&
      [D012.AntibodyClass.igg, .igm].contains a
  | .autoantibody i => [D014.Item.rnpQuant, .smQuant, .ssbQuant].contains i
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
  /-- D014注1の適用群が当日の入力に収まるとの確認。 -/
  autoantibodyDayConfirmed : Bool := false
  /-- D007のPAG法とD008のBAPが通知D008(16)の併施範囲に入るか。 -/
  alpPaired : Option Bool := none

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

private def Input.coagulation (c : Input) : List (Performance D006.Item) :=
  c.rows.filterMap fun p => match p.item with
    | .coagulation i => some { p with item := i }
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

/-- 対象はD007のPAG法とD008のBAPの二項目。併施の時間幅は確認値を使う。 -/
private def Input.alpGroups (c : Input) : Option (List ChoiceGroup) := do
  let rows := c.rows.filterMap fun p => match p.item with
    | .alpPag => some ({ p with item := .d007Pag } : Performance D008.CombinationItem)
    | .endocrine .bap => some { p with item := .endocrine .bap .other }
    | _ => none
  match rows with
  | [] | [_] => some []
  | [a, b] =>
    if a.item == b.item then none else
      (c.alpPaired).bind fun paired =>
        if paired then (endocrineGroup .alp rows).map (· :: []) else some []
  | _ => none

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
    let markers := c.coagulation.filter (fun p => D006.competingMarkers.contains p.item)
    if markers.length != (markers.map Performance.item).eraseDups.length then none else
      let coagulation ← match markers with
        | [a, b] => (a.simultaneousWith b).bind fun same =>
          if same then (coagulationMarkerGroup markers).map (· :: []) else some []
        | _ => some []
      let alp ← c.alpGroups
      return morphology.flatten ++ chemistry.flatten ++ coagulation ++ alp

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
    else c.excludedJudgmentCandidate)) ++
  c.rows.filterMap (fun p =>
    let test := match p.item with
      | .coagulation i => some (D006.judgmentTest i)
      | .endocrine i => some (D008.judgmentTest i)
      | .alpPag => some (D007.Item.judgmentTest ⟨.late, .alpIsoenzymesPag⟩)
      | .tumorMarker i => some (D009.judgmentTest i)
      | .hepatitis i => some (D013.judgmentTest i)
      | .specificIge _ => some (D015.judgmentTest .specificIge false)
      | .viralTiter _ => some (D012.judgmentTest .viralTiter)
      | .classTiter _ _ => some (D012.judgmentTest .classSpecificTiter)
      | .autoantibody i => some (D014.judgmentTest i)
      | _ => none
    test.map fun t => c.test p.id t
      (if retained choices p.id then some true else c.excludedJudgmentCandidate))

/-- 区分と採血IDから包括キーを求める。 -/
def Input.assignment (p : Performance Item) : Option BundleKey :=
  match p.item with
  | .chemistry _ => bundleKey ⟨7, 0, .draw⟩ p
  | .coagulation _ => bundleKey ⟨6, 0, .draw⟩ p
  | .endocrine _ => bundleKey ⟨8, 0, .draw⟩ p
  | .tumorMarker _ => bundleKey ⟨9, 0, .draw⟩ p
  | .hepatitis _ => bundleKey ⟨13, 0, .draw⟩ p
  | .specificIge _ => bundleKey ⟨15, 13, .draw⟩ p
  | .viralTiter _ => bundleKey ⟨12, 11, .specimen⟩ p
  | .classTiter _ _ => bundleKey ⟨12, 46, .specimen⟩ p
  | .autoantibody _ => bundleKey ⟨14, 0, .day⟩ p
  | _ => none

theorem assignment_disjoint (c : Input) {row : Performance Item} {a b : BundleKey}
    (ha : row ∈ assignedMembers Input.assignment c.rows a)
    (hb : row ∈ assignedMembers Input.assignment c.rows b) : a = b :=
  assigned_members_disjoint _ _ ha hb

private def Item.extraBundle : Item → Bool
  | .coagulation _ | .endocrine _ | .tumorMarker _ | .hepatitis _ | .specificIge _
  | .viralTiter _ | .classTiter _ _ | .autoantibody _ => true
  | _ => false

private def distinctItems (rows : List (Performance α)) [BEq α] : Bool :=
  let items := rows.map Performance.item
  items.length == items.eraseDups.length

private def Input.coagulationContext (c : Input) (choices : List GroupChoice)
    (p : Performance D006.Item) : D006.Context :=
  { performance := p
    simultaneousSurvey := some c.coagulation
    principalPerformance := if retained choices p.id then some p.id else none }

private def Input.extraBundlePoints (c : Input) (choices : List GroupChoice) :
    Option (List Nat) := do
  let rows := c.rows.filter (·.item.extraBundle)
  let viral := rows.any fun p => match p.item with
    | .viralTiter _ => true
    | _ => false
  let classTargets := rows.filterMap fun p => match p.item with
    | .classTiter target _ => some target
    | _ => none
  -- 通知(38)イ・ウの併測範囲が問題となる場合は保留する。
  if (viral && !classTargets.isEmpty) ||
      classTargets.length != classTargets.eraseDups.length then none else
  let keys ← rows.mapM Input.assignment
  let kept := rows.filter fun p => retained choices p.id
  let points ← keys.eraseDups.mapM fun key => do
    let members := assignedMembers Input.assignment kept key
    match members with
    | [] => some []
    | anchor :: _ =>
      match anchor.item with
      | .coagulation item =>
        let typed := members.filterMap fun p => match p.item with
          | .coagulation i => some ({ p with item := i } : Performance D006.Item)
          | _ => none
        if !distinctItems typed then none else
          let rows := typed.map (c.coagulationContext choices)
          let draw ← coagulationDraw { anchor with item := item } rows
          -- 対象の五項目はフィブリノゲン迅速測定加算の対象外。
          return [D006.drawPoints draw]
      | .endocrine _ =>
        let typed := members.filterMap fun p => match p.item with
          | .endocrine i => some ({ p with item := ⟨i, .blood⟩ } : Performance D008.BundleItem)
          | _ => none
        if !distinctItems typed then none else
          let items ← endocrineDraw c.site key.identity none typed
          return [D008.bundlePoints items]
      | .tumorMarker item =>
        let typed := members.filterMap fun p => match p.item with
          | .tumorMarker i => some ({ p with item := i } : Performance D009.Item)
          | _ => none
        if !distinctItems typed then none else
          let rows := typed.map fun p => ({ performance := p, route := .d009, bloodSpecimen := true } : D009.Context)
          let draw ← tumorMarkerDraw { anchor with item := item } rows (fun _ => none)
          return [D009.bundlePoints draw.items]
      | .hepatitis item =>
        let typed := members.filterMap fun p => match p.item with
          | .hepatitis i => some ({ p with item := i } : Performance D013.Item)
          | _ => none
        if !distinctItems typed then none else
          let rows := typed.map fun p => ({ performance := p } : D013.Context)
          let draw ← hepatitisDraw { anchor with item := item } rows
          return [SpecimenTests.groupedBase .hepatitis draw.count draw.standardSum]
      | .specificIge _ =>
        let rows ← members.mapM fun p => do
          let .specificIge antigen := p.item | none
          return (({ p with item := .specificIge } : Performance D015.Item), ← antigen)
        let ids := rows.map Prod.snd
        if ids.eraseDups != ids then none else
          let draw ← specificIgeDraw { anchor with item := .specificIge } rows
          return [SpecimenTests.groupedBase .specificIgE draw.tests.length 0]
      | .viralTiter _ =>
        let rows := members.filterMap fun p => match p.item with
          | .viralTiter t =>
            let test : D012.Context := {
              performance := { p with item := .local .viralTiter }
              target := some t }
            some (test, t)
          | _ => none
        let draw ← viralSpecimen { anchor with item := .local .viralTiter } rows
        return [SpecimenTests.groupedBase .viralAntibodies draw.targetCount 79]
      | .classTiter _ _ =>
        let rows := members.filterMap fun p => match p.item with
          | .classTiter t a =>
            let test : D012.Context := {
              performance := { p with item := .local .classSpecificTiter }
              target := some t
              antibodyClass := some a }
            some (test, t)
          | _ => none
        let draw ← classSpecimen { anchor with item := .local .classSpecificTiter } rows
        return [SpecimenTests.groupedBase .classSpecificViralAntibodies draw.targetCount 200]
      | .autoantibody _ =>
        let typed := members.filterMap fun p => match p.item with
          | .autoantibody i => some ({ p with item := i } : Performance D014.Item)
          | _ => none
        if !c.autoantibodyDayConfirmed || !distinctItems typed then none else
          let rows := typed.map fun p => ({ performance := p } : D014.Context)
          let group ← autoantibodyDay c.site rows
          return [SpecimenTests.groupedBase .autoantibodies group.count group.sum]
      | _ => none
  return points.flatten

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
      let extra ← c.extraBundlePoints choices
      let pag := c.rows.filterMap fun p => match p.item with
        | .alpPag =>
          if retained choices p.id then some (BloodChemistryLate.Item.points .alpIsoenzymesPag) else none
        | _ => none
      let execution := (draws.map fun (_, items) => BloodChemistry.pointsForItems items) ++
        morphology ++ urine ++ extra ++ pag
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

/-- D006の限定項目では、群の適格性を確認すれば、採血の本体点数が
加算込みの既存制約を満たし、他の点数は許されない。 -/
theorem coagulation_projection (g : D006.DrawGroup) (valid : g.Valid)
    (noAddition : ∀ c ∈ g.tests, D006.FibrinogenPrimaryFailure c) :
    D006.Payable g (D006.drawPoints g) ∧
      ∀ q, D006.Payable g q → q = D006.drawPoints g := by
  have zero : ∀ tests : List D006.Context,
      (∀ c ∈ tests, D006.FibrinogenPrimaryFailure c) → D006.Additions tests 0 := by
    intro tests
    induction tests with
    | nil => intro _; rfl
    | cons test rest ih =>
      intro h
      exact ⟨0, 0, (D006.addition_satisfies_iff _ _).2 (.inr ⟨rfl, .inl (h test (by simp))⟩),
        ih (fun c hc => h c (by simp [hc])), rfl⟩
  have payable : D006.Payable g (D006.drawPoints g) := by
    refine ⟨⟨_, _, D006.drawPoints g⟩, 0, (D006.draw_satisfies_iff _ _).2 ⟨valid, rfl, rfl, rfl⟩,
      zero _ noAddition, by simp⟩
  obtain ⟨_, _, unique⟩ := coagulationDraw_points g valid
    (fun c hc => .inr (.inl (noAddition c hc)))
  exact ⟨payable, fun q h => (unique q h).trans (unique _ payable).symm⟩

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

-- 複数区分の合成例はカーネルで簡約して検査する。
section
set_option maxRecDepth 4096
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

private def multiDivision : Input :=
  let coagulation := [D006.Item.antithrombinActivity, .pic, .dDimer, .tat, .prothrombinFragment]
  let hepatitis := [D013.Item.hbeAntigen, .hbeAntibody, .hcvAntibody]
  { twoGroups with rows := twoGroups.rows ++
      (coagulation.zipIdx.map fun (i, j) =>
        { id := j + 30, site, item := .coagulation i, draw := some 1, simultaneous := some 2 }) ++
      (hepatitis.zipIdx.map fun (i, j) =>
        { id := j + 40, site, item := .hepatitis i, draw := some 1 }) }

example :
    (multiDivision.groups.map List.length,
      (multiDivision.withoutAdditions (some [1, 20, 33])).map Breakdown.judgment,
      total multiDivision (some [1, 20, 33])) =
    (some 3, some 413, some 1479) := by decide

example :
    (multiDivision.prepare (some [1, 20, 33])).map (fun (day, _) =>
      SpecimenJudgment.allCategories.filter day.judgment.day.hasTest) =
    some [.hematological, .biochemicalI, .immunological] := by decide

example : total { multiDivision with judgment := { multiDivision.judgment with day :=
    { multiDivision.judgment.day with performances := ⟨{ site.monthScope with patient := 4 }, []⟩ } } }
    (some [1, 20, 33]) = none := by decide

example : total { multiDivision with judgment := { multiDivision.judgment with day :=
    { multiDivision.judgment.day with claims := ⟨⟨{ site.monthScope with patient := 4 }, []⟩, by simp⟩ } } }
    (some [1, 20, 33]) = none := by decide

example : total { multiDivision with rows := multiDivision.rows.map fun p =>
    if p.id == 30 then { p with draw := none } else p } (some [1, 20, 33]) = none := by decide

example : total multiDivision none = none := by decide

example : total { multiDivision with rows := multiDivision.rows ++
    [{ id := 99, site, item := .other ("D015", "specificIge") }] } (some [1, 20, 33]) =
    none := by decide

example :
    let rows : List (Performance Item) := (List.range 14).map fun i =>
      { id := i, site, item := .specificIge (some i), draw := some 1 }
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [1430] := by decide

example :
    let row : Performance Item := { id := 1, site, item := .specificIge none, draw := some 1 }
    total { base with rows := [row] } none = none := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .endocrine .fsh, draw := some 1 },
       { id := 2, site, item := .endocrine .lh, draw := some 1 },
       { id := 3, site, item := .endocrine .cortisol, draw := some 1 },
       { id := 4, site, item := .tumorMarker ⟨3, 0⟩, draw := some 1 },
       { id := 5, site, item := .tumorMarker ⟨4, 0⟩, draw := some 1 }]
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [410, 230] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .viralTiter .rubella, specimen := some 1 },
       { id := 2, site, item := .viralTiter .rubella, specimen := some 1 },
       { id := 3, site, item := .viralTiter .measles, specimen := some 1 }]
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [158] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .classTiter .rubella .igm, specimen := some 1 },
       { id := 2, site, item := .classTiter .measles .igg, specimen := some 1 },
       { id := 3, site, item := .classTiter .mumps .igg, specimen := some 1 }]
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [400] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .autoantibody .rnpQuant },
       { id := 2, site, item := .autoantibody .smQuant },
       { id := 3, site, item := .autoantibody .ssbQuant }]
    (({ base with rows, autoantibodyDayConfirmed := true } : Input).withoutAdditions none).map
      Breakdown.execution = some [490] ∧
    total { base with rows } none = none := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .alpPag, draw := some 1 },
       { id := 2, site, item := .endocrine .bap, draw := some 1 }]
    let c := { base with rows, alpPaired := some true }
    c.groups.map (List.map ChoiceGroup.members) = some [[1, 2]] ∧
      (c.withoutAdditions (some [1])).map Breakdown.execution = some [180] ∧
      (c.withoutAdditions (some [2])).map Breakdown.execution = some [D008.Item.bap.points] ∧
      total { c with alpPaired := none } (some [1]) = none := by decide

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

end

end Sanri.MedicalFee.SpecimenRawDay
