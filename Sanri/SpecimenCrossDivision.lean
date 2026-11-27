import Sanri.SpecimenOutpatientDay
import Sanri.SpecimenJudgmentRouting
import Sanri.HistoryConnections

namespace Sanri.MedicalFee.SpecimenCrossDivision

open Sanri.History Sanri.Logic

/-- 適用条件を確認した併施群。実施IDと、残す実施の件数を渡す。 -/
structure ChoiceGroup where
  source : SourceRef
  members : List Nat
  count : Nat
  deriving DecidableEq

structure GroupChoice where
  group : ChoiceGroup
  selected : List Nat

def GroupChoice.Valid (c : GroupChoice) : Prop :=
  c.group.members.Nodup ∧ c.selected.Nodup ∧
    c.selected.length = c.group.count ∧ ∀ id ∈ c.selected, id ∈ c.group.members

def Agree (choices : List GroupChoice) : Prop :=
  ∀ a ∈ choices, ∀ b ∈ choices, ∀ id ∈ a.group.members, id ∈ b.group.members →
    (id ∈ a.selected ↔ id ∈ b.selected)

def Realizes (choices : List GroupChoice) (keep : Nat → Prop) : Prop :=
  ∀ c ∈ choices, ∀ id ∈ c.group.members, (keep id ↔ id ∈ c.selected)

/-- 共通の実施に対する各選択が一致すれば、一日の選択へ合成できる。
どの群にも属さない実施は、この選択による除外を受けない。 -/
theorem exists_selection_iff (choices : List GroupChoice) :
    (∃ keep : Nat → Prop, Realizes choices keep) ↔ Agree choices := by
  constructor
  · rintro ⟨keep, h⟩ a ha b hb id ia ib
    exact (h a ha id ia).symm.trans (h b hb id ib)
  · intro agree
    refine ⟨fun id => (∀ g ∈ choices, id ∉ g.group.members) ∨
      (∃ g ∈ choices, id ∈ g.selected ∧ id ∈ g.group.members), ?_⟩
    intro c hc id hid
    constructor
    · rintro (outside | ⟨g, hg, hs, hm⟩)
      · exact (outside c hc hid).elim
      · exact (agree g hg c hc id hm hid).mp hs
    · intro hs
      exact Or.inr ⟨c, hc, hs, hid⟩

def GroupChoice.rule (c : GroupChoice) : Rule Unit (Nat → Prop) :=
  ⟨c.group.source.location, c.group.source, fun _ keep =>
    c.Valid ∧ ∀ id ∈ c.group.members, (keep id ↔ id ∈ c.selected)⟩

theorem choice_rules_satisfiable (choices : List GroupChoice)
    (valid : ∀ c ∈ choices, c.Valid) :
    SatisfiableAt (choices.map GroupChoice.rule) () ↔ Agree choices := by
  rw [← exists_selection_iff choices]
  constructor
  · rintro ⟨keep, h⟩
    exact ⟨keep, fun c hc => (h c.rule (List.mem_map.mpr ⟨c, hc, rfl⟩)).2⟩
  · rintro ⟨keep, h⟩
    refine ⟨keep, ?_⟩
    intro rule hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact ⟨valid c hc, h c hc⟩

def retained (choices : List GroupChoice) (id : Nat) : Bool :=
  choices.all fun c => !c.group.members.contains id || c.selected.contains id

theorem retained_iff (choices : List GroupChoice) (agree : Agree choices) :
    Realizes choices (fun id => retained choices id = true) := by
  intro c hc id hid
  simp only [retained, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, List.contains_iff_mem]
  constructor
  · intro h
    exact (h c hc).resolve_left (by simpa using hid)
  · intro hs g hg
    by_cases hm : id ∈ g.group.members
    · exact Or.inr ((agree c hc g hg id hid hm).mp hs)
    · exact Or.inl (by simpa using hm)

inductive BundleUnit where
  | draw | specimen | day
  deriving DecidableEq, Repr

/-- 準用の行き先と適用単位を確認した包括区分。 -/
structure BundleRoute where
  division : Nat
  subgroup : Nat
  unit : BundleUnit
  deriving DecidableEq, Repr

structure BundleKey where
  route : BundleRoute
  site : Site
  identity : Nat
  deriving DecidableEq, Repr

def bundleKey (route : BundleRoute) (p : Performance α) : Option BundleKey := do
  let identity ← match route.unit with
    | .draw => p.draw
    | .specimen => p.specimen
    | .day => some 0
  return ⟨route, p.site, identity⟩

def assignedMembers (assignment : Performance α → Option BundleKey)
    (rows : List (Performance α)) (key : BundleKey) : List (Performance α) :=
  rows.filter fun row => assignment row == some key

def bundleMembers (route : Performance α → Option BundleRoute)
    (rows : List (Performance α)) (key : BundleKey) : List (Performance α) :=
  assignedMembers (fun row => route row >>= (bundleKey · row)) rows key

theorem assigned_members_disjoint (assignment : Performance α → Option BundleKey)
    (rows : List (Performance α)) {row : Performance α} {a b : BundleKey}
    (ha : row ∈ assignedMembers assignment rows a) (hb : row ∈ assignedMembers assignment rows b) :
    a = b := by
  simp [assignedMembers] at ha hb
  exact Option.some.inj (ha.2.symm.trans hb.2)

theorem bundle_members_disjoint (route : Performance α → Option BundleRoute)
    (rows : List (Performance α)) {row : Performance α} {a b : BundleKey}
    (ha : row ∈ bundleMembers route rows a) (hb : row ∈ bundleMembers route rows b) :
    a = b :=
  assigned_members_disjoint _ rows ha hb

/-- D004(14)・D008の準用分を、確認済みの当日最初の採血に合流させる。
準用分の実施レコードの採血IDはそのまま保持する。 -/
def d008BundleAssignment (site : Site) (firstDraw : Option Nat)
    (reference : Performance α → Bool) (row : Performance α) : Option BundleKey :=
  let route : BundleRoute := ⟨8, 0, .draw⟩
  if row.site != site then none
  else if reference row then firstDraw.map (fun id => ⟨route, site, id⟩)
  else bundleKey route row

theorem d008_reference_assignment (row : Performance α) (reference : Performance α → Bool)
    (firstDraw : Nat) (h : reference row = true) :
    d008BundleAssignment row.site (some firstDraw) reference row =
      some ⟨⟨8, 0, .draw⟩, row.site, firstDraw⟩ := by
  simp [d008BundleAssignment, h]

/-- 個別制約または包括制約の評価を、日次の中で使うための射影。 -/
structure Charge where
  permits : Nat → Prop
  determines : ∃ p, permits p ∧ ∀ q, permits q → q = p

def Charge.fromProjection (rules : List (Rule C R)) (c : C)
    (h : DeterminesAt rules c) (project : R → Nat) : Charge :=
  ⟨fun p => ∃ r, Satisfies rules c r ∧ project r = p, by
    obtain ⟨⟨r, hr⟩, unique⟩ := h
    refine ⟨project r, ⟨r, hr, rfl⟩, ?_⟩
    rintro q ⟨other, ho, hq⟩
    exact hq.symm.trans (congrArg project (unique other r ho hr))⟩

def Charge.fromRules (rules : List (Rule C Nat)) (c : C)
    (h : DeterminesAt rules c) : Charge :=
  fromProjection rules c h id

inductive ChargeList : List Charge → List Nat → Prop where
  | nil : ChargeList [] []
  | cons : charge.permits p → ChargeList charges points →
      ChargeList (charge :: charges) (p :: points)

theorem charges_determine (charges : List Charge) :
    ∃ points, ChargeList charges points ∧
      ∀ other, ChargeList charges other → other = points := by
  induction charges with
  | nil => exact ⟨[], .nil, fun _ h => by cases h; rfl⟩
  | cons charge charges ih =>
    obtain ⟨p, hp, up⟩ := charge.determines
    obtain ⟨ps, hps, ups⟩ := ih
    refine ⟨p :: ps, .cons hp hps, ?_⟩
    intro other h
    cases h with
    | cons hq hqs => simp [up _ hq, ups _ hqs]

structure Day where
  execution : List Charge
  collection : List Charge
  judgment : SpecimenJudgment.OutpatientDay
  additions : SpecimenOutpatientDay.AdditionContext

structure Breakdown where
  execution : List Nat
  collection : List Nat
  judgment : Nat
  additions : SpecimenOutpatientDay.AdditionResult
  total : SpecimenOutpatientDay.Result

def Day.aggregation (c : Day) (r : Breakdown) : SpecimenOutpatientDay.Context :=
  ⟨c.judgment.day.site, r.execution.sum, r.judgment, r.collection,
    r.additions.emergency, r.additions.rapid⟩

def Day.Permits (c : Day) (r : Breakdown) : Prop :=
  ChargeList c.execution r.execution ∧
  ChargeList c.collection r.collection ∧
  c.judgment.PermitsPoints r.judgment ∧
  Satisfies SpecimenOutpatientDay.additionRules c.additions r.additions ∧
  Satisfies SpecimenOutpatientDay.rules (c.aggregation r) r.total

/-- 同じ日について、個別・包括と別算定の候補、判断料・加算の入力を確定した射影。 -/
theorem day_determines (c : Day) (_ : c.additions.site = c.judgment.day.site)
    (judgment : c.judgment.Eligible)
    (additions : DeterminesAt SpecimenOutpatientDay.additionRules c.additions) :
    ∃ r, c.Permits r ∧ ∀ other, c.Permits other → other = r := by
  obtain ⟨e, he, ue⟩ := charges_determine c.execution
  obtain ⟨s, hs, us⟩ := charges_determine c.collection
  obtain ⟨j, hj, uj⟩ := SpecimenJudgment.outpatient_day_determines c.judgment judgment
  obtain ⟨⟨a, ha⟩, ua⟩ := additions
  let subtotal : SpecimenOutpatientDay.Context :=
    ⟨c.judgment.day.site, e.sum, j, s, a.emergency, a.rapid⟩
  refine ⟨⟨e, s, j, a, SpecimenOutpatientDay.assess subtotal⟩,
    ⟨he, hs, hj, ha, (SpecimenOutpatientDay.satisfies_iff ..).mpr rfl⟩, ?_⟩
  rintro ⟨e', s', j', a', total⟩ ⟨he', hs', hj', ha', ht⟩
  have ee : e' = e := ue _ he'
  have es : s' = s := us _ hs'
  have ej : j' = j := uj _ hj'
  have ea : a' = a := ua _ _ ha' ha
  subst e'
  subst s'
  subst j'
  subst a'
  have et : total = SpecimenOutpatientDay.assess subtotal :=
    (SpecimenOutpatientDay.satisfies_iff ..).mp ht
  rw [et]

/-- 選択結果をD005の二件規則へ渡す。適用関係自体は検体ID・併施目的で確認する。 -/
def morphologyPair (a b : Performance BloodMorphology.Item)
    (forMalaria : Bool) (choices : List GroupChoice) : Option BloodMorphology.PairContext := do
  let same ← a.sameSpecimen b
  let selected := [a, b].filter (fun p => retained choices p.id)
  let principal := match selected with
    | [p] => some p.item
    | _ => none
  return ⟨a.item, b.item, same, forMalaria, principal⟩

/-- D005の二件規則を起動する実施群。三件以上を二件群に展開するかは別途確認する。 -/
def morphologyGroups (a b : Performance BloodMorphology.Item)
    (forMalaria : Bool) : Option (List ChoiceGroup) := do
  if a.id = b.id || a.site != b.site then none else
    let pair : BloodMorphology.PairContext := ⟨a.item, b.item, true, forMalaria, none⟩
    let same ← if pair.categoryConflict then a.sameSpecimen b else some false
    let specimen := if same then [BloodMorphology.eosinophilRule.source] else []
    let malaria := if pair.malariaConflict then [BloodMorphology.malariaRule.source] else []
    return (specimen ++ malaria).map fun source => ⟨source, [a.id, b.id], 1⟩

/-- D007注の採血群を既存の項目数点数へ渡す。併施の事実は別の入力で確認する。 -/
def chemistryDraw (choices : List GroupChoice) (rows : List (Performance BloodChemistry.Item))
    (site : Site) (draw : Nat) (context : BloodChemistry.Draw) : Option BloodChemistry.Draw := do
  let sameDay := rows.filter (fun p => p.site == site)
  if sameDay.any (fun p => p.draw.isNone) then none else
    let route : BundleRoute := ⟨7, 0, .draw⟩
    let members := bundleMembers (fun _ => some route) sameDay ⟨route, site, draw⟩
    if members.isEmpty then none else
      return { context with
        performed := (members.filter fun p => retained choices p.id).map Performance.item }

theorem chemistryDraw_points (choices : List GroupChoice)
    (rows : List (Performance BloodChemistry.Item)) (site : Site) (draw : Nat)
    (context projected : BloodChemistry.Draw) (p : Nat)
    (known : chemistryDraw choices rows site draw context = some projected) :
    BloodChemistry.DrawPoints projected p ↔
      (chemistryDraw choices rows site draw context).bind BloodChemistry.points = some p := by
  rw [known]
  exact BloodChemistry.drawPoints_iff _ _

/-- D001・D003の同月の選択は既存の共有条件で評価する。
当日の実施だけで同月の候補が尽くされるという仮定は置かない。 -/
def colitisChoice (urine : D001.Context) (stool : D003.Context)
    (id : Nat) : GroupChoice :=
  ⟨⟨D001.colitisRule.source, [urine.performance.id, stool.performance.id], 1⟩, [id]⟩

theorem colitisChoice_projects (urine : D001.Context) (stool : D003.Context)
    (id : Nat) (h : D003.SharedColitisSelection urine stool id) :
    (retained [colitisChoice urine stool id] urine.performance.id = true ↔
        urine.colitisMonthlySelection) ∧
    (retained [colitisChoice urine stool id] stool.performance.id = true ↔
        stool.pgeMonthlySelection) := by
  obtain ⟨_, _, _, _, _, _, hu, hs⟩ := h
  simp [retained, colitisChoice, hu, hs, eq_comm]

/-- 実施料の選択・包括と、判断料の候補への採用は別に記録する。
採用の確認がない実施を候補から黙って落とさない。 -/
structure DayTest where
  id : Nat
  site : Site
  judgment : SpecimenJudgment.IncludedTest
  judgmentCandidate : Option Bool
  emergency : Option SpecimenOutpatientDay.EmergencyTest
  rapid : Option SpecimenOutpatientDay.RapidTest

def judgmentFromDay (day : SpecimenJudgment.DailyJudgment)
    (rows : List DayTest) : Option SpecimenJudgment.DailyJudgment := do
  let candidates ← rows.filterM DayTest.judgmentCandidate
  return { day with tests := candidates.map DayTest.judgment }

def additionsFromDay (c : SpecimenOutpatientDay.AdditionContext)
    (rows : List DayTest) : SpecimenOutpatientDay.AdditionContext :=
  { c with emergencyTests := rows.filterMap DayTest.emergency
           rapidTests := rows.filterMap DayTest.rapid }

/-- 同じ実施一覧を判断料と加算に射影する。加算候補の none は候補なしの確認を表す。 -/
def Day.withTests (c : Day) (rows : List DayTest) : Option Day := do
  if rows.any (fun row => row.site != c.judgment.day.site) ||
      (rows.map DayTest.id).eraseDups != rows.map DayTest.id then none else
    let day ← judgmentFromDay c.judgment.day rows
    return { c with judgment := { c.judgment with day }
                    additions := additionsFromDay c.additions rows }

def collectionCharge (c : SpecimenCollection.Context)
    (h : ∃ p, SpecimenCollection.points c = some p) : Charge :=
  ⟨fun p => SpecimenCollection.points c = some p, by
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp, fun _ hq => Option.some.inj (hq.symm.trans hp)⟩⟩

private def sampleSite : Site := ⟨1, 2, ⟨⟨2026, 10⟩, ⟨22, by decide⟩⟩⟩

private def differentialGroup : ChoiceGroup :=
  ⟨BloodMorphology.eosinophilRule.source, [1, 2], 1⟩

private def sampleChoices (id : Nat) : List GroupChoice := [⟨differentialGroup, [id]⟩]

private def differentialPair (id : Nat) : Option BloodMorphology.PairContext :=
  morphologyPair
    { id := 1, site := sampleSite, item := .eosinophilCount, specimen := some 3 }
    { id := 2, site := sampleSite, item := .automatedDifferential, specimen := some 3 }
    false (sampleChoices id)

example : (differentialPair 1).bind (·.principal) = some .eosinophilCount ∧
    (differentialPair 2).bind (·.principal) = some .automatedDifferential :=
  ⟨rfl, rfl⟩

example : BloodMorphology.Item.eosinophilCount.basePoints ≠
    BloodMorphology.Item.automatedDifferential.basePoints := by decide

example : (bundleKey ⟨7, 0, .draw⟩
    ({ id := 1, site := sampleSite, item := () } : Performance Unit)) = none := rfl

private def conflictingChoices : List GroupChoice :=
  [⟨differentialGroup, [1]⟩,
   ⟨{ differentialGroup with members := [1, 8] }, [8]⟩]

/-- 両群で共有する実施1の指定が食い違う合成例。 -/
example : ¬ ∃ keep, Realizes conflictingChoices keep := by
  rw [exists_selection_iff]
  intro agree
  have contradiction := agree
    ⟨differentialGroup, [1]⟩ (by simp [conflictingChoices])
    ⟨{ differentialGroup with members := [1, 8] }, [8]⟩ (by simp [conflictingChoices])
    1 (by simp [differentialGroup]) (by simp)
  simp at contradiction

private def monthly : SpecimenJudgment.DailyJudgment :=
  { site := sampleSite
    tests := [
      ⟨BloodMorphology.Item.eosinophilCount.judgmentTest false, false, false, none, none⟩,
      ⟨D007.Item.judgmentTest ⟨.draw, .bun⟩, false, false, none, none⟩]
    coveredByD027 := false
    claims := ⟨⟨sampleSite.monthScope, []⟩, by simp⟩
    performances := ⟨sampleSite.monthScope, []⟩ }

private def additionSample : SpecimenOutpatientDay.AdditionContext :=
  ⟨sampleSite, .none, [], [], some false, some [], false⟩

private def chemistrySample : Option BloodChemistry.Draw :=
  let rows : List (Performance BloodChemistry.Item) :=
    [⟨3, sampleSite, .bun, some 5, none, none, none⟩,
     ⟨4, sampleSite, .uricAcid, some 5, none, none, none⟩,
     ⟨5, sampleSite, .glucose, some 5, none, none, none⟩,
     ⟨6, sampleSite, .ast, some 5, none, none, none⟩,
     ⟨7, sampleSite, .alt, some 5, none, none, none⟩]
  chemistryDraw [] rows sampleSite 5 { performed := [] }

example : chemistrySample.bind BloodChemistry.points = some 93 := by decide

example : chemistryDraw [] [{ id := 1, site := sampleSite, item := .bun }]
    sampleSite 5 { performed := [] } = none := rfl

private def morphologySample (item : BloodMorphology.Item) : BloodMorphology.Context :=
  { item, cellClasses := some [.lymphocyte, .monocyte, .neutrophil, .eosinophil, .basophil] }

private def sampleDay : Day :=
  let chemistry := [.bun, .uricAcid, .glucose, .ast, .alt]
  let morphology := morphologySample .eosinophilCount
  ⟨[Charge.fromRules [BloodChemistry.pointsRule] chemistry
      (BloodChemistry.determines_points chemistry),
    Charge.fromProjection BloodMorphology.individualRules morphology
      (BloodMorphology.individual_determines morphology _ _ rfl) (fun p => p.1 + p.2)], [],
    ⟨monthly, true, .outpatient, none, none, none⟩, additionSample⟩

example :
    (morphologySample .eosinophilCount).item.basePoints + 93 ≠
      (morphologySample .automatedDifferential).item.basePoints + 93 := by decide

example : ∃ r, sampleDay.Permits r ∧ ∀ other, sampleDay.Permits other → other = r := by
  apply day_determines sampleDay rfl
  · refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [sampleDay, monthly, SpecimenJudgment.DailyJudgment.Known,
        SpecimenJudgment.DailyJudgment.coverageResolved, SpecimenJudgment.IncludedTest.separateEligibility]
      decide
    · simp [sampleDay]
    · simp [sampleDay]
    · simp [sampleDay]
  · exact SpecimenOutpatientDay.additions_determine additionSample
      (by intro h; cases h) (by intro h; cases h)

example : ({ monthly with
    claims := ⟨⟨{ sampleSite.monthScope with patient := 2 }, []⟩, by simp⟩
  } : SpecimenJudgment.DailyJudgment).points = none := by decide

end Sanri.MedicalFee.SpecimenCrossDivision
