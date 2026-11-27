import Sanri.SpecimenOutpatientDay
import Sanri.SpecimenJudgmentRouting
import Sanri.HistoryConnections
import Sanri.GlycemicTests

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

theorem ChoiceGroup.valid_single (g : ChoiceGroup) (distinct : g.members.Nodup)
    (count : g.count = 1) {id : Nat} (member : id ∈ g.members) :
    (GroupChoice.mk g [id]).Valid := by
  simpa [GroupChoice.Valid, count] using And.intro distinct member

theorem ChoiceGroup.exists_single (g : ChoiceGroup) (distinct : g.members.Nodup)
    (count : g.count = 1) (nonempty : g.members ≠ []) :
    ∃ c : GroupChoice, c.group = g ∧ c.Valid := by
  obtain ⟨id, member⟩ := List.exists_mem_of_ne_nil g.members nonempty
  exact ⟨⟨g, [id]⟩, rfl, g.valid_single distinct count member⟩

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

/-- D001(10)・D004(14)の準用分を確認済みの当日最初の採血に合流させる。
準用分の実施レコードの採血IDはそのまま保持する。 -/
def firstBloodBundleAssignment (route : BundleRoute) (site : Site) (firstDraw : Option Nat)
    (reference : Performance α → Bool) (row : Performance α) : Option BundleKey :=
  if row.site != site then none
  else if reference row then firstDraw.map (fun id => ⟨route, site, id⟩)
  else bundleKey route row

def d008BundleAssignment (site : Site) (firstDraw : Option Nat)
    (reference : Performance α → Bool) (row : Performance α) : Option BundleKey :=
  firstBloodBundleAssignment ⟨8, 0, .draw⟩ site firstDraw reference row

theorem d008_reference_assignment (row : Performance α) (reference : Performance α → Bool)
    (firstDraw : Nat) (h : reference row = true) :
    d008BundleAssignment row.site (some firstDraw) reference row =
      some ⟨⟨8, 0, .draw⟩, row.site, firstDraw⟩ := by
  simp [d008BundleAssignment, firstBloodBundleAssignment, h]

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

private def selectionNotice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def jointFluidSource := selectionNotice "PDF334頁 D004(1)"
private def csfRatioSource := selectionNotice "PDF335頁 D004(13)イ"

/-- D004(1)の併施を確認した二件。一連の回数枠は区分側で別に評価する。 -/
def jointFluidGroup (joint : Performance D004.Item) (bacteria : D017.Context) :
    Option ChoiceGroup :=
  let smear := bacteria.performance
  if joint.item = .jointFluid && joint.id != smear.id &&
      joint.site.patient == smear.site.patient && joint.site.institution == smear.site.institution then
    some ⟨jointFluidSource, [joint.id, smear.id], 1⟩
  else none

/-- D004(13)イ。併施と確認した記録を使用し、アの成分同時測定とは区別する。 -/
def csfRatioGroup (anchor : Performance D004.Item) (rows : List (Performance D004.Item)) :
    Option ChoiceGroup :=
  let ids := rows.map Performance.id
  if rows.contains anchor && ids.eraseDups == ids &&
      ((rows.map Performance.item).eraseDups.length ≥ 2) &&
      rows.all (fun row =>
        row.site.patient == anchor.site.patient && row.site.institution == anchor.site.institution &&
        ([D004.Item.phosphoTau, .amyloidRatio, .phosphoTauAmyloidRatio]).contains row.item) then
    some ⟨csfRatioSource, ids, 1⟩
  else none

/-- 実施群の照会が完了した場合にのみ採否を渡す。 -/
def punctureSelectionInput (row : Performance D004.Item) (c : D004.Context)
    (choices : Option (List GroupChoice)) : Option D004.Context := do
  if row.item != c.item then none else
    let selectedBy (source : SourceRef) :=
      choices.map fun cs => retained (cs.filter (·.group.source == source)) row.id
    return { c with jointAloneOrPrincipalAgainstD017 := selectedBy jointFluidSource
                    aloneOrPrincipalAmongTauRatios := selectedBy csfRatioSource }

private def hematologicTests : List D004Tumor.OtherTest :=
  [.d004_2_1, .d006_2, .d006_6, .d006_14, .d006_16]

/-- 患者の暦月内の造血器関連の群。D004-2の実施がない月にも適用する。
同一区分の反復しかない場合の回数制限は各区分で評価する。 -/
def hematologicMonthlyGroup (site : Site) (institution : Option Nat)
    (survey : Snapshot (Performance D004Tumor.OtherTest)) : Option (List ChoiceGroup) := do
  if institution.isSome && institution != some site.institution then none else
  let rows ← survey.select Performance.site ⟨site.patient, institution, .month site.date.month⟩
    (fun p => hematologicTests.contains p.item)
  let ids := rows.map Performance.id
  if ids.eraseDups != ids then none
  else if (rows.map Performance.item).eraseDups.length < 2 then some []
  else some [⟨D004Tumor.hematologicRule.source, ids, 1⟩]

/-- D004-2(7)(8)の相手を、同月の確認範囲から取得する。 -/
def tumorMonthlyGroups (c : D004Tumor.Context) (institution : Option Nat)
    (survey : Snapshot (Performance D004Tumor.OtherTest)) : Option (List ChoiceGroup) := do
  let site := c.performance.site
  if institution.isSome && institution != some site.institution then none
  else if c.item.number != 1 then some []
  else
    let scope : Scope := ⟨site.patient, institution, .month site.date.month⟩
    let counterpartGroup (source : SourceRef) (items : List D004Tumor.OtherTest) :
        Option (List ChoiceGroup) := do
      let performed ← survey.select Performance.site scope (fun p => items.contains p.item)
      let ids := c.performance.id :: performed.map Performance.id
      if ids.eraseDups != ids then none
      else if performed.isEmpty then some []
      else some [⟨source, ids, 1⟩]
    let tumor : Performance D004Tumor.OtherTest := { c.performance with item := .d004_2_1 }
    let hematologic ← hematologicMonthlyGroup site institution
      { survey with entries := if survey.entries.contains tumor then survey.entries
                               else tumor :: survey.entries }
    let egfr ← if c.item == .drugAid && c.cancer == .lung && c.assay == some .egfr then
        counterpartGroup D004Tumor.egfrRule.source [.d006_12, .d006_24]
      else some []
    return hematologic ++ egfr

/-- 確認済みの月間履歴と共有採否を、D004-2側の照会入力に渡す。 -/
def tumorMonthlyInput (c : D004Tumor.Context) (institution : Option Nat)
    (survey : Snapshot (Performance D004Tumor.OtherTest))
    (choices : List GroupChoice) : D004Tumor.Context :=
  let principal (_ : D004Tumor.OtherTest) (other : Nat) :=
    let applicable := choices.filter fun g =>
      (g.group.source == D004Tumor.hematologicRule.source ||
        g.group.source == D004Tumor.egfrRule.source) &&
      g.group.members.contains c.performance.id && g.group.members.contains other
    if applicable.isEmpty then none else some (retained applicable c.performance.id)
  { c with monthlySelection := some ⟨survey, institution, principal⟩ }

/-- 自分の実施を相手側の照会から除き、共通の採否を区分の月間入力に渡す。 -/
def hematologicMonthlyInput (row : Performance D004Tumor.OtherTest)
    (institution : Option Nat) (survey : Snapshot (Performance D004Tumor.OtherTest))
    (choices : List GroupChoice) : D004Tumor.MonthlySelection :=
  let counterparts := survey.entries.filter (·.id != row.id)
  let principal (item : D004Tumor.OtherTest) (id : Nat) :=
    if !hematologicTests.contains item then none else
      let applicable := choices.filter fun g =>
        g.group.source == D004Tumor.hematologicRule.source &&
          g.group.members.contains row.id && g.group.members.contains id
      if applicable.isEmpty then none else some (retained applicable row.id)
  ⟨{ survey with entries := counterparts }, institution, principal⟩

private def tumorCombination (c : D004Tumor.Context) (kind : D004Tumor.Combination) :
    Option (SourceRef × List D004Tumor.OtherTest) :=
  match kind with
  | .alk =>
    if c.item == .drugAid && c.cancer == .lung && c.assay == some .alkFusion then
      some (D004Tumor.alkRule.source, [.d006_24, .n002_6, .n005_2])
    else none
  | .her2 =>
    if c.item == .drugAid && c.cancer == .breast && c.assay == some .her2 then
      some (D004Tumor.her2Rule.source, [.n005])
    else none
  | .brca =>
    if ([D004Tumor.Cancer.ovarianClearCell, .otherOvarian, .prostate]).contains c.cancer &&
        ((c.item == .drugAid && c.assay == some .msi) ||
          (c.item == .complex && c.assay.any ([D004Tumor.Assay.ntrkFusion, .mutationBurden].contains ·))) then
      some (D004Tumor.brcaRule.source, [.d006_18_1])
    else none

/-- D004-2(9)〜(11)。相手の併施範囲を確認した一覧を使う。 -/
def tumorCombinedGroup (c : D004Tumor.Context) (kind : D004Tumor.Combination)
    (rows : List (Performance D004Tumor.OtherTest)) : Option ChoiceGroup := do
  let (source, counterparts) ← tumorCombination c kind
  let members := c.performance.id :: rows.map Performance.id
  if rows.isEmpty || members.eraseDups != members ||
      !rows.all (fun p => counterparts.contains p.item &&
        p.site.patient == c.performance.site.patient) then none
  else some ⟨source, members, 1⟩

def tumorCombinedInput (c : D004Tumor.Context)
    (confirmed : D004Tumor.Combination → Option (List (Performance D004Tumor.OtherTest)))
    (choices : List GroupChoice) : D004Tumor.Context :=
  { c with combinations := fun kind => do
      let rows ← confirmed kind
      if rows.isEmpty then some [] else
        let group ← tumorCombinedGroup c kind rows
        let selected := choices.find? fun choice =>
          choice.group.source == group.source && choice.group.members.isPerm group.members &&
          choice.group.count == group.count
        return rows.map fun p =>
          ⟨p.item, selected.map fun _ => retained choices c.performance.id⟩ }

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

/-- D001(3)と(9)イの選択を、確認済みの同時・併施群から区分入力に渡す。 -/
def urineSpecialSelectionInput (c : D001.Context) (choices : List GroupChoice) :
    D001.Context :=
  let selectedBy (source : SourceRef) :=
    retained (choices.filter fun choice => choice.group.source == source) c.performance.id = true
  { c with renalSimultaneousSelection := selectedBy D001.renalRule.source
           lfabpNgalSelection := selectedBy D001.lfabpNgalRule.source }

/-- D003(4)ウ。同じ目的のD313を収録した実施履歴を照会する。 -/
def colonoscopyGroup (stool : D003.Context) (institution : Option Nat)
    (survey : Snapshot (Performance Unit)) : Option (List ChoiceGroup) := do
  let test := stool.performance
  if test.item != .calprotectin then some []
  else if stool.purpose.isNone || (institution.isSome && institution != some test.site.institution) then none
  else
    let exams ← survey.select Performance.site
      ⟨test.site.patient, institution, .month test.site.date.month⟩ (fun _ => true)
    let members := test.id :: exams.map Performance.id
    if members.eraseDups != members then none
    else if exams.isEmpty then some []
    else some [⟨D003.colonoscopyRule.source, members, 1⟩]

def colonoscopyInput (choices : List GroupChoice) (stool : D003.Context) : D003.Context :=
  let applicable := choices.filter (·.group.source == D003.colonoscopyRule.source)
  { stool with colonoscopyMonthlySelection := retained applicable stool.performance.id = true }

/-- D002(5)・D002-2(2)。併施の適用範囲を確認した鏡検法とフロー法を受ける。 -/
def sedimentMethodGroup (microscopy flow : UrineSediment.Context) : Option ChoiceGroup :=
  if microscopy.performance.item != .microscopy || flow.performance.item != .flow ||
    microscopy.performance.id == flow.performance.id ||
    microscopy.performance.site.patient != flow.performance.site.patient ||
    microscopy.performance.site.institution != flow.performance.site.institution then none
  else some ⟨UrineSediment.microscopySelectionRule.source,
    [microscopy.performance.id, flow.performance.id], 1⟩

def sedimentMethodInput (microscopy flow : UrineSediment.Context) (selected : Nat)
    (c : UrineSediment.Context) : Option UrineSediment.Context := do
  let group ← sedimentMethodGroup microscopy flow
  if !(group.members.contains c.performance.id) then none else
    let method ← if selected = microscopy.performance.id then some .microscopy
      else if selected = flow.performance.id then some .flow else none
    return { c with otherSedimentPerformed := some true, chosenSedimentMethod := some method }

/-- 告示D017末尾注。同一検体を確認したD017と尿沈渣の主検査を両側へ渡す。 -/
def sedimentBacteriaGroup (sediment : UrineSediment.Context) (bacteria : D017.Context) :
    Option ChoiceGroup :=
  if bacteria.performance.id != sediment.performance.id &&
      bacteria.sameSpecimen sediment.performance == some true then
    some ⟨D017.sedimentChoice.source, [sediment.performance.id, bacteria.performance.id], 1⟩
  else none

def sedimentBacteriaInputs (sediment : UrineSediment.Context) (bacteria : D017.Context)
    (selected : Nat) : Option (UrineSediment.Context × D017.Context) := do
  let group ← sedimentBacteriaGroup sediment bacteria
  if !group.members.contains selected then none else
    let main := if selected = sediment.performance.id then
      UrineFecalTests.MainTest.urineSediment else .d017BacterialMicroscopy
    return ({ sediment with d017 := some (.combined { bacteria.performance with item := () } (some main)) },
      { bacteria with sediment := some (.combined sediment.performance (some main)) })

/-- D002・D002-2・D017を三つの二件群と読む場合の採否制約。
D017の「又は」を三件全体の規則として読む場合は別のモデルになる。 -/
theorem sediment_pairwise_unsatisfiable :
    ¬ ∃ microscopy flow bacteria : Bool,
      microscopy ≠ flow ∧ microscopy ≠ bacteria ∧ flow ≠ bacteria := by decide

example : (∃ a b c : Bool, a ≠ b ∧ a ≠ c) ∧
    (∃ a b c : Bool, a ≠ b ∧ b ≠ c) ∧ (∃ a b c : Bool, a ≠ c ∧ b ≠ c) := by decide

/-- D006(8)イ。同時の確認がない実施を同じ群に入れない。 -/
def coagulationMarkerGroup (rows : List (Performance D006.Item)) : Option ChoiceGroup := do
  let ids := rows.map Performance.id
  if ids.length < 2 || ids.eraseDups != ids then none else
    if rows.all (fun a => decide (a.item ∈ D006.competingMarkers) &&
        rows.all (fun b => a.id == b.id || a.simultaneousWith b == some true)) then
      some ⟨D006.markerCombinationRule.source, ids, 1⟩
    else none

def coagulationMarkerInput (c : D006.Context) (survey : List (Performance D006.Item))
    (group : GroupChoice) : D006.Context :=
  { c with simultaneousSurvey := some survey
           principalPerformance := match group.selected with
             | [id] => some id
             | _ => none }

theorem coagulationMarkerInput_projects (c : D006.Context)
    (survey : List (Performance D006.Item)) (group : ChoiceGroup) (id : Nat)
    (member : c.performance.id ∈ group.members) :
    (coagulationMarkerInput c survey ⟨group, [id]⟩).principalPerformance =
      some c.performance.id ↔ retained [⟨group, [id]⟩] c.performance.id = true := by
  simp [coagulationMarkerInput, retained, member, eq_comm]
/-- D006-15(3)。対象のN004項2を、日付でなく同時実施IDで照合する。 -/
def bladderCytologyGroup (test : Performance D006Oncology.Bladder.Related)
    (cytology : List (Performance D006Oncology.Bladder.Related)) : Option (List ChoiceGroup) := do
  if test.item != .bladderGeneTest || cytology.any (·.item != .cytology) then none else
    let simultaneous ← cytology.filterM test.simultaneousWith
    let ids := test.id :: simultaneous.map Performance.id
    if ids.eraseDups != ids then none
    else if simultaneous.isEmpty then some []
    else some [⟨D006Oncology.Bladder.combinationRule.source, ids, 1⟩]

def bladderCytologyInput (c : D006Oncology.Bladder.Context)
    (cytology : List (Performance D006Oncology.Bladder.Related))
    (choices : List GroupChoice) : Option D006Oncology.Bladder.Context := do
  let _ ← bladderCytologyGroup c.performance cytology
  let simultaneous ← cytology.filterM c.performance.simultaneousWith
  let selected (id : Nat) :=
    let applicable := choices.filter fun g =>
      g.group.source == D006Oncology.Bladder.combinationRule.source &&
      g.group.members.contains c.performance.id && g.group.members.contains id
    if applicable.isEmpty then none else some (retained applicable c.performance.id)
  return { c with simultaneousCytology := some simultaneous, principalOverCytology := selected }

/-- D001(4)イ。併施を確認したD007・D009の膵関連実施を一群にまとめる。 -/
def pancreaticGroup (urine : D001.Context) (chemistry : List (Performance D007.Item))
    (markers : List D009.Context) : Option ChoiceGroup :=
  let p := urine.performance
  let sameProvider (site : Site) :=
    site.patient == p.site.patient && site.institution == p.site.institution
  let ids := p.id :: (chemistry.map Performance.id ++ markers.map (·.performance.id))
  if p.item != .trypsinogen2 || ids.length < 2 || ids.eraseDups != ids ||
      !chemistry.all (fun row => ([⟨.draw, .amylase⟩, ⟨.draw, .lipase⟩, ⟨.further, .amylaseIsoenzymes⟩,
          ⟨.late, .trypsin⟩] : List D007.Item).contains row.item && sameProvider row.site) ||
      !markers.all (fun c => c.performance.item.number == 8 && sameProvider c.performance.site) then none
  else some ⟨D001.pancreaticRule.source, ids, 1⟩

def pancreaticUrineInput (choices : List GroupChoice) (c : D001.Context) : D001.Context :=
  { c with pancreaticSelection := retained (choices.filter fun choice =>
      choice.group.source == D001.pancreaticRule.source) c.performance.id = true }

def pancreaticMarkerInput (choices : List GroupChoice) (c : D009.Context) : D009.Context :=
  { c with pancreaticSelection := retained (choices.filter fun choice =>
      choice.group.source == D001.pancreaticRule.source) c.performance.id = true }

/-- D001とD009の二件の部分モデル。D007側の併施もある場合は適用群全体を確認する。 -/
def pancreaticChoice (urine : D001.Context) (marker : D009.Context) (id : Nat) : GroupChoice :=
  ⟨⟨D001.pancreaticRule.source, [urine.performance.id, marker.performance.id], 1⟩, [id]⟩

theorem pancreaticChoice_projects (urine : D001.Context) (marker : D009.Context)
    (id : Nat) (h : D009.SharedPancreaticSelection urine marker id) :
    (retained [pancreaticChoice urine marker id] urine.performance.id = true ↔
        urine.pancreaticSelection) ∧
    (retained [pancreaticChoice urine marker id] marker.performance.id = true ↔
        marker.pancreaticSelection) := by
  obtain ⟨_, _, _, _, _, hu, hm⟩ := h
  simp [retained, pancreaticChoice, hu, hm, eq_comm]

inductive ChemistryCombination where
  | calcium | ironBinding | cholesterol | protein

/-- D007(2)(3)(5)(7)。適格性と併測を確認した一採血の候補を受ける。
同時を明記する二条項では同時実施IDも照合する。 -/
def chemistryCombinationGroup (kind : ChemistryCombination)
    (rows : List (Performance BloodChemistry.Item)) : Option ChoiceGroup := do
  let (source, items, count, simultaneous) := match kind with
    | .calcium => (BloodChemistry.calciumRule.source, BloodChemistry.calciumGroup, 1, true)
    | .ironBinding => (BloodChemistry.ironBindingRule.source, BloodChemistry.ironBindingGroup, 1, true)
    | .cholesterol => (BloodChemistry.cholesterolRule.source, BloodChemistry.cholesterolGroup, 2, false)
    | .protein => (BloodChemistry.proteinRule.source, BloodChemistry.proteinGroup, 2, false)
  let anchor :: rest := rows | none
  let ids := rows.map Performance.id
  if ids.eraseDups != ids || !(rows.map Performance.item).isPerm items ||
      !rest.all (fun row => anchor.site == row.site && anchor.sameDraw row == some true &&
        (!simultaneous || anchor.simultaneousWith row == some true)) then none
  else some ⟨source, ids, count⟩

/-- D007(9)(12)は残す側を明記する。ケトン体は確認済みの併施を受け、
重炭酸塩と血液ガスでは同一検体の条件も使う。 -/
def chemistryPriorityGroup (first second : Performance BloodChemistryFurther.Item) :
    Option GroupChoice := do
  if first.id = second.id || first.site.patient != second.site.patient ||
      first.site.institution != second.site.institution then none else
    let pair ← match first.item, second.item with
      | .ketoneBodies, .ketoneFractions => some BloodChemistryFurther.Pair.ketones
      | .bicarbonate, .bloodGas =>
        if first.sameSpecimen second = some true then some .bicarbonateAndBloodGas else none
      | _, _ => none
    return ⟨⟨pair.rule.source, [first.id, second.id], 1⟩, [second.id]⟩

/-- D005(9)・D007(14)の三検査の実施履歴。同一患者・機関の暦月を照会する。 -/
def glycemicMonth (site : Site) (survey : Snapshot (Performance GlycemicTests.Item))
    (exception : Option GlycemicTests.Exception) : Option GlycemicTests.Month := do
  let rows ← survey.select Performance.site site.monthScope (fun _ => true)
  return ⟨rows.map fun row => ⟨row.id, row.item⟩, exception⟩

/-- 方法と追加枠を区分側で評価し、解決した算定案を共有選択へ渡す。 -/
def glycemicChoice (month : GlycemicTests.Month) (selection : GlycemicTests.Selection) :
    Option GroupChoice :=
  match GlycemicTests.assess (some month) selection with
  | .resolved principal extra =>
    let ids := principal.id :: (extra.toList.map GlycemicTests.Performance.id)
    some ⟨⟨GlycemicTests.additionalRule.source, month.performed.map GlycemicTests.Performance.id,
      ids.length⟩, ids⟩
  | _ => none

/-- 月間評価から当日のD007項目だけを取り出し、元の採血IDを保持する。 -/
def glycemicChemistryDay (site : Site) (survey : Snapshot (Performance GlycemicTests.Item))
    (exception : Option GlycemicTests.Exception) (selection : GlycemicTests.Selection) :
    Option (List (Performance D007.Item)) := do
  let month ← glycemicMonth site survey exception
  let choice ← glycemicChoice month selection
  return survey.entries.filterMap fun row => do
    if row.site != site || !choice.selected.contains row.id then none else
      let item ← row.item.toD007
      return { row with item }

/-- 各通知の関係を照合した履歴を受け、採否だけを共通選択から射影する。 -/
def endocrineSurvey (choices : List GroupChoice)
    (performed : List (Performance D008.CombinationItem)) : D008.Survey :=
  ⟨performed, ((performed.filter fun p => retained choices p.id).map Performance.id)⟩

def markerSelection (choices : List GroupChoice) (id : Nat)
    (others : List (Performance D009.Companion)) : Option D009.Selection :=
  match ([id] ++ others.map Performance.id).filter (retained choices) with
  | [selected] => some ⟨others, selected⟩
  | _ => none

def infectionCombined (choices : List GroupChoice) (g : D012.Combined) : D012.Combined :=
  { g with selected := some ((g.members.filter fun p => retained choices p.id).map Performance.id) }

def hepatitisSelectionInput (c : D013.Context) (choices : List GroupChoice)
    (survey : List (Performance D013.Item)) : D013.Context :=
  { c with otherPayableLocal := some (survey.filter fun p =>
      p.id != c.performance.id && retained choices p.id) }

def autoantibodySelectionInput (c : D014.Context) (choices : List GroupChoice)
    (survey : List (Performance D014.Item)) : D014.Context :=
  { c with combined := some (survey.map Performance.item,
      (survey.filter fun p => retained choices p.id).map Performance.item) }

def plasmaProteinSelectionInput (c : D015.Context) (choices : List GroupChoice)
    (survey : List (Performance D015.Item)) : D015.Context :=
  { c with otherSelected := some (survey.filter fun p =>
      p.id != c.performance.id && retained choices p.id) }

/-- D018(1)ウ。同一検体の通常培養と簡易培養を照合する。 -/
def cultureChoice (ordinary simple : D018.Context) : Option GroupChoice :=
  if ordinary.item != .simple && simple.item == .simple &&
      ordinary.performance.id != simple.performance.id &&
      ordinary.performance.sameSpecimen simple.performance == some true then
    some ⟨⟨D018.perSpecimen.source, [simple.performance.id], 0⟩, []⟩
  else none

def culturePriority : Rule (D018.Context × D018.Context) GroupChoice :=
  ⟨D018.perSpecimen.id, D018.perSpecimen.source, fun (ordinary, simple) choice =>
    cultureChoice ordinary simple = some choice⟩

theorem culturePriority_determines (ordinary simple : D018.Context) (choice : GroupChoice)
    (applicable : cultureChoice ordinary simple = some choice) :
    DeterminesAt [culturePriority] (ordinary, simple) := by
  refine ⟨⟨choice, ?_⟩, ?_⟩
  · simpa [culturePriority, satisfies_cons, satisfies_nil] using applicable
  · intro a b ha hb
    simp only [satisfies_cons, satisfies_nil, and_true, culturePriority] at ha hb
    exact Option.some.inj (ha.symm.trans hb)

/-- 包括に数えることを確認した実施を、指定の単位のIDで分ける。
対象日にID不明の候補があれば、その群の項目数は未確定とする。 -/
private def contextBundleMembers (route : BundleRoute) (anchor : Performance α)
    (performance : C → Performance α) (rows : List C) : Option (List C) := do
  let key ← bundleKey route anchor
  let sameDay := rows.filter fun c => (performance c).site == anchor.site
  if sameDay.any (fun c => (bundleKey route (performance c)).isNone) then none else
    return sameDay.filter fun c => bundleKey route (performance c) == some key

def geneticTumorDraw (anchor : Performance D004Tumor.Item) (cancer : D004Tumor.Cancer)
    (rows : List D004Tumor.Classified) : Option D004Tumor.Group :=
  let sameCancer := rows.filter fun c => c.test.cancer == cancer
  (contextBundleMembers ⟨4, 2, .draw⟩ anchor (·.test.performance) sameCancer).map
    (⟨anchor, cancer, ·⟩)

theorem geneticTumorDraw_points (g : D004Tumor.Group) (p : D004Tumor.GroupResult) :
    Satisfies D004Tumor.groupRules g p ↔ g.Valid ∧ p = D004Tumor.groupPoints g :=
  D004Tumor.group_satisfies_iff _ _

def geneticTumorCharge (g : D004Tumor.Group) (valid : g.Valid) : Charge :=
  Charge.fromProjection D004Tumor.groupRules g
    (D004Tumor.group_determines g valid) (·.total)

def coagulationDraw (anchor : Performance D006.Item) (rows : List D006.Context) :
    Option D006.DrawGroup :=
  (contextBundleMembers ⟨6, 0, .draw⟩ anchor D006.Context.performance rows).map (⟨anchor, ·⟩)

theorem coagulationDraw_points (g : D006.DrawGroup) (valid : g.Valid)
    (known : ∀ c ∈ g.tests, D006.AddOnKnown c) :
    ∃ p, D006.Payable g p ∧ ∀ q, D006.Payable g q → q = p :=
  D006.payable_determines g valid known

/-- D006-4注2では採取群の他の疾患も保持し、主検査の等級から点数を決める。 -/
def geneticDiseaseDraw (anchor : Performance Nat) (rows : List D006Genetic.Examination)
    (choice : GroupChoice) (c : D006Genetic.Context) : Option D006Genetic.Context := do
  let members ← contextBundleMembers ⟨6, 4, .draw⟩ anchor
    D006Genetic.Examination.performance rows
  let ids := members.map (·.performance.id)
  let [id] := choice.selected | none
  if ids.eraseDups != ids || !ids.isPerm choice.group.members ||
      choice.group.source != D006Genetic.bundleRule.source || choice.group.count != 1 then none else
    let principal ← members.find? fun e => e.performance.id == id
    let grade ← principal.group
    let others := members.filter fun e => e.performance.id != id
    if others.isEmpty then none else
      return { c with principal, item := grade.grade, application := .multiple others
                      principalConfirmed := some true }

def plasmaPanelBundleKey (row : Performance D006PlasmaPanel.DrawItem) : Option BundleKey :=
  bundleKey ⟨6, if row.item.higherGroup then 271 else 270, .draw⟩ row

theorem plasmaPanelBundle_points (xs : List D006PlasmaPanel.Assessed)
    (p : D006PlasmaPanel.DrawPoints) :
    Satisfies D006PlasmaPanel.bundleRules xs p ↔ p = D006PlasmaPanel.bundlePoints xs :=
  D006PlasmaPanel.bundle_iff _ _

/-- D006-27注1・2の一採血評価を日次の実施料へ渡す。 -/
def plasmaPanelCharge (d : D006PlasmaPanel.Draw) (eligible : ∃ xs, d.Assesses xs) : Charge := by
  obtain ⟨existsPoints, uniquePoints⟩ := D006PlasmaPanel.determines_assessed_draw d eligible
  refine ⟨fun total => ∃ p, (∃ xs, d.Assesses xs ∧
    Satisfies D006PlasmaPanel.bundleRules xs p) ∧ p.total = total, ?_⟩
  obtain ⟨p, hp⟩ := existsPoints
  refine ⟨p.total, ⟨p, hp, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact congrArg D006PlasmaPanel.DrawPoints.total (uniquePoints _ _ hq hp)

/-- D007へ準用する尿・穿刺液と、それぞれの採血由来の項目を分ける。 -/
def chemistryDrawWithReferences (site : Site) (draw : Nat) (firstDraw : Option Nat)
    (reference : Performance BloodChemistry.Item → Bool)
    (rows : List (Performance BloodChemistry.Item)) : Option (List BloodChemistry.Item) := do
  let route : BundleRoute := ⟨7, 0, .draw⟩
  let sameDay := rows.filter fun row => row.site == site
  let assignment := firstBloodBundleAssignment route site firstDraw reference
  if sameDay.any (fun row => (assignment row).isNone) then none else
    return (assignedMembers assignment sameDay ⟨route, site, draw⟩).map Performance.item

def chemistryReferenceCharge (items : List BloodChemistry.Item) : Charge :=
  Charge.fromRules [BloodChemistry.pointsRule] items (BloodChemistry.determines_points items)

def endocrineDraw (site : Site) (draw : Nat) (firstDraw : Option Nat)
    (rows : List (Performance D008.BundleItem)) : Option (List D008.BundleItem) := do
  let sameDay := rows.filter fun row => row.site == site
  let assignment := d008BundleAssignment site firstDraw (fun row => row.item.source != .blood)
  if sameDay.any (fun row => (assignment row).isNone) then none else
    return (assignedMembers assignment sameDay ⟨⟨8, 0, .draw⟩, site, draw⟩).map
      Performance.item

theorem endocrineDraw_points (xs : List D008.BundleItem) (p : Nat) :
    Satisfies D008.bundleRules xs p ↔ p = D008.bundlePoints xs :=
  D008.bundle_iff _ _

/-- D009(26)の乳頭分泌液の行き先は、同日の血液群への単一の割当てで渡す。 -/
def tumorMarkerDraw (anchor : Performance D009.Item) (rows : List D009.Context)
    (nippleDraw : Performance D009.Item → Option Nat) : Option D009.Bundle := do
  let route : BundleRoute := ⟨9, 0, .draw⟩
  let key ← bundleKey route anchor
  let sameDay := rows.filter fun c => c.performance.site == anchor.site
  let assign (c : D009.Context) :=
    if c.performance.item.number = 33 then
      (nippleDraw c.performance).map fun id => BundleKey.mk route anchor.site id
    else bundleKey route c.performance
  if sameDay.any (fun c => (assign c).isNone) then none else
    return ⟨anchor, sameDay.filter fun c => assign c == some key⟩

theorem tumorMarkerDraw_points (g : D009.Bundle) (p : Nat) :
    Satisfies D009.bundleRules g.items p ↔ p = D009.bundlePoints g.items :=
  D009.bundle_iff _ _

def viralSpecimen (anchor : Performance D012.RelatedTest)
    (rows : List (D012.Context × D012.Target)) : Option D012.ViralGroup :=
  (contextBundleMembers ⟨12, 11, .specimen⟩ anchor (·.1.performance) rows).map (⟨anchor, ·⟩)

theorem viralSpecimen_points (g : D012.ViralGroup) (p : Nat) :
    Satisfies D012.viralRules g p ↔
      p = SpecimenTests.groupedBase .viralAntibodies g.targetCount 79 :=
  D012.viral_legacy_iff _ _

/-- 同一ウイルスのIgG・IgMの選択を確認した測定を検体IDでまとめる。 -/
def classSpecimen (anchor : Performance D012.RelatedTest)
    (rows : List (D012.Context × D012.Target)) : Option D012.ClassGroup :=
  (contextBundleMembers ⟨12, 46, .specimen⟩ anchor (·.1.performance) rows).map (⟨anchor, ·⟩)

theorem classSpecimen_points (g : D012.ClassGroup) (p : Nat) :
    Satisfies D012.classGroupRules g p ↔
      p = SpecimenTests.groupedBase .classSpecificViralAntibodies g.targetCount 200 :=
  D012.class_group_legacy_iff _ _

def hepatitisDraw (anchor : Performance D013.Item) (rows : List D013.Context) :
    Option D013.DrawGroup :=
  (contextBundleMembers ⟨13, 0, .draw⟩ anchor D013.Context.performance rows).map (⟨anchor, ·⟩)

theorem hepatitisDraw_points (g : D013.DrawGroup) (p : Nat) :
    Satisfies D013.bundleRules g p ↔
      p = SpecimenTests.groupedBase .hepatitis g.count g.standardSum :=
  D013.bundle_iff _ _

/-- 日次に収まると確認したD014の算定単位を受ける。採血IDは要求しない。 -/
def autoantibodyDay (site : Site) (rows : List D014.Context) : Option D014.BundleGroup :=
  if rows.any (fun c => c.performance.site != site) then none else some ⟨site, rows⟩

theorem autoantibodyDay_points (g : D014.BundleGroup) (p : Nat) :
    Satisfies D014.bundleRules g p ↔
      p = SpecimenTests.groupedBase .autoantibodies g.count g.sum :=
  D014.bundle_iff _ _

def specificIgeDraw (anchor : Performance D015.Item) (rows : List (Performance D015.Item × Nat)) :
    Option D015.IgeDraw :=
  (contextBundleMembers ⟨15, 13, .draw⟩ anchor Prod.fst rows).map (⟨anchor, ·⟩)

theorem specificIgeDraw_points (g : D015.IgeDraw) (p : Nat) :
    Satisfies D015.igeRules g p ↔
      p = SpecimenTests.groupedBase .specificIgE g.tests.length 0 :=
  D015.ige_legacy_iff _ _

/-- 実施料の選択・包括と、判断料の候補への採用は別に記録する。
採用の確認がない実施を候補から黙って落とさない。 -/
structure DayTest where
  id : Nat
  site : Site
  judgment : SpecimenJudgment.IncludedTest
  judgmentCandidate : Option Bool
  emergency : Option SpecimenOutpatientDay.EmergencyTest
  rapid : Option SpecimenOutpatientDay.RapidTest

/-- D026(5)によるD000の除外は、入力された候補性や実施料の算定に依存しない。 -/
def DayTest.resolvedJudgmentCandidate (row : DayTest) : Option Bool :=
  if row.judgment.test.major = 0 ∧ row.judgment.test.suffix = 0 then some false
  else row.judgmentCandidate

theorem d000_not_judgment_candidate (row : DayTest)
    (test : row.judgment.test = D000.judgmentTest) :
    row.resolvedJudgmentCandidate = some false := by
  simp [DayTest.resolvedJudgmentCandidate, test, D000.judgmentTest]

private def assessedChemistryItems (row : Performance BloodChemistry.Item)
    (rows : List (Performance BloodChemistry.Item)) (choices : List GroupChoice)
    (context : BloodChemistry.Draw) : Option (List BloodChemistry.Item) := do
  let draw ← row.draw
  if !rows.contains row || !retained choices row.id then none else
    let assessed ← chemistryDraw choices rows row.site draw context
    let items ← BloodChemistry.billableItems assessed
    if assessed.eligible row.item == some true && items.contains row.item.billingItem then
      some items
    else none

/-- 選択・適格性・項目数の評価を通過したD007の実施を判断料候補へ渡す。
除外された実施のD026候補性には、ここでは確定値を与えない。 -/
def chemistryJudgmentCandidate (row : Performance BloodChemistry.Item)
    (rows : List (Performance BloodChemistry.Item)) (choices : List GroupChoice)
    (context : BloodChemistry.Draw) : Option Bool :=
  (assessedChemistryItems row rows choices context).map fun _ => true

def chemistryJudgmentRule :
    Rule (Performance BloodChemistry.Item × List (Performance BloodChemistry.Item) ×
      List GroupChoice × BloodChemistry.Draw) (Option Bool) :=
  ⟨"notice/D026/paragraph/1", selectionNotice "PDF402頁 D026(1)", fun (row, rows, choices, context) out =>
    out = chemistryJudgmentCandidate row rows choices context⟩

def judgmentFromDay (day : SpecimenJudgment.DailyJudgment)
    (rows : List DayTest) : Option SpecimenJudgment.DailyJudgment := do
  let candidates ← rows.filterM DayTest.resolvedJudgmentCandidate
  return { day with tests := candidates.map DayTest.judgment }

/-- 点数・適格性を確認したD023(42)・(43)準用実施は微生物学的判断料の候補にする。 -/
def d023ReferenceDayTest (site : Site) (a : D023References.Assessment) (_ : a.Valid)
    (b001Claimed : Bool) (b001Included : Option Bool)
    (emergency : Option SpecimenOutpatientDay.EmergencyTest)
    (rapid : Option SpecimenOutpatientDay.RapidTest) : DayTest :=
  { id := a.legacy.1
    site
    judgment := ⟨a.legacy.2.judgmentTest, b001Claimed, false, b001Included, none⟩
    judgmentCandidate := some true
    emergency
    rapid }

def additionsFromDay (c : SpecimenOutpatientDay.AdditionContext)
    (rows : List DayTest) : SpecimenOutpatientDay.AdditionContext :=
  { c with emergencyTests := rows.filterMap DayTest.emergency
           rapidTests := rows.filterMap DayTest.rapid }

/-- 第1款迅速加算通知(2)で、実施項目数を使う多項目包括。 -/
inductive RapidBundle where
  | coagulation | chemistry | endocrine | tumorMarker

/-- 迅速加算の項目数に関する根拠。選択で除かれた場合の該当性は確認値を渡す。 -/
inductive RapidCountBasis where
  | individual
  | bundled (rule : RapidBundle)
  | outpatientConsultation
  | other (confirmed : Option Bool)

def RapidCountBasis.counts : RapidCountBasis → Option Bool
  | .individual | .bundled _ | .outpatientConsultation => some true
  | .other confirmed => confirmed

/-- D007注の包括を使う場合は迅速加算通知(2)、個別点数の場合は同(1)の項目候補とする。 -/
def chemistryRapidCountBasis (row : Performance BloodChemistry.Item)
    (rows : List (Performance BloodChemistry.Item)) (choices : List GroupChoice)
    (context : BloodChemistry.Draw) : Option RapidCountBasis :=
  (assessedChemistryItems row rows choices context).map fun items =>
    if 5 ≤ items.length then .bundled .chemistry else .individual

def rapidTestsFromAssessment
    (rows : List (SpecimenOutpatientDay.RapidTest × RapidCountBasis)) :
    Option (List SpecimenOutpatientDay.RapidTest) :=
  (rows.filterM fun (row : SpecimenOutpatientDay.RapidTest × RapidCountBasis) => row.2.counts).map (List.map Prod.fst)

def Day.withAssessedRapid (c : Day)
    (rows : List (SpecimenOutpatientDay.RapidTest × RapidCountBasis)) : Option Day := do
  let rapidTests ← rapidTestsFromAssessment rows
  return { c with additions := { c.additions with rapidTests } }

example (a b : SpecimenOutpatientDay.RapidTest) :
    rapidTestsFromAssessment [(a, .bundled .tumorMarker), (b, .bundled .tumorMarker)] =
      some [a, b] := rfl

example (a : SpecimenOutpatientDay.RapidTest) :
    rapidTestsFromAssessment [(a, .other none)] = none := rfl

/-- D012(24)の対象となる採取は、実施料に含まれる。 -/
theorem trachomatis_collection_from_test (c : D012.Context)
    (a : SpecimenCollection.Assessment) (kind : Nat)
    (item : c.performance.item = .local .trachomatisAntigen) :
    ∀ separate h, D012.trachomatisCollection c a kind separate h = none :=
  fun separate h => D012.trachomatis_collection_included c a kind separate h item

/-- 同じ実施一覧を判断料と加算に射影する。加算候補の none は候補なしの確認を表す。 -/
def Day.withTests (c : Day) (rows : List DayTest) : Option Day := do
  if rows.any (fun row => row.site != c.judgment.day.site) ||
      (rows.map DayTest.id).eraseDups != rows.map DayTest.id then none else
    let day ← judgmentFromDay c.judgment.day rows
    return { c with judgment := { c.judgment with day }
                    additions := additionsFromDay c.additions rows }

/-- 加算の算定履歴と要件から、日次合成に必要な加算の決定性を得る。 -/
theorem day_determines_with_addition_history (c : Day)
    (site : c.additions.site = c.judgment.day.site)
    (judgment : c.judgment.Eligible)
    (emergency : c.additions.selection = .emergency →
      SpecimenOutpatientDay.EmergencyConfirmed c.additions ∧
      c.additions.emergencyClaimed = some false ∧ c.additions.priorRapidItems = some [] ∧
      c.additions.nightEarlyMorningAddition = false)
    (rapid : c.additions.selection = .rapid → ∃ prior,
      c.additions.priorRapidItems = some prior ∧ prior.Nodup ∧ prior.length ≤ 5 ∧
      c.additions.emergencyClaimed = some false) :
    ∃ r, c.Permits r ∧ ∀ other, c.Permits other → other = r :=
  day_determines c site judgment
    (SpecimenOutpatientDay.additions_determine c.additions emergency rapid)

def collectionCharge (c : SpecimenCollection.Context)
    (h : ∃ p, SpecimenCollection.points c = some p) : Charge :=
  ⟨fun p => SpecimenCollection.points c = some p, by
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp, fun _ hq => Option.some.inj (hq.symm.trans hp)⟩⟩

private def sampleSite : Site := ⟨1, 2, ⟨⟨2026, 10⟩, ⟨22, by decide⟩⟩⟩

private def stoolSample : D003.Context :=
  { performance := { id := 11, site := sampleSite, item := .calprotectin }
    d017BacteriaOrProtozoa := some false
    purpose := some .diagnosis }

private def colonoscopySurvey : Snapshot (Performance Unit) :=
  ⟨sampleSite.monthScope, [{ id := 12, site := sampleSite, item := () }]⟩

example : (colonoscopyGroup stoolSample (some sampleSite.institution) colonoscopySurvey).map
    (List.map ChoiceGroup.members) = some [[11, 12]] := by decide

example : colonoscopyGroup stoolSample none colonoscopySurvey = none := by decide

private def tauSample : Performance D004.Item := { id := 11, site := sampleSite, item := .phosphoTau }
private def amyloidSample : Performance D004.Item := { id := 12, site := sampleSite, item := .amyloidRatio }

example :
    (csfRatioGroup tauSample [tauSample, amyloidSample]).map ChoiceGroup.members =
      some [11, 12] := by decide

example :
    (punctureSelectionInput tauSample { item := .phosphoTau } none).bind
      (·.aloneOrPrincipalAmongTauRatios) = none := rfl

example :
    (do
      let group ← csfRatioGroup tauSample [tauSample, amyloidSample]
      let projected ← punctureSelectionInput amyloidSample { item := .amyloidRatio }
        (some [⟨group, [tauSample.id]⟩])
      projected.aloneOrPrincipalAmongTauRatios) = some false := by decide

private def tumorSample : D004Tumor.Context :=
  { performance := { id := 11, site := sampleSite, item := .drugAid }, cancer := .lung, assay := some .egfr }

private def geneSurvey : Snapshot (Performance D004Tumor.OtherTest) :=
  ⟨sampleSite.monthScope, [{ id := 12, site := sampleSite, item := .d006_12 }]⟩

example : (tumorMonthlyGroups tumorSample (some sampleSite.institution) geneSurvey).map
    (List.map ChoiceGroup.members) = some [[11, 12]] := by decide

example : tumorMonthlyGroups tumorSample none geneSurvey = none := by decide

private def hematologicSample : Snapshot (Performance D004Tumor.OtherTest) :=
  ⟨sampleSite.monthScope, [{ id := 21, site := sampleSite, item := .d006_2 },
    { id := 22, site := sampleSite, item := .d006_6 },
    { id := 23, site := sampleSite, item := .d006_16 }]⟩

example : (hematologicMonthlyGroup sampleSite (some sampleSite.institution)
    hematologicSample).map (List.map ChoiceGroup.members) = some [[21, 22, 23]] := by decide

private def bladderSample : Performance D006Oncology.Bladder.Related :=
  { id := 31, site := sampleSite, item := .bladderGeneTest, simultaneous := some 9 }

private def cytologySample : Performance D006Oncology.Bladder.Related :=
  { id := 32, site := sampleSite, item := .cytology, simultaneous := some 9 }

example : (bladderCytologyGroup bladderSample [cytologySample]).map
    (List.map ChoiceGroup.members) = some [[31, 32]] := by decide

example : bladderCytologyGroup bladderSample [{ cytologySample with simultaneous := none }] =
    none := by decide

private def calciumSample : Performance BloodChemistry.Item :=
  { id := 51, site := sampleSite, item := .calcium, draw := some 7, simultaneous := some 9 }

private def ionizedSample : Performance BloodChemistry.Item :=
  { id := 52, site := sampleSite, item := .ionizedCalcium, draw := some 7, simultaneous := some 9 }

example : (do
    let group ← chemistryCombinationGroup .calcium [calciumSample, ionizedSample]
    let draw ← chemistryDraw [⟨group, [51]⟩] [calciumSample, ionizedSample] sampleSite 7
      { performed := [] }
    BloodChemistry.points draw) = some 11 := by decide

example : (do
    let group ← chemistryCombinationGroup .calcium [calciumSample, ionizedSample]
    chemistryJudgmentCandidate calciumSample [calciumSample, ionizedSample] [⟨group, [51]⟩]
      { performed := [] }) = some true := by decide

example : (do
    let group ← chemistryCombinationGroup .calcium [calciumSample, ionizedSample]
    chemistryJudgmentCandidate ionizedSample [calciumSample, ionizedSample] [⟨group, [51]⟩]
      { performed := [] }) = none := by decide

example : chemistryCombinationGroup .calcium
    [calciumSample, { ionizedSample with simultaneous := none }] = none := by decide

private def glycemicSample : Snapshot (Performance GlycemicTests.Item) :=
  ⟨sampleSite.monthScope, [{ id := 41, site := sampleSite, item := .a1c },
    { id := 42, site := sampleSite, item := .anhydroglucitol, draw := some 7 }]⟩

example : (glycemicChemistryDay sampleSite glycemicSample (some .clinical) ⟨41, some 42⟩).map
    (List.map Performance.draw) = some [some 7] := by decide

example : glycemicChemistryDay sampleSite glycemicSample (some .both) ⟨41, some 42⟩ =
    none := by decide

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

private def monthly (item := BloodMorphology.Item.eosinophilCount) : SpecimenJudgment.DailyJudgment :=
  { site := sampleSite
    tests := [
      ⟨item.judgmentTest false, false, false, none, none⟩,
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

private def urineSample : D000.Context :=
  ⟨{ id := 8, site := sampleSite, item := () }, some sampleSite.institution, some .strip,
    [.ph], some .direct⟩

private theorem urineSample_eligible : D000.Eligible urineSample := by
  simp [D000.Eligible, D000.InHouse, D000.ReportConfirmed, urineSample]

private def sampleDay (automated : Bool) : Day :=
  let item := if automated then BloodMorphology.Item.automatedDifferential else .eosinophilCount
  let chemistry := [.bun, .uricAcid, .glucose, .ast, .alt]
  let morphology := morphologySample item
  ⟨[Charge.fromRules [BloodChemistry.pointsRule] chemistry
      (BloodChemistry.determines_points chemistry),
    Charge.fromProjection BloodMorphology.individualRules morphology
      (BloodMorphology.individual_determines morphology item.basePoints 0 (by cases automated <;> rfl))
      (fun p => p.1 + p.2),
    Charge.fromProjection D000.rules urineSample (D000.determines _ urineSample_eligible)
      (fun r => r.charge.base)], [],
    ⟨monthly item, true, .outpatient, none, none, none⟩, additionSample⟩

example :
    (morphologySample .eosinophilCount).item.basePoints + 93 ≠
      (morphologySample .automatedDifferential).item.basePoints + 93 := by decide

private theorem sampleDay_judgmentEligible (automated : Bool) :
    (sampleDay automated).judgment.Eligible := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [sampleDay, monthly, SpecimenJudgment.DailyJudgment.Known,
      SpecimenJudgment.DailyJudgment.coverageResolved, SpecimenJudgment.IncludedTest.separateEligibility]
    cases automated <;> decide
  · simp [sampleDay]
  · simp [sampleDay]
  · simp [sampleDay]

example (automated : Bool) :
    ∃ r, (sampleDay automated).Permits r ∧ ∀ other, (sampleDay automated).Permits other → other = r :=
  day_determines_with_addition_history _ rfl (sampleDay_judgmentEligible automated)
    (by intro h; cases h) (by intro h; cases h)

private def sampleBreakdown (automated : Bool) : Breakdown :=
  let execution := [93, if automated then 15 else 17, 26]
  let judgment := 125 + 144
  ⟨execution, [], judgment, ⟨0, 0⟩, ⟨execution.sum + judgment, execution.sum + judgment⟩⟩

private theorem sampleDay_perm (automated : Bool) :
    (sampleDay automated).Permits (sampleBreakdown automated) := by
  refine ⟨?_, .nil, ?_, ?_, ?_⟩
  · apply ChargeList.cons
    · exact ⟨93, by simp [satisfies_cons, satisfies_nil, BloodChemistry.pointsRule_iff, BloodChemistry.pointsForItems], rfl⟩
    apply ChargeList.cons
    · refine ⟨(if automated then 15 else 17, 0), ?_, ?_⟩
      · apply (BloodMorphology.payable_iff ..).mpr
        cases automated <;> rfl
      · cases automated <;> rfl
    apply ChargeList.cons
    · obtain ⟨r, hr⟩ := (D000.determines _ urineSample_eligible).1
      have p : r.charge = ⟨26, 0⟩ := by
        have points := hr D000.headingRule (by simp [D000.rules])
        exact points
      exact ⟨r, hr, congrArg (·.base) p⟩
    · exact .nil
  · apply (SpecimenJudgment.outpatient_day_iff _ (sampleDay_judgmentEligible automated) _).mpr
    cases automated <;> rfl
  · simp [sampleDay, sampleBreakdown, additionSample, SpecimenOutpatientDay.additionRules,
      satisfies_cons, satisfies_nil, SpecimenOutpatientDay.emergencyPrimary,
      SpecimenOutpatientDay.rapidPrimary, SpecimenOutpatientDay.emergencyOnce,
      SpecimenOutpatientDay.emergencyNightExclusion, SpecimenOutpatientDay.rapidBundle,
      SpecimenOutpatientDay.rapidDailyLimit, SpecimenOutpatientDay.rapidConsultationBundle]
  · apply (SpecimenOutpatientDay.satisfies_iff ..).mpr
    cases automated <;> rfl

example :
    (sampleDay false).Permits (sampleBreakdown false) ∧
      (sampleDay true).Permits (sampleBreakdown true) ∧
      (sampleBreakdown false).total.specimenWithCollection = 405 ∧
      (sampleBreakdown true).total.specimenWithCollection = 403 :=
  ⟨sampleDay_perm false, sampleDay_perm true, rfl, rfl⟩

example : ({ (monthly) with
    claims := ⟨⟨{ sampleSite.monthScope with patient := 2 }, []⟩, by simp⟩
  } : SpecimenJudgment.DailyJudgment).points = none := by decide

end Sanri.MedicalFee.SpecimenCrossDivision
