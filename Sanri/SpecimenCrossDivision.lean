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

/-- 条項の対象と実施関係を確認した二実施に、D007の選択規則を適用する。
同時・同一検体の指定は実施IDとは別の識別子で照合する。 -/
def chemistryPairChoice (pair : BloodChemistryFurther.Pair)
    (first : Performance α) (second : Performance β)
    (linked : Bool) (choice : BloodChemistryFurther.Choice) : Option GroupChoice := do
  if !linked || first.id == second.id || first.site.patient != second.site.patient ||
      first.site.institution != second.site.institution then none else
    let linkedByRecord := match pair with
      | .bileAcids => first.simultaneous == second.simultaneous &&
          first.simultaneous.isSome
      | .bicarbonateAndBloodGas | .carnitineAndD010 =>
          first.specimen == second.specimen && first.specimen.isSome
      | _ => true
    if !linkedByRecord || !decide (pair.permits true choice) then none else
      let selected ← match choice with
        | .first => some first.id
        | .second => some second.id
        | .both => none
      return ⟨⟨pair.rule.source, [first.id, second.id], 1⟩, [selected]⟩

/-- D007(17)エのD010側。枝を落とさずに項8の範囲を照合する。 -/
def carnitineChoice (chemistry : Performance BloodChemistryFurther.Item)
    (special : D010.Context) (linked : Bool) (choice : BloodChemistryFurther.Choice) :
    Option GroupChoice :=
  if (chemistry.item = .totalCarnitine ∨ chemistry.item = .freeCarnitine) ∧
      special.performance.item.number = 8 then
    chemistryPairChoice .carnitineAndD010 chemistry special.performance linked choice
  else none

def carnitineSpecialInput (choices : List GroupChoice) (c : D010.Context) :
    Option D010.Context :=
  if retained choices c.performance.id then some c else none

theorem carnitine_special_points (choices : List GroupChoice) (c projected : D010.Context)
    (selected : carnitineSpecialInput choices c = some projected)
    (eligible : D010.Eligible c) : DeterminesAt D010.rules projected := by
  unfold carnitineSpecialInput at selected
  split at selected
  · cases selected
    exact D010.determines c eligible
  · contradiction

/-- 同一患者・機関の暦月を確認した実施から、IとTの併施群を作る。
月内に一方式しかない場合はこの選択規則を起動しない。 -/
def troponinMonthGroup (site : Site)
    (survey : Snapshot (Performance BloodChemistryAdditional.Item)) : Option (Option ChoiceGroup) := do
  let kind := BloodChemistryAdditional.Group.monthlyTroponins
  let rows ← survey.select Performance.site site.monthScope (fun p => kind.items.contains p.item)
  let ids := rows.map Performance.id
  if ids.eraseDups != ids then none else
    return if kind.restricts (rows.map Performance.item) then some ⟨kind.rule.source, ids, 1⟩ else none

/-- 同日の全実施からは併施を推定せず、D007(21)の併施が確認できた範囲を使う。 -/
def lungMarkerGroup (rows : List (Performance BloodChemistryAdditional.Item)) :
    Option ChoiceGroup := do
  let kind := BloodChemistryAdditional.Group.lungMarkers
  let members := rows.filter fun row => kind.items.contains row.item
  let anchor :: rest := members | none
  let ids := members.map Performance.id
  if ids.eraseDups != ids || !kind.restricts (members.map Performance.item) ||
      rest.any (fun row => row.site.patient != anchor.site.patient ||
        row.site.institution != anchor.site.institution) then none
  else some ⟨kind.rule.source, ids, 1⟩

inductive LateChemistryCombination where
  | cardiac | collagen | mac2 | autotaxin | ck18f | elf
  deriving DecidableEq

private def LateChemistryCombination.members (kind : LateChemistryCombination) :
    String × List BloodChemistryLate.Item × List BloodChemistryLate.Item :=
  let liver : List BloodChemistryLate.Item :=
    [.typeIVCollagen, .typeIVCollagen7S, .procollagenIII, .hyaluronicAcid]
  match kind with
  | .cardiac => ("27", [.hFabpQualitative, .hFabpQuantitative],
      [.myoglobinQualitative, .myoglobinQuantitative])
  | .collagen => ("30", [.typeIVCollagen, .typeIVCollagen7S], [.procollagenIII, .mac2])
  | .mac2 => ("40/i", [.mac2], liver)
  | .autotaxin => ("41/i", [.autotaxin], .mac2 :: liver)
  | .ck18f => ("42/i", [.ck18f], .autotaxin :: .mac2 :: liver)
  | .elf => ("43/u", [.elfScore], [.typeIVCollagen, .typeIVCollagen7S, .mac2, .autotaxin, .ck18f])

/-- D007後半の区分内の選択。ELF構成項目の非別算定は(43)イで別に評価する。 -/
def lateChemistryGroup (kind : LateChemistryCombination)
    (rows : List (Performance BloodChemistryLate.Item)) : Option ChoiceGroup := do
  let (paragraph, left, right) := kind.members
  let rule ← BloodChemistryLate.rules.find? fun r => r.id == "notice/D007/paragraph/" ++ paragraph &&
    (kind != .cardiac || r.source.location.endsWith "ただし書")
  let members := rows.filter fun p => (left ++ right).contains p.item
  let anchor :: rest := members | none
  let ids := members.map Performance.id
  if ids.eraseDups != ids || !members.any (fun p => left.contains p.item) ||
      !members.any (fun p => right.contains p.item) ||
      rest.any (fun p => p.site.patient != anchor.site.patient ||
        p.site.institution != anchor.site.institution) then none
  else some ⟨rule.source, ids, 1⟩

/-- 適用群の主検査種を既存の入力欄へ渡す。適用群と採用を確認できた場合に評価入力を得る。 -/
def lateChemistryInput (kind : LateChemistryCombination)
    (rows : List (Performance BloodChemistryLate.Item)) (choices : List GroupChoice)
    (row : Performance BloodChemistryLate.Item) (c : BloodChemistryLate.Context) :
    Option BloodChemistryLate.Context := do
  let g ← lateChemistryGroup kind rows
  if row.item != c.item || !rows.contains row || !g.members.contains row.id ||
      !choices.any (fun choice => choice.group == g) || !retained choices row.id then none else
    let principal := some (BloodChemistryLate.Principal.selected row.item)
    return match kind with
    | .cardiac => { c with hFabpMyoglobinSelection := principal }
    | .collagen => { c with collagenSelection := principal }
    | .mac2 => { c with mac2Selection := principal }
    | .autotaxin => { c with autotaxinSelection := principal }
    | .ck18f => { c with ck18fSelection := principal }
    | .elf => { c with elfSelection := principal }

/-- 同一患者・機関の日に確認された反復。通知(38)は先着順を指定しない。 -/
def myosinDayGroup (site : Site) (survey : Snapshot (Performance BloodChemistryLate.Item)) :
    Option (Option ChoiceGroup) := do
  let rows ← survey.select Performance.site ⟨site.patient, some site.institution, Period.day site.date⟩
    (fun p => p.item == .cardiacMyosinLightChainI)
  let ids := rows.map Performance.id
  if ids.eraseDups != ids then none else
    return if 2 ≤ ids.length then some ⟨selectionNotice "PDF359頁 D007(38)", ids, 1⟩ else none

def myosinDayInput (row : Performance BloodChemistryLate.Item)
    (survey : Snapshot (Performance BloodChemistryLate.Item)) (choices : List GroupChoice)
    (c : BloodChemistryLate.Context) : BloodChemistryLate.Context :=
  { c with myosinDailySelection := do
      if c.item != .cardiacMyosinLightChainI || row.item != c.item ||
          !survey.entries.contains row then none else
        match ← myosinDayGroup row.site survey with
        | none => some true
        | some g => if choices.any (fun a => a.group == g)
          then some (retained choices row.id) else none }

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

inductive EndocrineCombination where
  | renin | hcg | natriuretic | bone | tracp | alp | betaCtx | normetanephrine | igfbp3

/-- 各群の併施範囲を確認した実施を受ける。利尿ペプチドでは、起算日を含む
一週間の候補を渡す。重なる窓は別々に評価し、採否を Agree で照合する。 -/
def endocrineGroup (kind : EndocrineCombination)
    (performed : List (Performance D008.CombinationItem)) : Option ChoiceGroup := do
  let (source, items, trigger) : SourceRef × List D008.Item × Option D008.Item := match kind with
    | .renin => (D008.reninRule.source, [.reninActivity, .reninQuantitative], none)
    | .hcg => (D008.hcgChoiceRule.source,
        [.hcgBeta, .hcgQualitative, .hcgQuantitative, .hcgSemiquantitative], some .hcgBeta)
    | .natriuretic => (D008.bnpChoice.source, [.bnp, .ntProBnp, .anp], none)
    | .bone => (D008.boneMarkerRule.source, [.ntx, .osteocalcin, .urineDpd], none)
    | .tracp => (D008.tracpChoiceRule.source, [.ntx, .osteocalcin, .urineDpd, .tracp5b], some .tracp5b)
    | .alp => (D008.alpRule.source, [.bap, .pinp, .intactPinp], none)
    | .betaCtx => (D008.betaCtxChoice.source, [.urineBetaCtx, .betaCtx], none)
    | .normetanephrine => (D008.normetanephrineRule.source, [.metanephrine, .normetanephrine], none)
    | .igfbp3 => (D008.igfbp3Choice.source, [.igfbp3, .somatomedinC], none)
  let inGroup (p : D008.CombinationItem) := D008.endocrineGroup items p ||
    (match kind with | .alp => decide (p = .d007Pag) | _ => false)
  let rows := performed.filter fun p => inGroup p.item
  let first :: rest := rows | none
  let ids := rows.map Performance.id
  if ids.eraseDups != ids || rest.any (fun p => p.site.patient != first.site.patient) ||
      ((rows.map (D008.CombinationItem.testKind ∘ Performance.item)).eraseDups.length < 2) ||
      !(trigger.all fun i => rows.any fun p => D008.endocrineGroup [i] p.item) then none
  else some ⟨source, ids, 1⟩

private def nextDate (date : Date) : Date :=
  if within : date.day.val + 1 < date.month.days then
    ⟨date.month, ⟨date.day.val + 1, within⟩⟩
  else
    let month := date.month.shift 1
    ⟨month, ⟨0, month.days_pos⟩⟩

/-- D008(7)(10)(24)の起算日を含む7日。確認済みの起算日と照会する機関範囲を受ける。
窓が重なる場合も、各窓の候補を独立に取得する。 -/
def natriureticWeekGroup (anchor : Performance D008.CombinationItem) (institution : Option Nat)
    (survey : Snapshot (Performance D008.CombinationItem)) :
    Option (List (Performance D008.CombinationItem) × Option ChoiceGroup) := do
  let start := anchor.site.date
  let last := (List.range 6).foldl (fun day _ => nextDate day) start
  let isPeptide := D008.endocrineGroup [.bnp, .ntProBnp, .anp]
  if ordered : start.key ≤ last.key then
    let rows ← survey.select Performance.site ⟨anchor.site.patient, institution, ⟨start, last, ordered⟩⟩
      (fun p => isPeptide p.item)
    if !rows.contains anchor || (rows.map Performance.id).eraseDups != rows.map Performance.id
      then none else some (rows, endocrineGroup .natriuretic rows)
  else none

/-- D008の同時実施による非別算定。残る側の個別適格性は別に評価する。 -/
def endocrineSimultaneousExclusion (charged other : Performance D008.CombinationItem) :
    Option GroupChoice := do
  if charged.id = other.id || charged.simultaneousWith other != some true then none else
    let source ← match charged.item, other.item with
      | .endocrine .cPeptide sample, .endocrine .cPeptide .urine =>
          if sample ∈ [D008.Sample.wholeBlood, .serum, .plasma] then some D008.cprRule.source else none
      | .endocrine first _, .endocrine second _ =>
          if first ∈ [D008.Item.estriol, .estradiol] ∧
              second ∈ [D008.Item.estrogenSemiquantitative, .estrogenQuantitative]
            then some D008.estrogenRule.source else none
      | _, _ => none
    return ⟨⟨source, [other.id], 0⟩, []⟩

/-- 併施の確認一覧と共通の採否を既存の入力欄へ射影する。 -/
def endocrineInput (c : D008.Context) (choices : List GroupChoice)
    (together simultaneous natriureticWeek : Option (List (Performance D008.CombinationItem))) :
    D008.Context :=
  { c with together := together.map (endocrineSurvey choices)
           simultaneous := simultaneous.map (endocrineSurvey choices)
           natriureticWeek := natriureticWeek.map (endocrineSurvey choices) }

def markerSelection (choices : List GroupChoice) (id : Nat)
    (others : List (Performance D009.Companion)) : Option D009.Selection :=
  match ([id] ++ others.map Performance.id).filter (retained choices) with
  | [selected] => some ⟨others, selected⟩
  | _ => none

inductive MarkerCombination where
  | cea | ca125 | urine | cslex | progrp | s23 | phiPsa | phiRatio | apoa

/-- D009の各併施を確認した範囲で評価する。同時を明記する尿検査は識別子も照合する。
前立腺関連の重複群は、同じ実施IDに対する Agree の条件を共有する。 -/
def markerGroup (kind : MarkerCombination) (rows : List (Performance D009.Companion)) :
    Option ChoiceGroup := do
  let (source, anchor, others) : SourceRef × D009.Companion × List D009.Companion := match kind with
    | .cea => (D009.ceaChoice.source, .cea, [.dupan2])
    | .ca125 => (D009.ca125Choice.source, .ca125, [.ca602])
    | .urine => (D009.urinePair.source, .nmp22, [.urineCytokeratin])
    | .cslex => (D009.cslexChoice.source, .cslex, [.ca153])
    | .progrp => (D009.progrpChoice.source, .progrp, [.nse])
    | .s23 => (D009.s23Choice.source, .s23psa, [.psa, .freePsaRatio, .phi])
    | .phiPsa => (D009.phiPsaChoice.source, .phi, [.psa])
    | .phiRatio => (D009.phiRatioChoice.source, .phi, [.freePsaRatio])
    | .apoa => (D009.apoaChoice.source, .apoa2, [.cea, .dupan2, .span1])
  let first ← rows.find? fun p => p.item == anchor
  let members := rows.filter fun p => (p.item == anchor || others.contains p.item) &&
    p.site.patient == first.site.patient && p.site.institution == first.site.institution
  let ids := members.map Performance.id
  let simultaneous := match kind with
    | .urine => members.all fun p => first.simultaneousWith p == some true
    | _ => true
  if ids.eraseDups != ids || !simultaneous || !members.any (fun p => others.contains p.item)
    then none else some ⟨source, ids, 1⟩

/-- D009の個別評価には、適用群で残った実施だけを渡す。
各入力の実施一覧には採否にかかわらず確認した相手を残す。 -/
def markerInput (c : D009.Context) (choices : List GroupChoice)
    (together simultaneous management : Option (List (Performance D009.Companion))) :
    Option D009.Context :=
  if !retained choices c.performance.id then none else
    let selection := fun rows => D009.Selection.mk rows c.performance.id
    some { c with together := together.map selection
                  simultaneous := simultaneous.map selection
                  endometriosisManagementSelection := management.map selection }

/-- PF4の三方式を同じ一連で測定したときに一件を残す。 -/
def pf4SeriesGroup (rows : List (Performance D011.Item)) : Option ChoiceGroup := do
  let first :: _ := rows | none
  let ids := rows.map Performance.id
  if ids.eraseDups != ids ||
      !rows.all (fun p => p.item.isPf4 && first.sameSeries p == some true) ||
      !([D011.Item.pf4IgG, .pf4IgGmA, .pf4Qualitative].all fun i => rows.any (·.item == i))
    then none else some ⟨D011.pf4Choice.source, ids, 1⟩

def pf4Input (c : D011.Context) (rows : List (Performance D011.Item))
    (choices : List GroupChoice) : D011.Context :=
  { c with pf4Series := some rows
           mainPf4 := do
             let group ← pf4SeriesGroup rows
             let [id] := group.members.filter (retained choices) | none
             return id }

def infectionCombined (choices : List GroupChoice) (g : D012.Combined) : D012.Combined :=
  { g with selected := some ((g.members.filter fun p => retained choices p.id).map Performance.id) }

inductive InfectionCombination where
  | mycoplasma | stoolAntigen | pneumoniae | o157 | pneumococcus | pertussis | dengue | toxoplasma

/-- 通知の併施を確認した範囲から、当該条項の二側に属する実施を抽出する。 -/
def infectionGroup (kind : InfectionCombination) (g : D012.Combined) : Option ChoiceGroup := do
  let (source, left, right) : SourceRef × List D012.RelatedTest × List D012.RelatedTest :=
    match kind with
    | .mycoplasma => (D012.mycoplasmaAntibodyRule.source,
        [.local .mycoplasmaQual, .local .mycoplasmaSemi],
        [.local .mycoplasmaChromatography, .local .mycoplasmaFluorescence])
    | .stoolAntigen => (D012.stoolAntigenRule.source, [.local .stoolAdenovirus],
        [.local .stoolRotavirusQual, .local .stoolRotavirusQuant])
    | .o157 => (D012.o157Rule.source, [.local .ecoliO157Antibody],
        [.local .ecoliO157Antigen, .gastrointestinalCultureD018])
    | .pneumoniae => (D012.pneumoniaeChoice.source, [.local .pneumoniaeIgM],
        [.local .pneumoniaeIgG, .local .pneumoniaeIgA])
    | .pneumococcus => (D012.pneumococcusWallChoice.source, [.local .pneumococcusWall],
        [.local .pneumococcusCapsule])
    | .pertussis => (D012.pertussisChoice.source, [.local .pertussisAntigen],
        [.pertussisD023_13, .multiplexD023_25])
    | .dengue => (D012.dengueChoice.source, [.local .dengueAntigen], [.local .dengueCombo])
    | .toxoplasma => (D012.toxoplasmaChoice.source, [.local .toxoplasmaAntibody],
        [.local .toxoplasmaAvidity])
  let first :: rest := g.members | none
  let rows := g.members.filter fun p => (left ++ right).contains p.item
  let ids := g.members.map Performance.id
  let active := match kind with
    | .mycoplasma | .o157 => 2 ≤ (rows.map Performance.item).eraseDups.length
    | _ => rows.any (fun p => left.contains p.item) && rows.any (fun p => right.contains p.item)
  let sameEvent := match kind with
    | .stoolAntigen => match rows with
      | anchor :: others => others.all fun p => anchor.simultaneousWith p == some true
      | [] => false
    | _ => true
  if ids.eraseDups != ids || !active || !sameEvent ||
      rest.any (fun p => p.site.patient != first.site.patient ||
        p.site.institution != first.site.institution) then none
  else some ⟨source, rows.map Performance.id, 1⟩

/-- D012(38)イでは測定対象のウイルスとクラスを確認する。
併施の範囲を表す Combined と、点数を集計する検体群は区別する。 -/
def virusClassGroup (g : D012.Combined) (target : D012.Target) : Option ChoiceGroup := do
  let rows := g.members.filter fun p =>
    p.item == .local .classSpecificTiter && g.viralTarget p.id == some target
  let anchor :: rest := rows | none
  let ids := g.members.map Performance.id
  let hasClass (kind : D012.AntibodyClass) := rows.any fun p => g.antibodyClass p.id == some kind
  if ids.eraseDups != ids || !hasClass .igg || !hasClass .igm ||
      !rows.all (fun p => g.antibodyClass p.id == some .igg || g.antibodyClass p.id == some .igm) ||
      rest.any (fun p => p.site.patient != anchor.site.patient ||
        p.site.institution != anchor.site.institution) then none
  else some ⟨D012.classSpecificChoice.source, rows.map Performance.id, 1⟩

def infectionInput (c : D012.Context) (g : D012.Combined) (choices : List GroupChoice) :
    Option D012.Context :=
  if g.members.contains c.performance && retained choices c.performance.id then
    some { c with combined := some (infectionCombined choices g) }
  else none

inductive HepatitisCombination where
  | hbCore | ha

/-- D013(5)(6)。同時実施IDでまとまる一群を作る。採血IDは別に扱う。 -/
def hepatitisGroup (kind : HepatitisCombination) (anchor : Performance D013.Item)
    (rows : List (Performance D013.Item)) : Option ChoiceGroup := do
  let (rule, a, b) : Rule D013.Context Unit × D013.Item × D013.Item := match kind with
    | .hbCore => (D013.hbCoreChoice, .hbcAntibody, .hbcIgM)
    | .ha => (D013.haChoice, .haAntibody, .haIgM)
  let candidates := rows.filter fun p => p.item == a || p.item == b
  if !(candidates.contains anchor) ||
      candidates.any (fun p => (anchor.simultaneousWith p).isNone) then none else
    let simultaneous := candidates.filter fun p => anchor.simultaneousWith p == some true
    let ids := simultaneous.map Performance.id
    if ids.eraseDups != ids || !(simultaneous.any fun p => p.item == a) ||
        !(simultaneous.any fun p => p.item == b) then none
    else some ⟨rule.source, ids, 1⟩

private def hepatitisDnaSimultaneous (antigen : D013.Context) (dna : D023.HbvContext) :
    Option Bool :=
  antigen.performance.simultaneousWith
    { id := dna.performance.id, site := dna.performance.site,
      item := D013.Item.hbcrAntigen, simultaneous := dna.performance.simultaneous }

/-- D013(8)とD023項4の二件。DNA側の測定法・履歴はD023の規則で評価する。 -/
def hepatitisDnaGroup (antigen : D013.Context) (dna : D023.HbvContext) : Option ChoiceGroup :=
  if antigen.item == .hbcrAntigen && antigen.performance.id != dna.performance.id &&
      hepatitisDnaSimultaneous antigen dna == some true then
    some ⟨D013.coreRelatedAntigen.source, [antigen.performance.id, dna.performance.id], 1⟩
  else none

def hepatitisSelectionInput (c : D013.Context) (choices : List GroupChoice)
    (survey : List (Performance D013.Item)) : D013.Context :=
  { c with otherPayableLocal := some (survey.filter fun p =>
      p.id != c.performance.id && retained choices p.id) }

/-- 選択後の候補からD013の局所入力を得る。同時実施の事実は元の記録から渡す。 -/
def selectedHepatitisInput (c : D013.Context) (choices : List GroupChoice)
    (survey : List (Performance D013.Item)) : Option D013.Context :=
  if survey.contains c.performance && retained choices c.performance.id then
    some { hepatitisSelectionInput c choices survey with simultaneousLocal := some survey }
  else none

/-- 相手の実施を照合済みの場合に、同時実施と主検査の採否を分けて射影する。 -/
def hepatitisDnaInput (antigen : D013.Context) (dna : D023.HbvContext)
    (choices : List GroupChoice) : D013.Context :=
  let simultaneous := hepatitisDnaSimultaneous antigen dna
  let antigenSelected := retained choices antigen.performance.id
  let dnaSelected := retained choices dna.performance.id
  { antigen with
    simultaneousHbvDna := simultaneous
    mainWhenHbvDnaMeasured := if simultaneous == some true && antigenSelected != dnaSelected then
      some antigenSelected else none }

/-- D023項4の採否にはD013(8)と同じ実施IDを使う。 -/
def selectedHepatitisDna (dna : D023.HbvContext) (choices : List GroupChoice) :
    Option D023.HbvContext :=
  if retained choices dna.performance.id then some dna else none

/-- D014(8)は採血や同日ではなく同時実施を照合する。 -/
def thyroidAntibodyGroup (trab tsab : Performance D014.Item) : Option ChoiceGroup :=
  if trab.item == .trab && tsab.item == .tsab && trab.id != tsab.id &&
      trab.simultaneousWith tsab == some true then
    some ⟨D014.thyroidStimulation.source, [trab.id, tsab.id], 1⟩
  else none

/-- D014(12)の併施を確認した二件。通知が指定するTIA法を残す。 -/
def igg2Choice (tia nephelometry : Performance D014.Item) : Option GroupChoice :=
  if tia.item == .igg2Tia && nephelometry.item == .igg2Nephelometry &&
      tia.site.patient == nephelometry.site.patient &&
      tia.site.institution == nephelometry.site.institution &&
      tia.id != nephelometry.id then
    some ⟨⟨D014.igg2.source, [tia.id, nephelometry.id], 1⟩, [tia.id]⟩
  else none

def autoantibodySelectionInput (c : D014.Context) (choices : List GroupChoice)
    (survey : List (Performance D014.Item)) : D014.Context :=
  { c with combined := some (survey.map Performance.item,
      (survey.filter fun p => retained choices p.id).map Performance.item) }

/-- 確認済みの併測一覧と、同時実施を検査する一覧を区別して渡す。 -/
def selectedAutoantibodyInput (c : D014.Context) (choices : List GroupChoice)
    (combined simultaneous : List (Performance D014.Item)) : Option D014.Context :=
  if retained choices c.performance.id then
    some { autoantibodySelectionInput c choices combined with
      simultaneous := some (simultaneous, simultaneous.filter fun p => retained choices p.id) }
  else none

/-- D015(4)ア・イ。同一検体の実施を一群にする。欠落した検体IDは未確定。 -/
def electrophoresisGroup (anchor : Performance D015.Item)
    (rows : List (Performance D015.Item)) : Option ChoiceGroup := do
  let items : List D015.Item := [.wholeAntiserum, .specificAntiserum, .drugImmunofixation]
  let candidates := rows.filter fun p => items.contains p.item
  if !(candidates.contains anchor) ||
      candidates.any (fun p => (anchor.sameSpecimen p).isNone) then none else
    let related := candidates.filter fun p => anchor.sameSpecimen p == some true
    let ids := related.map Performance.id
    if ids.length < 2 || ids.eraseDups != ids then none
    else
      let source := if (related.map Performance.item).eraseDups.length = 1 then
        D015.electrophoresisOnce.source else D015.electrophoresisChoice.source
      some ⟨source, ids, 1⟩

/-- D015(11)イ。実施目的を照合した同一暦月の二件。履歴全体の照会は呼出側で行う。 -/
def atopyProteinGroup (scca tarc : D015.Context) : Option ChoiceGroup :=
  let a := scca.performance
  let b := tarc.performance
  if scca.item == .scca2 && tarc.item == .tarc &&
      scca.purpose == some .atopicSeverity && tarc.purpose == some .atopicSeverity &&
      a.id != b.id && a.site.patient == b.site.patient &&
      a.site.institution == b.site.institution && a.site.date.month == b.site.date.month then
    some ⟨D015.sccaChoice.source, [a.id, b.id], 1⟩
  else none

def plasmaProteinSelectionInput (c : D015.Context) (choices : List GroupChoice)
    (survey : List (Performance D015.Item)) : D015.Context :=
  { c with otherSelected := some (survey.filter fun p =>
      p.id != c.performance.id && retained choices p.id) }

/-- 同じ暦月の適用群を確認した二件に選択を渡す。 -/
def atopyProteinInput (scca tarc : D015.Context) (choices : List GroupChoice) :
    Option (D015.Context × D015.Context) := do
  let _ ← atopyProteinGroup scca tarc
  if retained choices scca.performance.id == retained choices tarc.performance.id then none else
  let project (c : D015.Context) : D015.Context :=
    { c with
      atopyTarcOrSccaSameMonth := some true
      atopyTarcOrSccaMain := some (retained choices c.performance.id) }
  return (project scca, project tarc)

/-- D016(1)。同じ項の方法を、確認した一連につき一回の実施料へまとめる。 -/
def cellularSeriesGroup (anchor : Performance D016.Item) (rows : List (Performance D016.Item)) :
    Option ChoiceGroup := do
  if !([D016.Item.tSubset, .granulocyteFunction, .granulocyteScreen].contains anchor.item) then
    none
  else
    let candidates := rows.filter fun p => p.item == anchor.item
    if !(candidates.contains anchor) ||
        candidates.any (fun p => (anchor.sameSeries p).isNone) then none else
      let ids := (candidates.filter fun p => anchor.sameSeries p == some true).map Performance.id
      if ids.length < 2 || ids.eraseDups != ids then none
      else some ⟨D016.seriesRule.source, ids, 1⟩

def selectedCellularInput (c : D016.Context) (choices : List GroupChoice)
    (rows : List (Performance D016.Item)) : Option D016.Context :=
  if rows.contains c.performance && retained choices c.performance.id then
    some { c with otherSelected := some (rows.filter fun p =>
      p.id != c.performance.id && retained choices p.id) }
  else none

/-- D017(2)。同じ顕微鏡検査として同定した方法別の実施を一回にまとめる。 -/
def microscopyMethodsGroup (anchor : Performance D017.Item)
    (rows : List (Performance D017.Item)) : Option ChoiceGroup :=
  let members := rows.filter fun p => anchor.sameSeries p == some true
  let ids := members.map Performance.id
  if !members.contains anchor || rows.any (fun p => (anchor.sameSeries p).isNone) ||
      ids.length < 2 || ids.eraseDups != ids then none
  else some ⟨D017.oneExamination.source, ids, 1⟩

def selectedMicroscopyInput (c : D017.Context) (choices : List GroupChoice)
    (rows : List (Performance D017.Item)) : Option D017.Context :=
  if rows.contains c.performance && retained choices c.performance.id &&
      !(rows.any fun p => (c.performance.sameSeries p).isNone) then
    some { c with selectedInExamination := some (rows.filter fun p =>
      c.performance.sameSeries p == some true && retained choices p.id) }
  else none

/-- D018(1)ウ。同一検体の通常培養と簡易培養を照合する。 -/
def cultureChoice (ordinary simple : D018.Context) : Option GroupChoice :=
  if ordinary.item != .simple && simple.item == .simple &&
      ordinary.performance.id != simple.performance.id &&
      ordinary.performance.sameSpecimen simple.performance == some true then
    some ⟨⟨D018.perSpecimen.source, [simple.performance.id], 0⟩, []⟩
  else none

/-- D018(1)エ。同一起因菌の検索群を確認済みで、血液二か所の例外を含まない場合。 -/
def cultureSiteGroup (rows : List D018.Context) : Option ChoiceGroup := do
  let first :: rest := rows | none
  let ids := rows.map (fun c => c.performance.id)
  if rest.isEmpty || ids.eraseDups != ids || rows.any (fun c => c.material == .blood) ||
      rest.any (fun c => c.performance.site.patient != first.performance.site.patient ||
        c.performance.site.institution != first.performance.site.institution) then none
  else some ⟨D018.selectedSite.source, ids, 1⟩

def cultureSiteInput (c : D018.Context) (rows : List D018.Context)
    (choices : List GroupChoice) (distinctBloodSites : Option Bool) : D018.Context :=
  let selected := (rows.filter fun r => retained choices r.performance.id).map
    (fun r => (r.performance, r.material))
  { c with searchSelection := some ⟨selected, distinctBloodSites⟩ }

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

/-- D019項1〜3。感受性を実際に検査した菌種の識別子から項と菌種数を求める。 -/
def susceptibilitySpeciesInput (c : D019.Context) (testedSpecies : List Nat) :
    Option D019.Context :=
  let count := testedSpecies.eraseDups.length
  match c.performance.item, count with
  | .resistance, _ | .combination, _ | _, 0 => none
  | _, n + 1 =>
    let item : D019.Item := match n with | 0 => .one | 1 => .two | _ => .threeOrMore
    some { c with performance := { c.performance with item }, speciesCount := count }

/-- D020(1)。全ての組で同時又は一連の採取を確認できる群を扱う。 -/
def mycobacterialCollectionGroup (rows : List (Performance D020.Item)) : Option ChoiceGroup :=
  let ids := rows.map Performance.id
  if ids.length < 2 || ids.eraseDups != ids ||
      !rows.all (fun a => rows.all fun b =>
        a.simultaneousWith b == some true || a.sameSeries b == some true) then none
  else some ⟨D020.collectionLimit.source, ids, 1⟩

def mycobacterialCollectionInput (c : D020.Context) (rows : List (Performance D020.Item))
    (choices : List GroupChoice) : Option D020.Context := do
  let _ ← mycobacterialCollectionGroup rows
  if !rows.contains c.performance || !retained choices c.performance.id then none
  else
    some { c with
      collection := some rows
      selected := some (rows.filter fun p => retained choices p.id) }

/-- D021。確認済みの同じ一連に属する同定法・培地の実施を一回にまとめる。 -/
def mycobacterialIdentificationGroup (anchor : Performance Unit) (rows : List (Performance Unit)) :
    Option ChoiceGroup :=
  let related := rows.filter fun p => anchor.sameSeries p == some true
  let ids := related.map Performance.id
  if !related.contains anchor || rows.any (fun p => (anchor.sameSeries p).isNone) ||
      ids.length < 2 || ids.eraseDups != ids then none
  else some ⟨D021.indication.source, ids, 1⟩

def mycobacterialIdentificationInput (c : D021.Context) (rows : List (Performance Unit))
    (choices : List GroupChoice) : Option D021.Context :=
  if rows.contains c.performance && retained choices c.performance.id &&
      !(rows.any fun p => (c.performance.sameSeries p).isNone) then
    some { c with selected := some (rows.filter fun p =>
      c.performance.sameSeries p == some true && retained choices p.id) }
  else none

/-- D023(36)(37)(39)。治療範囲を確認した既算定と当日の候補を受ける。
既算定には当日の選択を適用しない。相手の種類と一連の照合は各通知枝が行う。 -/
def panelBilledCompanions (prior pending : List (Performance D023.SeriesTest))
    (choices : List GroupChoice) : Option (List (Performance D023.SeriesTest)) :=
  let ids := (prior ++ pending).map Performance.id
  if ids.eraseDups != ids then none
  else some (prior ++ pending.filter fun p => retained choices p.id)

/-- D023(36)イの別算定一覧。適用できる外来経路は区分の制約で評価する。 -/
def pneumoniaPanelInput (c : D023.PneumoniaPanelContext)
    (prior pending : List (Performance D023.SeriesTest))
    (choices : List GroupChoice) : D023.PneumoniaPanelContext :=
  { c with separatelyBilled := panelBilledCompanions prior pending choices }

/-- D023(37)の一連の別算定候補を共通の採否から渡す。 -/
def respiratoryPanelInput (c : D023.RespiratoryPanelAssessment)
    (prior pending : List (Performance D023.SeriesTest))
    (choices : List GroupChoice) : D023.RespiratoryPanelAssessment :=
  { c with separatelyBilled := panelBilledCompanions prior pending choices }

/-- D023(39)の一連の別算定候補を共通の採否から渡す。 -/
def csfPanelInput (c : D023.CsfPanelContext)
    (prior pending : List (Performance D023.SeriesTest))
    (choices : List GroupChoice) : D023.CsfPanelContext :=
  { c with separatelyBilled := panelBilledCompanions prior pending choices }

/-- D023-2(1)イ。併施を確認したPBP2’項1とD023項17。 -/
def methicillinPbp2Group (gene : D023.MethicillinContext) (pbp2 : D023Other.Context) :
    Option ChoiceGroup :=
  let a := gene.performance
  let b := pbp2.performance
  if b.item == .pbp2 && a.id != b.id && a.site.patient == b.site.patient &&
      a.site.institution == b.site.institution then
    some ⟨D023Other.pbp2Main.source, [a.id, b.id], 1⟩
  else none

def methicillinPbp2Input (gene : D023.MethicillinContext) (pbp2 : D023Other.Context)
    (choices : List GroupChoice) : Option (Bool × D023Other.Context) := do
  let _ ← methicillinPbp2Group gene pbp2
  let geneSelected := retained choices gene.performance.id
  let pbpSelected := retained choices pbp2.performance.id
  if geneSelected == pbpSelected then none
  else
    let choice : D023Other.Pbp2Choice := if geneSelected then .d023MethicillinGene else .thisTest
    some (geneSelected, { pbp2 with pbp2Choice := some choice })

/-- D023-2(4)イの併施を確認した方法違いの二件。核酸検査を実施できるかは別に確認する。 -/
def rapidPbp2Group (ordinary rapid : D023Other.Context) : Option ChoiceGroup :=
  let a := ordinary.performance
  let b := rapid.performance
  if a.item == .pbp2 && b.item == .rapidPbp2 && a.id != b.id &&
      a.site.patient == b.site.patient && a.site.institution == b.site.institution then
    some ⟨D023Other.rapidPbp2Exclusion.source, [a.id, b.id], 1⟩
  else none

def rapidPbp2Input (ordinary rapid : D023Other.Context) (choices : List GroupChoice) :
    Option D023Other.Context := do
  let _ ← rapidPbp2Group ordinary rapid
  if retained choices rapid.performance.id then
    some { rapid with separatelyBilledPbp2 := some (retained choices ordinary.performance.id) }
  else none

/-- 包括に数えることを確認した実施を、指定の単位のIDで分ける。
対象日にID不明の候補があれば、その群の項目数は未確定とする。 -/
private def contextBundleMembers (route : BundleRoute) (anchor : Performance α)
    (performance : C → Performance α) (rows : List C) : Option (List C) := do
  let key ← bundleKey route anchor
  let sameDay := rows.filter fun c => (performance c).site == anchor.site
  if sameDay.any (fun c => (bundleKey route (performance c)).isNone) then none else
    return sameDay.filter fun c => bundleKey route (performance c) == some key

/-- Rh因子の種類・件数によらず、一検体について一つの個別評価へ渡す。 -/
def rhSpecimenInput (c : D011.Context) (rows : List (Performance Nat)) :
    Option D011.Context := do
  if c.performance.item != .otherRh then none else
    let members ← contextBundleMembers ⟨11, 3, .specimen⟩
      { c.performance with item := 0 } id rows
    if members.isEmpty then none else some { c with rhFactors := some members }

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

def selectedEndocrineDraw (choices : List GroupChoice) (site : Site) (draw : Nat)
    (firstDraw : Option Nat) (rows : List (Performance D008.BundleItem)) :
    Option (List D008.BundleItem) :=
  endocrineDraw site draw firstDraw (rows.filter fun p => retained choices p.id)

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

def selectedTumorMarkerDraw (choices : List GroupChoice) (anchor : Performance D009.Item)
    (rows : List D009.Context) (nippleDraw : Performance D009.Item → Option Nat) :
    Option D009.Bundle := do
  let group ← tumorMarkerDraw anchor rows nippleDraw
  let members := group.members.filter fun c => retained choices c.performance.id
  if members.isEmpty then none else some { group with members }

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

/-- 個別の採否を項11・46の検体群に反映する。候補の検体IDは除外前に確認する。 -/
def selectedViralSpecimen (choices : List GroupChoice) (anchor : Performance D012.RelatedTest)
    (rows : List (D012.Context × D012.Target)) : Option D012.ViralGroup := do
  let group ← viralSpecimen anchor (rows.filter fun p => p.1.performance.item == .local .viralTiter)
  let measurements := group.measurements.filter fun p => retained choices p.1.performance.id
  if measurements.isEmpty then none else some { group with measurements }

def selectedClassSpecimen (choices : List GroupChoice) (anchor : Performance D012.RelatedTest)
    (rows : List (D012.Context × D012.Target)) : Option D012.ClassGroup := do
  let group ← classSpecimen anchor
    (rows.filter fun p => p.1.performance.item == .local .classSpecificTiter)
  let measurements := group.measurements.filter fun p => retained choices p.1.performance.id
  if measurements.isEmpty then none else some { group with measurements }

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

/-- D008の包括に入る採否確認後の実施一覧から、通知(2)の項目候補を射影する。
当日の説明・文書交付・診療等は RapidTest の入力に残る。 -/
def endocrineRapidCountBasis (items : List D008.BundleItem) (item : D008.BundleItem) :
    Option RapidCountBasis :=
  if !items.contains item then none
  else if item.inNote && 3 ≤ (items.filter D008.BundleItem.inNote).length then
    some (.bundled .endocrine)
  else some .individual

/-- D009注2の対象実施が個別要件を満たすことは、既存の適格性で確認する。 -/
def tumorMarkerRapidCountBasis (g : D009.Bundle) (_ : g.Eligible) (id : Nat) :
    Option RapidCountBasis :=
  if g.members.any (fun c => c.performance.id == id) then
    some (if 2 ≤ g.items.length then .bundled .tumorMarker else .individual)
  else none

/-- 適格な項11・46の実施から、選択後の検体群に残った項目の判断料候補を得る。
候補性の結果は共通の区分振分けと同月の判断料評価に渡す。 -/
private def infectionJudgmentCandidate (rows : List (D012.Context × D012.Target))
    (id : Nat) : Option Bool :=
  if rows.any (fun row => row.1.performance.id == id) then some true else none

def viralJudgmentCandidate (g : D012.ViralGroup) (_ : g.Assessed) (id : Nat) : Option Bool :=
  infectionJudgmentCandidate g.measurements id

def classJudgmentCandidate (g : D012.ClassGroup) (_ : g.Assessed) (id : Nat) : Option Bool :=
  infectionJudgmentCandidate g.measurements id

/-- D013の包括に算入した実施をD026の免疫学的検査候補へ渡す。 -/
def hepatitisJudgmentCandidate (g : D013.DrawGroup) (_ : g.Assessed)
    (id : Nat) : Option Bool :=
  if g.tests.any (fun c => c.performance.id == id) then some true else none

theorem viral_specimen_judgment_candidate (g : D012.ViralGroup) (assessed : g.Assessed)
    (c : D012.Context) (target : D012.Target) (member : (c, target) ∈ g.measurements) :
    viralJudgmentCandidate g assessed c.performance.id = some true := by
  have present : g.measurements.any (fun row => row.1.performance.id == c.performance.id) = true :=
    List.any_eq_true.mpr ⟨(c, target), member, by simp⟩
  simp [viralJudgmentCandidate, infectionJudgmentCandidate, present]

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

/-- D023(16)ウ。同一検体を照合した廃液検査ではD419項1を別算定しない。 -/
theorem pylori_collection_not_separate (c : D023.PyloriContext)
    (row : Performance SpecimenCollection.Item) (collection : SpecimenCollection.Context)
    (separate : Bool) (pair : D023.PyloriCollectionPair c row collection separate)
    (waste : c.upperGiEndoscopyWaste = some true) :
    separate = false := by
  have rule := pair.2.2.2.2
  simpa [D023.pyloriCollection, waste] using rule

def collectionCharge (c : SpecimenCollection.Context)
    (h : ∃ p, SpecimenCollection.points c = some p) : Charge :=
  ⟨fun p => SpecimenCollection.points c = some p, by
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp, fun _ hq => Option.some.inj (hq.symm.trans hp)⟩⟩

private def sampleSite : Site := ⟨1, 2, ⟨⟨2026, 10⟩, ⟨22, by decide⟩⟩⟩

/-- PSA、遊離型PSA比、S2,3PSA、phiの四実施で、重複する三規則を
同じ併施範囲に適用した場合にも、phiを主とする選択は整合する。 -/
example :
    let rows : List (Performance D009.Companion) :=
      [⟨1, sampleSite, .psa, none, none, none, none⟩,
       ⟨2, sampleSite, .freePsaRatio, none, none, none, none⟩,
       ⟨3, sampleSite, .s23psa, none, none, none, none⟩,
       ⟨4, sampleSite, .phi, none, none, none, none⟩]
    let groups := ([.s23, .phiPsa, .phiRatio] : List MarkerCombination).filterMap
      (fun kind => markerGroup kind rows)
    (groups.map ChoiceGroup.members) = [[1, 2, 3, 4], [1, 4], [2, 4]] ∧
    SatisfiableAt ((groups.map fun g => GroupChoice.mk g [4]).map GroupChoice.rule) () := by
  refine ⟨rfl, ?_⟩
  apply (choice_rules_satisfiable _ ?_).mpr
  · intro a ha b hb id _ _
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    rfl
  · intro c hc
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hc
    change g ∈ [⟨D009.s23Choice.source, [1, 2, 3, 4], 1⟩,
      ⟨D009.phiPsaChoice.source, [1, 4], 1⟩,
      ⟨D009.phiRatioChoice.source, [2, 4], 1⟩] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ChoiceGroup.valid_single _ (by decide) rfl (by decide)
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ChoiceGroup.valid_single _ (by decide) rfl (by decide)
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ChoiceGroup.valid_single _ (by decide) rfl (by decide)
    · simp at hg


private def hbCoreSample : Performance D013.Item :=
  { id := 1, site := sampleSite, item := .hbcAntibody, draw := some 10, simultaneous := some 20 }

private def hbIgMSample : Performance D013.Item :=
  { hbCoreSample with id := 2, item := .hbcIgM, draw := some 11 }

private def hbCoreSampleGroup : ChoiceGroup :=
  ⟨D013.hbCoreChoice.source, [1, 2], 1⟩

example : hepatitisGroup .hbCore hbCoreSample [hbCoreSample, hbIgMSample] =
    some hbCoreSampleGroup := rfl

example : hepatitisGroup .hbCore hbCoreSample
    [hbCoreSample, { hbIgMSample with simultaneous := none }] = none := rfl

example : ∃ c : GroupChoice, c.group = hbCoreSampleGroup ∧ c.Valid :=
  hbCoreSampleGroup.exists_single (by decide) rfl (by decide)

example : (selectedHepatitisInput { performance := hbCoreSample } [⟨hbCoreSampleGroup, [1]⟩]
    [hbCoreSample, hbIgMSample]).map D013.Context.otherPayableLocal = some (some []) := rfl

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
