import Sanri.SpecimenCollection
import Sanri.History
import Sanri.BloodChemistryLate
import Sanri.BloodChemistryAdditional
import Sanri.GlycemicTests
import Sanri.CaseStudies.OutpatientBloodTests

/-! 既存の外来規則に渡す履歴の射影。各月次算定履歴から今回の算定候補を除いて渡す。 -/
namespace Sanri.MedicalFee

namespace SpecimenCollection

/-- 実施料の採血群と、別に確認したD400の採取記録を接続する。
D400の日内既算定・血液回路等の確認は既存の採取料評価へ渡す。 -/
def attachBloodDraw (test draw : History.Performance Unit) (collection : Context)
    (kind : Nat) (day : Examinations.DailyContext) :
    Option (Examinations.DailyContext × Assessment) := do
  if test.sameDraw draw != some true || collection.inpatient || !isD400 collection.item then none
  else
    let assessment ← assess collection
    let charge := (assessment.toCollection kind).toList
    return ({ day with collections := day.collections ++ charge }, assessment)

end SpecimenCollection

namespace BloodChemistry

/-- D007注の一採血。照会期間は当該採血に由来する全対象実施を含むものとする。
採血IDから通知(2)等の同時測定・併測は推論しない。 -/
def Draw.fromHistory (draw : Draw) (history : History.Snapshot (History.Performance Item))
    (anchor : History.Performance Item) (period : History.Period) : Option Draw := do
  let site := anchor.site
  let scope : History.Scope := ⟨site.patient, some site.institution, period⟩
  if !scope.Includes site || anchor.draw.isNone then none
  else
    let entries ← history.select History.Performance.site scope (fun _ => true)
    if !entries.contains anchor then none else
      let related ← entries.filterM anchor.sameDraw
      return { draw with performed := related.map History.Performance.item }

theorem Draw.fromHistory_note {draw projected : Draw} (h : draw.fromHistory history anchor period = some projected)
    (items : List Item) (selected : billableItems projected = some items) :
    (draw.fromHistory history anchor period).bind points = some p ↔ pointsRule.holds items p := by
  rw [pointsRule_iff]
  simp [h, points, selected, eq_comm]

end BloodChemistry

namespace BloodChemistryFurther

/-- D007(17)イの暦月枠。医療機関の射影範囲は明示的に渡す。 -/
def CarnitineContext.withMonthlyHistory (c : CarnitineContext)
    (history : History.ClaimHistory Item) (patient : Nat) (institution : Option Nat)
    (month : History.Month) : CarnitineContext :=
  { c with alreadyClaimedThisMonth :=
      (History.withinLimit history ⟨patient, institution, History.Period.month month⟩
        (fun item => item == .totalCarnitine || item == .freeCarnitine) 0).map (! ·) }

theorem carnitine_monthly_open (c : CarnitineContext) (history : History.ClaimHistory Item)
    (patient : Nat) (institution : Option Nat) (month : History.Month) :
    (c.withMonthlyHistory history patient institution month).alreadyClaimedThisMonth = some false ↔
      History.count history ⟨patient, institution, History.Period.month month⟩
        (fun item => item == .totalCarnitine || item == .freeCarnitine) = some 0 := by
  unfold CarnitineContext.withMonthlyHistory History.withinLimit
  cases History.count history ⟨patient, institution, History.Period.month month⟩
      (fun item => item == .totalCarnitine || item == .freeCarnitine) <;> simp

end BloodChemistryFurther

namespace BloodChemistryAdditional

/-- D007(22)。当月の実施から併施群を取り出し、主たる検査の選択は別に受ける。 -/
def monthlyTroponinsFromHistory
    (history : History.Snapshot (History.Performance Item))
    (site : History.Site) : Option (List Item) :=
  (history.select History.Performance.site site.monthScope
    (fun row => Group.monthlyTroponins.items.contains row.item)).map
    (List.map History.Performance.item)

theorem monthly_troponins_restrict
    (history : History.Snapshot (History.Performance Item)) (site : History.Site)
    (h : monthlyTroponinsFromHistory history site = some performed)
    (i : Item.troponinI ∈ performed)
    (t : Item.troponinTQualitative ∈ performed ∨ Item.troponinTQuantitative ∈ performed) :
    (monthlyTroponinsFromHistory history site).map Group.monthlyTroponins.restricts =
      some true := by
  rw [h]
  rcases t with t | t <;> simp_all [Group.restricts]

end BloodChemistryAdditional

namespace BloodChemistryLate

/-- D007(51)の暦月内の算定済み回数。医療機関の射影範囲は明示的に渡す。 -/
def Context.withVegfHistory (c : Context) (history : History.ClaimHistory Item)
    (patient : Nat) (institution : Option Nat) (month : History.Month) : Context :=
  { c with vegfPriorClaimsThisCalendarMonth :=
      History.count history ⟨patient, institution, History.Period.month month⟩ (· == .vegf) }

theorem vegf_monthly_open (c : Context) (history : History.ClaimHistory Item)
    (patient : Nat) (institution : Option Nat) (month : History.Month) :
    (c.withVegfHistory history patient institution month).vegfPriorClaimsThisCalendarMonth.map
        (· == 0) = some true ↔
      History.withinLimit history ⟨patient, institution, History.Period.month month⟩
        (· == .vegf) 0 = some true := by
  unfold Context.withVegfHistory History.withinLimit
  cases History.count history ⟨patient, institution, History.Period.month month⟩
    (· == .vegf) <;> simp

/-- D007(38)の同日枠。今回を選んだことを入力し、同じ枠の算定済み回数を照合する。 -/
def Context.withMyosinHistory (c : Context) (history : History.ClaimHistory Item)
    (patient : Nat) (institution : Option Nat) (date : History.Date)
    (selected : Bool) : Context :=
  { c with myosinDailySelection :=
      (History.withinLimit history ⟨patient, institution, History.Period.day date⟩
        (· == .cardiacMyosinLightChainI) 0).map (selected && ·) }

theorem myosin_daily_open (c : Context) (history : History.ClaimHistory Item)
    (patient : Nat) (institution : Option Nat) (date : History.Date) :
    (c.withMyosinHistory history patient institution date true).myosinDailySelection = some true ↔
      History.count history ⟨patient, institution, History.Period.day date⟩
        (· == .cardiacMyosinLightChainI) = some 0 := by
  simp [Context.withMyosinHistory, History.withinLimit_iff]

/-- D007(49)の患者通算枠。全機関の算定履歴を要求する。 -/
def Context.withInfliximabHistory (c : Context) (history : History.ClaimHistory Item)
    (patient : Nat) (date : History.Date) : Context :=
  { c with infliximabPriorClaims :=
      History.count history ⟨patient, none, History.Period.through date⟩ (· == .infliximabQualitative) }

theorem infliximab_limit_open (c : Context) (history : History.ClaimHistory Item)
    (patient : Nat) (date : History.Date) :
    (c.withInfliximabHistory history patient date).infliximabPriorClaims.map (fun n => decide (n < 3)) =
      some true ↔ History.withinLimit history ⟨patient, none, History.Period.through date⟩
        (· == .infliximabQualitative) 2 = some true := by
  unfold Context.withInfliximabHistory History.withinLimit
  cases History.count history ⟨patient, none, History.Period.through date⟩
    (· == .infliximabQualitative)
  · simp
  · simp only [Option.map_some, Option.some.injEq, decide_eq_true_eq]
    omega

end BloodChemistryLate

namespace GlycemicTests

/-- D005(9)・D007(14)の共有枠。三検査の全実施を同一患者・機関・暦月へ射影する。 -/
def Month.fromHistory (history : History.Snapshot (History.Performance Item))
    (site : History.Site) (exception : Option Exception) : Option Month := do
  let rows ← history.select History.Performance.site site.monthScope (fun _ => true)
  return { performed := rows.map (fun row => ⟨row.id, row.item⟩), exception }

theorem history_ordinary_no_two
    (hm : Month.fromHistory history site (some .none) = some month)
    (performed : month.performed.length ≥ 2)
    (h : Logic.Satisfies ordinaryRules month charged) : charged.length ≤ 1 := by
  apply ordinary_no_two month charged _ performed h
  unfold Month.fromHistory at hm
  cases hs : History.Snapshot.select history History.Performance.site site.monthScope
    (fun _ => true)
  · simp [hs] at hm
  · simp [hs] at hm
    subst month
    rfl

end GlycemicTests

namespace SpecimenJudgment

/-- D026注1・注4・通知(2)(4)(7)の算定済み履歴で区別する項目。 -/
inductive MonthlyClaim where
  | category (category : Category)
  | managementD026
  | managementD027
  deriving DecidableEq, Repr

def MonthlyClaim.category? : MonthlyClaim → Option Category
  | .category cat => some cat
  | _ => none

/-- 同一患者・機関の暦月内の算定済み情報。初回検査の実施日は別の事実。 -/
def Context.withMonthlyHistory (c : Context) (history : History.ClaimHistory MonthlyClaim)
    (site : History.Site) : Option Context := do
  let rows ← history.toSnapshot.select History.Claim.site site.monthScope (fun _ => true)
  return { c with
    categoriesClaimedThisMonth := rows.filterMap (fun row => row.item.category?)
    managementClaimsThisMonth := (rows.filter (fun row => row.item.category?.isNone)).length }

theorem monthly_history_categories (c : Context) (history : History.ClaimHistory MonthlyClaim)
    (site : History.Site) (h : c.withMonthlyHistory history site = some projected)
    (category : Category) :
    category ∈ projected.categoriesClaimedThisMonth ↔
      ∃ row ∈ history.entries, site.monthScope.Includes row.site = true ∧
        row.item = .category category := by
  by_cases known : history.coverage.Covers site.monthScope
  · simp [Context.withMonthlyHistory, History.Snapshot.select, known] at h
    subst projected
    simp [List.mem_filterMap, MonthlyClaim.category?]
    constructor
    · rintro ⟨row, ⟨mem, includes⟩, item⟩
      refine ⟨row, mem, includes, ?_⟩
      cases hi : row.item <;> simp_all
    · rintro ⟨row, mem, includes, item⟩
      exact ⟨row, ⟨mem, includes⟩, by simp [item]⟩
  · simp [Context.withMonthlyHistory, History.Snapshot.select, known] at h

theorem monthly_management_count (c : Context) (history : History.ClaimHistory MonthlyClaim)
    (site : History.Site) (h : c.withMonthlyHistory history site = some projected) :
    History.count history site.monthScope (fun item => item.category?.isNone) =
      some projected.managementClaimsThisMonth := by
  by_cases known : history.coverage.Covers site.monthScope
  · simp [Context.withMonthlyHistory, History.Snapshot.select, known] at h
    subst projected
    simp [History.count, History.Snapshot.select, known, Bool.and_comm]
  · simp [Context.withMonthlyHistory, History.Snapshot.select, known] at h

/-- 通知D026(2)の初回日を調べるための区分の集合。同日内の実施順は問わない。 -/
def earlierCategories (history : History.Snapshot (History.Performance Test))
    (site : History.Site) : Option (List Category) :=
  (history.select History.Performance.site site.monthScope
    (fun row => decide (row.site.date.key < site.date.key))).map
    (fun rows => (rows.filterMap (fun row => categoryFor row.item)).eraseDups)

theorem earlier_categories_iff (history : History.Snapshot (History.Performance Test))
    (site : History.Site) (h : earlierCategories history site = some categories)
    (category : Category) :
    category ∈ categories ↔ ∃ row ∈ history.entries,
      (site.monthScope.Includes row.site = true ∧ row.site.date.key < site.date.key) ∧
      categoryFor row.item = some category := by
  by_cases known : history.coverage.Covers site.monthScope
  · simp [earlierCategories, History.Snapshot.select, known] at h
    subst categories
    simp [List.mem_filterMap, and_assoc]
  · simp [earlierCategories, History.Snapshot.select, known] at h

/-- 判断料本体の同日入力。包括照合はD025とB001の15を対象とする。
照合できていない実施をリストに含めて通常算定へ進めない。 -/
structure DailyJudgment where
  site : History.Site
  tests : List IncludedTest
  coveredByD027 : Bool
  claims : History.ClaimHistory MonthlyClaim
  performances : History.Snapshot (History.Performance Test)

def DailyJudgment.hasTest (c : DailyJudgment) (category : Category) : Bool :=
  c.tests.any (fun entry => entry.separateEligibility == some true &&
    standardizedCategoryFor entry.test == some category)

def DailyJudgment.previousClaimLimit (c : DailyJudgment) (category : Category) : Option Bool :=
  History.withinLimit c.claims c.site.monthScope (· == .category category) 0

def DailyJudgment.firstDay (c : DailyJudgment) (category : Category) : Option Bool :=
  (c.performances.select History.Performance.site c.site.monthScope
    (fun row => decide (row.site.date.key < c.site.date.key) &&
      standardizedCategoryFor row.item == some category)).map List.isEmpty

def DailyJudgment.selectable (c : DailyJudgment) (category : Category) : Bool :=
  c.hasTest category && !(c.coveredByD027 && includedInD027 category) &&
    c.previousClaimLimit category == some true && c.firstDay category == some true

def DailyJudgment.coverageResolved (c : DailyJudgment) : Bool :=
  c.tests.all (fun t => t.separateEligibility.isSome)

def DailyJudgment.Known (c : DailyJudgment) : Prop :=
  c.claims.coverage.Covers c.site.monthScope ∧ c.performances.coverage.Covers c.site.monthScope ∧
    c.coverageResolved = true

private def dailyNotice (location : String) : Logic.SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF402頁 D026" ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def initialDayRule : Logic.Rule DailyJudgment (List Category) :=
  ⟨"notice/D026/paragraph/2", dailyNotice "(2)", fun c categories =>
    ∀ category ∈ categories, c.previousClaimLimit category = some true ∧
      c.firstDay category = some true⟩

def sharedMonthlyLimit : Logic.Rule DailyJudgment (List Category) :=
  ⟨"notice/D026/paragraph/4", dailyNotice "(4)", fun c categories =>
    ∀ category ∈ categories, c.previousClaimLimit category = some true⟩

def monthlyCategoryRule : Logic.Rule DailyJudgment (List Category) :=
  ⟨"primary/D026/note/1",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
      "PDF192頁 D026注1", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun c categories => ∀ category ∈ categories, c.previousClaimLimit category = some true ∧
      (c.coveredByD027 = true → includedInD027 category = false)⟩

/-- 判断料の算定を選ぶ区分をすべて列挙した内訳の合計。 -/
def multipleCategoriesRule : Logic.Rule (DailyJudgment × List Category) Nat :=
  ⟨"notice/D026/paragraph/3", dailyNotice "(3)", fun (_, categories) points =>
    points = (categories.map scheduledPoints).sum⟩

def executionAndJudgmentRule : Logic.Rule (Nat × Nat) Nat :=
  ⟨"notice/D026/paragraph/1", dailyNotice "(1)", fun (execution, judgment) total =>
    total = execution + judgment⟩

def DailyJudgment.categories (c : DailyJudgment) : List Category :=
  allCategories.filter c.selectable

def DailyJudgment.points (c : DailyJudgment) : Option Nat :=
  if c.claims.coverage.Covers c.site.monthScope ∧ c.performances.coverage.Covers c.site.monthScope ∧
      c.coverageResolved = true
  then some ((c.categories.map scheduledPoints).sum)
  else none

theorem daily_categories_iff (c : DailyJudgment) (category : Category) :
    category ∈ c.categories ↔ c.hasTest category = true ∧
      (c.coveredByD027 = true → includedInD027 category = false) ∧
      c.previousClaimLimit category = some true ∧ c.firstDay category = some true := by
  have mem : category ∈ allCategories := by cases category <;> decide
  cases covered : c.coveredByD027 <;>
    simp [DailyJudgment.categories, DailyJudgment.selectable, List.mem_filter, mem,
      Bool.and_eq_true, covered, and_assoc]

theorem daily_points (c : DailyJudgment) (h : c.Known) (p : Nat) :
    initialDayRule.holds c c.categories ∧ sharedMonthlyLimit.holds c c.categories ∧
      monthlyCategoryRule.holds c c.categories ∧ multipleCategoriesRule.holds (c, c.categories) p
      ↔ c.points = some p := by
  have eligible := fun category (mem : category ∈ c.categories) =>
    (daily_categories_iff c category).mp mem
  have initial : initialDayRule.holds c c.categories :=
    fun category mem => (eligible category mem).2.2
  have shared : sharedMonthlyLimit.holds c c.categories :=
    fun category mem => (eligible category mem).2.2.1
  have monthly : monthlyCategoryRule.holds c c.categories :=
    fun category mem => ⟨(eligible category mem).2.2.1, (eligible category mem).2.1⟩
  simp [initial, shared, monthly, multipleCategoriesRule, DailyJudgment.points,
    DailyJudgment.Known] at h ⊢
  simp [h, eq_comm]

/-- 判断料本体の算定候補と管理加算の届出・適合は別の確認事項。 -/
structure ManagementEvidence where
  day : DailyJudgment
  facilityComplies : Option Bool := none
  facilityNotified : Option Bool := none

def ManagementEvidence.monthlyLimit (c : ManagementEvidence) : Option Bool :=
  History.withinLimit c.day.claims c.day.site.monthScope (fun item => item.category?.isNone) 0

def managementPrimary : Logic.Rule ManagementEvidence Nat :=
  ⟨"primary/D026/note/4",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
      "PDF192頁 D026注4", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun c p => c.facilityComplies = some true ∧ c.facilityNotified = some true ∧
      c.monthlyLimit = some true ∧ managementI.holds () p⟩

def managementNotification : Logic.Rule ManagementEvidence Unit :=
  ⟨"notice/D026/paragraph/7",
    { dailyNotice "(7)" with location := "PDF403頁 D026(7)" },
    fun c _ => c.day.categories ≠ [] ∧ c.monthlyLimit = some true⟩

/-- 施設が入院患者にⅡ〜Ⅳを算定することは、外来のⅠの除外条件に含めない。 -/
def managementOutpatient : Logic.Rule ManagementEvidence Nat :=
  ⟨"notice/D026/paragraph/8",
    { dailyNotice "(8)" with location := "PDF403頁 D026(8)" },
    fun c points => managementPrimary.holds c points ∧ managementNotification.holds c ()⟩

theorem eligible_management_points (c : ManagementEvidence) (points : Nat)
    (h : managementOutpatient.holds c points) : points = 40 :=
  h.1.2.2.2

theorem daily_determines : Logic.DeterminesOn
    (fun c : DailyJudgment × List Category => c.1.Known ∧ c.2 = c.1.categories)
    [multipleCategoriesRule] := by
  intro c _
  refine ⟨⟨(c.2.map scheduledPoints).sum, ?_⟩, ?_⟩
  · simp [Logic.satisfies_cons, Logic.satisfies_nil, multipleCategoriesRule]
  · intro a b ha hb
    exact (ha multipleCategoriesRule (by simp)).trans (hb multipleCategoriesRule (by simp)).symm

structure FacilityCheck where
  complies : Option Bool := none
  notified : Option Bool := none

/-- 加算の候補を確認した外来1日分。none は追加の算定候補なしと確認した場合に使う。 -/
structure OutpatientDay where
  day : DailyJudgment
  insuranceMedicalInstitution : Bool
  status : ConsultationGeneralRules.PatientStatus
  management : Option FacilityCheck
  marrow : Option MarrowEvidence
  electrophoresis : Option DiagnosisEvidence

private def OutpatientDay.performed (c : OutpatientDay) (test : Test) : Prop :=
  test ∈ c.day.tests.map IncludedTest.test

private def OutpatientDay.managementEvidence (c : OutpatientDay) (facility : FacilityCheck) :
    ManagementEvidence :=
  ⟨c.day, facility.complies, facility.notified⟩

def OutpatientDay.Eligible (c : OutpatientDay) : Prop :=
  c.insuranceMedicalInstitution = true ∧ c.status = .outpatient ∧ c.day.Known ∧
    (∀ f, c.management = some f → managementOutpatient.holds (c.managementEvidence f) managementIPoints) ∧
    (∀ e, c.marrow = some e → e.site = c.day.site ∧ c.performed e.test ∧
      marrowNotification.holds e ()) ∧
    (∀ e, c.electrophoresis = some e → c.performed e.test ∧ electrophoresisNotification.holds e ())

def OutpatientDay.PermitsPoints (c : OutpatientDay) (points : Nat) : Prop :=
  ∃ base management marrow electrophoresis,
    multipleCategoriesRule.holds (c.day, c.day.categories) base ∧
    (match c.management with
      | none => management = 0
      | some f => managementOutpatient.holds (c.managementEvidence f) management) ∧
    (match c.marrow with
      | none => marrow = 0
      | some e => marrowAddition.holds e.test marrow ∧ marrowNotification.holds e ()) ∧
    (match c.electrophoresis with
      | none => electrophoresis = 0
      | some e => electrophoresisAddition.holds e.test electrophoresis ∧ electrophoresisNotification.holds e ()) ∧
    points = base + management + marrow + electrophoresis

def OutpatientDay.points (c : OutpatientDay) : Option Nat :=
  c.day.points.map fun base => base +
    (if c.management.isSome then managementIPoints else 0) +
    (if c.marrow.isSome then marrowPoints else 0) +
    (if c.electrophoresis.isSome then electrophoresisPoints else 0)

theorem outpatient_day_iff (c : OutpatientDay) (hc : c.Eligible) (points : Nat) :
    c.PermitsPoints points ↔ c.points = some points := by
  obtain ⟨_, _, hk, hm, hb, he⟩ := hc
  have base : c.day.points = some ((c.day.categories.map scheduledPoints).sum) := by
    simp [DailyJudgment.points, DailyJudgment.Known] at hk ⊢
    exact hk
  have m (p : Nat) :
      (match c.management with
      | none => p = 0
      | some f => managementOutpatient.holds (c.managementEvidence f) p) ↔
      p = (if c.management.isSome then managementIPoints else 0) := by
    cases h : c.management with
    | none => simp
    | some f =>
      refine ⟨fun valid => valid.1.2.2.2, ?_⟩
      intro eq
      simpa [eq] using hm f h
  have b (p : Nat) :
      (match c.marrow with
      | none => p = 0
      | some e => marrowAddition.holds e.test p ∧ marrowNotification.holds e ()) ↔
      p = (if c.marrow.isSome then marrowPoints else 0) := by
    cases h : c.marrow with
    | none => simp
    | some e =>
      have n := (hb e h).2.2
      exact ⟨fun valid => valid.1.1, fun eq => ⟨⟨eq, n.1.1⟩, n⟩⟩
  have e (p : Nat) :
      (match c.electrophoresis with
      | none => p = 0
      | some e => electrophoresisAddition.holds e.test p ∧ electrophoresisNotification.holds e ()) ↔
      p = (if c.electrophoresis.isSome then electrophoresisPoints else 0) := by
    cases h : c.electrophoresis with
    | none => simp
    | some report =>
      have n := (he report h).2
      exact ⟨fun valid => valid.1.1, fun eq => ⟨⟨eq, n.1⟩, n⟩⟩
  unfold OutpatientDay.PermitsPoints OutpatientDay.points
  simp only [multipleCategoriesRule, m, b, e, base, Option.map_some, Option.some.injEq]
  constructor
  · rintro ⟨_, _, _, _, rfl, rfl, rfl, rfl, eq⟩
    exact eq.symm
  · intro eq
    exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, eq.symm⟩

theorem outpatient_day_determines (c : OutpatientDay) (h : c.Eligible) :
    ∃ points, c.PermitsPoints points ∧ ∀ other, c.PermitsPoints other → other = points := by
  have hk := h.2.2.1
  have hp : c.points = some (((c.day.categories.map scheduledPoints).sum) +
      (if c.management.isSome then managementIPoints else 0) +
      (if c.marrow.isSome then marrowPoints else 0) +
      (if c.electrophoresis.isSome then electrophoresisPoints else 0)) := by
    simp [OutpatientDay.points, DailyJudgment.points, DailyJudgment.Known] at hk ⊢
    exact hk
  exact ⟨_, (outpatient_day_iff c h _).mpr hp,
    fun _ other => Option.some.inj (((outpatient_day_iff c h _).mp other).symm.trans hp)⟩

/-- 確認済みの日の判断料と加算を第1節の実施料集計へ合流させる。 -/
def OutpatientDay.applyToSpecimen (c : OutpatientDay) (_ : c.Eligible)
    (specimen : Examinations.SpecimenContext) : Option Examinations.SpecimenContext := do
  if specimen.inpatient then none else
    let judgmentPoints ← c.points
    some { specimen with judgmentPoints }

private def dailyExample : DailyJudgment :=
  let site : History.Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩
  { site
    tests := [{ test := { major := 23, ordinaryCategory := .microbiological }
                b001_15ClaimedThisMonth := false
                d025ClaimedThisMonth := false }]
    coveredByD027 := false
    claims := ⟨⟨site.monthScope, []⟩, by simp⟩
    performances := ⟨site.monthScope, []⟩ }

example : dailyExample.points = some 150 := by decide

private def outpatientDayExample : OutpatientDay :=
  ⟨dailyExample, true, .outpatient, some ⟨some true, some true⟩, none, none⟩

example : outpatientDayExample.Eligible := by
  simp [OutpatientDay.Eligible, outpatientDayExample, dailyExample, DailyJudgment.Known,
    DailyJudgment.coverageResolved, IncludedTest.separateEligibility, OutpatientDay.managementEvidence,
    managementOutpatient, managementPrimary, managementNotification, ManagementEvidence.monthlyLimit,
    managementI]
  decide

example : outpatientDayExample.points = some 190 := by decide
example : ({ dailyExample with coveredByD027 := true } : DailyJudgment).points = some 0 := by decide
example : ({ dailyExample with
    claims := ⟨⟨{ dailyExample.site.monthScope with patient := 2 }, []⟩, by simp⟩
  } : DailyJudgment).points = none := by decide

end SpecimenJudgment
end Sanri.MedicalFee

namespace Sanri.CaseStudies.OutpatientBloodTests

/-- D026の初回実施日を調べる履歴射影。他の事例入力は保持する。 -/
def Context.withJudgmentPerformanceHistory (c : Context)
    (history : History.Snapshot (History.Performance MedicalFee.SpecimenJudgment.Test))
    (site : History.Site) : Context :=
  { c with earlierTestCategoriesThisMonth := MedicalFee.SpecimenJudgment.earlierCategories history site }

end Sanri.CaseStudies.OutpatientBloodTests

namespace Sanri.MedicalFee

section Examples

private def october : History.Month := ⟨2026, 9⟩
private def today : History.Date := ⟨october, ⟨21, by decide⟩⟩
private def yesterday : History.Date := ⟨october, ⟨20, by decide⟩⟩
private def site : History.Site := ⟨1, 10, today⟩
private def otherFacility : History.Site := { site with institution := 11 }
private def yesterdaySite : History.Site := { site with date := yesterday }

private def carnitineContext : BloodChemistryFurther.CarnitineContext :=
  ⟨some .congenitalMetabolicDisorder, some true, some true, none, none⟩

private def carnitineHistory :
    History.ClaimHistory BloodChemistryFurther.Item :=
  ⟨⟨site.monthScope, [⟨1, yesterdaySite, .freeCarnitine, none⟩]⟩, by decide⟩

example : (carnitineContext.withMonthlyHistory carnitineHistory 1 (some 10)
    october).eligible = some false := by decide

example : (carnitineContext.withMonthlyHistory
    ⟨⟨site.monthScope, []⟩, by decide⟩ 1 (some 10) october).eligible = some true := by decide

example : (carnitineContext.withMonthlyHistory carnitineHistory 1 none
    october).eligible = none := by decide

private def vegfContext : BloodChemistryLate.Context :=
  { item := .vegf, method := some .elisa, poemsDiagnosisOrFollowUp := some true }

private def lateHistory : History.ClaimHistory BloodChemistryLate.Item :=
  ⟨⟨site.monthScope, [⟨1, yesterdaySite, .vegf, none⟩,
    ⟨2, yesterdaySite, .cardiacMyosinLightChainI, none⟩]⟩, by decide⟩

example : BloodChemistryLate.assess
    (vegfContext.withVegfHistory lateHistory 1 (some 10) october) = .ineligible := by decide

example : BloodChemistryLate.assess (vegfContext.withVegfHistory
    ⟨⟨site.monthScope, []⟩, by decide⟩ 1 (some 10) october) = .payable 460 := by decide

example : BloodChemistryLate.assess
    (vegfContext.withVegfHistory lateHistory 1 (some 11) october) = .unresolved := by decide

private def myosinContext : BloodChemistryLate.Context := { item := .cardiacMyosinLightChainI }

example : BloodChemistryLate.assess
    (myosinContext.withMyosinHistory lateHistory 1 (some 10) yesterday true) =
      .ineligible := by decide

example : BloodChemistryLate.assess
    (myosinContext.withMyosinHistory lateHistory 1 (some 10) today true) =
      .payable 184 := by decide

example : BloodChemistryLate.assess
    (myosinContext.withMyosinHistory lateHistory 1 (some 11) today true) =
      .unresolved := by decide

private def infliximabContext : BloodChemistryLate.Context :=
  { item := .infliximabQualitative, method := some .immunochromatography,
    rheumatoidArthritis := some true, infliximabDoseDecision := some true }

private def lifetimeScope : History.Scope := ⟨1, none, History.Period.through today⟩

private def infliximabClaims : List (History.Claim BloodChemistryLate.Item) :=
  [⟨1, yesterdaySite, .infliximabQualitative, none⟩,
   ⟨2, yesterdaySite, .infliximabQualitative, none⟩,
   ⟨3, { otherFacility with date := yesterday }, .infliximabQualitative, none⟩]

example : BloodChemistryLate.assess (infliximabContext.withInfliximabHistory
    ⟨⟨lifetimeScope, infliximabClaims⟩, by decide⟩ 1 today) = .ineligible := by decide

example : BloodChemistryLate.assess (infliximabContext.withInfliximabHistory
    ⟨⟨lifetimeScope, infliximabClaims.take 2⟩, by decide⟩ 1 today) = .payable 310 := by decide

example : BloodChemistryLate.assess
    (infliximabContext.withInfliximabHistory lateHistory 1 today) = .unresolved := by decide

private def anchor : History.Performance BloodChemistry.Item :=
  { id := 1, site, item := .bun, draw := some 1 }

private def drawHistory (fifthDraw : Nat) :
    History.Snapshot (History.Performance BloodChemistry.Item) :=
  ⟨site.monthScope, [anchor, { anchor with id := 2, item := .ast },
    { anchor with id := 3, item := .alt }, { anchor with id := 4, item := .ck },
    { anchor with id := 5, item := .ld, draw := some fifthDraw }]⟩

private def draw : BloodChemistry.Draw := { performed := [] }

example : ((draw.fromHistory (drawHistory 1) anchor site.monthScope.period).bind
    BloodChemistry.points) = some 93 := by decide

example : ((draw.fromHistory (drawHistory 2) anchor site.monthScope.period).bind
    BloodChemistry.points) = some ([.bun, .ast, .alt, .ck].map BloodChemistry.Item.points).sum := by decide

example : ((draw.fromHistory (drawHistory 1) anchor (History.Period.year 2026)).bind
    BloodChemistry.points) = none := by decide

private def glycemicHistory : History.Snapshot (History.Performance GlycemicTests.Item) :=
  ⟨site.monthScope, [⟨1, yesterdaySite, .a1c, none, none, none, none⟩,
    ⟨2, site, .anhydroglucitol, none, none, none, none⟩]⟩

example : GlycemicTests.assess
    (GlycemicTests.Month.fromHistory glycemicHistory site (some .none))
    ⟨1, some 2⟩ = .invalidSelection := by decide

example : GlycemicTests.assess
    (GlycemicTests.Month.fromHistory glycemicHistory site (some .none))
    ⟨1, none⟩ = .resolved ⟨1, .a1c⟩ none := by decide

example : GlycemicTests.assess
    (GlycemicTests.Month.fromHistory glycemicHistory otherFacility (some .none))
    ⟨1, none⟩ = .unresolved := by decide

private def troponinHistory :
    History.Snapshot (History.Performance BloodChemistryAdditional.Item) :=
  ⟨site.monthScope, [{ id := 1, site, item := .troponinI },
    { id := 2, site := yesterdaySite, item := .troponinTQualitative }]⟩

example : (BloodChemistryAdditional.monthlyTroponinsFromHistory troponinHistory site).map
    BloodChemistryAdditional.Group.monthlyTroponins.restricts = some true := by decide

example : (BloodChemistryAdditional.monthlyTroponinsFromHistory
    { troponinHistory with entries := troponinHistory.entries.take 1 } site).map
    BloodChemistryAdditional.Group.monthlyTroponins.restricts = some false := by decide

example : BloodChemistryAdditional.monthlyTroponinsFromHistory troponinHistory otherFacility =
    none := by decide

private def judgmentContext : SpecimenJudgment.Context :=
  { tests := [{ ordinaryCategory := .hematological, major := 5 }] }

private def judgmentHistory : History.ClaimHistory SpecimenJudgment.MonthlyClaim :=
  ⟨⟨site.monthScope, [⟨1, yesterdaySite, .category .hematological, none⟩]⟩, by decide⟩

example : ((judgmentContext.withMonthlyHistory judgmentHistory site).bind
    SpecimenJudgment.points) = some 0 := by decide

example : ((judgmentContext.withMonthlyHistory ⟨⟨site.monthScope, []⟩, by decide⟩ site).bind
    SpecimenJudgment.points) = some 125 := by decide

example : ((judgmentContext.withMonthlyHistory judgmentHistory otherFacility).bind
    SpecimenJudgment.points) = none := by decide

private def judgmentPerformanceHistory :
    History.Snapshot (History.Performance SpecimenJudgment.Test) :=
  ⟨site.monthScope, [⟨1, yesterdaySite, { ordinaryCategory := .hematological, major := 5 },
    none, none, none, none⟩]⟩

example : SpecimenJudgment.earlierCategories judgmentPerformanceHistory site =
    some [.hematological] := by decide

example : SpecimenJudgment.earlierCategories judgmentPerformanceHistory yesterdaySite =
    some [] := by decide

example : SpecimenJudgment.earlierCategories judgmentPerformanceHistory otherFacility =
    none := by decide

private def managementContext : SpecimenJudgment.Context :=
  { judgmentContext with management := .categoryI, managementStandardNotified := true }

private def managementHistory : History.ClaimHistory SpecimenJudgment.MonthlyClaim :=
  ⟨⟨site.monthScope, [⟨1, yesterdaySite, .managementD027, none⟩]⟩, by decide⟩

example : ((managementContext.withMonthlyHistory managementHistory site).bind
    SpecimenJudgment.assess).map SpecimenJudgment.Assessment.management = some 0 := by decide

example : ((managementContext.withMonthlyHistory ⟨⟨site.monthScope, []⟩, by decide⟩ site).bind
    SpecimenJudgment.assess).map SpecimenJudgment.Assessment.management = some 40 := by decide

example : (managementContext.withMonthlyHistory managementHistory otherFacility).isNone = true :=
  by decide

end Examples
end Sanri.MedicalFee
