import Sanri.History
import Sanri.BloodChemistryLate
import Sanri.BloodChemistryAdditional
import Sanri.GlycemicTests
import Sanri.CaseStudies.OutpatientBloodTests

/-! 既存の外来規則に渡す履歴の射影。各月次算定履歴から今回の算定候補を除いて渡す。 -/
namespace Sanri.MedicalFee

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
