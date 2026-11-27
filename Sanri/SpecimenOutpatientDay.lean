import Sanri.D023References
import Sanri.D400

namespace Sanri.MedicalFee.SpecimenOutpatientDay

open Sanri.History Sanri.Logic

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF173頁 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

inductive Visit where
  | initial | revisit | homeCare | other
  deriving DecidableEq

/-- 診療機関と採取実施者の勤務先は別の入力。日付は採取日を基準にする。 -/
structure VisitingNurseCollection where
  performance : Performance Unit
  physicianVisitDay : Bool
  visit : Visit
  directedByResponsiblePhysician : Bool
  visitingNurseOrEquivalent : Bool
  remoteWithNurse : Bool
  remoteVisitSupportFee : Bool
  visitingNurseStation : Bool
  visitingNursingToday : Bool
  performedAsPartOfVisitingNursing : Bool

def VisitingNurseCollection.applies (c : VisitingNurseCollection) : Bool :=
  c.directedByResponsiblePhysician && c.visitingNurseOrEquivalent &&
    ((!c.physicianVisitDay && decide (c.visit ≠ .other)) ||
      (c.remoteWithNurse && c.visitingNurseStation && c.performedAsPartOfVisitingNursing &&
        (c.remoteVisitSupportFee || c.visitingNursingToday)))

structure VisitingNurseObligations where
  executionInstitution : Option Nat
  supplySamplingMaterials : Bool
  deriving DecidableEq

def correctedVisitingNurseRule : Rule VisitingNurseCollection VisitingNurseObligations :=
  ⟨"notice/ch2-part3/general/18", notice "PDF329頁 第3部通則18・2026-04-02訂正反映",
    fun c r =>
      r.executionInstitution = (if c.applies then some c.performance.site.institution else none) ∧
      (r.supplySamplingMaterials = true ↔ c.applies = true)⟩

def visitingNurseObligations (c : VisitingNurseCollection) : VisitingNurseObligations :=
  if c.applies then ⟨some c.performance.site.institution, true⟩ else ⟨none, false⟩

theorem visitingNurse_iff (c : VisitingNurseCollection) (r : VisitingNurseObligations) :
    correctedVisitingNurseRule.holds c r ↔ r = visitingNurseObligations c := by
  cases r
  cases hc : c.applies <;> simp [correctedVisitingNurseRule, visitingNurseObligations, hc]

def visitingNurseDocumentation : Rule VisitingNurseCollection (Option Date) :=
  ⟨"notice/ch2-part3/general/18", notice "PDF329頁 第3部通則18・摘要欄",
    fun c entry => c.applies = true → c.physicianVisitDay = false →
      entry = some c.performance.site.date⟩

inductive Selection where
  | none | emergency | rapid
  deriving DecidableEq

structure EmergencyTest where
  /-- 医師による緊急性の判断と通知(6)の重篤性・待機不能の確認。 -/
  physicianDeterminedUrgent : Bool
  seriousAndCannotWait : Bool
  ownStaffAndEquipment : Bool
  outOfHoursConsultation : Bool
  outOfHoursStart : Bool
  outpatientAtTest : Bool

structure RapidTest where
  /-- 検査項目の同一性は当日の実施記録で解決済み。 -/
  item : Nat
  designated : Bool
  performedAtInstitution : Bool
  explainedAndWrittenToday : Bool
  careBasedOnResultToday : Bool
  outpatientAtTest : Bool

def RapidTest.eligible (t : RapidTest) : Bool :=
  t.designated && t.performedAtInstitution && t.explainedAndWrittenToday &&
    t.careBasedOnResultToday && t.outpatientAtTest

structure AdditionContext where
  site : Site
  selection : Selection
  emergencyTests : List EmergencyTest
  /-- 包括後の算定行ではなく、A002包括分も含めた実施項目の一覧。 -/
  rapidTests : List RapidTest
  emergencyClaimed : Option Bool
  /-- 確認済みの当日先行加算項目ID。 -/
  priorRapidItems : Option (List Nat)
  nightEarlyMorningAddition : Bool

def AdditionContext.rapidCandidates (c : AdditionContext) (prior : List Nat) : List Nat :=
  ((c.rapidTests.filter RapidTest.eligible).map RapidTest.item).eraseDups.filter
    (fun item => !prior.contains item)

private theorem deduplicatedItems_nodup (items : List Nat) : items.eraseDups.Nodup := by
  have loop (remaining seen : List Nat) (distinct : seen.Nodup) :
      (List.eraseDupsBy.loop (· == ·) remaining seen).Nodup := by
    induction remaining generalizing seen with
    | nil => simpa [List.eraseDupsBy.loop] using distinct.perm (List.reverse_perm seen).symm
    | cons item rest ih =>
      cases found : seen.any (item == ·)
      · rw [List.eraseDupsBy.loop, found]
        apply ih
        refine List.nodup_cons.mpr ⟨?_, distinct⟩
        intro member
        have existsTrue : seen.any (item == ·) = true :=
          List.any_eq_true.mpr ⟨item, member, by simp⟩
        simp [found] at existsTrue
      · rw [List.eraseDupsBy.loop, found]
        exact ih seen distinct
  exact loop items [] List.nodup_nil

/-- 迅速加算の項目候補は、当日先行算定を固定すれば、実施順を変えても同じ多重集合になる。 -/
theorem AdditionContext.rapidCandidates_perm (c : AdditionContext) {tests : List RapidTest}
    (h : c.rapidTests.Perm tests) (prior : List Nat) :
    (c.rapidCandidates prior).Perm ({ c with rapidTests := tests }.rapidCandidates prior) := by
  unfold rapidCandidates
  have before := (h.filter RapidTest.eligible).map RapidTest.item
  apply (List.perm_ext_iff_of_nodup ((deduplicatedItems_nodup _).filter _)
    ((deduplicatedItems_nodup _).filter _)).mpr
  intro item
  simp only [List.mem_filter, List.mem_eraseDups, before.mem_iff]

structure AdditionResult where
  emergency : Nat
  rapid : Nat
  deriving DecidableEq

def emergencyPrimary : Rule AdditionContext AdditionResult :=
  ⟨"primary/ch2-part3-section1-subsection1/general/1", primary "第1款通則1", fun c r =>
    (c.selection = .emergency → r.emergency = 200 ∧ c.priorRapidItems = some []) ∧
    (c.selection ≠ .emergency → r.emergency = 0) ∧
    (c.emergencyClaimed = some true → r.rapid = 0)⟩

def rapidPrimary : Rule AdditionContext AdditionResult :=
  ⟨"primary/ch2-part3-section1-subsection1/general/3", primary "第1款通則3", fun c r =>
    (c.selection = .rapid → ∃ prior, c.priorRapidItems = some prior ∧
      prior.Nodup ∧ prior.length ≤ 5 ∧ c.emergencyClaimed = some false ∧
      r.rapid = 10 * min (5 - prior.length) (c.rapidCandidates prior).length) ∧
    (c.selection ≠ .rapid → r.rapid = 0)⟩

/-- 各通知条件は同一の検査を指す。証人の共有により、異なる検査の事実を混ぜない。 -/
def emergencyEligibility : Rule (AdditionContext × EmergencyTest) AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/emergency/1", notice "PDF329頁 時間外緊急院内検査加算(1)",
    fun (c, t) _ => c.selection = .emergency →
      t ∈ c.emergencyTests ∧ t.physicianDeterminedUrgent = true ∧
        t.ownStaffAndEquipment = true ∧ t.outOfHoursConsultation = true⟩

def emergencyStart : Rule (AdditionContext × EmergencyTest) AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/emergency/2", notice "PDF330頁 時間外緊急院内検査加算(2)",
    fun (c, t) _ => c.selection = .emergency → t.outOfHoursStart = true⟩

def emergencyOnce : Rule AdditionContext AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/emergency/3", notice "PDF330頁 時間外緊急院内検査加算(3)",
    fun c _ => c.selection = .emergency → c.emergencyClaimed = some false⟩

def emergencyOutpatient : Rule (AdditionContext × EmergencyTest) AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/emergency/4", notice "PDF330頁 時間外緊急院内検査加算(4)",
    fun (c, t) _ => c.selection = .emergency → t.outpatientAtTest = true⟩

def emergencyNightExclusion : Rule AdditionContext AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/emergency/5", notice "PDF330頁 時間外緊急院内検査加算(5)",
    fun c _ => c.selection = .emergency → c.nightEarlyMorningAddition = false⟩

def emergencyUrgency : Rule (AdditionContext × EmergencyTest) AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/emergency/6", notice "PDF330頁 時間外緊急院内検査加算(6)",
    fun (c, t) _ => c.selection = .emergency → t.seriousAndCannotWait = true⟩

def EmergencyConfirmed (c : AdditionContext) : Prop :=
  ∃ t, emergencyEligibility.holds (c, t) ⟨0, 0⟩ ∧
    emergencyStart.holds (c, t) ⟨0, 0⟩ ∧ emergencyOutpatient.holds (c, t) ⟨0, 0⟩ ∧
    emergencyUrgency.holds (c, t) ⟨0, 0⟩

/-- 緊急性・時間帯等の証拠は、同じ検査の実施一覧を並べ替えても保たれる。 -/
theorem emergencyConfirmed_perm (c : AdditionContext) {tests : List EmergencyTest}
    (h : c.emergencyTests.Perm tests) :
    EmergencyConfirmed { c with emergencyTests := tests } ↔ EmergencyConfirmed c := by
  simp only [EmergencyConfirmed, emergencyEligibility, emergencyStart, emergencyOutpatient,
    emergencyUrgency]
  simp only [h.mem_iff]

def rapidPlace : Rule AdditionContext AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/rapid/1", notice "PDF330頁 外来迅速検体検査加算(1)",
    fun c r => c.selection = .rapid →
      r.rapid ≤ 10 * (c.rapidTests.filter RapidTest.eligible).length⟩

def rapidBundle : Rule AdditionContext AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/rapid/2", notice "PDF330頁 外来迅速検体検査加算(2)",
    fun c r => ∀ prior, c.selection = .rapid → c.priorRapidItems = some prior →
      r.rapid = 10 * min (5 - prior.length) (c.rapidCandidates prior).length⟩

def rapidDailyLimit : Rule AdditionContext AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/rapid/3", notice "PDF330頁 外来迅速検体検査加算(3)",
    fun c r => ∀ prior, c.selection = .rapid → c.priorRapidItems = some prior →
      r.rapid + 10 * prior.length ≤ 50⟩

def rapidConsultationBundle : Rule AdditionContext AdditionResult :=
  ⟨"notice/ch2-part3-section1-subsection1/rapid/4", notice "PDF330頁 外来迅速検体検査加算(4)",
    fun c r => ∀ prior, c.selection = .rapid → c.priorRapidItems = some prior →
      r.rapid ≤ 10 * min (5 - prior.length) (c.rapidCandidates prior).length⟩

def rapidOutpatient : Rule (RapidTest × Bool) Unit :=
  ⟨"notice/ch2-part3-section1-subsection1/rapid/5", notice "PDF330頁 外来迅速検体検査加算(5)",
    fun (t, counted) _ => counted = true → t.outpatientAtTest = true⟩

def additionRules : List (Rule AdditionContext AdditionResult) :=
  [emergencyPrimary, rapidPrimary, emergencyOnce, emergencyNightExclusion, rapidBundle,
    rapidDailyLimit, rapidConsultationBundle]

/-- 検査一覧だけの並べ替えでは、加算の点数制約を満たす結果は変わらない。 -/
theorem additionRules_rapid_perm (c : AdditionContext) {tests : List RapidTest}
    (h : c.rapidTests.Perm tests) (result : AdditionResult) :
    Satisfies additionRules { c with rapidTests := tests } result ↔
      Satisfies additionRules c result := by
  have counts (prior : List Nat) := (c.rapidCandidates_perm h prior).length_eq
  simp [additionRules, satisfies_cons, satisfies_nil, emergencyPrimary, rapidPrimary,
    emergencyOnce, emergencyNightExclusion, rapidBundle, rapidDailyLimit, rapidConsultationBundle,
    ← counts]

theorem additions_determine (c : AdditionContext)
    (emergency : c.selection = .emergency → EmergencyConfirmed c ∧
      c.emergencyClaimed = some false ∧ c.priorRapidItems = some [] ∧ c.nightEarlyMorningAddition = false)
    (rapid : c.selection = .rapid → ∃ prior, c.priorRapidItems = some prior ∧
      prior.Nodup ∧ prior.length ≤ 5 ∧ c.emergencyClaimed = some false) :
    DeterminesAt additionRules c := by
  simp only [DeterminesAt, SatisfiableAt, UniqueAt, additionRules]
  simp only [satisfies_cons, satisfies_nil, and_true, emergencyPrimary, rapidPrimary, emergencyOnce,
    emergencyNightExclusion, rapidBundle, rapidDailyLimit, rapidConsultationBundle]
  cases hs : c.selection
  · refine ⟨⟨⟨0, 0⟩, by simp⟩, ?_⟩
    rintro ⟨ae, ar⟩ ⟨be, br⟩ ha hb
    simp_all
  · obtain ⟨_, hc, hr, hn⟩ := emergency hs
    refine ⟨⟨⟨200, 0⟩, by simp [hc, hr, hn]⟩, ?_⟩
    rintro ⟨ae, ar⟩ ⟨be, br⟩ ha hb
    simp_all
  · obtain ⟨prior, hp, hn, hl, he⟩ := rapid hs
    refine ⟨⟨⟨0, 10 * min (5 - prior.length) (c.rapidCandidates prior).length⟩,
      by
        simp [hp, hn, hl, he]
        omega⟩, ?_⟩
    rintro ⟨ae, ar⟩ ⟨be, br⟩ ha hb
    simp_all

/-- 確認済みの日次内訳。第1款と第2款は準用と包括を個別モジュールで解決した後の点数。
採取は実際に患者から採取し、別算定と確認された第4節の点数だけを渡す。 -/
structure Context where
  site : Site
  execution : Nat
  judgment : Nat
  collections : List Nat
  emergencyAddition : Nat
  rapidAddition : Nat

structure Result where
  specimen : Nat
  specimenWithCollection : Nat
  deriving DecidableEq, Repr

def sectionOneRule : Rule Context Result :=
  ⟨"primary/ch2-part3-section1/general/unnumbered", primary "第1節通則",
    fun c r => r.specimen = (c.execution + c.emergencyAddition + c.rapidAddition) + c.judgment⟩

def partThreeRule : Rule Context Result :=
  ⟨"primary/ch2-part3/general/1", primary "第3部通則1",
    fun c r => r.specimenWithCollection = r.specimen + c.collections.sum⟩

def rules : List (Rule Context Result) := [sectionOneRule, partThreeRule]

def assess (c : Context) : Result :=
  let specimen := c.execution + c.emergencyAddition + c.rapidAddition + c.judgment
  ⟨specimen, specimen + c.collections.sum⟩

theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ r = assess c := by
  cases r with
  | mk specimen total =>
    simp only [rules, satisfies_cons, satisfies_nil, and_true, sectionOneRule, partThreeRule,
      assess, Result.mk.injEq]
    exact ⟨fun ⟨h, htotal⟩ => ⟨h, htotal.trans (congrArg (· + c.collections.sum) h)⟩,
      fun ⟨h, htotal⟩ => ⟨h, htotal.trans (congrArg (· + c.collections.sum) h.symm)⟩⟩

theorem determines (c : Context) : DeterminesAt rules c :=
  ⟨⟨assess c, (satisfies_iff ..).2 rfl⟩,
    fun a b ha hb => ((satisfies_iff c a).1 ha).trans ((satisfies_iff c b).1 hb).symm⟩

/-- 既存の個別評価とD023準用評価を実施料とD026の双方へ渡す。
採取の遠隔置換が該当する場合は、解決後の第4節相当額を collections に渡す。 -/
def fromReferences (site : Site) (refs : List D023References.Assessment)
    (valid : ∀ a ∈ refs, a.Valid) (judgment : SpecimenJudgment.Context)
    (specimen : Examinations.SpecimenContext) (collections : List Nat)
    (additionContext : AdditionContext) (additions : AdditionResult)
    (_ : additionContext.site = site) (_ : Satisfies additionRules additionContext additions)
    (_ : additionContext.selection = .emergency → EmergencyConfirmed additionContext) : Option Context := do
  let specimen ← D023References.apply refs valid judgment specimen
  let execution ← Examinations.executionPoints specimen
  return ⟨site, execution, specimen.judgmentPoints, collections, additions.emergency, additions.rapid⟩

private def sampleSite : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

example : assess ⟨sampleSite, 120, 155, [40], 0, 20⟩ = ⟨295, 335⟩ := rfl

private def remoteSample : VisitingNurseCollection :=
  ⟨⟨1, sampleSite, (), none, none, none, none⟩, true, .revisit, true, true,
    true, false, true, true, true⟩

example : visitingNurseObligations remoteSample = ⟨some 2, true⟩ := rfl
example : visitingNurseObligations { remoteSample with visitingNursingToday := false } =
    ⟨none, false⟩ := rfl

end Sanri.MedicalFee.SpecimenOutpatientDay
