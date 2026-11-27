import Sanri.History
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D006Genetic

open Sanri.Logic Sanri.History

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF177頁 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

inductive Item where
  | simple | complex | veryComplex
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.simple, .complex, .veryComplex]

def Item.number : Item → Nat
  | .simple => 1
  | .complex => 2
  | .veryComplex => 3

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem modeled_number (i : Item) : 1 ≤ i.number ∧ i.number ≤ 3 := by
  cases i <;> decide

def Item.points : Item → Nat
  | .simple => 3880
  | .complex => 5000
  | .veryComplex => 8000

inductive Branch where
  | a | i | u | e | o
  deriving DecidableEq

/-- 通知(1)の枝と丸数字。疾患の所属は原文と照合済みの入力として受ける。 -/
structure DiseaseGroup where
  branch : Branch
  grade : Item

inductive Method where
  | pcr | sequencing | fish | southernBlot | other
  deriving DecidableEq

structure Examination where
  performance : Performance Nat
  suspected : Option Bool := none
  group : Option DiseaseGroup := none
  method : Option Method := none
  undiagnosableByOtherMeans : Option Bool := none
  /-- 通知(1)の「２回以上」の起算と対象を確認した実施履歴の照会期間。 -/
  repeatPeriod : Option Period := none
  repeatNecessary : Option Bool := none

inductive Application where
  | single
  | multiple (others : List Examination)

structure Context where
  principal : Examination
  item : Item
  application : Application
  diseaseFacilityComplies : Option Bool := none
  diseaseFacilityNotified : Option Bool := none
  bundleFacilityComplies : Option Bool := none
  bundleFacilityNotified : Option Bool := none
  privacyGuidance : Option Bool := none
  geneticGuideline : Option Bool := none
  bundleGuideline : Option Bool := none
  bundleNecessary : Option Bool := none
  principalConfirmed : Option Bool := none
  priorPerformances : Option (Snapshot (Performance Nat)) := none

def Context.exams (c : Context) : List Examination :=
  c.principal :: (match c.application with
    | .single => []
    | .multiple others => others)

def priorCount (c : Context) (e : Examination) : Option Nat := do
  let h ← c.priorPerformances
  let period ← e.repeatPeriod
  let site := e.performance.site
  return (← h.select Performance.site ⟨site.patient, none, period⟩
    (fun p => p.item == e.performance.item)).length

def DiseaseFacility (c : Context) : Prop :=
  c.diseaseFacilityComplies = some true ∧ c.diseaseFacilityNotified = some true

def BranchCondition (c : Context) (branch : Branch) (e : Examination) : Prop :=
  match branch with
  | .a => ∃ m ∈ [Method.pcr, .sequencing, .fish, .southernBlot], e.method = some m
  | .i => e.method = some .pcr
  | .u => True
  | .e => DiseaseFacility c
  | .o => DiseaseFacility c ∧ e.undiagnosableByOtherMeans = some true

def RepeatCondition (c : Context) : Prop :=
  ∀ e ∈ c.exams, ∃ n, priorCount c e = some n ∧
    (n = 0 ∨ e.repeatNecessary = some true)

def Listed (c : Context) : Prop :=
  ∀ e ∈ c.exams, e.suspected = some true ∧
    ∃ g, e.group = some g ∧ (g.branch = .i → g.grade ≠ .veryComplex)

def DesignatedDiseaseFacility (c : Context) : Prop :=
  ∀ e ∈ c.exams, ∀ g, e.group = some g →
    g.branch = .e ∨ g.branch = .o → DiseaseFacility c

def BranchApplies (c : Context) (b : Branch) : Prop :=
  ∀ e ∈ c.exams, ∀ g, e.group = some g → g.branch = b → BranchCondition c b e

def Grade (c : Context) (i : Item) : Prop :=
  c.item = i → ∃ g, c.principal.group = some g ∧ g.grade = i

def BundleFacilityAndDraw (c : Context) : Prop :=
  match c.application with
  | .single => True
  | .multiple others =>
    c.bundleFacilityComplies = some true ∧ c.bundleFacilityNotified = some true ∧
    c.principalConfirmed = some true ∧ others ≠ [] ∧
    (c.exams.map (·.performance.item)).Nodup ∧
    ∀ e ∈ others, c.principal.performance.sameDraw e.performance = some true

def BundleIndication (c : Context) : Prop :=
  match c.application with
  | .single => True
  | .multiple _ => c.bundleGuideline = some true ∧ c.bundleNecessary = some true

inductive Entry where
  | repeatNecessity (disease : Nat)
  | cannotDiagnoseAndNecessity (disease : Nat)
  | bundledNamesAndNecessity (diseases : List Nat)

structure Result where
  base : Nat
  addition : Nat

def Result.total (r : Result) : Nat := r.base + r.addition

def simpleRule : Rule Context Result :=
  ⟨"primary/D006-4/item/1", primary "D006-4 1", fun c r =>
    c.item = .simple → r.base = 3880⟩

def complexRule : Rule Context Result :=
  ⟨"primary/D006-4/item/2", primary "D006-4 2", fun c r =>
    c.item = .complex → r.base = 5000⟩

def veryComplexRule : Rule Context Result :=
  ⟨"primary/D006-4/item/3", primary "D006-4 3", fun c r =>
    c.item = .veryComplex → r.base = 8000⟩

def facilityRule : Rule Context Result :=
  ⟨"primary/D006-4/note/1", primary "D006-4 注1", fun c _ =>
    DesignatedDiseaseFacility c⟩

def bundleRule : Rule Context Result :=
  ⟨"primary/D006-4/note/2", primary "D006-4 注2", fun c r =>
    BundleFacilityAndDraw c ∧ match c.application with
      | .single => r.addition = 0
      | .multiple _ => 2 * r.addition = r.base⟩

def frequencyRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1", notice "PDF341頁 D006-4(1)", fun c _ =>
    Listed c ∧ RepeatCondition c⟩

def aRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/a", notice "PDF341頁 D006-4(1)ア",
    fun c _ => BranchApplies c .a⟩

def iRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/i", notice "PDF341頁 D006-4(1)イ",
    fun c _ => BranchApplies c .i⟩

def uRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/u", notice "PDF341頁 D006-4(1)ウ",
    fun c _ => BranchApplies c .u⟩

def eRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/e", notice "PDF341–342頁 D006-4(1)エ",
    fun c _ => BranchApplies c .e⟩

def oRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/o", notice "PDF342–343頁 D006-4(1)オ",
    fun c _ => BranchApplies c .o⟩

def guidanceRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/2", notice "PDF343頁 D006-4(2)", fun c _ =>
    c.privacyGuidance = some true ∧ c.geneticGuideline = some true⟩

def diseaseFacilityRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/3", notice "PDF343頁 D006-4(3)", fun c _ =>
    DesignatedDiseaseFacility c⟩

def simpleGradeRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/5", notice "PDF343頁 D006-4(5)", fun c _ => Grade c .simple⟩

def complexGradeRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/6", notice "PDF343頁 D006-4(6)", fun c _ => Grade c .complex⟩

def veryComplexGradeRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/7", notice "PDF343頁 D006-4(7)", fun c _ => Grade c .veryComplex⟩

def bundleIndicationRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/8", notice "PDF343–344頁 D006-4(8)",
    fun c _ => BundleIndication c⟩

/-- 摘要欄に要求する内容。実際に記載したかどうかは点数の前提と別に扱う。 -/
def repeatEntryRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-4/paragraph/1", notice "PDF341頁 D006-4(1) 摘要", fun c entries =>
    ∀ e ∈ c.exams, ∀ n, priorCount c e = some n → 0 < n →
      entries (.repeatNecessity e.performance.item)⟩

def diagnosticEntryRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-4/paragraph/4", notice "PDF343頁 D006-4(4)", fun c entries =>
    ∀ e ∈ c.exams, ∀ g, e.group = some g → g.branch = .o →
      entries (.cannotDiagnoseAndNecessity e.performance.item)⟩

def bundleEntryRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-4/paragraph/8", notice "PDF343–344頁 D006-4(8) 摘要", fun c entries =>
    ∀ others, (∃ n, c.application = .multiple n ∧
      others = c.exams.map (·.performance.item)) → entries (.bundledNamesAndNecessity others)⟩

def rules := [simpleRule, complexRule, veryComplexRule, facilityRule, bundleRule,
  frequencyRule, aRule, iRule, uRule, eRule, oRule, guidanceRule, diseaseFacilityRule,
  simpleGradeRule, complexGradeRule, veryComplexGradeRule, bundleIndicationRule]

def Eligible (c : Context) : Prop :=
  DesignatedDiseaseFacility c ∧ BundleFacilityAndDraw c ∧ Listed c ∧ RepeatCondition c ∧
  BranchApplies c .a ∧ BranchApplies c .i ∧ BranchApplies c .u ∧
  BranchApplies c .e ∧ BranchApplies c .o ∧
  c.privacyGuidance = some true ∧ c.geneticGuideline = some true ∧
  Grade c .simple ∧ Grade c .complex ∧ Grade c .veryComplex ∧ BundleIndication c

def scheduled (c : Context) : Result :=
  ⟨c.item.points, match c.application with
    | .single => 0
    | .multiple _ => c.item.points / 2⟩

theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ Eligible c ∧ r = scheduled c := by
  obtain ⟨base, addition⟩ := r
  simp only [rules, satisfies_cons, satisfies_nil, simpleRule, complexRule, veryComplexRule,
    facilityRule, bundleRule, frequencyRule, aRule, iRule, uRule, eRule, oRule, guidanceRule,
    diseaseFacilityRule, simpleGradeRule, complexGradeRule, veryComplexGradeRule,
    bundleIndicationRule, Eligible, scheduled, Result.mk.injEq, and_true]
  cases c.item <;> cases c.application <;>
    simp [Item.points, *] <;>
    (constructor <;> intro h <;> simp_all only [and_assoc] <;> grind)

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  exact ⟨⟨scheduled c, (satisfies_iff _ _).mpr ⟨h, rfl⟩⟩,
    fun a b ha hb => ((satisfies_iff _ _).mp ha).2.trans ((satisfies_iff _ _).mp hb).2.symm⟩

def PermitsPoints (c : Context) (p : Nat) : Prop :=
  ∃ r, Satisfies rules c r ∧ r.total = p

theorem permits_points_iff (c : Context) (p : Nat) :
    PermitsPoints c p ↔ Eligible c ∧ (scheduled c).total = p := by
  constructor
  · rintro ⟨r, hr, hp⟩
    obtain ⟨eligible, rfl⟩ := (satisfies_iff _ _).mp hr
    exact ⟨eligible, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨scheduled c, (satisfies_iff _ _).mpr ⟨h, rfl⟩, hp⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 4, number := i.number, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

private def exampleSite : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def exampleExam : Examination :=
  { performance := ⟨1, exampleSite, 1, some 1, some 1, none, none⟩
    suspected := some true, group := some ⟨.a, .simple⟩, method := some .pcr
    repeatPeriod := some (Period.through exampleSite.date) }

private def exampleContext : Context :=
  { principal := exampleExam, item := .simple, application := .single
    privacyGuidance := some true, geneticGuideline := some true
    priorPerformances := some ⟨⟨1, none, Period.through exampleSite.date⟩, []⟩ }

private theorem example_eligible : Eligible exampleContext := by
  simp [Eligible, exampleContext, exampleExam, DesignatedDiseaseFacility, Context.exams,
    BundleFacilityAndDraw, Listed, RepeatCondition, BranchApplies, Grade, BundleIndication,
    priorCount, Snapshot.select, Scope.Covers, Period.Within, BranchCondition]
  all_goals first | rfl | exact ⟨.pcr, by simp, rfl⟩

example : Satisfies rules exampleContext ⟨3880, 0⟩ :=
  (satisfies_iff _ _).mpr ⟨example_eligible, rfl⟩

private def otherExam : Examination :=
  { exampleExam with
    performance := { exampleExam.performance with id := 2, item := 2 }
    group := some ⟨.i, .complex⟩ }

private def exampleBundle : Context :=
  { exampleContext with
    application := .multiple [otherExam], principalConfirmed := some true
    bundleFacilityComplies := some true, bundleFacilityNotified := some true
    bundleGuideline := some true, bundleNecessary := some true }

private theorem example_bundle_eligible : Eligible exampleBundle := by
  simp [Eligible, exampleBundle, exampleContext, exampleExam, otherExam,
    DesignatedDiseaseFacility, Context.exams, BundleFacilityAndDraw, Listed,
    RepeatCondition, BranchApplies, Grade, BundleIndication, priorCount, Snapshot.select,
    Scope.Covers, Period.Within, BranchCondition, Performance.sameDraw, Performance.sameGroup]
  all_goals first | rfl | exact ⟨.pcr, by simp, rfl⟩

example : PermitsPoints exampleBundle 5820 :=
  (permits_points_iff _ _).mpr ⟨example_bundle_eligible, rfl⟩

example : ¬ SatisfiableAt rules { exampleContext with priorPerformances := none } := by
  rintro ⟨r, hr⟩
  have h := (satisfies_iff _ _).mp hr |>.1.2.2.2.1
  have ⟨n, h, _⟩ := h exampleExam (by simp [Context.exams, exampleContext])
  contradiction

example : ¬ SatisfiableAt rules { exampleContext with geneticGuideline := some false } := by
  rintro ⟨r, hr⟩
  have h := (satisfies_iff _ _).mp hr
  simp [Eligible, exampleContext] at h

end Sanri.MedicalFee.D006Genetic
