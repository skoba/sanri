import Sanri.Logic
import Sanri.SpecimenJudgment
import Sanri.SpecimenCollection
import Sanri.UrineFecalTests
import Sanri.Cardiorespiratory

namespace Sanri.CaseStudies.OutpatientBloodTests

open Sanri.Logic
open Sanri.MedicalFee

/-! 一患者・一保険医療機関・一外来日の血液検査本体と静脈採血を扱う。
成人の通常外来で、他の包括・加算・委託が関わらない場合を対象とする。
血算は一検体、D007は下記の八種類に限り、同一採血での同一検査の反復は対象外。
採血識別子は採取行為を表し、採血管・検体容器を表さない。 -/

inductive BloodCountItem where
  | redCells | whiteCells | hemoglobin | hematocrit | platelets
  deriving DecidableEq, Repr

inductive ChemistryItem where
  | bun | creatinine | ast | alt | totalProtein | albumin | gammaGT | uricAcid
  deriving DecidableEq, Repr

structure Measurement where
  draw : Nat
  item : ChemistryItem
  deriving DecidableEq, Repr

structure Context where
  bloodCount : List BloodCountItem
  chemistry : List Measurement
  albuminByModifiedBCP : Option Bool
  creatinineByJaffe : Option Bool
  /-- D026(2)の当月初回実施日を過ぎた区分。none は履歴不明。 -/
  earlierTestCategoriesThisMonth : Option (List SpecimenJudgment.Category)
  /-- 同じ患者・機関で当日すでにD400を算定したか。none は履歴不明。 -/
  d400AlreadyChargedToday : Option Bool
  /-- 回路採血や手術時採血等の除外は、採血の事実から既存モデルで評価する。 -/
  collection : SpecimenCollection.Context

def ChemistryItem.number : ChemistryItem → Nat
  | .ast | .alt => 3
  | _ => 1

def ChemistryItem.points (item : ChemistryItem) : Nat :=
  if item.number = 3 then 17 else 11

def eligible (c : Context) : ChemistryItem → Option Bool
  | .albumin => c.albuminByModifiedBCP
  | .creatinine => c.creatinineByJaffe.map (! ·)
  | _ => some true

def chemistryItems (c : Context) : Option (List Measurement) := do
  if c.chemistry.eraseDups != c.chemistry then none else
    c.chemistry.filterM (fun m => eligible c m.item)

/-- D007注イ・ロのうち、対象の八種類で到達する範囲。 -/
def chemistryDrawPoints (items : List ChemistryItem) : Nat :=
  if 8 ≤ items.length then 99
  else if 5 ≤ items.length then 93
  else (items.map ChemistryItem.points).sum

def chemistryPoints (items : List Measurement) : Nat :=
  let draws := (items.map Measurement.draw).eraseDups
  (draws.map fun draw =>
    chemistryDrawPoints ((items.filter (fun m => m.draw == draw)).map Measurement.item)).sum

def bloodCountPoints (items : List BloodCountItem) : Nat :=
  if items.isEmpty then 0 else 21

def judgmentPoints (count : List BloodCountItem) (chemistry : List Measurement)
    (earlier : List SpecimenJudgment.Category) : Option Nat :=
  let countTests : List SpecimenJudgment.Test :=
    if count.isEmpty then [] else [{ major := 5, number := 5, ordinaryCategory := .hematological }]
  let chemistryTests : List SpecimenJudgment.Test :=
    chemistry.map fun m => { major := 7, number := m.item.number, ordinaryCategory := .biochemicalI }
  -- 初回検査日の条件を満たさない区分を既存の月内除外に渡す。
  SpecimenJudgment.points { tests := countTests ++ chemistryTests, categoriesClaimedThisMonth := earlier }

def collectionPoints (collection : SpecimenCollection.Context) (alreadyCharged : Bool) :
    Option Nat :=
  if collection.item != .venousBlood || collection.inpatient || collection.ageYears < 6 then none
  else SpecimenCollection.points
    { collection with dailyAlreadyClaimed := alreadyCharged || collection.dailyAlreadyClaimed }

structure Breakdown where
  count : Nat
  chemistry : Nat
  judgment : Nat
  collection : Nat
  deriving DecidableEq, Repr

def Breakdown.total (b : Breakdown) : Nat := b.count + b.chemistry + b.judgment + b.collection

def assess (c : Context) : Option Breakdown := do
  let items ← chemistryItems c
  let earlier ← c.earlierTestCategoriesThisMonth
  let charged ← c.d400AlreadyChargedToday
  let judgment ← judgmentPoints c.bloodCount items earlier
  let collection ← collectionPoints c.collection charged
  return ⟨bloodCountPoints c.bloodCount, chemistryPoints items, judgment, collection⟩

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "2026-10-22取得版",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def rules : List (Rule Context Breakdown) :=
  [⟨"D005.5", primary "PDF176頁 D005の5",
      fun c r => r.count = bloodCountPoints c.bloodCount⟩,
   ⟨"D005.4-notice", notice "PDF338頁 D005(4)",
      fun c r => (r.count > 0 ↔ c.bloodCount ≠ [])⟩,
   ⟨"D007.1.3-and-note", primary "PDF179・181頁 D007の1・3及び注イ・ロ",
      fun c r => ∃ items, chemistryItems c = some items ∧ r.chemistry = chemistryPoints items⟩,
   ⟨"D007.4-notice", notice "PDF356頁 D007(4)",
      fun c _ => ∀ items, chemistryItems c = some items →
        c.creatinineByJaffe = some true → ∀ m ∈ items, m.item ≠ .creatinine⟩,
   ⟨"D026.3.4-and-note1", primary "PDF192頁 D026の3・4及び注1",
      fun c r => ∃ items earlier, chemistryItems c = some items ∧
        c.earlierTestCategoriesThisMonth = some earlier ∧
        judgmentPoints c.bloodCount items earlier = some r.judgment⟩,
   ⟨"D026.2.3-notice", notice "PDF402頁 D026(2)・(3)",
      fun c r => ∀ earlier, c.earlierTestCategoriesThisMonth = some earlier →
        (.hematological ∈ earlier → .biochemicalI ∈ earlier → r.judgment = 0)⟩,
   ⟨"D400-and-collection-general", primary "PDF210頁 第4節通則・D400",
      fun c r => ∃ charged, c.d400AlreadyChargedToday = some charged ∧
        collectionPoints c.collection charged = some r.collection⟩]

/-- 規則が結果を許容する場合、その内訳は計算結果と一致する。 -/
theorem satisfies_implies_assessed {c : Context} {r : Breakdown} (h : Satisfies rules c r) :
    assess c = some r := by
  simp only [rules, satisfies_cons, satisfies_nil] at h
  change r.count = bloodCountPoints c.bloodCount ∧ _ at h
  obtain ⟨hc, _, ⟨otherItems, ho, hChem⟩, _, ⟨items, earlier, hi, he, hj⟩, _,
    ⟨charged, hd, hs⟩, _⟩ := h
  cases r with
  | mk count chemistry judgment collection =>
    rw [hi] at ho
    cases Option.some.inj ho
    change judgmentPoints c.bloodCount otherItems earlier = some judgment at hj
    change collectionPoints c.collection charged = some collection at hs
    change count = bloodCountPoints c.bloodCount at hc
    change chemistry = chemistryPoints otherItems at hChem
    subst count
    subst chemistry
    simp [assess, hi, he, hd, hj, hs]

def exampleContext : Context where
  bloodCount := [.redCells, .whiteCells, .hemoglobin, .hematocrit, .platelets]
  chemistry := [.bun, .creatinine, .ast, .alt, .totalProtein, .albumin, .gammaGT, .uricAcid].map
    (fun item => ⟨1, item⟩)
  albuminByModifiedBCP := some true
  creatinineByJaffe := some false
  earlierTestCategoriesThisMonth := some []
  d400AlreadyChargedToday := some false
  collection := { item := .venousBlood, ageYears := 40 }

theorem example_satisfies : Satisfies rules exampleContext ⟨21, 99, 269, 40⟩ := by
  simp only [rules, satisfies_cons, satisfies_nil]
  refine ⟨rfl, ?_, ⟨exampleContext.chemistry, rfl, rfl⟩, ?_,
    ⟨exampleContext.chemistry, [], rfl, rfl, rfl⟩, ?_, ⟨false, rfl, rfl⟩, trivial⟩
  · decide
  · intro _ _ hj
    cases hj
  · intro earlier he
    cases Option.some.inj he
    simp

theorem example_determines : DeterminesAt rules exampleContext := by
  refine ⟨⟨_, example_satisfies⟩, ?_⟩
  intro first second hf hs
  exact Option.some.inj ((satisfies_implies_assessed hf).symm.trans (satisfies_implies_assessed hs))

theorem example_total : (assess exampleContext).map Breakdown.total = some 429 := by decide

example : (assess { exampleContext with d400AlreadyChargedToday := some true }).map
    Breakdown.total = some 389 := by decide

private def afterEarlierBloodCount : Context :=
  { exampleContext with earlierTestCategoriesThisMonth := some [.hematological] }

example : (assess afterEarlierBloodCount).map Breakdown.total = some 304 := by decide

-- 翌月の初回実施日として、当月の履歴を明示的に与え直す。
example : (assess { afterEarlierBloodCount with earlierTestCategoriesThisMonth := some [] }).map
    Breakdown.total = some 429 := by decide

example : (assess { exampleContext with
    collection := { exampleContext.collection with bloodCircuitSampling := true } }).map
    Breakdown.collection = some 0 := by decide

example : assess { exampleContext with earlierTestCategoriesThisMonth := none } = none := by decide
example : assess { exampleContext with d400AlreadyChargedToday := none } = none := by decide
example : assess { exampleContext with albuminByModifiedBCP := none } = none := by decide
example : (assess { exampleContext with creatinineByJaffe := some true }).map
    Breakdown.chemistry = some 93 := by decide

-- 四項目ずつ別々に採取した場合は、同日でも八項目包括にならない。
private def twoDraws : List Measurement :=
  exampleContext.chemistry.take 4 ++
    ((exampleContext.chemistry.drop 4).map fun m => { m with draw := 2 })

example : (assess { exampleContext with chemistry := twoDraws }).map
    Breakdown.chemistry = some 100 := by decide

/-- 同じ症例に初診・院内D000・12誘導心電図・院外処方を加えた例。
施設・処方の加算を別に適用しない条件を固定し、正確な点数を1/100点単位で合算する。 -/
def exampleVisitHundredths : Option Nat := do
  let blood ← assess exampleContext
  let initial ← InitialConsultation.points { institution := .clinic, ageYears := 40 }
  let urineResult ← UrineFecalTests.assess { item := .generalUrine, performedInsideInstitution := true }
  let .charged urine := urineResult | none
  let ecg ← Cardiorespiratory.assess { item := .ecg12Lead, completedYears := 40 }
  let prescription ← PrescriptionFee.points {
    facility := .clinic
    issuedForInsurancePharmacy := true
    medication := { oralDrugs := 1 }
    additions := { prescribedDaysIncludingRefills := 28 } }
  return 100 * (blood.total + initial + urine.total) + ecg.totalHundredths + 20 * prescription.fifths

theorem example_visit_total : exampleVisitHundredths = some 93600 := by decide

end Sanri.CaseStudies.OutpatientBloodTests
