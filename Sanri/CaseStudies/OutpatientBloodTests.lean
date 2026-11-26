import Sanri.Logic
import Sanri.BloodMorphology
import Sanri.BloodChemistry
import Sanri.SpecimenCollection
import Sanri.UrineFecalTests
import Sanri.Cardiorespiratory

namespace Sanri.CaseStudies.OutpatientBloodTests

open Sanri.Logic
open Sanri.MedicalFee
open BloodMorphology (BloodCountItem bloodCountPoints)

/-! 一患者・一保険医療機関・一外来日の血液検査本体と静脈採血を扱う。
成人の通常外来で、他の包括・加算・委託が関わらない場合を対象とする。
血算は一検体、D007は下記の八種類に限り、同一採血での同一検査の反復は対象外。
採血識別子は採取行為を表し、採血管・検体容器を表さない。 -/

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

def ChemistryItem.toBloodChemistry : ChemistryItem → BloodChemistry.Item
  | .bun => .bun
  | .creatinine => .creatinine
  | .ast => .ast
  | .alt => .alt
  | .totalProtein => .totalProtein
  | .albumin => .albumin
  | .gammaGT => .gammaGT
  | .uricAcid => .uricAcid

def ChemistryItem.number (i : ChemistryItem) : Nat := i.toBloodChemistry.number

def eligible (c : Context) (i : ChemistryItem) : Option Bool :=
  BloodChemistry.Draw.eligible
    { performed := [], albuminByModifiedBCP := c.albuminByModifiedBCP,
      creatinineByJaffe := c.creatinineByJaffe } i.toBloodChemistry

def chemistryItems (c : Context) : Option (List Measurement) := do
  if c.chemistry.eraseDups != c.chemistry then none else
    c.chemistry.filterM (fun m => eligible c m.item)

def chemistryPoints (items : List Measurement) : Nat :=
  let draws := (items.map Measurement.draw).eraseDups
  (draws.map fun draw =>
    BloodChemistry.pointsForItems
      ((items.filter (fun m => m.draw == draw)).map (·.item.toBloodChemistry))).sum

def judgmentPoints (count : List BloodCountItem) (chemistry : List Measurement)
    (earlier : List SpecimenJudgment.Category) : Option Nat :=
  let countTests : List SpecimenJudgment.Test :=
    if count.isEmpty then [] else [BloodMorphology.Item.completeBloodCount.judgmentTest false]
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

private def chemistryDraw (c : Context) : BloodChemistry.Draw :=
  { performed := [], albuminByModifiedBCP := c.albuminByModifiedBCP,
    creatinineByJaffe := c.creatinineByJaffe }

private def Rejected (c : Context) (item : ChemistryItem) : Prop :=
  (item = .albumin ∧ c.albuminByModifiedBCP = some false) ∨
  (item = .creatinine ∧ c.creatinineByJaffe = some true)

private theorem rejected_iff (c : Context) (item : ChemistryItem) :
    Rejected c item ↔ eligible c item = some false := by
  cases item <;> simp [Rejected, eligible, ChemistryItem.toBloodChemistry,
    BloodChemistry.Draw.eligible]

private inductive Classified (c : Context) : List Measurement → List Measurement → Prop where
  | nil : Classified c [] []
  | keep {m rest items} :
      Satisfies BloodChemistry.eligibilityRules (chemistryDraw c) m.item.toBloodChemistry →
      Classified c rest items → Classified c (m :: rest) (m :: items)
  | drop {m rest items} :
      Rejected c m.item → Classified c rest items → Classified c (m :: rest) items

private theorem classified_iff (c : Context) (performed items : List Measurement) :
    Classified c performed items ↔ performed.filterM (fun m => eligible c m.item) = some items := by
  induction performed generalizing items with
  | nil =>
    constructor
    · intro h
      cases h
      rfl
    · intro h
      simpa using (show Classified c ([] : List Measurement) [] from .nil)
        |> fun proof => (Option.some.inj h) ▸ proof
  | cons m rest ih =>
    constructor
    · intro h
      cases h with
      | keep hm hs =>
        have he : eligible c m.item = some true := (BloodChemistry.eligible_iff _ _).mp hm
        simp [option_filterM_cons, he, (ih _).mp hs]
      | drop hm hs =>
        simp [option_filterM_cons, (rejected_iff _ _).mp hm, (ih _).mp hs]
    · intro h
      cases he : eligible c m.item with
      | none => simp [option_filterM_cons, he] at h
      | some b =>
        cases hs : rest.filterM (fun m => eligible c m.item) <;>
          cases b <;> simp [option_filterM_cons, he, hs] at h
        · subst items
          exact .drop ((rejected_iff _ _).mpr he) ((ih _).mpr hs)
        · subst items
          exact .keep ((BloodChemistry.eligible_iff _ _).mpr he) ((ih _).mpr hs)

private def ChemistrySelection (c : Context) (items : List Measurement) : Prop :=
  c.chemistry.eraseDups = c.chemistry ∧ Classified c c.chemistry items

private theorem chemistrySelection_iff (c : Context) (items : List Measurement) :
    ChemistrySelection c items ↔ chemistryItems c = some items := by
  by_cases h : c.chemistry.eraseDups = c.chemistry <;>
    simp [ChemistrySelection, chemistryItems, h, classified_iff]

private def DrawPoints (items : List Measurement) : List Nat → Nat → Prop
  | [], p => p = 0
  | draw :: rest, p =>
    ∃ points remaining,
      BloodChemistry.pointsRule.holds
        ((items.filter (fun m => m.draw == draw)).map (·.item.toBloodChemistry)) points ∧
      DrawPoints items rest remaining ∧ p = points + remaining

private def ChemistryPoints (items : List Measurement) (p : Nat) : Prop :=
  DrawPoints items (items.map Measurement.draw).eraseDups p

private theorem chemistryPoints_iff (items : List Measurement) (p : Nat) :
    ChemistryPoints items p ↔ p = chemistryPoints items := by
  unfold ChemistryPoints chemistryPoints
  generalize (items.map Measurement.draw).eraseDups = draws
  induction draws generalizing p with
  | nil => rfl
  | cons draw rest ih =>
    simp [DrawPoints, BloodChemistry.pointsRule_iff, ih]

private def CountPoints (items : List BloodCountItem) (p : Nat) : Prop :=
  (items = [] → p = 0) ∧ (items ≠ [] → p = BloodMorphology.Item.completeBloodCount.basePoints)

private theorem countPoints_iff (items : List BloodCountItem) (p : Nat) :
    CountPoints items p ↔ p = bloodCountPoints items := by
  cases items <;> simp [CountPoints, bloodCountPoints]

private def JudgmentPoints (count : List BloodCountItem) (items : List Measurement)
    (earlier : List SpecimenJudgment.Category) (p : Nat) : Prop :=
  ∃ hematological biochemical : Nat,
    ((count ≠ [] ∧ .hematological ∉ earlier) →
      hematological = SpecimenJudgment.scheduledPoints .hematological) ∧
    (¬ (count ≠ [] ∧ .hematological ∉ earlier) → hematological = 0) ∧
    ((items ≠ [] ∧ .biochemicalI ∉ earlier) →
      biochemical = SpecimenJudgment.scheduledPoints .biochemicalI) ∧
    (¬ (items ≠ [] ∧ .biochemicalI ∉ earlier) → biochemical = 0) ∧
    p = hematological + biochemical

private theorem judgmentPoints_iff (count : List BloodCountItem) (items : List Measurement)
    (earlier : List SpecimenJudgment.Category) (p : Nat) :
    JudgmentPoints count items earlier p ↔ judgmentPoints count items earlier = some p := by
  by_cases hh : SpecimenJudgment.Category.hematological ∈ earlier <;>
    by_cases hb : SpecimenJudgment.Category.biochemicalI ∈ earlier <;>
    cases count <;> cases items <;>
    simp [JudgmentPoints, judgmentPoints, SpecimenJudgment.points, SpecimenJudgment.assess,
      SpecimenJudgment.Assessment.total, SpecimenJudgment.allCategories,
      SpecimenJudgment.categoryFor, SpecimenJudgment.geneRouting,
      BloodMorphology.Item.judgmentTest, BloodMorphology.Item.number,
      SpecimenJudgment.boneMarrowEligible, SpecimenJudgment.immunoelectrophoresisEligible,
      hh, hb, eq_comm (a := p)]

private def CollectionScope (c : SpecimenCollection.Context) : Prop :=
  c.item = .venousBlood ∧ c.inpatient = false ∧ 6 ≤ c.ageYears ∧
  c.insuranceMedicalInstitution = true ∧ c.performed = true

private def SeparateCollection (c : SpecimenCollection.Context) (charged : Bool) : Prop :=
  c.duringSurgery = false ∧ c.commonProcedureClaimedSameDay = false ∧
  c.bloodCircuitSampling = false ∧ c.dailyAlreadyClaimed = false ∧ charged = false

private def CollectionPoints (c : SpecimenCollection.Context) (charged : Bool) (p : Nat) : Prop :=
  CollectionScope c ∧
    (SeparateCollection c charged → p = SpecimenCollection.basePoints .venousBlood) ∧
    (¬ SeparateCollection c charged → p = 0)

private theorem collectionPoints_iff (c : SpecimenCollection.Context) (charged : Bool) (p : Nat) :
    CollectionPoints c charged p ↔ collectionPoints c charged = some p := by
  by_cases hi : c.item = .venousBlood <;> by_cases ha : 6 ≤ c.ageYears <;>
    cases hn : c.inpatient <;> cases hm : c.insuranceMedicalInstitution <;>
    cases hp : c.performed <;>
    simp [CollectionPoints, CollectionScope, collectionPoints, hi, ← Nat.not_le, ha, hn, hm, hp,
      SpecimenCollection.points, SpecimenCollection.assess]
  cases hs : c.duringSurgery <;> cases hc : c.commonProcedureClaimedSameDay <;>
    cases hb : c.bloodCircuitSampling <;> cases hd : c.dailyAlreadyClaimed <;> cases charged <;>
    simp [SeparateCollection, hs, hc, hb, hd, SpecimenCollection.notSeparateReason,
      SpecimenCollection.eligible, SpecimenCollection.Assessment.total, SpecimenCollection.isD400,
      SpecimenCollection.isDaily, SpecimenCollection.isSeries, SpecimenCollection.isUnilateral,
      SpecimenCollection.infantPoints, ha, eq_comm]

def rules : List (Rule Context Breakdown) :=
  [⟨"D005.5", primary "PDF176頁 D005の5",
      fun c r => CountPoints c.bloodCount r.count⟩,
   ⟨"D005.4-notice", notice "PDF338頁 D005(4)",
      fun c r => (r.count > 0 ↔ c.bloodCount ≠ [])⟩,
   ⟨"D007.1.3-and-note", primary "PDF179・181頁 D007の1・3及び注イ・ロ",
      fun c r => ∃ items, ChemistrySelection c items ∧ ChemistryPoints items r.chemistry⟩,
   ⟨"D007.4-notice", notice "PDF356頁 D007(4)",
      fun c _ => ∀ items, ChemistrySelection c items →
        c.creatinineByJaffe = some true → ∀ m ∈ items, m.item ≠ .creatinine⟩,
   ⟨"D026.3.4-and-note1", primary "PDF192頁 D026の3・4及び注1",
      fun c r => ∃ items earlier, ChemistrySelection c items ∧
        c.earlierTestCategoriesThisMonth = some earlier ∧
        JudgmentPoints c.bloodCount items earlier r.judgment⟩,
   ⟨"D026.2.3-notice", notice "PDF402頁 D026(2)・(3)",
      fun c r => ∀ earlier, c.earlierTestCategoriesThisMonth = some earlier →
        (.hematological ∈ earlier → .biochemicalI ∈ earlier → r.judgment = 0)⟩,
   ⟨"D400-and-collection-general", primary "PDF210頁 第4節通則・D400",
      fun c r => ∃ charged, c.d400AlreadyChargedToday = some charged ∧
        CollectionPoints c.collection charged r.collection⟩]

private theorem classified_excludes_jaffe (c : Context) (performed items : List Measurement)
    (h : Classified c performed items) (hj : c.creatinineByJaffe = some true) :
    ∀ m ∈ items, m.item ≠ .creatinine := by
  induction h with
  | nil => simp
  | drop _ _ ih => exact ih
  | @keep m rest items he _ ih =>
    intro other member
    rcases List.mem_cons.mp member with same | tail
    · subst other
      intro item
      have hc := he BloodChemistry.creatinineRule (by simp [BloodChemistry.eligibilityRules])
      have forbidden := hc (by simp [item, ChemistryItem.toBloodChemistry])
      change c.creatinineByJaffe = some false at forbidden
      simp [hj] at forbidden
    · exact ih other tail

theorem assessed_iff (c : Context) (r : Breakdown) :
    Satisfies rules c r ↔ assess c = some r := by
  simp only [rules, satisfies_cons, satisfies_nil, and_true]
  constructor
  · rintro ⟨hc, _, ⟨otherItems, ho, hChem⟩, _, ⟨items, earlier, hi, he, hj⟩, _,
      charged, hd, hs⟩
    have h₁ := (chemistrySelection_iff c items).mp hi
    have h₂ := (chemistrySelection_iff c otherItems).mp ho
    have same := Option.some.inj (h₂.symm.trans h₁)
    subst otherItems
    cases r with
    | mk count chemistry judgment collection =>
      change CountPoints c.bloodCount count at hc
      change ChemistryPoints items chemistry at hChem
      simp [assess, h₁, he, hd, ((countPoints_iff _ _).mp hc).symm,
        ((chemistryPoints_iff _ _).mp hChem).symm,
        (judgmentPoints_iff _ _ _ _).mp hj, (collectionPoints_iff _ _ _).mp hs]
  · intro h
    cases hi : chemistryItems c <;> cases he : c.earlierTestCategoriesThisMonth <;>
      cases hd : c.d400AlreadyChargedToday <;> simp [assess, hi, he, hd] at h
    rename_i items earlier charged
    cases hj : judgmentPoints c.bloodCount items earlier <;>
      cases hs : collectionPoints c.collection charged <;> simp [hj, hs] at h
    subst r
    have selection := (chemistrySelection_iff c items).mpr hi
    have judgment := (judgmentPoints_iff _ _ _ _).mpr hj
    refine ⟨(countPoints_iff _ _).mpr rfl, ?_,
      ⟨items, selection, (chemistryPoints_iff _ _).mpr rfl⟩, ?_,
      ⟨items, earlier, selection, rfl, judgment⟩, ?_,
      ⟨charged, rfl, (collectionPoints_iff _ _ _).mpr hs⟩⟩
    · cases c.bloodCount <;> simp [bloodCountPoints, BloodMorphology.Item.basePoints]
    · intro selected hselected hjaffe
      exact classified_excludes_jaffe c _ _ hselected.2 hjaffe
    · intro history hhistory hh hb
      have same := Option.some.inj hhistory
      subst history
      obtain ⟨a, b, _, h₁, _, h₂, total⟩ := judgment
      simp [hh, hb] at h₁ h₂
      simpa [h₁, h₂] using total

/-- 規則が結果を許容する場合、その内訳は計算結果と一致する。 -/
theorem satisfies_implies_assessed {c : Context} {r : Breakdown} (h : Satisfies rules c r) :
    assess c = some r :=
  (assessed_iff c r).mp h

def Scope (c : Context) : Prop :=
  (∃ items, ChemistrySelection c items) ∧
  (∃ earlier, c.earlierTestCategoriesThisMonth = some earlier) ∧
  (∃ charged, c.d400AlreadyChargedToday = some charged) ∧ CollectionScope c.collection

theorem determines_on : DeterminesOn Scope rules := by
  rintro c ⟨⟨items, hi⟩, ⟨earlier, he⟩, ⟨charged, hd⟩, hc⟩
  classical
  let collection := if SeparateCollection c.collection charged then
    SpecimenCollection.basePoints .venousBlood else 0
  let hematological := if c.bloodCount ≠ [] ∧ .hematological ∉ earlier then
    SpecimenJudgment.scheduledPoints .hematological else 0
  let biochemical := if items ≠ [] ∧ .biochemicalI ∉ earlier then
    SpecimenJudgment.scheduledPoints .biochemicalI else 0
  have hj : JudgmentPoints c.bloodCount items earlier (hematological + biochemical) :=
    ⟨hematological, biochemical, fun h => ite_eq_left h, fun h => ite_eq_right h,
      fun h => ite_eq_left h, fun h => ite_eq_right h, rfl⟩
  have hs : CollectionPoints c.collection charged collection :=
    ⟨hc, fun h => ite_eq_left h, fun h => ite_eq_right h⟩
  refine ⟨⟨⟨bloodCountPoints c.bloodCount, chemistryPoints items,
    hematological + biochemical, collection⟩, (assessed_iff c _).mpr ?_⟩, ?_⟩
  · simp [assess, (chemistrySelection_iff _ _).mp hi, he, hd,
      (judgmentPoints_iff _ _ _ _).mp hj, (collectionPoints_iff _ _ _).mp hs]
  · intro a b ha hb
    exact Option.some.inj ((satisfies_implies_assessed ha).symm.trans (satisfies_implies_assessed hb))

def exampleContext : Context where
  bloodCount := [.redCells, .whiteCells, .hemoglobin, .hematocrit, .platelets]
  chemistry := [.bun, .creatinine, .ast, .alt, .totalProtein, .albumin, .gammaGT, .uricAcid].map
    (fun item => ⟨1, item⟩)
  albuminByModifiedBCP := some true
  creatinineByJaffe := some false
  earlierTestCategoriesThisMonth := some []
  d400AlreadyChargedToday := some false
  collection := { item := .venousBlood, ageYears := 40 }

example : Scope exampleContext := by
  refine ⟨⟨_, (chemistrySelection_iff _ _).mpr rfl⟩, ⟨[], rfl⟩, ⟨false, rfl⟩, ?_⟩
  exact ⟨rfl, rfl, by decide, rfl, rfl⟩

example : ¬ Scope { exampleContext with d400AlreadyChargedToday := none } := by
  simp [Scope]

theorem example_satisfies : Satisfies rules exampleContext ⟨21, 99, 269, 40⟩ := by
  exact (assessed_iff _ _).mpr (by decide)

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
