import Sanri.Examinations
import Sanri.Logic
import Sanri.History
import Sanri.SpecimenRules

namespace Sanri.MedicalFee.SpecimenJudgment

/-! Ｄ０２６の外来算定。Ｄ０２７・入院限定加算の算定処理は後続で扱う。
月内履歴は同一患者・同一医療機関について呼出元が管理する。
通常の検査の判断料区分は入力し、注２・３・６・７の特例は区分番号から判定する。 -/

inductive Category where
  | urineFecal
  | geneticChromosomal
  | hematological
  | biochemicalI
  | biochemicalII
  | immunological
  | microbiological
  deriving DecidableEq, Repr

def allCategories : List Category :=
  [.urineFecal, .geneticChromosomal, .hematological, .biochemicalI,
   .biochemicalII, .immunological, .microbiological]

def scheduledPoints : Category → Nat
  | .urineFecal => 34
  | .geneticChromosomal => 100
  | .hematological => 125
  | .biochemicalI | .biochemicalII | .immunological => 144
  | .microbiological => 150

structure Test where
  /-- Ｄの後の番号（Ｄ００４－２の１なら major=4, suffix=2, number=1）。 -/
  major : Nat
  suffix : Nat := 0
  number : Nat := 0
  /-- 同一項の別検査を区別する。Ｄ０１５の16では０が抗ヒト全血清、１がＩＬ－６。 -/
  variant : Nat := 0
  ordinaryCategory : Category
  performed : Bool := true
  /-- 旧入力との互換用。D000の判断料除外は実施料の算定有無に依存しない。 -/
  d000PointsCharged : Bool := false
  /-- 当該検査の専門知識を有する医師が、その結果を文書報告した。 -/
  specialistWrittenReport : Bool := false
  deriving DecidableEq, Repr

def d026RoutingSource : Logic.SourceRef := {
  kind := .notification
  identifier := "保医発0305第6号 別添1"
  edition := "2026-04-02訂正"
  location := "訂正PDF 4頁、登録版PDF 402頁 D026(6)"
  verification := .checkedAgainstSource
}

/-- 出典は `d026RoutingSource`。D004-3は区分単位で振り分ける。 -/
def geneRouting (t : Test) : Bool :=
  decide ((t.major = 4 ∧ ((t.suffix = 2 ∧ t.number = 1) ∨ t.suffix = 3)) ∨
    (t.major = 6 ∧ ((2 ≤ t.suffix ∧ t.suffix ≤ 9) ∨
      (11 ≤ t.suffix ∧ t.suffix ≤ 20) ∨ (22 ≤ t.suffix ∧ t.suffix ≤ 31))))

def categoryFor (t : Test) : Option Category :=
  if !t.performed then none
  else if t.major = 0 ∧ t.suffix = 0 then none
  else if geneRouting t then some .geneticChromosomal
  else some t.ordinaryCategory

/-- 本文の第1款の検査群による通常の振分け。D004系は個別検査・準用先の
照合結果を保持し、通知(6)の特例は `categoryFor` と共有する。 -/
def ordinaryCategoryFor (t : Test) : Option Category :=
  match t.major with
  | 0 | 1 | 2 | 3 => some .urineFecal
  | 4 => some t.ordinaryCategory
  | 5 | 6 => some .hematological
  | 7 => some .biochemicalI
  | 8 | 9 | 10 => some .biochemicalII
  | 11 | 12 | 13 | 14 | 15 | 16 => some .immunological
  | 17 | 18 | 19 | 20 | 21 | 22 | 23 => some .microbiological
  | _ => none

def standardizedCategoryFor (t : Test) : Option Category :=
  (ordinaryCategoryFor t).bind fun ordinary => categoryFor { t with ordinaryCategory := ordinary }

theorem standardizedCategoryFor_iff (t : Test) (category : Category)
    (h : ordinaryCategoryFor t = some category) :
    standardizedCategoryFor t = categoryFor { t with ordinaryCategory := category } := by
  simp [standardizedCategoryFor, h]

theorem standardizedCategoryFor_legacy (t : Test)
    (h : ordinaryCategoryFor t = some t.ordinaryCategory) :
    standardizedCategoryFor t = categoryFor t := by
  rw [standardizedCategoryFor_iff t _ h]

def Category.number : Category → Nat
  | .urineFecal => 1
  | .geneticChromosomal => 2
  | .hematological => 3
  | .biochemicalI => 4
  | .biochemicalII => 5
  | .immunological => 6
  | .microbiological => 7

private def primary (location : String) : Logic.SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : Logic.SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def categoryRate (category : Category) : Logic.Rule Category Nat :=
  ⟨"primary/D026/item/" ++ toString category.number,
    primary ("PDF192頁 D026 " ++ toString category.number),
    fun c p => c = category → p = scheduledPoints category⟩

def categoryRates := allCategories.map categoryRate

theorem category_rates_iff (category : Category) (p : Nat) :
    Logic.Satisfies categoryRates category p ↔ p = scheduledPoints category := by
  constructor
  · intro h
    exact h (categoryRate category)
      (List.mem_map.mpr ⟨category, by cases category <;> decide, rfl⟩) rfl
  · intro h r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    intro e
    simpa [e] using h

def d000Primary : Logic.Rule Test (Option Category) :=
  ⟨"primary/D026/note/2", primary "PDF192頁 D026注2",
    fun t category => t.performed = true → t.d000PointsCharged = true → t.major = 0 → t.suffix = 0 →
      category ≠ some .urineFecal⟩

/-- D004-3の追加は告示注3の列挙とは別に、訂正後の通知(6)で扱う。 -/
def genePrimary : Logic.Rule Test (Option Category) :=
  ⟨"primary/D026/note/3", primary "PDF192頁 D026注3",
    fun t category => t.performed = true → geneRouting t = true →
      ¬ (t.major = 4 ∧ t.suffix = 3) → category = some .geneticChromosomal⟩

def d000Notification : Logic.Rule Test (Option Category) :=
  ⟨"notice/D026/paragraph/5", notice "PDF402頁 D026(5) D000の実施",
    fun t category => t.performed = true → t.major = 0 → t.suffix = 0 → category = none⟩

def geneNotification : Logic.Rule Test (Option Category) :=
  ⟨"notice/D026/paragraph/6", d026RoutingSource,
    fun t category => t.performed = true → geneRouting t = true →
      category = some .geneticChromosomal⟩

theorem categoryFor_d000 (t : Test) : d000Notification.holds t (categoryFor t) := by
  intro performed major suffix
  simp [categoryFor, performed, major, suffix]

theorem categoryFor_gene (t : Test) : geneNotification.holds t (categoryFor t) := by
  intro performed gene
  have notD000 : ¬ (t.major = 0 ∧ t.suffix = 0) := by
    rintro ⟨major, _⟩
    simp [geneRouting, major] at gene
  simp [categoryFor, performed, gene, notD000]

/-- 注１のＤ０２７による包括。生化学（Ⅱ）は列挙にないため除外しない。 -/
def includedInD027 : Category → Bool
  | .biochemicalII => false
  | _ => true

inductive ManagementCategory where
  | none
  | categoryI
  | categoryII
  | categoryIII
  | categoryIV
  deriving DecidableEq, Repr

structure Context where
  insuranceMedicalInstitution : Bool := true
  status : ConsultationGeneralRules.PatientStatus := .outpatient
  tests : List Test := []
  /-- 算定済み区分の履歴。各区分は種類・実施回数にかかわらず月１回。 -/
  categoriesClaimedThisMonth : List Category := []
  /-- Ｄ０２７を算定する患者か（例：同月の入院時の算定を呼出元が把握）。 -/
  basicD027ClaimedForPatient : Bool := false
  management : ManagementCategory := .none
  managementStandardNotified : Bool := false
  /-- Ｄ０２６・Ｄ０２７を通じ、いずれかの検体検査管理加算の同月算定済み回数。 -/
  managementClaimsThisMonth : Nat := 0
  claimInternationalStandardAddition : Bool := false
  deriving DecidableEq, Repr

structure Assessment where
  categories : List Category
  judgment : Nat
  management : Nat
  boneMarrowDiagnosis : Nat
  immunoelectrophoresisDiagnosis : Nat
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Nat :=
  a.judgment + a.management + a.boneMarrowDiagnosis + a.immunoelectrophoresisDiagnosis

def boneMarrowEligible (t : Test) : Bool :=
  t.performed && decide (t.major = 5 ∧ t.suffix = 0 ∧ t.number = 14) && t.specialistWrittenReport

def immunoelectrophoresisEligible (t : Test) : Bool :=
  t.performed && decide (t.major = 15 ∧ t.suffix = 0) &&
    (decide (t.number = 16 ∧ t.variant = 0) || decide (t.number = 23 ∨ t.number = 30)) &&
    t.specialistWrittenReport

/-- 加算の文書報告・専門性の確認と採取場所を、適格な検査の実施と区別する。 -/
structure DiagnosisEvidence where
  test : Test
  physicianExperienceYears : Option Nat := none
  marrowCollectedAtInstitution : Option Bool := none
  interpretedElectrophoresisImage : Option Bool := none
  reportForDiagnosis : Option Bool := none

def marrowReport (e : DiagnosisEvidence) : Prop :=
  boneMarrowEligible e.test = true ∧
    (∃ years, e.physicianExperienceYears = some years ∧ 5 ≤ years) ∧
    e.marrowCollectedAtInstitution = some true

def electrophoresisReport (e : DiagnosisEvidence) : Prop :=
  immunoelectrophoresisEligible e.test = true ∧
    (∃ years, e.physicianExperienceYears = some years ∧ 5 ≤ years) ∧
    e.interpretedElectrophoresisImage = some true ∧ e.reportForDiagnosis = some true

def managementIPoints : Nat := 40
def marrowPoints : Nat := 240
def electrophoresisPoints : Nat := 50

def marrowAddition : Logic.Rule Test Nat :=
  ⟨"primary/D026/note/6", primary "PDF192頁 D026注6",
    fun t p => p = marrowPoints ∧ boneMarrowEligible t = true⟩

def electrophoresisAddition : Logic.Rule Test Nat :=
  ⟨"primary/D026/note/7", primary "PDF192–193頁 D026注7",
    fun t p => p = electrophoresisPoints ∧ immunoelectrophoresisEligible t = true⟩

/-- 骨髄像診断加算だけを射影した算定履歴。 -/
structure MarrowEvidence extends DiagnosisEvidence where
  site : Sanri.History.Site
  history : Sanri.History.ClaimHistory Unit

def marrowNotification : Logic.Rule MarrowEvidence Unit :=
  ⟨"notice/D026/paragraph/9", notice "PDF403頁 D026(9)", fun c _ =>
    marrowReport c.toDiagnosisEvidence ∧
    Sanri.History.withinLimit c.history c.site.monthScope (fun _ => true) 0 = some true⟩

def electrophoresisNotification : Logic.Rule DiagnosisEvidence Unit :=
  ⟨"notice/D026/paragraph/10", notice "PDF403頁 D026(10)", fun c _ =>
    electrophoresisReport c⟩

def managementI : Logic.Rule Unit Nat :=
  ⟨"primary/D026/note/4/i", primary "PDF192頁 D026注4イ", fun _ p => p = managementIPoints⟩

/-- 他区分を算定済みの月の包括対象かは、検査の実施ごとに照合する。 -/
structure IncludedTest where
  test : Test
  b001_15ClaimedThisMonth : Bool
  d025ClaimedThisMonth : Bool
  includedInB001_15 : Option Bool := none
  includedInD025 : Option Bool := none

def IncludedTest.separateEligibility (c : IncludedTest) : Option Bool := do
  let b001 ← if c.b001_15ClaimedThisMonth then c.includedInB001_15 else some false
  let d025 ← if c.d025ClaimedThisMonth then c.includedInD025 else some false
  return !b001 && !d025

def coveredTestNotification : Logic.Rule IncludedTest Unit :=
  ⟨"notice/D026/paragraph/5", notice "PDF402頁 D026(5) B001の15・D025",
    fun c _ => (c.b001_15ClaimedThisMonth = true → c.includedInB001_15 = some false) ∧
      (c.d025ClaimedThisMonth = true → c.includedInD025 = some false)⟩

def d025Admission : Logic.Rule (ConsultationGeneralRules.PatientStatus × Bool) Unit :=
  ⟨"primary/D025/note/1", primary "PDF191頁 D025注1",
    fun (status, advancedTreatmentHospital) _ => status = .inpatient ∧ advancedTreatmentHospital = true⟩

def d027Admission : Logic.Rule (ConsultationGeneralRules.PatientStatus × Bool) Unit :=
  ⟨"primary/D027/note/1", primary "PDF193頁 D027注1",
    fun (status, advancedTreatmentHospital) _ => status = .inpatient ∧ advancedTreatmentHospital = true⟩

def d027Exclusion : Logic.Rule (Bool × Category) Unit :=
  ⟨"notice/D027/paragraph/5", notice "PDF403頁 D027(5)", fun (applies, category) _ =>
    applies = true → includedInD027 category = false⟩

/-- 外来用。入院・短期滞在、管理加算Ⅱ〜Ⅳ、注５の加算の請求は受け付けない。
判断料本体の月内既算定だけを理由に、独自の回数制限のない診断加算を落とさない。 -/
def assess (c : Context) : Option Assessment :=
  if !c.insuranceMedicalInstitution || c.status != .outpatient ||
      c.management ∈ [.categoryII, .categoryIII, .categoryIV] ||
      c.claimInternationalStandardAddition then none
  else
    let categories := allCategories.filter (fun category =>
      c.tests.any (fun t => categoryFor t == some category) &&
      !c.categoriesClaimedThisMonth.contains category &&
      !(c.basicD027ClaimedForPatient && includedInD027 category))
    let management := if c.management = .categoryI && c.managementStandardNotified &&
      !categories.isEmpty && decide (c.managementClaimsThisMonth = 0) then managementIPoints else 0
    some {
      categories := categories
      judgment := (categories.map scheduledPoints).sum
      management := management
      boneMarrowDiagnosis := if c.tests.any boneMarrowEligible then marrowPoints else 0
      immunoelectrophoresisDiagnosis := if c.tests.any immunoelectrophoresisEligible then electrophoresisPoints else 0 }

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-- 第１節の実施料＋判断料へ接続。外来の入力だけを受け付け、判断料を上書きする。 -/
def applyToSpecimen (judgment : Context) (specimen : Examinations.SpecimenContext) :
    Option Examinations.SpecimenContext := do
  if specimen.inpatient then none else
    let a ← assess judgment
    some { specimen with judgmentPoints := a.total }

/-- 準用元の実施を保持する。準用先の検査を実施したものとして扱わない。 -/
inductive D023Reference where
  | bk (request : SpecimenTests.BkRequest)
  | mycobacteria (request : SpecimenTests.MycobacteriaRequest)

def D023Reference.points : D023Reference → Option Nat
  | .bk request => SpecimenTests.bkReferencePoints request
  | .mycobacteria request => SpecimenTests.mycobacteriaReferencePoints request

/-- 第１款の微生物学的検査。準用元に告示の項番はない。 -/
def D023Reference.judgmentTest (_ : D023Reference) : Test :=
  { major := 23, ordinaryCategory := .microbiological }

/-- 外来の同一集計範囲で既存の実施料・判断料一覧に準用を追加する。
既存一覧との実施の重複は呼出元で照合し、この一覧内では実施IDを照合する。 -/
def applyD023References (references : List (Nat × D023Reference))
    (judgment : Context) (specimen : Examinations.SpecimenContext) :
    Option Examinations.SpecimenContext := do
  if !(references.map Prod.fst).Nodup then none else
    let items ← references.mapM fun (_, reference) => do
      let points ← reference.points
      pure ({ kind := 23, executionPoints := points } : Examinations.SpecimenItem)
    applyToSpecimen
      { judgment with tests := judgment.tests ++ references.map (·.2.judgmentTest) }
      { specimen with items := specimen.items ++ items }

private def bkSample : D023Reference :=
  .bk {
    insuranceMedicalInstitution := true
    performed := true
    specimen := .plasma
    organOrHematopoieticCellTransplant := true
    indication := some .suspectedNephropathy
    recordedIndication := some .suspectedNephropathy }

private def mycobacteriaReferenceSample : D023Reference :=
  .mycobacteria {
    insuranceMedicalInstitution := true
    performed := true
    specimen := .sputum
    dnaDetectionByPcrRsso := true
    panelSize := 28
    claimsInTreatmentSeries := 0
    indication := some .suspectedPulmonaryTbAndNontuberculousDisease
    recordedIndication := some .suspectedPulmonaryTbAndNontuberculousDisease
    necessityRecorded := true
    staffingRequirementMet := true }

example : (do
    let assessed ← applyD023References [(1, bkSample), (2, mycobacteriaReferenceSample)] {} {}
    let execution ← Examinations.executionPoints assessed
    pure (execution, assessed.judgmentPoints)) = some (1413, 150) := by decide

example : (applyD023References [(1, bkSample)]
    { categoriesClaimedThisMonth := [.microbiological] } {}).map (·.judgmentPoints) =
    some 0 := by decide

example : (applyD023References [(1, bkSample), (1, bkSample)] {} {}).isNone = true := by decide

example : (do
    let assessed ← applyD023References [(1, bkSample)]
      { tests := [{ major := 13, number := 4, ordinaryCategory := .immunological }] }
      { items := [{ kind := 13, executionPoints := 98 }] }
    let execution ← Examinations.executionPoints assessed
    pure (execution, assessed.judgmentPoints)) = some (548, 294) := by decide

private def urine : Test :=
  { major := 1, ordinaryCategory := .urineFecal }
private def gene (suffix : Nat) : Test :=
  { major := 6, suffix := suffix, ordinaryCategory := .hematological }
private def electrophoresis : Test :=
  { major := 15, number := 16, ordinaryCategory := .immunological, specialistWrittenReport := true }

private def methylation : Test := { major := 4, suffix := 3, ordinaryCategory := .urineFecal }

-- 旧来の振分けではD004-3は入力の通常区分を採用していた。
example : scheduledPoints methylation.ordinaryCategory = 34 ∧
    categoryFor methylation = some .geneticChromosomal ∧
    points { tests := [methylation] } = some 100 := by decide

example : allCategories.map scheduledPoints = [34, 100, 125, 144, 144, 144, 150] := rfl
example : points { tests := [urine, urine, urine] } = some 34 := by decide
example : points { tests := [urine], categoriesClaimedThisMonth := [.urineFecal] } = some 0 := by decide
example : points { tests := [{ urine with major := 0 }] } = some 0 := by decide
example : points { tests := [{ urine with major := 0, d000PointsCharged := true }] } = some 0 := by decide
example : points { tests := [urine, { urine with major := 0, d000PointsCharged := true }] } = some 34 := by decide
example : (List.map (fun n => categoryFor (gene n)) [1, 2, 9, 10, 11, 20, 21, 22, 31, 32]) =
    [some .hematological, some .geneticChromosomal, some .geneticChromosomal, some .hematological, some .geneticChromosomal, some .geneticChromosomal, some .hematological, some .geneticChromosomal, some .geneticChromosomal, some .hematological] := by decide
example : categoryFor { urine with major := 4, suffix := 2, number := 1 } = some .geneticChromosomal := by decide
example : categoryFor { urine with major := 4, suffix := 2, number := 2 } = some .urineFecal := by decide
example : points { tests := [gene 2, gene 9] } = some 100 := by decide
example : points { tests := [gene 2, urine] } = some 134 := by decide
example : points { tests := [urine, { urine with ordinaryCategory := .biochemicalII }], basicD027ClaimedForPatient := true } = some 144 := by decide
example : points { tests := [urine], management := .categoryI, managementStandardNotified := true } = some 74 := by decide
example : points { tests := [urine]
                   management := .categoryI
                   managementStandardNotified := true
                   categoriesClaimedThisMonth := [.urineFecal] } =
    some 0 := by decide
example : points { tests := [urine], management := .categoryI } = some 34 := by decide
example : points { tests := [urine], management := .categoryI, managementStandardNotified := true, managementClaimsThisMonth := 1 } = some 34 := by decide
example : points { tests := [urine], management := .categoryII } = none := by decide
example : points { tests := [urine], claimInternationalStandardAddition := true } = none := by decide
example : points { status := .inpatient, tests := [urine] } = none := by decide
example : points { status := .shortStaySurgeryBasicFeePatient, tests := [urine] } = none := by decide
example : points { tests := [electrophoresis] } = some 194 := by decide
example : points { tests := [{ electrophoresis with variant := 1 }] } = some 144 := by decide
example : points { tests := [{ electrophoresis with specialistWrittenReport := false }] } = some 144 := by decide
example : points { tests := [{ electrophoresis with number := 23 }] } = some 194 := by decide
example : points { tests := [{ electrophoresis with number := 30 }] } = some 194 := by decide
example : points { tests := [{ electrophoresis with number := 23 }], categoriesClaimedThisMonth := [.immunological] } = some 50 := by decide
example : points { tests := [{ major := 5, number := 14, ordinaryCategory := .hematological, specialistWrittenReport := true }] } = some 365 := by decide
example : points { tests := [{ major := 5, number := 14, ordinaryCategory := .hematological }] } = some 125 := by decide
example : (applyToSpecimen { tests := [urine] } {}).map Examinations.SpecimenContext.judgmentPoints =
    some 34 := by decide
example : applyToSpecimen { tests := [urine] } { inpatient := true } = none := by decide

end Sanri.MedicalFee.SpecimenJudgment
