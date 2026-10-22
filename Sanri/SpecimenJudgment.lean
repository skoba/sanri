import Sanri.Examinations

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
  d000PointsCharged : Bool := false
  /-- 当該検査の専門知識を有する医師が、その結果を文書報告した。 -/
  specialistWrittenReport : Bool := false
  deriving DecidableEq, Repr

/-- 注３。Ｄ００６－10・21など、指定範囲の隙間を含めない。 -/
def geneRouting (t : Test) : Bool :=
  decide ((t.major = 4 ∧ t.suffix = 2 ∧ t.number = 1) ∨
    (t.major = 6 ∧ ((2 ≤ t.suffix ∧ t.suffix ≤ 9) ∨
      (11 ≤ t.suffix ∧ t.suffix ≤ 20) ∨ (22 ≤ t.suffix ∧ t.suffix ≤ 31))))

def categoryFor (t : Test) : Option Category :=
  if !t.performed then none
  else if t.major = 0 ∧ t.suffix = 0 ∧ t.d000PointsCharged = true then none
  else if geneRouting t then some .geneticChromosomal
  else some t.ordinaryCategory

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
      c.tests.any (fun t => t.performed) && decide (c.managementClaimsThisMonth = 0) then 40 else 0
    some {
      categories := categories
      judgment := (categories.map scheduledPoints).sum
      management := management
      boneMarrowDiagnosis := if c.tests.any boneMarrowEligible then 240 else 0
      immunoelectrophoresisDiagnosis := if c.tests.any immunoelectrophoresisEligible then 50 else 0 }

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-- 第１節の実施料＋判断料へ接続。外来の入力だけを受け付け、判断料を上書きする。 -/
def applyToSpecimen (judgment : Context) (specimen : Examinations.SpecimenContext) :
    Option Examinations.SpecimenContext := do
  if specimen.inpatient then none else
    let a ← assess judgment
    some { specimen with judgmentPoints := a.total }

private def urine : Test :=
  { major := 1, ordinaryCategory := .urineFecal }
private def gene (suffix : Nat) : Test :=
  { major := 6, suffix := suffix, ordinaryCategory := .hematological }
private def electrophoresis : Test :=
  { major := 15, number := 16, ordinaryCategory := .immunological, specialistWrittenReport := true }

example : allCategories.map scheduledPoints = [34, 100, 125, 144, 144, 144, 150] := rfl
example : points { tests := [urine, urine, urine] } = some 34 := by decide
example : points { tests := [urine], categoriesClaimedThisMonth := [.urineFecal] } = some 0 := by decide
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
