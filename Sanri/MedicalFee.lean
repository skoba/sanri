namespace Sanri
namespace MedicalFee

inductive Section where
  | generalRules -- Tsusoku
  | basicFees -- Kihon Shinryou-ryo
  | specialFees -- Tokukei Shinryou-ryo
  deriving DecidableEq, Repr

inductive FeeItem where
  | initialConsultation -- Shoshinryou
  | revisitConsultation -- Saishinryou
  | outpatientConsultation -- Gairai Shinryou-ryo
  | prescriptionFee -- Shohousenryou
  deriving DecidableEq, Repr

inductive Facility where
  | clinic
  /-- 全許可病床が一般病床である病院の略記。 -/
  | hospital (beds : Nat)
  /-- 許可病床総数と、そのうちの一般病床数を区別する。 -/
  | hospitalWithGeneralBeds (permittedBeds generalBeds : Nat)
  deriving DecidableEq, Repr

/-- 通則２に従う診療の別。 -/
inductive CareDomain where
  | medical
  | dental
  deriving DecidableEq, Repr

structure Claim where
  day : Nat
  item : FeeItem
  domain : CareDomain := .medical
  deriving DecidableEq, Repr

def sectionOf : FeeItem → Section
  | .initialConsultation => .basicFees
  | .revisitConsultation => .basicFees
  | .outpatientConsultation => .basicFees
  | .prescriptionFee => .specialFees

/-- 各項目の基本点数。初診料の注による置換・加算・算定可否は
`InitialConsultation.assess`（Sanri.InitialConsultation）で評価する。
再診料の注・通則３は `RevisitConsultation.assess`（Sanri.RevisitConsultation）、
外来診療料は `OutpatientConsultation.assess`（Sanri.OutpatientConsultation）で評価する。 -/
def pointsAt (facility : Facility) : FeeItem → Option Nat
  | .initialConsultation => some 291
  | .revisitConsultation =>
      match facility with
      | .clinic => some 76
      | .hospital beds => if beds < 200 then some 76 else none
      | .hospitalWithGeneralBeds _ generalBeds => if generalBeds < 200 then some 76 else none
  | .outpatientConsultation =>
      match facility with
      | .clinic => none
      | .hospital beds => if 200 ≤ beds then some 77 else none
      | .hospitalWithGeneralBeds _ generalBeds => if 200 ≤ generalBeds then some 77 else none
  | .prescriptionFee => none

theorem initialConsultation_isBasic :
    sectionOf .initialConsultation = .basicFees := rfl

theorem revisitConsultation_isBasic :
    sectionOf .revisitConsultation = .basicFees := rfl

theorem outpatientConsultation_isBasic :
    sectionOf .outpatientConsultation = .basicFees := rfl

theorem prescriptionFee_isSpecial :
    sectionOf .prescriptionFee = .specialFees := rfl

theorem initialConsultation_points (facility : Facility) :
    pointsAt facility .initialConsultation = some 291 := rfl

theorem clinic_revisitConsultation_points :
    pointsAt .clinic .revisitConsultation = some 76 := rfl

theorem hospital_under200_revisitConsultation_points (beds : Nat)
    (h : beds < 200) :
    pointsAt (.hospital beds) .revisitConsultation = some 76 := by
  simp [pointsAt, h]

theorem hospital_200_or_more_revisitConsultation_unavailable (beds : Nat)
    (h : 200 ≤ beds) :
    pointsAt (.hospital beds) .revisitConsultation = none := by
  simp [pointsAt, Nat.not_lt.mpr h]

theorem hospital_under200_outpatientConsultation_unavailable (beds : Nat)
    (h : beds < 200) :
    pointsAt (.hospital beds) .outpatientConsultation = none := by
  simp [pointsAt, Nat.not_le.mpr h]

theorem hospital_200_or_more_outpatientConsultation_points (beds : Nat)
    (h : 200 ≤ beds) :
    pointsAt (.hospital beds) .outpatientConsultation = some 77 := by
  simp [pointsAt, h]

/-- 従来の同日併算定制約。通則２に合わせ、同じ診療の別の中で検査する。
この制約自体は今回提示された通則１〜３から導出するものではない。 -/
def NoSameDayInitialAndRevisit (claims : List Claim) : Prop :=
  ∀ (day : Nat) (domain : CareDomain),
    Claim.mk day .initialConsultation domain ∈ claims →
    Claim.mk day .revisitConsultation domain ∉ claims

theorem sameDayInitialAndRevisit_not_allowed
    (claims : List Claim)
    (day : Nat)
    (initialClaim : Claim.mk day .initialConsultation .medical ∈ claims)
    (revisitClaim : Claim.mk day .revisitConsultation .medical ∈ claims) :
    ¬ NoSameDayInitialAndRevisit claims := by
  intro noSameDayClaims
  exact noSameDayClaims day .medical initialClaim revisitClaim

/-! 初・再診料の通則１〜３。対象は提示された法令の適用範囲内の診療とする。
同時診療のまとまりは呼出元が識別する。「同時」を「同日」に置き換えない。
歯科の点数表や参照先の注の詳細はここでは補わない。 -/
namespace ConsultationGeneralRules

inductive Kind where
  | initial
  | revisit
  | outpatient
  deriving DecidableEq, Repr

def feeItem : Kind → FeeItem
  | .initial => .initialConsultation
  | .revisit => .revisitConsultation
  | .outpatient => .outpatientConsultation

/-- 通則１の例外。参照先の要件を満たすかは、その注の仕様で判定する。 -/
structure Exceptions where
  initialNote5Proviso : Bool := false
  revisitNote3 : Bool := false
  outpatientNote5 : Bool := false
  deriving DecidableEq, Repr

inductive MultipleDiseaseNote where
  | a000Note5Proviso
  | a001Note3
  | a002Note5
  deriving DecidableEq, Repr

def applicableException (kind : Kind) (e : Exceptions) : Option MultipleDiseaseNote :=
  match kind with
  | .initial => if e.initialNote5Proviso then some .a000Note5Proviso else none
  | .revisit => if e.revisitNote3 then some .a001Note3 else none
  | .outpatient => if e.outpatientNote5 then some .a002Note5 else none

/-- １患者・１医療機関・１回の同時診療・１種類の診療（歯科／歯科以外）。
両方の診療を行う場合は、それぞれのまとまりを作り独立に評価する。 -/
structure Encounter where
  domain : CareDomain
  kind : Kind
  simultaneousDiseaseCount : Nat
  exceptions : Exceptions := {}
  deriving DecidableEq, Repr

inductive CountRule where
  | noConsultation
  | once
  /-- 例外先の注で回数・点数を決定する。複数回や満額とは仮定しない。 -/
  | accordingToNote (note : MultipleDiseaseNote)
  deriving DecidableEq, Repr

/-- 通則１・２。傷病数が増えても原則１回。歯科と歯科以外で回数を合算しない。 -/
def countRule (e : Encounter) : CountRule :=
  if e.simultaneousDiseaseCount = 0 then .noConsultation
  else if e.simultaneousDiseaseCount ≥ 2 then
    match applicableException e.kind e.exceptions with
    | some note => .accordingToNote note
    | none => .once
  else .once

/-- 通則１の所定点数への参照。歯科は別表の仕様に委ねる。
`none` はこの医科モデルで点数を解決しないことを表す。 -/
def scheduledMedicalPoints (f : Facility) (e : Encounter) : Option Nat :=
  match e.domain with
  | .medical => pointsAt f (feeItem e.kind)
  | .dental => none

inductive PatientStatus where
  | outpatient
  | inpatient
  | shortStaySurgeryBasicFeePatient
  deriving DecidableEq, Repr

/-- 通則３で包括から除外される加算の参照。点数・個別要件は未定義。 -/
inductive RevisitAddition where
  | a001Note5
  | a001Note6
  | a002Note8
  | a002Note9
  deriving DecidableEq, Repr

inductive RevisitComponent where
  | base
  | addition (note : RevisitAddition)
  deriving DecidableEq, Repr

inductive CostTreatment where
  | accordingToSection1Or2
  | includedInPart2Section1Or3Or4
  /-- 包括対象から除外される。実際の算定可否は参照先の注による。 -/
  | accordingToAdditionNote (note : RevisitAddition)
  deriving DecidableEq, Repr

/-- 通則３は再診の費用に適用する。初診料には適用しない。 -/
def initialCostTreatment : CostTreatment := .accordingToSection1Or2

def revisitCostTreatment (status : PatientStatus) (component : RevisitComponent) :
    CostTreatment :=
  match status, component with
  | .outpatient, .base => .accordingToSection1Or2
  | .outpatient, .addition note => .accordingToAdditionNote note
  | _, .base => .includedInPart2Section1Or3Or4
  | _, .addition note => .accordingToAdditionNote note

theorem multipleDiseases_once (e : Encounter)
    (nonzero : e.simultaneousDiseaseCount ≠ 0)
    (noException : applicableException e.kind e.exceptions = none) :
    countRule e = .once := by
  simp [countRule, nonzero, noException]

theorem dentalAndMedical_countedSeparately (e : Encounter) :
    countRule { e with domain := .medical } = countRule { e with domain := .dental } := rfl

theorem inpatientRevisit_included :
    revisitCostTreatment .inpatient .base = .includedInPart2Section1Or3Or4 := rfl

theorem shortStayRevisit_included :
    revisitCostTreatment .shortStaySurgeryBasicFeePatient .base =
      .includedInPart2Section1Or3Or4 := rfl

theorem inpatientAddition_excludedFromInclusion (status : PatientStatus)
    (note : RevisitAddition) :
    revisitCostTreatment status (.addition note) = .accordingToAdditionNote note := by
  cases status <;> rfl

example : countRule ⟨.medical, .initial, 0, {}⟩ = .noConsultation := by decide
example : countRule ⟨.medical, .initial, 3, {}⟩ = .once := by decide
example : countRule ⟨.medical, .revisit, 2, {}⟩ = .once := by decide
example : countRule ⟨.medical, .outpatient, 2, {}⟩ = .once := by decide
example : countRule ⟨.medical, .initial, 2, { initialNote5Proviso := true }⟩ =
    .accordingToNote .a000Note5Proviso := by decide
example : countRule ⟨.medical, .revisit, 2, { revisitNote3 := true }⟩ =
    .accordingToNote .a001Note3 := by decide
example : countRule ⟨.medical, .outpatient, 2, { outpatientNote5 := true }⟩ =
    .accordingToNote .a002Note5 := by decide
example : countRule ⟨.medical, .initial, 2, { revisitNote3 := true }⟩ = .once := by decide
example : countRule ⟨.medical, .initial, 1, { initialNote5Proviso := true }⟩ = .once := by decide
example : scheduledMedicalPoints .clinic ⟨.medical, .initial, 1, {}⟩ = some 291 := rfl
example : scheduledMedicalPoints .clinic ⟨.dental, .initial, 1, {}⟩ = none := rfl
example : NoSameDayInitialAndRevisit
    [⟨1, .initialConsultation, .medical⟩, ⟨1, .revisitConsultation, .dental⟩] := by
  intro day domain hi hr
  simp at hi hr
  rcases hi with ⟨rfl, rfl⟩
  simp at hr

end ConsultationGeneralRules

/-! 第５節 Ｆ４００ 処方箋料。
提示された本文をモデル化する。大臣指定・「一定以上」等の外部定義は
入力として与え、数値や要件をここで補わない。各入力は同一患者・同一月を対象とする。
`pointsAt` は施設だけで確定する点数用であり、処方箋料には以下を用いる。 -/
namespace PrescriptionFee

inductive Category where
  | psychotropicPolypharmacy -- １
  | otherPolypharmacyOrLongTerm -- ２
  | ordinary -- ３
  deriving DecidableEq, Repr

/-- 種類数は各除外を適用した後の数。
抗不安薬・睡眠薬は臨時の投薬等を除外する。
抗うつ薬・抗精神病薬はさらに、病状等によりやむを得ない３種類の投与を除外する。
４種類以上の投与を「やむを得ない３種類」として除外してはならない。 -/
structure Medication where
  anxiolytics : Nat := 0
  hypnotics : Nat := 0
  antidepressants : Nat := 0
  antipsychotics : Nat := 0
  /-- 臨時かつ２週間以内の薬を除外した内服薬の種類数。 -/
  oralDrugs : Nat := 0
  regionalComprehensiveCareAddition : Bool := false
  anxietyOrInsomnia : Bool := false
  designatedDrugForAtLeastOneYear : Bool := false
  experiencedDoctorOrPsychiatristAdviceOrEquivalent : Bool := false
  deriving DecidableEq, Repr

def category (m : Medication) : Category :=
  if m.anxiolytics ≥ 3 ∨ m.hypnotics ≥ 3 ∨ m.antidepressants ≥ 3 ∨
      m.antipsychotics ≥ 3 ∨ m.anxiolytics + m.hypnotics ≥ 4 then
    .psychotropicPolypharmacy
  else if (m.oralDrugs ≥ 7 ∧ m.regionalComprehensiveCareAddition = false) ∨
      (m.anxietyOrInsomnia = true ∧ m.designatedDrugForAtLeastOneYear = true ∧
        m.experiencedDoctorOrPsychiatristAdviceOrEquivalent = false) then
    .otherPolypharmacyOrLongTerm
  else .ordinary

/-- 注８の３要件を別々に記録する。 -/
structure PharmacyRelationship where
  issuedEnoughPrescriptionsInLastThreeMonths : Bool := false
  specialDispensingBasicFeeAAndConcentratedReception : Bool := false
  specialRelationshipIncludingRealEstate : Bool := false
  deriving DecidableEq, Repr

def substitutesPoints (r : PharmacyRelationship) : Bool :=
  r.issuedEnoughPrescriptionsInLastThreeMonths &&
  r.specialDispensingBasicFeeAAndConcentratedReception &&
  r.specialRelationshipIncludingRealEstate

def basePoints (c : Category) (substitute : Bool) : Nat :=
  match c, substitute with
  | .psychotropicPolypharmacy, false => 20
  | .otherPolypharmacyOrLongTerm, false => 32
  | .ordinary, false => 60
  | .psychotropicPolypharmacy, true => 18
  | .otherPolypharmacyOrLongTerm, true => 29
  | .ordinary, true => 42

structure LongPrescription where
  initialNote2Or3OrOutpatientNote2Or3 : Bool := false
  /-- 大臣指定の除外薬剤を除き、１処方で30日以上の投薬を行った。 -/
  nonExemptDrugForAtLeast30Days : Bool := false
  refill : Bool := false
  daysPerRefillUse : Nat := 0
  deriving DecidableEq, Repr

def reduced (p : LongPrescription) : Bool :=
  p.initialNote2Or3OrOutpatientNote2Or3 && p.nonExemptDrugForAtLeast30Days &&
    !(p.refill && decide (p.daysPerRefillUse ≤ 29))

inductive GenericNameAddition where
  | none
  | category1
  | category2
  deriving DecidableEq, Repr

structure Additions where
  ageUnderThree : Bool := false
  inpatient : Bool := false
  designatedPrimaryDisease : Bool := false
  /-- リフィルの場合は複数回使用の合計日数。 -/
  prescribedDaysIncludingRefills : Nat := 0
  specificDiseaseClaimsThisMonth : Nat := 0
  notifiedAntineoplasticFacilityStandard : Bool := false
  writtenExplanationAtTreatmentStart : Bool := false
  antineoplasticPrescription : Bool := false
  antineoplasticClaimsThisMonth : Nat := 0
  genericNameFacilityStandard : Bool := false
  /-- 処方箋の内容が満たす区分（外部で定める要件により判定）。 -/
  genericName : GenericNameAddition := .none
  previouslyPrescribedPsychotropics : Bool := false
  comprehensiveEvaluationAndAdjustment : Bool := false
  psychotropicTypesOrDoseDecreased : Bool := false
  pharmacistInstructedToCheckSymptomChanges : Bool := false
  psychotropicCoordinationClaimsThisMonth : Nat := 0
  claimsA250ThisMonth : Bool := false
  claimsB008_2ThisMonth : Bool := false
  deriving DecidableEq, Repr

def smallFacility : Facility → Bool
  | .clinic => true
  | .hospital beds => decide (beds < 200)
  | .hospitalWithGeneralBeds permittedBeds _ => decide (permittedBeds < 200)

def largeHospital : Facility → Bool
  | .clinic => false
  | .hospital beds => decide (200 ≤ beds)
  | .hospitalWithGeneralBeds permittedBeds _ => decide (200 ≤ permittedBeds)

/-- 注３。交付１回につき。 -/
def infantPoints (a : Additions) : Nat :=
  if a.ageUnderThree then 3 else 0

/-- 注４。月１回、１処方につき。 -/
def specificDiseasePoints (f : Facility) (a : Additions) : Nat :=
  if smallFacility f = true ∧ a.inpatient = false ∧ a.designatedPrimaryDisease = true ∧
      a.prescribedDaysIncludingRefills ≥ 28 ∧ a.specificDiseaseClaimsThisMonth = 0
  then 56 else 0

/-- 注５。月１回、交付１回につき。 -/
def antineoplasticPoints (f : Facility) (a : Additions) : Nat :=
  if largeHospital f = true ∧ a.notifiedAntineoplasticFacilityStandard = true ∧
      a.writtenExplanationAtTreatmentStart = true ∧ a.antineoplasticPrescription = true ∧
      a.antineoplasticClaimsThisMonth = 0 then 70 else 0

/-- 注６。区分１・２を重複加算しない。 -/
def genericNamePoints (a : Additions) : Nat :=
  if a.genericNameFacilityStandard then
    match a.genericName with
    | .none => 0
    | .category1 => 8
    | .category2 => 6
  else 0

/-- 注７の臨床要件と月１回の制限。併算定禁止は `validClaim` で検査する。 -/
def psychotropicCoordinationEligible (a : Additions) : Bool :=
  a.previouslyPrescribedPsychotropics && a.comprehensiveEvaluationAndAdjustment &&
  a.psychotropicTypesOrDoseDecreased && a.pharmacistInstructedToCheckSymptomChanges &&
  decide (a.psychotropicCoordinationClaimsThisMonth = 0)

structure Context where
  facility : Facility
  /-- 注１：保険薬局で調剤を受けるために処方箋を交付した。 -/
  issuedForInsurancePharmacy : Bool := false
  medication : Medication := {}
  relationship : PharmacyRelationship := {}
  longPrescription : LongPrescription := {}
  additions : Additions := {}
  /-- 注７の加算を今回請求するか。 -/
  claimPsychotropicCoordination : Bool := false
  deriving DecidableEq, Repr

def validClaim (c : Context) : Bool :=
  c.issuedForInsurancePharmacy &&
    (!c.claimPsychotropicCoordination ||
      (psychotropicCoordinationEligible c.additions &&
        !c.additions.claimsA250ThisMonth && !c.additions.claimsB008_2ThisMonth))

/-- 点数を1/5点単位で正確に表す。提示文にない端数処理は行わない。 -/
structure Points where
  fifths : Nat
  deriving DecidableEq, Repr

/-- 交付１回についての点数。注２の40%は基本点数に適用し、加算はその後に加える。
月内算定済回数は呼出元が記録・更新する。 -/
def points (c : Context) : Option Points :=
  if validClaim c then
    let base := basePoints (category c.medication) (substitutesPoints c.relationship)
    let adjusted := if reduced c.longPrescription then 2 * base else 5 * base
    let extra := infantPoints c.additions + specificDiseasePoints c.facility c.additions +
      antineoplasticPoints c.facility c.additions + genericNamePoints c.additions +
      (if c.claimPsychotropicCoordination then 12 else 0)
    some ⟨adjusted + 5 * extra⟩
  else none

-- 区分の優先順位、境界値、減算・加算・併算定禁止の検証。
example : category { anxiolytics := 3, oralDrugs := 7 } =
    .psychotropicPolypharmacy := by decide
example : category { anxiolytics := 2, hypnotics := 2 } =
    .psychotropicPolypharmacy := by decide
example : category { antidepressants := 3 } = .psychotropicPolypharmacy := by decide
example : category { antipsychotics := 3 } = .psychotropicPolypharmacy := by decide
example : category { oralDrugs := 7 } = .otherPolypharmacyOrLongTerm := by decide
example : category { oralDrugs := 7, regionalComprehensiveCareAddition := true } =
    .ordinary := by decide
example : category { anxietyOrInsomnia := true, designatedDrugForAtLeastOneYear := true } =
    .otherPolypharmacyOrLongTerm := by decide
example : category { anxietyOrInsomnia := true, designatedDrugForAtLeastOneYear := true,     experiencedDoctorOrPsychiatristAdviceOrEquivalent := true } = .ordinary := by decide
example : category { oralDrugs := 6 } = .ordinary := by decide
example : (List.map (fun c => basePoints c false)
    [.psychotropicPolypharmacy, .otherPolypharmacyOrLongTerm, .ordinary]) =
    [20, 32, 60] := by decide
example : (List.map (fun c => basePoints c true)
    [.psychotropicPolypharmacy, .otherPolypharmacyOrLongTerm, .ordinary]) =
    [18, 29, 42] := by decide
example : reduced { initialNote2Or3OrOutpatientNote2Or3 := true,     nonExemptDrugForAtLeast30Days := true, refill := true, daysPerRefillUse := 29 } =
    false := by decide
example : reduced { initialNote2Or3OrOutpatientNote2Or3 := true,     nonExemptDrugForAtLeast30Days := true, refill := true, daysPerRefillUse := 30 } =
    true := by decide
example : specificDiseasePoints (.hospital 199)
    { designatedPrimaryDisease := true, prescribedDaysIncludingRefills := 28 } = 56 := by decide
example : specificDiseasePoints (.hospital 200)
    { designatedPrimaryDisease := true, prescribedDaysIncludingRefills := 28 } = 0 := by decide
example : specificDiseasePoints .clinic { designatedPrimaryDisease := true,     prescribedDaysIncludingRefills := 28, specificDiseaseClaimsThisMonth := 1 } = 0 := by decide
example : antineoplasticPoints (.hospital 200) { notifiedAntineoplasticFacilityStandard := true,     writtenExplanationAtTreatmentStart := true, antineoplasticPrescription := true } = 70 := by decide
example : points { facility := .clinic } = none := by decide
example : points { facility := .clinic, issuedForInsurancePharmacy := true } =
    some ⟨300⟩ := by decide
example : points { facility := .clinic, issuedForInsurancePharmacy := true,     medication := { oralDrugs := 7 },     relationship := { issuedEnoughPrescriptionsInLastThreeMonths := true,       specialDispensingBasicFeeAAndConcentratedReception := true,       specialRelationshipIncludingRealEstate := true },     longPrescription := { initialNote2Or3OrOutpatientNote2Or3 := true,       nonExemptDrugForAtLeast30Days := true }, additions := { ageUnderThree := true } } =
    some ⟨73⟩ := by decide -- 29 × 40% + 3 = 14.6点
example : points { facility := .clinic, issuedForInsurancePharmacy := true,     claimPsychotropicCoordination := true, additions := {
      previouslyPrescribedPsychotropics := true, comprehensiveEvaluationAndAdjustment := true,       psychotropicTypesOrDoseDecreased := true, pharmacistInstructedToCheckSymptomChanges := true,       claimsA250ThisMonth := true } } = none := by decide

example : specificDiseasePoints .clinic
    { designatedPrimaryDisease := true, prescribedDaysIncludingRefills := 27 } = 0 := by decide
example : specificDiseasePoints .clinic
    { designatedPrimaryDisease := true, prescribedDaysIncludingRefills := 28,
      inpatient := true } = 0 := by decide
example : genericNamePoints
    { genericNameFacilityStandard := true, genericName := .category1 } = 8 := by decide
example : genericNamePoints
    { genericNameFacilityStandard := true, genericName := .category2 } = 6 := by decide
example : genericNamePoints { genericName := .category1 } = 0 := by decide
example : substitutesPoints
    { issuedEnoughPrescriptionsInLastThreeMonths := true,
      specialDispensingBasicFeeAAndConcentratedReception := true } = false := by decide
example : points
    { facility := .clinic, issuedForInsurancePharmacy := true,
      claimPsychotropicCoordination := true,
      additions := {
        previouslyPrescribedPsychotropics := true,
        comprehensiveEvaluationAndAdjustment := true,
        psychotropicTypesOrDoseDecreased := true,
        pharmacistInstructedToCheckSymptomChanges := true } } = some ⟨360⟩ := by decide
example : points
    { facility := .clinic, issuedForInsurancePharmacy := true,
      claimPsychotropicCoordination := true,
      additions := {
        previouslyPrescribedPsychotropics := true,
        comprehensiveEvaluationAndAdjustment := true,
        psychotropicTypesOrDoseDecreased := true,
        pharmacistInstructedToCheckSymptomChanges := true,
        claimsB008_2ThisMonth := true } } = none := by decide
example : psychotropicCoordinationEligible
    { previouslyPrescribedPsychotropics := true,
      comprehensiveEvaluationAndAdjustment := true,
      psychotropicTypesOrDoseDecreased := true,
      pharmacistInstructedToCheckSymptomChanges := true,
      psychotropicCoordinationClaimsThisMonth := 1 } = false := by decide

end PrescriptionFee

end MedicalFee
end Sanri
