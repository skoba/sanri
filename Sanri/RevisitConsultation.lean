import Sanri.InitialConsultation

namespace Sanri.MedicalFee.RevisitConsultation

/-! Ａ００１ 再診料・注１〜20。大臣指定の基準・患者区分は入力とする。
時刻・施設の詳細型は初診料と共有する。月内回数と３月に１回の制限期間内の回数は、
同一患者・同一医療機関について呼出元が記録する。 -/

abbrev Institution := InitialConsultation.Institution
abbrev Time := InitialConsultation.Time
abbrev TimeStandards := InitialConsultation.TimeStandards
abbrev TimeAddition := InitialConsultation.TimeAddition

/-- 注１は許可病床の総数ではなく一般病床数で判定する。 -/
def eligibleInstitution : Institution → Bool
  | .clinic => true
  | .hospital h => decide (h.generalBeds < 200)

/-- 注２は許可病床の総数で判定する。注１の対象施設であることは別に検査する。 -/
def settlementReduction (i : Institution) (standard : Bool) : Bool :=
  match i with
  | .clinic => false
  | .hospital h => decide (200 ≤ h.permittedBeds) && standard

inductive Visit where
  | ordinary
  | anotherDepartment (sameInstitution sameDay otherDisease : Bool) (ordinal : Nat)
  deriving DecidableEq, Repr

def secondDepartment : Visit → Bool
  | .ordinary => false
  | .anotherDepartment sameInstitution sameDay otherDisease ordinal =>
      sameInstitution && sameDay && otherDisease && decide (ordinal = 2)

def billableVisit : Visit → Bool
  | .ordinary => true
  | v => secondDepartment v

def generalRuleExceptions (v : Visit) : ConsultationGeneralRules.Exceptions :=
  { revisitNote3 := secondDepartment v }

def basePoints (isReduced second : Bool) : Nat :=
  match isReduced, second with
  | false, false => 76
  | true, false => 56
  | false, true => 39
  | true, true => 29

inductive Mode where
  | inPerson
  | telemedicine
  | telephoneAdvice
  deriving DecidableEq, Repr

inductive AdviceRequester where
  | patient
  | caregiver
  | other
  deriving DecidableEq, Repr

/-- 注５・６の時間帯判定は初診料と共通で、点数のみ異なる。 -/
def timePoints (a : TimeAddition) (underSix : Bool) : Nat :=
  match a with
  | .none => 0
  | .afterHours => if underSix then 135 else 65
  | .holiday => if underSix then 260 else 190
  | .deepNight => if underSix then 590 else 420
  | .emergencyNight => if underSix then 250 else 180
  | .pediatricNight => 135
  | .pediatricHoliday => 260
  | .pediatricDeepNight => 590

inductive AfterHoursSystemCategory where
  | none
  | category1
  | category2
  | category3
  | category4
  deriving DecidableEq, Repr

def afterHoursSystemPoints : AfterHoursSystemCategory → Nat
  | .none => 0
  | .category1 => 7
  | .category2 => 5
  | .category3 => 4
  | .category4 => 2

inductive ComprehensiveCategory where
  | none
  | category1
  | category2
  deriving DecidableEq, Repr

inductive ComprehensivePatient where
  | notDesignated
  | dementiaEtc
  | otherChronicDiseaseEtc
  deriving DecidableEq, Repr

def comprehensivePoints : ComprehensiveCategory → ComprehensivePatient → Nat
  | .category1, .dementiaEtc => 38
  | .category1, .otherChronicDiseaseEtc => 28
  | .category2, .dementiaEtc => 31
  | .category2, .otherChronicDiseaseEtc => 21
  | _, _ => 0

/-- 注８の計画的医学管理と、併施してはならない診療行為。 -/
structure OutpatientManagement where
  designatedPlannedMedicalManagement : Bool := false
  chronicPainManagement : Bool := false
  designatedTests : Bool := false
  rehabilitation : Bool := false
  psychiatricSpecializedTherapy : Bool := false
  procedures : Bool := false
  surgery : Bool := false
  anesthesia : Bool := false
  radiationTherapy : Bool := false
  deriving DecidableEq, Repr

def outpatientManagementEligible (m : OutpatientManagement) : Bool :=
  m.designatedPlannedMedicalManagement && !m.chronicPainManagement && !m.designatedTests &&
  !m.rehabilitation && !m.psychiatricSpecializedTherapy && !m.procedures && !m.surgery &&
  !m.anesthesia && !m.radiationTherapy

inductive OtherCare where
  | none
  | admittedToOtherHospital
  | admittedToGeriatricHealthFacility
  | continuingOtherOutpatientCare
  deriving DecidableEq, Repr

structure MedicationCoordination where
  otherCare : OtherCare := .none
  medicationUseAndHistoryProvided : Bool := false
  appropriateCooperation : Bool := false
  drugTypesReducedAtOtherFacility : Bool := false
  /-- 処方内容の情報提供を実際に受け、かつ指定期間内であったこと。
「１月」「３月」は暦による判定を入力し、30日・90日とは置き換えない。 -/
  receivedWithinOneMonthAfterDischarge : Bool := false
  receivedWithinThreeMonthsAfterInformation : Bool := false
  claimsInThreeMonthPeriod : Nat := 0
  deriving DecidableEq, Repr

def medicationCoordinationEligible (m : MedicationCoordination) : Bool :=
  let discharged := match m.otherCare with
    | .admittedToOtherHospital | .admittedToGeriatricHealthFacility => true
    | _ => false
  decide (m.otherCare ≠ .none) && m.medicationUseAndHistoryProvided &&
    m.appropriateCooperation && m.drugTypesReducedAtOtherFacility &&
    ((discharged && m.receivedWithinOneMonthAfterDischarge) ||
      m.receivedWithinThreeMonthsAfterInformation) && decide (m.claimsInThreeMonthPeriod = 0)

structure Additions where
  outpatientManagement : OutpatientManagement := {}
  afterHoursSystemNotified : Bool := false
  afterHoursSystemCategory : AfterHoursSystemCategory := .none
  statementFacilityStandard : Bool := false
  /-- 注11と注19は選択して請求できるようにする。 -/
  claimStatement : Bool := true
  comprehensiveNotified : Bool := false
  comprehensiveCategory : ComprehensiveCategory := .none
  comprehensivePatient : ComprehensivePatient := .notDesignated
  patientConsent : Bool := false
  necessaryGuidanceAndCare : Bool := false
  dataSubmissionNotified : Bool := false
  continuouslySubmitsClaimsAndCareData : Bool := false
  dataSubmissionClaimsThisMonth : Nat := 0
  medicationCoordination : MedicationCoordination := {}
  infectionControlNotified : Bool := false
  infectionControlClaimsThisMonth : Nat := 0
  infectiousSymptoms : Bool := false
  appropriateInfectionPrecautions : Bool := false
  feverResponseClaimsThisMonth : Nat := 0
  cooperationNotified : Bool := false
  cooperationClaimsThisMonth : Nat := 0
  surveillanceNotified : Bool := false
  surveillanceClaimsThisMonth : Nat := 0
  antimicrobialStewardshipNotified : Bool := false
  antimicrobialClaimsThisMonth : Nat := 0
  electronicInformationNotified : Bool := false
  electronicInformationClaimsThisMonth : Nat := 0
  claimElectronicInformation : Bool := true
  /-- 同時に別算定しようとするＡ０００注16。 -/
  claimsA000Note16 : Bool := false
  nurseRemoteAssistanceNotified : Bool := false
  patientWithNurseEtc : Bool := false
  deriving DecidableEq, Repr

structure Context where
  institution : Institution
  insuranceMedicalInstitution : Bool := true
  revisitPerformed : Bool := true
  mode : Mode := .inPerson
  telemedicineStandardNotified : Bool := false
  adviceRequester : AdviceRequester := .patient
  therapeuticAdviceRequested : Bool := false
  instructionsGiven : Bool := false
  settlementRateStandard : Bool := false
  visit : Visit := .ordinary
  status : ConsultationGeneralRules.PatientStatus := .outpatient
  ageYears : Nat := 20
  time : Time := {}
  timeStandards : TimeStandards := {}
  additions : Additions := {}
  deriving DecidableEq, Repr

/-- 注９の電話等は、注１の届出済み情報通信機器による再診と区別する。 -/
def performed (c : Context) : Bool :=
  match c.mode with
  | .inPerson => c.revisitPerformed
  | .telemedicine => c.revisitPerformed && c.telemedicineStandardNotified
  | .telephoneAdvice => decide (c.adviceRequester ≠ .other) &&
      c.therapeuticAdviceRequested && c.instructionsGiven

structure Breakdown where
  infant : Nat := 0
  time : Nat := 0
  nightEarlyMorning : Nat := 0
  outpatientManagement : Nat := 0
  afterHoursSystem : Nat := 0
  statement : Nat := 0
  comprehensive : Nat := 0
  dataSubmission : Nat := 0
  medicationCoordination : Nat := 0
  infectionControl : Nat := 0
  feverResponse : Nat := 0
  cooperation : Nat := 0
  surveillance : Nat := 0
  antimicrobial : Nat := 0
  electronic : Nat := 0
  nurseRemoteAssistance : Nat := 0
  deriving DecidableEq, Repr

def Breakdown.total (b : Breakdown) : Nat :=
  b.infant + b.time + b.nightEarlyMorning + b.outpatientManagement + b.afterHoursSystem +
  b.statement + b.comprehensive + b.dataSubmission + b.medicationCoordination +
  b.infectionControl + b.feverResponse + b.cooperation + b.surveillance + b.antimicrobial +
  b.electronic + b.nurseRemoteAssistance

/-- 注３の２科目、注９の電話等の除外を、加算ごとに適用する。
注14は電話等の除外一覧にないが、注12に該当する必要がある。 -/
def additionBreakdown (c : Context) : Breakdown :=
  let ordinaryDepartment := !secondDepartment c.visit
  let notPhone := decide (c.mode ≠ .telephoneAdvice)
  let outpatient := decide (c.status = .outpatient)
  let underSix := decide (c.ageYears < 6)
  let ta := InitialConsultation.timeAddition c.timeStandards c.time underSix
  let a := c.additions
  let isClinic := InitialConsultation.clinic c.institution
  let comprehensive := if ordinaryDepartment && notPhone && outpatient && isClinic &&
      a.comprehensiveNotified && a.patientConsent && a.necessaryGuidanceAndCare
    then comprehensivePoints a.comprehensiveCategory a.comprehensivePatient else 0
  let infection := ordinaryDepartment && notPhone && isClinic && a.infectionControlNotified
  { infant := if ordinaryDepartment && underSix && decide (ta = .none) then 38 else 0
    time := if ordinaryDepartment then timePoints ta underSix else 0
    nightEarlyMorning := if ordinaryDepartment then
      InitialConsultation.nightEarlyMorningPoints c.institution c.timeStandards c.time ta else 0
    outpatientManagement := if ordinaryDepartment && notPhone && outpatient &&
      outpatientManagementEligible a.outpatientManagement then 52 else 0
    afterHoursSystem := if ordinaryDepartment && isClinic && a.afterHoursSystemNotified
      then afterHoursSystemPoints a.afterHoursSystemCategory else 0
    statement := if ordinaryDepartment && isClinic && a.statementFacilityStandard && a.claimStatement
      then 1 else 0
    comprehensive := comprehensive
    dataSubmission := if decide (comprehensive > 0) && a.dataSubmissionNotified &&
      a.continuouslySubmitsClaimsAndCareData && decide (a.dataSubmissionClaimsThisMonth = 0)
      then 10 else 0
    medicationCoordination := if decide (comprehensive > 0) &&
      medicationCoordinationEligible a.medicationCoordination then 30 else 0
    infectionControl := if infection && decide (a.infectionControlClaimsThisMonth = 0) then 6 else 0
    feverResponse := if infection && a.infectiousSymptoms && a.appropriateInfectionPrecautions &&
      decide (a.feverResponseClaimsThisMonth = 0) then 20 else 0
    cooperation := if infection && a.cooperationNotified && decide (a.cooperationClaimsThisMonth = 0)
      then 3 else 0
    surveillance := if infection && a.surveillanceNotified && decide (a.surveillanceClaimsThisMonth = 0)
      then 1 else 0
    antimicrobial := if infection && a.antimicrobialStewardshipNotified &&
      decide (a.antimicrobialClaimsThisMonth = 0) then 5 else 0
    electronic := if ordinaryDepartment && notPhone && a.electronicInformationNotified &&
      a.claimElectronicInformation && decide (a.electronicInformationClaimsThisMonth = 0) then 2 else 0
    nurseRemoteAssistance := if ordinaryDepartment && decide (c.mode = .telemedicine) &&
      a.nurseRemoteAssistanceNotified && a.patientWithNurseEtc then 50 else 0 }

/-- 通則３により入院中・短期滞在の再診では注５・６のみ別算定する。 -/
def separatelyBillableAdditions (status : ConsultationGeneralRules.PatientStatus)
    (b : Breakdown) : Breakdown :=
  match status with
  | .outpatient => b
  | _ => { time := b.time }

def includedAdditions (status : ConsultationGeneralRules.PatientStatus)
    (b : Breakdown) : Breakdown :=
  match status with
  | .outpatient => {}
  | _ => { b with time := 0 }

structure Assessment where
  base : Nat
  additions : Breakdown
  includedBase : Nat := 0
  includedAdditions : Breakdown := {}
  deriving DecidableEq, Repr

/-- 入院費用に包括される部分を除いた別算定点数。 -/
def Assessment.total (a : Assessment) : Nat := a.base + a.additions.total

def assess (c : Context) : Option Assessment :=
  let b := additionBreakdown c
  let extra := separatelyBillableAdditions c.status b
  if c.insuranceMedicalInstitution && eligibleInstitution c.institution && performed c &&
      billableVisit c.visit &&
      !(decide (extra.statement > 0) &&
        (decide (extra.electronic > 0) || c.additions.claimsA000Note16)) then
    let base := basePoints (settlementReduction c.institution c.settlementRateStandard)
      (secondDepartment c.visit)
    let outpatient := decide (c.status = .outpatient)
    some {
      base := if outpatient then base else 0
      additions := extra
      includedBase := if outpatient then 0 else base
      includedAdditions := includedAdditions c.status b }
  else none

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-- 処方箋料区分２で使う地域包括診療加算の算定有無。 -/
def claimsRegionalComprehensiveCare (c : Context) : Bool :=
  match assess c with
  | some result => decide (result.additions.comprehensive > 0)
  | none => false

/-! 点数、境界条件、除外・包括・回数制限の検証。 -/
private def ordinary : Context := {
          institution := .clinic }
private def phone : Context :=
  { ordinary with
          mode := .telephoneAdvice
          therapeuticAdviceRequested := true
          instructionsGiven := true }
private def comprehensive : Additions :=
  {
          comprehensiveNotified := true
          comprehensiveCategory := .category1
          comprehensivePatient := .dementiaEtc
          patientConsent := true
          necessaryGuidanceAndCare := true }
private def coordination : MedicationCoordination :=
  {
          otherCare := .admittedToOtherHospital
          medicationUseAndHistoryProvided := true
          appropriateCooperation := true
          drugTypesReducedAtOtherFacility := true
          receivedWithinOneMonthAfterDischarge := true }
private def infection : Additions :=
  {
          infectionControlNotified := true
          infectiousSymptoms := true
          appropriateInfectionPrecautions := true
          cooperationNotified := true
          surveillanceNotified := true
          antimicrobialStewardshipNotified := true }

example : points ordinary = some 76 := by decide
example : points { ordinary with
          insuranceMedicalInstitution := false } = none := by decide
example : points { ordinary with
          revisitPerformed := false } = none := by decide
example : eligibleInstitution (.hospital ⟨400, 199, false, false, false, false, false⟩) = true := by decide
example : eligibleInstitution (.hospital ⟨400, 200, false, false, false, false, false⟩) = false := by decide
example : points { ordinary with
          institution := .hospital ⟨400,
          199,
          false,
          false,
          false,
          false,
          false⟩
          settlementRateStandard := true } = some 56 := by decide
example : points { ordinary with
          institution := .hospital ⟨199,
          199,
          false,
          false,
          false,
          false,
          false⟩
          settlementRateStandard := true } = some 76 := by decide
example : points { ordinary with
          institution := .hospital ⟨400,
          200,
          false,
          false,
          false,
          false,
          false⟩
          settlementRateStandard := true } = none := by decide
example : points { ordinary with
          mode := .telemedicine } = none := by decide
example : points { ordinary with
          mode := .telemedicine
          telemedicineStandardNotified := true } = some 76 := by decide
example : (List.map (fun (r, s) => basePoints r s)
    [(false, false), (true, false), (false, true), (true, true)]) = [76, 56, 39, 29] := by decide
example : points { ordinary with
          visit := .anotherDepartment true true true 2
          ageYears := 2
          time := {
            holiday := true }
          additions := infection } = some 39 := by decide
example : points { ordinary with
          visit := .anotherDepartment true true true 3 } = none := by decide
example : points { ordinary with
          visit := .anotherDepartment true false true 2 } = none := by decide
example : (generalRuleExceptions (.anotherDepartment true true true 2)).revisitNote3 = true := rfl

example : points { ordinary with
          ageYears := 5 } = some 114 := by decide
example : points { ordinary with
          ageYears := 6 } = some 76 := by decide
example : (List.map (fun a => timePoints a false)
    [.afterHours, .holiday, .deepNight, .emergencyNight]) = [65, 190, 420, 180] := by decide
example : (List.map (fun a => timePoints a true)
    [.afterHours, .holiday, .deepNight, .emergencyNight]) = [135, 260, 590, 250] := by decide
example : points { ordinary with
          ageYears := 5
          time := {
            holiday := true } } = some 336 := by decide
example : points { ordinary with
          ageYears := 5
          time := {
            holiday := true }
          timeStandards := {
            advertisesPediatrics := true,
            nightEarlyMorningClinicStandard := true } } =
    some 336 := by decide
example : points { ordinary with
          time := {
            minute := 1080 }
          timeStandards := {
            nightEarlyMorningClinicStandard := true } } = some 126 := by decide
example : points { ordinary with
          additions := {
            outpatientManagement := {
              designatedPlannedMedicalManagement := true } } } =
    some 128 := by decide
example : (List.map outpatientManagementEligible
    [{
          designatedPlannedMedicalManagement := true,
          chronicPainManagement := true },
     {
          designatedPlannedMedicalManagement := true,
          designatedTests := true },
     {
          designatedPlannedMedicalManagement := true,
          rehabilitation := true },
     {
          designatedPlannedMedicalManagement := true,
          psychiatricSpecializedTherapy := true },
     {
          designatedPlannedMedicalManagement := true,
          procedures := true },
     {
          designatedPlannedMedicalManagement := true,
          surgery := true },
     {
          designatedPlannedMedicalManagement := true,
          anesthesia := true },
     {
          designatedPlannedMedicalManagement := true,
          radiationTherapy := true }]) =
    [false, false, false, false, false, false, false, false] := by decide

example : points phone = some 76 := by decide
example : points { phone with
          adviceRequester := .caregiver } = some 76 := by decide
example : points { phone with
          adviceRequester := .other } = none := by decide
example : points { phone with
          instructionsGiven := false } = none := by decide
example : points { phone with
          therapeuticAdviceRequested := false } = none := by decide
example : (additionBreakdown { phone with
          additions := infection }).total = 0 := by decide
example : (additionBreakdown { phone with
          additions := comprehensive }).comprehensive = 0 := by decide
example : (additionBreakdown { phone with
          additions := {
            outpatientManagement := {
              designatedPlannedMedicalManagement := true } } }).total =
    0 := by decide
example : points { phone with
          additions := {
            afterHoursSystemNotified := true,
            afterHoursSystemCategory := .category1,
            statementFacilityStandard := true } } = some 84 := by decide
example : (List.map afterHoursSystemPoints [.category1, .category2, .category3, .category4]) =
    [7, 5, 4, 2] := by decide
example : (List.map (fun (c, p) => comprehensivePoints c p)
    [(.category1, .dementiaEtc), (.category1, .otherChronicDiseaseEtc),
     (.category2, .dementiaEtc), (.category2, .otherChronicDiseaseEtc)]) = [38, 28, 31, 21] := by decide
example : points { ordinary with
          additions := comprehensive } = some 114 := by decide
example : points { ordinary with
          additions := { comprehensive with
            patientConsent := false } } = some 76 := by decide
example : claimsRegionalComprehensiveCare { ordinary with
          additions := comprehensive } = true := by decide
example : (additionBreakdown { ordinary with
          additions := { comprehensive with
            dataSubmissionNotified := true
            continuouslySubmitsClaimsAndCareData := true } }).dataSubmission = 10 := by decide
example : (additionBreakdown { ordinary with
          additions := { comprehensive with
            dataSubmissionNotified := true
            continuouslySubmitsClaimsAndCareData := true
            dataSubmissionClaimsThisMonth := 1 } }).dataSubmission = 0 := by decide
example : (additionBreakdown { ordinary with
          additions := {
            dataSubmissionNotified := true,
            continuouslySubmitsClaimsAndCareData := true } }).dataSubmission =
    0 := by decide
example : medicationCoordinationEligible coordination = true := by decide
example : medicationCoordinationEligible { coordination with
          claimsInThreeMonthPeriod := 1 } = false := by decide
example : medicationCoordinationEligible { coordination with
          receivedWithinOneMonthAfterDischarge := false } = false := by decide
example : medicationCoordinationEligible { coordination with
          otherCare := .continuingOtherOutpatientCare } = false := by decide
example : medicationCoordinationEligible { coordination with
          otherCare := .continuingOtherOutpatientCare
          receivedWithinThreeMonthsAfterInformation := true } = true := by decide
example : medicationCoordinationEligible { coordination with
          otherCare := .admittedToGeriatricHealthFacility } = true := by decide
example : (additionBreakdown { ordinary with
          additions := { comprehensive with
            medicationCoordination := coordination } }).medicationCoordination =
    30 := by decide
example : (additionBreakdown { phone with
          additions := { comprehensive with
            medicationCoordination := coordination } }).medicationCoordination =
    0 := by decide
example : (additionBreakdown { ordinary with
          additions := infection }).total = 35 := by decide
example : (additionBreakdown { ordinary with
          additions := { infection with
            infectionControlClaimsThisMonth := 1
            feverResponseClaimsThisMonth := 1
            cooperationClaimsThisMonth := 1
            surveillanceClaimsThisMonth := 1
            antimicrobialClaimsThisMonth := 1 } }).total = 0 := by decide
example : (additionBreakdown { ordinary with
          additions := { infection with
            infectionControlNotified := false } }).total = 0 := by decide
example : points { ordinary with
          additions := {
            electronicInformationNotified := true } } = some 78 := by decide
example : points { ordinary with
          additions := {
            electronicInformationNotified := true,
            electronicInformationClaimsThisMonth := 1 } } =
    some 76 := by decide
example : points { ordinary with
          additions := {
            electronicInformationNotified := true,
            statementFacilityStandard := true } } = none := by decide
example : points { ordinary with
          additions := {
            electronicInformationNotified := true,
            statementFacilityStandard := true,
            claimStatement := false } } = some 78 := by decide
example : points { ordinary with
          additions := {
            electronicInformationNotified := true,
            statementFacilityStandard := true,
            claimElectronicInformation := false } } = some 77 := by decide
example : points { ordinary with
          additions := {
            statementFacilityStandard := true,
            claimsA000Note16 := true } } = none := by decide
example : points { ordinary with
          mode := .telemedicine
          telemedicineStandardNotified := true
          additions := {
            nurseRemoteAssistanceNotified := true,
            patientWithNurseEtc := true } } =
    some 126 := by decide
example : points { ordinary with
          additions := {
            nurseRemoteAssistanceNotified := true,
            patientWithNurseEtc := true } } =
    some 76 := by decide
example : points { phone with
          additions := {
            nurseRemoteAssistanceNotified := true,
            patientWithNurseEtc := true } } =
    some 76 := by decide

example : points { ordinary with
          status := .inpatient } = some 0 := by decide
example : points { ordinary with
          status := .shortStaySurgeryBasicFeePatient
          time := {
            holiday := true }
          additions := infection } = some 190 := by decide
example : (assess { ordinary with
          status := .inpatient }).map Assessment.includedBase = some 76 := by decide
example : points { ordinary with
          status := .inpatient
          visit := .anotherDepartment true true true 2
          time := {
            holiday := true } } = some 0 := by decide

theorem inpatient_onlyTimeAddition (b : Breakdown) :
    separatelyBillableAdditions .inpatient b = {
          time := b.time } := rfl

theorem shortStay_onlyTimeAddition (b : Breakdown) :
    separatelyBillableAdditions .shortStaySurgeryBasicFeePatient b = {
          time := b.time } := rfl

example : pointsAt (.hospitalWithGeneralBeds 400 199) .revisitConsultation = some 76 := by decide
example : pointsAt (.hospitalWithGeneralBeds 400 200) .revisitConsultation = none := by decide
example : InitialConsultation.facility (.hospital ⟨400, 199, false, false, false, false, false⟩) =
    .hospitalWithGeneralBeds 400 199 := rfl

theorem secondDepartment_noAdditions (c : Context) (h : secondDepartment c.visit = true) :
    additionBreakdown c = {} := by
  simp [additionBreakdown, h]

theorem scheduledBase_matchesGeneralBeds (i : Institution) :
    pointsAt (InitialConsultation.facility i) .revisitConsultation =
      if eligibleInstitution i then some 76 else none := by
  cases i <;> simp [InitialConsultation.facility, pointsAt, eligibleInstitution]

end Sanri.MedicalFee.RevisitConsultation
