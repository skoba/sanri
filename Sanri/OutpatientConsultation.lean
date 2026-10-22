import Sanri.RevisitConsultation

namespace Sanri.MedicalFee.OutpatientConsultation

/-! Ａ００２ 外来診療料・注１〜11。
大臣指定の施設基準・患者・時間帯、検体検査通則３の要件と点数は入力とする。
月内回数は同一患者・同一医療機関について呼出元が管理する。 -/

abbrev Institution := InitialConsultation.Institution
abbrev Hospital := InitialConsultation.Hospital
abbrev Visit := RevisitConsultation.Visit
abbrev Mode := InitialConsultation.Mode

def eligibleInstitution : Institution → Bool
  | .clinic => false
  | .hospital h => decide (200 ≤ h.generalBeds)

/-- 注２。一般病床数の対象判定は注１として別に行う。 -/
def note2Hospital (h : Hospital) : Bool :=
  h.advancedTreatment || h.regionalSupport ||
    (h.outpatientFunctionReporting && h.prefecturePublishedCoreHospital)

/-- 注３。注２の病院を除き、許可病床400床以上。 -/
def note3Hospital (h : Hospital) : Bool :=
  decide (400 ≤ h.permittedBeds) && !note2Hospital h

structure Reduction where
  lowWrittenReferralRatioEtc : Bool := false
  designatedPatient : Bool := false
  settlementRateStandard : Bool := false
  deriving DecidableEq, Repr

/-- 処方箋料注２から参照する注２・３の適用条件。注４とは分ける。 -/
def note2Or3Applies (i : Institution) (r : Reduction) : Bool :=
  match i with
  | .clinic => false
  | .hospital h => eligibleInstitution i && (note2Hospital h || note3Hospital h) &&
      r.lowWrittenReferralRatioEtc && r.designatedPatient

def reduced (i : Institution) (r : Reduction) : Bool :=
  note2Or3Applies i r || r.settlementRateStandard

def generalRuleExceptions (v : Visit) : ConsultationGeneralRules.Exceptions :=
  { outpatientNote5 := RevisitConsultation.secondDepartment v }

def basePoints (isReduced online second : Bool) : Nat :=
  if second then (if isReduced then 29 else 39)
  else if isReduced then 57
  else if online then 76 else 77

/-- 面積を非負有理数（平方センチメートル）で表し、境界で丸めない。 -/
structure Area where
  numerator : Nat
  denominator : Nat
  positiveDenominator : 0 < denominator
  deriving DecidableEq, Repr

def Area.below (a : Area) (limit : Nat) : Bool :=
  decide (a.numerator < limit * a.denominator)

inductive FecalTest where
  | calprotectin
  | otherD003
  deriving DecidableEq, Repr

inductive BloodTest where
  | hemoglobinA1c
  | thymidineKinaseActivity
  | terminalDeoxynucleotidylTransferase
  | boneMarrowPicture
  | hematopoieticTumorCellAntigenSeries
  | otherD005
  deriving DecidableEq, Repr

/-- コードの範囲や各項目への所属は呼出元で確認する。
「ホ 削除」に対応する処置は定義しない。 -/
inductive Service where
  | urineD000ThroughD002_2
  | fecalD003 (test : FecalTest)
  | bloodD005 (test : BloodTest)
  | woundCare (area : Area)
  | dermatologicalOintmentCare (area : Area)
  | bladderIrrigation
  | vaginalIrrigation
  | eyeTreatment
  | eyelashRemoval
  | earTreatment
  | eustachianTubeTreatment
  | nasalTreatment
  | oralOrPharyngealTreatment
  | indirectLaryngoscopicTreatment
  | nebulizer
  | ultrasonicNebulizer
  | indirectTraction
  | antiInflammatoryAnalgesicTreatment
  | other
  deriving DecidableEq, Repr

/-- 注６本文の包括範囲。false は別算定の可否を保証しない。 -/
def includedByNote6 : Service → Bool
  | .urineD000ThroughD002_2 => true
  | .fecalD003 .otherD003 => true
  | .fecalD003 .calprotectin => false
  | .bloodD005 .otherD005 => true
  | .bloodD005 _ => false
  | .woundCare area => area.below 500
  | .dermatologicalOintmentCare area => !area.below 100 && area.below 500
  | .bladderIrrigation | .vaginalIrrigation | .eyeTreatment | .eyelashRemoval
  | .earTreatment | .eustachianTubeTreatment | .nasalTreatment | .oralOrPharyngealTreatment
  | .indirectLaryngoscopicTreatment | .nebulizer | .ultrasonicNebulizer | .indirectTraction
  | .antiInflammatoryAnalgesicTreatment => true
  | .other => false

structure Additions where
  /-- 注６ただし書。通則３の要件・点数は当該仕様で判定して入力する。 -/
  specimenTestGeneralRule3Eligible : Bool := false
  specimenTestGeneralRule3Points : Nat := 0
  electronicInformationNotified : Bool := false
  electronicInformationClaimsThisMonth : Nat := 0
  nurseRemoteAssistanceNotified : Bool := false
  patientWithNurseEtc : Bool := false
  deriving DecidableEq, Repr

structure Context where
  institution : Institution
  insuranceMedicalInstitution : Bool := true
  revisitPerformed : Bool := true
  mode : Mode := .inPerson
  telemedicineStandardNotified : Bool := false
  reduction : Reduction := {}
  visit : Visit := .ordinary
  status : ConsultationGeneralRules.PatientStatus := .outpatient
  ageYears : Nat := 20
  time : InitialConsultation.Time := {}
  timeStandards : InitialConsultation.TimeStandards := {}
  additions : Additions := {}
  deriving DecidableEq, Repr

structure Breakdown where
  specimenTest : Nat := 0
  infant : Nat := 0
  time : Nat := 0
  electronic : Nat := 0
  nurseRemoteAssistance : Nat := 0
  deriving DecidableEq, Repr

def Breakdown.total (b : Breakdown) : Nat :=
  b.specimenTest + b.infant + b.time + b.electronic + b.nurseRemoteAssistance

/-- 注５では注６ただし書・注７〜11の加算をすべて除外する。
検査・処置の包括自体は、２つ目の診療科でも維持する。 -/
def additionBreakdown (c : Context) : Breakdown :=
  if RevisitConsultation.secondDepartment c.visit then {} else
    let underSix := decide (c.ageYears < 6)
    let ta := InitialConsultation.timeAddition c.timeStandards c.time underSix
    { specimenTest := if c.additions.specimenTestGeneralRule3Eligible
        then c.additions.specimenTestGeneralRule3Points else 0
      infant := if underSix && decide (ta = .none) then 38 else 0
      time := RevisitConsultation.timePoints ta underSix
      electronic := if c.additions.electronicInformationNotified &&
        decide (c.additions.electronicInformationClaimsThisMonth = 0) then 2 else 0
      nurseRemoteAssistance := if decide (c.mode = .telemedicine) &&
        c.additions.nurseRemoteAssistanceNotified && c.additions.patientWithNurseEtc then 50 else 0 }

/-- 通則３。注８・９のみ入院中にも別算定する。 -/
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

def Assessment.total (a : Assessment) : Nat := a.base + a.additions.total

def assess (c : Context) : Option Assessment :=
  if c.insuranceMedicalInstitution && c.revisitPerformed && eligibleInstitution c.institution &&
      RevisitConsultation.billableVisit c.visit &&
      (decide (c.mode = .inPerson) || c.telemedicineStandardNotified) then
    let base := basePoints (reduced c.institution c.reduction) (decide (c.mode = .telemedicine))
      (RevisitConsultation.secondDepartment c.visit)
    let extra := additionBreakdown c
    let outpatient := decide (c.status = .outpatient)
    some {
      base := if outpatient then base else 0
      additions := separatelyBillableAdditions c.status extra
      includedBase := if outpatient then 0 else base
      includedAdditions := includedAdditions c.status extra }
  else none

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-- 有効な外来診療料の算定における注６の包括対象。
none は外来診療料の対象外。some false は「注６による包括ではない」の意。 -/
def serviceIncluded (c : Context) (s : Service) : Option Bool :=
  (assess c).map (fun _ => includedByNote6 s)

/-! 対象施設、置換点数、包括範囲、加算制限の検証。 -/
private def hospital : Hospital :=
  {
        permittedBeds := 400
        generalBeds := 200 }
private def ordinary : Context := {
        institution := .hospital hospital }
private def remote : Context :=
  { ordinary with
        mode := .telemedicine
        telemedicineStandardNotified := true }
private def lowReferral : Reduction :=
  {
        lowWrittenReferralRatioEtc := true
        designatedPatient := true }
private def allAdditions : Additions :=
  {
        specimenTestGeneralRule3Eligible := true
        specimenTestGeneralRule3Points := 10
        electronicInformationNotified := true
        nurseRemoteAssistanceNotified := true
        patientWithNurseEtc := true }

example : points ordinary = some 77 := by decide
example : points remote = some 76 := by decide
example : points { ordinary with
        institution := .clinic } = none := by decide
example : points { ordinary with
        insuranceMedicalInstitution := false } = none := by decide
example : points { ordinary with
        revisitPerformed := false } = none := by decide
example : points { ordinary with
        mode := .telemedicine } = none := by decide
example : points { ordinary with
        institution := .hospital { hospital with
          generalBeds := 199 } } = none := by decide
example : points { ordinary with
        institution := .hospital { hospital with
          generalBeds := 200 } } = some 77 := by decide
example : note2Hospital { hospital with
        advancedTreatment := true } = true := by decide
example : note2Hospital { hospital with
        regionalSupport := true } = true := by decide
example : note2Hospital { hospital with
        outpatientFunctionReporting := true } = false := by decide
example : note2Hospital { hospital with
        outpatientFunctionReporting := true
        prefecturePublishedCoreHospital := true } = true := by decide
example : note3Hospital { hospital with
        permittedBeds := 399 } = false := by decide
example : note3Hospital hospital = true := by decide
example : note3Hospital { hospital with
        regionalSupport := true } = false := by decide
example : points { ordinary with
        reduction := lowReferral } = some 57 := by decide
example : points { remote with
        reduction := lowReferral } = some 57 := by decide
example : points { ordinary with
        institution := .hospital { hospital with
          advancedTreatment := true }
        reduction := lowReferral } = some 57 := by decide
example : points { ordinary with
        reduction := { lowReferral with
          designatedPatient := false } } = some 77 := by decide
example : points { ordinary with
        institution := .hospital { hospital with
          permittedBeds := 399 }
        reduction := lowReferral } = some 77 := by decide
example : points { ordinary with
        reduction := {
          settlementRateStandard := true } } = some 57 := by decide
example : points { remote with
        reduction := {
          settlementRateStandard := true } } = some 57 := by decide
example : (List.map (fun (r, o, s) => basePoints r o s)
    [(false, false, false), (false, true, false), (true, false, false), (true, true, false),
     (false, false, true), (false, true, true), (true, false, true), (true, true, true)]) =
    [77, 76, 57, 57, 39, 39, 29, 29] := by decide
example : points { ordinary with
        visit := .anotherDepartment true true true 2 } = some 39 := by decide
example : points { remote with
        reduction := lowReferral
        visit := .anotherDepartment true true true 2
        ageYears := 5
        time := {
          holiday := true }
        additions := allAdditions } = some 29 := by decide
example : points { ordinary with
        visit := .anotherDepartment true true true 3 } = none := by decide
example : points { ordinary with
        visit := .anotherDepartment false true true 2 } = none := by decide
example : points { ordinary with
        visit := .anotherDepartment true false true 2 } = none := by decide
example : points { ordinary with
        visit := .anotherDepartment true true false 2 } = none := by decide
example : (generalRuleExceptions (.anotherDepartment true true true 2)).outpatientNote5 = true := rfl

example : includedByNote6 .urineD000ThroughD002_2 = true := rfl
example : includedByNote6 (.fecalD003 .otherD003) = true := rfl
example : includedByNote6 (.fecalD003 .calprotectin) = false := rfl
example : (List.map (fun t => includedByNote6 (.bloodD005 t))
    [.hemoglobinA1c, .thymidineKinaseActivity, .terminalDeoxynucleotidylTransferase,
     .boneMarrowPicture, .hematopoieticTumorCellAntigenSeries, .otherD005]) =
    [false, false, false, false, false, true] := by decide
example : (List.map (fun a => includedByNote6 (.woundCare a))
    [⟨99, 1, by decide⟩, ⟨100, 1, by decide⟩, ⟨999, 2, by decide⟩, ⟨500, 1, by decide⟩]) =
    [true, true, true, false] := by decide
example : (List.map (fun a => includedByNote6 (.dermatologicalOintmentCare a))
    [⟨199, 2, by decide⟩, ⟨100, 1, by decide⟩, ⟨999, 2, by decide⟩, ⟨500, 1, by decide⟩]) =
    [false, true, true, false] := by decide
example : (List.map includedByNote6
    [.bladderIrrigation, .vaginalIrrigation, .eyeTreatment, .eyelashRemoval, .earTreatment,
     .eustachianTubeTreatment, .nasalTreatment, .oralOrPharyngealTreatment,
     .indirectLaryngoscopicTreatment, .nebulizer, .ultrasonicNebulizer, .indirectTraction,
     .antiInflammatoryAnalgesicTreatment]).all id = true := by decide
example : includedByNote6 .other = false := rfl
example : serviceIncluded { ordinary with
        visit := .anotherDepartment true true true 2 }
    .urineD000ThroughD002_2 = some true := by decide
example : serviceIncluded ordinary (.fecalD003 .calprotectin) = some false := by decide
example : serviceIncluded { ordinary with
        institution := .clinic }
    .urineD000ThroughD002_2 = none := by decide

example : points { ordinary with
        ageYears := 5 } = some 115 := by decide
example : points { ordinary with
        ageYears := 6 } = some 77 := by decide
example : points { ordinary with
        ageYears := 5
        time := {
          withinDisplayedHours := false } } = some 212 := by decide
example : points { ordinary with
        time := {
          holiday := true } } = some 267 := by decide
example : points { ordinary with
        time := {
          minute := 1320 } } = some 497 := by decide
example : points { ordinary with
        ageYears := 5
        time := {
          holiday := true }
        timeStandards := {
          advertisesPediatrics := true } } = some 337 := by decide
example : points { ordinary with
        ageYears := 5
        time := {
          minute := 1320 }
        timeStandards := {
          advertisesPediatrics := true } } = some 667 := by decide
example : points { ordinary with
        time := {
          designatedEmergencyNight := true }
        timeStandards := {
          exclusivelyNightEmergencyInstitution := true } } = some 257 := by decide
example : points { ordinary with
        ageYears := 5
        time := {
          designatedEmergencyNight := true }
        timeStandards := {
          exclusivelyNightEmergencyInstitution := true } } = some 327 := by decide
example : points { ordinary with
        additions := {
          specimenTestGeneralRule3Eligible := true,
          specimenTestGeneralRule3Points := 10 } } =
    some 87 := by decide
example : points { ordinary with
        additions := {
          specimenTestGeneralRule3Points := 10 } } = some 77 := by decide
example : points { ordinary with
        additions := {
          electronicInformationNotified := true } } = some 79 := by decide
example : points { ordinary with
        additions := {
          electronicInformationNotified := true,
          electronicInformationClaimsThisMonth := 1 } } =
    some 77 := by decide
example : points { remote with
        additions := allAdditions } = some 138 := by decide
example : (additionBreakdown { ordinary with
        additions := allAdditions }).nurseRemoteAssistance = 0 := by decide
example : (additionBreakdown { remote with
        additions := { allAdditions with
          patientWithNurseEtc := false } }).nurseRemoteAssistance = 0 := by decide
example : points { ordinary with
        status := .inpatient } = some 0 := by decide
example : points { ordinary with
        status := .shortStaySurgeryBasicFeePatient
        additions := allAdditions
        time := {
          holiday := true } } = some 190 := by decide
example : (assess { remote with
        status := .inpatient }).map Assessment.includedBase = some 76 := by decide
example : (assess { remote with
        status := .inpatient,
        additions := allAdditions }).map
    (fun result => result.includedAdditions.total) = some 62 := by decide

theorem secondDepartment_noAdditions (c : Context)
    (h : RevisitConsultation.secondDepartment c.visit = true) :
    additionBreakdown c = {
        } := by simp [additionBreakdown, h]

theorem inpatient_onlyTimeAddition (b : Breakdown) :
    separatelyBillableAdditions .inpatient b = {
        time := b.time } := rfl

theorem scheduledBase_matchesGeneralBeds (i : Institution) :
    pointsAt (InitialConsultation.facility i) .outpatientConsultation =
      if eligibleInstitution i then some 77 else none := by
  cases i <;> simp [InitialConsultation.facility, pointsAt, eligibleInstitution]

theorem revisitAndOutpatient_areComplementary (i : Institution) :
    eligibleInstitution i = !RevisitConsultation.eligibleInstitution i := by
  cases i with
  | clinic => rfl
  | hospital h =>
    by_cases hg : h.generalBeds < 200
    · simp [eligibleInstitution, RevisitConsultation.eligibleInstitution, hg, Nat.not_le.mpr hg]
    · simp [eligibleInstitution, RevisitConsultation.eligibleInstitution, hg, Nat.le_of_not_gt hg]

end Sanri.MedicalFee.OutpatientConsultation
