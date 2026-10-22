import Sanri.MedicalFee

namespace Sanri.MedicalFee.InitialConsultation

/-! Ａ０００ 初診料・注１〜16。提示本文の範囲をモデル化する。
大臣指定の施設基準・患者・時間の詳細は入力とする。
月内算定済回数は同一患者・同一医療機関について呼出元が管理する。 -/

structure Hospital where
  permittedBeds : Nat
  generalBeds : Nat
  advancedTreatment : Bool := false
  regionalSupport : Bool := false
  outpatientFunctionReporting : Bool := false
  prefecturePublishedCoreHospital : Bool := false
  referralPriority : Bool := false
  deriving DecidableEq, Repr

inductive Institution where
  | clinic
  | hospital (details : Hospital)
  deriving DecidableEq, Repr

def facility : Institution → Facility
  | .clinic => .clinic
  | .hospital h => .hospitalWithGeneralBeds h.permittedBeds h.generalBeds

def smallInstitution : Institution → Bool
  | .clinic => true
  | .hospital h => decide (h.permittedBeds < 200)

def clinic : Institution → Bool
  | .clinic => true
  | .hospital _ => false

/-- 注２。特定機能病院には一般病床200床の制限を付けない。 -/
def note2Hospital (h : Hospital) : Bool :=
  h.advancedTreatment || (decide (200 ≤ h.generalBeds) &&
    (h.regionalSupport || (h.outpatientFunctionReporting && h.prefecturePublishedCoreHospital)))

/-- 注３。許可病床400床と一般病床200床を別々に判定する。 -/
def note3Hospital (h : Hospital) : Bool :=
  decide (400 ≤ h.permittedBeds) && decide (200 ≤ h.generalBeds) &&
    !h.advancedTreatment && !h.regionalSupport &&
    !(h.outpatientFunctionReporting && h.prefecturePublishedCoreHospital)

structure Reduction where
  lowWrittenReferralRatioEtc : Bool := false
  designatedPatient : Bool := false
  /-- 注４に定める妥結率の施設基準を満たす。 -/
  settlementRateStandard : Bool := false
  deriving DecidableEq, Repr

/-- 注２・３の適用を処方箋料注２などからも参照できるよう独立に定義。 -/
def note2Or3Applies (i : Institution) (r : Reduction) : Bool :=
  match i with
  | .clinic => false
  | .hospital h => (note2Hospital h || note3Hospital h) &&
      r.lowWrittenReferralRatioEtc && r.designatedPatient

def note4Applies (i : Institution) (r : Reduction) : Bool :=
  match i with
  | .clinic => false
  | .hospital h => decide (200 ≤ h.permittedBeds) && r.settlementRateStandard

def reduced (i : Institution) (r : Reduction) : Bool :=
  note2Or3Applies i r || note4Applies i r

inductive Mode where
  | inPerson
  | telemedicine
  deriving DecidableEq, Repr

/-- 注５。継続中の別傷病の初診は原則として新たな初診料を算定しない。 -/
inductive Visit where
  | first
  | otherDiseaseDuringOngoingCare
  | anotherDepartment
      (sameInstitution sameDay otherDisease newlyVisitedDepartment : Bool)
      (departmentOrdinal : Nat)
  deriving DecidableEq, Repr

def secondDepartment : Visit → Bool
  | .anotherDepartment sameInstitution sameDay otherDisease newlyVisitedDepartment ordinal =>
      sameInstitution && sameDay && otherDisease && newlyVisitedDepartment && decide (ordinal = 2)
  | _ => false

def billableVisit : Visit → Bool
  | .first => true
  | v => secondDepartment v

/-- 注５ただし書を通則１の例外入力に接続する。 -/
def generalRuleExceptions (v : Visit) : ConsultationGeneralRules.Exceptions :=
  { initialNote5Proviso := secondDepartment v }

def basePoints (isReduced online second : Bool) : Nat :=
  match isReduced, online, second with
  | false, false, false => 291
  | false, true, false => 253
  | true, false, false => 216
  | true, true, false => 188
  | false, false, true => 146
  | false, true, true => 127
  | true, false, true => 108
  | true, true, true => 94

structure Time where
  /-- 午前０時からの分数。 -/
  minute : Fin 1440 := 720
  saturday : Bool := false
  holiday : Bool := false
  withinDisplayedHours : Bool := true
  /-- 注７ただし書・注８それぞれの大臣指定時間帯に該当するか。 -/
  designatedEmergencyNight : Bool := false
  designatedPediatricNight : Bool := false
  deriving DecidableEq, Repr

def deepNight (t : Time) : Bool := decide (t.minute.val ≥ 1320 ∨ t.minute.val < 360)

inductive TimeAddition where
  | none
  | afterHours
  | holiday
  | deepNight
  | emergencyNight
  | pediatricNight
  | pediatricHoliday
  | pediatricDeepNight
  deriving DecidableEq, Repr

structure TimeStandards where
  exclusivelyNightEmergencyInstitution : Bool := false
  advertisesPediatrics : Bool := false
  nightEarlyMorningClinicStandard : Bool := false
  deriving DecidableEq, Repr

/-- 注７・８。深夜、休日、その他の時間帯の順に排他的に判定する。 -/
def timeAddition (s : TimeStandards) (t : Time) (underSix : Bool) : TimeAddition :=
  if s.exclusivelyNightEmergencyInstitution && t.designatedEmergencyNight then .emergencyNight
  else if s.advertisesPediatrics && !s.exclusivelyNightEmergencyInstitution &&
      underSix && t.withinDisplayedHours then
    if deepNight t then .pediatricDeepNight
    else if t.holiday then .pediatricHoliday
    else if t.designatedPediatricNight then .pediatricNight
    else .none
  else if deepNight t then .deepNight
  else if t.holiday then .holiday
  else if !t.withinDisplayedHours then .afterHours
  else .none

def timePoints (a : TimeAddition) (underSix : Bool) : Nat :=
  match a with
  | .none => 0
  | .afterHours => if underSix then 200 else 85
  | .holiday => if underSix then 365 else 250
  | .deepNight => if underSix then 695 else 480
  | .emergencyNight => if underSix then 345 else 230
  | .pediatricNight => 200
  | .pediatricHoliday => 365
  | .pediatricDeepNight => 695

/-- 注９。注７ただし書又は注８との重複を除外。 -/
def nightEarlyMorningPoints (i : Institution) (s : TimeStandards) (t : Time)
    (a : TimeAddition) : Nat :=
  let excluded := match a with
    | .emergencyNight | .pediatricNight | .pediatricHoliday | .pediatricDeepNight => true
    | _ => false
  let eveningStart := if t.saturday then 720 else 1080
  if clinic i && s.nightEarlyMorningClinicStandard && t.withinDisplayedHours && !excluded &&
      (t.holiday || deepNight t || decide (t.minute.val ≥ eveningStart ∨ t.minute.val < 480))
  then 50 else 0

inductive ElectronicInformationCategory where
  | none
  | category1
  | category2
  | category3
  deriving DecidableEq, Repr

structure Additions where
  functionEnhancementNotified : Bool := false
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
  /-- 紹介元病院。none は該当する紹介なし。 -/
  referralSource : Option Hospital := none
  electronicInformationNotified : Bool := false
  electronicInformationCategory : ElectronicInformationCategory := .none
  electronicInformationClaimsThisMonth : Nat := 0
  /-- 注16と併算定できないＡ００１注11の請求。 -/
  claimsA001Note11 : Bool := false
  deriving DecidableEq, Repr

/-- 注11本文の施設条件。月内回数制限は各加算について個別に判定する。 -/
def infectionFacilityEligible (i : Institution) (a : Additions) : Bool :=
  clinic i && a.infectionControlNotified

def referralSourceEligible (h : Hospital) : Bool :=
  h.advancedTreatment || (decide (200 ≤ h.generalBeds) &&
    (h.regionalSupport || h.referralPriority || decide (400 ≤ h.permittedBeds)))

def electronicPoints (a : Additions) : Nat :=
  if a.electronicInformationNotified && decide (a.electronicInformationClaimsThisMonth = 0) then
    match a.electronicInformationCategory with
    | .none => 0
    | .category1 => 15
    | .category2 => 9
    | .category3 => 4
  else 0

/-- 加算ごとの内訳。注５ただし書では全フィールドを０とする。 -/
structure Breakdown where
  infant : Nat := 0
  time : Nat := 0
  nightEarlyMorning : Nat := 0
  functionEnhancement : Nat := 0
  infectionControl : Nat := 0
  feverResponse : Nat := 0
  cooperation : Nat := 0
  surveillance : Nat := 0
  antimicrobial : Nat := 0
  referral : Nat := 0
  electronic : Nat := 0
  deriving DecidableEq, Repr

def Breakdown.total (b : Breakdown) : Nat :=
  b.infant + b.time + b.nightEarlyMorning + b.functionEnhancement + b.infectionControl +
  b.feverResponse + b.cooperation + b.surveillance + b.antimicrobial + b.referral + b.electronic

structure Context where
  institution : Institution
  insuranceMedicalInstitution : Bool := true
  initialConsultationPerformed : Bool := true
  mode : Mode := .inPerson
  telemedicineStandardNotified : Bool := false
  reduction : Reduction := {}
  visit : Visit := .first
  ageYears : Nat := 20
  time : Time := {}
  timeStandards : TimeStandards := {}
  additions : Additions := {}
  deriving DecidableEq, Repr

def additionBreakdown (c : Context) : Breakdown :=
  if secondDepartment c.visit then {} else
    let underSix := decide (c.ageYears < 6)
    let ta := timeAddition c.timeStandards c.time underSix
    let a := c.additions
    let infection := infectionFacilityEligible c.institution a
    { infant := if underSix && decide (ta = .none) then 75 else 0
      time := timePoints ta underSix
      nightEarlyMorning := nightEarlyMorningPoints c.institution c.timeStandards c.time ta
      functionEnhancement := if smallInstitution c.institution && a.functionEnhancementNotified
        then 80 else 0
      infectionControl := if infection && decide (a.infectionControlClaimsThisMonth = 0)
        then 6 else 0
      feverResponse := if infection && a.infectiousSymptoms && a.appropriateInfectionPrecautions &&
        decide (a.feverResponseClaimsThisMonth = 0) then 20 else 0
      cooperation := if infection && a.cooperationNotified && decide (a.cooperationClaimsThisMonth = 0)
        then 3 else 0
      surveillance := if infection && a.surveillanceNotified && decide (a.surveillanceClaimsThisMonth = 0)
        then 1 else 0
      antimicrobial := if infection && a.antimicrobialStewardshipNotified &&
        decide (a.antimicrobialClaimsThisMonth = 0) then 5 else 0
      referral := if smallInstitution c.institution &&
        (a.referralSource.any referralSourceEligible) then 60 else 0
      electronic := electronicPoints a }

structure Assessment where
  base : Nat
  additions : Breakdown
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Nat := a.base + a.additions.total

/-- 未届出の情報通信初診、注５本文の継続診療、３科目以降、注16の併算定を除外。
加算は入力要件に該当するものを算入する。算定しない加算はその入力を立てない。 -/
def assess (c : Context) : Option Assessment :=
  let extra := additionBreakdown c
  if c.insuranceMedicalInstitution && c.initialConsultationPerformed && billableVisit c.visit &&
      (decide (c.mode = .inPerson) || c.telemedicineStandardNotified) &&
      !(decide (extra.electronic > 0) && c.additions.claimsA001Note11) then
    let base := basePoints (reduced c.institution c.reduction)
      (decide (c.mode = .telemedicine)) (secondDepartment c.visit)
    some { base := base, additions := extra }
  else none

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-! 基本点数、境界値、加算の優先順位と制限の検証。 -/
example : (List.map (fun (r, o, s) => basePoints r o s)
    [(false, false, false), (false, true, false), (true, false, false), (true, true, false),
     (false, false, true), (false, true, true), (true, false, true), (true, true, true)]) =
    [291, 253, 216, 188, 146, 127, 108, 94] := by decide

example : note2Hospital {
        permittedBeds := 199,
        generalBeds := 199,
        advancedTreatment := true } = true := by decide
example : note2Hospital {
        permittedBeds := 200,
        generalBeds := 199,
        regionalSupport := true } = false := by decide
example : note2Hospital {
        permittedBeds := 200,
        generalBeds := 200,
        regionalSupport := true } = true := by decide
example : note2Hospital {
        permittedBeds := 200,
        generalBeds := 200,
        outpatientFunctionReporting := true } = false := by decide
example : note2Hospital {
        permittedBeds := 200,
        generalBeds := 200,
        outpatientFunctionReporting := true,
        prefecturePublishedCoreHospital := true } = true := by decide
example : note3Hospital {
        permittedBeds := 399,
        generalBeds := 200 } = false := by decide
example : note3Hospital {
        permittedBeds := 400,
        generalBeds := 199 } = false := by decide
example : note3Hospital {
        permittedBeds := 400,
        generalBeds := 200 } = true := by decide
example : note3Hospital {
        permittedBeds := 400,
        generalBeds := 200,
        regionalSupport := true } = false := by decide
example : note3Hospital {
        permittedBeds := 400,
        generalBeds := 200,
        outpatientFunctionReporting := true } = true := by decide
example : note4Applies (.hospital {
        permittedBeds := 199,
        generalBeds := 100 })
    {
        settlementRateStandard := true } = false := by decide
example : note4Applies (.hospital {
        permittedBeds := 200,
        generalBeds := 100 })
    {
        settlementRateStandard := true } = true := by decide
example : points {
        institution := .clinic } = some 291 := by decide
example : points {
        institution := .clinic,
        mode := .telemedicine } = none := by decide
example : points {
        institution := .clinic,
        mode := .telemedicine,
        telemedicineStandardNotified := true } = some 253 := by decide
example : points {
        institution := .hospital {
          permittedBeds := 400,
          generalBeds := 200 },
        reduction := {
          lowWrittenReferralRatioEtc := true,
          designatedPatient := true } } =
    some 216 := by decide
example : points {
        institution := .hospital {
          permittedBeds := 400,
          generalBeds := 200 },
        reduction := {
          lowWrittenReferralRatioEtc := true } } = some 291 := by decide
example : points {
        institution := .clinic,
        visit := .otherDiseaseDuringOngoingCare } = none := by decide
example : points {
        institution := .clinic,
        visit := .anotherDepartment true true true true 2,
        ageYears := 2,
        additions := {
          functionEnhancementNotified := true,
          electronicInformationNotified := true,
          electronicInformationCategory := .category1 } } = some 146 := by decide
example : points {
        institution := .clinic,
        visit := .anotherDepartment true true true true 3 } = none := by decide
example : points {
        institution := .clinic,
        visit := .anotherDepartment true false true true 2 } = none := by decide

theorem secondDepartment_noAdditions (c : Context) (h : secondDepartment c.visit = true) :
    additionBreakdown c = {
        } := by simp [additionBreakdown, h]

example : points {
        institution := .clinic,
        ageYears := 5 } = some 366 := by decide
example : points {
        institution := .clinic,
        ageYears := 6 } = some 291 := by decide
example : (List.map (fun n => deepNight {
        minute := n })
    [⟨359, by decide⟩, ⟨360, by decide⟩, ⟨1319, by decide⟩, ⟨1320, by decide⟩]) =
    [true, false, false, true] := by decide
example : (List.map (fun a => timePoints a false)
    [.afterHours, .holiday, .deepNight, .emergencyNight]) = [85, 250, 480, 230] := by decide
example : (List.map (fun a => timePoints a true)
    [.afterHours, .holiday, .deepNight, .emergencyNight]) = [200, 365, 695, 345] := by decide
example : points {
        institution := .clinic,
        ageYears := 5,
        time := {
          withinDisplayedHours := false } } = some 491 := by decide
example : timeAddition {
        } {
        minute := 1320,
        holiday := true } false = .deepNight := by decide
example : timeAddition {
        advertisesPediatrics := true }
    {
        holiday := true } true = .pediatricHoliday := by decide
example : timeAddition {
        advertisesPediatrics := true }
    {
        holiday := true,
        withinDisplayedHours := false } true = .holiday := by decide
example : timeAddition {
        advertisesPediatrics := true,
        exclusivelyNightEmergencyInstitution := true }
    {
        designatedEmergencyNight := true,
        designatedPediatricNight := true } true =
    .emergencyNight := by decide
example : nightEarlyMorningPoints .clinic {
        nightEarlyMorningClinicStandard := true }
    {
        minute := 1079 } .none = 0 := by decide
example : nightEarlyMorningPoints .clinic {
        nightEarlyMorningClinicStandard := true }
    {
        minute := 1080 } .none = 50 := by decide
example : nightEarlyMorningPoints .clinic {
        nightEarlyMorningClinicStandard := true }
    {
        minute := 720,
        saturday := true } .none = 50 := by decide
example : nightEarlyMorningPoints .clinic {
        nightEarlyMorningClinicStandard := true }
    {
        minute := 479 } .none = 50 := by decide
example : nightEarlyMorningPoints .clinic {
        nightEarlyMorningClinicStandard := true }
    {
        minute := 480 } .none = 0 := by decide
example : nightEarlyMorningPoints .clinic {
        nightEarlyMorningClinicStandard := true }
    {
        holiday := true } .pediatricHoliday = 0 := by decide
example : (additionBreakdown {
        institution := .hospital {
          permittedBeds := 200,
          generalBeds := 100 },
        additions := {
          functionEnhancementNotified := true,
          infectionControlNotified := true } }).total =
    0 := by decide
example : (additionBreakdown {
        institution := .clinic,
        additions := {
          infectionControlNotified := true,
          infectiousSymptoms := true,
          appropriateInfectionPrecautions := true,
          cooperationNotified := true,
          surveillanceNotified := true,
          antimicrobialStewardshipNotified := true } }).total =
    35 := by decide
example : (additionBreakdown {
        institution := .clinic,
        additions := {
          infectionControlNotified := true,
          infectionControlClaimsThisMonth := 1,
          infectiousSymptoms := true,
          appropriateInfectionPrecautions := true,
          feverResponseClaimsThisMonth := 1,
          cooperationNotified := true,
          cooperationClaimsThisMonth := 1,
          surveillanceNotified := true,
          surveillanceClaimsThisMonth := 1,
          antimicrobialStewardshipNotified := true,
          antimicrobialClaimsThisMonth := 1 } }).total =
    0 := by decide
example : (additionBreakdown {
        institution := .clinic,
        additions := {
          cooperationNotified := true,
          surveillanceNotified := true,
          antimicrobialStewardshipNotified := true,
          infectiousSymptoms := true,
          appropriateInfectionPrecautions := true } }).total = 0 := by decide
example : referralSourceEligible {
        permittedBeds := 100,
        generalBeds := 100,
        advancedTreatment := true } = true := by decide
example : referralSourceEligible {
        permittedBeds := 400,
        generalBeds := 199 } = false := by decide
example : (additionBreakdown {
        institution := .clinic,
        additions := {
          referralSource := some {
            permittedBeds := 400,
            generalBeds := 200 } } }).referral =
    60 := by decide
example : (List.map (fun k => electronicPoints {
        electronicInformationNotified := true,
        electronicInformationCategory := k }) [.category1, .category2, .category3]) = [15, 9, 4] := by decide
example : electronicPoints {
        electronicInformationNotified := true,
        electronicInformationCategory := .category1,
        electronicInformationClaimsThisMonth := 1 } = 0 := by decide
example : points {
        institution := .clinic,
        additions := {
          electronicInformationNotified := true,
          electronicInformationCategory := .category1,
          claimsA001Note11 := true } } = none := by decide
example : points {
        institution := .clinic,
        additions := {
          electronicInformationNotified := true,
          electronicInformationCategory := .category1 } } = some 306 := by decide


end Sanri.MedicalFee.InitialConsultation
