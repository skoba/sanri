import Sanri.InitialConsultation
import Sanri.MedicalManagement

namespace Sanri.MedicalFee.SpecificDiseaseManagement

/-! Ｂ０００ 特定疾患療養管理料・注１〜５。
大臣指定の疾患・施設基準、暦による「１月以内」の判定は入力する。
算定済回数は同一患者・同一医療機関・同一月について呼出元が管理する。 -/

/-- 許可病床総数で区分する。一般病床数は用いない。 -/
def hospitalPoints (permittedBeds : Nat) (online : Bool) : Option Nat :=
  if permittedBeds < 100 then some (if online then 128 else 147)
  else if permittedBeds < 200 then some (if online then 76 else 87)
  else none

def scheduledPoints (facility : Facility) (online : Bool) : Option Nat :=
  match facility with
  | .clinic => some (if online then 196 else 225)
  | .hospital beds => hospitalPoints beds online
  | .hospitalWithGeneralBeds permittedBeds _ => hospitalPoints permittedBeds online

/-- 注２〜４の包括先。複数の条件を満たす場合も、根拠をすべて保持する。 -/
inductive InclusionSource where
  | initialConsultationFee
  | inpatientBasicFee
  | homeCareGuidanceManagementFee
  | dermatologicalSpecificDiseaseGuidanceManagementFee
  deriving DecidableEq, Repr

structure Inclusion where
  /-- Ａ０００を算定する初診当日。 -/
  initialFeeClaimedOnThisDay : Bool := false
  /-- Ａ０００を算定した初診の日から暦で１月以内。30日とは仮定しない。 -/
  withinOneMonthOfChargedInitialVisit : Bool := false
  inpatient : Bool := false
  /-- 退院の日から起算して暦で１月以内。 -/
  withinOneMonthOfDischarge : Bool := false
  /-- 「算定すべき」指導管理を受けているか。請求済みであることは要求しない。 -/
  receivingHomeCareGuidanceManagement : Bool := false
  receivingB001_8Management : Bool := false
  deriving DecidableEq, Repr

def inclusionSources (i : Inclusion) : List InclusionSource :=
  (if i.initialFeeClaimedOnThisDay || i.withinOneMonthOfChargedInitialVisit
    then [.initialConsultationFee] else []) ++
  (if i.inpatient || i.withinOneMonthOfDischarge then [.inpatientBasicFee] else []) ++
  (if i.receivingHomeCareGuidanceManagement then [.homeCareGuidanceManagementFee] else []) ++
  (if i.receivingB001_8Management
    then [.dermatologicalSpecificDiseaseGuidanceManagementFee] else [])

structure Context where
  facility : Facility
  insuranceMedicalInstitution : Bool := true
  facilityStandardMet : Bool := false
  designatedPrimaryDisease : Bool := false
  necessaryManagementUnderTreatmentPlan : Bool := false
  claimsThisMonth : Nat := 0
  mode : InitialConsultation.Mode := .inPerson
  telemedicineStandardNotified : Bool := false
  inclusion : Inclusion := {}
  materials : List MedicalManagement.MaterialCharge := []
  remote : MedicalManagement.RemoteCare := {}
  deriving DecidableEq, Repr

/-- 通則への接続。基本点数・項目・情報通信機器の使用はＢ０００の判定から設定する。 -/
def generalRulesContext (c : Context) (base : Nat) : MedicalManagement.Context :=
  { facility := c.facility
    insuranceMedicalInstitution := c.insuranceMedicalInstitution
    item := .specificDiseaseManagement
    section1Eligible := true
    section1Points := base
    materials := c.materials
    remote := { c.remote with
      usingInformationCommunicationEquipment := decide (c.mode = .telemedicine) } }

inductive Assessment where
  /-- 当該管理費用の包括先。材料等の別算定可否はこの結果から導かない。 -/
  | included (sources : List InclusionSource)
  | separatelyBillable (details : MedicalManagement.Assessment)
  deriving DecidableEq, Repr

def Assessment.total : Assessment → Nat
  | .included _ => 0
  | .separatelyBillable details => details.total

/-- 第３回以降の別算定、対象外施設、要件不足は none。
包括対象はその根拠を返し、月２回の別算定には数えない。 -/
def assess (c : Context) : Option Assessment := do
  let base ← scheduledPoints c.facility (decide (c.mode = .telemedicine))
  if !(c.insuranceMedicalInstitution && c.facilityStandardMet && c.designatedPrimaryDisease &&
      c.necessaryManagementUnderTreatmentPlan &&
      (decide (c.mode = .inPerson) || c.telemedicineStandardNotified)) then none
  else
    let sources := inclusionSources c.inclusion
    if !sources.isEmpty then some (.included sources)
    else if c.claimsThisMonth < 2 then
      let details ← MedicalManagement.assess (generalRulesContext c base)
      some (.separatelyBillable details)
    else none

/-- 包括対象は some 0、算定不可は none、別算定時は通則の材料・加算を含む合計。 -/
def points (c : Context) : Option Nat := (assess c).map Assessment.total

private def ordinary : Context :=
  { facility := .clinic
    facilityStandardMet := true
    designatedPrimaryDisease := true
    necessaryManagementUnderTreatmentPlan := true }
private def online : Context :=
  { ordinary with
    mode := .telemedicine
    telemedicineStandardNotified := true }

example : points ordinary = some 225 := by decide
example : points online = some 196 := by decide
example : (List.map (fun beds => scheduledPoints (.hospital beds) false) [99, 100, 199, 200]) =
    [some 147, some 87, some 87, none] := by decide
example : (List.map (fun beds => scheduledPoints (.hospital beds) true) [99, 100, 199, 200]) =
    [some 128, some 76, some 76, none] := by decide
example : points { ordinary with facility := .hospitalWithGeneralBeds 200 50 } = none := by decide
example : points { ordinary with facility := .hospitalWithGeneralBeds 100 50 } = some 87 := by decide
example : points { ordinary with insuranceMedicalInstitution := false } = none := by decide
example : points { ordinary with facilityStandardMet := false } = none := by decide
example : points { ordinary with designatedPrimaryDisease := false } = none := by decide
example : points { ordinary with necessaryManagementUnderTreatmentPlan := false } = none := by decide
example : points { online with telemedicineStandardNotified := false } = none := by decide
example : points { ordinary with claimsThisMonth := 1 } = some 225 := by decide
example : points { ordinary with claimsThisMonth := 2 } = none := by decide
example : points { ordinary with claimsThisMonth := 3 } = none := by decide
example : assess { ordinary with inclusion := { initialFeeClaimedOnThisDay := true } } =
    some (.included [.initialConsultationFee]) := by decide
example : assess { ordinary with inclusion := { withinOneMonthOfChargedInitialVisit := true } } =
    some (.included [.initialConsultationFee]) := by decide
example : assess { ordinary with inclusion := { inpatient := true } } =
    some (.included [.inpatientBasicFee]) := by decide
example : assess { ordinary with inclusion := { withinOneMonthOfDischarge := true } } =
    some (.included [.inpatientBasicFee]) := by decide
example : assess { ordinary with inclusion := { receivingHomeCareGuidanceManagement := true } } =
    some (.included [.homeCareGuidanceManagementFee]) := by decide
example : assess { ordinary with inclusion := { receivingB001_8Management := true } } =
    some (.included [.dermatologicalSpecificDiseaseGuidanceManagementFee]) := by decide
example : points { ordinary with inclusion := { inpatient := true }, claimsThisMonth := 2 } =
    some 0 := by decide
example : inclusionSources {
    initialFeeClaimedOnThisDay := true
    inpatient := true
    receivingHomeCareGuidanceManagement := true
    receivingB001_8Management := true } =
    [.initialConsultationFee, .inpatientBasicFee, .homeCareGuidanceManagementFee,
     .dermatologicalSpecificDiseaseGuidanceManagementFee] := by decide
example : points { ordinary with materials := [⟨12⟩, ⟨23⟩] } = some 260 := by decide
example : points { online with
    remote := {
      electronicPrescriptionStandardNotified := true
      issuedStatutoryElectronicPrescription := true
      functionCooperationStandardNotified := true } } = some 256 := by decide
example : points { ordinary with
    remote := {
      usingInformationCommunicationEquipment := true
      electronicPrescriptionStandardNotified := true
      issuedStatutoryElectronicPrescription := true
      functionCooperationStandardNotified := true } } = some 225 := by decide
example : MedicalManagement.infectionEligibleItem .specificDiseaseManagement = false := rfl

theorem includedManagement_noSeparatePoints (c : Context) (sources : List InclusionSource)
    (h : assess c = some (.included sources)) : points c = some 0 := by
  simp [points, h, Assessment.total]

end Sanri.MedicalFee.SpecificDiseaseManagement
