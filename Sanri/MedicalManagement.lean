import Sanri.MedicalFee

namespace Sanri.MedicalFee.MedicalManagement

/-! 第２章 特掲診療料 第１部 医学管理等 通則１〜８。
第１節の個別算定要件・点数、第３節の材料の所属と点数、参照先の施設基準は入力する。
回数・他区分の算定履歴は同一患者・同一医療機関・同一月について呼出元で管理する。 -/

/-- 通則３の対象８項目と、それ以外の第１節の医学管理等。 -/
inductive Item where
  | pediatricOutpatient -- 小児科外来診療料
  | outpatientRehabilitation -- 外来リハビリテーション診療料
  | outpatientRadiation -- 外来放射線照射診療料
  | comprehensiveCommunityCare -- 地域包括診療料（Ａ００１注12の加算とは別）
  | pediatricPrimaryCare -- 小児かかりつけ診療料
  | outpatientTumorChemotherapy -- 外来腫瘍化学療法診療料
  | emergencyLifeSavingManagement -- 救急救命管理料
  | postDischargeVisitGuidance -- 退院後訪問指導料
  | specificDiseaseManagement -- Ｂ０００ 特定疾患療養管理料
  | otherSection1
  deriving DecidableEq, Repr

def infectionEligibleItem : Item → Bool
  | .specificDiseaseManagement | .otherSection1 => false
  | _ => true

/-- 第３節の特定保険医療材料に該当し、実際に使用した材料の算定点数。
数量・単価・丸め等は第３節の仕様で解決済みの値とする。未使用の材料は含めない。 -/
structure MaterialCharge where
  section3Points : Nat
  deriving DecidableEq, Repr

/-- 通則３に掲げる、同月の外来感染対策向上加算の別算定を妨げる参照先。 -/
inductive OtherInfectionClaimSource where
  | a000Note11
  | a001Note15
  | part2GeneralRule5
  | i012Note14
  deriving DecidableEq, Repr

structure InfectionControl where
  /-- Ａ０００注11・Ａ００１注15に規定する基準に適合し届出済み。 -/
  standardNotified : Bool := false
  claimsThisMonth : Nat := 0
  otherSourcesThisMonth : List OtherInfectionClaimSource := []
  infectiousSymptoms : Bool := false
  appropriatePrecautions : Bool := false
  feverClaimsThisMonth : Nat := 0
  /-- 通則４〜６：参照先と同じ基準に適合し届出済み。 -/
  cooperationNotified : Bool := false
  cooperationClaimsThisMonth : Nat := 0
  surveillanceNotified : Bool := false
  surveillanceClaimsThisMonth : Nat := 0
  antimicrobialStewardshipNotified : Bool := false
  antimicrobialClaimsThisMonth : Nat := 0
  deriving DecidableEq, Repr

structure RemoteCare where
  usingInformationCommunicationEquipment : Bool := false
  electronicPrescriptionStandardNotified : Bool := false
  /-- 通則７に定義された法令に基づく電子処方箋を発行した。 -/
  issuedStatutoryElectronicPrescription : Bool := false
  electronicPrescriptionClaimsThisMonth : Nat := 0
  /-- Ａ２５４の注に規定する基準に適合し届出済み。 -/
  functionCooperationStandardNotified : Bool := false
  functionCooperationClaimsThisMonth : Nat := 0
  deriving DecidableEq, Repr

structure Context where
  facility : Facility
  insuranceMedicalInstitution : Bool := true
  item : Item
  /-- 第１節の当該区分の算定要件を満たしている。 -/
  section1Eligible : Bool := true
  section1Points : Nat
  materials : List MaterialCharge := []
  infection : InfectionControl := {}
  remote : RemoteCare := {}
  deriving DecidableEq, Repr

def isClinic : Facility → Bool
  | .clinic => true
  | _ => false

def infectionEligible (c : Context) : Bool :=
  isClinic c.facility && infectionEligibleItem c.item && c.infection.standardNotified &&
  c.infection.otherSourcesThisMonth.isEmpty

structure Breakdown where
  infectionControl : Nat := 0
  feverResponse : Nat := 0
  cooperation : Nat := 0
  surveillance : Nat := 0
  antimicrobial : Nat := 0
  remoteElectronicPrescription : Nat := 0
  functionCooperation : Nat := 0
  deriving DecidableEq, Repr

def Breakdown.total (b : Breakdown) : Nat :=
  b.infectionControl + b.feverResponse + b.cooperation + b.surveillance + b.antimicrobial +
  b.remoteElectronicPrescription + b.functionCooperation

/-- 通則４〜６は、今回通則３の外来感染対策向上加算を算定する場合に加える。
発熱対応は、その固有の月内回数を判定する（外来感染対策向上加算と回数を混同しない）。 -/
def additionBreakdown (c : Context) : Breakdown :=
  let a := c.infection
  let eligible := infectionEligible c
  let infection := eligible && decide (a.claimsThisMonth = 0)
  let r := c.remote
  { infectionControl := if infection then 6 else 0
    feverResponse := if eligible && a.infectiousSymptoms && a.appropriatePrecautions &&
      decide (a.feverClaimsThisMonth = 0) then 20 else 0
    cooperation := if infection && a.cooperationNotified && decide (a.cooperationClaimsThisMonth = 0)
      then 3 else 0
    surveillance := if infection && a.surveillanceNotified && decide (a.surveillanceClaimsThisMonth = 0)
      then 1 else 0
    antimicrobial := if infection && a.antimicrobialStewardshipNotified &&
      decide (a.antimicrobialClaimsThisMonth = 0) then 5 else 0
    remoteElectronicPrescription := if r.usingInformationCommunicationEquipment &&
      r.electronicPrescriptionStandardNotified && r.issuedStatutoryElectronicPrescription &&
      decide (r.electronicPrescriptionClaimsThisMonth = 0) then 10 else 0
    functionCooperation := if r.usingInformationCommunicationEquipment &&
      r.functionCooperationStandardNotified && decide (r.functionCooperationClaimsThisMonth = 0)
      then 50 else 0 }

structure Assessment where
  section1 : Nat
  section3Materials : Nat
  additions : Breakdown
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Nat :=
  a.section1 + a.section3Materials + a.additions.total

/-- 通則１・２による合算。対象外の加算は０、第１節自体が算定不可なら none。 -/
def assess (c : Context) : Option Assessment :=
  if c.insuranceMedicalInstitution && c.section1Eligible then
    some {
      section1 := c.section1Points
      section3Materials := (c.materials.map MaterialCharge.section3Points).sum
      additions := additionBreakdown c }
  else none

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-! 以下の100点等は通則の検証用入力であり、個別区分の実点数ではない。 -/
private def ordinary : Context :=
  { facility := .clinic
    item := .pediatricOutpatient
    section1Points := 100 }
private def infection : InfectionControl :=
  { standardNotified := true
    infectiousSymptoms := true
    appropriatePrecautions := true
    cooperationNotified := true
    surveillanceNotified := true
    antimicrobialStewardshipNotified := true }
private def remote : RemoteCare :=
  { usingInformationCommunicationEquipment := true
    electronicPrescriptionStandardNotified := true
    issuedStatutoryElectronicPrescription := true
    functionCooperationStandardNotified := true }

example : points ordinary = some 100 := by decide
example : points { ordinary with materials := [⟨12⟩, ⟨23⟩] } = some 135 := by decide
example : points { ordinary with section1Eligible := false } = none := by decide
example : points { ordinary with insuranceMedicalInstitution := false } = none := by decide
example : (List.map infectionEligibleItem
    [.pediatricOutpatient, .outpatientRehabilitation, .outpatientRadiation,
     .comprehensiveCommunityCare, .pediatricPrimaryCare, .outpatientTumorChemotherapy,
     .emergencyLifeSavingManagement, .postDischargeVisitGuidance, .otherSection1]) =
    [true, true, true, true, true, true, true, true, false] := by decide
example : points { ordinary with infection := infection } = some 135 := by decide
example : points { ordinary with
    item := .otherSection1
    infection := infection } = some 100 := by decide
example : points { ordinary with
    facility := .hospital 100
    infection := infection } = some 100 := by decide
example : points { ordinary with
    infection := { infection with standardNotified := false } } = some 100 := by decide
example : (List.map (fun source => points { ordinary with
    infection := { infection with otherSourcesThisMonth := [source] } })
    [.a000Note11, .a001Note15, .part2GeneralRule5, .i012Note14]) =
    [some 100, some 100, some 100, some 100] := by decide
example : points { ordinary with
    infection := { infection with infectiousSymptoms := false } } = some 115 := by decide
example : points { ordinary with
    infection := { infection with appropriatePrecautions := false } } = some 115 := by decide
example : points { ordinary with
    infection := { infection with feverClaimsThisMonth := 1 } } = some 115 := by decide
example : points { ordinary with
    infection := { infection with
      cooperationClaimsThisMonth := 1
      surveillanceClaimsThisMonth := 1
      antimicrobialClaimsThisMonth := 1 } } = some 126 := by decide
example : (additionBreakdown { ordinary with
    infection := { infection with claimsThisMonth := 1 } }).cooperation = 0 := by decide
example : (additionBreakdown { ordinary with
    infection := { infection with claimsThisMonth := 1 } }).surveillance = 0 := by decide
example : (additionBreakdown { ordinary with
    infection := { infection with claimsThisMonth := 1 } }).antimicrobial = 0 := by decide
example : points { ordinary with
    infection := { infection with claimsThisMonth := 1, feverClaimsThisMonth := 1 } } =
    some 100 := by decide
example : points { ordinary with remote := remote } = some 160 := by decide
example : points { ordinary with
    remote := { remote with usingInformationCommunicationEquipment := false } } = some 100 := by decide
example : points { ordinary with
    remote := { remote with issuedStatutoryElectronicPrescription := false } } = some 150 := by decide
example : points { ordinary with
    remote := { remote with electronicPrescriptionStandardNotified := false } } = some 150 := by decide
example : points { ordinary with
    remote := { remote with functionCooperationStandardNotified := false } } = some 110 := by decide
example : points { ordinary with
    remote := { remote with
      electronicPrescriptionClaimsThisMonth := 1
      functionCooperationClaimsThisMonth := 1 } } = some 100 := by decide
example : points { ordinary with
    facility := .hospitalWithGeneralBeds 400 200
    item := .otherSection1
    remote := remote } = some 160 := by decide
example : points { ordinary with
    materials := [⟨12⟩, ⟨23⟩]
    infection := infection
    remote := remote } = some 230 := by decide

theorem cooperation_requiresInfectionClaim (c : Context)
    (h : (additionBreakdown c).infectionControl = 0) :
    (additionBreakdown c).cooperation = 0 := by
  simp only [additionBreakdown] at h ⊢
  split at h <;> simp_all

theorem surveillance_requiresInfectionClaim (c : Context)
    (h : (additionBreakdown c).infectionControl = 0) :
    (additionBreakdown c).surveillance = 0 := by
  simp only [additionBreakdown] at h ⊢
  split at h <;> simp_all

theorem antimicrobial_requiresInfectionClaim (c : Context)
    (h : (additionBreakdown c).infectionControl = 0) :
    (additionBreakdown c).antimicrobial = 0 := by
  simp only [additionBreakdown] at h ⊢
  split at h <;> simp_all

end Sanri.MedicalFee.MedicalManagement
