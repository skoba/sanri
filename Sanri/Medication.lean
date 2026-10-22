import Sanri.MedicalFee

namespace Sanri.MedicalFee.Medication

/-! 第５部 投薬 通則１〜６。Ｆ４００は既存の PrescriptionFee で解決する。
第１〜３・４・６節の個別要件と点数、貼付剤63枚以内／超過分の薬剤価格は入力する。
１回の投薬・１処方を対象とし、入院の個別料金体系は今回追加しない。 -/

inductive Route where
  | inHouse
  | prescription (details : PrescriptionFee.Context)
  deriving DecidableEq, Repr

structure PatchRule where
  prescribedSheets : Nat := 0
  physicianJudgedUnavoidableNecessity : Bool := false
  reasonOnPrescription : Bool := false
  reasonOnClaim : Bool := false
  deriving DecidableEq, Repr

def patchException (p : PatchRule) : Bool :=
  p.physicianJudgedUnavoidableNecessity && p.reasonOnPrescription && p.reasonOnClaim

def patchRestriction (p : PatchRule) : Bool :=
  decide (p.prescribedSheets > 63) && !patchException p

structure NutritionRule where
  nutritionMaintenanceDrugPrescribed : Bool := false
  postoperative : Bool := false
  tubeFeeding : Bool := false
  statusOnPrescription : Bool := false
  statusOnClaim : Bool := false
  difficultToObtainNutritionFromMealsOrEquivalent : Bool := false
  physicianJudgedNecessary : Bool := false
  reasonOnPrescription : Bool := false
  reasonOnClaim : Bool := false
  deriving DecidableEq, Repr

def nutritionException (n : NutritionRule) : Bool :=
  ((n.postoperative || n.tubeFeeding) && n.statusOnPrescription && n.statusOnClaim) ||
  (n.difficultToObtainNutritionFromMealsOrEquivalent && n.physicianJudgedNecessary &&
    n.reasonOnPrescription && n.reasonOnClaim)

def nutritionRestriction (n : NutritionRule) : Bool :=
  n.nutritionMaintenanceDrugPrescribed && !nutritionException n

structure DrugPoints where
  /-- 貼付剤以外の薬剤の解決済み点数。 -/
  other : Nat := 0
  patchesWithin63Sheets : Nat := 0
  patchesExceeding63Sheets : Nat := 0
  deriving DecidableEq, Repr

structure Context where
  insuranceMedicalInstitution : Bool := true
  medicationProvided : Bool := true
  inpatient : Bool := false
  route : Route := .inHouse
  /-- 通則４の「うがい薬のみ」。他の薬剤も処方した場合は false。 -/
  gargleOnly : Bool := false
  patch : PatchRule := {}
  nutrition : NutritionRule := {}
  dispensingFee : Nat := 0 -- Ｆ０００
  prescribingFee : Nat := 0 -- Ｆ１００
  drugs : DrugPoints := {}
  /-- 実際に支給した指定材料の第４節の点数。 -/
  section4Materials : List Nat := []
  pharmacistAlwaysOnDuty : Bool := false
  dispensingTechnicalBasicFee : Nat := 0 -- Ｆ５００
  deriving DecidableEq, Repr

inductive Restriction where
  | gargleOnly | excessivePatches | nutritionMaintenance
  deriving DecidableEq, Repr

def restrictions (c : Context) : List Restriction :=
  if c.inpatient then [] else
    (if c.gargleOnly then [.gargleOnly] else []) ++
    (if patchRestriction c.patch then [.excessivePatches] else []) ++
    (if nutritionRestriction c.nutrition then [.nutritionMaintenance] else [])

structure Assessment where
  dispensing : Nat := 0
  prescribing : Nat := 0
  drugs : Nat := 0
  prescription : PrescriptionFee.Points := ⟨0⟩
  materials : Nat := 0
  dispensingTechnicalBasic : Nat := 0
  restrictions : List Restriction := []
  /-- 通則５で除外した薬剤点数。その他の薬剤分を含めない。 -/
  excludedExcessPatchDrugPoints : Nat := 0
  deriving DecidableEq, Repr

/-- Ｆ４００の端数を維持して1/5点単位で合算する。 -/
def Assessment.total (a : Assessment) : PrescriptionFee.Points :=
  ⟨5 * (a.dispensing + a.prescribing + a.drugs + a.materials + a.dispensingTechnicalBasic) +
    a.prescription.fifths⟩

/-- 共通の患者状態をＦ４００注４等の判定へ反映する。 -/
def prescriptionPoints (c : Context) (details : PrescriptionFee.Context) : Option PrescriptionFee.Points :=
  PrescriptionFee.points { details with additions := { details.additions with inpatient := c.inpatient } }

/-- 通則１の交付時はＦ４００だけを採用し、通則２の材料は両経路で加算する。
通則４〜６の列挙にない材料費を、それらの制限で自動除外しない。 -/
def assess (c : Context) : Option Assessment := do
  if !c.insuranceMedicalInstitution || !c.medicationProvided ||
      (c.patch.prescribedSheets ≤ 63 ∧ c.drugs.patchesExceeding63Sheets > 0) then none else
    let rs := restrictions c
    let allListedBlocked := rs.contains .gargleOnly || rs.contains .nutritionMaintenance
    let patchesBlocked := rs.contains .excessivePatches
    let feesBlocked := allListedBlocked || patchesBlocked
    let materials := c.section4Materials.sum
    match c.route with
    | .prescription details =>
      if feesBlocked then some { materials := materials, restrictions := rs }
      else
        let points ← prescriptionPoints c details
        some { prescription := points, materials := materials, restrictions := rs }
    | .inHouse =>
      let drugPoints := if allListedBlocked then 0 else c.drugs.other + c.drugs.patchesWithin63Sheets +
        (if patchesBlocked then 0 else c.drugs.patchesExceeding63Sheets)
      some {
        dispensing := if feesBlocked then 0 else c.dispensingFee
        prescribing := if feesBlocked then 0 else c.prescribingFee
        drugs := drugPoints
        materials := materials
        dispensingTechnicalBasic := if !feesBlocked && c.pharmacistAlwaysOnDuty
          then c.dispensingTechnicalBasicFee else 0
        restrictions := rs
        excludedExcessPatchDrugPoints := if patchesBlocked then c.drugs.patchesExceeding63Sheets else 0 }

def points (c : Context) : Option PrescriptionFee.Points := (assess c).map Assessment.total

private def ordinary : Context :=
  { dispensingFee := 10
    prescribingFee := 20
    drugs := { other := 30 }
    dispensingTechnicalBasicFee := 40 }
private def prescription : PrescriptionFee.Context :=
  { facility := .clinic, issuedForInsurancePharmacy := true }
private def excessive : Context :=
  { ordinary with
    patch := { prescribedSheets := 64 }
    drugs := { other := 30, patchesWithin63Sheets := 63, patchesExceeding63Sheets := 1 }
    pharmacistAlwaysOnDuty := true }

example : points ordinary = some ⟨300⟩ := by decide
example : points { ordinary with pharmacistAlwaysOnDuty := true } = some ⟨500⟩ := by decide
example : points { ordinary with route := .prescription prescription, pharmacistAlwaysOnDuty := true } = some ⟨300⟩ := by decide
example : points { ordinary with route := .prescription prescription, section4Materials := [12, 23] } = some ⟨475⟩ := by decide
example : points { ordinary with gargleOnly := true } = some ⟨0⟩ := by decide
example : points { ordinary with gargleOnly := true, section4Materials := [5] } = some ⟨25⟩ := by decide
example : points { ordinary with gargleOnly := true, route := .prescription prescription } = some ⟨0⟩ := by decide
example : points { ordinary with gargleOnly := true, inpatient := true } = some ⟨300⟩ := by decide
example : patchRestriction { prescribedSheets := 63 } = false := by decide
example : patchRestriction { prescribedSheets := 64 } = true := by decide
example : points excessive = some ⟨465⟩ := by decide -- 他薬30点＋63枚以内63点だけ
example : points { excessive with route := .prescription prescription } = some ⟨0⟩ := by decide
example : points { excessive with patch := { prescribedSheets := 64, physicianJudgedUnavoidableNecessity := true, reasonOnPrescription := true, reasonOnClaim := true } } =
    some ⟨820⟩ := by decide
example : points { excessive with patch := { prescribedSheets := 64, physicianJudgedUnavoidableNecessity := true, reasonOnPrescription := true } } = some ⟨465⟩ := by decide
example : points { ordinary with nutrition := { nutritionMaintenanceDrugPrescribed := true } } = some ⟨0⟩ := by decide
example : points { ordinary with nutrition := { nutritionMaintenanceDrugPrescribed := true, postoperative := true, statusOnPrescription := true, statusOnClaim := true } } = some ⟨300⟩ := by decide
example : points { ordinary with nutrition := { nutritionMaintenanceDrugPrescribed := true, tubeFeeding := true, statusOnPrescription := true, statusOnClaim := true } } = some ⟨300⟩ := by decide
example : points { ordinary with nutrition := { nutritionMaintenanceDrugPrescribed := true, postoperative := true } } = some ⟨0⟩ := by decide
example : points { ordinary with nutrition := { nutritionMaintenanceDrugPrescribed := true, difficultToObtainNutritionFromMealsOrEquivalent := true, physicianJudgedNecessary := true, reasonOnPrescription := true, reasonOnClaim := true } } = some ⟨300⟩ := by decide
example : points { ordinary with nutrition := { nutritionMaintenanceDrugPrescribed := true, difficultToObtainNutritionFromMealsOrEquivalent := true, reasonOnPrescription := true, reasonOnClaim := true } } = some ⟨0⟩ := by decide
example : points { ordinary with insuranceMedicalInstitution := false } = none := by decide
example : points { ordinary with medicationProvided := false } = none := by decide
example : points { ordinary with route := .prescription { prescription with
    issuedForInsurancePharmacy := false } } = none := by decide

theorem prescriptionRoute_noDispensingFee (c : Context) (details : PrescriptionFee.Context)
    (a : Assessment) (route : c.route = .prescription details) (h : assess c = some a) :
    a.dispensing = 0 ∧ a.prescribing = 0 ∧ a.drugs = 0 ∧ a.dispensingTechnicalBasic = 0 := by
  simp [assess, route] at h
  split at h
  · simp only [Option.some.injEq] at h
    rcases h with ⟨_, rfl⟩
    simp
  · cases hp : prescriptionPoints c details <;> simp [hp] at h
    rcases h with ⟨_, rfl⟩
    simp

end Sanri.MedicalFee.Medication
