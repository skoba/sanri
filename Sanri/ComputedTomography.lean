import Sanri.Imaging
import Sanri.PhysiologicalExaminations

namespace Sanri.MedicalFee.ComputedTomography

/-! 第３節通則１〜４、Ｅ２００・Ｅ２００－２・Ｅ２０１・Ｅ２０２・Ｅ２０３。
同一患者の月次履歴・一連・同時実施を呼出元で同定する。端数は1/100点単位で保持する。 -/

inductive Kind where
  | ct (rows : Nat) (jointUse : Bool)
  | cisternCt
  | xenon
  /-- 磁場強度は0.1テスラ単位。 -/
  | mri (teslaTenths : Nat) (jointUse : Bool)
  deriving DecidableEq, Repr

inductive Modality where
  | ct | mri
  deriving DecidableEq, Repr

def modality : Kind → Option Modality
  | .ct _ _ | .cisternCt => some .ct
  | .mri _ _ => some .mri
  | .xenon => none

def basePoints : Kind → Nat
  | .ct rows joint =>
    if rows ≥ 128 then if joint then 1120 else 1100
    else if rows ≥ 64 then if joint then 1020 else 1000
    else if rows ≥ 16 then 900 else if rows ≥ 4 then 750 else 560
  | .cisternCt => 2300
  | .xenon => 2000
  | .mri strength joint => if strength ≥ 30 then if joint then 1720 else 1700
      else if strength ≥ 15 then 1330 else 900

structure Scan where
  id : Nat
  kind : Kind
  simultaneousId : Nat
  seriesId : Nat
  performed : Bool := true
  seriesAlreadyCharged : Bool := false
  /-- ＣＴのイ〜ニ又はＭＲＩの１・２の算定基準に適合し届出済み。 -/
  equipmentStandardNotified : Bool := false
  jointUseStandardNotified : Bool := false
  referredByOtherInstitutionForImaging : Bool := false
  headTrauma : Bool := false
  contrastUsed : Bool := false
  mriCerebrovascularContrast : Bool := false
  coronaryCt : Bool := false
  coronaryCtStandardNotified : Bool := false
  wholeBodyTraumaCt : Bool := false
  traumaCtStandardNotified : Bool := false
  colonCt : Bool := false
  colonCtStandardMet : Bool := false
  cardiacMri : Bool := false
  cardiacMriStandardNotified : Bool := false
  breastMri : Bool := false
  breastMriStandardNotified : Bool := false
  sedationWithAnesthesia : Bool := false
  multipleRegionsInOneSeries : Bool := false
  pediatricSedationStandardNotified : Bool := false
  headMri : Bool := false
  headMriStandardNotified : Bool := false
  wholeBodyMri : Bool := false
  wholeBodyMriStandardNotified : Bool := false
  liverElastography : Bool := false
  liverElastographyStandardNotified : Bool := false
  deriving DecidableEq, Repr

structure Principal where
  simultaneousId : Nat
  modality : Modality
  scanId : Nat
  deriving DecidableEq, Repr

structure ImageSeries where
  id : Nat
  digitizedManagedAndStored : Bool := false
  electronicAdditionAlreadyClaimed : Bool := false
  filmPoints : Nat := 0
  deriving DecidableEq, Repr

structure Context where
  insuranceMedicalInstitution : Bool := true
  scans : List Scan
  principals : List Principal := []
  imageSeries : List ImageSeries := []
  completedYears : Nat := 20
  newborn : Bool := false
  /-- ＣＴ・ＭＲＩ共通の月内算定済み撮影回数。Ｅ２０１は含めない。 -/
  priorCtMriSeriesThisMonth : Nat := 0
  ffrAnalysisPerformed : Bool := false
  ffrStandardNotified : Bool := false
  ffrClaimedThisMonth : Bool := false
  diagnosisPerformed : Bool := true
  diagnosisClaimedThisMonth : Bool := false
  deriving DecidableEq, Repr

def eligible (s : Scan) : Bool :=
  match s.kind with
  | .ct rows joint =>
    (decide (rows < 4) || s.equipmentStandardNotified) &&
    (decide (rows < 64) || !joint || s.jointUseStandardNotified || s.referredByOtherInstitutionForImaging) &&
    (!s.colonCt || (decide (rows ≥ 16) && s.colonCtStandardMet)) &&
    (!s.coronaryCt || s.coronaryCtStandardNotified) &&
    (!s.wholeBodyTraumaCt || s.traumaCtStandardNotified)
  | .mri strength joint =>
    (decide (strength < 15) || s.equipmentStandardNotified) &&
    (decide (strength < 30) || !joint || s.jointUseStandardNotified || s.referredByOtherInstitutionForImaging) &&
    (!s.cardiacMri || s.cardiacMriStandardNotified) &&
    (!s.breastMri || s.breastMriStandardNotified) &&
    (!s.headMri || (decide (strength ≥ 30) && s.headMriStandardNotified)) &&
    (!s.wholeBodyMri || s.wholeBodyMriStandardNotified) &&
    (!s.liverElastography || s.liverElastographyStandardNotified)
  | _ => true

def generalAgeRate (age : PhysiologicalExaminations.AgeGroup) (headTrauma : Bool) : Nat :=
  match age with
  | .newborn => if headTrauma then 85 else 80
  | .underThreeNonNewborn => if headTrauma then 55 else 50
  | .threeToUnderSix => if headTrauma then 35 else 30
  | .sixOrOlder => 0

def fixedAdditions (s : Scan) : Nat :=
  match s.kind with
  | .ct rows _ =>
    (if s.contrastUsed then 500 else 0) + (if s.coronaryCt then 600 else 0) +
    (if s.wholeBodyTraumaCt then 800 else 0) +
    (if s.colonCt then if rows ≥ 64 then 620 else 500 else 0)
  | .mri _ _ =>
    (if s.contrastUsed && !s.mriCerebrovascularContrast then 250 else 0) +
    (if s.cardiacMri then 400 else 0) + (if s.breastMri then 100 else 0) +
    (if s.headMri then 100 else 0) + (if s.wholeBodyMri then 600 else 0) +
    (if s.liverElastography then 600 else 0)
  | _ => 0

inductive Exclusion where
  | principalScan | xenonIncludesCt | alreadyChargedSeries
  deriving DecidableEq, Repr

structure ScanCharge where
  id : Nat
  exclusion : Option Exclusion := none
  baseHundredths : Nat := 0
  fixedAdditionsHundredths : Nat := 0
  ageAdditionHundredths : Nat := 0
  sedationAdditionHundredths : Nat := 0
  repeatRateTenths : Nat := 10
  deriving DecidableEq, Repr

def ScanCharge.totalHundredths (a : ScanCharge) : Nat :=
  (a.baseHundredths + a.fixedAdditionsHundredths + a.ageAdditionHundredths +
    a.sedationAdditionHundredths) * a.repeatRateTenths / 10

structure Assessment where
  scans : List ScanCharge
  ffr : Nat
  diagnosis : Nat
  electronic : Nat
  film : Nat
  deriving DecidableEq, Repr

def Assessment.totalHundredths (a : Assessment) : Nat :=
  (a.scans.map ScanCharge.totalHundredths).sum + 100 * (a.ffr + a.diagnosis + a.electronic + a.film)

/-- 同時撮影の主検査を選択してから、ＣＴ・ＭＲＩ共通の月内回数を更新する。
年齢・固定・鎮静加算を加えた当該撮影費用に80％を適用し、Ｅ２０３等は別に合算する。 -/
def assess (c : Context) : Option Assessment := do
  if !c.insuranceMedicalInstitution || (c.scans.isEmpty && !c.ffrAnalysisPerformed) ||
      (c.ffrAnalysisPerformed && !c.ffrStandardNotified) then none else
    let age ← PhysiologicalExaminations.ageGroup c.completedYears c.newborn
    let performed := c.scans.filter Scan.performed
    if (c.scans.map Scan.id).eraseDups.length != c.scans.length ||
        (c.imageSeries.map ImageSeries.id).eraseDups.length != c.imageSeries.length ||
        performed.any (fun s => !eligible s) then none else
      let keys := c.principals.map (fun p => (p.simultaneousId, p.modality))
      if keys.eraseDups.length != keys.length || c.principals.any (fun p =>
          !performed.any (fun s => s.id == p.scanId && s.simultaneousId == p.simultaneousId &&
            modality s.kind == some p.modality)) then none else
          let state ← performed.foldlM (fun (state : List Scan × List ScanCharge × Nat) s => do
            let mode := modality s.kind
            let peers := performed.filter (fun x => x.simultaneousId == s.simultaneousId && modality x.kind == mode)
            let principal := c.principals.find? (fun p => p.simultaneousId == s.simultaneousId && some p.modality == mode)
            let xenonIncludes := mode == some .ct && performed.any (fun x =>
              x.kind == .xenon && x.simultaneousId == s.simultaneousId)
            if mode.isSome && decide (peers.length ≥ 2) && principal.isNone && !xenonIncludes then none else
              let reason := if xenonIncludes then some Exclusion.xenonIncludesCt
                else if mode.isSome && decide (peers.length ≥ 2) && principal.any (fun p => p.scanId != s.id)
                  then some Exclusion.principalScan
                else if mode == some .ct && performed.any (fun x => x.kind == .xenon && x.simultaneousId == s.simultaneousId)
                  then some .xenonIncludesCt
                else if s.seriesAlreadyCharged || state.1.any (fun x =>
                    x.seriesId == s.seriesId && modality x.kind == mode) then some .alreadyChargedSeries
                else none
              match reason with
              | some reason => some (state.1, state.2.1 ++ [{ id := s.id, exclusion := some reason }], state.2.2)
              | none =>
                let base := basePoints s.kind
                let sedation := match s.kind with
                  | .mri _ _ => decide (c.completedYears < 15) && s.sedationWithAnesthesia &&
                      s.multipleRegionsInOneSeries && s.pediatricSedationStandardNotified
                  | _ => false
                let charge : ScanCharge := {
                  id := s.id
                  baseHundredths := 100 * base
                  fixedAdditionsHundredths := 100 * fixedAdditions s
                  ageAdditionHundredths := base * generalAgeRate age s.headTrauma
                  sedationAdditionHundredths := if sedation then 80 * base else 0
                  repeatRateTenths := if mode.isSome && decide (state.2.2 ≥ 1) then 8 else 10 }
                some (state.1 ++ [s], state.2.1 ++ [charge], state.2.2 + if mode.isSome then 1 else 0))
              ([], [], c.priorCtMriSeriesThisMonth)
          let seriesIds := (state.1.map Scan.seriesId).eraseDups
          let series := c.imageSeries.filter (fun s => seriesIds.contains s.id)
          if series.any (fun s => s.digitizedManagedAndStored && decide (s.filmPoints > 0)) then none else
            some {
              scans := state.2.1
              ffr := if c.ffrAnalysisPerformed && !c.ffrClaimedThisMonth then 7800 else 0
              diagnosis := if c.diagnosisPerformed && !c.diagnosisClaimedThisMonth then 450 else 0
              electronic := 120 * (series.filter (fun s => s.digitizedManagedAndStored && !s.electronicAdditionAlreadyClaimed)).length
              film := ((series.filter (fun s => !s.digitizedManagedAndStored)).map ImageSeries.filmPoints).sum }

structure CombinedAssessment where
  tomography : Assessment
  general : Imaging.Assessment
  deriving DecidableEq, Repr

def CombinedAssessment.totalHundredths (a : CombinedAssessment) : Nat :=
  a.tomography.totalHundredths + 100 * a.general.total

/-- 撮影を評価してから第４部通則のＥ２０３管理加算等と丸めず合算する。
existing に今回の撮影・診断・電子画像管理・フィルムを二重入力しない。 -/
def assessWithGeneralRules (c : Context) (existing : Imaging.Context)
    (management : Option Imaging.Management := none) : Option CombinedAssessment := do
  let a ← assess c
  if !c.diagnosisPerformed && management.isSome then none else
    let general ← Imaging.assess { existing with
      insuranceMedicalInstitution := existing.insuranceMedicalInstitution && c.insuranceMedicalInstitution
      entries := existing.entries ++ [⟨if c.diagnosisPerformed then .e203 else .other, .section3, 0, management⟩] }
    some ⟨a, general⟩

inductive IncludedService where
  | contrastInjection | anesthesiaOtherThanL008 | xenonInhalation | simultaneousCt | colonGasInjection
  deriving DecidableEq, Repr

def serviceIncluded (s : Scan) (service : IncludedService) : Bool :=
  match s.kind, service with
  | .cisternCt, .contrastInjection | .cisternCt, .anesthesiaOtherThanL008 => true
  | .ct _ _, .contrastInjection | .ct _ _, .anesthesiaOtherThanL008 => s.contrastUsed || s.colonCt
  | .ct _ _, .colonGasInjection => s.colonCt
  | .mri _ _, .contrastInjection | .mri _ _, .anesthesiaOtherThanL008 => s.contrastUsed && !s.mriCerebrovascularContrast
  | .xenon, .xenonInhalation | .xenon, .simultaneousCt => true
  | _, _ => false

private def ct : Scan :=
  { id := 1, kind := .ct 128 false, simultaneousId := 1, seriesId := 1, equipmentStandardNotified := true }
private def mri : Scan :=
  { id := 2, kind := .mri 30 false, simultaneousId := 2, seriesId := 2, equipmentStandardNotified := true }
private def total (c : Context) : Option Nat := (assess c).map Assessment.totalHundredths

example : (List.map (fun rows => basePoints (.ct rows false)) [3, 4, 15, 16, 63, 64, 127, 128]) =
    [560, 750, 750, 900, 900, 1000, 1000, 1100] := by decide
example : basePoints (.ct 128 true) = 1120 := by decide
example : basePoints (.ct 64 true) = 1020 := by decide
example : (List.map (fun strength => basePoints (.mri strength false)) [14, 15, 29, 30]) =
    [900, 1330, 1330, 1700] := by decide
example : basePoints (.mri 30 true) = 1720 := by decide
example : total { scans := [ct] } = some 155000 := by decide
example : total { scans := [{ ct with equipmentStandardNotified := false }] } = none := by decide
example : total { scans := [{ ct with kind := .ct 128 true }] } = none := by decide
example : total { scans := [{ ct with kind := .ct 128 true, referredByOtherInstitutionForImaging := true }] } = some 157000 := by decide
example : total { scans := [ct, mri] } = some 291000 := by decide
example : total { scans := [ct], priorCtMriSeriesThisMonth := 1 } = some 133000 := by decide
example : total { scans := [mri], priorCtMriSeriesThisMonth := 1 } = some 181000 := by decide
example : total { scans := [{ ct with kind := .xenon }], priorCtMriSeriesThisMonth := 1 } = some 245000 := by decide
example : total { scans := [ct, { ct with id := 2, kind := .cisternCt }] } = none := by decide
example : total { scans := [ct, { ct with id := 2, kind := .cisternCt }], principals := [⟨1, .ct, 2⟩] } = some 275000 := by decide
example : total { scans := [ct, { ct with id := 2, kind := .xenon }] } = some 245000 := by decide
example : total { scans := [ct, { ct with id := 2, kind := .cisternCt }, { ct with id := 3, kind := .xenon }] } = some 245000 := by decide
example : total { scans := [ct], completedYears := 0, newborn := true } = some 243000 := by decide
example : total { scans := [{ ct with headTrauma := true }], completedYears := 0, newborn := true } = some 248500 := by decide
example : total { scans := [ct], completedYears := 2 } = some 210000 := by decide
example : total { scans := [{ ct with headTrauma := true }], completedYears := 2 } = some 215500 := by decide
example : total { scans := [ct], completedYears := 5 } = some 188000 := by decide
example : total { scans := [{ ct with headTrauma := true }], completedYears := 5 } = some 193500 := by decide
example : total { scans := [ct], completedYears := 6 } = some 155000 := by decide
example : total { scans := [{ ct with contrastUsed := true }] } = some 205000 := by decide
example : total { scans := [{ ct with kind := .cisternCt, contrastUsed := true }] } = some 275000 := by decide
example : total { scans := [{ ct with coronaryCt := true }] } = none := by decide
example : total { scans := [{ ct with coronaryCt := true, coronaryCtStandardNotified := true }] } = some 215000 := by decide
example : total { scans := [{ ct with wholeBodyTraumaCt := true, traumaCtStandardNotified := true }] } = some 235000 := by decide
example : total { scans := [{ ct with colonCt := true, colonCtStandardMet := true }] } = some 217000 := by decide
example : total { scans := [{ ct with kind := .ct 16 false, colonCt := true, colonCtStandardMet := true }] } = some 185000 := by decide
example : total { scans := [{ mri with contrastUsed := true }] } = some 240000 := by decide
example : total { scans := [{ mri with contrastUsed := true, mriCerebrovascularContrast := true }] } = some 215000 := by decide
example : total { scans := [{ mri with sedationWithAnesthesia := true, multipleRegionsInOneSeries := true, pediatricSedationStandardNotified := true }], completedYears := 14 } = some 351000 := by decide
example : total { scans := [{ mri with sedationWithAnesthesia := true, multipleRegionsInOneSeries := true, pediatricSedationStandardNotified := true }], completedYears := 15 } = some 215000 := by decide
example : total { scans := [{ mri with sedationWithAnesthesia := true, pediatricSedationStandardNotified := true }], completedYears := 14 } = some 215000 := by decide
example : total { scans := [{ mri with headMri := true, headMriStandardNotified := true }] } = some 225000 := by decide
example : total { scans := [{ mri with kind := .mri 15 false, headMri := true, headMriStandardNotified := true }] } = none := by decide
example : total { scans := [ct], ffrAnalysisPerformed := true } = none := by decide
example : total { scans := [ct], ffrAnalysisPerformed := true, ffrStandardNotified := true } = some 935000 := by decide
example : total { scans := [ct], ffrAnalysisPerformed := true, ffrStandardNotified := true, ffrClaimedThisMonth := true } = some 155000 := by decide
example : total { scans := [ct], diagnosisClaimedThisMonth := true } = some 110000 := by decide
example : total { scans := [ct], imageSeries := [⟨1, true, false, 0⟩] } = some 167000 := by decide
example : total { scans := [ct], imageSeries := [⟨1, true, false, 10⟩] } = none := by decide
example : serviceIncluded { ct with kind := .cisternCt } .anesthesiaOtherThanL008 = true := by decide
example : serviceIncluded { ct with kind := .xenon } .simultaneousCt = true := by decide

example : total { scans := [{ ct with kind := .ct 64 false, colonCt := true, colonCtStandardMet := true }] } = some 207000 := by decide
example : total { scans := [{ ct with kind := .ct 63 false, colonCt := true, colonCtStandardMet := true }] } = some 185000 := by decide
example : total { scans := [{ ct with kind := .ct 15 false, colonCt := true, colonCtStandardMet := true }] } = none := by decide
example : total { scans := [{ ct with colonCt := true }] } = none := by decide

example : (assessWithGeneralRules { scans := [ct] } {
    entries := [], localStandards := { two := true }, localDedicatedFullTimeDoctorWrittenReport := true } (some .two)).map
    CombinedAssessment.totalHundredths = some 172500 := by decide

end Sanri.MedicalFee.ComputedTomography
