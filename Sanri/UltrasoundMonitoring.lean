import Sanri.Cardiorespiratory

namespace Sanri.MedicalFee.UltrasoundMonitoring

/-! 超音波検査等の通則、Ｄ２１５〜Ｄ２３４（Ｄ２２１は削除）。
購入・暦月・暦年・同一部位・一連・同日・同月の履歴は呼出元で管理する。
既存の外来優先方針に従い、入院固有の規則は追加しない。 -/

inductive Item where
  | aMode | tomographyHomeVisit | tomographyThoracoabdominal | tomographyLegVessels | tomographyOther
  | transthoracicEcho | mMode | transesophagealEcho | fetalEcho | stressEcho
  | fetalDoppler | peripheralDoppler | continuousCerebralDoppler | mappingCerebralDoppler
  | intravascularUltrasound | liverStiffness | elastography | attenuation
  | thermography | residualUrineUltrasound | residualUrineCatheter | fluorescentLymphography
  | dexaLumbar | remsLumbar | mdSexa | boneUltrasound
  | laborMonitoring | nonStressTest
  | cardiorespiratoryMonitoring | neonatalMonitoring | cardioscope | cardiotachoscope
  | compartmentPressure | transcutaneousBloodGas | continuousBloodGas | transcutaneousOxygen
  | oxygenSaturation | overnightOxygenSaturation | endTidalCO2
  | invasiveArterialPressure | noninvasiveContinuousBloodPressure | ambulatoryBloodPressure | headUpTilt
  | centralVenousPressure | intracranialPressure | deepBodyTemperature | peripheralCirculationTemperature
  | pulmonaryArteryPressure | artificialPancreas | subcutaneousGlucose
  | esophagealPressure | anorectalFunction | gastrointestinalPH24Hours
  deriving DecidableEq, Repr

def code : Item → Nat
  | .aMode | .tomographyHomeVisit | .tomographyThoracoabdominal | .tomographyLegVessels
  | .tomographyOther | .transthoracicEcho | .mMode | .transesophagealEcho | .fetalEcho
  | .stressEcho | .fetalDoppler | .peripheralDoppler | .continuousCerebralDoppler
  | .mappingCerebralDoppler | .intravascularUltrasound | .liverStiffness | .elastography | .attenuation => 215
  | .thermography | .residualUrineUltrasound | .residualUrineCatheter | .fluorescentLymphography => 216
  | .dexaLumbar | .remsLumbar | .mdSexa | .boneUltrasound => 217
  | .laborMonitoring => 218
  | .nonStressTest => 219
  | .cardiorespiratoryMonitoring | .neonatalMonitoring | .cardioscope | .cardiotachoscope => 220
  | .compartmentPressure => 221
  | .transcutaneousBloodGas | .continuousBloodGas | .transcutaneousOxygen => 222
  | .oxygenSaturation | .overnightOxygenSaturation => 223
  | .endTidalCO2 => 224
  | .invasiveArterialPressure | .noninvasiveContinuousBloodPressure | .ambulatoryBloodPressure | .headUpTilt => 225
  | .centralVenousPressure => 226
  | .intracranialPressure => 227
  | .deepBodyTemperature => 228
  | .peripheralCirculationTemperature => 229
  | .pulmonaryArteryPressure => 230
  | .artificialPancreas | .subcutaneousGlucose => 231
  | .esophagealPressure => 232
  | .anorectalFunction => 233
  | .gastrointestinalPH24Hours => 234

def suffix : Item → Nat
  | .liverStiffness | .residualUrineUltrasound | .residualUrineCatheter | .compartmentPressure
  | .transcutaneousOxygen | .overnightOxygenSaturation | .noninvasiveContinuousBloodPressure
  | .subcutaneousGlucose => 2
  | .elastography | .fluorescentLymphography | .ambulatoryBloodPressure => 3
  | .attenuation | .headUpTilt => 4
  | _ => 0

def isTomography (i : Item) : Bool := decide (i ∈
  [.tomographyHomeVisit, .tomographyThoracoabdominal, .tomographyLegVessels, .tomographyOther])
def isCardiacEcho (i : Item) : Bool := decide (i ∈
  [.transthoracicEcho, .mMode, .transesophagealEcho, .fetalEcho, .stressEcho])
def isDoppler (i : Item) : Bool := decide (i ∈
  [.fetalDoppler, .peripheralDoppler, .continuousCerebralDoppler, .mappingCerebralDoppler])
def isBone (i : Item) : Bool := decide (code i = 217)
def isResidualUrine (i : Item) : Bool := decide (i = .residualUrineUltrasound ∨ i = .residualUrineCatheter)
def isHourly (i : Item) : Bool := decide (i ∈
  [.laborMonitoring, .cardiorespiratoryMonitoring, .neonatalMonitoring, .cardioscope, .cardiotachoscope,
   .transcutaneousBloodGas, .continuousBloodGas, .invasiveArterialPressure, .intracranialPressure, .pulmonaryArteryPressure])
def isSeries (i : Item) : Bool := decide (i ∈
  [.nonStressTest, .overnightOxygenSaturation, .artificialPancreas, .subcutaneousGlucose])
def isDaily (i : Item) : Bool :=
  isDoppler i || decide (i ∈ [.transcutaneousOxygen, .oxygenSaturation, .endTidalCO2,
    .noninvasiveContinuousBloodPressure, .centralVenousPressure, .deepBodyTemperature,
    .peripheralCirculationTemperature])

inductive CerebralPrincipal where
  | continuous | mapping
  deriving DecidableEq, Repr

structure Context where
  item : Item
  insuranceMedicalInstitution : Bool := true
  performed : Bool := true
  completedYears : Nat := 20
  newborn : Bool := false
  priorExecutionsThisMonth : Nat := 0
  dailyFeeClaimed : Bool := false
  seriesAlreadyClaimed : Bool := false
  seriesId : Nat := 0
  siteId : Nat := 0
  /-- Ｄ２１５の２イ又は３ニの当月算定済回数（各々の該当検査の履歴）。 -/
  limitedUltrasoundClaimsThisMonth : Nat := 0
  residualUrineClaimsThisMonth : Nat := 0
  facilityStandardNotified : Bool := false
  contrastUsed : Bool := false
  pulsedDopplerPerformed : Bool := false
  fetalEchoDiagnosisPerformed : Bool := false
  bothCerebralDopplerPerformed : Bool := false
  cerebralPrincipal : Option CerebralPrincipal := none
  hitsMesDetected : Bool := false
  liverStiffnessClaimedForPatient : Bool := false
  elastographyClaimedForPatient : Bool := false
  thermographyLoadPerformed : Bool := false
  dexaFemurSameDay : Bool := false
  remsFemurSameDay : Bool := false
  /-- Ｄ２１７全方式を合算した履歴。期間は30日・365日等で代用しない。 -/
  boneClaimsInYear : Nat := 0
  withinOneYearOfOsteoporosisTreatmentStart : Bool := false
  boneClaimsInFourMonthPeriod : Nat := 0
  durationMinutes : Nat := 0
  /-- Ｄ２２０の当該監視開始からの日数（１始まり）。 -/
  monitoringDay : Nat := 1
  observedEcgCurve : Bool := false
  observedHeartRate : Bool := false
  simultaneousMechanicalVentilation : Bool := false
  sameDayL008Anesthesia : Bool := false
  sameDayWalkingTest : Bool := false
  suspectedAcuteCompartmentSyndrome : Bool := false
  compartmentDiagnosisAlreadyClaimedAtSameSite : Bool := false
  /-- Ｄ２２５・２２６・２３０の一連のうち、今回の日次分を算定済みか。
カテーテル交換で履歴をリセットしない。 -/
  catheterSeriesDailyFeeClaimed : Bool := false
  pressureMeasurementCount : Nat := 0
  balloonPulmonaryCatheterInserted : Bool := false
  catheterInsertionStartDay : Bool := false
  facility : Facility := .clinic
  glucoseClaimsInSixMonthPeriod : Nat := 0
  anorectalItemCount : Nat := 0
  anorectalClaimsThisMonth : Nat := 0
  deriving DecidableEq, Repr

def hourlyUnits (minutes : Nat) : Nat := (minutes + 59) / 60

def basePoints (c : Context) : Option Nat :=
  match c.item with
  | .aMode => some 150
  | .tomographyHomeVisit => some 400
  | .tomographyThoracoabdominal => some 530
  | .tomographyLegVessels => some 450
  | .tomographyOther => some 350
  | .transthoracicEcho => some 880
  | .mMode => some 500
  | .transesophagealEcho => some 1800
  | .fetalEcho => some 300
  | .stressEcho => some 2010
  | .fetalDoppler | .peripheralDoppler => some 20
  | .continuousCerebralDoppler => some 150
  | .mappingCerebralDoppler => some 400
  | .intravascularUltrasound => some 4290
  | .liverStiffness | .elastography | .attenuation | .thermography => some 200
  | .residualUrineUltrasound => some 55
  | .residualUrineCatheter => some 45
  | .fluorescentLymphography => some 500
  | .dexaLumbar => some 360
  | .remsLumbar | .mdSexa => some 140
  | .boneUltrasound => some 80
  | .laborMonitoring => some (if c.durationMinutes ≤ 60 then 510 else if c.durationMinutes ≤ 90 then 700 else 890)
  | .nonStressTest => some 210
  | .cardiorespiratoryMonitoring | .neonatalMonitoring | .cardioscope | .cardiotachoscope =>
    some (if c.durationMinutes ≤ 180 then 50 * hourlyUnits c.durationMinutes
      else if c.monitoringDay ≤ 7 then 150 else if c.monitoringDay ≤ 14 then 130 else 50)
  | .compartmentPressure => some 620
  | .transcutaneousBloodGas | .continuousBloodGas =>
    some (if c.durationMinutes ≤ 300 then 100 * hourlyUnits c.durationMinutes else 630)
  | .transcutaneousOxygen | .endTidalCO2 | .noninvasiveContinuousBloodPressure
  | .deepBodyTemperature | .peripheralCirculationTemperature => some 100
  | .oxygenSaturation => some 35
  | .overnightOxygenSaturation => some 100
  | .invasiveArterialPressure => some (if c.durationMinutes ≤ 60 then 130 else 260)
  | .ambulatoryBloodPressure => some 200
  | .headUpTilt => some 1030
  | .centralVenousPressure => if c.pressureMeasurementCount = 0 then none
      else some (if c.pressureMeasurementCount ≤ 4 then 120 else 240)
  | .intracranialPressure => some (if c.durationMinutes ≤ 180 then 200 * hourlyUnits c.durationMinutes else 960)
  | .pulmonaryArteryPressure => some (if c.durationMinutes ≤ 120 then 180 * hourlyUnits c.durationMinutes else 570)
  | .artificialPancreas => some 5000
  | .subcutaneousGlucose => some 700
  | .esophagealPressure => some 936
  | .anorectalFunction => if c.anorectalItemCount = 0 then none
      else some (if c.anorectalItemCount = 1 then 800 else 1200)
  | .gastrointestinalPH24Hours => some 3000

def isClinic : Facility → Bool
  | .clinic => true
  | _ => false

/-- 個別の月・年・部位・施設条件。日次重複や他項目への包括は別に記録する。 -/
def eligible (c : Context) : Bool :=
  c.insuranceMedicalInstitution && c.performed &&
  (!isHourly c.item || decide (c.durationMinutes > 0)) &&
  (decide (code c.item ≠ 220) || (c.observedEcgCurve && c.observedHeartRate && decide (c.monitoringDay > 0))) &&
  (decide (c.item ≠ .tomographyHomeVisit) || decide (c.limitedUltrasoundClaimsThisMonth < 1)) &&
  (decide (c.item ≠ .fetalEcho) || (c.facilityStandardNotified && decide (c.limitedUltrasoundClaimsThisMonth < 1))) &&
  (!isResidualUrine c.item || decide (c.residualUrineClaimsThisMonth < 2)) &&
  (!isBone c.item || (if c.withinOneYearOfOsteoporosisTreatmentStart
    then decide (c.boneClaimsInFourMonthPeriod < 1) else decide (c.boneClaimsInYear < 1))) &&
  (decide (c.item ≠ .compartmentPressure) || (c.suspectedAcuteCompartmentSyndrome &&
    !c.compartmentDiagnosisAlreadyClaimedAtSameSite)) &&
  (decide (c.item ∉ [.headUpTilt, .artificialPancreas, .subcutaneousGlucose]) || c.facilityStandardNotified) &&
  (decide (c.item ≠ .subcutaneousGlucose) || !isClinic c.facility || decide (c.glucoseClaimsInSixMonthPeriod < 2)) &&
  (decide (c.item ≠ .anorectalFunction) || decide (c.anorectalClaimsThisMonth < 1))

inductive Inclusion where
  | liverStiffness | elastography | principalCerebralDoppler | mechanicalVentilation
  | l008Anesthesia | walkingTest | dailyAlreadyClaimed | seriesAlreadyClaimed
  deriving DecidableEq, Repr

def inclusion (c : Context) : Option Inclusion :=
  if c.item = .elastography ∧ c.liverStiffnessClaimedForPatient = true then some .liverStiffness
  else if c.item = .attenuation ∧ c.liverStiffnessClaimedForPatient = true then some .liverStiffness
  else if c.item = .attenuation ∧ c.elastographyClaimedForPatient = true then some .elastography
  else if c.bothCerebralDopplerPerformed &&
      ((decide (c.item = .continuousCerebralDoppler) && c.cerebralPrincipal == some .mapping) ||
       (decide (c.item = .mappingCerebralDoppler) && c.cerebralPrincipal == some .continuous))
    then some .principalCerebralDoppler
  else if c.simultaneousMechanicalVentilation &&
      (decide (code c.item = 220) || decide (c.item = .oxygenSaturation ∨ c.item = .noninvasiveContinuousBloodPressure))
    then some .mechanicalVentilation
  else if code c.item = 220 ∧ c.sameDayL008Anesthesia = true then some .l008Anesthesia
  else if Cardiorespiratory.monitoringIncludedWithWalking (code c.item) (suffix c.item) c.sameDayWalkingTest
    then some .walkingTest
  else if (isDaily c.item || decide (code c.item = 220 ∧ c.durationMinutes > 180) ||
      (decide (c.item ∈ [.transcutaneousBloodGas, .continuousBloodGas]) && decide (c.durationMinutes > 300)) ||
      (decide (c.item = .intracranialPressure) && decide (c.durationMinutes > 180)) ||
      (decide (c.item = .pulmonaryArteryPressure) && decide (c.durationMinutes > 120)) ||
      (decide (c.item = .invasiveArterialPressure) && decide (c.durationMinutes > 60))) && c.dailyFeeClaimed then some .dailyAlreadyClaimed
  else if c.item ∈ [.invasiveArterialPressure, .centralVenousPressure, .pulmonaryArteryPressure] ∧
      c.catheterSeriesDailyFeeClaimed = true then some .dailyAlreadyClaimed
  else if isSeries c.item && c.seriesAlreadyClaimed then some .seriesAlreadyClaimed
  else none

def ageComponent (i : Item) : PhysiologicalExaminations.Component :=
  match i with
  | .cardiorespiratoryMonitoring | .neonatalMonitoring | .cardioscope | .cardiotachoscope => .cardiorespiratoryMonitoring
  | .transcutaneousBloodGas | .continuousBloodGas => .bloodGasMonitoring
  | .transcutaneousOxygen => .transcutaneousOxygenPartialPressure
  | .deepBodyTemperature => .deepBodyTemperature
  | .peripheralCirculationTemperature => .peripheralCirculatoryObservation
  | _ => .ordinary

def additions (c : Context) : Nat :=
  (if c.contrastUsed && (isTomography c.item || isCardiacEcho c.item) then 180 else 0) +
  (if c.pulsedDopplerPerformed && isTomography c.item then 150 else 0) +
  (if c.item = .fetalEcho && c.fetalEchoDiagnosisPerformed then 1200 else 0) +
  (if c.item = .continuousCerebralDoppler && c.hitsMesDetected then 150 else 0) +
  (if c.item = .thermography && c.thermographyLoadPerformed then 100 else 0) +
  (if c.item = .dexaLumbar && c.dexaFemurSameDay then 90 else 0) +
  (if c.item = .remsLumbar && c.remsFemurSameDay then 55 else 0) +
  (if c.item = .pulmonaryArteryPressure && c.balloonPulmonaryCatheterInserted && c.catheterInsertionStartDay
    then 1300 else 0)

def repeatRate (c : Context) : Nat :=
  if ((code c.item = 215 ∧ suffix c.item = 0 ∧ c.item ≠ .fetalEcho) ∨ c.item = .thermography) ∧
      c.priorExecutionsThisMonth ≥ 1 then 9 else 10

structure Assessment where
  included : Option Inclusion
  baseHundredths : Nat := 0
  additionsHundredths : Nat := 0
  ageAdditionHundredths : Nat := 0
  repeatRateTenths : Nat := 10
  deriving DecidableEq, Repr

def Assessment.totalHundredths (a : Assessment) : Nat :=
  (a.baseHundredths + a.additionsHundredths + a.ageAdditionHundredths) * a.repeatRateTenths / 10

/-- 生体検査通則の年齢加算と接続。計算順序は呼吸循環機能モデルと共通。 -/
def assess (c : Context) : Option Assessment := do
  if !eligible c || (c.bothCerebralDopplerPerformed && c.cerebralPrincipal.isNone) then none else
    let age ← PhysiologicalExaminations.ageGroup c.completedYears c.newborn
    let base ← basePoints c
    match inclusion c with
    | some reason => some { included := some reason }
    | none =>
      let extra := additions c
      let rate := PhysiologicalExaminations.additionRate age (code c.item) (ageComponent c.item)
      some {
        included := none
        baseHundredths := 100 * base
        additionsHundredths := 100 * extra
        ageAdditionHundredths := 10 * (base + extra) * rate
        repeatRateTenths := repeatRate c }

/-- 同時実施と併算定の根拠を一覧から共有する。主たる脳動脈検査は呼出元が選ぶ。 -/
def assessBatch (contexts : List Context) : Option (List Assessment) := do
  let has := fun (item : Item) => contexts.any (fun c => c.item == item && eligible c)
  let prepared := contexts.map (fun c => { c with
    liverStiffnessClaimedForPatient := c.liverStiffnessClaimedForPatient || has .liverStiffness
    elastographyClaimedForPatient := c.elastographyClaimedForPatient || has .elastography
    bothCerebralDopplerPerformed := c.bothCerebralDopplerPerformed ||
      (decide (c.item = Item.continuousCerebralDoppler ∨ c.item = Item.mappingCerebralDoppler) &&
        has Item.continuousCerebralDoppler && has Item.mappingCerebralDoppler) })
  -- 各検査に矛盾した主検査を指定して、両方を算定することを避ける。
  let principals := (prepared.filterMap (fun c => if isDoppler c.item then c.cerebralPrincipal else none)).eraseDups
  if principals.length > 1 then none else
    let result ← prepared.foldlM (fun (state : List Context × List Assessment) original => do
      let prior := state.1
      let count := fun (predicate : Context → Bool) => (prior.filter predicate).length
      let c := { original with
        cerebralPrincipal := original.cerebralPrincipal.orElse (fun _ => principals.head?)
        priorExecutionsThisMonth := original.priorExecutionsThisMonth + count (fun x => x.item == original.item)
        residualUrineClaimsThisMonth := original.residualUrineClaimsThisMonth + count (fun x => isResidualUrine x.item)
        limitedUltrasoundClaimsThisMonth := original.limitedUltrasoundClaimsThisMonth + count (fun x => x.item == original.item)
        boneClaimsInYear := original.boneClaimsInYear + count (fun x => isBone x.item)
        boneClaimsInFourMonthPeriod := original.boneClaimsInFourMonthPeriod + count (fun x => isBone x.item)
        glucoseClaimsInSixMonthPeriod := original.glucoseClaimsInSixMonthPeriod + count (fun x => x.item == Item.subcutaneousGlucose)
        anorectalClaimsThisMonth := original.anorectalClaimsThisMonth + count (fun x => x.item == Item.anorectalFunction)
        compartmentDiagnosisAlreadyClaimedAtSameSite := original.compartmentDiagnosisAlreadyClaimedAtSameSite ||
          prior.any (fun x => x.item == Item.compartmentPressure && x.siteId == original.siteId)
        seriesAlreadyClaimed := original.seriesAlreadyClaimed ||
          prior.any (fun x => x.item == original.item && x.seriesId == original.seriesId)
        dailyFeeClaimed := original.dailyFeeClaimed || prior.any (fun x => x.item == original.item) }
      let a ← assess c
      let prior := if a.included.isNone then prior ++ [c] else prior
      some (prior, state.2 ++ [a])) ([], [])
    some result.2

inductive BundledService where
  | simultaneousRespiratoryCurve
  | recording | contrastInjection | anesthesiaOtherThanL008
  | simultaneousEcg | simultaneousPhonocardiogram | simultaneousPulseWave | simultaneousMechanocardiogram
  | respiratoryMonitoring | bloodGas | cardiacOutput | pulsePressure | fluoroscopy
  | contrastImaging | xrayDiagnosis | sameMonthAngioscopy
  | catheterInsertion | insertionFluoroscopy | insertionImagingAndTests
  deriving DecidableEq, Repr

/-- 包括される費用の根拠。false から別算定可とは判定しない。 -/
def serviceIncluded (c : Context) (service : BundledService) : Bool :=
  match service with
  | .simultaneousRespiratoryCurve => decide (code c.item = 220)
  | .recording => decide ((code c.item = 215 ∧ suffix c.item = 0) ∨ c.item = .thermography)
  | .contrastInjection | .anesthesiaOtherThanL008 => c.contrastUsed && (isTomography c.item || isCardiacEcho c.item) ||
      decide (c.item = .intravascularUltrasound ∧ service = .contrastInjection)
  | .simultaneousEcg | .simultaneousPhonocardiogram | .simultaneousPulseWave | .simultaneousMechanocardiogram =>
      isCardiacEcho c.item
  | .respiratoryMonitoring | .bloodGas | .cardiacOutput | .pulsePressure | .fluoroscopy
  | .contrastImaging | .xrayDiagnosis | .sameMonthAngioscopy => decide (c.item = .intravascularUltrasound)
  | .catheterInsertion | .insertionFluoroscopy => decide (c.item = .invasiveArterialPressure)
  | .insertionImagingAndTests => decide (c.item = .pulmonaryArteryPressure) && c.balloonPulmonaryCatheterInserted

private def req (item : Item) : Context := { item := item }
private def total (c : Context) : Option Nat := (assess c).map Assessment.totalHundredths
private def batchTotal (xs : List Context) : Option Nat :=
  (assessBatch xs).map (fun ys => (ys.map Assessment.totalHundredths).sum)
private def monitor : Context :=
  { item := .cardiorespiratoryMonitoring, durationMinutes := 60, observedEcgCurve := true, observedHeartRate := true }

example : (List.map (fun i => basePoints (req i))
    [.aMode, .tomographyHomeVisit, .tomographyThoracoabdominal, .tomographyLegVessels, .tomographyOther, .transthoracicEcho, .mMode, .transesophagealEcho, .fetalEcho, .stressEcho, .fetalDoppler, .continuousCerebralDoppler, .mappingCerebralDoppler, .intravascularUltrasound]) =
    [some 150, some 400, some 530, some 450, some 350, some 880, some 500, some 1800, some 300, some 2010, some 20, some 150, some 400, some 4290] := by decide
example : total { req .aMode with priorExecutionsThisMonth := 1 } = some 13500 := by decide
example : total { req .liverStiffness with priorExecutionsThisMonth := 1 } = some 20000 := by decide
example : repeatRate { req .fetalEcho with priorExecutionsThisMonth := 1 } = 10 := by decide
example : total { req .tomographyHomeVisit with limitedUltrasoundClaimsThisMonth := 1 } = none := by decide
example : total (req .fetalEcho) = none := by decide
example : total { req .fetalEcho with facilityStandardNotified := true, fetalEchoDiagnosisPerformed := true } = some 150000 := by decide
example : total { req .tomographyThoracoabdominal with contrastUsed := true, pulsedDopplerPerformed := true } = some 86000 := by decide
example : total { req .aMode with contrastUsed := true, pulsedDopplerPerformed := true } = some 15000 := by decide
example : total { req .continuousCerebralDoppler with hitsMesDetected := true } = some 30000 := by decide
example : batchTotal [req .continuousCerebralDoppler, req .mappingCerebralDoppler] = none := by decide
example : batchTotal [{ req .continuousCerebralDoppler with cerebralPrincipal := some .continuous }, req .mappingCerebralDoppler, req .aMode] = some 30000 := by decide
example : batchTotal [req .liverStiffness, req .elastography, req .attenuation] = some 20000 := by decide
example : batchTotal [req .elastography, req .attenuation] = some 20000 := by decide
example : total { req .thermography with thermographyLoadPerformed := true, priorExecutionsThisMonth := 1 } = some 27000 := by decide
example : batchTotal [{ req .residualUrineUltrasound with residualUrineClaimsThisMonth := 1 }, { req .residualUrineCatheter with residualUrineClaimsThisMonth := 1 }] = none := by decide
example : total { req .residualUrineCatheter with residualUrineClaimsThisMonth := 2 } = none := by decide
example : total { req .dexaLumbar with dexaFemurSameDay := true } = some 45000 := by decide
example : total { req .remsLumbar with remsFemurSameDay := true } = some 19500 := by decide
example : total { req .boneUltrasound with boneClaimsInYear := 1 } = none := by decide
example : total { req .boneUltrasound with boneClaimsInYear := 1, withinOneYearOfOsteoporosisTreatmentStart := true } = some 8000 := by decide
example : total { req .boneUltrasound with withinOneYearOfOsteoporosisTreatmentStart := true, boneClaimsInFourMonthPeriod := 1 } = none := by decide
example : batchTotal [req .dexaLumbar, req .boneUltrasound] = none := by decide
example : (List.map (fun m => total { req .laborMonitoring with durationMinutes := m })
    [0, 60, 61, 90, 91]) = [none, some 51000, some 70000, some 70000, some 89000] := by decide
example : total { monitor with observedEcgCurve := false } = none := by decide
example : total { monitor with observedHeartRate := false } = none := by decide
example : (List.map (fun m => total { monitor with durationMinutes := m }) [60, 61, 180, 181]) =
    [some 5000, some 10000, some 15000, some 15000] := by decide
example : (List.map (fun day => total { monitor with durationMinutes := 181, monitoringDay := day })
    [7, 8, 14, 15]) = [some 15000, some 13000, some 13000, some 5000] := by decide
example : total { monitor with simultaneousMechanicalVentilation := true } = some 0 := by decide
example : total { monitor with sameDayL008Anesthesia := true } = some 0 := by decide
example : total { monitor with sameDayWalkingTest := true } = some 0 := by decide
example : total { req .oxygenSaturation with simultaneousMechanicalVentilation := true } = some 0 := by decide
example : total { req .noninvasiveContinuousBloodPressure with simultaneousMechanicalVentilation := true } = some 0 := by decide
example : total { req .compartmentPressure with suspectedAcuteCompartmentSyndrome := true } = some 62000 := by decide
example : total { req .compartmentPressure with suspectedAcuteCompartmentSyndrome := true, compartmentDiagnosisAlreadyClaimedAtSameSite := true } = none := by decide
example : (List.map (fun m => total { req .continuousBloodGas with durationMinutes := m })
    [1, 60, 61, 300, 301]) = [some 10000, some 10000, some 20000, some 50000, some 63000] := by decide
example : total { req .continuousBloodGas with durationMinutes := 301, dailyFeeClaimed := true } = some 0 := by decide
example : (List.map (fun m => total { req .invasiveArterialPressure with durationMinutes := m })
    [60, 61]) = [some 13000, some 26000] := by decide
example : total { req .invasiveArterialPressure with durationMinutes := 61, catheterSeriesDailyFeeClaimed := true } = some 0 := by decide
example : total (req .headUpTilt) = none := by decide
example : total { req .headUpTilt with facilityStandardNotified := true } = some 103000 := by decide
example : (List.map (fun n => total { req .centralVenousPressure with pressureMeasurementCount := n })
    [0, 4, 5]) = [none, some 12000, some 24000] := by decide
example : (List.map (fun m => total { req .intracranialPressure with durationMinutes := m })
    [60, 180, 181]) = [some 20000, some 60000, some 96000] := by decide
example : (List.map (fun m => total { req .pulmonaryArteryPressure with durationMinutes := m })
    [60, 120, 121]) = [some 18000, some 36000, some 57000] := by decide
example : total { req .pulmonaryArteryPressure with durationMinutes := 121, balloonPulmonaryCatheterInserted := true, catheterInsertionStartDay := true } = some 187000 := by decide
example : total { req .artificialPancreas with facilityStandardNotified := true } = some 500000 := by decide
example : total { req .subcutaneousGlucose with facilityStandardNotified := true, glucoseClaimsInSixMonthPeriod := 2 } = none := by decide
example : total { req .subcutaneousGlucose with facilityStandardNotified := true, facility := .hospital 100, glucoseClaimsInSixMonthPeriod := 2 } = some 70000 := by decide
example : total { req .anorectalFunction with anorectalItemCount := 2 } = some 120000 := by decide
example : total { req .anorectalFunction with anorectalItemCount := 2, anorectalClaimsThisMonth := 1 } = none := by decide
example : total { req .aMode with completedYears := 2 } = some 25500 := by decide
example : total { monitor with completedYears := 0, newborn := true } = some 5000 := by decide
example : total { req .continuousBloodGas with durationMinutes := 60, completedYears := 2 } = some 10000 := by decide
example : serviceIncluded { req .transthoracicEcho with contrastUsed := true } .anesthesiaOtherThanL008 = true := by decide
example : serviceIncluded (req .intravascularUltrasound) .sameMonthAngioscopy = true := by decide
example : serviceIncluded monitor .simultaneousRespiratoryCurve = true := by decide

end Sanri.MedicalFee.UltrasoundMonitoring
