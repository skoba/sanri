import Sanri.PhysiologicalExaminations

namespace Sanri.MedicalFee.Cardiorespiratory

/-! 呼吸循環機能検査等の通則１・２、Ｄ２００〜Ｄ２１４－２。
同月の同一検査、一連・開始日・同日実施、主たる検査、施設基準は呼出元で管理する。
点数は1/100点単位で保持し、提示文にない丸めをしない。 -/

inductive Item where
  | lungVolumes | flowVolumeCurve | functionalResidualCapacity | respiratoryGasAnalysis | separateLungFunction
  | oscillationResistance | otherRespiratoryResistance | compliance | airwayResistance
  | pulmonaryViscousResistance | singleBreathDistribution
  | tracerWashout | closingVolume | diffusionCapacity | deadSpace | pulmonaryShunt | basalMetabolism
  | respiratoryJudgment
  | rightHeartCatheter | leftHeartCatheter
  | bodyFluidVolume | extracellularFluidVolume
  | bloodFlow | skinPerfusionPressure | flapBloodFlow | dyeCirculatingFlow | indicatorSkinTemperature
  | cardiacOutput | circulationTime | circulatingBloodVolume | dyeCerebralCirculation
  | endothelialFunction | nitrousOxideCerebralCirculation
  | ecg12Lead | vectorEcg | surfaceHisEcg | portableEventMemoryEcg | latePotential | ecg6Lead
  | externalEcgDiagnosis
  | stressEcg12Lead | stressEcg6Lead | externalStressEcgDiagnosis
  | holter | bodySurfaceEcg | epicardialExcitationMap | implantedEcg | tWaveAlternans
  | treadmillCardiopulmonary | cycleCardiopulmonary | asthmaExercise | timedWalking | shuttleWalking
  | realtimeEcg | portableEventRecorderEcg | phonocardiogram | waveforms | vascularDistensibility
  | electrokymograph
  deriving DecidableEq, Repr

def code : Item → Nat
  | .lungVolumes | .flowVolumeCurve | .functionalResidualCapacity | .respiratoryGasAnalysis
  | .separateLungFunction => 200
  | .oscillationResistance | .otherRespiratoryResistance | .compliance | .airwayResistance
  | .pulmonaryViscousResistance | .singleBreathDistribution => 201
  | .tracerWashout | .closingVolume => 202
  | .diffusionCapacity | .deadSpace | .pulmonaryShunt => 203
  | .basalMetabolism => 204
  | .respiratoryJudgment => 205
  | .rightHeartCatheter | .leftHeartCatheter => 206
  | .bodyFluidVolume | .extracellularFluidVolume | .bloodFlow | .skinPerfusionPressure
  | .flapBloodFlow | .dyeCirculatingFlow | .indicatorSkinTemperature | .cardiacOutput
  | .circulationTime | .circulatingBloodVolume | .dyeCerebralCirculation | .endothelialFunction
  | .nitrousOxideCerebralCirculation => 207
  | .ecg12Lead | .vectorEcg | .surfaceHisEcg | .portableEventMemoryEcg | .latePotential
  | .ecg6Lead | .externalEcgDiagnosis => 208
  | .stressEcg12Lead | .stressEcg6Lead | .externalStressEcgDiagnosis => 209
  | .holter | .bodySurfaceEcg | .epicardialExcitationMap | .implantedEcg | .tWaveAlternans => 210
  | .treadmillCardiopulmonary | .cycleCardiopulmonary | .asthmaExercise | .timedWalking | .shuttleWalking => 211
  | .realtimeEcg | .portableEventRecorderEcg => 212
  | .phonocardiogram => 213
  | .waveforms | .vascularDistensibility | .electrokymograph => 214

/-- 区分の枝番号（例：Ｄ２１０－４は4）。 -/
def suffix : Item → Nat
  | .bodySurfaceEcg | .epicardialExcitationMap | .asthmaExercise | .portableEventRecorderEcg
  | .electrokymograph => 2
  | .implantedEcg | .timedWalking => 3
  | .tWaveAlternans | .shuttleWalking => 4
  | _ => 0

def isCardiacCatheter (i : Item) : Bool := decide (code i = 206)
def isD200 (i : Item) : Bool := decide (code i = 200)
def isD208 (i : Item) : Bool := decide (code i = 208)
def isD211 (i : Item) : Bool := decide (code i = 211 ∧ suffix i = 0)
def isWalking (i : Item) : Bool := decide (i = .timedWalking ∨ i = .shuttleWalking)

inductive Signal where
  | ecgAsPartOfWaveforms
  | other (kind : Nat)
  deriving DecidableEq, Repr

def signalCount (signals : List Signal) : Nat :=
  (signals.filterMap (fun s => match s with
    | .ecgAsPartOfWaveforms => none
    | .other kind => some kind)).eraseDups.length

def maxSimultaneousCount (recordings : List (List Signal)) : Nat :=
  (recordings.map signalCount).foldl max 0

def waveformPoints (count : Nat) : Option Nat :=
  if count = 0 then none else some (
    if count = 1 then 60 else if count = 2 then 80 else if count ≤ 4 then 130
    else if count ≤ 6 then 180 else 220)

inductive CatheterAddition where
  | foramenOrDefect | brockenbrough | conduction | hisBundle | pacing | prematureStimulation
  | coronarySpasmDrugLoad | coronaryAngiography | guidewireMicrocirculation | intracardiacUltrasound
  deriving DecidableEq, Repr

def catheterAdditionPoints : CatheterAddition → Nat
  | .foramenOrDefect => 800
  | .brockenbrough => 2000
  | .conduction | .hisBundle | .pacing | .intracardiacUltrasound => 400
  | .prematureStimulation | .coronarySpasmDrugLoad => 800
  | .coronaryAngiography => 1400
  | .guidewireMicrocirculation => 150

inductive ExclusiveCatheterTest where
  | intravascularUltrasound | opticalTomography | nearInfraredSpectroscopy | flowReserve | angioscopy
  deriving DecidableEq, Repr

inductive FlowReserve where
  | none | ordinary | hemodynamicAnalyzer
  deriving DecidableEq, Repr

structure CatheterContext where
  additions : List CatheterAddition := []
  intravascularUltrasound : Bool := false
  opticalTomography : Bool := false
  nearInfraredSpectroscopy : Bool := false
  flowReserve : FlowReserve := .none
  angioscopy : Bool := false
  angioscopyStandardNotified : Bool := false
  /-- 注７の同月に実施した検査（今回分も関数内で加える）。 -/
  performedEarlierThisMonth : List ExclusiveCatheterTest := []
  principal : Option ExclusiveCatheterTest := none
  /-- 注７で選択した加算を同月に既に算定したか。 -/
  principalAdditionClaimedThisMonth : Bool := false
  /-- 注９のＥ４００の仕様で解決した、実際に使用したフィルムの点数。 -/
  filmPoints : Nat := 0
  deriving DecidableEq, Repr

def currentExclusiveTests (c : CatheterContext) : List ExclusiveCatheterTest :=
  (if c.intravascularUltrasound then [.intravascularUltrasound] else []) ++
  (if c.opticalTomography then [.opticalTomography] else []) ++
  (if c.nearInfraredSpectroscopy then [.nearInfraredSpectroscopy] else []) ++
  (if c.flowReserve != .none then [.flowReserve] else []) ++
  (if c.angioscopy then [.angioscopy] else [])

def exclusivePoints (c : CatheterContext) (test : ExclusiveCatheterTest) : Nat :=
  match test with
  | .flowReserve => if c.flowReserve = .hemodynamicAnalyzer then 7200 else 600
  | _ => 400

/-- 注７。高い点数を自動選択せず、主たる検査の指定を要求する。 -/
def catheterExtras (c : CatheterContext) : Option Nat :=
  if c.angioscopy && !c.angioscopyStandardNotified then none else
    let current := currentExclusiveTests c
    let monthly := (c.performedEarlierThisMonth ++ current).eraseDups
    if monthly.length ≥ 2 && c.principal.isNone then none
    else if c.principal.any (fun p => !monthly.contains p) then none
    else
      let selected := if monthly.length ≥ 2 && c.principalAdditionClaimedThisMonth then []
        else if monthly.length ≥ 2 then current.filter (fun p => c.principal == some p)
        else current
      some ((c.additions.eraseDups.map catheterAdditionPoints).sum +
        (selected.map (exclusivePoints c)).sum)

structure Context where
  item : Item
  insuranceMedicalInstitution : Bool := true
  performed : Bool := true
  completedYears : Nat := 20
  newborn : Bool := false
  priorExecutionsThisMonth : Nat := 0
  /-- 個別規定により90％にしないことが確定した場合だけ指定する。 -/
  repeatExceptionApplies : Bool := false
  respiratoryJudgmentClaimedThisMonth : Bool := false
  durationMinutes : Nat := 0
  facilityStandardMet : Bool := false
  facilityStandardNotified : Bool := false
  asthmaAssessmentOrTreatmentPurpose : Bool := false
  continuousGasAnalysisForSpecifiedPurpose : Bool := false
  cardiacOutputCatheterInserted : Bool := false
  catheterInsertionStartDay : Bool := false
  /-- カテーテル交換・再挿入等による同じ一連の重複算定を避ける。 -/
  seriesAlreadyCharged : Bool := false
  seriesId : Nat := 0
  simultaneousRecordings : List (List Signal) := []
  sameDayStressEcg : Bool := false
  sameDayCardiopulmonaryExercise : Bool := false
  sameDayWalking : Bool := false
  catheter : CatheterContext := {}
  /-- 実際に使用したガスの購入価格（円）。 -/
  gasPurchaseYen : Nat := 0
  deriving DecidableEq, Repr

def halfHourUnits (minutes : Nat) : Nat := (minutes + 29) / 30

def basePoints (c : Context) : Option Nat :=
  match c.item with
  | .lungVolumes => some 90
  | .flowVolumeCurve => some 100
  | .functionalResidualCapacity => some 140
  | .respiratoryGasAnalysis => some 145
  | .separateLungFunction => some 1010
  | .oscillationResistance => some 150
  | .otherRespiratoryResistance => some 60
  | .compliance | .airwayResistance | .pulmonaryViscousResistance | .singleBreathDistribution
  | .tracerWashout | .closingVolume | .deadSpace | .pulmonaryShunt => some 135
  | .diffusionCapacity => some 180
  | .basalMetabolism => some 85
  | .respiratoryJudgment => some 140
  | .rightHeartCatheter => some 3600
  | .leftHeartCatheter => some 4000
  | .bodyFluidVolume | .extracellularFluidVolume => some 60
  | .bloodFlow | .skinPerfusionPressure | .flapBloodFlow | .dyeCirculatingFlow | .indicatorSkinTemperature => some 100
  | .cardiacOutput | .circulationTime | .circulatingBloodVolume | .dyeCerebralCirculation => some 150
  | .endothelialFunction => some 200
  | .nitrousOxideCerebralCirculation => some 1350
  | .ecg12Lead => some 130
  | .vectorEcg | .surfaceHisEcg | .portableEventMemoryEcg => some 150
  | .latePotential => some 200
  | .ecg6Lead => some 90
  | .externalEcgDiagnosis | .externalStressEcgDiagnosis => some 70
  | .stressEcg12Lead => some 380
  | .stressEcg6Lead => some 190
  | .holter => if c.durationMinutes = 0 then none
      else some (if c.durationMinutes ≥ 480 then 1730 else 90 * halfHourUnits c.durationMinutes)
  | .bodySurfaceEcg | .epicardialExcitationMap => some 1500
  | .implantedEcg => if c.durationMinutes = 0 then none else some (90 * halfHourUnits c.durationMinutes)
  | .tWaveAlternans => some 1100
  | .treadmillCardiopulmonary | .cycleCardiopulmonary => some 1600
  | .asthmaExercise => some 800
  | .timedWalking | .shuttleWalking => some 200
  | .realtimeEcg => some 600
  | .portableEventRecorderEcg => some 500
  | .phonocardiogram => some 150
  | .waveforms => waveformPoints (maxSimultaneousCount c.simultaneousRecordings)
  | .vascularDistensibility => some 100
  | .electrokymograph => some 260

inductive Inclusion where
  | d209SameDay | d211SameDay | walkingSameDay | sameSeries | monthlyJudgment
  deriving DecidableEq, Repr

def inclusion (c : Context) : Option Inclusion :=
  if isD208 c.item && c.sameDayStressEcg then some .d209SameDay
  else if (isD200 c.item || isD208 c.item) && c.sameDayCardiopulmonaryExercise then some .d211SameDay
  else if isD200 c.item && c.sameDayWalking then some .walkingSameDay
  else if c.seriesAlreadyCharged && (isCardiacCatheter c.item ||
      decide (c.item = .cardiacOutput ∨ c.item = .endothelialFunction) || isD211 c.item) then some .sameSeries
  else if c.item = .respiratoryJudgment && c.respiratoryJudgmentClaimedThisMonth then some .monthlyJudgment
  else none

/-- 金額・加算を丸めず1/100点単位で保持する。 -/
structure Assessment where
  included : Option Inclusion
  baseHundredths : Nat := 0
  ageAdditionHundredths : Nat := 0
  otherAdditionsHundredths : Nat := 0
  repeatRateTenths : Nat := 10
  gasHundredths : Nat := 0
  filmHundredths : Nat := 0
  deriving DecidableEq, Repr

def Assessment.totalHundredths (a : Assessment) : Nat :=
  (a.baseHundredths + a.ageAdditionHundredths + a.otherAdditionsHundredths) *
    a.repeatRateTenths / 10 + a.gasHundredths + a.filmHundredths

/-- 90％は本体・当該検査の加算に適用し、購入価格由来のガス・Ｅ４００フィルムは別に合算する。 -/
def assess (c : Context) : Option Assessment := do
  if !c.insuranceMedicalInstitution || !c.performed ||
      (c.item = .implantedEcg && !c.facilityStandardMet) ||
      (isWalking c.item && !c.facilityStandardNotified) ||
      (c.item = .asthmaExercise && !c.asthmaAssessmentOrTreatmentPurpose) then none
  else
    let age ← PhysiologicalExaminations.ageGroup c.completedYears c.newborn
    let base ← basePoints c
    match inclusion c with
    | some included => some { included := some included }
    | none =>
      let special ← if isCardiacCatheter c.item then catheterExtras c.catheter else some 0
      let component := if isCardiacCatheter c.item then .cardiacCatheterTests
        else if c.item = .respiratoryJudgment then .respiratoryFunctionJudgment
        else if c.item = .externalEcgDiagnosis then .electrocardiogramNote
        else if c.item = .externalStressEcgDiagnosis then .stressElectrocardiogramNote1 else .ordinary
      let extra := special +
        (if c.item = .cardiacOutput && c.cardiacOutputCatheterInserted && c.catheterInsertionStartDay
          then 1300 else 0) +
        (if c.item = .holter && decide (c.durationMinutes ≥ 7 * 24 * 60) then 320 else 0) +
        (if isD211 c.item && c.continuousGasAnalysisForSpecifiedPurpose then 520 else 0)
      let ageAddition := if isCardiacCatheter c.item then
          match age with
          | .newborn => 300 * base
          | .underThreeNonNewborn => 100 * base
          | _ => 0
        else 10 * (base + extra) * PhysiologicalExaminations.additionRate age (code c.item) component
      some {
        included := none
        baseHundredths := 100 * base
        ageAdditionHundredths := ageAddition
        otherAdditionsHundredths := 100 * extra
        repeatRateTenths := if code c.item ≥ 206 && decide (c.priorExecutionsThisMonth ≥ 1) &&
          !c.repeatExceptionApplies then 9 else 10
        gasHundredths := 10 * c.gasPurchaseYen
        filmHundredths := if isCardiacCatheter c.item then 100 * c.catheter.filmPoints else 0 }

/-- 日次の同日包括を実施一覧から導く。別算定するＤ２００〜Ｄ２０４があれば
Ｄ２０５を１件だけ加える。月内のＤ２０５算定済み情報は各 Context で共有する。 -/
def assessDay (contexts : List Context) : Option (List Assessment) := do
  let performed := contexts.filter (fun c => c.performed)
  let sameDay := contexts.map (fun c => { c with
    sameDayStressEcg := c.sameDayStressEcg || performed.any (fun x => decide (code x.item = 209))
    sameDayCardiopulmonaryExercise := c.sameDayCardiopulmonaryExercise || performed.any (fun x => isD211 x.item)
    sameDayWalking := c.sameDayWalking || performed.any (fun x => isWalking x.item) })
  let prepared := sameDay.foldl (fun acc c =>
    let repeatedLoad := isD211 c.item && acc.any (fun previous =>
      isD211 previous.item && decide (previous.seriesId = c.seriesId))
    acc ++ [{ c with
      seriesAlreadyCharged := c.seriesAlreadyCharged || repeatedLoad
      respiratoryJudgmentClaimedThisMonth := c.respiratoryJudgmentClaimedThisMonth ||
        (decide (c.item = .respiratoryJudgment) &&
          acc.any (fun previous => decide (previous.item = .respiratoryJudgment))) }]) ([] : List Context)
  -- 左右のカテーテル等を同じ一連として二重請求しない。どちらを算定するかは入力する。
  let catheterClaims := prepared.filter (fun c => isCardiacCatheter c.item && !c.seriesAlreadyCharged)
  if (catheterClaims.map (fun c => c.seriesId)).eraseDups.length != catheterClaims.length then none else
  let results ← prepared.mapM assess
  let needsJudgment := prepared.any (fun c =>
    decide (200 ≤ code c.item ∧ code c.item ≤ 204) && (inclusion c).isNone) &&
    !prepared.any (fun c => decide (c.item = .respiratoryJudgment))
  if needsJudgment then
    let judgment ← assess {
      item := .respiratoryJudgment
      respiratoryJudgmentClaimedThisMonth := contexts.any (fun c => c.respiratoryJudgmentClaimedThisMonth) }
    some (results ++ [judgment])
  else some results

/-- Ｄ２２０〜Ｄ２２３－２の監視項目にも使える歩行試験の同日包括判定。 -/
def monitoringIncludedWithWalking (major suffix : Nat) (sameDayWalking : Bool) : Bool :=
  sameDayWalking && decide ((220 ≤ major ∧ major ≤ 222) ∨ (major = 223 ∧ suffix ≤ 2))

inductive CatheterIncludedService where
  | monitoring | bloodGasAnalysis | cardiacOutput | pulsePressure | pulmonaryBloodFlow
  | fluoroscopy | contrastInjectionTechnique | contrastImaging | xrayDiagnosis
  deriving DecidableEq, Repr

/-- Ｄ２０６注８の列挙費用。フィルムはここに含めない。 -/
def includedInCardiacCatheter (_ : CatheterIncludedService) : Bool := true

/-- Ｄ２０７の心拍出量測定の挿入に伴う画像診断・検査は別算定しない。 -/
def insertionImagingAndTestsIncluded (c : Context) : Bool :=
  decide (c.item = .cardiacOutput) && c.cardiacOutputCatheterInserted

/-- Ｄ２１０・Ｄ２１０－３の解析費用は所定点数に含まれる。 -/
def analysisIncluded (i : Item) : Bool := decide (i = .holter ∨ i = .implantedEcg)

private def req (item : Item) : Context := { item := item }
private def total (c : Context) : Option Nat := (assess c).map Assessment.totalHundredths
private def dayTotal (contexts : List Context) : Option Nat :=
  (assessDay contexts).map (fun xs => (xs.map Assessment.totalHundredths).sum)

example : (List.map (fun i => basePoints (req i))
    [.lungVolumes, .flowVolumeCurve, .functionalResidualCapacity, .respiratoryGasAnalysis, .separateLungFunction, .oscillationResistance, .otherRespiratoryResistance, .compliance, .tracerWashout, .closingVolume, .diffusionCapacity, .deadSpace, .basalMetabolism]) =
    [some 90, some 100, some 140, some 145, some 1010, some 150, some 60, some 135, some 135, some 135, some 180, some 135, some 85] := by decide
example : dayTotal [req .lungVolumes, req .flowVolumeCurve] = some 33000 := by decide
example : dayTotal [{ req .lungVolumes with respiratoryJudgmentClaimedThisMonth := true }] = some 9000 := by decide
example : total { req .lungVolumes with priorExecutionsThisMonth := 1 } = some 9000 := by decide
example : total { req .ecg12Lead with priorExecutionsThisMonth := 1 } = some 11700 := by decide
example : total { req .ecg12Lead with priorExecutionsThisMonth := 2, repeatExceptionApplies := true } = some 13000 := by decide
example : total { req .lungVolumes with gasPurchaseYen := 123 } = some 10230 := by decide
example : total { req .lungVolumes with completedYears := 2 } = some 15300 := by decide
example : total { req .rightHeartCatheter with completedYears := 0, newborn := true } = some 1440000 := by decide
example : total { req .leftHeartCatheter with completedYears := 0, newborn := true } = some 1600000 := by decide
example : total { req .rightHeartCatheter with completedYears := 2 } = some 720000 := by decide
example : total { req .leftHeartCatheter with completedYears := 2 } = some 800000 := by decide
example : total { req .rightHeartCatheter with completedYears := 3 } = some 360000 := by decide
example : total { req .externalEcgDiagnosis with completedYears := 0, newborn := true } = some 7000 := by decide
example : catheterExtras { intravascularUltrasound := true, opticalTomography := true } = none := by decide
example : catheterExtras { intravascularUltrasound := true, opticalTomography := true, principal := some .opticalTomography } = some 400 := by decide
example : catheterExtras { flowReserve := .hemodynamicAnalyzer } = some 7200 := by decide
example : catheterExtras { angioscopy := true } = none := by decide
example : catheterExtras { angioscopy := true, angioscopyStandardNotified := true } = some 400 := by decide
example : catheterExtras { intravascularUltrasound := true, performedEarlierThisMonth := [.opticalTomography], principal := some .opticalTomography, principalAdditionClaimedThisMonth := true } = some 0 := by decide
example : total { req .rightHeartCatheter with catheter := { filmPoints := 25 } } = some 362500 := by decide
example : total { req .rightHeartCatheter with seriesAlreadyCharged := true } = some 0 := by decide
example : dayTotal [req .rightHeartCatheter, req .leftHeartCatheter] = none := by decide
example : total { req .cardiacOutput with cardiacOutputCatheterInserted := true, catheterInsertionStartDay := true } = some 145000 := by decide
example : total { req .cardiacOutput with cardiacOutputCatheterInserted := true } = some 15000 := by decide
example : total { req .cardiacOutput with cardiacOutputCatheterInserted := true, seriesAlreadyCharged := true } = some 0 := by decide
example : dayTotal [req .ecg12Lead, req .stressEcg12Lead] = some 38000 := by decide
example : dayTotal [req .lungVolumes, req .ecg12Lead, req .treadmillCardiopulmonary] = some 160000 := by decide
example : dayTotal [req .treadmillCardiopulmonary, req .cycleCardiopulmonary] = some 160000 := by decide
example : total { req .treadmillCardiopulmonary with continuousGasAnalysisForSpecifiedPurpose := true } = some 212000 := by decide
example : (List.map (fun minutes => basePoints { req .holter with durationMinutes := minutes })
    [0, 1, 30, 31, 479, 480]) = [none, some 90, some 90, some 180, some 1440, some 1730] := by decide
example : total { req .holter with durationMinutes := 10079 } = some 173000 := by decide
example : total { req .holter with durationMinutes := 10080 } = some 205000 := by decide
example : total { req .implantedEcg with durationMinutes := 31 } = none := by decide
example : total { req .implantedEcg with durationMinutes := 31, facilityStandardMet := true } = some 18000 := by decide
example : total (req .asthmaExercise) = none := by decide
example : total { req .asthmaExercise with asthmaAssessmentOrTreatmentPurpose := true } = some 80000 := by decide
example : total (req .timedWalking) = none := by decide
example : dayTotal [req .lungVolumes, { req .timedWalking with facilityStandardNotified := true }] = some 20000 := by decide
example : monitoringIncludedWithWalking 223 2 true = true := by decide
example : monitoringIncludedWithWalking 223 3 true = false := by decide
example : (List.map waveformPoints [0, 1, 2, 3, 4, 5, 6, 7]) =
    [none, some 60, some 80, some 130, some 130, some 180, some 180, some 220] := by decide
example : total { req .waveforms with simultaneousRecordings :=
    [[.other 1, .other 2, .ecgAsPartOfWaveforms], [.other 3]] } = some 8000 := by decide
example : total { req .waveforms with simultaneousRecordings :=
    [[.other 1, .other 1, .ecgAsPartOfWaveforms]] } = some 6000 := by decide
example : analysisIncluded .holter = true := rfl
example : analysisIncluded .implantedEcg = true := rfl

example : dayTotal [req .respiratoryJudgment, req .respiratoryJudgment] = some 14000 := by decide
example : total { req .ecg12Lead with completedYears := 2, priorExecutionsThisMonth := 1 } = some 19890 := by decide
example : total { req .cardiacOutput with completedYears := 2, cardiacOutputCatheterInserted := true, catheterInsertionStartDay := true } = some 246500 := by decide

end Sanri.MedicalFee.Cardiorespiratory
