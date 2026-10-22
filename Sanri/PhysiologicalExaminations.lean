import Sanri.Examinations

namespace Sanri.MedicalFee.PhysiologicalExaminations

/-! 第３節 生体検査料 通則１・２。
各区分の所定点数・本節への所属は入力する。注に掲げる加算等は本体と別の項目とし、
当該部分の除外を検査本体全体へ拡張しない。新生児の該当性は外部で判定する。 -/

inductive Component where
  | ordinary
  | respiratoryFunctionJudgment -- イ
  | cardiacCatheterTests -- ロ
  | electrocardiogramNote -- ハ
  | stressElectrocardiogramNote1 -- ニ
  /-- 呼吸心拍監視、新生児心拍・呼吸監視、カルジオスコープ、カルジオタコスコープ。 -/
  | cardiorespiratoryMonitoring -- ホ
  /-- 経皮的血液ガス分圧測定、血液ガス連続測定。 -/
  | bloodGasMonitoring -- ヘ
  | transcutaneousOxygenPartialPressure -- ト
  | deepBodyTemperature -- チ
  /-- 前額部・胸部・手掌部・足底部の体表面体温測定による末梢循環不全状態観察。 -/
  | peripheralCirculatoryObservation -- リ
  | electroencephalogramNote2 -- ヌ
  | electroencephalogramJudgment -- ル
  | nerveMuscleJudgment -- ヲ
  | radioisotopeJudgment -- 通則１ ワ
  | endoscopyGeneralRule3 -- 通則１ カ
  | endoscopicUltrasoundAddition -- 通則１ ヨ
  | pharyngealImageAnalysisForInfluenza -- 通則１ タ
  | lungLiverPancreasCatheterTests -- 通則１ レ、通則２のＤ３２５
  deriving DecidableEq, Repr

def commonExclusion : Component → Bool
  | .respiratoryFunctionJudgment | .cardiacCatheterTests | .electrocardiogramNote
  | .stressElectrocardiogramNote1 | .cardiorespiratoryMonitoring | .bloodGasMonitoring
  | .transcutaneousOxygenPartialPressure | .deepBodyTemperature | .peripheralCirculatoryObservation
  | .electroencephalogramNote2 | .electroencephalogramJudgment | .nerveMuscleJudgment => true
  | _ => false

def underThreeExclusion (component : Component) : Bool :=
  commonExclusion component || match component with
    | .radioisotopeJudgment | .endoscopyGeneralRule3 | .endoscopicUltrasoundAddition
    | .pharyngealImageAnalysisForInfluenza | .lungLiverPancreasCatheterTests => true
    | _ => false

/-- 通則２。Ｄ２００〜Ｄ２４２以外では、明示された７区分だけが対象。 -/
def preschoolCode (code : Nat) : Bool :=
  decide ((200 ≤ code ∧ code ≤ 242) ∨ code ∈ [306, 308, 310, 312, 313, 317, 325])

inductive AgeGroup where
  | newborn
  | underThreeNonNewborn
  | threeToUnderSix
  | sixOrOlder
  deriving DecidableEq, Repr

/-- 新生児の外部判定を受け、満年齢との明らかな矛盾は受け付けない。 -/
def ageGroup (completedYears : Nat) (newborn : Bool) : Option AgeGroup :=
  if newborn then if completedYears = 0 then some .newborn else none
  else if completedYears < 3 then some .underThreeNonNewborn
  else if completedYears < 6 then some .threeToUnderSix else some .sixOrOlder

/-- 加算率を十分率で表す（100%=10、70%=7、40%=4）。 -/
def additionRate (age : AgeGroup) (code : Nat) (component : Component) : Nat :=
  match age with
  | .newborn => if underThreeExclusion component then 0 else 10
  | .underThreeNonNewborn => if underThreeExclusion component then 0 else 7
  | .threeToUnderSix => if preschoolCode code && !commonExclusion component then 4 else 0
  | .sixOrOlder => 0

structure Points where
  tenths : Nat
  deriving DecidableEq, Repr

structure Test where
  /-- 第３部通則７の種類数に使う識別子。本体と付随加算が同じ検査なら同じ値を使う。 -/
  kind : Nat
  /-- 区分番号のＤ以降の数字。所属する区分の番号を指定する。 -/
  code : Nat
  component : Component := .ordinary
  scheduledPoints : Nat
  belongsToSection3 : Bool := true
  performed : Bool := true
  deriving DecidableEq, Repr

structure Assessment where
  base : Points
  addition : Points
  rateTenths : Nat
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Points := ⟨a.base.tenths + a.addition.tenths⟩

/-- 所定点数に率を掛け、丸めず1/10点単位で保持する。 -/
def assess (t : Test) (completedYears : Nat) (newborn : Bool := false) : Option Assessment := do
  if !t.belongsToSection3 || !t.performed then none else
    let age ← ageGroup completedYears newborn
    let rate := additionRate age t.code t.component
    some { base := ⟨10 * t.scheduledPoints⟩, addition := ⟨rate * t.scheduledPoints⟩, rateTenths := rate }

/-- 新規項目の点数は有理数側で加算するため、この橋渡しでは０点を入れる。
検査識別子は保持し、第３部通則７の種類数と置換判定に使用する。 -/
def remoteKindEntry (t : Test) : Examinations.TestCharge :=
  { kind := t.kind, scheduledPoints := 0 }

structure DailyAssessment where
  /-- 既存の日次入力の点数と遠隔置換分。新規生体検査の通常点数は次フィールド。 -/
  general : Examinations.Assessment
  additionalPhysiological : Points
  deriving DecidableEq, Repr

def DailyAssessment.total (a : DailyAssessment) : Points :=
  ⟨10 * a.general.total + a.additionalPhysiological.tenths⟩

inductive DailyResult where
  | calculated (details : DailyAssessment)
  | requiresOutsourcingRule
  deriving DecidableEq, Repr

/-- 検査通則への接続。tests は新たな第３節項目で、existing に二重登録しない。
遠隔検査実施料への置換時は、新規項目の本体・年齢加算をさらに加えない。 -/
def assessDaily (existing : Examinations.DailyContext) (tests : List Test)
    (completedYears : Nat) (newborn : Bool := false) : Option DailyResult := do
  let assessments ← tests.mapM (fun t => assess t completedYears newborn)
  let combined := { existing with
    physiologicalTests := existing.physiologicalTests ++ tests.map remoteKindEntry }
  match ← Examinations.assess combined with
  | .requiresOutsourcingRule => some .requiresOutsourcingRule
  | .calculated general =>
    let extra := if Examinations.remoteApplies combined then 0
      else (assessments.map (fun a => a.total.tenths)).sum
    some (.calculated { general := general, additionalPhysiological := ⟨extra⟩ })

private def ordinary : Test := { kind := 1, code := 200, scheduledPoints := 27 }

example : (assess ordinary 0 true).map (fun a => a.total.tenths) = some 540 := by decide
example : (assess ordinary 0).map (fun a => a.total.tenths) = some 459 := by decide
example : (assess ordinary 2).map (fun a => a.total.tenths) = some 459 := by decide
example : (assess ordinary 3).map (fun a => a.total.tenths) = some 378 := by decide
example : (assess ordinary 5).map (fun a => a.total.tenths) = some 378 := by decide
example : (assess ordinary 6).map (fun a => a.total.tenths) = some 270 := by decide
example : assess ordinary 1 true = none := by decide
example : assess { ordinary with belongsToSection3 := false } 2 = none := by decide
example : assess { ordinary with performed := false } 2 = none := by decide
example : (List.map preschoolCode [199, 200, 242, 243, 305, 306, 308, 310, 312, 313, 317, 325, 326]) =
    [false, true, true, false, false, true, true, true, true, true, true, true, false] := by decide
example : additionRate .underThreeNonNewborn 300 .ordinary = 7 := by decide
example : additionRate .threeToUnderSix 300 .ordinary = 0 := by decide
example : additionRate .newborn 325 .lungLiverPancreasCatheterTests = 0 := by decide
example : additionRate .underThreeNonNewborn 325 .lungLiverPancreasCatheterTests = 0 := by decide
example : additionRate .threeToUnderSix 325 .lungLiverPancreasCatheterTests = 4 := by decide
example : (List.map (additionRate .newborn 200)
    [.respiratoryFunctionJudgment, .cardiacCatheterTests, .electrocardiogramNote,
     .stressElectrocardiogramNote1, .cardiorespiratoryMonitoring, .bloodGasMonitoring,
     .transcutaneousOxygenPartialPressure, .deepBodyTemperature, .peripheralCirculatoryObservation,
     .electroencephalogramNote2, .electroencephalogramJudgment, .nerveMuscleJudgment,
     .radioisotopeJudgment, .endoscopyGeneralRule3, .endoscopicUltrasoundAddition,
     .pharyngealImageAnalysisForInfluenza, .lungLiverPancreasCatheterTests]) =
    List.replicate 17 0 := by decide
example : additionRate .threeToUnderSix 200 .electrocardiogramNote = 0 := by decide
example : additionRate .threeToUnderSix 200 .ordinary = 4 := by decide
example : assessDaily {} [ordinary] 2 = some (.calculated ⟨⟨0, 0, 0, 0, 0, 0⟩, ⟨459⟩⟩) := by decide
example : assessDaily { usingInformationCommunicationEquipment := true, patientWithNurseEtc := true }
    [ordinary] 2 = some (.calculated ⟨⟨0, 0, 0, 100, 0, 0⟩, ⟨0⟩⟩) := by decide
example : assessDaily { usingInformationCommunicationEquipment := true, patientWithNurseEtc := true }
    [ordinary, { ordinary with kind := 2, code := 306 }] 2 =
    some (.calculated ⟨⟨0, 0, 0, 150, 0, 0⟩, ⟨0⟩⟩) := by decide
example : assessDaily { usingInformationCommunicationEquipment := true, patientWithNurseEtc := true }
    [ordinary, { ordinary with component := .electrocardiogramNote }] 2 =
    some (.calculated ⟨⟨0, 0, 0, 100, 0, 0⟩, ⟨0⟩⟩) := by decide

theorem sixOrOlder_noAgeAddition (t : Test) : additionRate .sixOrOlder t.code t.component = 0 := rfl

end Sanri.MedicalFee.PhysiologicalExaminations
