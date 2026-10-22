import Sanri.OutpatientConsultation

namespace Sanri.MedicalFee.Examinations

/-! 第３部通則１〜７、第１節通則、第１款通則１〜３。
本モジュールでは個別区分・薬剤・材料・基本的検体検査実施料の点数を入力する。
各日次入力は同一患者・同一医療機関・同一日にまとめ、履歴は呼出元が管理する。 -/

inductive Reference where
  | listed
  /-- 通則４。未収載で特殊な検査について、最も近似する収載検査を選定済み。 -/
  | closestListedForSpecialUnlisted
  deriving DecidableEq, Repr

inductive OrganScope where
  | notPaired
  | oneSide
  | bothSides
  deriving DecidableEq, Repr

structure TestCharge where
  /-- 同じ種類には同じ識別子を使う（第３節・第４節を通じて共通）。 -/
  kind : Nat
  scheduledPoints : Nat
  reference : Reference := .listed
  organScope : OrganScope := .notPaired
  /-- 対称器官について特則があるときに限り、当該特則で解決した点数。 -/
  pairedOrganExceptionPoints : Option Nat := none
  deriving DecidableEq, Repr

/-- 通則４・５。近似検査も所定点数を使う。左右数による自動的な倍算はしない。 -/
def TestCharge.points (t : TestCharge) : Nat :=
  t.pairedOrganExceptionPoints.getD t.scheduledPoints

structure SpecimenItem where
  kind : Nat
  executionPoints : Nat
  reference : Reference := .listed
  includedInBasicExecutionFee : Bool := false
  /-- 第１款通則３の大臣指定項目への該当。 -/
  designatedRapidTest : Bool := false
  resultsExplainedOnTestDay : Bool := false
  writtenResultsProvided : Bool := false
  careBasedOnResults : Bool := false
  deriving DecidableEq, Repr

def rapidEligible (i : SpecimenItem) : Bool :=
  i.designatedRapidTest && i.resultsExplainedOnTestDay && i.writtenResultsProvided && i.careBasedOnResults

structure SpecimenContext where
  items : List SpecimenItem := []
  /-- 第２款の判断料の算定要件・回数制限は当該款で解決済み。 -/
  judgmentPoints : Nat := 0
  inpatient : Bool := false
  advancedTreatmentHospital : Bool := false
  /-- 第１款通則２の基本的検体検査実施料。対象時は必須。 -/
  basicExecutionPoints : Option Nat := none
  urgent : Bool := false
  performedInsideInstitution : Bool := false
  time : InitialConsultation.Time := {}
  emergencyAdditionClaimedEarlierToday : Bool := false
  rapidAdditionClaimedEarlierToday : Bool := false
  claimEmergencyAddition : Bool := true
  claimRapidAddition : Bool := true
  deriving DecidableEq, Repr

structure SpecimenAssessment where
  execution : Nat
  judgment : Nat
  emergency : Nat
  rapid : Nat
  deriving DecidableEq, Repr

def SpecimenAssessment.total (a : SpecimenAssessment) : Nat :=
  a.execution + a.judgment + a.emergency + a.rapid

def emergencyEligible (c : SpecimenContext) : Bool :=
  !c.inpatient && !c.items.isEmpty && c.urgent && c.performedInsideInstitution &&
    (!c.time.withinDisplayedHours || c.time.holiday || InitialConsultation.deepNight c.time)

/-- 基本的検体検査実施料に含まれる項目を重複算定しない。 -/
def executionPoints (c : SpecimenContext) : Option Nat :=
  if c.inpatient && c.advancedTreatmentHospital then do
    let basic ← c.basicExecutionPoints
    some (basic + ((c.items.filter (fun i => !i.includedInBasicExecutionFee)).map
      SpecimenItem.executionPoints).sum)
  else some ((c.items.map SpecimenItem.executionPoints).sum)

/-- 緊急加算を算定する日は迅速加算を除外する。
先に迅速加算を算定済みの日に緊急加算を追加しようとする場合は none。
通則３は要件を満たした異なる項目を５項目まで数える。 -/
def assessSpecimen (c : SpecimenContext) : Option SpecimenAssessment := do
  let execution ← executionPoints c
  let emergency := emergencyEligible c && c.claimEmergencyAddition &&
    !c.emergencyAdditionClaimedEarlierToday
  if emergency && c.rapidAdditionClaimedEarlierToday then none else
    let rapidCount := ((c.items.filter rapidEligible).map SpecimenItem.kind).eraseDups.length
    let rapid := if !c.inpatient && c.claimRapidAddition &&
        !c.emergencyAdditionClaimedEarlierToday && !emergency
      then 10 * min 5 rapidCount else 0
    some {
      execution := execution
      judgment := c.judgmentPoints
      emergency := if emergency then 200 else 0
      rapid := rapid }

/-- 第３部通則６。委託時の算定方法は大臣の定めで解決する。
指定検査の外部委託だけに使い、院内検査の加算を自動適用しない。 -/
inductive SpecimenSource where
  | none
  | inHouse (context : SpecimenContext)
  | outsourced (resolvedMinisterialPoints : Option Nat)
  deriving DecidableEq, Repr

/-- 通則２の「特に規定する場合」は、その規定で解決した総点数を入力する。
ordinary は実際に患者に施用した薬剤についての第５節の合計点数。 -/
inductive Drugs where
  | none
  | ordinary (section5Points : Nat)
  | specialProvision (resolvedPoints : Nat)
  deriving DecidableEq, Repr

def Drugs.points : Drugs → Nat
  | .none => 0
  | .ordinary n | .specialProvision n => n

structure DailyContext where
  insuranceMedicalInstitution : Bool := true
  specimen : SpecimenSource := .none
  physiologicalTests : List TestCharge := []
  /-- 実際に患者から穿刺・採取した場合だけ、第４節の算定項目を含める。 -/
  collections : List TestCharge := []
  drugs : Drugs := .none
  /-- 実際に使用した大臣指定の特定保険医療材料の第６節の点数。 -/
  section6MaterialPoints : List Nat := []
  usingInformationCommunicationEquipment : Bool := false
  patientWithNurseEtc : Bool := false
  remoteExaminationClaimedEarlierToday : Bool := false
  deriving DecidableEq, Repr

/-- 通則７の種類数。第３節・第４節の所定点数をまとめて置換する。 -/
def remoteKindCount (c : DailyContext) : Nat :=
  ((c.physiologicalTests ++ c.collections).map TestCharge.kind).eraseDups.length

def remoteApplies (c : DailyContext) : Bool :=
  c.usingInformationCommunicationEquipment && c.patientWithNurseEtc && decide (0 < remoteKindCount c)

def remotePoints (c : DailyContext) : Nat :=
  if !remoteApplies c || c.remoteExaminationClaimedEarlierToday then 0
  else if remoteKindCount c = 1 then 100 else 150

structure Assessment where
  section1 : Nat
  section3 : Nat
  section4 : Nat
  remoteExamination : Nat
  drugs : Nat
  section6Materials : Nat
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Nat :=
  a.section1 + a.section3 + a.section4 + a.remoteExamination + a.drugs + a.section6Materials

inductive Result where
  | calculated (details : Assessment)
  /-- 通則６の別定の方法が未入力。０点・算定不可とは区別する。 -/
  | requiresOutsourcingRule
  deriving DecidableEq, Repr

/-- 入力は１日分。通則７の既算定日は第３・４節を再加算せず、置換分も０とする。 -/
def assess (c : DailyContext) : Option Result := do
  if !c.insuranceMedicalInstitution then none else
    let section1 ← match c.specimen with
      | .none => some (some 0)
      | .inHouse specimen => do
          let a ← assessSpecimen specimen
          some (some a.total)
      | .outsourced resolved => some resolved
    match section1 with
    | none => some .requiresOutsourcingRule
    | some section1 =>
      let remote := remoteApplies c
      some (.calculated {
        section1 := section1
        section3 := if remote then 0 else (c.physiologicalTests.map TestCharge.points).sum
        section4 := if remote then 0 else (c.collections.map TestCharge.points).sum
        remoteExamination := if remote then remotePoints c else 0
        drugs := c.drugs.points
        section6Materials := c.section6MaterialPoints.sum })

/-- Ａ００２注６ただし書に、解決済みの迅速加算を接続する。
検体検査の本体や緊急加算を、この加算として転記しない。 -/
def outpatientAdditions (a : SpecimenAssessment)
    (existing : OutpatientConsultation.Additions := {}) : OutpatientConsultation.Additions :=
  { existing with
    specimenTestGeneralRule3Eligible := decide (a.rapid > 0)
    specimenTestGeneralRule3Points := a.rapid }

/-! 点数は通則の動作を確認する仮の入力であり、個別区分の実点数ではない。 -/
private def rapidItem (kind : Nat) : SpecimenItem :=
  { kind := kind
    executionPoints := 20
    designatedRapidTest := true
    resultsExplainedOnTestDay := true
    writtenResultsProvided := true
    careBasedOnResults := true }
private def specimen : SpecimenContext :=
  { items := [rapidItem 1]
    judgmentPoints := 30 }
private def daily : DailyContext :=
  { specimen := .inHouse specimen
    physiologicalTests := [⟨1, 50, .listed, .notPaired, none⟩]
    collections := [⟨2, 10, .listed, .notPaired, none⟩]
    drugs := .ordinary 5
    section6MaterialPoints := [3, 4] }
private def dailyTotal (c : DailyContext) : Option Nat := do
  let r ← assess c
  match r with
  | .calculated a => some a.total
  | .requiresOutsourcingRule => none

example : assessSpecimen specimen = some ⟨20, 30, 0, 10⟩ := by decide
example : assessSpecimen { specimen with
    items := (List.range 6).map rapidItem } = some ⟨120, 30, 0, 50⟩ := by decide
example : assessSpecimen { specimen with
    items := [rapidItem 1, rapidItem 1] } = some ⟨40, 30, 0, 10⟩ := by decide
example : (assessSpecimen { specimen with
    items := [{ rapidItem 1 with writtenResultsProvided := false }] }).map
    SpecimenAssessment.rapid = some 0 := by decide
example : (assessSpecimen { specimen with
    items := [{ rapidItem 1 with resultsExplainedOnTestDay := false }] }).map
    SpecimenAssessment.rapid = some 0 := by decide
example : (assessSpecimen { specimen with
    items := [{ rapidItem 1 with careBasedOnResults := false }] }).map
    SpecimenAssessment.rapid = some 0 := by decide
example : (assessSpecimen { specimen with
    items := [{ rapidItem 1 with designatedRapidTest := false }] }).map
    SpecimenAssessment.rapid = some 0 := by decide
example : (assessSpecimen { specimen with inpatient := true }).map
    SpecimenAssessment.rapid = some 0 := by decide
example : assessSpecimen { specimen with
    urgent := true
    performedInsideInstitution := true
    time := { holiday := true } } = some ⟨20, 30, 200, 0⟩ := by decide
example : (assessSpecimen { specimen with
    urgent := true
    performedInsideInstitution := true }).map SpecimenAssessment.emergency = some 0 := by decide
example : (assessSpecimen { specimen with
    urgent := true
    time := { holiday := true } }).map SpecimenAssessment.emergency = some 0 := by decide
example : (assessSpecimen { specimen with
    urgent := true
    performedInsideInstitution := true
    time := { minute := 1320 } }).map SpecimenAssessment.emergency = some 200 := by decide
example : assessSpecimen { specimen with
    urgent := true
    performedInsideInstitution := true
    rapidAdditionClaimedEarlierToday := true
    time := { holiday := true } } = none := by decide
example : assessSpecimen { specimen with
    emergencyAdditionClaimedEarlierToday := true } = some ⟨20, 30, 0, 0⟩ := by decide
example : executionPoints { specimen with
    inpatient := true
    advancedTreatmentHospital := true } = none := by decide
example : executionPoints { specimen with
    inpatient := true
    advancedTreatmentHospital := true
    basicExecutionPoints := some 100
    items := [{ rapidItem 1 with includedInBasicExecutionFee := true }, rapidItem 2] } =
    some 120 := by decide
example : executionPoints { specimen with
    advancedTreatmentHospital := true
    basicExecutionPoints := some 100 } = some 20 := by decide

example : dailyTotal daily = some 132 := by decide
example : dailyTotal { daily with drugs := .specialProvision 2 } = some 129 := by decide
example : dailyTotal { daily with collections := [] } = some 122 := by decide
example : dailyTotal { daily with
    usingInformationCommunicationEquipment := true
    patientWithNurseEtc := true } = some 222 := by decide
example : dailyTotal { daily with
    usingInformationCommunicationEquipment := true
    patientWithNurseEtc := true
    collections := [] } = some 172 := by decide
example : dailyTotal { daily with
    usingInformationCommunicationEquipment := true
    patientWithNurseEtc := true
    remoteExaminationClaimedEarlierToday := true } = some 72 := by decide
example : dailyTotal { daily with usingInformationCommunicationEquipment := true } = some 132 := by decide
example : remotePoints {} = 0 := by decide
example : remoteKindCount { daily with
    collections := [⟨1, 10, .listed, .notPaired, none⟩] } = 1 := by decide
example : TestCharge.points ⟨1, 50, .listed, .bothSides, none⟩ = 50 := rfl
example : TestCharge.points ⟨1, 50, .listed, .oneSide, none⟩ = 50 := rfl
example : TestCharge.points ⟨1, 50, .listed, .oneSide, some 25⟩ = 25 := rfl
example : TestCharge.points ⟨1, 50, .closestListedForSpecialUnlisted, .notPaired, none⟩ = 50 := rfl
example : assess { daily with specimen := .outsourced none } =
    some .requiresOutsourcingRule := by decide
example : dailyTotal { daily with specimen := .outsourced (some 40) } = some 112 := by decide
example : assess { daily with insuranceMedicalInstitution := false } = none := by decide
example : (outpatientAdditions ⟨20, 30, 0, 50⟩).specimenTestGeneralRule3Points = 50 := rfl
example : (outpatientAdditions ⟨20, 30, 200, 0⟩).specimenTestGeneralRule3Eligible = false := rfl

theorem pairedOrgans_noAutomaticDoubling (t : TestCharge)
    (h : t.pairedOrganExceptionPoints = none) : t.points = t.scheduledPoints := by
  simp [TestCharge.points, h]

end Sanri.MedicalFee.Examinations
