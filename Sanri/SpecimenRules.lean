import Sanri.SpecimenCatalog
import Sanri.UrineFecalTests
import Sanri.Logic

namespace Sanri.MedicalFee.SpecimenTests

/-! 添付本文の算定規則。要件は各検査に対する入力であり、施設基準の内容を補わない。
採血・採取１回は collectionId、抗原・ウイルスの種類は analyteId、
一連の検査は seriesId によって呼出元が同定する。 -/

inductive Surgery where
  | none
  | thoracicPart10Section7
  | cardiovascularPart10Section8
  | abdominalPart10Section9
  | k898EtcWithinPart10Section11
  deriving DecidableEq, Repr

inductive AquaporinMethod where
  | elisa | cleia | other
  deriving DecidableEq, Repr

inductive AquaporinHistory where
  | first
  | repeatAfterNegative (changedFindings stronglySuspected diagnosisNeeded
      priorDateRecorded necessityRecorded : Bool)
  | other
  deriving DecidableEq, Repr

structure AquaporinAssessment where
  method : AquaporinMethod
  diagnosisPurpose : Bool
  treatmentEffectAssessment : Bool
  history : AquaporinHistory
  deriving DecidableEq, Repr

structure AspergillusAssessment where
  elisa : Bool
  suspectedChronicProgressivePulmonaryDisease : Bool
  suspectedAllergicBronchopulmonaryDisease : Bool
  guidelineFollowed : Bool
  deriving DecidableEq, Repr

structure Conditions where
  aquaporin : Option AquaporinAssessment := none
  aspergillus : Option AspergillusAssessment := none
  insuranceMedicalInstitution : Bool := true
  performed : Bool := true
  /-- 当該検査の注で要求される施設基準を満たす。 -/
  facilityStandardMet : Bool := false
  /-- 当該検査の注で要求される施設基準に適合し、届出済み。 -/
  facilityNotified : Bool := false
  performedInsideInstitution : Bool := false
  claimsThisMonth : Nat := 0
  malignancyStronglySuspectedFromCareAndNonMarkerTests : Bool := false
  tumorMarkerAlreadyClaimed : Bool := false
  claimsB001_3 : Bool := false
  surgery : Surgery := .none
  /-- 細胞診でベセスダ分類ＡＳＣ－ＵＳと判定された。 -/
  ascUsCytology : Bool := false
  /-- Ｋ８６７：子宮頸部（膣部）切除術の既往。 -/
  historyK867 : Bool := false
  /-- Ｋ８６７－３：子宮頸部摘出術（膣部切断術を含む。）の既往。 -/
  historyK867_3 : Bool := false
  /-- Ｋ８６７－４：子宮頸部異形成上皮又は上皮内癌レーザー照射治療の既往。 -/
  historyK867_4 : Bool := false
  designatedPatient : Bool := false
  inpatient : Bool := false
  concentrationSmear : Bool := false
  sameSpecimenUrineSediment : Bool := false
  urineSedimentIsMain : Bool := false
  generalCulture : Bool := false
  anaerobicCulture : Bool := false
  fungalCulture : Bool := false
  massSpectrometricIdentification : Bool := false
  ultracentrifugalConcentration : Bool := false
  resultsExplainedOnTestDay : Bool := false
  writtenResultsProvided : Bool := false
  deriving DecidableEq, Repr

structure Request where
  code : Code
  number : Nat
  branch : Nat := 0
  /-- catalog の variants の０始まりの添字。 -/
  variant : Nat := 0
  collectionId : Nat := 0
  analyteId : Nat := 0
  seriesId : Nat := 0
  /-- アミノ酸の種類数、ＬＳＴの薬剤数、菌種数、Ｄ０２２の薬剤数。 -/
  quantity : Nat := 1
  conditions : Conditions := {}
  deriving DecidableEq, Repr

inductive ItemResult where
  | charged (base additions : Nat)
  | suppressedByMainUrineSediment
  | missingSource (code : Code) (number branch : Nat)
  deriving DecidableEq, Repr

def d012AspergillusSource : Logic.SourceRef := {
  kind := .notification
  identifier := "保医発0305第6号 別添1"
  edition := "2026-05-01訂正"
  location := "訂正PDF 7–8頁、登録版PDF 377頁 D012(52)"
  verification := .checkedAgainstSource
}

def d014AquaporinSource : Logic.SourceRef := {
  kind := .notification
  identifier := "保医発0430第4号 別添2"
  edition := "2026-06-01適用"
  location := "2026-05-18差替版 PDF 10頁 指示4 D014(26)"
  url := some "https://kouseikyoku.mhlw.go.jp/kantoshinetsu/080525_016.pdf"
  verification := .checkedAgainstSource
}

/-- D014(26)。診断目的と検査歴を呼出元が確認する。 -/
def AquaporinAssessment.eligible (a : AquaporinAssessment) : Bool :=
  decide (a.method = .elisa ∨ a.method = .cleia) &&
  a.diagnosisPurpose && !a.treatmentEffectAssessment &&
  match a.history with
  | .first => true
  | .repeatAfterNegative changed suspected needed dateRecorded necessityRecorded =>
    changed && suspected && needed && dateRecorded && necessityRecorded
  | .other => false

/-- 施設・患者・回数条件。D012の62とD014の46の第1種は
`d012AspergillusSource` と `d014AquaporinSource` の範囲を評価する。 -/
def eligible (r : Request) : Bool :=
  let c := r.conditions
  c.insuranceMedicalInstitution && c.performed &&
  match r.code with
  | .d009 => c.malignancyStronglySuspectedFromCareAndNonMarkerTests &&
      !c.tumorMarkerAlreadyClaimed && !c.claimsB001_3
  | .d010 =>
    if r.number = 8 then c.facilityNotified && decide (c.claimsThisMonth = 0) &&
      (decide (r.branch ≠ 4) || c.performedInsideInstitution)
    else if r.number = 4 then
      if r.branch = 1 then decide (0 < r.quantity ∧ r.quantity < 5)
      else decide (r.branch = 2 ∧ 5 ≤ r.quantity)
    else true
  | .d011 => if r.number = 4 then decide (c.surgery ≠ .none) else true
  | .d012 =>
    if r.number = 56 ∧ r.variant < 2 then c.facilityStandardMet
    else if r.number = 70 then c.facilityNotified
    else if r.number = 62 then c.aspergillus.any (fun a => a.elisa && a.guidelineFollowed &&
      (a.suspectedChronicProgressivePulmonaryDisease || a.suspectedAllergicBronchopulmonaryDisease))
    else true
  | .d014 => if r.number = 46 ∧ r.variant = 0 then c.aquaporin.any AquaporinAssessment.eligible
    else if r.number = 47 ∨ r.number = 49 then c.facilityNotified else true
  | .d016 => if r.number = 7 then
      match r.branch with
      | 1 => decide (r.quantity = 1)
      | 2 => decide (r.quantity = 2)
      | 3 => decide (3 ≤ r.quantity)
      | _ => false
    else true
  | .d019 =>
    if r.number = 1 then decide (r.quantity = 1)
    else if r.number = 2 then decide (r.quantity = 2)
    else if r.number = 3 then decide (3 ≤ r.quantity) else true
  | .d022 => decide (4 ≤ r.quantity)
  | .d023 =>
    if r.number = 10 ∨ r.number = 11 then c.facilityNotified &&
      (c.ascUsCytology || c.historyK867 || c.historyK867_3 || c.historyK867_4)
    else if r.number = 24 ∨ r.number = 25 then c.facilityNotified && c.designatedPatient
    else if r.number = 26 then c.facilityStandardMet &&
      (decide (r.variant ≠ 1) || c.facilityNotified)
    else true
  | .d023_2 => if r.number = 5 then c.facilityStandardMet else true
  | _ => true

/-- Ｄ０２３末尾注の対象を項番号だけで広げない。 -/
def rapidMicrobialEligible (r : Request) : Bool :=
  decide (r.code = .d023) &&
  (decide (r.number = 6 ∧ r.variant = 0) || decide (r.number = 7) ||
   decide (r.number = 13 ∧ (r.variant = 0 ∨ r.variant = 2)) ||
   decide (r.number = 14 ∧ r.variant = 1)) &&
  r.conditions.resultsExplainedOnTestDay && r.conditions.writtenResultsProvided

def additions (r : Request) : Nat :=
  let c := r.conditions
  (if r.code = .d017 ∧ r.number = 1 ∧ c.concentrationSmear = true then 35 else 0) +
  (if r.code = .d018 then
    (if c.generalCulture && c.anaerobicCulture then 137 else 0) +
    (if c.generalCulture && c.fungalCulture then 122 else 0) +
    (if c.inpatient && c.massSpectrometricIdentification then 40 else 0)
   else 0) +
  (if r.code = .d023 ∧ r.number = 18 ∧ c.ultracentrifugalConcentration = true then 130 else 0) +
  (if rapidMicrobialEligible r then 100 else 0)

def assessOne (r : Request) : Option ItemResult := do
  match lookup r.code r.number r.branch with
  | none => some (.missingSource r.code r.number r.branch)
  | some entry =>
    if r.variant ≥ entry.variants.length then none
    else if !eligible r then none
    else if r.code = .d017 ∧ r.conditions.sameSpecimenUrineSediment = true ∧
        r.conditions.urineSedimentIsMain = true then some .suppressedByMainUrineSediment
    else match entry.points with
      | none => some (.missingSource r.code r.number r.branch)
      | some base =>
        let base := if r.code = .d010 ∧ r.number = 4 ∧ r.branch = 1 then base * r.quantity else base
        some (.charged base (additions r))

inductive Bundle where
  | ordinary
  | tumorMarkers
  | hepatitis
  | autoantibodies
  | viralAntibodies
  | classSpecificViralAntibodies
  | specificIgE
  deriving DecidableEq, Repr

def bundle (r : Request) : Bundle :=
  match r.code with
  | .d009 => if 2 ≤ r.number ∧ r.number ≤ 36 then .tumorMarkers else .ordinary
  | .d013 => if 3 ≤ r.number ∧ r.number ≤ 14 then .hepatitis else .ordinary
  | .d014 => if (10 ≤ r.number ∧ r.number ≤ 16) ∨
      r.number ∈ [18, 19, 23, 35, 36] then .autoantibodies else .ordinary
  | .d012 => if r.number = 11 then .viralAntibodies
      else if r.number = 46 then .classSpecificViralAntibodies else .ordinary
  | .d015 => if r.number = 13 then .specificIgE else .ordinary
  | _ => .ordinary

/-- 同一の実施を重複入力しても二重算定しない。一連の検査は採取回数で増やさない。 -/
def identity (r : Request) : Code × Nat × Nat × Nat × Nat × Nat :=
  let series := (r.code = .d016 ∧ r.number ∈ [2, 4, 5]) ∨ r.code = .d021
  (r.code, r.number, r.branch, r.variant,
    if series then r.seriesId else r.collectionId,
    if series then 0 else r.analyteId)

/-- 自己抗体の注１は同一採血という条件を追加せず、今回の算定単位でまとめる。 -/
def sameGroup (a b : Request) : Bool :=
  if bundle a = .ordinary then decide (identity a = identity b)
  else decide (bundle a = bundle b) &&
    (decide (bundle a = .autoantibodies) || decide (a.collectionId = b.collectionId))

def groupedBase (kind : Bundle) (count ordinaryPoints : Nat) : Nat :=
  match kind with
  | .ordinary => ordinaryPoints
  | .tumorMarkers => if count ≥ 4 then 385 else if count = 3 then 290
      else if count = 2 then 230 else ordinaryPoints
  | .hepatitis => if count ≥ 5 then 425 else if count = 4 then 360
      else if count = 3 then 290 else ordinaryPoints
  | .autoantibodies => if count ≥ 3 then 490 else if count = 2 then 320 else ordinaryPoints
  | .viralAntibodies => 79 * min 8 count
  | .classSpecificViralAntibodies => 200 * min 2 count
  | .specificIgE => min 1430 (110 * count)

structure PricedGroup where
  members : List Request
  base : Nat
  additions : Nat
  deriving DecidableEq, Repr

def PricedGroup.total (g : PricedGroup) : Nat := g.base + g.additions

inductive BatchResult where
  | calculated (groups : List PricedGroup)
  | missingSource (items : List (Code × Nat × Nat))
  deriving DecidableEq, Repr

/-- 不適格項目を黙って集計から落とさず、全体を none とする。
欠落資料が１つでもあれば、根拠のない合計を返さず missingSource とする。 -/
def assess (requests : List Request) : Option BatchResult := do
  let results ← requests.mapM assessOne
  let missing := results.filterMap (fun r => match r with
    | .missingSource code number branch => some (code, number, branch)
    | _ => none)
  if !missing.isEmpty then some (.missingSource missing.eraseDups) else
    let billable := requests.filter (fun r => match assessOne r with
      | some (.charged _ _) => true
      | _ => false)
    let keys := (billable.map identity).eraseDups
    let unique := keys.filterMap (fun k => billable.find? (fun r => decide (identity r = k)))
    let leaders := unique.foldl (fun acc r =>
      if acc.any (sameGroup r) then acc else acc ++ [r]) ([] : List Request)
    let groups := leaders.map (fun leader =>
      let members := unique.filter (sameGroup leader)
      let charges := members.filterMap (fun r => match assessOne r with
        | some (.charged base extra) => some (base, extra)
        | _ => none)
      { members := members
        base := groupedBase (bundle leader) members.length ((charges.map Prod.fst).sum)
        additions := (charges.map Prod.snd).sum : PricedGroup })
    some (.calculated groups)

/-- 点数集計のみ。欠落資料は none になるため、理由を要する場合は assess を使う。 -/
def points (requests : List Request) : Option Nat := do
  match ← assess requests with
  | .calculated groups => some ((groups.map PricedGroup.total).sum)
  | .missingSource _ => none

/-- 同一検体でのＤ００２／Ｄ００２－２とＤ０１７を１つの主検査選択で評価する。 -/
def assessSedimentPair (urine : UrineFecalTests.Context) (bacteria : Request)
    (main : UrineFecalTests.MainTest) : Option (UrineFecalTests.Assessment × ItemResult) := do
  if !UrineFecalTests.isSediment urine.item || bacteria.code != .d017 then none else
    let urineResult ← UrineFecalTests.assess { urine with
      sameSpecimenD017Performed := true
      mainTest := main }
    let bacteriaResult ← assessOne { bacteria with conditions := { bacteria.conditions with
      sameSpecimenUrineSediment := true
      urineSedimentIsMain := decide (main = .urineSediment) } }
    some (urineResult, bacteriaResult)

/-- Ｄ００１の点数準用先へ接続する。Ｄ００７・Ｄ００８は今回の添付範囲外。 -/
def urineReferenceTarget : Code → Option UrineFecalTests.ReferenceSection
  | .d009 => some (.other .d009)
  | .d010 => some (.other .d010)
  | .d015 => some .d015
  | _ => none

/-- 準用先の施設・患者条件、注の包括・上限・加算まで適用した結果を使う。
異なる区分の混入や空入力は認めず、欠落資料は準用未解決として保持する。 -/
def assessUrineByReference (urine : UrineFecalTests.Context) (requests : List Request) :
    Option UrineFecalTests.Assessment := do
  match UrineFecalTests.pointRule urine.item with
  | .fixed _ => UrineFecalTests.assess urine
  | .reference target _notes =>
    if requests.isEmpty || requests.any (fun r => urineReferenceTarget r.code != some target) then none
    else match ← assess requests with
      | .missingSource _ => UrineFecalTests.assess { urine with referenceResolution := none }
      | .calculated groups =>
        UrineFecalTests.assess { urine with
          referenceResolution := some {
            target := target
            points := (groups.map PricedGroup.total).sum
            sectionNotesAppliedAndSatisfied := true } }

/-- 算定済みの実施料合計を検査通則へ渡す。迅速加算の個別項目情報は
この集計項目には付けない。項目別の迅速加算は元の検査項目に基づいて別途評価する。 -/
def executionItem (groups : List PricedGroup) (kind : Nat) : Examinations.SpecimenItem :=
  { kind := kind
    executionPoints := (groups.map PricedGroup.total).sum }

def d023BkSource : Logic.SourceRef := {
  kind := .notification
  identifier := "保医発0529第2号 別添1"
  edition := "2026-05-29発出、2026-06-01適用"
  location := "PDF 3頁 指示4 D023(42)"
  verification := .checkedAgainstSource
}

def d023MycobacteriaSource : Logic.SourceRef := {
  kind := .notification
  identifier := "保医発0930第2号 別添1"
  edition := "2026-09-30発出、2026-10-01適用"
  location := "PDF 2頁 指示2 D023(43)"
  verification := .checkedAgainstSource
}

inductive BkIndication where
  | suspectedNephropathy | suspectedHemorrhagicCystitis
  | treatmentEffectAfterBkTreatmentStarted | activationDuringRejectionOrGvhdTreatment
  deriving DecidableEq, Repr

inductive BkSpecimen where
  | plasma | urine | other
  deriving DecidableEq, Repr

structure BkRequest where
  insuranceMedicalInstitution : Bool
  performed : Bool
  specimen : BkSpecimen
  organOrHematopoieticCellTransplant : Bool
  /-- (42)ア〜エの該当判断と摘要に記載した区分。 -/
  indication : Option BkIndication
  recordedIndication : Option BkIndication

/-- D023(42)。準用は17の所定点数を参照する。 -/
def bkReferencePoints (r : BkRequest) : Option Nat := do
  let indication ← r.indication
  if r.insuranceMedicalInstitution && r.performed && r.specimen != .other &&
      r.organOrHematopoieticCellTransplant && r.recordedIndication == some indication then
    (lookup .d023 17 0).bind (·.points)
  else none

inductive MycobacteriaSpecimen where
  | sputum | culturedOrganism | other
  deriving DecidableEq, Repr

inductive MycobacteriaIndication where
  | symptomaticAfterIntravesicalBcgNeedingDifferentiation
  | suspectedPulmonaryTbAndNontuberculousDisease
  deriving DecidableEq, Repr

structure MycobacteriaRequest where
  insuranceMedicalInstitution : Bool
  performed : Bool
  specimen : MycobacteriaSpecimen
  dnaDetectionByPcrRsso : Bool
  panelSize : Nat
  /-- 同一患者の同じ一連の治療における本検査の既算定回数。 -/
  claimsInTreatmentSeries : Nat
  indication : Option MycobacteriaIndication
  recordedIndication : Option MycobacteriaIndication
  necessityRecorded : Bool
  /-- (43)イの担当・常勤・経験年数等を照合した施設要件。 -/
  staffingRequirementMet : Bool

/-- D023(43)。25ロの所定点数を参照する。 -/
def mycobacteriaReferencePoints (r : MycobacteriaRequest) : Option Nat := do
  let indication ← r.indication
  if r.insuranceMedicalInstitution && r.performed && r.specimen != .other &&
      r.dnaDetectionByPcrRsso && decide (28 ≤ r.panelSize ∧ r.claimsInTreatmentSeries = 0) &&
      r.recordedIndication == some indication && r.necessityRecorded && r.staffingRequirementMet then
    (lookup .d023 25 2).bind (·.points)
  else none

example : bkReferencePoints {
    insuranceMedicalInstitution := true, performed := true, specimen := .urine,
    organOrHematopoieticCellTransplant := true, indication := some .suspectedNephropathy,
    recordedIndication := some .suspectedNephropathy } = some 450 := by decide

private def mycobacteriaSample : MycobacteriaRequest := {
  insuranceMedicalInstitution := true, performed := true, specimen := .sputum,
  dnaDetectionByPcrRsso := true, panelSize := 28, claimsInTreatmentSeries := 0,
  indication := some .suspectedPulmonaryTbAndNontuberculousDisease,
  recordedIndication := some .suspectedPulmonaryTbAndNontuberculousDisease,
  necessityRecorded := true, staffingRequirementMet := true
}

example : mycobacteriaReferencePoints mycobacteriaSample = some 963 ∧
    mycobacteriaReferencePoints { mycobacteriaSample with claimsInTreatmentSeries := 1 } = none := by decide

example : assessOne {
    code := .d012, number := 62, conditions := { aspergillus := some ⟨true, true, false, true⟩ }
    } = some (.charged 390 0) := by decide

example : assessOne { code := .d012, number := 62 } = none := by decide

private def qualifyingAquaporin : AquaporinAssessment :=
  { method := .cleia, diagnosisPurpose := true, treatmentEffectAssessment := false, history := .first }

-- 登録版で列挙された測定法はELISA。差替通知はCLEIAを追加する。
example : qualifyingAquaporin.method ≠ .elisa ∧
    assessOne {
      code := .d014, number := 46,
      conditions := { aquaporin := some qualifyingAquaporin } } = some (.charged 1000 0) := by decide

example : assessOne { code := .d014, number := 46, conditions := {
    aquaporin := some { qualifyingAquaporin with
      history := .repeatAfterNegative true true true false true } } } = none := by decide

end Sanri.MedicalFee.SpecimenTests
