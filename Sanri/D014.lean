import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment

/-! D014、基準診療日2026-10-22の外来検体検査実施料。 -/
namespace Sanri.MedicalFee.D014

open Sanri.Logic Sanri.History

inductive Item where
  | cold
  | rf
  | thyroglobulinSemi
  | microsomal
  | donath
  | anaQual
  | anaSemi
  | anaQuant
  | insulin
  | anaOther
  | galactoseQual
  | galactoseQuant
  | mmp3
  | thyroglobulin
  | tpo
  | jo1Qual
  | jo1Semi
  | jo1Quant
  | rnpQual
  | rnpSemi
  | rnpQuant
  | smQual
  | smSemi
  | smQuant
  | c1q
  | ssbQual
  | ssbSemi
  | ssbQuant
  | sclQual
  | sclSemi
  | sclQuant
  | dnaQuant
  | dnaQual
  | ssaQual
  | ssaSemi
  | ssaQuant
  | rnaPolymerase
  | centromereQuant
  | centromereQual
  | mitochondrialQual
  | mitochondrialSemi
  | mitochondrialQuant
  | rfComplex
  | ars
  | ccpQual
  | ccpQuant
  | iggRf
  | trab
  | lkm1
  | cardiolipinComplex
  | cardiolipinIgg
  | cardiolipinIgm
  | beta2Igg
  | beta2Igm
  | igg2Tia
  | mpoAnca
  | pr3Anca
  | gbm
  | lupusQuant
  | lupusQual
  | dsg3
  | bp180
  | tif1
  | mi2
  | mda5
  | anca
  | dsg1
  | tsab
  | igg4
  | igg2Nephelometry
  | gm1
  | gq1b
  | skinCombo
  | achr
  | glutamate
  | aqp4
  | musk
  | vgcc
  | nf155
  | cntn1
  | hlaScreen
  | gmCsf
  | hlaIdentify
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .cold => 1
  | .rf => 2
  | .thyroglobulinSemi => 3
  | .microsomal => 3
  | .donath => 4
  | .anaQual => 5
  | .anaSemi => 5
  | .anaQuant => 5
  | .insulin => 6
  | .anaOther => 7
  | .galactoseQual => 8
  | .galactoseQuant => 8
  | .mmp3 => 9
  | .thyroglobulin => 10
  | .tpo => 11
  | .jo1Qual => 12
  | .jo1Semi => 12
  | .jo1Quant => 12
  | .rnpQual => 13
  | .rnpSemi => 13
  | .rnpQuant => 13
  | .smQual => 14
  | .smSemi => 14
  | .smQuant => 14
  | .c1q => 15
  | .ssbQual => 15
  | .ssbSemi => 15
  | .ssbQuant => 15
  | .sclQual => 16
  | .sclSemi => 16
  | .sclQuant => 16
  | .dnaQuant => 17
  | .dnaQual => 17
  | .ssaQual => 18
  | .ssaSemi => 18
  | .ssaQuant => 18
  | .rnaPolymerase => 19
  | .centromereQuant => 20
  | .centromereQual => 20
  | .mitochondrialQual => 21
  | .mitochondrialSemi => 21
  | .mitochondrialQuant => 22
  | .rfComplex => 22
  | .ars => 23
  | .ccpQual => 24
  | .ccpQuant => 24
  | .iggRf => 25
  | .trab => 26
  | .lkm1 => 27
  | .cardiolipinComplex => 28
  | .cardiolipinIgg => 29
  | .cardiolipinIgm => 29
  | .beta2Igg => 29
  | .beta2Igm => 29
  | .igg2Tia => 30
  | .mpoAnca => 31
  | .pr3Anca => 31
  | .gbm => 32
  | .lupusQuant => 33
  | .lupusQual => 33
  | .dsg3 => 34
  | .bp180 => 34
  | .tif1 => 35
  | .mi2 => 35
  | .mda5 => 36
  | .anca => 37
  | .dsg1 => 38
  | .tsab => 39
  | .igg4 => 40
  | .igg2Nephelometry => 41
  | .gm1 => 42
  | .gq1b => 42
  | .skinCombo => 43
  | .achr => 44
  | .glutamate => 45
  | .aqp4 => 46
  | .musk => 46
  | .vgcc => 46
  | .nf155 => 46
  | .cntn1 => 46
  | .hlaScreen => 47
  | .gmCsf => 48
  | .hlaIdentify => 49

def Item.variant : Item → Nat
  | .microsomal => 1
  | .anaSemi => 1
  | .anaQuant => 2
  | .galactoseQuant => 1
  | .jo1Semi => 1
  | .jo1Quant => 2
  | .rnpSemi => 1
  | .rnpQuant => 2
  | .smSemi => 1
  | .smQuant => 2
  | .ssbQual => 1
  | .ssbSemi => 2
  | .ssbQuant => 3
  | .sclSemi => 1
  | .sclQuant => 2
  | .dnaQual => 1
  | .ssaSemi => 1
  | .ssaQuant => 2
  | .centromereQual => 1
  | .mitochondrialSemi => 1
  | .rfComplex => 1
  | .ccpQuant => 1
  | .cardiolipinIgm => 1
  | .beta2Igg => 2
  | .beta2Igm => 3
  | .pr3Anca => 1
  | .lupusQual => 1
  | .bp180 => 1
  | .mi2 => 1
  | .gq1b => 1
  | .musk => 1
  | .vgcc => 2
  | .nf155 => 3
  | .cntn1 => 4
  | _ => 0

def Item.points : Item → Nat
  | .cold => 11
  | .rf => 30
  | .thyroglobulinSemi => 37
  | .microsomal => 37
  | .donath => 55
  | .anaQual => 99
  | .anaSemi => 99
  | .anaQuant => 99
  | .insulin => 107
  | .anaOther => 110
  | .galactoseQual => 111
  | .galactoseQuant => 111
  | .mmp3 => 116
  | .thyroglobulin => 136
  | .tpo => 138
  | .jo1Qual => 140
  | .jo1Semi => 140
  | .jo1Quant => 140
  | .rnpQual => 144
  | .rnpSemi => 144
  | .rnpQuant => 144
  | .smQual => 147
  | .smSemi => 147
  | .smQuant => 147
  | .c1q => 153
  | .ssbQual => 153
  | .ssbSemi => 153
  | .ssbQuant => 153
  | .sclQual => 157
  | .sclSemi => 157
  | .sclQuant => 157
  | .dnaQuant => 159
  | .dnaQual => 159
  | .ssaQual => 161
  | .ssaSemi => 161
  | .ssaQuant => 161
  | .rnaPolymerase => 166
  | .centromereQuant => 173
  | .centromereQual => 173
  | .mitochondrialQual => 181
  | .mitochondrialSemi => 181
  | .mitochondrialQuant => 189
  | .rfComplex => 189
  | .ars => 190
  | .ccpQual => 193
  | .ccpQuant => 193
  | .iggRf => 198
  | .trab => 208
  | .lkm1 => 215
  | .cardiolipinComplex => 223
  | .cardiolipinIgg => 226
  | .cardiolipinIgm => 226
  | .beta2Igg => 226
  | .beta2Igm => 226
  | .igg2Tia => 239
  | .mpoAnca => 250
  | .pr3Anca => 250
  | .gbm => 257
  | .lupusQuant => 265
  | .lupusQual => 265
  | .dsg3 => 270
  | .bp180 => 270
  | .tif1 => 270
  | .mi2 => 270
  | .mda5 => 275
  | .anca => 290
  | .dsg1 => 300
  | .tsab => 330
  | .igg4 => 373
  | .igg2Nephelometry => 388
  | .gm1 => 460
  | .gq1b => 460
  | .skinCombo => 490
  | .achr => 752
  | .glutamate => 970
  | .aqp4 => 1000
  | .musk => 1000
  | .vgcc => 1000
  | .nf155 => 1000
  | .cntn1 => 1000
  | .hlaScreen => 1000
  | .gmCsf => 1380
  | .hlaIdentify => 4850

def ledgerItems : List Item :=
  [.cold, .rf, .thyroglobulinSemi, .microsomal, .donath, .anaQual,
   .anaSemi, .anaQuant, .insulin, .anaOther, .galactoseQual, .galactoseQuant,
   .mmp3, .thyroglobulin, .tpo, .jo1Qual, .jo1Semi, .jo1Quant,
   .rnpQual, .rnpSemi, .rnpQuant, .smQual, .smSemi, .smQuant,
   .c1q, .ssbQual, .ssbSemi, .ssbQuant, .sclQual, .sclSemi,
   .sclQuant, .dnaQuant, .dnaQual, .ssaQual, .ssaSemi, .ssaQuant,
   .rnaPolymerase, .centromereQuant, .centromereQual, .mitochondrialQual, .mitochondrialSemi, .mitochondrialQuant,
   .rfComplex, .ars, .ccpQual, .ccpQuant, .iggRf, .trab,
   .lkm1, .cardiolipinComplex, .cardiolipinIgg, .cardiolipinIgm, .beta2Igg, .beta2Igm,
   .igg2Tia, .mpoAnca, .pr3Anca, .gbm, .lupusQuant, .lupusQual,
   .dsg3, .bp180, .tif1, .mi2, .mda5, .anca,
   .dsg1, .tsab, .igg4, .igg2Nephelometry, .gm1, .gq1b,
   .skinCombo, .achr, .glutamate, .aqp4, .musk, .vgcc,
   .nf155, .cntn1, .hlaScreen, .gmCsf, .hlaIdentify]

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF186–188頁 D014 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (pages : String) (n : Nat) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF" ++ pages ++ "頁 D014(" ++ toString n ++ ")", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def rateRule (i : Item) : Rule Item Nat :=
  ⟨"primary/D014/item/" ++ toString i.number,
    primary (toString i.number), fun item p => item = i → p = i.points⟩

def rates := ledgerItems.map rateRule

theorem rate_iff (i : Item) (p : Nat) : Satisfies rates i p ↔ p = i.points := by
  constructor
  · intro h
    have hi : i ∈ ledgerItems := by cases i <;> decide
    exact h (rateRule i) (List.mem_map.mpr ⟨i, hi, rfl⟩) rfl
  · intro h r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro eq
    simpa [eq] using h

inductive Method where
  | eclia | lectinEnzyme | elisa | cleia | clia | fia | latex | russellViper
  | phospholipidNeutralization | indirectFluorescence | nephelometry | tia
  | ria | immunochromatography
  deriving DecidableEq

/-- 医学的判断は、この列挙の個別条件について独立に確認する。 -/
inductive Finding where
  | diffuseSclerodermaDiagnosis | positiveInitialRna | highRenalCrisisRisk | renalCrisis
  | pbcOrSclerodermaDiagnosisOrPlanning | raUnconfirmed | priorCcpNegative | raDrugReselectionNeeded
  | excludesViralAlcoholDrugLiverDisease | suspectedAnaNegativeAutoimmuneHepatitis
  | apsDiagnosis | suspectedPrimaryImmunodeficiency | rapidlyProgressiveGnDiagnosisOrFollowUp
  | gbmNephritisOrGoodpastureDiagnosisOrPlanning | suspectedPemphigusUnderCriteria
  | pemphigusTreatmentMonitoring | vulgarisMonitoring | foliaceusMonitoring
  | bullousPemphigoidDifferentialOrMonitoring | dermatomyositisUnderCriteria
  | suspectedGuillainBarre | suspectedFisher | diagnosticVisit | suspectedBullousPemphigoid
  | pemphigusOrPemphigoidDifferential | myastheniaDiagnosisOrFollowUp
  | rasmussenOrSpecifiedEpilepsyOrOpsoclonusDiagnosis
  | lambertEatonDiagnosis | symptomaticLambertEaton | abnormalRepetitiveStimulation
  | vgccMedicallyNecessary | cidpOrNodopathyDiagnosisWithoutMonitoring | suspectedNodopathyRelapse
  | itemPositiveInitially | priorTransplantOrListed | hlaRepeatNecessary
  | suspectedAutoimmunePulmonaryAlveolarProteinosis | positiveHlaScreen
  | confirmsAntibodyMediatedRejectionOrHlaAcquisition | rejectionFollowUp
  | listedAndDesensitizedAfterPositiveIdentification
  deriving DecidableEq

inductive Purpose where
  | diagnosis | treatmentSelection | diseaseActivity
  deriving DecidableEq

inductive Window where
  | threeMonths | sixMonths | oneYear
  deriving DecidableEq

inductive Remark where
  | ccpValue | ccpNecessity | negativeAnaDate | aqp4PriorDate | aqp4Necessity
  | vgccDetailedReason | nodopathyNecessity | hlaChartReasonAndNecessity | hlaClaimReasonAndNecessity
  deriving DecidableEq

structure Context where
  performance : Performance Item
  method : Option Method := none
  finding : Finding → Option Bool := fun _ => none
  purpose : Option Purpose := none
  /-- 対象の併施範囲全体に対する実施一覧と算定選択。 -/
  combined : Option (List Item × List Item) := none
  simultaneous : Option (List (Performance Item) × List (Performance Item)) := none
  priorClaims : Option (ClaimHistory Item) := none
  /-- 同じ検査目的・病態段階に絞った履歴。質的に異なる目的を共有枠にしない。 -/
  purposeClaims : Option (ClaimHistory Item) := none
  /-- 起算を確認した照会期間。 -/
  window : Window → Option Period := fun _ => none
  treatmentSeries : Option (List (Performance Item)) := none
  facilityComplies : Option Bool := none
  facilityFilingConfirmed : Option Bool := none
  aquaporin : Option SpecimenTests.AquaporinAssessment := none

def Context.item (c : Context) := c.performance.item
def Confirmed (c : Context) (f : Finding) : Prop := c.finding f = some true
def Uses (c : Context) (methods : List Method) : Prop := ∃ m ∈ methods, c.method = some m

def sameTest (i j : Item) : Bool :=
  if i.number = 24 then j.number == 24 else i == j

def prior (c : Context) (history : Option (ClaimHistory Item)) (period : Period) : Option Nat :=
  history.bind fun h => count h ⟨c.performance.site.patient, none, period⟩ (sameTest c.item)

def Context.totalPrior (c : Context) := prior c c.priorClaims (Period.through c.performance.site.date)
def Context.purposePrior (c : Context) := prior c c.purposeClaims (Period.through c.performance.site.date)

def Within (c : Context) (w : Window) (history : Option (ClaimHistory Item)) (max : Nat) : Prop :=
  ∃ period n, c.window w = some period ∧ period.Contains c.performance.site.date ∧
    prior c history period = some n ∧ n ≤ max

def DistinctSelected (c : Context) (items : List Item) (threshold limit : Nat) : Prop :=
  c.item ∈ items → ∃ performed selected, c.combined = some (performed, selected) ∧
    c.item ∈ selected ∧ selected.Nodup ∧ performed.Nodup ∧
    (∀ i ∈ selected, i ∈ performed) ∧
    (threshold ≤ (performed.filter (· ∈ items)).length →
      (selected.filter (· ∈ items)).length ≤ limit)

def PairChoice (c : Context) (as bs : List Item) : Prop :=
  c.item ∈ as ++ bs → ∃ performed selected, c.combined = some (performed, selected) ∧
    c.item ∈ selected ∧ (∀ i ∈ selected, i ∈ performed) ∧
    (∀ a ∈ as, ∀ b ∈ bs, a ∈ selected → b ∉ selected)

private def noticeRule (n : Nat) (pages : String) (condition : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D014/paragraph/" ++ toString n, notice pages n, fun c _ => condition c⟩

private def branchRule (n : Nat) (branch pages : String) (condition : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D014/paragraph/" ++ toString n ++ "/" ++ branch, notice pages n, fun c _ => condition c⟩

private def rheumatoidGroup : List Item := [.galactoseQual, .galactoseQuant, .mmp3, .c1q, .rfComplex, .iggRf]
private def ccpItems : List Item := [.ccpQual, .ccpQuant]
private def joItems : List Item := [.jo1Qual, .jo1Semi, .jo1Quant]
private def apsItems : List Item := [.cardiolipinIgg, .cardiolipinIgm, .beta2Igg, .beta2Igm]
private def skinMethods : List Method := [.elisa, .cleia]

def rheumatoidLimit := noticeRule 1 "379" fun c =>
  DistinctSelected c (.rf :: rheumatoidGroup) 3 2

def galactoseMethod := noticeRule 2 "379" fun c =>
  (c.item ∈ [.galactoseQual, .galactoseQuant] → Uses c [.eclia, .lectinEnzyme]) ∧
    PairChoice c [.galactoseQual, .galactoseQuant] [.rf]

def thyroidChoice := noticeRule 3 "380" fun c => PairChoice c [.tpo] [.microsomal]

def rnaPolymerase := noticeRule 4 "380" fun c => c.item = .rnaPolymerase →
  (c.purpose = some .diagnosis ∧ Confirmed c .diffuseSclerodermaDiagnosis ∧ c.purposePrior = some 0) ∨
  (Confirmed c .positiveInitialRna ∧
    ((c.purpose = some .treatmentSelection ∧ Confirmed c .highRenalCrisisRisk) ∨
      (c.purpose = some .diseaseActivity ∧ Confirmed c .renalCrisis)) ∧
      Within c .threeMonths c.purposeClaims 0)

def centromere := noticeRule 5 "380" fun c => c.item ∈ [.centromereQuant, .centromereQual] →
  Confirmed c .pbcOrSclerodermaDiagnosisOrPlanning

def arsChoice := noticeRule 6 "380" fun c => PairChoice c [.ars] joItems

def CcpDiagnosis (c : Context) : Prop :=
  Confirmed c .raUnconfirmed ∧
    (c.purposePrior = some 0 ∨ (Confirmed c .priorCcpNegative ∧ Within c .threeMonths c.purposeClaims 0))

def CcpTreatment (c : Context) : Prop :=
  c.purposePrior = some 0 ∨ (Confirmed c .raDrugReselectionNeeded ∧ Within c .sixMonths c.purposeClaims 0)

def ccpParagraph := noticeRule 7 "380" fun c => c.item ∈ ccpItems →
  c.purpose = some .diagnosis ∨ c.purpose = some .treatmentSelection

def ccpPurpose := branchRule 7 "a" "380" fun c => c.item ∈ ccpItems →
  (c.purpose = some .diagnosis ∧ CcpDiagnosis c) ∨ (c.purpose = some .treatmentSelection ∧ CcpTreatment c)

def ccpDiagnosis := branchRule 7 "a/i" "380" fun c =>
  c.item ∈ ccpItems → c.purpose = some .diagnosis → CcpDiagnosis c

def ccpTreatment := branchRule 7 "a/ro" "380" fun c =>
  c.item ∈ ccpItems → c.purpose = some .treatmentSelection → CcpTreatment c

def ccpChoice := branchRule 7 "i" "380" fun c =>
  DistinctSelected c (ccpItems ++ rheumatoidGroup) 2 1

def thyroidStimulation := noticeRule 8 "380" fun c => c.item ∈ [.trab, .tsab] →
  ∃ performed selected, c.simultaneous = some (performed, selected) ∧ c.performance ∈ selected ∧
    (∀ e ∈ selected, e ∈ performed) ∧
    (∀ e ∈ selected, e.item ∈ [.trab, .tsab] → e.item ≠ c.item →
      c.performance.simultaneousWith e = some false)

def lkmParagraph := noticeRule 9 "380" fun c => c.item = .lkm1 →
  Confirmed c .excludesViralAlcoholDrugLiverDisease ∧ Confirmed c .suspectedAnaNegativeAutoimmuneHepatitis

def lkmClinical := branchRule 9 "a" "380" fun c => c.item = .lkm1 →
  Confirmed c .excludesViralAlcoholDrugLiverDisease ∧ Confirmed c .suspectedAnaNegativeAutoimmuneHepatitis

def cardiolipinChoice := noticeRule 10 "380" fun c => PairChoice c [.cardiolipinComplex] apsItems

def ApsSeries (c : Context) : Prop :=
  c.performance.series.isSome = true ∧ ∃ prior, c.treatmentSeries = some prior ∧ (prior.map Performance.id).Nodup ∧
    (∀ e ∈ prior, c.performance.sameSeries e = some true ∧ e.item = c.item ∧
      e.id ≠ c.performance.id) ∧ prior.length ≤ 1

def ApsTest (c : Context) (methods : List Method) : Prop :=
  Confirmed c .apsDiagnosis ∧ Uses c methods ∧ ApsSeries c

def apsParagraph := noticeRule 11 "380–381" fun c =>
  DistinctSelected c apsItems 4 3

def apsCardiolipin := branchRule 11 "a" "381" fun c => c.item = .cardiolipinIgm →
  ApsTest c [.elisa, .clia, .fia]

def apsBetaIgg := branchRule 11 "i" "381" fun c => c.item = .beta2Igg →
  ApsTest c [.cleia, .clia, .fia]

def apsBetaIgm := branchRule 11 "u" "381" fun c => c.item = .beta2Igm →
  ApsTest c [.cleia, .clia, .fia]

def apsChoice := branchRule 11 "e" "381" fun c => DistinctSelected c apsItems 4 3

def igg2 := noticeRule 12 "381" fun c =>
  (c.item ∈ [.igg2Tia, .igg2Nephelometry] → Confirmed c .suspectedPrimaryImmunodeficiency) ∧
  (c.item = .igg2Nephelometry → ∃ performed selected,
    c.combined = some (performed, selected) ∧ .igg2Tia ∉ performed)

def mpoAnca := noticeRule 13 "381" fun c => c.item = .mpoAnca →
  Uses c [.elisa, .cleia, .latex, .fia] ∧ Confirmed c .rapidlyProgressiveGnDiagnosisOrFollowUp

def gbm := noticeRule 14 "381" fun c => c.item = .gbm →
  Confirmed c .gbmNephritisOrGoodpastureDiagnosisOrPlanning

def lupus := noticeRule 15 "381" fun c => c.item ∈ [.lupusQual, .lupusQuant] →
  Uses c [.russellViper, .phospholipidNeutralization] ∧ Confirmed c .apsDiagnosis

def PemphigusTest (c : Context) : Prop :=
  Uses c skinMethods ∧
    ((c.purpose = some .diagnosis ∧ Confirmed c .suspectedPemphigusUnderCriteria) ∨
      Confirmed c .pemphigusTreatmentMonitoring)

def dsg3Paragraph := noticeRule 16 "381" fun c => c.item = .dsg3 → PemphigusTest c
def dsg3Clinical := branchRule 16 "a" "381" fun c => c.item = .dsg3 → PemphigusTest c
def vulgarisChoice := branchRule 16 "i" "381" fun c => c.item ∈ [.dsg3, .dsg1] →
  c.finding .vulgarisMonitoring = some false ∨
    (Confirmed c .vulgarisMonitoring ∧ PairChoice c [.dsg3] [.dsg1])

def bp180 := noticeRule 17 "381" fun c => c.item = .bp180 →
  Uses c skinMethods ∧ Confirmed c .bullousPemphigoidDifferentialOrMonitoring

def dermatomyositis := noticeRule 18 "381" fun c => c.item ∈ [.tif1, .mi2, .mda5] →
  c.method = some .elisa ∧ Confirmed c .dermatomyositisUnderCriteria

def dsg1Paragraph := noticeRule 19 "381–382" fun c => c.item = .dsg1 → PemphigusTest c
def dsg1Clinical := branchRule 19 "a" "381–382" fun c => c.item = .dsg1 → PemphigusTest c
def foliaceusChoice := branchRule 19 "i" "382" fun c => c.item ∈ [.dsg3, .dsg1] →
  c.finding .foliaceusMonitoring = some false ∨
    (Confirmed c .foliaceusMonitoring ∧ PairChoice c [.dsg3] [.dsg1])

def igg4 := noticeRule 20 "382" fun c => c.item = .igg4 → Uses c [.nephelometry, .tia]

def gm1 := noticeRule 21 "382" fun c => c.item = .gm1 →
  c.method = some .elisa ∧ Confirmed c .suspectedGuillainBarre ∧
    Confirmed c .diagnosticVisit ∧ c.totalPrior = some 0

def gq1b := noticeRule 22 "382" fun c => c.item = .gq1b →
  c.method = some .elisa ∧ Confirmed c .suspectedFisher ∧
    Confirmed c .diagnosticVisit ∧ c.totalPrior = some 0

def SkinCombo (c : Context) : Prop :=
  c.method = some .indirectFluorescence ∧ Confirmed c .pemphigusOrPemphigoidDifferential ∧
    (Confirmed c .suspectedPemphigusUnderCriteria ∨ Confirmed c .suspectedBullousPemphigoid)

def skinComboParagraph := noticeRule 23 "382" fun c => c.item = .skinCombo → SkinCombo c
def skinComboClinical := branchRule 23 "a" "382" fun c => c.item = .skinCombo → SkinCombo c
def skinComboChoice := branchRule 23 "i" "382" fun c =>
  Confirmed c .pemphigusOrPemphigoidDifferential → PairChoice c [.skinCombo] [.dsg3, .bp180, .dsg1]

def achrParagraph := noticeRule 24 "382" fun c => c.item = .achr → Confirmed c .myastheniaDiagnosisOrFollowUp
def achrClinical := branchRule 24 "a" "382" fun c => c.item = .achr → Confirmed c .myastheniaDiagnosisOrFollowUp
def achrChoice := branchRule 24 "i" "382" fun c => PairChoice c [.achr] [.musk]

def glutamate := noticeRule 25 "382" fun c => c.item = .glutamate →
  Confirmed c .rasmussenOrSpecifiedEpilepsyOrOpsoclonusDiagnosis ∧
    prior c c.priorClaims (Period.month c.performance.site.date.month) = some 0

def AquaporinClinical (a : SpecimenTests.AquaporinAssessment) : Prop :=
  (a.method = .elisa ∨ a.method = .cleia) ∧ a.diagnosisPurpose = true ∧ a.treatmentEffectAssessment = false ∧
    match a.history with
    | .first => True
    | .repeatAfterNegative changed suspected needed _ _ => changed = true ∧ suspected = true ∧ needed = true
    | .other => False

def aquaporinRule : Rule Context Unit :=
  ⟨"notice/D014/paragraph/26", SpecimenTests.d014AquaporinSource, fun c _ => c.item = .aqp4 →
    ∃ a, c.aquaporin = some a ∧ AquaporinClinical a⟩

def muskParagraph := noticeRule 27 "382" fun c => c.item = .musk →
  c.method = some .ria ∧ Confirmed c .myastheniaDiagnosisOrFollowUp

def muskClinical := branchRule 27 "a" "382" fun c => c.item = .musk →
  c.method = some .ria ∧ Confirmed c .myastheniaDiagnosisOrFollowUp

def muskChoice := branchRule 27 "i" "382" fun c => PairChoice c [.achr] [.musk]

def vgccParagraph := noticeRule 28 "382–383" fun c => c.item = .vgcc →
  c.method = some .ria ∧ Confirmed c .lambertEatonDiagnosis

def vgccMethod := branchRule 28 "a" "383" fun c => c.item = .vgcc →
  c.method = some .ria ∧ Confirmed c .lambertEatonDiagnosis

def vgccException := branchRule 28 "i" "383" fun c => c.item = .vgcc →
  Confirmed c .symptomaticLambertEaton ∧
    (Confirmed c .abnormalRepetitiveStimulation ∨
      (c.finding .abnormalRepetitiveStimulation = some false ∧ Confirmed c .vgccMedicallyNecessary))

def nodopathy := noticeRule 29 "383" fun c => c.item ∈ [.nf155, .cntn1] →
  c.method = some .elisa ∧ Confirmed c .cidpOrNodopathyDiagnosisWithoutMonitoring ∧
    (c.totalPrior = some 0 ∨ (Confirmed c .suspectedNodopathyRelapse ∧
      Confirmed c .itemPositiveInitially ∧ PairChoice c [.nf155] [.cntn1]))

def hlaScreen := noticeRule 30 "383" fun c => c.item = .hlaScreen →
  Confirmed c .priorTransplantOrListed ∧
    (Within c .oneYear c.priorClaims 0 ∨ (Confirmed c .hlaRepeatNecessary ∧ Within c .oneYear c.priorClaims 1))

def gmCsf := noticeRule 31 "383" fun c => c.item = .gmCsf →
  c.method = some .immunochromatography ∧ Confirmed c .suspectedAutoimmunePulmonaryAlveolarProteinosis ∧
    Confirmed c .diagnosticVisit ∧ c.totalPrior = some 0

def hlaIdentify := noticeRule 32 "383" fun c => c.item = .hlaIdentify →
  (Confirmed c .positiveHlaScreen ∧ Confirmed c .confirmsAntibodyMediatedRejectionOrHlaAcquisition) ∨
    ((Confirmed c .rejectionFollowUp ∨ Confirmed c .listedAndDesensitizedAfterPositiveIdentification) ∧
      Within c .oneYear c.purposeClaims 1)

def facilities : Rule Context Unit :=
  ⟨"primary/D014/note/2", primary "注2", fun c _ => c.item ∈ [.hlaScreen, .hlaIdentify] →
    c.facilityComplies = some true ∧ c.facilityFilingConfirmed = some true⟩

def aqp4Documentation : Rule Context (Remark → Prop) :=
  ⟨"notice/D014/paragraph/26", SpecimenTests.d014AquaporinSource, fun c recorded =>
    c.item = .aqp4 →
      ∀ a changed suspected needed date necessity, c.aquaporin = some a →
        a.history = .repeatAfterNegative changed suspected needed date necessity →
        recorded .aqp4PriorDate ∧ recorded .aqp4Necessity⟩

private def documentation (n : Nat) (suffix pages : String)
    (condition : Context → (Remark → Prop) → Prop) : Rule Context (Remark → Prop) :=
  ⟨"notice/D014/paragraph/" ++ toString n ++ suffix, notice pages n, condition⟩

def ccpDiagnosisDocumentation := documentation 7 "/a/i" "380" fun c recorded =>
  c.item ∈ ccpItems → c.purpose = some .diagnosis → c.purposePrior ≠ some 0 → recorded .ccpValue

def ccpTreatmentDocumentation := documentation 7 "/a/ro" "380" fun c recorded =>
  c.item ∈ ccpItems → c.purpose = some .treatmentSelection → c.purposePrior ≠ some 0 → recorded .ccpNecessity

def lkmDocumentation := documentation 9 "/i" "380" fun c recorded =>
  c.item = .lkm1 → recorded .negativeAnaDate

def vgccDocumentation := documentation 28 "/i" "383" fun c recorded =>
  c.item = .vgcc → c.finding .abnormalRepetitiveStimulation = some false → recorded .vgccDetailedReason

def nodopathyDocumentation := documentation 29 "" "383" fun c recorded =>
  c.item ∈ [.nf155, .cntn1] → c.totalPrior ≠ some 0 → recorded .nodopathyNecessity

def hlaScreenDocumentation := documentation 30 "" "383" fun c recorded =>
  c.item = .hlaScreen → ¬ Within c .oneYear c.priorClaims 0 →
    recorded .hlaChartReasonAndNecessity ∧ recorded .hlaClaimReasonAndNecessity

def hlaIdentifyDocumentation := documentation 32 "" "383" fun c recorded =>
  c.item = .hlaIdentify →
  ¬ (Confirmed c .positiveHlaScreen ∧ Confirmed c .confirmsAntibodyMediatedRejectionOrHlaAcquisition) →
    recorded .hlaChartReasonAndNecessity ∧ recorded .hlaClaimReasonAndNecessity

def documentationRules :=
  [ccpDiagnosisDocumentation, ccpTreatmentDocumentation, lkmDocumentation, aqp4Documentation,
   vgccDocumentation, nodopathyDocumentation, hlaScreenDocumentation, hlaIdentifyDocumentation]

def eligibilityRules :=
  [facilities, rheumatoidLimit, galactoseMethod, thyroidChoice, rnaPolymerase, centromere,
   arsChoice, ccpParagraph, ccpPurpose, ccpDiagnosis, ccpTreatment, ccpChoice, thyroidStimulation,
   lkmParagraph, lkmClinical, cardiolipinChoice, apsParagraph, apsCardiolipin, apsBetaIgg,
   apsBetaIgm, apsChoice, igg2, mpoAnca, gbm, lupus, dsg3Paragraph, dsg3Clinical, vulgarisChoice,
   bp180, dermatomyositis, dsg1Paragraph, dsg1Clinical, foliaceusChoice, igg4, gm1, gq1b,
   skinComboParagraph, skinComboClinical, skinComboChoice, achrParagraph, achrClinical, achrChoice,
   glutamate, aquaporinRule, muskParagraph, muskClinical, muskChoice, vgccParagraph, vgccMethod,
   vgccException, nodopathy, hlaScreen, gmCsf, hlaIdentify]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()
def PermitsRate (c : Context) (p : Nat) : Prop := Eligible c ∧ Satisfies rates c.item p

def legacyRequest (i : Item) (a : Option SpecimenTests.AquaporinAssessment) (filed : Bool) :
    SpecimenTests.Request :=
  { code := .d014, number := i.number, variant := i.variant,
    conditions := { aquaporin := a, facilityNotified := filed } }

theorem legacy_rate (i : Item) (a : Option SpecimenTests.AquaporinAssessment)
    (filed : Bool) (ha : i = .aqp4 → a.any SpecimenTests.AquaporinAssessment.eligible = true)
    (hf : i ∈ [.hlaScreen, .hlaIdentify] → filed = true) :
    SpecimenTests.assessOne (legacyRequest i a filed) = some (.charged i.points 0) := by
  cases i <;> first
    | rfl
    | have h := hf (by simp)
      subst filed
      rfl
    | have h := ha rfl
      change (if !(a.any SpecimenTests.AquaporinAssessment.eligible)
        then none else some (SpecimenTests.ItemResult.charged 1000 0)) = _
      simp [h, Item.points]

theorem aqp4_legacy_condition (a : SpecimenTests.AquaporinAssessment) :
    a.eligible = true ↔ AquaporinClinical a ∧
      (match a.history with
       | .repeatAfterNegative _ _ _ date necessity => date = true ∧ necessity = true
       | _ => True) := by
  cases a with
  | mk method purpose followUp history =>
    cases history <;>
      simp [SpecimenTests.AquaporinAssessment.eligible, AquaporinClinical, and_assoc]

theorem legacy_iff (c : Context) (p : Nat)
    (ha : c.item = .aqp4 → c.aquaporin.any SpecimenTests.AquaporinAssessment.eligible = true)
    (hf : c.item ∈ [.hlaScreen, .hlaIdentify] → c.facilityFilingConfirmed = some true) :
    PermitsRate c p ↔ Eligible c ∧
      SpecimenTests.assessOne (legacyRequest c.item c.aquaporin
        (c.facilityFilingConfirmed == some true)) = some (.charged p 0) := by
  have hFile : c.item ∈ [.hlaScreen, .hlaIdentify] → (c.facilityFilingConfirmed == some true) = true := by
    intro hi
    simp [hf hi]
  simp [PermitsRate, rate_iff, legacy_rate _ _ _ ha hFile, eq_comm]

theorem determines (c : Context) (h : Eligible c) :
    (∃ p, PermitsRate c p) ∧ (∀ p q, PermitsRate c p → PermitsRate c q → p = q) :=
  ⟨⟨c.item.points, h, (rate_iff _ _).mpr rfl⟩, fun _ _ hp hq =>
    ((rate_iff _ _).mp hp.2).trans ((rate_iff _ _).mp hq.2).symm⟩

def IsBundleItem (i : Item) : Prop :=
  (10 ≤ i.number ∧ i.number ≤ 16) ∨ i.number ∈ [18, 19, 23, 35, 36]

structure BundleGroup where
  site : Site
  tests : List Context

def BundleGroup.Assessed (g : BundleGroup) : Prop :=
  g.tests ≠ [] ∧ (g.tests.map Context.item).Nodup ∧
    ∀ c ∈ g.tests, Eligible c ∧ IsBundleItem c.item ∧
      c.performance.site.patient = g.site.patient ∧ c.performance.site.institution = g.site.institution

def BundleGroup.count (g : BundleGroup) := g.tests.length
def BundleGroup.sum (g : BundleGroup) := (g.tests.map fun c => c.item.points).sum

def twoItemPoints : Nat := 320
def threeOrMorePoints : Nat := 490

def bundled : Rule BundleGroup Nat :=
  ⟨"primary/D014/note/1", primary "注1", fun g p =>
    (g.count < 2 → p = g.sum) ∧ (g.count = 2 → p = twoItemPoints) ∧ (3 ≤ g.count → p = threeOrMorePoints)⟩

def bundleRules := [bundled]

theorem bundle_iff (g : BundleGroup) (p : Nat) :
    Satisfies bundleRules g p ↔ p = SpecimenTests.groupedBase .autoantibodies g.count g.sum := by
  simp only [bundleRules, satisfies_cons, satisfies_nil, and_true, bundled, SpecimenTests.groupedBase,
    twoItemPoints, threeOrMorePoints]
  split
  · omega
  · split <;> omega

theorem bundle_determines : DeterminesOn BundleGroup.Assessed bundleRules := by
  intro g _
  let p := SpecimenTests.groupedBase .autoantibodies g.count g.sum
  exact ⟨⟨p, (bundle_iff _ _).mpr rfl⟩, fun _ _ hx hy =>
    ((bundle_iff _ _).mp hx).trans ((bundle_iff _ _).mp hy).symm⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 14, number := i.number, ordinaryCategory := .immunological }

def execution (kind : Nat) (c : Context) (p : Nat) (_ : PermitsRate c p) :
    Examinations.SpecimenItem :=
  { kind := kind, executionPoints := p }

def bundleExecution (kind : Nat) (g : BundleGroup) (p : Nat) (_ : g.Assessed)
    (_ : Satisfies bundleRules g p) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := p }

private def sample (i : Item) : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, i, none, none, none, none⟩ }

example : PermitsRate { sample .aqp4 with aquaporin := some ⟨.cleia, true, false, .first⟩ } 1000 := by
  refine ⟨?_, (rate_iff _ _).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, Context.item, sample,
    facilities, rheumatoidLimit, galactoseMethod, thyroidChoice, rnaPolymerase, centromere, arsChoice,
    ccpParagraph, ccpPurpose, ccpDiagnosis, ccpTreatment, ccpChoice, thyroidStimulation, lkmParagraph,
    lkmClinical, cardiolipinChoice, apsParagraph, apsCardiolipin, apsBetaIgg, apsBetaIgm, apsChoice,
    igg2, mpoAnca, gbm, lupus, dsg3Paragraph, dsg3Clinical, vulgarisChoice, bp180, dermatomyositis,
    dsg1Paragraph, dsg1Clinical, foliaceusChoice, igg4, gm1, gq1b, skinComboParagraph, skinComboClinical,
    skinComboChoice, achrParagraph, achrClinical, achrChoice, glutamate, aquaporinRule, AquaporinClinical,
    muskParagraph, muskClinical, muskChoice, vgccParagraph, vgccMethod, vgccException, nodopathy,
    hlaScreen, gmCsf, hlaIdentify, noticeRule, branchRule, DistinctSelected, PairChoice,
    rheumatoidGroup, ccpItems, apsItems, joItems, Confirmed]

example : ¬ Eligible (sample .hlaScreen) := by
  intro h
  have hr := h facilities (by simp [eligibilityRules])
  have hfile := (hr (by simp [Context.item, sample])).2
  contradiction

end Sanri.MedicalFee.D014
