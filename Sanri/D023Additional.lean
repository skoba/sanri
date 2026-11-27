import Sanri.D023
import Sanri.D021
import Sanri.SpecimenCollection

namespace Sanri.MedicalFee.D023

open Sanri.Logic Sanri.History

private def addedNotice (id page : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF" ++ page ++ "頁 D023 " ++ id, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def condition (id page : String) (p : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D023/paragraph/" ++ id, addedNotice id page, fun c _ => p c⟩

structure PyloriContext where
  performance : Performance Unit
  stronglySuspectedPylori : Option Bool := none
  pcr : Option Bool := none
  separatePyloriNotificationSatisfied : Option Bool := none
  upperGiEndoscopyWaste : Option Bool := none

def pyloriMethod : Rule PyloriContext Unit :=
  condition "16/a" "391" fun c => c.stronglySuspectedPylori = some true ∧ c.pcr = some true

def pyloriReference : Rule PyloriContext Unit :=
  condition "16/i" "391" fun c => c.separatePyloriNotificationSatisfied = some true

def pyloriCollection : Rule PyloriContext Bool :=
  ⟨"notice/D023/paragraph/16/u", addedNotice "16/u" "391", fun c separate =>
    (c.upperGiEndoscopyWaste = some true ∧ separate = false) ∨ c.upperGiEndoscopyWaste = some false⟩

def pylori : Rule PyloriContext Unit :=
  condition "16" "391" fun c =>
    pyloriMethod.holds c () ∧ pyloriReference.holds c () ∧ c.upperGiEndoscopyWaste.isSome = true

def PyloriCollectionPair (c : PyloriContext) (p : Performance SpecimenCollection.Item)
    (collection : SpecimenCollection.Context) (separate : Bool) : Prop :=
  pylori.holds c () ∧ p.item = .gastricDuodenalFluid ∧ collection.item = p.item ∧
  p.sameSpecimen { c.performance with item := p.item } = some true ∧
  pyloriCollection.holds c separate

structure MacContext where
  performance : Performance Unit
  otherTestConfirmedTbNegative : Option Bool := none
  /-- 確認済みのD021併施群と、その主たる検査。 -/
  comparison : Option (Option D021.Context × Nat) := none

def macIndication : Rule MacContext Unit :=
  condition "20/a" "392" fun c => c.otherTestConfirmedTbNegative = some true

def macChoice : Rule MacContext Unit :=
  condition "20/i" "392" fun c => ∃ other,
    c.comparison = some (other, c.performance.id) ∧
    ∀ d, other = some d →
      D021.InScope d ∧ d.performance.site.patient = c.performance.site.patient ∧
      d.performance.site.institution = c.performance.site.institution ∧
      d.performance.id ≠ c.performance.id

def mac : Rule MacContext Unit :=
  condition "20" "392" fun c => macIndication.holds c () ∧ macChoice.holds c ()

inductive Histology where
  | cin1 | cin2 | other
  deriving DecidableEq

structure HpvGenotypeContext where
  performance : Performance Unit
  histology : Option (Date × Histology) := none
  histologyObtainedBeforeTest : Option Bool := none
  forTreatmentPlan : Option Bool := none
  testedIndividualHighRiskTypes : Option Bool := none
  d023TenAndElevenFacilityNotified : Option Bool := none
  /-- 確認済みの前回実施。未確認と初回を区別する。 -/
  precedingTest : Option (Option Date) := none

structure HpvDocumentation where
  histology : Option (Date × Histology)
  precedingTest : Option Date

def hpvGenotypeIndication : Rule HpvGenotypeContext Unit :=
  condition "40/a" "400" fun c => (∃ day grade, c.histology = some (day, grade) ∧
    (grade = .cin1 ∨ grade = .cin2) ∧ c.histologyObtainedBeforeTest = some true) ∧
    c.forTreatmentPlan = some true ∧ c.testedIndividualHighRiskTypes = some true

def hpvGenotypeFacility : Rule HpvGenotypeContext Unit :=
  condition "40/i" "400" fun c => c.d023TenAndElevenFacilityNotified = some true

def hpvHistologyDocumentation : Rule HpvGenotypeContext HpvDocumentation :=
  ⟨"notice/D023/paragraph/40/u", addedNotice "40/u" "400", fun c d =>
    c.histology.isSome = true ∧ d.histology = c.histology⟩

def hpvPrecedingDocumentation : Rule HpvGenotypeContext HpvDocumentation :=
  ⟨"notice/D023/paragraph/40/e", addedNotice "40/e" "401", fun c d =>
    c.precedingTest = some none ∨
    ∃ day, c.precedingTest = some (some day) ∧ d.precedingTest = some day⟩

def hpvGenotype : Rule HpvGenotypeContext Unit :=
  condition "40" "400–401" fun c =>
    hpvGenotypeIndication.holds c () ∧ hpvGenotypeFacility.holds c ()

structure HivGenotypeContext where
  performance : Performance Unit
  selectsOrReselectsAntiretroviralTreatment : Option Bool := none
  /-- ３月の起算と算定枠を確認した照会範囲。 -/
  window : Option Scope := none
  history : Option (ClaimHistory Unit) := none

def hivGenotype : Rule HivGenotypeContext Unit :=
  condition "41" "401" fun c => c.selectsOrReselectsAntiretroviralTreatment = some true ∧
    ∃ scope history, c.window = some scope ∧ c.history = some history ∧
      scope.Includes c.performance.site = true ∧ count history scope (fun _ => true) = some 0

inductive MpoxSample where
  | skinLesion | mucosalLesion | pharyngealSwab | other
  deriving DecidableEq

structure MpoxContext where
  performance : Performance Unit
  suspectedMpox : Option Bool := none
  forDiagnosis : Option Bool := none
  specimen : Option MpoxSample := none
  pcr : Option Bool := none
  scope : Scope
  history : ClaimHistory Nat

def mpox : Rule MpoxContext Unit :=
  condition "32" "395" fun c =>
    c.suspectedMpox = some true ∧ c.forDiagnosis = some true ∧
    c.specimen ∈ [some .skinLesion, some .mucosalLesion, some .pharyngealSwab] ∧ c.pcr = some true ∧
    c.scope.institution = some c.performance.site.institution ∧ c.scope.Includes c.performance.site = true ∧
    ∃ series, c.performance.series = some series ∧ count c.history c.scope (· == series) = some 0

inductive SelectedTest where
  | noCounterpart | thisTest | counterpart
  deriving DecidableEq

private def AllowsThis (choice : Option SelectedTest) : Prop :=
  choice = some .noCounterpart ∨ choice = some .thisTest

structure CmvDetectionContext where
  performance : Performance Unit
  forCongenitalDiagnosis : Option Bool := none
  urine : Option Bool := none
  isothermalAmplification : Option Bool := none
  /-- 当該診断に対する初回の算定かを確認した入力。 -/
  firstForThisDiagnosis : Option Bool := none
  comparisonWithCmvAntibodies : Option SelectedTest := none

def cmvDetectionMethod : Rule CmvDetectionContext Unit :=
  condition "33/a" "395" fun c =>
    c.forCongenitalDiagnosis = some true ∧ c.urine = some true ∧
    c.isothermalAmplification = some true ∧ c.firstForThisDiagnosis = some true

def cmvDetectionChoice : Rule CmvDetectionContext Unit :=
  condition "33/i" "395" fun c => AllowsThis c.comparisonWithCmvAntibodies

def cmvDetection : Rule CmvDetectionContext Unit :=
  condition "33" "395" fun c => cmvDetectionMethod.holds c () ∧ cmvDetectionChoice.holds c ()

structure TbResistanceContext where
  performance : Performance Unit
  simultaneousTbDetection : Option Bool := none
  comparisonWithTbNucleicAcidDetection : Option SelectedTest := none
  suspectedDrugResistantTb : Option Bool := none
  confirmedTbBySmearOrOtherFindings : Option Bool := none
  comparisonWithSingleRifampicinOrIsoniazid : Option SelectedTest := none

def singleResistanceSimultaneous : Rule TbResistanceContext Unit :=
  condition "34/a" "395" fun c => c.simultaneousTbDetection = some true

def singleResistanceChoice : Rule TbResistanceContext Unit :=
  condition "34/i" "395" fun c => AllowsThis c.comparisonWithTbNucleicAcidDetection

def singleResistanceIndication : Rule TbResistanceContext Unit :=
  condition "34/u" "395" fun c => c.suspectedDrugResistantTb = some true

def singleResistance : Rule TbResistanceContext Unit :=
  condition "34" "395" fun c => singleResistanceSimultaneous.holds c () ∧
    singleResistanceChoice.holds c () ∧ singleResistanceIndication.holds c ()

def dualResistanceIndication : Rule TbResistanceContext Unit :=
  condition "35/a" "395" fun c =>
    c.confirmedTbBySmearOrOtherFindings = some true ∧ c.suspectedDrugResistantTb = some true

def dualResistanceChoice : Rule TbResistanceContext Unit :=
  condition "35/i" "395" fun c => AllowsThis c.comparisonWithSingleRifampicinOrIsoniazid

def dualResistance : Rule TbResistanceContext Unit :=
  condition "35" "395" fun c => dualResistanceIndication.holds c () ∧ dualResistanceChoice.holds c ()

structure SepsisPanelContext where
  performance : Performance Unit
  suspectedSepsis : Option Bool := none
  distinctTargetCount : Option Nat := none
  simultaneousMicroarrayForBacterialNucleicAcidsAndResistanceGenes : Option Bool := none
  guidelineSatisfied : Option Bool := none
  mrsaTestChoice : Option SelectedTest := none
  scope : Scope
  history : ClaimHistory Nat

def sepsisMethod : Rule SepsisPanelContext Unit :=
  condition "38/a" "399" fun c =>
    c.suspectedSepsis = some true ∧
    (∃ n, c.distinctTargetCount = some n ∧ 15 ≤ n) ∧
    c.simultaneousMicroarrayForBacterialNucleicAcidsAndResistanceGenes = some true ∧
    c.guidelineSatisfied = some true ∧ c.scope.institution = some c.performance.site.institution ∧
    c.scope.Includes c.performance.site = true ∧
    ∃ series, c.performance.series = some series ∧ count c.history c.scope (· == series) = some 0

def sepsisChoice : Rule SepsisPanelContext Unit :=
  condition "38/i" "399–400" fun c => AllowsThis c.mrsaTestChoice

structure SepsisDocumentation where
  inMedicalRecord : Bool
  inClaimRemarks : Bool

def sepsisDocumentation : Rule SepsisPanelContext SepsisDocumentation :=
  ⟨"notice/D023/paragraph/38/u", addedNotice "38/u" "400", fun _ d =>
    d.inMedicalRecord = true ∧ d.inClaimRemarks = true⟩

def sepsis : Rule SepsisPanelContext Unit :=
  condition "38" "399–400" fun c => sepsisMethod.holds c () ∧ sepsisChoice.holds c ()

def SepsisPbp2Pair (c : SepsisPanelContext) (p : D023Other.Context) (points : Nat) : Prop :=
  sepsis.holds c () ∧ c.mrsaTestChoice = some .thisTest ∧
  p.performance.item ∈ [.pbp2, .rapidPbp2] ∧
  c.performance.site.patient = p.performance.site.patient ∧
  c.performance.site.institution = p.performance.site.institution ∧
  D023Other.InScope p ∧ Satisfies D023Other.rates p points

/-- 条項が列挙する併施相手を、D012の検査種類とD023の項・カタログ内の
検査種類に区別する。検査項目番号だけではウイルス抗体価の対象は決まらない。 -/
inductive SeriesTest where
  | antibody (item : D012.Item) (target : Option D012.Target := none)
  | molecular (number variant : Nat)
  | respiratoryPanel (includesCovid : Bool)
  deriving DecidableEq

def seriesTestFromD012 (c : D012.Context) (item : D012.Item)
    (_ : c.performance.item = .local item) : Performance SeriesTest :=
  { c.performance with item := .antibody item c.target }

private def exactSeriesTest (test : SeriesTest) (actual : SeriesTest) : Option Bool :=
  match test, actual with
  | .antibody expected _, .antibody item _ => some (expected == item)
  | _, _ => some (test == actual)

private def viralTiterTargets (targets : List D012.Target) : SeriesTest → Option Bool
  | .antibody .viralTiter target => target.map targets.contains
  | _ => some false

private def respiratoryTiter := viralTiterTargets
  [.influenzaA, .influenzaB, .parainfluenzaI, .parainfluenzaII, .parainfluenzaIII, .rs]

private def csfTiter := viralTiterTargets [.cytomegalovirus, .herpes, .varicellaZoster]

/-- 確認範囲を当該患者・機関の治療範囲に合わせ、照合済みの候補実施を調べる。
対象又は一連のIDが不明な相手について別算定可を導かない。 -/
def SeriesExcludes (anchor : Performance Unit) (related : List (Performance SeriesTest))
    (matchTest : SeriesTest → Option Bool) : Prop :=
  ∀ other ∈ related,
    matchTest other.item = some false ∨
      anchor.sameSeries { other with item := () } = some false

structure RespiratoryPanelAssessment where
  panel : RespiratoryPanelContext
  filingEvidence : PanelFilingEvidence
  /-- 通知(37)の一連について、対象区分の既算定・同時審査の候補を確認した一覧。 -/
  separatelyBilled : Option (List (Performance SeriesTest)) := none

private def respiratoryExclusion (withCovid : Bool) (suffix page : String)
    (matchTest : SeriesTest → Option Bool) : Rule RespiratoryPanelAssessment Unit :=
  ⟨"notice/D023/paragraph/37/" ++ (if withCovid then "u/" else "e/") ++ suffix,
    addedNotice "(37) 一連の治療中の別算定" page, fun c _ =>
    c.panel.performance.item = withCovid →
      ∃ related, c.separatelyBilled = some related ∧
        SeriesExcludes { c.panel.performance with item := () } related matchTest⟩

def panelWithCovidI :=
  respiratoryExclusion true "i" "397" (exactSeriesTest (.antibody .mycoplasmaQual))
def panelWithCovidRo :=
  respiratoryExclusion true "ro" "397" (exactSeriesTest (.antibody .mycoplasmaSemi))
def panelWithCovidHa :=
  respiratoryExclusion true "ha" "397" (exactSeriesTest (.antibody .pneumoniaeIgG))
def panelWithCovidNi :=
  respiratoryExclusion true "ni" "397" (exactSeriesTest (.antibody .pneumoniaeIgA))
def panelWithCovidHo :=
  respiratoryExclusion true "ho" "397" respiratoryTiter
def panelWithCovidHe :=
  respiratoryExclusion true "he" "397" (exactSeriesTest (.antibody .pertussisQual))
def panelWithCovidTo :=
  respiratoryExclusion true "to" "397" (exactSeriesTest (.antibody .pertussisSemi))
def panelWithCovidChi :=
  respiratoryExclusion true "chi" "397" (exactSeriesTest (.antibody .influenzaAntigen))
def panelWithCovidRi :=
  respiratoryExclusion true "ri" "397" (exactSeriesTest (.antibody .rsAntigen))
def panelWithCovidNu :=
  respiratoryExclusion true "nu" "397" (exactSeriesTest (.antibody .metapneumovirusAntigen))
def panelWithCovidRu :=
  respiratoryExclusion true "ru" "397–398" (exactSeriesTest (.antibody .mycoplasmaChromatography))
def panelWithCovidWo :=
  respiratoryExclusion true "wo" "398" (exactSeriesTest (.antibody .covidQual))
def panelWithCovidWa :=
  respiratoryExclusion true "wa" "398" (exactSeriesTest (.antibody .pneumoniaeIgM))
def panelWithCovidKa :=
  respiratoryExclusion true "ka" "398" (exactSeriesTest (.antibody .mycoplasmaFluorescence))
def panelWithCovidYo :=
  respiratoryExclusion true "yo" "398" (exactSeriesTest (.antibody .nonStoolAdenovirus))
def panelWithCovidTa :=
  respiratoryExclusion true "ta" "398" (exactSeriesTest (.antibody .pertussisAntigen))
def panelWithCovidRe :=
  respiratoryExclusion true "re" "398" (exactSeriesTest (.antibody .covidFlu))
def panelWithCovidSo :=
  respiratoryExclusion true "so" "398" (exactSeriesTest (.antibody .pertussisAntibody))
def panelWithCovidTsu :=
  respiratoryExclusion true "tsu" "398" (exactSeriesTest (.antibody .covidRs))
def panelWithCovidNe :=
  respiratoryExclusion true "ne" "398" (exactSeriesTest (.antibody .covidFluRs))
def panelWithCovidNa :=
  respiratoryExclusion true "na" "398" (exactSeriesTest (.antibody .covidQuant))
def panelWithCovidRa :=
  respiratoryExclusion true "ra" "398" (exactSeriesTest (.molecular 6 0))
def panelWithCovidMu :=
  respiratoryExclusion true "mu" "398" (exactSeriesTest (.molecular 6 1))
def panelWithCovidU :=
  respiratoryExclusion true "u" "398" (exactSeriesTest (.molecular 6 2))
def panelWithCovidWi :=
  respiratoryExclusion true "wi" "398" (exactSeriesTest (.molecular 13 0))
def panelWithCovidNo :=
  respiratoryExclusion true "no" "398" (exactSeriesTest (.molecular 13 1))
def panelWithCovidO :=
  respiratoryExclusion true "o" "398" (exactSeriesTest (.molecular 13 2))
def panelWithCovidKu :=
  respiratoryExclusion true "ku" "398" (exactSeriesTest (.molecular 19 0))
def panelWithCovidYa :=
  respiratoryExclusion true "ya" "398" (exactSeriesTest (.molecular 20 0))
def panelWithCovidMa :=
  respiratoryExclusion true "ma" "398" (exactSeriesTest (.molecular 20 1))
def panelWithCovidKe :=
  respiratoryExclusion true "ke" "398" (exactSeriesTest (.molecular 20 2))
def panelWithCovidFu :=
  respiratoryExclusion true "fu" "398" (exactSeriesTest (.molecular 24 0))
def panelWithCovidKo :=
  respiratoryExclusion true "ko" "398" (exactSeriesTest (.respiratoryPanel false))

def respiratoryWithCovidExclusions := [
  panelWithCovidI, panelWithCovidRo, panelWithCovidHa, panelWithCovidNi,
  panelWithCovidHo, panelWithCovidHe, panelWithCovidTo, panelWithCovidChi,
  panelWithCovidRi, panelWithCovidNu, panelWithCovidRu, panelWithCovidWo,
  panelWithCovidWa, panelWithCovidKa, panelWithCovidYo, panelWithCovidTa,
  panelWithCovidRe, panelWithCovidSo, panelWithCovidTsu, panelWithCovidNe,
  panelWithCovidNa, panelWithCovidRa, panelWithCovidMu, panelWithCovidU,
  panelWithCovidWi, panelWithCovidNo, panelWithCovidO, panelWithCovidKu,
  panelWithCovidYa, panelWithCovidMa, panelWithCovidKe, panelWithCovidFu,
  panelWithCovidKo]

def panelWithoutCovidI :=
  respiratoryExclusion false "i" "398" (exactSeriesTest (.antibody .mycoplasmaQual))
def panelWithoutCovidRo :=
  respiratoryExclusion false "ro" "398" (exactSeriesTest (.antibody .mycoplasmaSemi))
def panelWithoutCovidHa :=
  respiratoryExclusion false "ha" "398" (exactSeriesTest (.antibody .pneumoniaeIgG))
def panelWithoutCovidNi :=
  respiratoryExclusion false "ni" "399" (exactSeriesTest (.antibody .pneumoniaeIgA))
def panelWithoutCovidHo :=
  respiratoryExclusion false "ho" "399" respiratoryTiter
def panelWithoutCovidHe :=
  respiratoryExclusion false "he" "399" (exactSeriesTest (.antibody .pertussisQual))
def panelWithoutCovidTo :=
  respiratoryExclusion false "to" "399" (exactSeriesTest (.antibody .pertussisSemi))
def panelWithoutCovidChi :=
  respiratoryExclusion false "chi" "399" (exactSeriesTest (.antibody .influenzaAntigen))
def panelWithoutCovidRi :=
  respiratoryExclusion false "ri" "399" (exactSeriesTest (.antibody .rsAntigen))
def panelWithoutCovidNu :=
  respiratoryExclusion false "nu" "399" (exactSeriesTest (.antibody .metapneumovirusAntigen))
def panelWithoutCovidRu :=
  respiratoryExclusion false "ru" "399" (exactSeriesTest (.antibody .mycoplasmaChromatography))
def panelWithoutCovidWo :=
  respiratoryExclusion false "wo" "399" (exactSeriesTest (.antibody .pneumoniaeIgM))
def panelWithoutCovidWa :=
  respiratoryExclusion false "wa" "399" (exactSeriesTest (.antibody .mycoplasmaFluorescence))
def panelWithoutCovidKa :=
  respiratoryExclusion false "ka" "399" (exactSeriesTest (.antibody .nonStoolAdenovirus))
def panelWithoutCovidYo :=
  respiratoryExclusion false "yo" "399" (exactSeriesTest (.antibody .pertussisAntigen))
def panelWithoutCovidTa :=
  respiratoryExclusion false "ta" "399" (exactSeriesTest (.antibody .pertussisAntibody))
def panelWithoutCovidRe :=
  respiratoryExclusion false "re" "399" (exactSeriesTest (.molecular 6 0))
def panelWithoutCovidSo :=
  respiratoryExclusion false "so" "399" (exactSeriesTest (.molecular 6 1))
def panelWithoutCovidTsu :=
  respiratoryExclusion false "tsu" "399" (exactSeriesTest (.molecular 6 2))
def panelWithoutCovidNe :=
  respiratoryExclusion false "ne" "399" (exactSeriesTest (.molecular 13 0))
def panelWithoutCovidNa :=
  respiratoryExclusion false "na" "399" (exactSeriesTest (.molecular 13 1))
def panelWithoutCovidRa :=
  respiratoryExclusion false "ra" "399" (exactSeriesTest (.molecular 13 2))
def panelWithoutCovidMu :=
  respiratoryExclusion false "mu" "399" (exactSeriesTest (.molecular 24 0))
def panelWithoutCovidU :=
  respiratoryExclusion false "u" "399" (exactSeriesTest (.respiratoryPanel true))

def respiratoryWithoutCovidExclusions := [
  panelWithoutCovidI, panelWithoutCovidRo, panelWithoutCovidHa, panelWithoutCovidNi,
  panelWithoutCovidHo, panelWithoutCovidHe, panelWithoutCovidTo, panelWithoutCovidChi,
  panelWithoutCovidRi, panelWithoutCovidNu, panelWithoutCovidRu, panelWithoutCovidWo,
  panelWithoutCovidWa, panelWithoutCovidKa, panelWithoutCovidYo, panelWithoutCovidTa,
  panelWithoutCovidRe, panelWithoutCovidSo, panelWithoutCovidTsu, panelWithoutCovidNe,
  panelWithoutCovidNa, panelWithoutCovidRa, panelWithoutCovidMu, panelWithoutCovidU]

def respiratoryOutpatientRoute : Rule RespiratoryPanelAssessment Unit :=
  ⟨"notice/D023/paragraph/37/i", addedNotice "(37)イ 外来" "397",
    fun c _ => panelOutpatient.holds c.panel ()⟩

def respiratoryWithCovid : Rule RespiratoryPanelAssessment Unit :=
  ⟨"notice/D023/paragraph/37/u", addedNotice "(37)ウ" "397–398",
    fun c _ => Satisfies respiratoryWithCovidExclusions c ()⟩

def respiratoryWithoutCovid : Rule RespiratoryPanelAssessment Unit :=
  ⟨"notice/D023/paragraph/37/e", addedNotice "(37)エ" "398–399",
    fun c _ => Satisfies respiratoryWithoutCovidExclusions c ()⟩

def respiratoryPanel : Rule RespiratoryPanelAssessment Unit :=
  ⟨"notice/D023/paragraph/37", addedNotice "(37)" "396–399", fun c _ =>
    panelMethod.holds c.panel () ∧ respiratoryOutpatientRoute.holds c () ∧
    respiratoryWithCovid.holds c () ∧ respiratoryWithoutCovid.holds c ()⟩

def RespiratoryPanelEligible (c : RespiratoryPanelAssessment) : Prop :=
  c.panel.evidence.tier = c.panel.tier ∧
    c.filingEvidence.site = c.panel.performance.site ∧
    c.filingEvidence.includesCovid = c.panel.performance.item ∧
    panelFilingQuestion.holds c.filingEvidence () ∧
    D023Schedule.respiratoryPanelFacility.holds c.panel.evidence () ∧ respiratoryPanel.holds c ()

theorem respiratory_panel_determines (c : RespiratoryPanelAssessment)
    (_ : RespiratoryPanelEligible c) : DeterminesAt D023Schedule.rates c.panel.tier :=
  D023Schedule.base_determines c.panel.tier trivial

structure CsfPanelContext where
  performance : Performance Unit
  followedGuideline : Option Bool := none
  stronglySuspectedMeningitisOrEncephalitis : Option Bool := none
  forCsfPathogenDetection : Option Bool := none
  specifiedSimultaneousCsfPanel : Option Bool := none
  evidence : D023Schedule.Evidence
  treatmentScope : Scope
  history : ClaimHistory Nat
  separatelyBilled : Option (List (Performance SeriesTest)) := none

def CsfPanelContext.prior (c : CsfPanelContext) : Option Nat := do
  let series ← c.performance.series
  if c.treatmentScope.institution = some c.performance.site.institution ∧
      c.treatmentScope.Includes c.performance.site = true then
    count c.history c.treatmentScope (· == series)
  else none

def csfPanelIndication : Rule CsfPanelContext Unit :=
  ⟨"notice/D023/paragraph/39/a", addedNotice "(39)ア" "400", fun c _ =>
    c.followedGuideline = some true ∧ c.stronglySuspectedMeningitisOrEncephalitis = some true ∧
    c.forCsfPathogenDetection = some true ∧ c.specifiedSimultaneousCsfPanel = some true ∧
    c.prior = some 0⟩

def csfPanelDocumentation : Rule CsfPanelContext (Bool × Bool) :=
  ⟨"notice/D023/paragraph/39/a", addedNotice "(39)ア 摘要" "400", fun _ recorded =>
    recorded = (true, true)⟩

private def csfExclusion (suffix : String) (matchTest : SeriesTest → Option Bool) :
    Rule CsfPanelContext Unit :=
  ⟨"notice/D023/paragraph/39/i/" ++ suffix, addedNotice "(39)イ 一連の治療中の別算定" "400",
    fun c _ => ∃ related, c.separatelyBilled = some related ∧
      SeriesExcludes c.performance related matchTest⟩

def csfExclusionI := csfExclusion "i" csfTiter
def csfExclusionRo := csfExclusion "ro" (exactSeriesTest (.antibody .pneumococcusAntigen))
def csfExclusionHa := csfExclusion "ha" (exactSeriesTest (.antibody .nontypeableHaemophilus))
def csfExclusionNi := csfExclusion "ni" (exactSeriesTest (.antibody .cryptococcusQual))
def csfExclusionHo := csfExclusion "ho" (exactSeriesTest (.antibody .cryptococcusSemi))
def csfExclusionHe := csfExclusion "he" (fun test => some (test == .antibody .herpesAntigen || test == .antibody .herpesSkin))
def csfExclusionTo := csfExclusion "to" (fun test => some (test == .antibody .herpesCornea || test == .antibody .herpesGenital))
def csfExclusionChi := csfExclusion "chi" (exactSeriesTest (.antibody .pneumococcusCapsule))
def csfExclusionRi := csfExclusion "ri" (exactSeriesTest (.antibody .cmvPp65))
def csfExclusionNu := csfExclusion "nu" (fun test => some (test == .molecular 17 4 || test == .molecular 17 5))
def csfExclusionRu := csfExclusion "ru" (exactSeriesTest (.molecular 21 0))

def csfExclusions := [
  csfExclusionI, csfExclusionRo, csfExclusionHa, csfExclusionNi,
  csfExclusionHo, csfExclusionHe, csfExclusionTo, csfExclusionChi,
  csfExclusionRi, csfExclusionNu, csfExclusionRu]

def csfPanelExclusions : Rule CsfPanelContext Unit :=
  ⟨"notice/D023/paragraph/39/i", addedNotice "(39)イ" "400", fun c _ =>
    Satisfies csfExclusions c ()⟩

def csfPanel : Rule CsfPanelContext Unit :=
  ⟨"notice/D023/paragraph/39", addedNotice "(39)" "400", fun c _ =>
    csfPanelIndication.holds c () ∧ csfPanelExclusions.holds c ()⟩

def CsfPanelEligible (c : CsfPanelContext) : Prop :=
  c.evidence.tier = .sepsisOrCsfPanel ∧ c.evidence.csfPanel = some true ∧
    D023Schedule.csfPanelFacility.holds c.evidence () ∧ csfPanel.holds c ()

theorem csf_panel_determines (c : CsfPanelContext) (_ : CsfPanelEligible c) :
    DeterminesAt D023Schedule.rates .sepsisOrCsfPanel :=
  D023Schedule.base_determines _ trivial

structure PneumoniaPanelContext where
  performance : Performance Unit
  severePneumoniaDiagnosed : Option Bool := none
  sputumOrBronchoalveolarLavage : Option Bool := none
  simultaneousQualitativeMicroarray : Option Bool := none
  detectedSpecifiedKinds : Option Bool := none
  targetCount : Option Nat := none
  /-- 通知(36)ア(ロ)に該当する病床と集中治療相当性の確認。 -/
  treatedInOtherBed : Option Bool := none
  confirmedEquivalentIntensiveCare : Option Bool := none
  evidence : D023Schedule.Evidence
  treatmentScope : Scope
  history : ClaimHistory Nat
  separatelyBilled : Option (List (Performance SeriesTest)) := none

def PneumoniaPanelContext.prior (c : PneumoniaPanelContext) : Option Nat := do
  let series ← c.performance.series
  if c.treatmentScope.institution = some c.performance.site.institution ∧
      c.treatmentScope.Includes c.performance.site = true then
    count c.history c.treatmentScope (· == series)
  else none

def pneumoniaPanelOtherBed : Rule PneumoniaPanelContext Unit :=
  ⟨"notice/D023/paragraph/36/a/ro", addedNotice "(36)ア(ロ)" "396", fun c _ =>
    c.treatedInOtherBed = some true ∧ c.confirmedEquivalentIntensiveCare = some true⟩

def pneumoniaPanelOutpatientRoute : Rule PneumoniaPanelContext Unit :=
  ⟨"notice/D023/paragraph/36/a", addedNotice "(36)ア 外来の参照範囲" "395–396",
    pneumoniaPanelOtherBed.holds⟩

def pneumoniaPanelOtherBedDocumentation : Rule PneumoniaPanelContext Bool :=
  ⟨"notice/D023/paragraph/36/a/ro", addedNotice "(36)ア(ロ) 摘要" "396",
    fun _ documented => documented = true⟩

private def pneumoniaPanelExclusion (suffix : String) (matchTest : SeriesTest → Option Bool) :
    Rule PneumoniaPanelContext Unit :=
  ⟨"notice/D023/paragraph/36/i/" ++ suffix, addedNotice "(36)イ 一連の治療中の別算定" "396",
    fun c _ => ∃ related, c.separatelyBilled = some related ∧
      SeriesExcludes c.performance related matchTest⟩

def pneumoniaPanelI := pneumoniaPanelExclusion "i" (exactSeriesTest (.antibody .mycoplasmaQual))
def pneumoniaPanelRo := pneumoniaPanelExclusion "ro" (exactSeriesTest (.antibody .mycoplasmaSemi))
def pneumoniaPanelHa := pneumoniaPanelExclusion "ha" respiratoryTiter
def pneumoniaPanelNi := pneumoniaPanelExclusion "ni" (exactSeriesTest (.antibody .influenzaAntigen))
def pneumoniaPanelHo := pneumoniaPanelExclusion "ho" (exactSeriesTest (.antibody .rsAntigen))
def pneumoniaPanelHe := pneumoniaPanelExclusion "he" (exactSeriesTest (.antibody .metapneumovirusAntigen))
def pneumoniaPanelTo := pneumoniaPanelExclusion "to" (exactSeriesTest (.antibody .mycoplasmaChromatography))
def pneumoniaPanelChi := pneumoniaPanelExclusion "chi" (exactSeriesTest (.antibody .mycoplasmaFluorescence))
def pneumoniaPanelRi := pneumoniaPanelExclusion "ri" (exactSeriesTest (.antibody .nonStoolAdenovirus))
def pneumoniaPanelNu := pneumoniaPanelExclusion "nu" (exactSeriesTest (.antibody .pneumococcusCapsule))
def pneumoniaPanelRu := pneumoniaPanelExclusion "ru" fun test =>
  some (test == .molecular 6 0 || test == .molecular 6 1 || test == .molecular 6 2)
def pneumoniaPanelWo := pneumoniaPanelExclusion "wo" (exactSeriesTest (.molecular 7 0))
def pneumoniaPanelWa := pneumoniaPanelExclusion "wa" (exactSeriesTest (.molecular 13 1))
def pneumoniaPanelKa := pneumoniaPanelExclusion "ka" (exactSeriesTest (.molecular 17 1))

def pneumoniaPanelExclusions : Rule PneumoniaPanelContext Unit :=
  ⟨"notice/D023/paragraph/36/i", addedNotice "(36)イ" "396", fun c _ =>
    Satisfies [pneumoniaPanelI, pneumoniaPanelRo, pneumoniaPanelHa, pneumoniaPanelNi,
      pneumoniaPanelHo, pneumoniaPanelHe, pneumoniaPanelTo, pneumoniaPanelChi,
      pneumoniaPanelRi, pneumoniaPanelNu, pneumoniaPanelRu, pneumoniaPanelWo,
      pneumoniaPanelWa, pneumoniaPanelKa] c ()⟩

def pneumoniaPanel : Rule PneumoniaPanelContext Unit :=
  ⟨"notice/D023/paragraph/36", addedNotice "(36) 外来の参照範囲" "395–396", fun c _ =>
    c.severePneumoniaDiagnosed = some true ∧ c.sputumOrBronchoalveolarLavage = some true ∧
    c.simultaneousQualitativeMicroarray = some true ∧ c.detectedSpecifiedKinds = some true ∧
    (∃ n, c.targetCount = some n ∧ 30 ≤ n) ∧ c.prior = some 0 ∧
    pneumoniaPanelOutpatientRoute.holds c () ∧ pneumoniaPanelExclusions.holds c ()⟩

def pneumoniaPanelDocumentation : Rule PneumoniaPanelContext Date :=
  ⟨"notice/D023/paragraph/36", addedNotice "(36) 摘要" "395–396", fun c recorded =>
    recorded = c.performance.site.date⟩

def PneumoniaPanelEligible (c : PneumoniaPanelContext) : Prop :=
  c.evidence.tier = .pneumoniaResistancePanel ∧
    D023Schedule.pneumoniaPanelFacility.holds c.evidence () ∧ pneumoniaPanel.holds c ()

end Sanri.MedicalFee.D023
