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

end Sanri.MedicalFee.D023
