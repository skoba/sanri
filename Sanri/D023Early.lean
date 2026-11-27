import Sanri.D023Additional

namespace Sanri.MedicalFee.D023

open Sanri.Logic Sanri.History

private def condition (id page : String) (p : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D023/paragraph/" ++ id,
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF" ++ page ++ "頁 D023 " ++ id, .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c _ => p c⟩

inductive GenitourinaryTest where
  | trachomatis | gonococcus | combined
  deriving DecidableEq

inductive GenitourinarySample where
  | urinary | genital | pharyngeal | rectal | other
  deriving DecidableEq

inductive GenitourinaryMethod where
  | pcr | pcrHybridization | lcr | lcrEia | hybridCapture | tmaHpaDka
  | tmaHybridization | sda | trc | dnaProbe | other
  deriving DecidableEq

structure GenitourinaryContext where
  performance : Performance GenitourinaryTest
  sample : GenitourinarySample
  method : GenitourinaryMethod
  /-- 条項に列挙された相手検査との併施と、主たる検査の確認結果。 -/
  comparison : Option SelectedTest := none
  suspectedEitherOrCoinfection : Option Bool := none
  difficultToDistinguishBasedOnOtherFindings : Option Bool := none
  forTreatmentSelection : Option Bool := none
  diagnosedCoinfection : Option Bool := none
  forTreatmentEffect : Option Bool := none

private def AllowsGenitourinary (c : GenitourinaryContext) (methods pharyngeal : List GenitourinaryMethod) : Prop :=
  (c.sample ∈ [.urinary, .genital] ∧ c.method ∈ methods) ∨
  (c.sample = .pharyngeal ∧ c.method ∈ pharyngeal) ∨
  (c.sample = .rectal ∧ c.method ∈ [.pcr, .pcrHybridization])

private def ThisOrUnpaired (selection : Option SelectedTest) : Prop :=
  selection ∈ [some .noCounterpart, some .thisTest]

def trachomatisChoice : Rule GenitourinaryContext Unit :=
  condition "1/a" "388" fun c => c.performance.item = .trachomatis → ThisOrUnpaired c.comparison

def trachomatisMethod : Rule GenitourinaryContext Unit :=
  condition "1/i" "388" fun c => c.performance.item = .trachomatis →
    let methods := [.pcr, .pcrHybridization, .lcr, .hybridCapture, .tmaHpaDka,
      .tmaHybridization, .sda, .trc]
    AllowsGenitourinary c methods methods

def trachomatis : Rule GenitourinaryContext Unit :=
  condition "1" "388" fun c => trachomatisChoice.holds c () ∧ trachomatisMethod.holds c ()

def gonococcusChoice : Rule GenitourinaryContext Unit :=
  condition "2/a" "388" fun c => c.performance.item = .gonococcus → ThisOrUnpaired c.comparison

def gonococcusMethod : Rule GenitourinaryContext Unit :=
  condition "2/i" "388" fun c => c.performance.item = .gonococcus →
    let shared := [.pcrHybridization, .tmaHpaDka, .sda, .trc]
    AllowsGenitourinary c (.dnaProbe :: .lcrEia :: shared) shared

def gonococcus : Rule GenitourinaryContext Unit :=
  condition "2" "388" fun c => gonococcusChoice.holds c () ∧ gonococcusMethod.holds c ()

def combinedGenitourinaryIndication : Rule GenitourinaryContext Unit :=
  condition "5/a" "389" fun c => c.performance.item = .combined →
    ((c.suspectedEitherOrCoinfection = some true ∧ c.difficultToDistinguishBasedOnOtherFindings = some true ∧
      c.forTreatmentSelection = some true) ∨
      (c.diagnosedCoinfection = some true ∧ c.forTreatmentEffect = some true)) ∧ ThisOrUnpaired c.comparison

def combinedGenitourinaryMethod : Rule GenitourinaryContext Unit :=
  condition "5/i" "389" fun c => c.performance.item = .combined →
    let methods := [.pcrHybridization, .tmaHpaDka, .sda, .trc]
    AllowsGenitourinary c methods methods

def combinedGenitourinary : Rule GenitourinaryContext Unit :=
  condition "5" "389" fun c => combinedGenitourinaryIndication.holds c () ∧
    combinedGenitourinaryMethod.holds c ()

structure GroupAStrepContext where
  performance : Performance Unit
  ageYears : Option Nat := none
  suspectedGroupAStrep : Option Bool := none
  isothermalAmplification : Option Bool := none
  explainedOnTestDay : Option Bool := none
  comparisonWithAntigenOrCulture : Option SelectedTest := none

def groupAStrep : Rule GroupAStrepContext Unit :=
  condition "3" "388–389" fun c => (∃ age, c.ageYears = some age ∧ age < 15) ∧
    c.suspectedGroupAStrep = some true ∧ c.isothermalAmplification = some true ∧
    c.explainedOnTestDay = some true ∧ ThisOrUnpaired c.comparisonWithAntigenOrCulture

inductive HbvMethod where
  | branchedDnaProbe | tma | pcr | other
  deriving DecidableEq

structure HbvContext where
  performance : Performance Unit
  method : HbvMethod
  considersReactivation : Option Bool := none
  priorHbvInfection : Option Bool := none
  immunosuppressionOrChemotherapyForLymphomaOrSimilar : Option Bool := none
  /-- 現在治療中又は終了後１年以内であることの照合結果。 -/
  duringOrWithinYearAfterTreatment : Option Bool := none
  monthlyClaims : Option (ClaimHistory Unit) := none

def hbvQuantity : Rule HbvContext Unit :=
  condition "4" "389" fun c =>
    c.method ∈ [.branchedDnaProbe, .tma, .pcr] ∧
      (c.considersReactivation = some false ∨
        (c.considersReactivation = some true ∧ c.priorHbvInfection = some true ∧
          c.immunosuppressionOrChemotherapyForLymphomaOrSimilar = some true ∧
          c.duringOrWithinYearAfterTreatment = some true ∧
          ∃ h, c.monthlyClaims = some h ∧ count h c.performance.site.monthScope (fun _ => true) = some 0))

structure InfluenzaContext where
  ageYears : Option Nat := none
  pregnant : Option Bool := none
  otherRiskOfSevereDisease : Option Bool := none
  performedWithinTwelveHoursOfOnset : Option Bool := none
  explainedOnTestDay : Option Bool := none

def influenzaYoung : Rule InfluenzaContext Unit :=
  condition "6/a" "389" fun c => ∃ age, c.ageYears = some age ∧ age < 5

def influenzaOlder : Rule InfluenzaContext Unit :=
  condition "6/i" "389" fun c => ∃ age, c.ageYears = some age ∧ 65 ≤ age

def influenzaPregnant : Rule InfluenzaContext Unit :=
  condition "6/u" "389" fun c => c.pregnant = some true

def influenzaRisk : Rule InfluenzaContext Unit :=
  condition "6/e" "389" fun c => c.otherRiskOfSevereDisease = some true

def influenza : Rule InfluenzaContext Unit :=
  condition "6" "389" fun c => c.performedWithinTwelveHoursOfOnset = some true ∧
    c.explainedOnTestDay = some true ∧
    (influenzaYoung.holds c () ∨ influenzaOlder.holds c () ∨
      influenzaPregnant.holds c () ∨ influenzaRisk.holds c ())

def influenzaDocumentation : Rule InfluenzaContext Bool :=
  ⟨"notice/D023/paragraph/6", influenza.source, fun _ necessityRecorded => necessityRecorded = true⟩

structure RsContext where
  ageMonths : Option Nat := none
  antibodyProphylaxisIndicated : Option Bool := none
  suspectedRs : Option Bool := none
  negativeRsAntigen : Option Bool := none
  forDiagnosis : Option Bool := none
  nasalSwab : Option Bool := none
  nearMethod : Option Bool := none

def rsInpatient : Rule RsContext Unit :=
  condition "7/a" "389" fun _ => False

def rsInfant : Rule RsContext Unit :=
  condition "7/i" "389" fun c => ∃ age, c.ageMonths = some age ∧ age < 12

def rsProphylaxis : Rule RsContext Unit :=
  condition "7/u" "389" fun c => c.antibodyProphylaxisIndicated = some true

def rs : Rule RsContext Unit :=
  condition "7" "389" fun c => c.suspectedRs = some true ∧ c.negativeRsAntigen = some true ∧
    c.forDiagnosis = some true ∧ c.nasalSwab = some true ∧ c.nearMethod = some true ∧
    (rsInfant.holds c () ∨ rsProphylaxis.holds c ())

end Sanri.MedicalFee.D023
