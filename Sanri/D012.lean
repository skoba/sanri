import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment
import Sanri.SpecimenCollection

namespace Sanri.MedicalFee.D012

open Sanri.Logic Sanri.History

/-- 基準診療日2026-10-22の外来。条項別に対応した検査種類。 -/
inductive Item where
  | stsQual | asoQual | asoSemi | asoQuant
  | toxoplasmaQual | toxoplasmaSemi
  | askQual | askSemi
  | treponemaQual | mycoplasmaQual | mycoplasmaSemi
  | stsSemi | stsQuant
  | treponemaSemi | treponemaQuant
  | stoolAdenovirus | urease
  | stoolRotavirusQual | stoolRotavirusQuant
  | pyloriQualSemi | pneumoniaeIgG
  | pneumoniaeIgA
  | viralTiter
  | pyloriAntibody | pertussisQual | pertussisSemi
  | htlvQual | htlvSemi | toxoplasmaAntibody | toxoplasmaIgM | difficileAntigen
  | hiv12Qual | hiv12Semi | hiv12ComboQual
  | hiv1Antibody
  | rapidGroupAStrep
  | hiv12Quant
  | hibAntigen
  | hiv12ComboQuant
  | influenzaAntigen
  | candidaQual | candidaSemi | candidaQuant | ftaAbsQual | ftaAbsSemi
  | rsAntigen | pyloriAntigen
  | metapneumovirusAntigen
  | pneumococcusAntigen
  | mycoplasmaChromatography
  | norovirusAntigen | nontypeableHaemophilus | covidQual
  | mycobacteriumQuant | mycobacteriumQual
  | pneumoniaeIgM | trachomatisAntigen
  | ecoliO157Antibody
  | aspergillusAntigen
  | htlvAntibody
  | arabinitol
  | ecoliO157Antigen
  | cryptococcusQual
  | cryptococcusSemi
  | mycoplasmaFluorescence
  | nonStoolAdenovirus
  | ecoliSerotype
  | pneumococcusWall
  | gonococcusAntigen | herpesAntigen | herpesSkin
  | campylobacterAntigen
  | betaGlucan
  | brucellaQual | brucellaSemi | trachomatisClass
  | classSpecificTiter
  | scrubTyphusQual | scrubTyphusSemi
  | legionellaAntigen
  | herpesCornea | herpesGenital | anisakisAntibody
  | pertussisAntigen
  | pneumococcusCapsule
  | amoebaAntibodySemi | amoebaAntigen | amoebaAntibodyQual
  | covidFlu
  | varicellaAntigen
  | endotoxin
  | dengueAntigen | dengueCombo | dermatophyteAntigen
  | pertussisAntibody
  | hiv1WesternBlot
  | tuberculosisAntigen
  | cmvPp65
  | hiv2WesternBlot
  | aspergillusIgG
  | covidRs | covidFluRs
  | htlvBlot | toxoplasmaAvidity
  | covidQuant
  | hivAntigen
  | hivSpecific
  | trichosporonAntibody
  | birdIgG
  | aav9 | aavRh74
  deriving DecidableEq

def Item.number : Item → Nat
  | .stsQual | .asoQual | .asoSemi | .asoQuant => 1
  | .toxoplasmaQual | .toxoplasmaSemi => 2
  | .askQual | .askSemi => 3
  | .treponemaQual | .mycoplasmaQual | .mycoplasmaSemi => 4
  | .stsSemi | .stsQuant => 5
  | .treponemaSemi | .treponemaQuant => 6
  | .stoolAdenovirus | .urease => 7
  | .stoolRotavirusQual | .stoolRotavirusQuant => 8
  | .pyloriQualSemi | .pneumoniaeIgG => 9
  | .pneumoniaeIgA => 10
  | .viralTiter => 11
  | .pyloriAntibody | .pertussisQual | .pertussisSemi => 12
  | .htlvQual | .htlvSemi => 13
  | .toxoplasmaAntibody => 14
  | .toxoplasmaIgM | .difficileAntigen => 15
  | .hiv12Qual | .hiv12Semi | .hiv12ComboQual => 16
  | .hiv1Antibody => 17
  | .rapidGroupAStrep => 18
  | .hiv12Quant => 19
  | .hibAntigen => 20
  | .hiv12ComboQuant => 21
  | .influenzaAntigen => 22
  | .candidaQual | .candidaSemi | .candidaQuant | .ftaAbsQual | .ftaAbsSemi => 23
  | .rsAntigen | .pyloriAntigen => 24
  | .metapneumovirusAntigen => 25
  | .pneumococcusAntigen => 26
  | .mycoplasmaChromatography => 27
  | .norovirusAntigen | .nontypeableHaemophilus | .covidQual => 28
  | .mycobacteriumQuant | .mycobacteriumQual => 29
  | .pneumoniaeIgM | .trachomatisAntigen => 30
  | .ecoliO157Antibody => 31
  | .aspergillusAntigen => 32
  | .htlvAntibody => 33
  | .arabinitol => 34
  | .ecoliO157Antigen => 35
  | .cryptococcusQual => 36
  | .cryptococcusSemi => 37
  | .mycoplasmaFluorescence => 38
  | .nonStoolAdenovirus => 39
  | .ecoliSerotype => 40
  | .pneumococcusWall => 41
  | .gonococcusAntigen | .herpesAntigen | .herpesSkin => 42
  | .campylobacterAntigen => 43
  | .betaGlucan => 44
  | .brucellaQual | .brucellaSemi | .trachomatisClass => 45
  | .classSpecificTiter => 46
  | .scrubTyphusQual | .scrubTyphusSemi => 47
  | .legionellaAntigen => 48
  | .herpesCornea | .herpesGenital | .anisakisAntibody => 49
  | .pertussisAntigen => 50
  | .pneumococcusCapsule => 51
  | .amoebaAntibodySemi | .amoebaAntigen | .amoebaAntibodyQual => 52
  | .covidFlu => 53
  | .varicellaAntigen => 54
  | .endotoxin => 55
  | .dengueAntigen | .dengueCombo | .dermatophyteAntigen => 56
  | .pertussisAntibody => 57
  | .hiv1WesternBlot => 58
  | .tuberculosisAntigen => 59
  | .cmvPp65 => 60
  | .hiv2WesternBlot => 61
  | .aspergillusIgG => 62
  | .covidRs | .covidFluRs => 63
  | .htlvBlot | .toxoplasmaAvidity => 64
  | .covidQuant => 65
  | .hivAntigen => 66
  | .hivSpecific => 67
  | .trichosporonAntibody => 68
  | .birdIgG => 69
  | .aav9 | .aavRh74 => 70

def Item.points : Item → Nat
  | .stsQual | .asoQual | .asoSemi | .asoQuant => 15
  | .toxoplasmaQual | .toxoplasmaSemi => 26
  | .askQual | .askSemi => 29
  | .treponemaQual | .mycoplasmaQual | .mycoplasmaSemi => 32
  | .stsSemi | .stsQuant => 34
  | .treponemaSemi | .treponemaQuant => 53
  | .stoolAdenovirus | .urease => 60
  | .stoolRotavirusQual | .stoolRotavirusQuant => 65
  | .pyloriQualSemi | .pneumoniaeIgG => 70
  | .pneumoniaeIgA => 75
  | .viralTiter => 79
  | .pyloriAntibody | .pertussisQual | .pertussisSemi => 80
  | .htlvQual | .htlvSemi => 85
  | .toxoplasmaAntibody => 93
  | .toxoplasmaIgM | .difficileAntigen => 95
  | .hiv12Qual | .hiv12Semi | .hiv12ComboQual => 109
  | .hiv1Antibody => 113
  | .rapidGroupAStrep => 121
  | .hiv12Quant => 124
  | .hibAntigen => 126
  | .hiv12ComboQuant => 127
  | .influenzaAntigen => 132
  | .candidaQual | .candidaSemi | .candidaQuant | .ftaAbsQual | .ftaAbsSemi => 134
  | .rsAntigen | .pyloriAntigen => 138
  | .metapneumovirusAntigen => 141
  | .pneumococcusAntigen => 146
  | .mycoplasmaChromatography => 148
  | .norovirusAntigen | .nontypeableHaemophilus | .covidQual => 150
  | .mycobacteriumQuant | .mycobacteriumQual => 151
  | .pneumoniaeIgM | .trachomatisAntigen => 152
  | .ecoliO157Antibody => 155
  | .aspergillusAntigen => 157
  | .htlvAntibody => 159
  | .arabinitol => 160
  | .ecoliO157Antigen => 161
  | .cryptococcusQual => 164
  | .cryptococcusSemi => 166
  | .mycoplasmaFluorescence => 170
  | .nonStoolAdenovirus => 174
  | .ecoliSerotype => 175
  | .pneumococcusWall => 179
  | .gonococcusAntigen | .herpesAntigen | .herpesSkin => 180
  | .campylobacterAntigen => 184
  | .betaGlucan => 190
  | .brucellaQual | .brucellaSemi | .trachomatisClass => 200
  | .classSpecificTiter => 200
  | .scrubTyphusQual | .scrubTyphusSemi => 203
  | .legionellaAntigen => 205
  | .herpesCornea | .herpesGenital | .anisakisAntibody => 210
  | .pertussisAntigen => 217
  | .pneumococcusCapsule => 220
  | .amoebaAntibodySemi | .amoebaAntigen | .amoebaAntibodyQual => 223
  | .covidFlu => 225
  | .varicellaAntigen => 227
  | .endotoxin => 229
  | .dengueAntigen | .dengueCombo | .dermatophyteAntigen => 233
  | .pertussisAntibody => 250
  | .hiv1WesternBlot => 280
  | .tuberculosisAntigen => 291
  | .cmvPp65 => 356
  | .hiv2WesternBlot => 380
  | .aspergillusIgG => 390
  | .covidRs | .covidFluRs => 420
  | .htlvBlot | .toxoplasmaAvidity => 425
  | .covidQuant => 560
  | .hivAntigen => 600
  | .hivSpecific => 660
  | .trichosporonAntibody => 798
  | .birdIgG => 873
  | .aav9 | .aavRh74 => 12850

def Item.variant : Item → Nat
  | .hiv12Semi => 1
  | .hiv12ComboQual => 2
  | .asoQual | .toxoplasmaSemi | .askSemi | .mycoplasmaQual | .stsQuant | .treponemaQuant | .urease | .stoolRotavirusQuant | .pneumoniaeIgG | .pertussisQual | .htlvSemi | .difficileAntigen => 1
  | .asoSemi | .mycoplasmaSemi | .pertussisSemi => 2
  | .asoQuant => 3
  | .candidaSemi => 1
  | .candidaQuant => 2
  | .ftaAbsQual => 3
  | .ftaAbsSemi => 4
  | .pyloriAntigen => 1
  | .nontypeableHaemophilus => 1
  | .covidQual => 2
  | .mycobacteriumQual => 1
  | .trachomatisAntigen => 1
  | .herpesAntigen => 1
  | .herpesSkin => 2
  | .brucellaSemi => 1
  | .trachomatisClass => 2
  | .scrubTyphusSemi => 1
  | .herpesGenital => 1
  | .anisakisAntibody => 2
  | .amoebaAntigen => 1
  | .amoebaAntibodyQual => 2
  | .dengueCombo => 1
  | .dermatophyteAntigen => 2
  | .covidFluRs => 1
  | .toxoplasmaAvidity => 1
  | .aavRh74 => 1
  | _ => 0

def ledgerItems : List Item :=
  [.stsQual, .asoQual, .asoSemi, .asoQuant,
    .toxoplasmaQual, .toxoplasmaSemi,
    .askQual, .askSemi,
    .treponemaQual, .mycoplasmaQual, .mycoplasmaSemi,
    .stsSemi, .stsQuant,
    .treponemaSemi, .treponemaQuant,
    .stoolAdenovirus, .urease,
    .stoolRotavirusQual, .stoolRotavirusQuant,
    .pyloriQualSemi, .pneumoniaeIgG,
    .pneumoniaeIgA,
    .viralTiter,
    .pyloriAntibody, .pertussisQual, .pertussisSemi, .htlvQual, .htlvSemi,
    .toxoplasmaAntibody, .toxoplasmaIgM, .difficileAntigen,
    .hiv12Qual, .hiv12Semi, .hiv12ComboQual, .hiv1Antibody, .rapidGroupAStrep,
    .hiv12Quant, .hibAntigen, .hiv12ComboQuant,
    .influenzaAntigen,
    .candidaQual, .candidaSemi, .candidaQuant, .ftaAbsQual, .ftaAbsSemi,
    .rsAntigen, .pyloriAntigen,
    .metapneumovirusAntigen,
    .pneumococcusAntigen,
    .mycoplasmaChromatography,
    .norovirusAntigen, .nontypeableHaemophilus, .covidQual,
    .mycobacteriumQuant, .mycobacteriumQual,
    .pneumoniaeIgM, .trachomatisAntigen,
    .ecoliO157Antibody,
    .aspergillusAntigen,
    .htlvAntibody,
    .arabinitol,
    .ecoliO157Antigen,
    .cryptococcusQual,
    .cryptococcusSemi,
    .mycoplasmaFluorescence,
    .nonStoolAdenovirus,
    .ecoliSerotype,
    .pneumococcusWall,
    .gonococcusAntigen, .herpesAntigen, .herpesSkin,
    .campylobacterAntigen,
    .betaGlucan,
    .brucellaQual, .brucellaSemi, .trachomatisClass,
    .classSpecificTiter,
    .scrubTyphusQual, .scrubTyphusSemi,
    .legionellaAntigen,
    .herpesCornea, .herpesGenital, .anisakisAntibody,
    .pertussisAntigen,
    .pneumococcusCapsule,
    .amoebaAntibodySemi, .amoebaAntigen, .amoebaAntibodyQual,
    .covidFlu,
    .varicellaAntigen,
    .endotoxin,
    .dengueAntigen, .dengueCombo, .dermatophyteAntigen,
    .pertussisAntibody,
    .hiv1WesternBlot,
    .tuberculosisAntigen,
    .cmvPp65,
    .hiv2WesternBlot,
    .aspergillusIgG,
    .covidRs, .covidFluRs,
    .htlvBlot, .toxoplasmaAvidity,
    .covidQuant,
    .hivAntigen,
    .hivSpecific,
    .trichosporonAntibody,
    .birdIgG,
    .aav9, .aavRh74]

private def primary (page : Nat) (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度・2026-06-01適用",
    s!"PDF{page}頁 D012 {loc}", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (pages loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    s!"PDF{pages}頁 D012({loc})", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def itemRule (i : Item) : Rule Item Nat :=
  let n := toString i.number
  let page := if i.number ≤ 18 then 184 else if i.number ≤ 56 then 185 else 186
  ⟨"primary/D012/item/" ++ n, primary page n,
    fun candidate p => candidate = i → p = i.points⟩

def rules : List (Rule Item Nat) := ledgerItems.map itemRule

theorem rate_iff (i : Item) (p : Nat) :
    Satisfies rules i p ↔ p = i.points := by
  constructor
  · intro h
    exact h _ (List.mem_map.mpr ⟨i, by cases i <;> simp [ledgerItems], rfl⟩) rfl
  · intro h _ hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro hi
    simpa [hi] using h

inductive Target where
  | adenovirus | coxsackie | cytomegalovirus | eb | echo | herpes
  | influenzaA | influenzaB | mumps | parainfluenzaI | parainfluenzaII | parainfluenzaIII
  | parvovirusB19
  | polioI | polioII | polioIII | rs | rubella | measles | japaneseEncephalitis
  | psittacosis | varicellaZoster
  deriving DecidableEq

inductive RelatedTest where
  | local (item : Item)
  | dengueNs1 | dengueIgG | dengueIgM
  | bacterialCultureD018 | gastrointestinalCultureD018 | pertussisD023_13 | multiplexD023_25
  | pneumoniaeD023_13


  deriving DecidableEq

inductive PyloriMethod where
  | la | immunochromatography | goldColloid | simpleEia
  deriving DecidableEq

inductive AntibodyClass where
  | igg | iga | igm
  deriving DecidableEq

structure Combined where
  /-- 当該通知の「併せて」に該当することを確認した実施群。 -/
  members : List (Performance RelatedTest)
  /-- 医学的判断又は選択で確定した算定対象の実施ID。 -/
  selected : Option (List Nat) := none
  viralTarget : Nat → Option Target := fun _ => none
  antibodyClass : Nat → Option AntibodyClass := fun _ => none
  scrubTyphusStrain : Nat → Option Nat := fun _ => none
  coexistingAspergillosisSuspected : Option Bool := none

inductive HivMethod where
  | la | eia | pa | immunochromatography | other
  deriving DecidableEq

inductive HistoricalBleeding where
  | neonatalOrSimilar | severeLiverDisease | digestiveDisease | surgeryOrDelivery
  deriving DecidableEq

inductive HivIndication where
  | documentedUnheatedFactor
  | undocumentedFactor (inpatientYear : Nat) (bleeding : HistoricalBleeding)
  | suspectedWithDifferentialDisease
  | suspectedWithAssociatedSexuallyTransmittedInfection
  deriving DecidableEq

inductive TransfusionKind where
  | k920NonAutologous | plasmaProduct
  deriving DecidableEq

/-- 他機関の一連も識別する。算定履歴のキーには実施元機関も含める。 -/
structure TransfusionSeries where
  patient : Nat
  provider : Nat
  seriesId : Nat
  finalDay : Date
  kind : TransfusionKind

structure HivFollowUp where
  series : TransfusionSeries
  /-- 最終日から概ね2か月後に該当することを確認した外部判断。 -/
  approximatelyTwoMonths : Bool
  /-- 候補を除き、同じ一連に対する既算定を全機関について確認する。 -/
  history : ClaimHistory (Nat × Nat)

inductive HivRoute where
  | clinical (indication : HivIndication)
  | transfusion (followUp : HivFollowUp)

inductive Method where
  | immunochromatography | oia
  /-- OIA・免疫クロマト法以外で、当該抗原定性の実施方法であると確認したもの。 -/
  | otherFluAntigen
  | eia | elisa | la | goldColloid | serumAntibody | chromogenic | turbidimetric | westernBlot | immunostaining | lineBlot | clia | cleia | eclia | opticalWaveguide
  deriving DecidableEq

inductive Specimen where
  | urinary | genital | conjunctiva | nasopharynx | sputum | nasopharyngealSwab | stool | serum | nail | plasma | wholeBlood
  deriving DecidableEq

inductive ClinicalFact where
  | candidaBloodstreamDiagnosis | candidaPneumoniaDiagnosis
  | suspectedRs | palivizumabIndicated | nirsevimabIndicated
  | suspectedMetapneumovirus | pneumoniaStronglySuspectedOnImaging
  | pneumoniaStronglySuspectedOnAuscultation | suspectedNorovirus | confirmedMalignancy
  | organTransplant | receivingAntineoplasticOrImmunosuppressiveDrug
  | suspectedHaemophilus | otitisMedia | sinusitis | nontypeableHaemophilusDiagnosis
  | inclusionConjunctivitisOrTrachomaDiagnosis | infantTrachomatisPneumoniaDiagnosis
  | invasivePulmonaryAspergillosisDiagnosis | ecoliConfirmedByD018 | verotoxinConfirmedByD023_2
  | ecoliGrewOnSelectiveMedium | ecoliOAntigenIdentified | ecoliHAntigenIdentified
  | pneumoniaDiagnosis | lowerRespiratoryInfectionDiagnosis | otitisMediaAndSinusitisDiagnosis
  | trachomatisDiseaseDiagnosis | trachomatisAntigenUndetectable | trachomatisCollectionDifficult
  | youngChildPneumoniaDiagnosis | erythemaPresent | parvovirusStronglySuspected
  | legionellaSuspectedFromFindings | intestinalAnisakiasisDiagnosis
  | granulomatousChronicGastricAnisakiasisDiagnosis | ectopicAnisakiasisDiagnosis
  | suspectedCornealHerpesEpithelialLesion | pertussisGuidelineClinicalCase
  | priorSameTestNegative | noAlternativeDiagnosis | covidSuspected | covidDiagnosis
  | influenzaSuspected | influenzaDiagnosis | intestinalAmoebiasisSymptoms
  | amoebicDysenteryDiagnosis | amoebaGuidelineFollowed | amoebicLiverAbscessSuspected
  | amoebicColitisSuspected | amoebaStoolNegative | dengueSuspectedUnderGuideline
  | requiresHospitalization | epidemiologicalSurvey | onychomycosisSuspected
  | onychomycosisSuspectedFromFindings | kohCannotBePerformed | dermatophyteGuidelineFollowed
  | confirmsAmoebaGuidelineIdentity
  | confirmatoryDiagnosis | stemCellTransplant | hivInfection | severeCellularImmunodeficiency
  | rsDiagnosis | toxoplasmaManualFollowed | toxoplasmaIgMPositive | takingSpiramycin
  | toxoplasmaExceptionMedicallyNeeded | hivFollowUpPurpose | hivHighRisk | acuteInfectionSymptoms
  | summerPneumonitisDifferentialDiagnosis | summerPneumonitisSuspectedUnderCriteria
  | birdPneumonitisStronglySuspected | aavRepeatMedicallyNeeded | spinalMuscularAtrophy
  | onasemnogeneIndicationSupport | duchenneMuscularDystrophy | delandistrogeneIndicationSupport
  | herpesTypeIdentified | suspectedHerpesSkinLesion | initialHerpesPresentation
  | herpesRepeatMedicallyNeeded | suspectedCampylobacter | suspectedDeepFungalInfection
  | selectFungalTreatment | assessFungalTreatment
  deriving DecidableEq

inductive WallRoute where
  | respiratory | ent
  deriving DecidableEq

inductive RsRoute where
  | infant | prophylaxis | inpatient
  deriving DecidableEq

inductive NorovirusRoute where
  | young | older | malignancy | transplant | medication
  deriving DecidableEq

inductive KohRoute where
  | negative | unavailable
  deriving DecidableEq

structure PriorClaims where
  /-- 確認した算定履歴と条項の回数を数える範囲。算定項目と一連IDを別に記録する。 -/
  history : ClaimHistory (Item × Option Nat)
  scope : Scope

/-- 外来の保険医療機関で実施した確認済みの検査を受ける。 -/
structure Context where
  performance : Performance RelatedTest
  /-- 確認済みの併施なしは候補実施だけの群とする。同時実施には別途同時IDを使う。 -/
  combined : Option Combined := none
  method : Option Method := none
  specimen : Option Specimen := none
  /-- 診療所見・診断目的・外部指針に基づき確認した事実。 -/
  confirmed : ClinicalFact → Option Bool := fun _ => none
  ageYears : Option Nat := none
  hoursSinceOnset : Option Rat := none
  rsRoute : Option RsRoute := none
  antibodyClass : Option AntibodyClass := none
  priorClaims : Option PriorClaims := none
  strain : Option Nat := none
  kohRoute : Option KohRoute := none
  facilityStandardMet : Option Bool := none
  facilityNotified : Option Bool := none
  measurements : List (Performance RelatedTest) := []
  positiveScreen : Option (Performance RelatedTest) := none
  gestationWeeks : Option Nat := none
  wallRoute : Option WallRoute := none
  norovirusRoute : Option NorovirusRoute := none
  target : Option Target := none
  conventionalStsMethod : Option Bool := none
  /-- 同じSTS定性・半定量・定量区分で、確認された沈降反応の方法数。 -/
  stsMethodCount : Option Nat := none
  pyloriMethod : Option PyloriMethod := none
  pyloriNoticeSatisfied : Option Bool := none
  treatmentNecessity : Option Bool := none
  particleAgglutination : Option Bool := none
  hivRoute : Option HivRoute := none
  /-- 当該機関での採血を保健所に委託した検査に該当するか。 -/
  hivHealthCenterOutsourcing : Option Bool := none
  hivMethod : Option HivMethod := none
  aspergillus : Option SpecimenTests.AspergillusAssessment := none

private def condition (id pages paragraph : String) (holds : Context → Prop) :
    Rule Context Unit :=
  ⟨"notice/D012/paragraph/" ++ id, notice pages paragraph, fun c _ => holds c⟩

/-- 確認された併施群の局所IDを、患者・機関をまたいで再利用しない。 -/
def Combined.Valid (g : Combined) (p : Performance RelatedTest) : Prop :=
  p ∈ g.members ∧ (g.members.map (·.id)).Nodup ∧
    ∀ q ∈ g.members, q.site.patient = p.site.patient ∧ q.site.institution = p.site.institution

private def selectedFrom (g : Combined) (members : List (Performance RelatedTest))
    (p : Performance RelatedTest) (limit : Nat) : Prop :=
  ∃ ids, g.selected = some ids ∧
    let chosen := ids.filter fun id => members.any fun q => q.id == id
    chosen.Nodup ∧ chosen.length = limit ∧ p.id ∈ chosen

def stsRule : Rule Context Unit :=
  condition "1" "370" "1" fun c =>
    ∀ i ∈ [Item.stsQual, .stsSemi, .stsQuant], c.performance.item = .local i →
      c.conventionalStsMethod = some true ∧ ∃ n, c.stsMethodCount = some n ∧ 0 < n ∧
        (2 ≤ n → ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
          selectedFrom g (g.members.filter fun q => q.item == .local i) c.performance 1)

private def isMycoplasma (i : RelatedTest) : Bool :=
  decide (i ∈ [RelatedTest.local .mycoplasmaQual, .local .mycoplasmaSemi,
    .local .mycoplasmaChromatography, .local .mycoplasmaFluorescence])

private def mycoplasmaSelection (c : Context) : Prop :=
  isMycoplasma c.performance.item = true → ∃ g, c.combined = some g ∧
    g.Valid c.performance ∧
    let members := g.members.filter (isMycoplasma ∘ Performance.item)
    (2 ≤ members.length → selectedFrom g members c.performance 1)

def mycoplasmaAntibodyRule : Rule Context Unit :=
  condition "2" "370" "2" mycoplasmaSelection

def mycoplasmaChromatographyRule : Rule Context Unit :=
  condition "18" "373" "18" mycoplasmaSelection

def mycoplasmaFluorescenceRule : Rule Context Unit :=
  condition "29" "374" "29" mycoplasmaSelection

def ureaseRule : Rule Context Unit :=
  condition "3" "370" "3" fun c =>
    c.performance.item = .local .urease → c.pyloriNoticeSatisfied = some true

private def isRotavirus (i : RelatedTest) : Bool :=
  decide (i ∈ [RelatedTest.local .stoolRotavirusQual, .local .stoolRotavirusQuant])

def stoolAntigenRule : Rule Context Unit :=
  condition "4" "370" "4" fun c =>
    let p := c.performance
    (p.item = .local .stoolAdenovirus ∨ isRotavirus p.item = true) →
      ∃ g, c.combined = some g ∧ g.Valid p ∧
        let stool := g.members.filter fun q =>
          q.item == .local .stoolAdenovirus || isRotavirus q.item
        (∀ q ∈ stool, q.id ≠ p.id → (p.simultaneousWith q).isSome = true) ∧
        let simultaneous := stool.filter fun q => q.id == p.id || p.simultaneousWith q == some true
        (simultaneous.any (fun q => q.item == .local .stoolAdenovirus) = true →
          simultaneous.any (fun q => isRotavirus q.item) = true →
          selectedFrom g simultaneous p 1)

def pyloriMethodRule : Rule Context Unit :=
  condition "5/a" "370" "5 ア" fun c =>
    c.performance.item = .local .pyloriQualSemi → c.pyloriMethod.isSome = true

def pyloriReferenceRule : Rule Context Unit :=
  condition "5/i" "370" "5 イ" fun c =>
    c.performance.item = .local .pyloriQualSemi → c.pyloriNoticeSatisfied = some true

def pyloriRule : Rule Context Unit :=
  condition "5" "370" "5" fun c => pyloriMethodRule.holds c () ∧ pyloriReferenceRule.holds c ()

private def viralTargetRule (suffix page label : String) (target : Target) : Rule Context Unit :=
  condition ("6/a/" ++ suffix) page ("6 ア " ++ label) fun c =>
    c.performance.item = .local .viralTiter → c.target = some target →
      c.treatmentNecessity = some true

def viralAdenovirus := viralTargetRule "i" "370" "(イ)" .adenovirus
def viralCoxsackie := viralTargetRule "ro" "370" "(ロ)" .coxsackie
def viralCmv := viralTargetRule "ha" "370" "(ハ)" .cytomegalovirus
def viralEb := viralTargetRule "ni" "370" "(ニ)" .eb
def viralEcho := viralTargetRule "ho" "370" "(ホ)" .echo
def viralHerpes := viralTargetRule "he" "370" "(ヘ)" .herpes
def viralFluA := viralTargetRule "to" "370" "(ト)" .influenzaA
def viralFluB := viralTargetRule "chi" "370" "(チ)" .influenzaB
def viralMumps := viralTargetRule "ri" "370" "(リ)" .mumps
def viralParainfluenzaI := viralTargetRule "nu" "371" "(ヌ)" .parainfluenzaI
def viralParainfluenzaII := viralTargetRule "ru" "371" "(ル)" .parainfluenzaII
def viralParainfluenzaIII := viralTargetRule "wo" "371" "(ヲ)" .parainfluenzaIII
def viralPolioI := viralTargetRule "wa" "371" "(ワ)" .polioI
def viralPolioII := viralTargetRule "ka" "371" "(カ)" .polioII
def viralPolioIII := viralTargetRule "yo" "371" "(ヨ)" .polioIII
def viralRs := viralTargetRule "ta" "371" "(タ)" .rs
def viralRubella := viralTargetRule "re" "371" "(レ)" .rubella
def viralMeasles := viralTargetRule "so" "371" "(ソ)" .measles
def viralJapaneseEncephalitis := viralTargetRule "tsu" "371" "(ツ)" .japaneseEncephalitis
def viralPsittacosis := viralTargetRule "ne" "371" "(ネ)" .psittacosis
def viralVaricella := viralTargetRule "na" "371" "(ナ)" .varicellaZoster

def viralIndication : Rule Context Unit :=
  condition "6/a" "370–371" "6 ア" fun c =>
    c.performance.item = .local .viralTiter → c.treatmentNecessity = some true ∧
      c.target.isSome = true ∧ c.target ≠ some .parvovirusB19

def viralParagraph : Rule Context Unit :=
  condition "6" "370–371" "6" fun c => viralIndication.holds c ()

def pyloriAntibodyRule : Rule Context Unit :=
  condition "7" "371" "7" fun c =>
    c.performance.item = .local .pyloriAntibody → c.pyloriNoticeSatisfied = some true

def htlvRule : Rule Context Unit :=
  condition "8" "371" "8" fun c =>
    c.performance.item ∈ [RelatedTest.local .htlvQual, .local .htlvSemi] →
      c.particleAgglutination = some true

def pneumoniaeChoice : Rule Context Unit :=
  condition "23" "373" "23" fun c =>
    let antibodies := [RelatedTest.local .pneumoniaeIgG, .local .pneumoniaeIgA, .local .pneumoniaeIgM]
    c.performance.item ∈ antibodies → ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
      let members := g.members.filter fun q => decide (q.item ∈ antibodies)
      (members.any (fun q => q.item == .local .pneumoniaeIgM) = true →
        members.any (fun q => q.item == .local .pneumoniaeIgG ||
          q.item == .local .pneumoniaeIgA) = true →
        selectedFrom g members c.performance 1)

private def isFluTarget (t : Option Target) : Bool :=
  decide (t ∈ [some .influenzaA, some .influenzaB])

private def confirmedTargets (g : Combined) (c : Context) : Prop :=
  (∀ q ∈ g.members, q.item = .local .viralTiter → (g.viralTarget q.id).isSome = true) ∧
    (c.performance.item = .local .viralTiter → g.viralTarget c.performance.id = c.target)

private def isFluAntibody (g : Combined) (q : Performance RelatedTest) : Bool :=
  q.item == .local .viralTiter && isFluTarget (g.viralTarget q.id)

def influenzaChoice : Rule Context Unit :=
  condition "13/i" "372" "13 イ" fun c =>
    (c.performance.item = .local .influenzaAntigen ∨
      (c.performance.item = .local .viralTiter ∧ isFluTarget c.target = true)) →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧ confirmedTargets g c ∧
        (g.members.any (fun q => q.item == .local .influenzaAntigen) = true →
          g.members.any (isFluAntibody g) = true →
          selectedFrom g (g.members.filter fun q =>
            q.item == .local .influenzaAntigen || isFluAntibody g q) c.performance 1)

private inductive RespiratoryGroup where
  | influenza | metapneumovirus | rs
  deriving DecidableEq

private def respiratoryGroup (g : Combined) (q : Performance RelatedTest) :
    Option RespiratoryGroup :=
  match q.item with
  | .local .influenzaAntigen => some .influenza
  | .local .metapneumovirusAntigen => some .metapneumovirus
  | .local .rsAntigen => some .rs
  | .local .viralTiter => if isFluAntibody g q then some .influenza else none
  | _ => none

def metapneumovirusChoice : Rule Context Unit :=
  condition "17/a" "372–373" "17 ア" fun c =>
    (c.performance.item ∈ [RelatedTest.local .influenzaAntigen, .local .rsAntigen,
      .local .metapneumovirusAntigen] ∨
      (c.performance.item = .local .viralTiter ∧ isFluTarget c.target = true)) →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧ confirmedTargets g c ∧
        ((g.members.filterMap (respiratoryGroup g)).eraseDups.length = 3 →
          ∃ ids, g.selected = some ids ∧ c.performance.id ∈ ids ∧
            ((g.members.filter fun q => decide (q.id ∈ ids)).filterMap
              (respiratoryGroup g)).eraseDups.length = 2)

def viralClassChoice : Rule Context Unit :=
  condition "38/u" "375" "38 ウ" fun c =>
    c.performance.item ∈ [RelatedTest.local .viralTiter, .local .classSpecificTiter] →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        let other := g.members.filter fun q => if c.performance.item = .local .viralTiter then q.item == .local .classSpecificTiter
          else q.item == .local .viralTiter
        (other ≠ [] → ∃ ids, g.selected = some ids ∧ c.performance.id ∈ ids ∧
          ∀ q ∈ other, q.id ∉ ids)

def aspergillusRule : Rule Context Unit :=
  { id := "notice/D012/paragraph/52"
    source := { SpecimenTests.d012AspergillusSource with
      url := some "https://www.mhlw.go.jp/content/12400000/001700249.pdf" }
    holds := fun c _ => c.performance.item = .local .aspergillusIgG →
      ∃ a, c.aspergillus = some a ∧ a.elisa = true ∧ a.guidelineFollowed = true ∧
        (a.suspectedChronicProgressivePulmonaryDisease = true ∨
          a.suspectedAllergicBronchopulmonaryDisease = true) }

/-- (56)のうち第14項との併施に関する制約。第64項の適格性は別途扱う。 -/
def toxoplasmaChoice : Rule Context Unit :=
  condition "56" "378" "56" fun c =>
    c.performance.item ∈ [RelatedTest.local .toxoplasmaAntibody, .local .toxoplasmaAvidity] →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        let other := g.members.filter fun q =>
          if c.performance.item = .local .toxoplasmaAvidity then q.item == .local .toxoplasmaAntibody
          else q.item == .local .toxoplasmaAvidity
        (other ≠ [] → selectedFrom g
          (g.members.filter fun q =>
            q.item == .local .toxoplasmaAntibody || q.item == .local .toxoplasmaAvidity)
          c.performance 1)

def isHivScreening : RelatedTest → Bool
  | .local .hiv12Qual | .local .hiv12Semi | .local .hiv12ComboQual
  | .local .hiv1Antibody | .local .hiv12Quant | .local .hiv12ComboQuant => true
  | _ => false

private def HivFollowUp.Valid (f : HivFollowUp) (site : Site) : Prop :=
  f.series.patient = site.patient ∧
    ∃ period : Period, period.first = f.series.finalDay ∧ period.last = site.date ∧
      f.approximatelyTwoMonths = true ∧
      withinLimit f.history ⟨site.patient, none, period⟩
        (· == (f.series.provider, f.series.seriesId)) 0 = some true

def hivClinicalRule : Rule Context Unit :=
  condition "9" "371" "9" fun c =>
    isHivScreening c.performance.item = true →
      c.hivRoute.isSome = true ∧
      ∀ indication, c.hivRoute = some (.clinical indication) →
        c.hivHealthCenterOutsourcing = some false

private def historicalBranch (id label : String) (b : HistoricalBleeding) : Rule Context Unit :=
  condition id "371" label fun c =>
    ∀ year, isHivScreening c.performance.item = true →
      c.hivRoute = some (.clinical (.undocumentedFactor year b)) →
      1978 ≤ year ∧ year ≤ 1988

def hivNeonatalRule := historicalBranch "9/a" "9 ア" .neonatalOrSimilar
def hivLiverRule := historicalBranch "9/i" "9 イ" .severeLiverDisease
def hivDigestiveRule := historicalBranch "9/u" "9 ウ" .digestiveDisease
def hivSurgeryRule := historicalBranch "9/e" "9 エ" .surgeryOrDelivery

def hivFollowUpRule : Rule Context Unit :=
  condition "10/a" "371–372" "10 ア" fun c =>
    isHivScreening c.performance.item = true →
    ∀ f, c.hivRoute = some (.transfusion f) → f.series.provider = c.performance.site.institution →
      f.Valid c.performance.site

def hivOtherInstitutionRule : Rule Context Unit :=
  condition "10/i" "372" "10 イ" fun c =>
    isHivScreening c.performance.item = true →
    ∀ f, c.hivRoute = some (.transfusion f) → f.series.provider ≠ c.performance.site.institution →
      f.Valid c.performance.site

def hivTransfusionRule : Rule Context Unit :=
  condition "10" "371–372" "10" fun c =>
    hivFollowUpRule.holds c () ∧ hivOtherInstitutionRule.holds c ()

def hivFinalDayEntry : Rule Context (Option Date) :=
  ⟨"notice/D012/paragraph/10/u", notice "372" "10 ウ", fun c entry =>
    isHivScreening c.performance.item = true →
    ∀ f, c.hivRoute = some (.transfusion f) → entry = some f.series.finalDay⟩

def hivMethodRule : Rule Context Unit :=
  condition "11" "372" "11" fun c =>
    c.performance.item ∈ [RelatedTest.local .hiv12Qual, .local .hiv12Semi, .local .hiv12Quant] →
      c.hivMethod ∈ [some .la, some .eia, some .pa, some .immunochromatography]

/-- D018側との照合入力。陰性を受けた後続検査かどうかは実施記録で確認する。 -/
structure StrepCulture where
  rapid : Performance RelatedTest
  culture : Performance RelatedTest
  followedNegativeRapid : Option Bool

def strepCultureRule : Rule StrepCulture Bool :=
  ⟨"notice/D012/paragraph/12", notice "372" "12", fun c separate =>
    c.rapid.item = .local .rapidGroupAStrep → c.culture.item = .bacterialCultureD018 →
    c.rapid.site.patient = c.culture.site.patient →
    c.rapid.site.institution = c.culture.site.institution → separate = true →
      c.rapid.simultaneousWith c.culture = some false ∧ c.followedNegativeRapid = some false⟩

private def applies (items : List Item) (c : Context) : Prop :=
  ∃ i ∈ items, c.performance.item = .local i

private def methodIn (c : Context) (methods : List Method) : Prop :=
  ∃ m ∈ methods, c.method = some m

def fluTiming : Rule Context Unit :=
  condition "13/a" "372" "13 ア" fun c =>
    applies [.influenzaAntigen] c → ∃ hours, c.hoursSinceOnset = some hours ∧ 0 ≤ hours ∧ hours ≤ 48

def fluOptical : Rule Context Unit :=
  condition "13/u" "372" "13 ウ" fun c =>
    applies [.influenzaAntigen] c → methodIn c [.immunochromatography, .oia, .otherFluAntigen]

def fluParagraph : Rule Context Unit :=
  condition "13" "372" "13" fun c =>
    fluTiming.holds c () ∧ influenzaChoice.holds c () ∧ fluOptical.holds c ()

def candidaPurpose : Rule Context Unit :=
  condition "14" "372" "14" fun c =>
    applies [.candidaQual, .candidaSemi, .candidaQuant] c →
      c.confirmed .candidaBloodstreamDiagnosis = some true ∨
        c.confirmed .candidaPneumoniaDiagnosis = some true

/-- 入院のみの経路は外来の評価範囲から除く。 -/
def rsInpatientScope : Rule Context Unit :=
  condition "15/a" "372" "15 ア" fun c =>
    applies [.rsAntigen] c → c.rsRoute ≠ some .inpatient

def rsInfant : Rule Context Unit :=
  condition "15/i" "372" "15 イ" fun c =>
    applies [.rsAntigen] c → c.rsRoute = some .infant → c.ageYears = some 0

def rsProphylaxis : Rule Context Unit :=
  condition "15/u" "372" "15 ウ" fun c =>
    applies [.rsAntigen] c → c.rsRoute = some .prophylaxis →
      c.confirmed .palivizumabIndicated = some true ∨ c.confirmed .nirsevimabIndicated = some true

def rsParagraph : Rule Context Unit :=
  condition "15" "372" "15" fun c =>
    applies [.rsAntigen] c → c.confirmed .suspectedRs = some true ∧
      c.rsRoute.isSome = true ∧ rsInpatientScope.holds c () ∧ rsInfant.holds c () ∧ rsProphylaxis.holds c ()

def pyloriAntigenMethod : Rule Context Unit :=
  condition "16/a" "372" "16 ア" fun c =>
    applies [.pyloriAntigen] c → methodIn c [.eia, .immunochromatography]

def pyloriAntigenReference : Rule Context Unit :=
  condition "16/i" "372" "16 イ" fun c =>
    applies [.pyloriAntigen] c → c.pyloriNoticeSatisfied = some true

def pyloriAntigenParagraph : Rule Context Unit :=
  condition "16" "372" "16" fun c =>
    pyloriAntigenMethod.holds c () ∧ pyloriAntigenReference.holds c ()

def metapneumovirusIndication : Rule Context Unit :=
  condition "17/i" "373" "17 イ" fun c =>
    applies [.metapneumovirusAntigen] c →
      (∃ age, c.ageYears = some age ∧ age < 6) ∧
      c.confirmed .suspectedMetapneumovirus = some true ∧
      (c.confirmed .pneumoniaStronglySuspectedOnImaging = some true ∨
        c.confirmed .pneumoniaStronglySuspectedOnAuscultation = some true)

def metapneumovirusParagraph : Rule Context Unit :=
  condition "17" "372–373" "17" fun c =>
    metapneumovirusChoice.holds c () ∧ metapneumovirusIndication.holds c ()

private def norovirusBranch (id label : String) (route : NorovirusRoute)
    (holds : Context → Prop) : Rule Context Unit :=
  condition ("19/" ++ id) "373" ("19 " ++ label) fun c =>
    applies [.norovirusAntigen] c → c.norovirusRoute = some route → holds c

def norovirusYoung := norovirusBranch "a" "ア" .young fun c =>
  ∃ age, c.ageYears = some age ∧ age < 3

def norovirusOlder := norovirusBranch "i" "イ" .older fun c =>
  ∃ age, c.ageYears = some age ∧ 65 ≤ age

def norovirusMalignancy := norovirusBranch "u" "ウ" .malignancy fun c =>
  c.confirmed .confirmedMalignancy = some true

def norovirusTransplant := norovirusBranch "e" "エ" .transplant fun c =>
  c.confirmed .organTransplant = some true

def norovirusMedication := norovirusBranch "o" "オ" .medication fun c =>
  c.confirmed .receivingAntineoplasticOrImmunosuppressiveDrug = some true

def norovirusParagraph : Rule Context Unit :=
  condition "19" "373" "19" fun c =>
    applies [.norovirusAntigen] c → c.confirmed .suspectedNorovirus = some true ∧
      c.norovirusRoute.isSome = true ∧ norovirusYoung.holds c () ∧ norovirusOlder.holds c () ∧
      norovirusMalignancy.holds c () ∧ norovirusTransplant.holds c () ∧ norovirusMedication.holds c ()

def haemophilusIndication : Rule Context Unit :=
  condition "20" "373" "20" fun c =>
    applies [.nontypeableHaemophilus] c → methodIn c [.elisa] ∧
      c.confirmed .suspectedHaemophilus = some true ∧
      (c.confirmed .otitisMedia = some true ∨ c.confirmed .sinusitis = some true) ∧
      c.confirmed .nontypeableHaemophilusDiagnosis = some true

def mycobacteriumMethod : Rule Context Unit :=
  condition "22" "373" "22" fun c =>
    applies [.mycobacteriumQuant, .mycobacteriumQual] c → methodIn c [.goldColloid, .eia]

def trachomatisSpecimen : Rule Context Unit :=
  condition "24" "373" "24" fun c =>
    applies [.trachomatisAntigen] c →
      ∃ s ∈ [Specimen.urinary, .genital, .conjunctiva, .nasopharynx], c.specimen = some s

def trachomatisIncludedCollection : Rule Context Bool :=
  ⟨"notice/D012/paragraph/24", notice "373" "24", fun c separate =>
    applies [.trachomatisAntigen] c → separate = false⟩

def trachomatisPurpose : Rule Context Unit :=
  condition "25" "373" "25" fun c =>
    applies [.trachomatisAntigen] c →
      (c.specimen = some .conjunctiva ∨ c.specimen = some .nasopharynx) →
      c.confirmed .inclusionConjunctivitisOrTrachomaDiagnosis = some true ∨
        c.confirmed .infantTrachomatisPneumoniaDiagnosis = some true

private def pairedChoice (c : Context) (left right : List RelatedTest) : Prop :=
  c.performance.item ∈ left ++ right →
    ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
      let relevant := fun (q : Performance RelatedTest) => decide (q.item ∈ left ++ right)
      (g.members.any (fun q => decide (q.item ∈ left)) = true →
        g.members.any (fun q => decide (q.item ∈ right)) = true →
        selectedFrom g (g.members.filter relevant) c.performance 1)

def aspergillusAntigenRule : Rule Context Unit :=
  condition "26" "373" "26" fun c =>
    applies [.aspergillusAntigen] c → methodIn c [.la, .elisa] ∧
      c.confirmed .invasivePulmonaryAspergillosisDiagnosis = some true

def arabinitolRule : Rule Context Unit :=
  condition "27" "374" "27" fun c =>
    applies [.arabinitol] c →
      c.confirmed .candidaBloodstreamDiagnosis = some true ∨
        c.confirmed .candidaPneumoniaDiagnosis = some true

private def o157Tests : List RelatedTest :=
  [.local .ecoliO157Antibody, .local .ecoliO157Antigen, .gastrointestinalCultureD018]

def o157Rule : Rule Context Unit :=
  condition "28" "374" "28" fun c =>
    (applies [.ecoliO157Antibody] c → methodIn c [.la]) ∧
    (c.performance.item ∈ o157Tests → ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
      let relevant := g.members.filter fun q => decide (q.item ∈ o157Tests)
      ((relevant.map (·.item)).eraseDups.length ≥ 2 → selectedFrom g relevant c.performance 1))

def ecoliSerotypeRule : Rule Context Unit :=
  condition "30" "374" "30" fun c =>
    applies [.ecoliSerotype] c → c.confirmed .ecoliConfirmedByD018 = some true ∧
      (c.confirmed .verotoxinConfirmedByD023_2 = some true ∨
        c.confirmed .ecoliGrewOnSelectiveMedium = some true) ∧
      methodIn c [.serumAntibody] ∧
      (c.confirmed .ecoliOAntigenIdentified = some true ∨
        c.confirmed .ecoliHAntigenIdentified = some true)

def ecoliCultureIncluded : Rule Context Bool :=
  ⟨"notice/D012/paragraph/30", notice "374" "30", fun c separate =>
    applies [.ecoliSerotype] c → separate = false⟩

def pneumococcusWallRespiratory : Rule Context Unit :=
  condition "31/a/i" "374" "31 ア (イ)" fun c =>
    applies [.pneumococcusWall] c → c.wallRoute = some .respiratory →
      (c.specimen = some .sputum ∨ c.specimen = some .nasopharyngealSwab) ∧
        (c.confirmed .pneumoniaDiagnosis = some true ∨
          c.confirmed .lowerRespiratoryInfectionDiagnosis = some true)

def pneumococcusWallEnt : Rule Context Unit :=
  condition "31/a/ro" "374" "31 ア (ロ)" fun c =>
    applies [.pneumococcusWall] c → c.wallRoute = some .ent →
      c.confirmed .otitisMediaAndSinusitisDiagnosis = some true

def pneumococcusWallIndication : Rule Context Unit :=
  condition "31/a" "374" "31 ア" fun c =>
    applies [.pneumococcusWall] c → methodIn c [.immunochromatography] ∧
      c.wallRoute.isSome = true ∧ pneumococcusWallRespiratory.holds c () ∧
      pneumococcusWallEnt.holds c ()

def gonococcusCultureRule : Rule Context Unit :=
  condition "32" "374" "32" fun c =>
    applies [.gonococcusAntigen] c → ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
      ∀ q ∈ g.members, q.item ∈ [RelatedTest.bacterialCultureD018, .gastrointestinalCultureD018] →
        c.performance.simultaneousWith q = some false

def herpesTypedRule : Rule Context Unit :=
  condition "33" "374" "33" fun c =>
    applies [.herpesAntigen] c → c.confirmed .herpesTypeIdentified = some true

def pneumococcusWallChoice : Rule Context Unit :=
  condition "31/i" "374" "31 イ" fun c =>
    pairedChoice c [.local .pneumococcusWall] [.local .pneumococcusCapsule]

def pneumococcusWallParagraph : Rule Context Unit :=
  condition "31" "374" "31" fun c =>
    pneumococcusWallIndication.holds c () ∧ pneumococcusWallChoice.holds c ()

def PriorClaims.countFor (h : PriorClaims) (item : Item) (series : Option Nat) : Option Nat :=
  History.count h.history h.scope fun recorded =>
    recorded.1 == item && (series.isNone || recorded.2 == series)

private def priorCount (c : Context) (item : Item) (patientLifetime : Bool)
    (series : Option Nat) (n : Nat) : Prop :=
  ∃ h, c.priorClaims = some h ∧ h.scope.patient = c.performance.site.patient ∧
    h.scope.period.Contains c.performance.site.date ∧
    (∀ q ∈ h.history.entries, q.site.date.key ≤ c.performance.site.date.key ∧
      (q.site.institution = c.performance.site.institution →
        ∃ id, q.performance = some id ∧ id ≠ c.performance.id)) ∧
    (if patientLifetime then
      h.scope.institution = none ∧ h.scope.period.first = (Period.through c.performance.site.date).first
    else h.scope.institution = some c.performance.site.institution) ∧
    (series.isSome = true → ∀ q ∈ h.history.entries,
      h.scope.Includes q.site = true → q.item.1 = item → q.item.2.isSome = true) ∧
    h.countFor item series = some n

private def repeatSeries (c : Context) (item : Item) (n : Nat) : Prop :=
  ∃ series, c.performance.series = some series ∧ priorCount c item false (some series) n

private def herpesAlternatives : List RelatedTest :=
  [.local .herpesAntigen, .local .herpesCornea, .local .herpesGenital]

private def excludes (c : Context) (anchors blocked : List RelatedTest) : Prop :=
  c.performance.item ∈ anchors ++ blocked →
    ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
      (c.performance.item ∈ blocked → ∀ q ∈ g.members, q.item ∉ anchors)

def herpesSkinRule : Rule Context Unit :=
  condition "34" "374" "34" fun c =>
    (applies [.herpesSkin] c → methodIn c [.immunochromatography] ∧
      c.confirmed .suspectedHerpesSkinLesion = some true ∧
      c.confirmed .initialHerpesPresentation = some true ∧
      ∃ n, priorCount c .herpesSkin false none n ∧
        (0 < n → c.confirmed .herpesRepeatMedicallyNeeded = some true)) ∧
    (c.performance.item ∈ [.local .herpesSkin] ++ herpesAlternatives →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        let relevant := g.members.filter fun q =>
          decide (q.item ∈ [.local .herpesSkin] ++ herpesAlternatives)
        (relevant.any (fun q => q.item == .local .herpesSkin) = true →
          relevant.any (fun q => decide (q.item ∈ herpesAlternatives)) = true →
          ∃ ids, g.selected = some ids ∧ c.performance.id ∈ ids ∧
            ∀ a ∈ relevant, ∀ b ∈ relevant,
              a.item = .local .herpesSkin → b.item ∈ herpesAlternatives →
              a.id ∉ ids ∨ b.id ∉ ids))

def campylobacterRule : Rule Context Unit :=
  condition "35" "374" "35" fun c =>
    applies [.campylobacterAntigen] c → methodIn c [.immunochromatography] ∧
      c.confirmed .suspectedCampylobacter = some true

private def fungalAlternatives : List RelatedTest :=
  [.local .candidaQual, .local .candidaSemi, .local .candidaQuant, .local .aspergillusAntigen,
    .local .arabinitol, .local .cryptococcusQual, .local .cryptococcusSemi, .local .aspergillusIgG]

def glucanRule : Rule Context Unit :=
  condition "36" "374–375" "36" fun c =>
    (applies [.betaGlucan] c → methodIn c [.chromogenic, .turbidimetric, .elisa] ∧
      ((c.confirmed .suspectedDeepFungalInfection = some true ∧
        c.confirmed .selectFungalTreatment = some true) ∨
        c.confirmed .assessFungalTreatment = some true)) ∧
    (c.performance.item ∈ [.local .betaGlucan] ++ fungalAlternatives →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        ((g.members.any (fun q => q.item == .local .betaGlucan) = true →
          g.members.any (fun q => q.item == .local .aspergillusIgG) = true →
          g.coexistingAspergillosisSuspected.isSome = true)) ∧
        let alternatives := fungalAlternatives.filter fun i =>
          i != .local .aspergillusIgG || g.coexistingAspergillosisSuspected != some true
        (c.performance.item ∈ [.local .betaGlucan] ++ alternatives →
          pairedChoice c [.local .betaGlucan] alternatives))

def trachomatisClassIndication : Rule Context Unit :=
  condition "37/a" "375" "37 ア" fun c =>
    applies [.trachomatisClass] c →
      ((c.antibodyClass = some .igg ∨ c.antibodyClass = some .iga) ∧
        c.confirmed .trachomatisDiseaseDiagnosis = some true ∧
        (c.confirmed .trachomatisAntigenUndetectable = some true ∨
          c.confirmed .trachomatisCollectionDifficult = some true)) ∨
      (c.antibodyClass = some .igm ∧ c.confirmed .youngChildPneumoniaDiagnosis = some true)

def trachomatisClassChoice : Rule Context Unit :=
  condition "37/i" "375" "37 イ" fun c =>
    applies [.trachomatisClass] c →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        c.antibodyClass.isSome = true ∧ g.antibodyClass c.performance.id = c.antibodyClass ∧
        let sameItem := g.members.filter fun q => q.item == .local .trachomatisClass
        (∀ q ∈ sameItem, q.id ≠ c.performance.id →
          (c.performance.simultaneousWith q).isSome = true ∧
            (g.antibodyClass q.id).isSome = true) ∧
        let simultaneous := sameItem.filter fun q =>
          q.id == c.performance.id || c.performance.simultaneousWith q == some true
        (2 ≤ (simultaneous.filterMap fun q => g.antibodyClass q.id).eraseDups.length →
          selectedFrom g simultaneous c.performance 1)

def trachomatisClassParagraph : Rule Context Unit :=
  condition "37" "375" "37" fun c =>
    trachomatisClassIndication.holds c () ∧ trachomatisClassChoice.holds c ()

private def classTargetRule (suffix label : String) (target : Target) (allows : Context → Prop) :
    Rule Context Unit :=
  condition ("38/a/" ++ suffix) "375" ("38 ア " ++ label) fun c =>
    applies [.classSpecificTiter] c → c.target = some target → allows c

private def iggOrIgm (c : Context) : Prop :=
  c.antibodyClass = some .igg ∨ c.antibodyClass = some .igm

def classHerpes := classTargetRule "i" "(イ)" .herpes iggOrIgm
def classRubella := classTargetRule "ro" "(ロ)" .rubella iggOrIgm
def classCmv := classTargetRule "ha" "(ハ)" .cytomegalovirus iggOrIgm
def classEb := classTargetRule "ni" "(ニ)" .eb iggOrIgm
def classMeasles := classTargetRule "ho" "(ホ)" .measles iggOrIgm
def classMumps := classTargetRule "he" "(ヘ)" .mumps iggOrIgm
def classParvovirus := classTargetRule "to" "(ト)" .parvovirusB19 fun c =>
  c.antibodyClass = some .igm ∧ (∃ age, c.ageYears = some age ∧ 15 ≤ age) ∧
    c.confirmed .erythemaPresent = some true ∧
    c.confirmed .parvovirusStronglySuspected = some true
def classVaricella := classTargetRule "chi" "(チ)" .varicellaZoster iggOrIgm

def classSpecificIndication : Rule Context Unit :=
  condition "38/a" "375" "38 ア" fun c =>
    applies [.classSpecificTiter] c →
      (∃ t ∈ [Target.herpes, .rubella, .cytomegalovirus, .eb, .measles, .mumps,
        .parvovirusB19, .varicellaZoster], c.target = some t) ∧
      classHerpes.holds c () ∧ classRubella.holds c () ∧ classCmv.holds c () ∧
      classEb.holds c () ∧ classMeasles.holds c () ∧ classMumps.holds c () ∧
      classParvovirus.holds c () ∧ classVaricella.holds c ()

def classSpecificChoice : Rule Context Unit :=
  condition "38/i" "375" "38 イ" fun c =>
    applies [.classSpecificTiter] c → ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
      g.viralTarget c.performance.id = c.target ∧ g.antibodyClass c.performance.id = c.antibodyClass ∧
      (∀ q ∈ g.members, q.item = .local .classSpecificTiter →
        (g.viralTarget q.id).isSome = true ∧
          (g.antibodyClass q.id = some .igg ∨ g.antibodyClass q.id = some .igm)) ∧
      let sameVirus := g.members.filter fun q =>
        q.item == .local .classSpecificTiter && g.viralTarget q.id == c.target
      (sameVirus.any (fun q => g.antibodyClass q.id == some .igg) = true →
        sameVirus.any (fun q => g.antibodyClass q.id == some .igm) = true →
        selectedFrom g sameVirus c.performance 1)

def classSpecificParagraph : Rule Context Unit :=
  condition "38" "375" "38" fun c =>
    classSpecificIndication.holds c () ∧ classSpecificChoice.holds c () ∧
      viralClassChoice.holds c ()

def scrubTyphusStrainRule : Rule Context Unit :=
  condition "39" "375" "39" fun c =>
    applies [.scrubTyphusQual, .scrubTyphusSemi] c →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        g.scrubTyphusStrain c.performance.id = c.strain ∧
        let measurements := g.members.filter fun q =>
          q.item == .local .scrubTyphusQual || q.item == .local .scrubTyphusSemi
        (∀ q ∈ measurements, (g.scrubTyphusStrain q.id).isSome = true) ∧
        let sameStrain := measurements.filter fun q => g.scrubTyphusStrain q.id == c.strain
        (2 ≤ sameStrain.length → selectedFrom g sameStrain c.performance 1)

def legionellaRule : Rule Context Unit :=
  condition "40" "375" "40" fun c =>
    applies [.legionellaAntigen] c → methodIn c [.elisa, .immunochromatography] ∧
      c.confirmed .legionellaSuspectedFromFindings = some true ∧
      priorCount c .legionellaAntigen false none 0

def anisakisRule : Rule Context Unit :=
  condition "41" "375" "41" fun c =>
    applies [.anisakisAntibody] c →
      c.confirmed .intestinalAnisakiasisDiagnosis = some true ∨
      c.confirmed .granulomatousChronicGastricAnisakiasisDiagnosis = some true ∨
      c.confirmed .ectopicAnisakiasisDiagnosis = some true

def herpesCorneaRule : Rule Context Unit :=
  condition "42" "375" "42" fun c =>
    applies [.herpesCornea] c → methodIn c [.immunochromatography] ∧
      c.confirmed .suspectedCornealHerpesEpithelialLesion = some true

def pertussisIndication : Rule Context Unit :=
  condition "43/a" "375" "43 ア" fun c =>
    applies [.pertussisAntigen] c → methodIn c [.immunochromatography] ∧
      c.confirmed .pertussisGuidelineClinicalCase = some true

def pertussisChoice : Rule Context Unit :=
  condition "43/i" "375–376" "43 イ" fun c =>
    pairedChoice c [.local .pertussisAntigen] [.pertussisD023_13, .multiplexD023_25]

def pertussisParagraph : Rule Context Unit :=
  condition "43" "375–376" "43" fun c =>
    pertussisIndication.holds c () ∧ pertussisChoice.holds c ()

def pneumococcusCapsuleRule : Rule Context Unit :=
  condition "44" "376" "44" fun c =>
    applies [.pneumococcusCapsule] c → methodIn c [.immunochromatography]

private def diagnosticRepeat (c : Context) (item : Item) : Prop :=
  priorCount c item false none 0 ∨
    (priorCount c item false none 1 ∧
      c.confirmed .priorSameTestNegative = some true ∧
      c.confirmed .noAlternativeDiagnosis = some true)

inductive EntryReason where
  | diagnosticRepeat | herpesRepeat | kohNegative | kohUnavailable | severeImmunodeficiency
  | toxoplasmaException | birdIgG | aavRepeat
  deriving DecidableEq

abbrev Entries := EntryReason → Prop

private def entryRule (id pages label : String) (reason : EntryReason)
    (required : Context → Prop) : Rule Context Entries :=
  ⟨"notice/D012/paragraph/" ++ id, notice pages label, fun c entries =>
    required c → entries reason⟩

private def diagnosticRepeatEntry (id pages label : String) (item : Item) : Rule Context Entries :=
  entryRule id pages label .diagnosticRepeat fun c =>
    applies [item] c ∧ priorCount c item false none 1

def covidQualIndication : Rule Context Unit :=
  condition "21/a" "373" "21 ア" fun c =>
    applies [.covidQual] c → c.confirmed .covidSuspected = some true ∧
      c.confirmed .covidDiagnosis = some true ∧ diagnosticRepeat c .covidQual
def covidQualEntry := diagnosticRepeatEntry "21/a" "373" "21 ア" .covidQual

def covidQualExcludes : Rule Context Unit :=
  condition "21/i" "373" "21 イ" fun c =>
    excludes c [.local .covidQual]
      [.local .covidFlu, .local .covidRs, .local .covidFluRs, .local .covidQuant]

def covidQualParagraph : Rule Context Unit :=
  condition "21" "373" "21" fun c =>
    covidQualIndication.holds c () ∧ covidQualExcludes.holds c ()

def amoebaAntigenRule : Rule Context Unit :=
  condition "45" "376" "45" fun c =>
    applies [.amoebaAntigen] c → c.specimen = some .stool ∧ methodIn c [.eia] ∧
      c.confirmed .intestinalAmoebiasisSymptoms = some true ∧
      c.confirmed .amoebicDysenteryDiagnosis = some true

def amoebaAntibodyRule : Rule Context Unit :=
  condition "46" "376" "46" fun c =>
    applies [.amoebaAntibodyQual] c → c.specimen = some .serum ∧ methodIn c [.elisa] ∧
      c.confirmed .amoebaGuidelineFollowed = some true ∧
      (c.confirmed .amoebicLiverAbscessSuspected = some true ∨
        (c.confirmed .amoebicColitisSuspected = some true ∧
          c.confirmed .amoebaStoolNegative = some true)) ∧
      repeatSeries c .amoebaAntibodyQual 0

def covidFluIndication : Rule Context Unit :=
  condition "47/a" "376" "47 ア" fun c =>
    applies [.covidFlu] c → c.confirmed .covidSuspected = some true ∧
      c.confirmed .influenzaSuspected = some true ∧ c.confirmed .covidDiagnosis = some true ∧
      c.confirmed .influenzaDiagnosis = some true ∧ diagnosticRepeat c .covidFlu
def covidFluEntry := diagnosticRepeatEntry "47/a" "376" "47 ア" .covidFlu

def covidFluExcludes : Rule Context Unit :=
  condition "47/i" "376" "47 イ" fun c =>
    excludes c [.local .covidFlu] [.local .influenzaAntigen, .local .covidQual,
      .local .covidRs, .local .covidFluRs, .local .covidQuant]

def covidFluParagraph : Rule Context Unit :=
  condition "47" "376" "47" fun c =>
    covidFluIndication.holds c () ∧ covidFluExcludes.holds c ()

private def dengueTests : List Item := [.dengueAntigen, .dengueCombo]

def dengueFacility : Rule Context Unit :=
  ⟨"primary/D012/item/56/note", primary 185 "56 注", fun c _ =>
    applies dengueTests c → c.facilityStandardMet = some true⟩

def dengueComboRule : Rule Context Unit :=
  condition "48/a" "376" "48 ア" fun c =>
    applies [.dengueCombo] c → methodIn c [.immunochromatography] ∧
      ∃ ns1 igg igm : Performance RelatedTest,
        ns1 ∈ c.measurements ∧ igg ∈ c.measurements ∧ igm ∈ c.measurements ∧
        ns1.item = .dengueNs1 ∧ igg.item = .dengueIgG ∧ igm.item = .dengueIgM ∧
        c.performance.simultaneousWith ns1 = some true ∧
        c.performance.simultaneousWith igg = some true ∧
        c.performance.simultaneousWith igm = some true

def dengueIndication : Rule Context Unit :=
  condition "48/i" "376" "48 イ" fun c =>
    applies dengueTests c → c.confirmed .dengueSuspectedUnderGuideline = some true ∧
      c.confirmed .requiresHospitalization = some true

def dengueSurvey : Rule Context Unit :=
  condition "48/u" "376" "48 ウ" fun c =>
    applies dengueTests c → c.confirmed .epidemiologicalSurvey = some false

def dengueChoice : Rule Context Unit :=
  condition "48/e" "376" "48 エ" fun c =>
    pairedChoice c [.local .dengueAntigen] [.local .dengueCombo]

def dengueParagraph : Rule Context Unit :=
  condition "48" "376" "48" fun c =>
    dengueComboRule.holds c () ∧ dengueIndication.holds c () ∧
      dengueSurvey.holds c () ∧ dengueChoice.holds c ()

def dermatophyteMethod : Rule Context Unit :=
  condition "49/a" "376" "49 ア" fun c =>
    applies [.dermatophyteAntigen] c → methodIn c [.immunochromatography] ∧
      c.specimen = some .nail ∧ c.confirmed .onychomycosisSuspected = some true

def dermatophyteNegative : Rule Context Unit :=
  condition "49/i/i" "376" "49 イ (イ)" fun c =>
    applies [.dermatophyteAntigen] c → c.kohRoute = some .negative →
      c.confirmed .onychomycosisSuspectedFromFindings = some true

def dermatophyteUnavailable : Rule Context Unit :=
  condition "49/i/ro" "377" "49 イ (ロ)" fun c =>
    applies [.dermatophyteAntigen] c → c.kohRoute = some .unavailable →
      c.confirmed .kohCannotBePerformed = some true

def dermatophyteNegativeEntry : Rule Context Entries :=
  entryRule "49/i/i" "376" "49 イ (イ)" .kohNegative fun c =>
    applies [.dermatophyteAntigen] c ∧ c.kohRoute = some .negative

def dermatophyteUnavailableEntry : Rule Context Entries :=
  entryRule "49/i/ro" "377" "49 イ (ロ)" .kohUnavailable fun c =>
    applies [.dermatophyteAntigen] c ∧ c.kohRoute = some .unavailable

def dermatophyteKoh : Rule Context Unit :=
  condition "49/i" "376–377" "49 イ" fun c =>
    applies [.dermatophyteAntigen] c → c.kohRoute.isSome = true ∧
      dermatophyteNegative.holds c () ∧ dermatophyteUnavailable.holds c ()

def dermatophyteGuideline : Rule Context Unit :=
  condition "49/u" "377" "49 ウ" fun c =>
    applies [.dermatophyteAntigen] c → c.confirmed .dermatophyteGuidelineFollowed = some true

def dermatophyteParagraph : Rule Context Unit :=
  condition "49" "376–377" "49" fun c =>
    dermatophyteMethod.holds c () ∧ dermatophyteKoh.holds c () ∧ dermatophyteGuideline.holds c ()

private def confirmedAfterScreen (c : Context) (accepts : RelatedTest → Bool) : Prop :=
  ∃ q, c.positiveScreen = some q ∧ q.site.patient = c.performance.site.patient ∧
    q.site.date.key ≤ c.performance.site.date.key ∧
    (q.site.institution = c.performance.site.institution → q.id ≠ c.performance.id) ∧
    accepts q.item = true ∧ c.confirmed .confirmatoryDiagnosis = some true

def hivWesternBlot : Rule Context Unit :=
  condition "50" "377" "50" fun c =>
    applies [.hiv1WesternBlot, .hiv2WesternBlot] c →
      confirmedAfterScreen c isHivScreening ∧ methodIn c [.westernBlot]

def cmvPp65Rule : Rule Context Unit :=
  condition "51" "377" "51" fun c =>
    applies [.cmvPp65] c → methodIn c [.immunostaining] ∧
      (c.confirmed .organTransplant = some true ∨
        c.confirmed .stemCellTransplant = some true ∨
        c.confirmed .hivInfection = some true ∨
        c.confirmed .severeCellularImmunodeficiency = some true)

def cmvPp65Entry : Rule Context Entries :=
  entryRule "51" "377" "51" .severeImmunodeficiency fun c =>
    applies [.cmvPp65] c ∧ c.confirmed .severeCellularImmunodeficiency = some true

def herpesSkinEntry : Rule Context Entries :=
  entryRule "34" "374" "34" .herpesRepeat fun c =>
    applies [.herpesSkin] c ∧ ∃ n, priorCount c .herpesSkin false none n ∧ 0 < n

def amoebaGuidelineIdentity : Rule Context Unit :=
  ⟨"clarification/r08-20260401-02-medical/question/108",
    ⟨.clarification, "疑義解釈資料の送付について（その2）", "2026-04-01",
      "物理PDF33頁 医科問108", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001689076.pdf"⟩,
    fun c _ => applies [.amoebaAntibodyQual] c →
      c.confirmed .confirmsAmoebaGuidelineIdentity = some true⟩

def covidRsIndication : Rule Context Unit :=
  condition "53/a" "377" "53 ア" fun c =>
    applies [.covidRs] c → c.confirmed .covidSuspected = some true ∧
      c.confirmed .suspectedRs = some true ∧ c.confirmed .covidDiagnosis = some true ∧
      c.confirmed .rsDiagnosis = some true ∧ diagnosticRepeat c .covidRs
def covidRsEntry := diagnosticRepeatEntry "53/a" "377" "53 ア" .covidRs

def covidRsExcludes : Rule Context Unit :=
  condition "53/i" "377" "53 イ" fun c =>
    excludes c [.local .covidRs] [.local .rsAntigen, .local .covidQual, .local .covidFlu,
      .local .covidFluRs, .local .covidQuant]

def covidRsParagraph : Rule Context Unit :=
  condition "53" "377" "53" fun c =>
    covidRsIndication.holds c () ∧ covidRsExcludes.holds c ()

def covidFluRsIndication : Rule Context Unit :=
  condition "54/a" "377" "54 ア" fun c =>
    applies [.covidFluRs] c → c.confirmed .covidSuspected = some true ∧
      c.confirmed .influenzaSuspected = some true ∧ c.confirmed .suspectedRs = some true ∧
      c.confirmed .covidDiagnosis = some true ∧ c.confirmed .influenzaDiagnosis = some true ∧
      c.confirmed .rsDiagnosis = some true ∧ diagnosticRepeat c .covidFluRs
def covidFluRsEntry := diagnosticRepeatEntry "54/a" "377" "54 ア" .covidFluRs

def covidFluRsExcludes : Rule Context Unit :=
  condition "54/i" "377" "54 イ" fun c =>
    excludes c [.local .covidFluRs] [.local .influenzaAntigen, .local .rsAntigen,
      .local .covidQual, .local .covidFlu, .local .covidRs, .local .covidQuant]

def covidFluRsParagraph : Rule Context Unit :=
  condition "54" "377" "54" fun c =>
    covidFluRsIndication.holds c () ∧ covidFluRsExcludes.holds c ()

def htlvConfirmation : Rule Context Unit :=
  condition "55" "378" "55" fun c =>
    applies [.htlvBlot] c → methodIn c [.westernBlot, .lineBlot] ∧
      confirmedAfterScreen c (fun item =>
        decide (item ∈ [RelatedTest.local .htlvQual, .local .htlvSemi, .local .htlvAntibody]))

private def toxoplasmaException (c : Context) : Prop :=
  repeatSeries c .toxoplasmaAvidity 1 ∨ ∃ weeks, c.gestationWeeks = some weeks ∧ 16 ≤ weeks

def toxoplasmaAvidityRule : Rule Context Unit :=
  condition "56" "378" "56" fun c =>
    toxoplasmaChoice.holds c () ∧
    (applies [.toxoplasmaAvidity] c → methodIn c [.clia] ∧
      (c.specimen = some .serum ∨ c.specimen = some .plasma) ∧
      c.confirmed .toxoplasmaManualFollowed = some true ∧
      c.confirmed .toxoplasmaIgMPositive = some true ∧
      c.confirmed .takingSpiramycin = some true ∧
      (repeatSeries c .toxoplasmaAvidity 0 ∨ repeatSeries c .toxoplasmaAvidity 1) ∧
      (∃ weeks, c.gestationWeeks = some weeks) ∧
      (toxoplasmaException c → c.confirmed .toxoplasmaExceptionMedicallyNeeded = some true))

def toxoplasmaEntry : Rule Context Entries :=
  entryRule "56" "378" "56" .toxoplasmaException fun c =>
    applies [.toxoplasmaAvidity] c ∧ toxoplasmaException c

def covidQuantIndication : Rule Context Unit :=
  condition "57/a" "378" "57 ア" fun c =>
    applies [.covidQuant] c → c.confirmed .covidSuspected = some true ∧
      c.confirmed .covidDiagnosis = some true ∧ methodIn c [.cleia, .eclia, .clia, .opticalWaveguide] ∧
      diagnosticRepeat c .covidQuant
def covidQuantEntry := diagnosticRepeatEntry "57/a" "378" "57 ア" .covidQuant

def covidQuantExcludes : Rule Context Unit :=
  condition "57/i" "378" "57 イ" fun c =>
    excludes c [.local .covidQuant] [.local .covidQual, .local .covidFlu,
      .local .covidRs, .local .covidFluRs]

def covidQuantParagraph : Rule Context Unit :=
  condition "57" "378" "57" fun c =>
    covidQuantIndication.holds c () ∧ covidQuantExcludes.holds c ()

def hivAntigenRule : Rule Context Unit :=
  condition "58" "378" "58" fun c =>
    applies [.hivAntigen] c →
      (c.confirmed .hivInfection = some true ∧ c.confirmed .hivFollowUpPurpose = some true) ∨
      (c.confirmed .hivHighRisk = some true ∧ c.confirmed .acuteInfectionSymptoms = some true ∧
        c.confirmed .confirmatoryDiagnosis = some true)

def hivSpecificRule : Rule Context Unit :=
  condition "59" "378" "59" fun c =>
    (applies [.hivSpecific] c → confirmedAfterScreen c isHivScreening ∧
      methodIn c [.immunochromatography] ∧
      (∃ s ∈ [Specimen.wholeBlood, .serum, .plasma], c.specimen = some s)) ∧
    excludes c [.local .hivSpecific] [.local .hiv1WesternBlot, .local .hiv2WesternBlot]

def trichosporonRule : Rule Context Unit :=
  condition "60" "378" "60" fun c =>
    applies [.trichosporonAntibody] c → methodIn c [.elisa] ∧
      c.confirmed .summerPneumonitisDifferentialDiagnosis = some true ∧
      c.confirmed .summerPneumonitisSuspectedUnderCriteria = some true

def birdIgGRule : Rule Context Unit :=
  condition "61" "378" "61" fun c =>
    applies [.birdIgG] c → methodIn c [.eia] ∧
      c.confirmed .birdPneumonitisStronglySuspected = some true

def birdIgGEntry : Rule Context Entries :=
  entryRule "61" "378" "61" .birdIgG (applies [.birdIgG])

private def aavTests : List Item := [.aav9, .aavRh74]

def aavFacility : Rule Context Unit :=
  ⟨"primary/D012/item/70/note", primary 186 "70 注", fun c _ =>
    applies aavTests c →
      c.facilityStandardMet = some true ∧ c.facilityNotified = some true⟩

private def aavFrequency (c : Context) (item : Item) : Prop :=
  ∃ n, priorCount c item true none n ∧
    (0 < n → c.confirmed .aavRepeatMedicallyNeeded = some true)

def aav9Rule : Rule Context Unit :=
  condition "62" "378–379" "62" fun c =>
    applies [.aav9] c →
      (∃ age, c.ageYears = some age ∧ age < 2) ∧
      c.confirmed .spinalMuscularAtrophy = some true ∧
      c.confirmed .onasemnogeneIndicationSupport = some true ∧ aavFrequency c .aav9

def aavRh74Rule : Rule Context Unit :=
  condition "63" "379" "63" fun c =>
    applies [.aavRh74] c → c.confirmed .duchenneMuscularDystrophy = some true ∧
      c.confirmed .delandistrogeneIndicationSupport = some true ∧ methodIn c [.eclia] ∧
      aavFrequency c .aavRh74

def aav9Entry : Rule Context Entries :=
  entryRule "62" "378–379" "62" .aavRepeat fun c =>
    applies [.aav9] c ∧ ∃ n, priorCount c .aav9 true none n ∧ 0 < n

def aavRh74Entry : Rule Context Entries :=
  entryRule "63" "379" "63" .aavRepeat fun c =>
    applies [.aavRh74] c ∧ ∃ n, priorCount c .aavRh74 true none n ∧ 0 < n

def documentationRules : List (Rule Context Entries) :=
  [covidQualEntry, herpesSkinEntry, covidFluEntry, dermatophyteNegativeEntry,
    dermatophyteUnavailableEntry, cmvPp65Entry, covidRsEntry, covidFluRsEntry,
    toxoplasmaEntry, covidQuantEntry, birdIgGEntry, aav9Entry, aavRh74Entry]

attribute [local simp] covidRsParagraph covidRsIndication covidRsExcludes covidFluRsParagraph
  covidFluRsIndication covidFluRsExcludes htlvConfirmation toxoplasmaAvidityRule covidQuantParagraph
  covidQuantIndication covidQuantExcludes hivAntigenRule hivSpecificRule trichosporonRule
  birdIgGRule aavTests aavFacility aav9Rule aavRh74Rule

attribute [local simp] excludes covidQualParagraph covidQualIndication covidQualExcludes
  amoebaAntigenRule amoebaAntibodyRule amoebaGuidelineIdentity covidFluParagraph covidFluIndication covidFluExcludes
  dengueTests dengueFacility dengueParagraph dengueComboRule dengueIndication dengueSurvey
  dengueChoice dermatophyteParagraph dermatophyteMethod dermatophyteKoh dermatophyteGuideline
  hivWesternBlot cmvPp65Rule

attribute [local simp] trachomatisClassParagraph trachomatisClassIndication trachomatisClassChoice
  classSpecificParagraph classSpecificIndication classSpecificChoice scrubTyphusStrainRule
  legionellaRule anisakisRule herpesCorneaRule pertussisParagraph pertussisIndication
  pertussisChoice pneumococcusCapsuleRule

attribute [local simp] pairedChoice aspergillusAntigenRule arabinitolRule o157Rule o157Tests
  ecoliSerotypeRule pneumococcusWallParagraph pneumococcusWallIndication pneumococcusWallChoice
  gonococcusCultureRule herpesTypedRule herpesSkinRule herpesAlternatives campylobacterRule
  glucanRule fungalAlternatives

attribute [local simp] applies fluParagraph fluTiming fluOptical candidaPurpose rsParagraph
  pyloriAntigenParagraph pyloriAntigenMethod pyloriAntigenReference metapneumovirusParagraph
  metapneumovirusIndication norovirusParagraph haemophilusIndication mycobacteriumMethod
  trachomatisSpecimen trachomatisPurpose

def eligibilityRules :=
  [stsRule, mycoplasmaAntibodyRule, ureaseRule, stoolAntigenRule, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule, htlvRule,
    mycoplasmaChromatographyRule, pneumoniaeChoice,
    hivClinicalRule, hivNeonatalRule, hivLiverRule, hivDigestiveRule, hivSurgeryRule,
    hivTransfusionRule, hivFollowUpRule, hivOtherInstitutionRule, hivMethodRule,
    mycoplasmaFluorescenceRule, aspergillusRule,
    fluParagraph, candidaPurpose, rsParagraph, pyloriAntigenParagraph, metapneumovirusParagraph,
    norovirusParagraph, haemophilusIndication, mycobacteriumMethod, trachomatisSpecimen,
    trachomatisPurpose, aspergillusAntigenRule, arabinitolRule, o157Rule, ecoliSerotypeRule,
    pneumococcusWallParagraph, gonococcusCultureRule, herpesTypedRule, herpesSkinRule,
    campylobacterRule, glucanRule, trachomatisClassParagraph, classSpecificParagraph,
    scrubTyphusStrainRule, legionellaRule, anisakisRule, herpesCorneaRule, pertussisParagraph,
    pneumococcusCapsuleRule, covidQualParagraph, amoebaAntigenRule, amoebaAntibodyRule,
    amoebaGuidelineIdentity,
    covidFluParagraph, dengueFacility, dengueParagraph, dermatophyteParagraph,
    hivWesternBlot, cmvPp65Rule, covidRsParagraph, covidFluRsParagraph, htlvConfirmation,
    toxoplasmaAvidityRule, covidQuantParagraph, hivAntigenRule, hivSpecificRule, trichosporonRule,
    birdIgGRule, aavFacility, aav9Rule, aavRh74Rule]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def PermitsRate (i : Item) (c : Context) (p : Nat) : Prop :=
  c.performance.item = .local i ∧ Eligible c ∧ Satisfies rules i p

def legacyRequest (i : Item) (a : Option SpecimenTests.AspergillusAssessment)
    (facilityStandardMet : Bool := false) (facilityNotified : Bool := false) :
    SpecimenTests.Request :=
  { code := .d012, number := i.number, variant := i.variant, conditions := { aspergillus := a, facilityStandardMet, facilityNotified } }

theorem legacy_rate (i : Item) (a : Option SpecimenTests.AspergillusAssessment)
    (h : i = .aspergillusIgG → a.any (fun x => x.elisa && x.guidelineFollowed &&
      (x.suspectedChronicProgressivePulmonaryDisease ||
        x.suspectedAllergicBronchopulmonaryDisease)) = true)
    (facilityStandardMet facilityNotified : Bool)
    (hd : i ∈ dengueTests → facilityStandardMet = true)
    (hn : i ∈ aavTests → facilityNotified = true) :
    SpecimenTests.assessOne (legacyRequest i a facilityStandardMet facilityNotified) =
      some (.charged i.points 0) := by
  cases i <;> try rfl
  case dengueAntigen => rw [hd (by decide)]; rfl
  case dengueCombo => rw [hd (by decide)]; rfl
  case aav9 => rw [hn (by decide)]; rfl
  case aavRh74 => rw [hn (by decide)]; rfl
  change (if !(a.any fun x => x.elisa && x.guidelineFollowed &&
      (x.suspectedChronicProgressivePulmonaryDisease ||
        x.suspectedAllergicBronchopulmonaryDisease)) then none else some (SpecimenTests.ItemResult.charged 390 0)) =
    some (SpecimenTests.ItemResult.charged 390 0)
  simp [h rfl]

theorem legacy_iff (c : Context) (i : Item) (p : Nat)
    (hi : c.performance.item = .local i) (he : Eligible c) :
    Satisfies rules i p ↔
      SpecimenTests.assessOne (legacyRequest i c.aspergillus
        (c.facilityStandardMet == some true) (c.facilityNotified == some true)) =
        some (.charged p 0) := by
  have h := he aspergillusRule (by simp [eligibilityRules])
  rw [rate_iff, legacy_rate]
  · simp [eq_comm]
  · intro h62
    subst i
    obtain ⟨a, ha, helisa, hguide, hsuspect⟩ := h hi
    rcases hsuspect with hc | ha'
    · simp [ha, helisa, hguide, hc]
    · simp [ha, helisa, hguide, ha']
  · intro hd
    have meet := he dengueFacility (by simp [eligibilityRules]) ⟨i, hd, hi⟩
    simp [meet]
  · intro hn
    have notified := (he aavFacility (by simp [eligibilityRules]) ⟨i, hn, hi⟩).2
    simp [notified]

theorem determines (c : Context) (i : Item)
    (hi : c.performance.item = .local i) (he : Eligible c) :
    (∃ p, PermitsRate i c p) ∧
      ∀ a b, PermitsRate i c a → PermitsRate i c b → a = b := by
  exact ⟨⟨i.points, hi, he, (rate_iff ..).mpr rfl⟩,
    fun a b ha hb => ((rate_iff i a).mp ha.2.2).trans ((rate_iff i b).mp hb.2.2).symm⟩

/-- 検体単位の照合済み抗体価測定。異なる方法による同じ対象も保持する。 -/
structure ViralGroup where
  anchor : Performance RelatedTest
  measurements : List (Context × Target)

def ViralGroup.Assessed (g : ViralGroup) : Prop :=
  g.measurements ≠ [] ∧ (g.measurements.map (·.1.performance.id)).Nodup ∧
    ∀ (pair : Context × Target), pair ∈ g.measurements →
      pair.1.performance.item = .local .viralTiter ∧ pair.1.target = some pair.2 ∧
      g.anchor.sameSpecimen pair.1.performance = some true ∧ Eligible pair.1

def ViralGroup.targetCount (g : ViralGroup) : Nat :=
  (g.measurements.map Prod.snd).eraseDups.length

def viralMethods : Rule ViralGroup Nat :=
  ⟨"notice/D012/paragraph/6/i", notice "371" "6 イ", fun g p =>
    g.targetCount ≤ 8 → p = 79 * g.targetCount⟩

def viralCapPoints : Nat := 79 * 8

def viralCap : Rule ViralGroup Nat :=
  ⟨"primary/D012/item/11/note", primary 184 "11 注", fun g p =>
    8 ≤ g.targetCount → p = viralCapPoints⟩

def viralRules := [viralMethods, viralCap]

theorem viral_legacy_iff (g : ViralGroup) (p : Nat) :
    Satisfies viralRules g p ↔
      p = SpecimenTests.groupedBase .viralAntibodies g.targetCount 79 := by
  by_cases hn : g.targetCount ≤ 8
  · simp only [viralRules, satisfies_cons, satisfies_nil, viralMethods, viralCap, viralCapPoints,
      and_true, SpecimenTests.groupedBase, Nat.min_eq_right hn]
    constructor
    · exact fun h => h.1 hn
    · intro h
      exact ⟨fun _ => h, fun h8 => by have eq := Nat.le_antisymm hn h8; simpa [eq] using h⟩
  · have h8 : 8 ≤ g.targetCount := by omega
    simp [viralRules, satisfies_cons, satisfies_nil, viralMethods, viralCap, viralCapPoints, hn, h8,
      SpecimenTests.groupedBase, Nat.min_eq_left h8]

theorem viral_determines : DeterminesOn ViralGroup.Assessed viralRules := by
  intro g _
  exact ⟨⟨_, (viral_legacy_iff ..).mpr rfl⟩,
    fun a b ha hb => ((viral_legacy_iff g a).mp ha).trans ((viral_legacy_iff g b).mp hb).symm⟩

/-- 選択済みの第46項の検査を、確認済み同一検体ごとに評価する。 -/
structure ClassGroup where
  anchor : Performance RelatedTest
  measurements : List (Context × Target)

def ClassGroup.Assessed (g : ClassGroup) : Prop :=
  g.measurements ≠ [] ∧ (g.measurements.map (·.1.performance.id)).Nodup ∧
    (g.measurements.map Prod.snd).Nodup ∧
    ∀ (pair : Context × Target), pair ∈ g.measurements →
      pair.1.performance.item = .local .classSpecificTiter ∧ pair.1.target = some pair.2 ∧
      g.anchor.sameSpecimen pair.1.performance = some true ∧ Eligible pair.1

def ClassGroup.targetCount (g : ClassGroup) : Nat := g.measurements.length

def classGroupBase : Rule ClassGroup Nat :=
  ⟨"primary/D012/item/46", primary 185 "46", fun g p =>
    g.targetCount ≤ 2 → p = Item.classSpecificTiter.points * g.targetCount⟩

def classCapPoints : Nat := 200 * 2

def classGroupCap : Rule ClassGroup Nat :=
  ⟨"primary/D012/item/46/note", primary 185 "46 注", fun g p =>
    2 ≤ g.targetCount → p = classCapPoints⟩

def classGroupRules := [classGroupBase, classGroupCap]

theorem class_group_legacy_iff (g : ClassGroup) (p : Nat) :
    Satisfies classGroupRules g p ↔
      p = SpecimenTests.groupedBase .classSpecificViralAntibodies g.targetCount 200 := by
  by_cases hn : g.targetCount ≤ 2
  · simp only [classGroupRules, satisfies_cons, satisfies_nil, classGroupBase, classGroupCap,
      classCapPoints, Item.points, and_true, SpecimenTests.groupedBase, Nat.min_eq_right hn]
    constructor
    · exact fun h => h.1 hn
    · intro h
      exact ⟨fun _ => h, fun h2 => by rw [Nat.le_antisymm hn h2] at h; exact h⟩
  · have h2 : 2 ≤ g.targetCount := by omega
    simp [classGroupRules, satisfies_cons, satisfies_nil, classGroupBase, classGroupCap,
      classCapPoints, Item.points, hn, h2, SpecimenTests.groupedBase, Nat.min_eq_left h2]

theorem class_group_determines : DeterminesOn ClassGroup.Assessed classGroupRules := by
  intro g _
  exact ⟨⟨_, (class_group_legacy_iff ..).mpr rfl⟩,
    fun a b ha hb => ((class_group_legacy_iff g a).mp ha).trans
      ((class_group_legacy_iff g b).mp hb).symm⟩

theorem determines_rate : DeterminesOn (fun _ : Item => True) rules := by
  intro i _
  exact ⟨⟨i.points, (rate_iff ..).mpr rfl⟩,
    fun a b ha hb => ((rate_iff i a).mp ha).trans ((rate_iff i b).mp hb).symm⟩

/-- 検体検査の実施料に含まれる採取の投影。別算定できるかは採取側で判定する。 -/
def trachomatisCollection (c : Context) (a : SpecimenCollection.Assessment) (kind : Nat)
    (separate : Bool) (_ : trachomatisIncludedCollection.holds c separate) :
    Option Examinations.TestCharge :=
  if separate then a.toCollection kind else none

theorem trachomatis_collection_included (c : Context) (a : SpecimenCollection.Assessment)
    (kind : Nat) (separate : Bool) (h : trachomatisIncludedCollection.holds c separate)
    (item : c.performance.item = .local .trachomatisAntigen) :
    trachomatisCollection c a kind separate h = none := by
  have eq := h ⟨.trachomatisAntigen, by simp, item⟩
  subst separate
  rfl

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 12, number := i.number, variant := i.variant, ordinaryCategory := .immunological }

private def executionItem (kind points : Nat) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := points }

def individualExecution (kind : Nat) (i : Item) (c : Context) (p : Nat)
    (_ : i ≠ .viralTiter) (_ : i ≠ .classSpecificTiter) (_ : PermitsRate i c p) : Examinations.SpecimenItem :=
  executionItem kind p

def viralExecution (kind : Nat) (g : ViralGroup) (p : Nat)
    (_ : g.Assessed) (_ : Satisfies viralRules g p) : Examinations.SpecimenItem :=
  executionItem kind p

def classExecution (kind : Nat) (g : ClassGroup) (p : Nat)
    (_ : g.Assessed) (_ : Satisfies classGroupRules g p) : Examinations.SpecimenItem :=
  executionItem kind p

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .immunological := rfl

private def sample (item : Item) : Context :=
  { performance := ⟨1, ⟨2, 3, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .local item,
    none, some 1, none, none⟩ }

private def aspergillusSample : Context :=
  { sample .aspergillusIgG with
    combined := some { members := [(sample .aspergillusIgG).performance] }
    aspergillus := some ⟨true, false, true, true⟩ }

example : PermitsRate .aspergillusIgG aspergillusSample 390 := by
  refine ⟨rfl, ?_, (rate_iff ..).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, condition, stsRule,
    mycoplasmaAntibodyRule, mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule,
    mycoplasmaSelection, isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule, htlvRule, influenzaChoice,
    pneumoniaeChoice, metapneumovirusChoice, viralClassChoice, aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule, hivDigestiveRule,
    hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule, hivOtherInstitutionRule,
    hivMethodRule, isHivScreening, aspergillusSample, sample, Combined.Valid]

example : ¬ Eligible (sample .aspergillusIgG) := by
  intro h
  obtain ⟨a, ha, _⟩ := h aspergillusRule (by simp [eligibilityRules]) rfl
  cases ha

private def hivSample : Context :=
  { sample .hiv12Qual with
    hivRoute := some (.clinical (.undocumentedFactor 1978 .neonatalOrSimilar))
    hivHealthCenterOutsourcing := some false
    hivMethod := some .pa }

example : PermitsRate .hiv12Qual hivSample 109 := by
  refine ⟨rfl, ?_, (rate_iff ..).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, condition, stsRule,
    mycoplasmaAntibodyRule, mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule,
    mycoplasmaSelection, isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule,
    htlvRule, influenzaChoice, pneumoniaeChoice, metapneumovirusChoice, viralClassChoice,
    aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule,
    hivDigestiveRule, hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule,
    hivOtherInstitutionRule, hivMethodRule, isHivScreening, hivSample, sample]

example : ¬ Eligible
    { hivSample with hivRoute := some (.clinical (.undocumentedFactor 1977 .neonatalOrSimilar)) } := by
  intro h
  have year := h hivNeonatalRule (by simp [eligibilityRules]) 1977 rfl rfl
  omega

private def followUpPeriod : Period :=
  ⟨⟨⟨2026, 7⟩, ⟨22, by decide⟩⟩, hivSample.performance.site.date, by decide⟩

private def followUpSample : HivFollowUp :=
  { series := ⟨2, 4, 1, followUpPeriod.first, .plasmaProduct⟩
    approximatelyTwoMonths := true
    history := ⟨⟨⟨2, none, followUpPeriod⟩, []⟩, by simp⟩ }

private def transfusionSample : Context :=
  { hivSample with hivRoute := some (.transfusion followUpSample) }

example : hivOtherInstitutionRule.holds transfusionSample () := by
  intro _ f hf _
  have eq : followUpSample = f := by
    simpa [transfusionSample] using hf
  subst f
  exact ⟨rfl, followUpPeriod, rfl, rfl, rfl, by decide⟩

example : hivFinalDayEntry.holds transfusionSample (some followUpPeriod.first) := by
  intro _ f hf
  have eq : followUpSample = f := by
    simpa [transfusionSample] using hf
  subst f
  rfl

private def strepCultureSample : StrepCulture :=
  let rapid := { (sample .rapidGroupAStrep).performance with simultaneous := some 1 }
  ⟨rapid, { rapid with id := 2, item := .bacterialCultureD018 }, some false⟩

example : ¬ strepCultureRule.holds strepCultureSample true := by
  intro h
  have bad := (h rfl rfl rfl rfl rfl).1
  contradiction

private def titer (id : Nat) (target : Target) : Context × Target :=
  let p := { (sample .viralTiter).performance with id := id }
  ({ performance := p, target := some target, treatmentNecessity := some true
     combined := some { members := [p] } }, target)

private def nineTargets : List (Context × Target) :=
  [titer 1 .adenovirus, titer 2 .coxsackie, titer 3 .cytomegalovirus,
    titer 4 .eb, titer 5 .echo, titer 6 .herpes, titer 7 .mumps,
    titer 8 .parainfluenzaI, titer 9 .parainfluenzaII]

private def nineTargetGroup : ViralGroup :=
  ⟨(sample .viralTiter).performance, nineTargets⟩

example : nineTargetGroup.Assessed := by
  refine ⟨by simp [nineTargetGroup, nineTargets], by decide, ?_⟩
  simp (config := { maxSteps := 500000 }) [nineTargetGroup, nineTargets, titer, sample, Eligible, eligibilityRules,
    satisfies_cons, satisfies_nil, stsRule, condition, mycoplasmaAntibodyRule,
    mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule, mycoplasmaSelection,
    isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule, pyloriMethodRule,
    pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule, htlvRule,
    influenzaChoice, metapneumovirusChoice, isFluTarget, pneumoniaeChoice, viralClassChoice,
    aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule, hivDigestiveRule,
    hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule, hivOtherInstitutionRule,
    hivMethodRule, isHivScreening, Combined.Valid, Performance.sameSpecimen, Performance.sameGroup]

example : Satisfies viralRules nineTargetGroup 632 :=
  (viral_legacy_iff ..).mpr rfl

example : Satisfies viralRules
    { nineTargetGroup with measurements := nineTargets.take 8 } 632 :=
  (viral_legacy_iff ..).mpr rfl

example : Satisfies viralRules
    { nineTargetGroup with measurements := [titer 1 .adenovirus, titer 2 .adenovirus] } 79 :=
  (viral_legacy_iff ..).mpr rfl

private def withoutPartners (c : Context) : Context :=
  { c with combined := some {
      members := [c.performance]
      viralTarget := fun _ => c.target
      antibodyClass := fun _ => c.antibodyClass } }

private def influenzaSample (hours : Rat) : Context :=
  withoutPartners { sample .influenzaAntigen with hoursSinceOnset := some hours, method := some .oia }

example : PermitsRate .influenzaAntigen (influenzaSample 48) 132 := by
  refine ⟨rfl, ?_, (rate_iff ..).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, condition,
    stsRule, mycoplasmaAntibodyRule, mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule,
    mycoplasmaSelection, isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule,
    htlvRule, influenzaChoice, pneumoniaeChoice, metapneumovirusChoice, viralClassChoice,
    aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule,
    hivDigestiveRule, hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule,
    hivOtherInstitutionRule, hivMethodRule, isHivScreening, influenzaSample, withoutPartners,
    sample, confirmedTargets, Combined.Valid, respiratoryGroup, isFluAntibody, methodIn] <;> decide

example : ¬ fluTiming.holds (influenzaSample 49) () := by
  rintro h
  obtain ⟨hours, hHours, _, hBound⟩ := h ⟨_, by simp, rfl⟩
  have eq : hours = 49 := (Option.some.inj hHours).symm
  subst hours
  exact (by decide : ¬ ((49 : Rat) ≤ 48)) hBound

private def classSample (id : Nat) (target : Target) : Context × Target :=
  let c := sample .classSpecificTiter
  let measurement := { c with
    performance := { c.performance with id := id }
    target := some target
    antibodyClass := some .igg }
  (withoutPartners measurement, target)

private def classSampleGroup : ClassGroup :=
  ⟨(sample .classSpecificTiter).performance,
    [classSample 1 .herpes, classSample 2 .rubella, classSample 3 .cytomegalovirus]⟩

example : classSampleGroup.Assessed := by
  refine ⟨by simp [classSampleGroup], by decide, by decide, ?_⟩
  simp (config := { maxSteps := 500000 }) [classSampleGroup, classSample, withoutPartners,
    sample, Eligible, eligibilityRules, satisfies_cons, satisfies_nil, condition,
    stsRule, mycoplasmaAntibodyRule, mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule,
    mycoplasmaSelection, isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule,
    htlvRule, influenzaChoice, metapneumovirusChoice, pneumoniaeChoice, viralClassChoice,
    aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule,
    hivDigestiveRule, hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule,
    hivOtherInstitutionRule, hivMethodRule, isHivScreening, Combined.Valid,
    Performance.sameSpecimen, Performance.sameGroup, classHerpes, classRubella, classCmv,
    classEb, classMeasles, classMumps, classParvovirus, classVaricella, classTargetRule, iggOrIgm]

example : Satisfies classGroupRules classSampleGroup 400 :=
  (class_group_legacy_iff ..).mpr rfl

example : Satisfies classGroupRules
    { classSampleGroup with measurements := classSampleGroup.measurements.take 2 } 400 :=
  (class_group_legacy_iff ..).mpr rfl

example : Satisfies classGroupRules
    { classSampleGroup with measurements := classSampleGroup.measurements.take 1 } 200 :=
  (class_group_legacy_iff ..).mpr rfl

example : ¬ aavFacility.holds { sample .aav9 with facilityNotified := some true } () := by
  intro h
  have missing := (h ⟨_, by simp [aavTests], rfl⟩).1
  contradiction

example : ¬ diagnosticRepeat (sample .covidQual) .covidQual := by
  rintro (⟨h, hh, _⟩ | ⟨⟨h, hh, _⟩, _⟩) <;> cases hh

end Sanri.MedicalFee.D012
