import Sanri.D001
import Sanri.D004
import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D009

open Sanri.Logic Sanri.History

abbrev Number := Fin 36

structure Item where
  slot : Number
  variant : Nat := 0
  deriving DecidableEq, Repr

def Item.number (i : Item) : Nat := i.slot.val + 1

def Item.variantCount (i : Item) : Nat :=
  if i.number ∈ [6, 9, 10, 12, 16, 17, 28, 33] then 2 else 1

def rates : Vector Nat 36 :=
  #v[80, 98, 99, 101, 110, 112, 115, 120, 121, 131, 136, 139,
    140, 142, 144, 146, 150, 152, 154, 158, 160, 163, 170, 175,
    184, 185, 187, 190, 200, 220, 248, 281, 305, 320, 335, 438]

def Item.base (i : Item) : Nat := rates.get i.slot

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度・2026-06-01適用",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def itemRule (slot : Number) : Rule Item Nat :=
  let n := slot.val + 1
  ⟨"primary/D009/item/" ++ toString n,
    primary ("PDF" ++ (if n ≤ 12 then "182" else "183") ++ "頁 D009 " ++ toString n),
    fun i p => i.slot = slot → i.variant < i.variantCount ∧ p = rates.get slot⟩

def itemRules : List (Rule Item Nat) := (List.finRange 36).map itemRule

theorem item_iff (i : Item) (p : Nat) :
    Satisfies itemRules i p ↔ i.variant < i.variantCount ∧ p = i.base := by
  constructor
  · intro h
    exact h (itemRule i.slot) (by simp [itemRules]) rfl
  · rintro ⟨valid, hp⟩ _ member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    intro hs
    subst slot
    exact ⟨valid, hp⟩

def legacyRow (slot : Number) : Option (Nat × Option Nat) :=
  (SpecimenTests.lookup .d009 (slot.val + 1) 0).map fun e => (e.variants.length, e.points)

private theorem legacyRows :
    ∀ slot : Number, legacyRow slot = some
      ((Item.mk slot 0).variantCount, some (Item.mk slot 0).base) := by decide

theorem legacy_lookup (i : Item) :
    legacyRow i.slot = some (i.variantCount, some i.base) := legacyRows i.slot

theorem item_determines : DeterminesOn (fun i => i.variant < i.variantCount) itemRules := by
  intro i valid
  exact ⟨⟨i.base, (item_iff ..).mpr ⟨valid, rfl⟩⟩,
    fun a b ha hb => ((item_iff i a).mp ha).2.trans ((item_iff i b).mp hb).2.symm⟩

inductive Route where
  | d009 | b001I | b001Ro | b001Management
  deriving DecidableEq

inductive Phase where
  | diagnosis | beforeTreatment | afterTreatment
  deriving DecidableEq

inductive ClaimKind where
  | diagnosticEpisode | liverException | endometriosis (phase : Phase)
  | psa | p53 | s23psa | phi | apoa2 | management
  deriving DecidableEq

inductive Method where
  | electrophoresisWithAffinityBlot | lba | quantitativeLba | eia | clia | eclia | cleia | elisa
  deriving DecidableEq

inductive Purpose where
  | diagnosis | diagnosisAid | treatmentEffect | followup | recurrence | boneMetastasis
  deriving DecidableEq

inductive Companion where
  | cea | dupan2 | ca125 | ca602 | nmp22 | urineCytokeratin | ca153 | cslex
  | nse | progrp | psa | freePsaRatio | s23psa | phi | apoa2 | span1
  deriving DecidableEq

structure Selection where
  group : List (Performance Companion)
  selected : Nat

inductive MesotheliomaEvidence where
  | asbestosAndFluid | cytology | imaging
  deriving DecidableEq

inductive PhiBand where
  | standard | age50To64 | age65To69
  deriving DecidableEq

inductive PancreaticRisk where
  | high | moderate | multipleFactors
  deriving DecidableEq

structure Context where
  performance : Performance Item
  route : Route
  history : Option (ClaimHistory ClaimKind) := none
  episode : Option Period := none
  prostateEpisode : Option Period := none
  pancreaticEpisode : Option Period := none
  repeatWindow : Option Period := none
  endometriosisPeriod : Option Period := none
  phase : Option Phase := none
  method : Option Method := none
  mesotheliomaEvidence : Option MesotheliomaEvidence := none
  phiBand : Option PhiBand := none
  pancreaticRisk : Option PancreaticRisk := none
  purpose : Option Purpose := none
  psaValue : Option Rat := none
  ca199Value : Option Rat := none
  age : Option Nat := none
  malignancySuspectedFromCareAndNonMarkerTests : Prop := False
  malignancyConfirmed : Option Bool := none
  plannedManagementInProgress : Option Bool := none
  plannedManagementBasedOnResult : Prop := False
  pancreatitis : Prop := False
  endometriosisTarget : Prop := False
  cirrhosis : Prop := False
  hbsPositiveChronicHepatitis : Prop := False
  hcvAntibodyPositiveChronicHepatitis : Prop := False
  familialAdenomatousPolyposis : Prop := False
  confirmedBladderCancer : Prop := False
  prostateCancerStronglySuspected : Prop := False
  prostateDiagnosisUndetermined : Prop := False
  prostateBiopsyEtcUndetermined : Prop := False
  d002Erythrocytes : Prop := False
  urothelialCancerStronglySuspected : Prop := False
  breastCancerStronglySuspected : Prop := False
  confirmedNonSmallCellLungCancer : Prop := False
  esophagealColorectalOrBreastCancerStronglySuspected : Prop := False
  confirmedBreastLungOrProstateCancer : Prop := False
  confirmedMesothelioma : Prop := False
  asbestosExposure : Prop := False
  cavityFluidPresent : Prop := False
  mesotheliomaSuspectedOnCytology : Prop := False
  serosalTumorOnImaging : Prop := False
  phiCalculatedFromThreeComponents : Prop := False
  abnormalNippleDischarge : Prop := False
  nonMassBreastCancerStronglySuspected : Prop := False
  nippleFluidCeaMeasured : Prop := False
  her2Overexpression : Prop := False
  recurrentCancerHer2UnconfirmedByOtherMethods : Prop := False
  bloodSpecimen : Prop := False
  pancreaticGuidanceFollowed : Prop := False
  pancreaticHighRisk : Prop := False
  pancreaticModerateRisk : Prop := False
  pancreaticRiskFactors : Option Nat := none
  noRecentCa199AtLeast37 : Prop := False
  ceaNegative : Prop := False
  ca199Negative : Prop := False
  confirmedNhlOrAtl : Prop := False
  nhlAtlOrMethotrexateAssociatedLpdDiagnosticTarget : Prop := False
  /-- 併測・同時実施の確認範囲と選択。候補自身の実施IDで照合する。 -/
  together : Option Selection := none
  simultaneous : Option Selection := none
  pancreaticSelection : Prop := False
  /-- (6)におけるD009とB001-3の両経路を横断する同じ選択。 -/
  endometriosisManagementSelection : Option Selection := none

def Context.is (c : Context) (n : Nat) : Prop := c.performance.item.number = n

def Context.isVariant (c : Context) (n v : Nat) : Prop :=
  c.is n ∧ c.performance.item.variant = v

def prior (c : Context) (period : Period) (kind : ClaimKind) : Option Nat := do
  let h ← c.history
  count h ⟨c.performance.site.patient, none, period⟩ (· == kind)

def Within (c : Context) (window : Option Period) (kind : ClaimKind) (limit : Nat) : Prop :=
  ∃ p, window = some p ∧ p.Contains c.performance.site.date ∧
    ∃ n, prior c p kind = some n ∧ n ≤ limit

def monthly (c : Context) : Option Period := some (Period.month c.performance.site.date.month)

def RepeatAllowed (c : Context) (kind : ClaimKind) (condition : Prop) : Prop :=
  Within c c.prostateEpisode kind 0 ∨
    (condition ∧ Within c c.prostateEpisode kind 2 ∧ Within c c.repeatWindow kind 0)

def InSelection (c : Context) (selection : Option Selection) (others : List Companion)
    (sameEvent : Performance Item → Performance Companion → Prop) : Prop :=
  ∃ s, selection = some s ∧
    ((∃ e ∈ s.group, e.item ∈ others ∧ sameEvent c.performance e) →
      s.selected = c.performance.id)

def main (c : Context) (others : List Companion) : Prop :=
  InSelection c c.together others fun a b =>
    a.site.patient = b.site.patient ∧ a.site.institution = b.site.institution

def simultaneousChoice (c : Context) (others : List Companion) : Prop :=
  ∃ s, c.simultaneous = some s ∧
    ∀ e ∈ s.group, e.item ∈ others →
      (c.performance.sameGroup Performance.simultaneous
        { id := e.id, site := e.site, item := c.performance.item, simultaneous := e.simultaneous }) =
          some false ∨
      ((c.performance.sameGroup Performance.simultaneous
        { id := e.id, site := e.site, item := c.performance.item, simultaneous := e.simultaneous }) =
          some true ∧ s.selected = c.performance.id)

def d009Only (c : Context) : Prop := c.route = .d009

def exceptionA (c : Context) : Prop :=
  c.is 8 ∧ c.pancreatitis ∧ (c.purpose = some .diagnosis ∨ c.purpose = some .followup)

def exceptionI (c : Context) : Prop :=
  (c.is 2 ∨ c.is 10) ∧ (c.cirrhosis ∨ c.hbsPositiveChronicHepatitis ∨ c.hcvAntibodyPositiveChronicHepatitis) ∧
    Within c (monthly c) .liverException 0

def exceptionU (c : Context) : Prop :=
  (c.is 11 ∨ c.isVariant 28 0) ∧ c.endometriosisTarget ∧ ∃ phase, c.phase = some phase ∧
    (phase = .diagnosis ∧ c.purpose = some .diagnosis ∨
      (phase = .beforeTreatment ∨ phase = .afterTreatment) ∧ c.purpose = some .treatmentEffect) ∧
    Within c c.endometriosisPeriod (.endometriosis phase) 0

def exceptionE (c : Context) : Prop := c.is 3 ∧ c.familialAdenomatousPolyposis

def SeparateException (c : Context) : Prop :=
  c.malignancyConfirmed = some true ∧ (exceptionA c ∨ exceptionI c ∨ exceptionU c ∨ exceptionE c)

/-- (4)、(20)イ、(21)イが認める診断中の再検査。 -/
def ConfirmedRepeat (c : Context) (kind : ClaimKind) : Prop :=
  ¬ Within c c.prostateEpisode kind 0 ∧
    Within c c.prostateEpisode kind 2 ∧ Within c c.repeatWindow kind 0

def ProstateRepeat (c : Context) : Prop :=
  (c.isVariant 9 0 ∧ c.prostateDiagnosisUndetermined ∧
    (∃ v, c.psaValue = some v ∧ 4 ≤ v) ∧ ConfirmedRepeat c .psa) ∨
  (c.is 31 ∧ c.prostateBiopsyEtcUndetermined ∧ ConfirmedRepeat c .s23psa) ∨
  (c.is 32 ∧ c.prostateBiopsyEtcUndetermined ∧ ConfirmedRepeat c .phi)

def EpisodeAvailable (c : Context) : Prop :=
  Within c c.episode .diagnosticEpisode 0 ∨ ProstateRepeat c

def note1 : Rule Context Unit :=
  ⟨"primary/D009/note/1", primary "PDF183頁 D009 注1", fun c _ => d009Only c →
    SeparateException c ∨ (c.malignancySuspectedFromCareAndNonMarkerTests ∧
      EpisodeAvailable c ∧ Within c (monthly c) .management 0)⟩

private def clause {Input : Type} (id page : String) (holds : Input → Prop) : Rule Input Unit :=
  ⟨"notice/D009/paragraph/" ++ id, notice ("PDF" ++ page ++ "頁 D009(" ++ id ++ ")"),
    fun c _ => holds c⟩

def generalRule : Rule Context Unit :=
  clause "1" "364–365" fun c => d009Only c → SeparateException c ∨
    (c.malignancyConfirmed = some false ∧ c.plannedManagementInProgress = some false ∧
      EpisodeAvailable c ∧ Within c (monthly c) .management 0)

inductive Exception where
  | pancreatitis | chronicLiverDisease | endometriosis | polyposis
  deriving DecidableEq

def Exception.condition : Exception → Context → Prop
  | .pancreatitis => exceptionA
  | .chronicLiverDisease => exceptionI
  | .endometriosis => exceptionU
  | .polyposis => exceptionE

def exceptionRule (e : Exception) : Rule (Context × Exception) Unit :=
  clause (match e with
    | .pancreatitis => "1/a" | .chronicLiverDisease => "1/i"
    | .endometriosis => "1/u" | .polyposis => "1/e") "365"
    (fun x => x.2 = e → x.1.malignancyConfirmed = some true ∧ e.condition x.1)

def btaRule : Rule Context Unit :=
  clause "2" "365" fun c => c.is 1 →
    c.route = .b001I ∧ c.confirmedBladderCancer ∧ c.purpose = some .recurrence ∧
      c.plannedManagementBasedOnResult

def ceaChoice : Rule Context Unit :=
  clause "3" "365" fun c => d009Only c →
    (c.is 3 → main c [.dupan2]) ∧ (c.is 7 → main c [.cea])

def psaRule : Rule Context Unit :=
  clause "4" "365" fun c => d009Only c → c.isVariant 9 0 →
    c.prostateCancerStronglySuspected ∧ RepeatAllowed c .psa
      (c.prostateDiagnosisUndetermined ∧ ∃ v, c.psaValue = some v ∧ 4 ≤ v)

def ca125Choice : Rule Context Unit :=
  clause "5" "365" fun c => d009Only c →
    (c.is 11 → main c [.ca602]) ∧ (c.isVariant 28 0 → main c [.ca125])

def crossManagementChoice : Rule Context Unit :=
  clause "6" "365" fun c =>
    (c.is 11 → InSelection c c.endometriosisManagementSelection [.ca602]
      (fun a b => a.site.patient = b.site.patient)) ∧
    (c.isVariant 28 0 → InSelection c c.endometriosisManagementSelection [.ca125]
      (fun a b => a.site.patient = b.site.patient))

def nmpRule : Rule Context Unit :=
  clause "7/a" "365" fun c => c.is 12 → d009Only c ∧
    c.d002Erythrocytes ∧ c.urothelialCancerStronglySuspected

def nmpManagement : Rule Context Unit :=
  clause "7/i" "365" fun c => c.is 12 → c.malignancyConfirmed = some true → d009Only c

def urinePair : Rule Context Unit :=
  clause "8" "366" fun c => d009Only c →
    (c.is 12 → simultaneousChoice c [.urineCytokeratin]) ∧
    (c.is 21 → simultaneousChoice c [.nmp22])

def freePsaRule : Rule Context Unit :=
  clause "9" "366" fun c => d009Only c → c.isVariant 17 1 → c.prostateCancerStronglySuspected

def cslexRule : Rule Context Unit :=
  clause "10/a" "366" fun c => d009Only c → c.is 18 → c.breastCancerStronglySuspected

def cslexChoice : Rule Context Unit :=
  clause "10/i" "366" fun c => d009Only c →
    (c.is 18 → main c [.ca153]) ∧ (c.isVariant 6 1 → main c [.cslex])

def cyfraRule : Rule Context Unit :=
  clause "11" "366" fun c => c.is 19 → c.malignancyConfirmed = some true →
    c.route = .b001Management ∧ c.confirmedNonSmallCellLungCancer

def cytokeratinRule : Rule Context Unit :=
  clause "12/a" "366" fun c => c.is 21 → d009Only c ∧
    c.d002Erythrocytes ∧ c.urothelialCancerStronglySuspected

def cytokeratinManagement : Rule Context Unit :=
  clause "12/i" "366" fun c => c.is 21 → c.malignancyConfirmed = some true → d009Only c

def p53Rule : Rule Context Unit :=
  clause "13" "366" fun c => d009Only c → c.is 22 →
    c.esophagealColorectalOrBreastCancerStronglySuspected ∧ Within c (monthly c) .p53 0

def boneMetastasisRule : Rule Context Unit :=
  clause "14" "366" fun c => c.is 23 → c.malignancyConfirmed = some true →
    c.route = .b001Ro ∧ c.confirmedBreastLungOrProstateCancer ∧
      c.purpose = some .boneMetastasis ∧ c.plannedManagementBasedOnResult

def progrpChoice : Rule Context Unit :=
  clause "15" "366" fun c => d009Only c →
    (c.is 14 → main c [.progrp]) ∧ (c.is 24 → main c [.nse])

def afpL3Rule : Rule Context Unit :=
  clause "16" "366" fun c => c.is 26 →
    c.method = some .electrophoresisWithAffinityBlot ∨ c.method = some .lba

def tfpiRule : Rule Context Unit :=
  clause "17" "366" fun c => c.isVariant 28 1 → c.method = some .eia

def he4Rule : Rule Context Unit :=
  clause "18" "366" fun c => c.is 29 → c.method = some .clia ∨ c.method = some .eclia

def mesotheliomaPurpose : Rule Context Unit :=
  clause "19/a" "366–367" fun c => c.is 30 →
    (c.purpose = some .diagnosisAid ∨ c.purpose = some .treatmentEffect ∨ c.purpose = some .followup)

def mesotheliomaAid : Rule Context Unit :=
  clause "19/i" "367" fun c => c.is 30 → c.purpose = some .diagnosisAid →
    d009Only c ∧ c.mesotheliomaEvidence.isSome = true

def mesotheliomaEvidenceRule (e : MesotheliomaEvidence) : Rule Context Unit :=
  clause (match e with | .asbestosAndFluid => "19/i/i" | .cytology => "19/i/ro" | .imaging => "19/i/ha")
    "367" fun c => c.is 30 → c.purpose = some .diagnosisAid → c.mesotheliomaEvidence = some e →
      match e with
      | .asbestosAndFluid => c.asbestosExposure ∧ c.cavityFluidPresent
      | .cytology => c.mesotheliomaSuspectedOnCytology
      | .imaging => c.serosalTumorOnImaging

def mesotheliomaManagement : Rule Context Unit :=
  clause "19/u" "367" fun c => c.is 30 →
    (c.purpose = some .treatmentEffect ∨ c.purpose = some .followup) →
      c.route = .b001Ro ∧ c.confirmedMesothelioma ∧ c.plannedManagementBasedOnResult

def PsaIn (c : Context) (lower : Rat) : Prop :=
  ∃ v, c.psaValue = some v ∧ lower ≤ v ∧ v ≤ 10

def s23Indication : Rule Context Unit :=
  clause "20/a" "367" fun c => d009Only c → c.is 31 →
    c.prostateCancerStronglySuspected ∧ PsaIn c 4 ∧ c.method = some .quantitativeLba

def s23Repeat : Rule Context Unit :=
  clause "20/i" "367" fun c => d009Only c → c.is 31 →
    c.purpose = some .diagnosis ∧ RepeatAllowed c .s23psa c.prostateBiopsyEtcUndetermined

def s23Choice : Rule Context Unit :=
  clause "20/u" "367" fun c => d009Only c →
    (c.is 31 → main c [.psa, .freePsaRatio, .phi]) ∧
    (c.isVariant 9 0 ∨ c.isVariant 17 1 ∨ c.is 32 → main c [.s23psa])

def phiIndication : Rule Context Unit :=
  clause "21/a" "367" fun c => d009Only c → c.is 32 →
    c.prostateCancerStronglySuspected ∧ c.method = some .cleia ∧ c.phiCalculatedFromThreeComponents ∧
      c.phiBand.isSome = true

def phiBandRule (band : PhiBand) : Rule Context Unit :=
  clause (match band with | .standard => "21/a/i" | .age50To64 => "21/a/ro" | .age65To69 => "21/a/ha")
    "367" fun c => d009Only c → c.is 32 → c.phiBand = some band →
      match band with
      | .standard => PsaIn c 4
      | .age50To64 => (∃ age, c.age = some age ∧ 50 ≤ age ∧ age < 65) ∧ PsaIn c 3
      | .age65To69 => (∃ age, c.age = some age ∧ 65 ≤ age ∧ age < 70) ∧ PsaIn c (7 / 2)

def phiRepeat : Rule Context Unit :=
  clause "21/i" "367" fun c => d009Only c → c.is 32 →
    RepeatAllowed c .phi c.prostateBiopsyEtcUndetermined

def phiPsaChoice : Rule Context Unit :=
  clause "21/u" "367" fun c => d009Only c →
    (c.is 32 → main c [.psa]) ∧ (c.isVariant 9 0 → main c [.phi])

def phiRatioChoice : Rule Context Unit :=
  clause "21/e" "368" fun c => d009Only c →
    (c.is 32 → main c [.freePsaRatio]) ∧ (c.isVariant 17 1 → main c [.phi])

def nippleRule : Rule Context Unit :=
  clause "22" "368" fun c => c.is 33 → d009Only c ∧ c.abnormalNippleDischarge ∧
    c.nonMassBreastCancerStronglySuspected ∧ c.nippleFluidCeaMeasured

def her2Rule : Rule Context Unit :=
  clause "23" "368" fun c => c.is 34 → c.route = .b001Ro ∧
    ((c.malignancyConfirmed = some true ∧ c.her2Overexpression) ∨ c.recurrentCancerHer2UnconfirmedByOtherMethods) ∧
    c.plannedManagementBasedOnResult

def apoaIndication : Rule Context Unit :=
  clause "24/a" "368" fun c => c.is 35 → d009Only c ∧ c.purpose = some .diagnosisAid ∧
    c.bloodSpecimen ∧ c.method = some .elisa ∧ c.pancreaticGuidanceFollowed ∧
    Within c c.pancreaticEpisode .apoa2 0 ∧
    c.pancreaticRisk.isSome = true

def pancreaticRiskRule (risk : PancreaticRisk) : Rule Context Unit :=
  clause (match risk with | .high => "24/a/i" | .moderate => "24/a/ro" | .multipleFactors => "24/a/ha")
    "368" fun c => c.is 35 → c.pancreaticRisk = some risk →
      match risk with
      | .high => c.pancreaticHighRisk ∧ c.noRecentCa199AtLeast37
      | .moderate => c.pancreaticModerateRisk ∧ c.ceaNegative ∧
          ∃ v, c.ca199Value = some v ∧ 37 ≤ v ∧ v ≤ 100
      | .multipleFactors => c.ceaNegative ∧ c.ca199Negative ∧
          ∃ n, c.pancreaticRiskFactors = some n ∧ 3 ≤ n

def apoaChoice : Rule Context Unit :=
  clause "24/i" "368" fun c => d009Only c →
    (c.is 35 → main c [.cea, .dupan2, .span1]) ∧
    (c.is 3 ∨ c.is 7 ∨ c.is 15 → main c [.apoa2])

def sil2Rule : Rule Context Unit :=
  clause "25" "368" fun c => c.is 36 →
    (d009Only c ∧ c.purpose = some .diagnosis ∧ c.nhlAtlOrMethotrexateAssociatedLpdDiagnosticTarget) ∨
    (c.route = .b001Ro ∧ c.purpose = some .followup ∧ c.confirmedNhlOrAtl)

structure Documentation where
  psaValue : Prop
  psaDateAndResult : Prop
  repeatMedicalGrounds : Prop
  mesotheliomaReason : Prop
  apoaHighRisk : Prop
  apoaOtherRisk : Prop

private def written (id page : String) (holds : Context → Documentation → Prop) :
    Rule Context Documentation :=
  ⟨"notice/D009/paragraph/" ++ id, notice ("PDF" ++ page ++ "頁 D009(" ++ id ++ ")"), holds⟩

def psaDocumentation : Rule Context Documentation :=
  written "4" "365" fun c d => c.isVariant 9 0 →
    ¬ Within c c.prostateEpisode .psa 0 → d.psaValue

def mesotheliomaDocumentation : Rule Context Documentation :=
  written "19/i" "367" fun c d => c.is 30 → c.purpose = some .diagnosisAid → d.mesotheliomaReason

def s23Documentation : Rule Context Documentation :=
  written "20/e" "367" fun c d => c.is 31 →
    d.psaDateAndResult ∧ (¬ Within c c.prostateEpisode .s23psa 0 → d.repeatMedicalGrounds)

def phiDocumentation : Rule Context Documentation :=
  written "21/o" "368" fun c d => c.is 32 →
    d.psaDateAndResult ∧ (¬ Within c c.prostateEpisode .phi 0 → d.repeatMedicalGrounds)

def apoaDocumentation : Rule Context Documentation :=
  ⟨"notice/D009/paragraph/24/u", notice "PDF368頁 D009(24)ウ",
    fun c d => c.is 35 →
      (c.pancreaticRisk = some .high → d.apoaHighRisk) ∧
      (c.pancreaticRisk = some .moderate ∨ c.pancreaticRisk = some .multipleFactors → d.apoaOtherRisk)⟩

def nmpParagraph : Rule Context Unit :=
  clause "7" "365" fun c => c.is 12 → d009Only c

def cslexParagraph : Rule Context Unit :=
  clause "10" "366" fun c => c.is 18 → d009Only c → c.breastCancerStronglySuspected

def cytokeratinParagraph : Rule Context Unit :=
  clause "12" "366" fun c => c.is 21 → d009Only c

def mesotheliomaParagraph : Rule Context Unit :=
  clause "19" "366–367" fun c => c.is 30 →
    (d009Only c ∧ c.purpose = some .diagnosisAid) ∨
    (c.route = .b001Ro ∧ (c.purpose = some .treatmentEffect ∨ c.purpose = some .followup))

def s23Paragraph : Rule Context Unit :=
  clause "20" "367" fun c => c.is 31 → d009Only c

def phiParagraph : Rule Context Unit :=
  clause "21" "367–368" fun c => c.is 32 → d009Only c

def apoaParagraph : Rule Context Unit :=
  clause "24" "368" fun c => c.is 35 → d009Only c

def pancreaticSelectionRule : Rule Context Unit :=
  ⟨D001.pancreaticRule.id, D001.pancreaticRule.source, fun c _ =>
    c.is 8 → d009Only c → c.pancreaticSelection⟩

/-- 膵関連の相手と共有する主検査選択。D007は同じ選択への照合を外部で確認する。 -/
def SharedPancreaticSelection (urine : D001.Context) (marker : Context) (selected : Nat) : Prop :=
  urine.performance.item = .trypsinogen2 ∧ marker.is 8 ∧
    urine.performance.site.patient = marker.performance.site.patient ∧
    urine.performance.site.institution = marker.performance.site.institution ∧
    urine.performance.id ≠ marker.performance.id ∧
    (urine.pancreaticSelection ↔ selected = urine.performance.id) ∧
    (marker.pancreaticSelection ↔ selected = marker.performance.id)

theorem sharedPancreaticSelection_exclusive (h : SharedPancreaticSelection urine marker selected) :
    ¬ (urine.pancreaticSelection ∧ marker.pancreaticSelection) := by
  obtain ⟨_, _, _, _, distinct, hu, hm⟩ := h
  exact fun ⟨u, m⟩ => distinct ((hu.mp u).symm.trans (hm.mp m))

def eligibilityRules :=
  [note1, generalRule, btaRule, ceaChoice, psaRule, ca125Choice, crossManagementChoice,
    nmpRule, nmpManagement, urinePair, freePsaRule, cslexRule, cslexChoice, cyfraRule,
    cytokeratinRule, cytokeratinManagement, p53Rule, boneMetastasisRule, progrpChoice,
    afpL3Rule, tfpiRule, he4Rule, mesotheliomaPurpose, mesotheliomaAid, mesotheliomaManagement,
    s23Indication, s23Repeat, s23Choice, phiIndication, phiRepeat, phiPsaChoice, phiRatioChoice,
    nippleRule, her2Rule, apoaIndication, apoaChoice, sil2Rule, nmpParagraph, cslexParagraph,
    cytokeratinParagraph, mesotheliomaParagraph, s23Paragraph, phiParagraph, apoaParagraph, pancreaticSelectionRule,
    mesotheliomaEvidenceRule .asbestosAndFluid, mesotheliomaEvidenceRule .cytology,
    mesotheliomaEvidenceRule .imaging, phiBandRule .standard, phiBandRule .age50To64, phiBandRule .age65To69,
    pancreaticRiskRule .high, pancreaticRiskRule .moderate, pancreaticRiskRule .multipleFactors]

def Eligible (c : Context) : Prop :=
  d009Only c ∧ c.performance.item.variant < c.performance.item.variantCount ∧
    Satisfies eligibilityRules c ()

theorem individual_determines (c : Context) (h : Eligible c) :
    DeterminesAt itemRules c.performance.item := item_determines _ h.2.1


/-- 旧関数に渡せる共通範囲。通知による適格性は別途確認する。 -/
def legacyRequest (i : Item) (draw : Nat) : SpecimenTests.Request :=
  { code := .d009, number := i.number, variant := i.variant, collectionId := draw
    conditions := { malignancyStronglySuspectedFromCareAndNonMarkerTests := true } }

theorem legacy_individual_iff (i : Item) (draw p : Nat) :
    Satisfies itemRules i p ↔
      SpecimenTests.assessOne (legacyRequest i draw) = some (.charged p 0) := by
  have h := legacy_lookup i
  unfold legacyRow at h
  rw [item_iff]
  generalize hf : SpecimenTests.lookup .d009 (i.slot.val + 1) 0 = row at h
  cases row with
  | none => simp at h
  | some e =>
    have h' : e.variants.length = i.variantCount ∧ e.points = some i.base := by
      simpa using h
    simp only [SpecimenTests.assessOne, legacyRequest, Item.number, hf]
    simp [SpecimenTests.eligible, SpecimenTests.additions, SpecimenTests.rapidMicrobialEligible,
      h'.1, h'.2]
    by_cases hv : i.variant < i.variantCount <;> simp [hv, eq_comm]

def bundleCount (xs : List Item) : Nat := xs.length

def note2 : Rule (List Item) Nat :=
  ⟨"primary/D009/note/2", primary "PDF183頁 D009 注2", fun xs p =>
    bundleCount xs ≤ 1 → p = (xs.map Item.base).sum⟩

def note2I : Rule (List Item) Nat :=
  ⟨"primary/D009/note/2/i", primary "PDF183頁 D009 注2イ", fun xs p =>
    bundleCount xs = 2 → p = 230⟩

def note2Ro : Rule (List Item) Nat :=
  ⟨"primary/D009/note/2/ro", primary "PDF183頁 D009 注2ロ", fun xs p =>
    bundleCount xs = 3 → p = 290⟩

def note2Ha : Rule (List Item) Nat :=
  ⟨"primary/D009/note/2/ha", primary "PDF183頁 D009 注2ハ", fun xs p =>
    4 ≤ bundleCount xs → p = 385⟩

def bundleRules := [note2, note2I, note2Ro, note2Ha]

def bundlePoints (xs : List Item) : Nat :=
  SpecimenTests.groupedBase .tumorMarkers (bundleCount xs) (xs.map Item.base).sum

theorem bundle_iff (xs : List Item) (p : Nat) :
    Satisfies bundleRules xs p ↔ p = bundlePoints xs := by
  simp only [bundleRules, satisfies_cons, satisfies_nil, note2, note2I, note2Ro, note2Ha,
    and_true, bundlePoints, SpecimenTests.groupedBase]
  generalize bundleCount xs = n
  generalize (xs.map Item.base).sum = total
  by_cases h4 : 4 ≤ n
  · simp [h4, show ¬ n ≤ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
  by_cases h3 : n = 3
  · subst n
    simp
  by_cases h2 : n = 2
  · subst n
    simp
  simp [h4, h3, h2, show n ≤ 1 by omega]

structure Bundle where
  anchor : Performance Item
  members : List Context

def Bundle.items (g : Bundle) : List Item := g.members.map (·.performance.item)

def SameNippleDay (a b : Performance Item) : Prop :=
  a.site.patient = b.site.patient ∧ a.site.institution = b.site.institution ∧
    a.site.sameDay b.site = true ∧ b.item.number = 33

def sameDayNippleRule : Rule Bundle Unit :=
  clause "26" "369" fun g =>
    ∀ c ∈ g.members, c.performance.sameDraw g.anchor = some true ∨
      (SameNippleDay g.anchor c.performance ∧
        ∃ blood ∈ g.members, blood.bloodSpecimen ∧ blood.performance.sameDraw g.anchor = some true)

/-- 一採取群への割当てを確認した重複のない適格実施。 -/
def Bundle.Eligible (g : Bundle) : Prop :=
  g.members ≠ [] ∧ g.items.Nodup ∧
    (∀ c ∈ g.members, D009.Eligible c ∧ 2 ≤ c.performance.item.number) ∧
    Satisfies [sameDayNippleRule] g ()

theorem bundle_determines (g : Bundle) (_ : g.Eligible) :
    DeterminesAt bundleRules g.items :=
  ⟨⟨bundlePoints g.items, (bundle_iff ..).mpr rfl⟩,
    fun a b ha hb => ((bundle_iff g.items a).mp ha).trans ((bundle_iff g.items b).mp hb).symm⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 9, number := i.number, variant := i.variant, ordinaryCategory := .biochemicalII }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .biochemicalII := rfl

def Bundle.toSpecimenItem (g : Bundle) (kind : Nat) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := bundlePoints g.items }

/-- 準用する検査種類と同日群の割当てを確認した側で使う。 -/
def Bundle.urineReference (g : Bundle) (_ : g.Eligible) : UrineFecalTests.ReferenceResolution :=
  ⟨.other .d009, bundlePoints g.items, true⟩

def Bundle.fluidReference (g : Bundle) (_ : g.Eligible) : D004.ReferenceResolution :=
  ⟨.other .d009, bundlePoints g.items, true⟩

theorem permits_individual_iff (c : Context) (draw p : Nat) :
    (Eligible c ∧ Satisfies itemRules c.performance.item p) ↔
      (Eligible c ∧ SpecimenTests.assessOne (legacyRequest c.performance.item draw) =
        some (.charged p 0)) := by
  rw [legacy_individual_iff]

private def sampleDate : Date := ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩

private def sample : Context :=
  { performance := ⟨1, ⟨2, 3, sampleDate⟩, ⟨1, 0⟩, some 4, some 5, none, none⟩
    route := .d009
    history := some ⟨⟨⟨2, none, Period.month sampleDate.month⟩, []⟩, by simp⟩
    episode := some (Period.day sampleDate)
    malignancySuspectedFromCareAndNonMarkerTests := True
    malignancyConfirmed := some false
    plannedManagementInProgress := some false
    bloodSpecimen := True }

private theorem sample_eligible : Eligible sample := by
  have episode : Within sample sample.episode .diagnosticEpisode 0 := by
    exact ⟨_, rfl, (Period.day sampleDate).contains_first, 0, rfl, by decide⟩
  have monthlyManagement : Within sample (monthly sample) .management 0 := by
    exact ⟨_, rfl, by decide, 0, rfl, by decide⟩
  refine ⟨rfl, by decide, ?_⟩
  simp only [eligibilityRules, satisfies_cons, satisfies_nil, note1, generalRule, btaRule,
    ceaChoice, psaRule, ca125Choice, crossManagementChoice, nmpRule, nmpManagement, urinePair,
    freePsaRule, cslexRule, cslexChoice, cyfraRule, cytokeratinRule, cytokeratinManagement,
    p53Rule, boneMetastasisRule, progrpChoice, afpL3Rule, tfpiRule, he4Rule,
    mesotheliomaPurpose, mesotheliomaAid, mesotheliomaManagement, s23Indication, s23Repeat,
    s23Choice, phiIndication, phiRepeat, phiPsaChoice, phiRatioChoice, nippleRule, her2Rule,
    apoaIndication, apoaChoice, sil2Rule, nmpParagraph, cslexParagraph,
    cytokeratinParagraph, mesotheliomaParagraph, s23Paragraph, phiParagraph, apoaParagraph, pancreaticSelectionRule,
    mesotheliomaEvidenceRule, phiBandRule, pancreaticRiskRule, clause]
  simp [sample, d009Only, Context.isVariant, Context.is, Item.number, SeparateException, EpisodeAvailable, ProstateRepeat]
  repeat first | exact episode | exact monthlyManagement | constructor

example : Eligible sample ∧ Satisfies itemRules sample.performance.item 98 :=
  ⟨sample_eligible, (item_iff ..).mpr ⟨by decide, rfl⟩⟩

example : ¬ Eligible { sample with history := none } := by
  intro h
  have result := h.2.2 note1 (by simp [eligibilityRules]) rfl
  rcases result with exception | ⟨_, _, ⟨p, _, _, n, hn, _⟩⟩
  · cases exception.1
  · have impossible : (none : Option Nat) = some n := hn
    cases impossible

example : Satisfies bundleRules [⟨1, 0⟩, ⟨2, 0⟩] 230 := (bundle_iff ..).mpr rfl
example : Satisfies bundleRules [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩] 385 :=
  (bundle_iff ..).mpr rfl

private def nippleSample : Context :=
  { sample with
    performance := { sample.performance with id := 2, item := ⟨32, 0⟩, draw := none, specimen := some 6 }
    bloodSpecimen := False }

private def mixedSample : Bundle := ⟨sample.performance, [sample, nippleSample]⟩

example : sameDayNippleRule.holds mixedSample () := by
  change ∀ c ∈ [sample, nippleSample], _
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact Or.inl rfl
  · have eq := List.mem_singleton.mp hc
    subst c
    exact Or.inr ⟨⟨rfl, rfl, rfl, rfl⟩, sample, List.Mem.head _, trivial, rfl⟩

example : bundlePoints mixedSample.items = 230 := rfl

end Sanri.MedicalFee.D009
