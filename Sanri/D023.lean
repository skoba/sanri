import Sanri.D023Other
import Sanri.D023References
import Sanri.D013

namespace Sanri.MedicalFee.D023

open Sanri.Logic Sanri.History

inductive PertussisTest where
  | pertussis | pertussisAndParapertussis
  deriving DecidableEq, Repr

inductive PertussisMethod where
  | lamp | pcr | other
  deriving DecidableEq

structure PertussisContext where
  performance : Performance PertussisTest
  method : PertussisMethod
  meetsGuidelineClinicalCase : Option Bool := none
  explainedOnTestDay : Bool
  suppliedWrittenResults : Bool

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def pertussisIndication : Rule PertussisContext Unit :=
  ⟨"notice/D023/paragraph/13", notice "PDF391頁 D023(13)", fun c _ =>
    c.performance.item = .pertussis →
      c.meetsGuidelineClinicalCase = some true ∧ c.method ∈ [.lamp, .pcr]⟩

def pertussisDualIndication : Rule PertussisContext Unit :=
  ⟨"notice/D023/paragraph/14", notice "PDF391頁 D023(14)", fun c _ =>
    c.performance.item = .pertussisAndParapertussis →
      c.meetsGuidelineClinicalCase = some true ∧ c.method = .pcr⟩

def PertussisEligible (c : PertussisContext) : Prop :=
  Satisfies [pertussisIndication, pertussisDualIndication] c ()

def pertussisBase : Nat := 360
def rapidPoints : Nat := 100

/-- 第13項のうち百日咳関連の二検査への射影。 -/
def pertussisRate : Rule PertussisContext (Nat × Nat) :=
  ⟨"primary/D023/item/13", primary "PDF190頁 D023 13 百日咳関連", fun _ p => p.1 = pertussisBase⟩

/-- 末尾注の第13項への射影。 -/
def pertussisRapid : Rule PertussisContext (Nat × Nat) :=
  ⟨"primary/D023/note/unnumbered/1", primary "PDF191頁 D023末尾注 第13項",
    fun c p => p.2 = if c.explainedOnTestDay && c.suppliedWrittenResults then rapidPoints else 0⟩

def pertussisRates := [pertussisRate, pertussisRapid]

def pertussisLegacyRequest (c : PertussisContext) : SpecimenTests.Request :=
  { code := .d023, number := 13
    variant := match c.performance.item with | .pertussis => 0 | .pertussisAndParapertussis => 2
    conditions := { resultsExplainedOnTestDay := c.explainedOnTestDay
                    writtenResultsProvided := c.suppliedWrittenResults } }

theorem pertussis_legacy_iff (c : PertussisContext) (p : Nat × Nat) :
    Satisfies pertussisRates c p ↔ SpecimenTests.assessOne (pertussisLegacyRequest c) =
      some (.charged p.1 p.2) := by
  unfold pertussisLegacyRequest
  cases c.performance.item <;> cases he : c.explainedOnTestDay <;> cases hw : c.suppliedWrittenResults <;>
    change Satisfies pertussisRates c p ↔ some (SpecimenTests.ItemResult.charged 360 _) = _ <;>
    simp [pertussisRates, satisfies_cons, satisfies_nil, pertussisRate, pertussisRapid,
      pertussisBase, rapidPoints, he, hw, SpecimenTests.additions, SpecimenTests.rapidMicrobialEligible, @eq_comm Nat 360 p.1, @eq_comm Nat 100 p.2, @eq_comm Nat 0 p.2]

theorem pertussis_determines : DeterminesOn PertussisEligible pertussisRates := by
  intro c _
  refine ⟨⟨(pertussisBase, if c.explainedOnTestDay && c.suppliedWrittenResults then rapidPoints else 0),
    by simp [pertussisRates, satisfies_cons, satisfies_nil, pertussisRate, pertussisRapid]⟩, ?_⟩
  intro a b ha hb
  have same := ((pertussis_legacy_iff _ _).mp ha).symm.trans ((pertussis_legacy_iff _ _).mp hb)
  exact Prod.ext (Option.some.inj same |> SpecimenTests.ItemResult.charged.inj |>.1)
    (Option.some.inj same |> SpecimenTests.ItemResult.charged.inj |>.2)

/-- 末尾注のうち、百日咳関連以外の対象。 -/
inductive OtherRapidTest where
  | mycoplasma | legionella | tuberculosis
  deriving DecidableEq, Repr

def OtherRapidTest.catalogKey : OtherRapidTest → Nat × Nat
  | .mycoplasma => (6, 0)
  | .legionella => (7, 0)
  | .tuberculosis => (14, 1)

structure OtherRapidContext where
  test : OtherRapidTest
  explainedOnTestDay : Bool
  suppliedWrittenResults : Bool

def otherRapid : Rule OtherRapidContext Nat :=
  ⟨"primary/D023/note/unnumbered/1", primary "PDF191頁 D023末尾注 第6・7・14項",
    fun c p => p = if c.explainedOnTestDay && c.suppliedWrittenResults then rapidPoints else 0⟩

def OtherRapidContext.legacyRequest (c : OtherRapidContext) : SpecimenTests.Request :=
  { code := .d023, number := c.test.catalogKey.1, variant := c.test.catalogKey.2
    conditions := { resultsExplainedOnTestDay := c.explainedOnTestDay
                    writtenResultsProvided := c.suppliedWrittenResults } }

theorem otherRapid_legacy_iff (c : OtherRapidContext) (p : Nat) :
    otherRapid.holds c p ↔ SpecimenTests.additions c.legacyRequest = p := by
  obtain ⟨test, explained, supplied⟩ := c
  cases test <;> cases explained <;> cases supplied <;>
    simp [otherRapid, rapidPoints, OtherRapidContext.legacyRequest, OtherRapidTest.catalogKey,
      SpecimenTests.additions, SpecimenTests.rapidMicrobialEligible] <;> exact eq_comm

theorem otherRapid_determines : DeterminesOn (fun _ => True) [otherRapid] := by
  intro c _
  refine ⟨⟨SpecimenTests.additions c.legacyRequest, ?_⟩, ?_⟩
  · simpa [satisfies_cons, satisfies_nil] using
      (otherRapid_legacy_iff c _).mpr rfl
  · intro a b ha hb
    exact ((otherRapid_legacy_iff c a).mp (ha otherRapid (by simp))).symm.trans
      ((otherRapid_legacy_iff c b).mp (hb otherRapid (by simp)))

example : otherRapid.holds ⟨.legionella, true, true⟩ 100 := by rfl
example : otherRapid.holds ⟨.tuberculosis, true, false⟩ 0 := by rfl

def PertussisCombination (c : PertussisContext) (p : Nat × Nat) (antigen : D012.Context)
    (group : D012.Combined) : Prop :=
  PertussisEligible c ∧ Satisfies pertussisRates c p ∧
  antigen.performance.item = .local .pertussisAntigen ∧
  D012.pertussisIndication.holds antigen () ∧
  antigen.combined = some group ∧ group.Valid antigen.performance ∧
  let molecular : Performance D012.RelatedTest := { c.performance with item := .pertussisD023_13 }
  group.Valid molecular ∧
  ∃ selected, group.selected = some selected ∧
    ((antigen.performance.id ∈ selected ∧ molecular.id ∉ selected) ∨
      (molecular.id ∈ selected ∧ antigen.performance.id ∉ selected))

inductive MethicillinMethod where
  | edPcr | pcr | other
  deriving DecidableEq

structure MethicillinContext where
  performance : Performance Unit
  method : MethicillinMethod
  staphDetectedByBloodCulture : Option Bool := none
  immunodeficientWithStrongMrsaSuspicion : Option Bool := none

def methicillinIndication : Rule MethicillinContext Unit :=
  ⟨"notice/D023/paragraph/22", notice "PDF392頁 D023(22)", fun c _ =>
    c.method ∈ [.edPcr, .pcr] ∧
    (c.staphDetectedByBloodCulture = some true ∨
      c.immunodeficientWithStrongMrsaSuspicion = some true)⟩

def MethicillinPair (c : MethicillinContext) (other : D023Other.Context)
    (billedGene : Bool) : Prop :=
  methicillinIndication.holds c () ∧ other.performance.item = .pbp2 ∧
  D023Other.pbp2Indication.holds other () ∧
  c.performance.site.patient = other.performance.site.patient ∧
  c.performance.site.institution = other.performance.site.institution ∧
  (other.pbp2Choice = some .d023MethicillinGene ∧ billedGene = true ∨
    other.pbp2Choice = some .thisTest ∧ billedGene = false)

structure RespiratoryPanelContext where
  performance : Performance Bool
  /-- true は25イ。方法・検体・枝別に指定された同時測定の各対象を照合した結果。 -/
  specifiedQualitativeMicroarrayOnNasopharyngealSwab : Option Bool := none
  highNeedForMultiplePathogens : Option Bool := none
  respiratoryInfectionMayBecomeSevere : Option Bool := none
  forDecidingAdmission : Option Bool := none
  antigenAndOtherNucleicAcidTestsInsufficient : Option Bool := none
  particularMedicalNecessity : Option Bool := none
  evidence : D023Schedule.Evidence
  treatmentScope : Scope
  history : ClaimHistory Nat

def RespiratoryPanelContext.tier (c : RespiratoryPanelContext) : D023Schedule.Tier :=
  if c.performance.item then .respiratoryPanelCovid else .respiratoryPanelWithoutCovid

def RespiratoryPanelContext.prior (c : RespiratoryPanelContext) : Option Nat := do
  let series ← c.performance.series
  if c.treatmentScope.institution = some c.performance.site.institution ∧
      c.treatmentScope.Includes c.performance.site = true then
    count c.history c.treatmentScope (· == series)
  else none

def panelMethod : Rule RespiratoryPanelContext Unit :=
  ⟨"notice/D023/paragraph/37/a", notice "PDF396–397頁 D023(37)ア", fun c _ =>
    c.highNeedForMultiplePathogens = some true ∧
    c.specifiedQualitativeMicroarrayOnNasopharyngealSwab = some true ∧ c.prior = some 0⟩

def panelOutpatient : Rule RespiratoryPanelContext Unit :=
  ⟨"notice/D023/paragraph/37/i/ha", notice "PDF397頁 D023(37)イ(ハ)", fun c _ =>
    c.respiratoryInfectionMayBecomeSevere = some true ∧ c.forDecidingAdmission = some true ∧
    c.antigenAndOtherNucleicAcidTestsInsufficient = some true ∧
    c.particularMedicalNecessity = some true⟩

def panelOutpatientDocumentation : Rule RespiratoryPanelContext Bool :=
  ⟨"notice/D023/paragraph/37/i/ha", notice "PDF397頁 D023(37)イ(ハ) 摘要",
    fun _ recordedMedicalBasis => recordedMedicalBasis = true⟩

def panelAntigenExclusionWithCovid : Rule (RespiratoryPanelContext × D012.Context) Bool :=
  ⟨"notice/D023/paragraph/37/u/ta", notice "PDF398頁 D023(37)ウ(タ)", fun (c, a) separate =>
    c.performance.item = true → a.performance.item = .local .pertussisAntigen →
    Performance.sameSeries { c.performance with item := .multiplexD023_25 }
      a.performance = some true → separate = false⟩

def panelAntigenExclusionWithoutCovid : Rule (RespiratoryPanelContext × D012.Context) Bool :=
  ⟨"notice/D023/paragraph/37/e/yo", notice "PDF399頁 D023(37)エ(ヨ)", fun (c, a) separate =>
    c.performance.item = false → a.performance.item = .local .pertussisAntigen →
    Performance.sameSeries { c.performance with item := .multiplexD023_25 }
      a.performance = some true → separate = false⟩

/-- 第25項の併施相手に対する部分仕様。通知(37)全体の適格性とは別に扱う。 -/
def PanelPertussisCombination (c : RespiratoryPanelContext) (antigen : D012.Context)
    (group : D012.Combined) (antigenSeparatelyBilled : Bool) : Prop :=
  c.evidence.tier = c.tier ∧ D023Schedule.respiratoryPanelFacility.holds c.evidence () ∧
  panelMethod.holds c () ∧ panelOutpatient.holds c () ∧
  antigen.performance.item = .local .pertussisAntigen ∧
  D012.pertussisIndication.holds antigen () ∧ antigen.combined = some group ∧
  group.Valid antigen.performance ∧
  let panel : Performance D012.RelatedTest := { c.performance with item := .multiplexD023_25 }
  group.Valid panel ∧ panel.sameSeries antigen.performance = some true ∧
  (∃ selected, group.selected = some selected ∧ panel.id ∈ selected ∧
    (antigenSeparatelyBilled = true ↔ antigen.performance.id ∈ selected)) ∧
  panelAntigenExclusionWithCovid.holds (c, antigen) antigenSeparatelyBilled ∧
  panelAntigenExclusionWithoutCovid.holds (c, antigen) antigenSeparatelyBilled

private def pertussisSample : PertussisContext :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩,
      .pertussis, none, some 1, none, none⟩
    method := .lamp, meetsGuidelineClinicalCase := some true
    explainedOnTestDay := true, suppliedWrittenResults := true }

example : PertussisEligible pertussisSample ∧ Satisfies pertussisRates pertussisSample (360, 100) := by
  constructor
  · simp [PertussisEligible, satisfies_cons, satisfies_nil, pertussisIndication,
      pertussisDualIndication, pertussisSample]
  · exact (pertussis_legacy_iff _ _).mpr rfl

example : ¬ PertussisEligible { pertussisSample with
    performance := { pertussisSample.performance with item := .pertussisAndParapertussis } } := by
  simp [PertussisEligible, satisfies_cons, satisfies_nil, pertussisIndication,
    pertussisDualIndication, pertussisSample]

inductive GenitalTestPurpose where
  | selectTreatment | assessTreatment
  deriving DecidableEq

/-- 第12項の二検査の通知。疑いと確定診断は診療上の確認事項。 -/
structure GenitalTestContext where
  realTimePcr : Option Bool := none
  suspectedTrichomoniasis : Option Bool := none
  microscopyNegativeOrUnavailable : Option Bool := none
  suspectedGenitalium : Option Bool := none
  trichomoniasisDiagnosed : Option Bool := none
  genitaliumDiagnosed : Option Bool := none
  purpose : Option GenitalTestPurpose := none

private def notice391 (id : String) : SourceRef :=
  notice ("PDF391頁 D023 " ++ id)

def genitalCombinedChoice : Rule GenitalTestContext Unit :=
  ⟨"notice/D023/paragraph/11/a", notice391 "(11)ア", fun c _ =>
    c.purpose = some .selectTreatment ∧
      ((c.suspectedTrichomoniasis = some true ∧ c.microscopyNegativeOrUnavailable = some true) ∨
        c.suspectedGenitalium = some true)⟩

def genitalCombinedFollowUp : Rule GenitalTestContext Unit :=
  ⟨"notice/D023/paragraph/11/i", notice391 "(11)イ", fun c _ =>
    c.purpose = some .assessTreatment ∧
      (c.trichomoniasisDiagnosed = some true ∨ c.genitaliumDiagnosed = some true)⟩

def genitalCombined : Rule GenitalTestContext Unit :=
  ⟨"notice/D023/paragraph/11", notice391 "(11)", fun c _ =>
    c.realTimePcr = some true ∧
      (genitalCombinedChoice.holds c () ∨ genitalCombinedFollowUp.holds c ())⟩

def genitalResistanceChoice : Rule GenitalTestContext Unit :=
  ⟨"notice/D023/paragraph/12/a", notice391 "(12)ア", fun c _ =>
    c.purpose = some .selectTreatment ∧ c.suspectedGenitalium = some true⟩

def genitalResistanceFollowUp : Rule GenitalTestContext Unit :=
  ⟨"notice/D023/paragraph/12/i", notice391 "(12)イ", fun c _ =>
    c.purpose = some .assessTreatment ∧ c.genitaliumDiagnosed = some true⟩

def genitalResistance : Rule GenitalTestContext Unit :=
  ⟨"notice/D023/paragraph/12", notice391 "(12)", fun c _ =>
    c.realTimePcr = some true ∧
      (genitalResistanceChoice.holds c () ∨ genitalResistanceFollowUp.holds c ())⟩

example : genitalCombined.holds
    { realTimePcr := some true, suspectedGenitalium := some true
      purpose := some .selectTreatment } () := by
  exact ⟨rfl, Or.inl ⟨rfl, Or.inr rfl⟩⟩

example : ¬ genitalCombined.holds
    { realTimePcr := some true, suspectedTrichomoniasis := some true
      purpose := some .selectTreatment } () := by
  simp [genitalCombined, genitalCombinedChoice, genitalCombinedFollowUp]

structure PneumoniaeContext where
  performance : Performance D012.RelatedTest
  diagnosisPurpose : Option Bool := none
  lamp : Option Bool := none
  combined : D012.Combined

def pneumoniaeMethod : Rule PneumoniaeContext Unit :=
  ⟨"notice/D023/paragraph/15/a", notice391 "(15)ア", fun c _ =>
    c.performance.item = .pneumoniaeD023_13 ∧ c.diagnosisPurpose = some true ∧
    c.lamp = some true⟩

def pneumoniaeAntibodies : List D012.RelatedTest :=
  [.local .pneumoniaeIgG, .local .pneumoniaeIgA, .local .pneumoniaeIgM]

def pneumoniaePartners : List D012.RelatedTest :=
  .multiplexD023_25 :: pneumoniaeAntibodies

def pneumoniaeChoice : Rule PneumoniaeContext Bool :=
  ⟨"notice/D023/paragraph/15/i", notice391 "(15)イ", fun c separatelyBilled =>
    c.combined.Valid c.performance ∧
    let partners := c.combined.members.filter fun q => decide (q.item ∈ pneumoniaePartners)
    (partners = [] → separatelyBilled = true) ∧
    (partners ≠ [] → ∃ ids, c.combined.selected = some ids ∧
      let selected := (c.performance :: partners).filter fun q => ids.contains q.id
      selected.length = 1 ∧ (separatelyBilled = true ↔ c.performance.id ∈ ids))⟩

def pneumoniae : Rule PneumoniaeContext Bool :=
  ⟨"notice/D023/paragraph/15", notice391 "(15)", fun c billed =>
    pneumoniaeMethod.holds c () ∧ pneumoniaeChoice.holds c billed⟩

/-- D012側の実施・併施群と、同じ算定対象IDを用いる。 -/
def PneumoniaeCombination (c : PneumoniaeContext) (antibody : D012.Context)
    (molecularBilled antibodyBilled : Bool) : Prop :=
  pneumoniae.holds c molecularBilled ∧
  antibody.performance.item ∈ pneumoniaeAntibodies ∧
  antibody.combined = some c.combined ∧ c.combined.Valid antibody.performance ∧
  (antibodyBilled = true → D012.pneumoniaeChoice.holds antibody ()) ∧
  ∃ ids, c.combined.selected = some ids ∧
    (antibodyBilled = true ↔ antibody.performance.id ∈ ids)

inductive HpvTest where
  | detection | simpleGenotype
  deriving DecidableEq

structure HpvContext where
  performance : Performance HpvTest
  evidence : D023Schedule.Evidence
  simultaneousCytology : Option Bool := none
  /-- 当該通知の併施範囲を確認した候補群の主検査。 -/
  combinedSelection : Option (Option HpvTest) := none

def hpvIndication : Rule HpvContext Unit :=
  ⟨"notice/D023/paragraph/10/a", notice "PDF390頁 D023(10)ア", fun c _ =>
    ((c.performance.item = .detection ∧ c.evidence.tier = .hpv) ∨
      (c.performance.item = .simpleGenotype ∧ c.evidence.tier = .hpvSimpleGenotype)) ∧
    (c.evidence.priorSpecifiedCervicalProcedure = some true ∨
      (c.evidence.priorSpecifiedCervicalProcedure = some false ∧ c.evidence.ascUs = some true ∧
        c.simultaneousCytology = some false))⟩

def hpvMain : Rule HpvContext Unit :=
  ⟨"notice/D023/paragraph/10/i", notice "PDF390–391頁 D023(10)イ", fun c _ =>
    c.combinedSelection = some none ∨ c.combinedSelection = some (some c.performance.item)⟩

def hpv : Rule HpvContext Unit :=
  ⟨"notice/D023/paragraph/10", notice "PDF390–391頁 D023(10)", fun c _ =>
    hpvIndication.holds c () ∧ hpvMain.holds c ()⟩

def HpvEligible (c : HpvContext) : Prop :=
  hpv.holds c () ∧ D023Schedule.hpvEligibility.holds c.evidence () ∧
    D023Schedule.hpvSimpleEligibility.holds c.evidence ()

inductive GenitalTest where
  | combined | resistance
  deriving DecidableEq

def genitalRules (test : GenitalTest) : Rule GenitalTestContext Unit :=
  match test with
  | .combined => genitalCombined
  | .resistance => genitalResistance

def GenitalTest.variant : GenitalTest → Nat
  | .combined => 0
  | .resistance => 1

theorem genital_legacy_iff (test : GenitalTest) (c : GenitalTestContext) (p : Nat) :
    (genitalRules test).holds c () ∧ Satisfies D023Schedule.rates .genitalCombination p ↔
      (genitalRules test).holds c () ∧ SpecimenTests.assessOne
        { code := .d023, number := 12, variant := test.variant } = some (.charged p 0) := by
  rw [D023Schedule.rates_iff]
  cases test <;>
    change (_ ∧ p = 350 ↔ _ ∧ some (SpecimenTests.ItemResult.charged 350 0) = some (.charged p 0)) <;>
    simp [eq_comm (a := p)]

inductive HcvTest where
  | detection | quantity
  deriving DecidableEq

inductive HcvMethod where
  | pcr | tma | branchedDnaProbe | tmaWithHybridization
  deriving DecidableEq

inductive HcvPurpose where
  | acuteDiagnosis | selectTreatment | monitorTreatment
  deriving DecidableEq

structure HcvContext where
  performance : Performance HcvTest
  method : Option HcvMethod := none
  purpose : Option HcvPurpose := none
  antibodyPositive : Option Bool := none
  quantitativeResultBelowDetectionLimit : Option Bool := none
  /-- some none は併施なし、some (some id) は併施群で選択した実施ID。 -/
  confirmedSelection : Option (Option Nat) := none

private def HcvSelection (c : HcvContext) : Prop :=
  c.confirmedSelection = some none ∨ c.confirmedSelection = some (some c.performance.id)

def hcvDetectionMethod : Rule HcvContext Unit :=
  ⟨"notice/D023/paragraph/9/a", notice "PDF390頁 D023(9)ア", fun c _ =>
    c.performance.item = .detection ∧ c.method ∈ [some .pcr, some .tma] ∧
    c.purpose ∈ [some .selectTreatment, some .monitorTreatment]⟩

def hcvDetectionIndication : Rule HcvContext Unit :=
  ⟨"notice/D023/paragraph/9/i", notice "PDF390頁 D023(9)イ", fun c _ =>
    (c.purpose = some .selectTreatment → c.antibodyPositive = some true ∧
      c.quantitativeResultBelowDetectionLimit = some true) ∧
    (c.purpose = some .monitorTreatment → HcvSelection c)⟩

def hcvDetection : Rule HcvContext Unit :=
  ⟨"notice/D023/paragraph/9", notice "PDF390頁 D023(9)", fun c _ =>
    hcvDetectionMethod.holds c () ∧ hcvDetectionIndication.holds c ()⟩

def hcvQuantityMethod : Rule HcvContext Unit :=
  ⟨"notice/D023/paragraph/19/a", notice "PDF392頁 D023(19)ア", fun c _ =>
    c.performance.item = .quantity ∧
    c.method ∈ [some .branchedDnaProbe, some .pcr, some .tmaWithHybridization] ∧
    c.purpose.isSome = true⟩

def hcvQuantityMain : Rule HcvContext Unit :=
  ⟨"notice/D023/paragraph/19/i", notice "PDF392頁 D023(19)イ", fun c _ =>
    c.purpose = some .monitorTreatment → HcvSelection c⟩

def hcvQuantity : Rule HcvContext Unit :=
  ⟨"notice/D023/paragraph/19", notice "PDF392頁 D023(19)", fun c _ =>
    hcvQuantityMethod.holds c () ∧ hcvQuantityMain.holds c ()⟩

/-- 通知(9)イと(19)イの併施に同じ主検査選択を用いる。
併施対象であることは実施群の確認を受ける。 -/
def HcvMonitoringPair (detection quantity : HcvContext) (selected : Nat) : Prop :=
  detection.performance.item = .detection ∧ quantity.performance.item = .quantity ∧
  detection.performance.id ≠ quantity.performance.id ∧
  detection.performance.site.patient = quantity.performance.site.patient ∧
  detection.performance.site.institution = quantity.performance.site.institution ∧
  detection.purpose = some .monitorTreatment ∧ quantity.purpose = some .monitorTreatment ∧
  detection.confirmedSelection = some (some selected) ∧
  quantity.confirmedSelection = some (some selected) ∧
  (hcvDetection.holds detection () ∨ hcvQuantity.holds quantity ())

theorem hcv_monitoring_exclusive (detection quantity : HcvContext) (selected : Nat)
    (pair : HcvMonitoringPair detection quantity selected) :
    ¬ (hcvDetection.holds detection () ∧ hcvQuantity.holds quantity ()) := by
  rintro ⟨hd, hq⟩
  obtain ⟨_, _, different, _, _, dp, qp, ds, qs, _⟩ := pair
  have hd' := hd.2.2 dp
  have hq' := hq.2 qp
  simp [HcvSelection, ds] at hd'
  simp [HcvSelection, qs] at hq'
  exact different (hd'.symm.trans hq')

structure PanelFilingEvidence where
  site : Site
  includesCovid : Bool
  facilityComplies : Option Bool := none
  priorFeeFilingAtEndOfMay : Option Bool := none
  filingEffectiveOnTestDay : Option Bool := none

private def filingQuestionSource : SourceRef :=
  ⟨.clarification, "疑義解釈資料の送付について（その8）", "2026-06-17",
    "PDF6–7頁 別添1 医科 問10", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001712853.pdf"⟩

/-- 6・7月に限る届出未受理の取扱い。8月以降の有効な届出は確認入力に残す。 -/
def panelFilingQuestion : Rule PanelFilingEvidence Unit :=
  ⟨"clarification/r08-08/question/10", filingQuestionSource, fun c _ =>
    c.facilityComplies = some true ∧
    (c.filingEffectiveOnTestDay = some true ∨
      (c.includesCovid = true ∧ c.site.date.year = 2026 ∧
        c.site.date.month.index.val ∈ [5, 6]) ∨
      (c.includesCovid = false ∧ c.priorFeeFilingAtEndOfMay = some true ∧
        (2026 * 12 + 5 ≤ c.site.date.year * 12 + c.site.date.month.index.val)))⟩

inductive HtlvPatient where
  | pregnant | transplantRecipient | organDonor
  deriving DecidableEq

structure HtlvContext where
  performance : Performance Unit
  antibodyTest : D012.Context
  antibodyIndeterminateConfirmedOn : Option Date := none
  patientGroup : Option HtlvPatient := none
  specifiedLivingDonorTransplant : Option Bool := none

private def notice393 (id : String) : SourceRef := notice ("PDF393頁 D023 " ++ id)

def htlv : Rule HtlvContext Unit :=
  ⟨"notice/D023/paragraph/24", notice393 "(24)", fun c _ =>
    c.antibodyTest.performance.item = .local .htlvBlot ∧
    D012.htlvConfirmation.holds c.antibodyTest () ∧
    c.antibodyTest.performance.site.patient = c.performance.site.patient ∧
    (∃ day, c.antibodyIndeterminateConfirmedOn = some day ∧
      c.antibodyTest.performance.site.date.key ≤ day.key ∧ day.key ≤ c.performance.site.date.key) ∧
    (c.patientGroup = some .pregnant ∨
      (c.patientGroup ∈ [some .transplantRecipient, some .organDonor] ∧
        c.specifiedLivingDonorTransplant = some true))⟩

def htlvDocumentation : Rule HtlvContext (Option Date) :=
  ⟨"notice/D023/paragraph/24", notice393 "(24) 摘要", fun c recorded =>
    ∃ day, c.antibodyIndeterminateConfirmedOn = some day ∧ recorded = some day⟩

structure HerpesQuantityContext where
  performance : Performance Unit
  immunodeficient : Option Bool := none
  stronglySuspectedHerpesOrVaricella : Option Bool := none
  realTimePcr : Option Bool := none
  seriesScope : Scope
  claims : ClaimHistory Nat

def HerpesQuantityContext.withinSeriesLimit (c : HerpesQuantityContext) : Option Bool := do
  let series ← c.performance.series
  if c.seriesScope.institution = some c.performance.site.institution ∧
      c.seriesScope.Includes c.performance.site = true then
    withinLimit c.claims c.seriesScope (· == series) 0
  else none

def herpesQuantity : Rule HerpesQuantityContext Unit :=
  ⟨"notice/D023/paragraph/25", notice393 "(25)", fun c _ =>
    c.immunodeficient = some true ∧ c.stronglySuspectedHerpesOrVaricella = some true ∧
    c.realTimePcr = some true ∧ c.withinSeriesLimit = some true⟩

inductive CmvIndication where
  | transplant | hiv | severeCellularImmunodeficiency | symptomaticCongenital
  deriving DecidableEq

inductive CmvPurpose where
  | diagnosis | assessTreatment
  deriving DecidableEq

structure CmvQuantityContext where
  detectedDnaInBloodByRealTimePcr : Option Bool := none
  indication : Option CmvIndication := none
  purpose : Option CmvPurpose := none

def cmvQuantityAdultRoute : Rule CmvQuantityContext Unit :=
  ⟨"notice/D023/paragraph/26/a", notice393 "(26)ア", fun c _ =>
    c.indication ∈ [some .transplant, some .hiv, some .severeCellularImmunodeficiency] ∧
    c.purpose ∈ [some .diagnosis, some .assessTreatment]⟩

def cmvQuantityCongenitalRoute : Rule CmvQuantityContext Unit :=
  ⟨"notice/D023/paragraph/26/i", notice393 "(26)イ", fun c _ =>
    c.indication = some .symptomaticCongenital ∧ c.purpose = some .assessTreatment⟩

def cmvQuantity : Rule CmvQuantityContext Unit :=
  ⟨"notice/D023/paragraph/26", notice393 "(26)", fun c _ =>
    c.detectedDnaInBloodByRealTimePcr = some true ∧
    (cmvQuantityAdultRoute.holds c () ∨ cmvQuantityCongenitalRoute.holds c ())⟩

def cmvQuantityDocumentation : Rule CmvQuantityContext Bool :=
  ⟨"notice/D023/paragraph/26/a", notice393 "(26)ア 摘要", fun c documented =>
    c.indication = some .severeCellularImmunodeficiency → documented = true⟩

inductive MycobacterialMethod where
  | amplificationWithLiquidHybridization | lcrWithEia | lamp
  | amplificationWithCapillaryElectrophoresis | microplateHybridization
  deriving DecidableEq

def tuberculosisMethod : Rule (Option MycobacterialMethod) Unit :=
  ⟨"notice/D023/paragraph/17", notice "PDF391–392頁 D023(17) 外来の方法", fun method _ =>
    method ∈ [some .amplificationWithLiquidHybridization, some .lcrWithEia, some .lamp,
      some .amplificationWithCapillaryElectrophoresis]⟩

def mycobacterialIdentificationMethod : Rule (Option MycobacterialMethod) Unit :=
  ⟨"notice/D023/paragraph/18/a", notice "PDF392頁 D023(18)ア", fun method _ =>
    method = some .microplateHybridization⟩

def mycobacterialIdentification : Rule (Option MycobacterialMethod) Unit :=
  ⟨"notice/D023/paragraph/18", notice "PDF392頁 D023(18) 外来の方法",
    mycobacterialIdentificationMethod.holds⟩

inductive HivQuantityMethod where
  | pcrWithHybridization | tmaWithHybridization
  deriving DecidableEq

structure HivQuantityContext where
  performance : Performance Unit
  method : Option HivQuantityMethod := none
  monitoringConfirmedHiv : Option Bool := none
  forConfirmingDiagnosis : Option Bool := none
  positiveScreen : Option (Performance D012.RelatedTest) := none

def hivQuantityIndication : Rule HivQuantityContext Unit :=
  ⟨"notice/D023/paragraph/27/a", notice393 "(27)ア", fun c _ =>
    c.method.isSome = true ∧
    (c.monitoringConfirmedHiv = some true ∨
      (c.forConfirmingDiagnosis = some true ∧ ∃ screen, c.positiveScreen = some screen ∧
        screen.item ∈ [D012.RelatedTest.local .hiv12Qual, .local .hiv12Semi, .local .hiv12ComboQual,
          .local .hiv1Antibody, .local .hiv12Quant, .local .hiv12ComboQuant] ∧
        screen.site.patient = c.performance.site.patient ∧
        screen.site.date.key ≤ c.performance.site.date.key))⟩

/-- 同じ併施群で確認した二件について、それぞれの適格性を保つ。 -/
def hivQuantityAndAntibody : Rule (HivQuantityContext × D012.Context) (Bool × Bool) :=
  ⟨"notice/D023/paragraph/27/i", notice393 "(27)イ", fun (c, antibody) requested =>
    requested = (true, true) → hivQuantityIndication.holds c () ∧
      antibody.performance.item = .local .hiv1WesternBlot ∧
      D012.hivWesternBlot.holds antibody () ∧
      antibody.performance.site.patient = c.performance.site.patient ∧
      antibody.performance.site.institution = c.performance.site.institution⟩

def hivQuantity : Rule HivQuantityContext Unit :=
  ⟨"notice/D023/paragraph/27", notice393 "(27) 個別算定", hivQuantityIndication.holds⟩

inductive CovidTest where
  | single | influenza | rs | influenzaRs
  deriving DecidableEq, Repr

inductive CovidCompanion where
  | covid (test : CovidTest)
  | influenzaNucleicAcid | panelWithCovid | panelWithoutCovid
  | antigen (item : D012.Item)
  deriving DecidableEq

structure CovidContext where
  performance : Performance CovidTest
  suspected : Option Bool := none
  diagnosisPurpose : Option Bool := none
  previousTestNegative : Option Bool := none
  noAlternativeDiagnosis : Option Bool := none
  outsourced : Option Bool := none
  confirmedTransportCompliance : Option Bool := none
  diagnosticScope : Scope
  claims : ClaimHistory (CovidTest × Nat)
  /-- 併施範囲内の別算定を照合した結果。 -/
  separatelyBilled : Option (List CovidCompanion) := none

def CovidContext.prior (c : CovidContext) : Option Nat := do
  let series ← c.performance.series
  if c.diagnosticScope.institution = some c.performance.site.institution ∧
      c.diagnosticScope.Includes c.performance.site = true then
    count c.claims c.diagnosticScope (· == (c.performance.item, series))
  else none

private def CovidIndication (c : CovidContext) : Prop :=
  c.suspected = some true ∧ c.diagnosisPurpose = some true ∧
    (c.prior = some 0 ∨
      (c.prior = some 1 ∧ c.previousTestNegative = some true ∧
        c.noAlternativeDiagnosis = some true)) ∧
    (c.outsourced = some false ∨
      (c.outsourced = some true ∧ c.confirmedTransportCompliance = some true))

private def CovidExcludes (c : CovidContext) (excluded : List CovidCompanion) : Prop :=
  ∃ billed, c.separatelyBilled = some billed ∧ ∀ test ∈ billed, test ∉ excluded

private def covidRule (paragraph page branch : String) (test : CovidTest)
    (p : CovidContext → Prop) : Rule CovidContext Unit :=
  ⟨"notice/D023/paragraph/" ++ paragraph ++ branch, notice ("PDF" ++ page ++ "頁 D023(" ++ paragraph ++ ")"),
    fun c _ => c.performance.item = test → p c⟩

def covidSingleIndication := covidRule "28" "393" "/a" .single CovidIndication
def covidSingleExclusions := covidRule "28" "393–394" "/i" .single fun c =>
  CovidExcludes c [.covid .influenza, .covid .rs, .covid .influenzaRs, .panelWithCovid]
def covidSingle := covidRule "28" "393–394" "" .single fun c =>
  covidSingleIndication.holds c () ∧ covidSingleExclusions.holds c ()

def covidInfluenzaIndication := covidRule "29" "394" "/a" .influenza CovidIndication
def covidInfluenzaExclusions := covidRule "29" "394" "/i" .influenza fun c =>
  CovidExcludes c [.antigen .influenzaAntigen, .influenzaNucleicAcid,
    .covid .single, .covid .rs, .covid .influenzaRs, .panelWithCovid, .panelWithoutCovid]
def covidInfluenza := covidRule "29" "394" "" .influenza fun c =>
  covidInfluenzaIndication.holds c () ∧ covidInfluenzaExclusions.holds c ()

def covidRsIndication := covidRule "30" "394" "/a" .rs CovidIndication
def covidRsExclusions := covidRule "30" "394" "/i" .rs fun c =>
  CovidExcludes c [.antigen .rsAntigen, .covid .single, .covid .influenza, .covid .influenzaRs,
    .panelWithCovid, .panelWithoutCovid]
def covidRs := covidRule "30" "394" "" .rs fun c =>
  covidRsIndication.holds c () ∧ covidRsExclusions.holds c ()

def covidInfluenzaRsIndication := covidRule "31" "394" "/a" .influenzaRs CovidIndication
def covidInfluenzaRsExclusions := covidRule "31" "395" "/i" .influenzaRs fun c =>
  CovidExcludes c [.antigen .influenzaAntigen, .antigen .rsAntigen, .influenzaNucleicAcid,
    .covid .single, .covid .influenza, .covid .rs, .panelWithCovid, .panelWithoutCovid]
def covidInfluenzaRs := covidRule "31" "394–395" "" .influenzaRs fun c =>
  covidInfluenzaRsIndication.holds c () ∧ covidInfluenzaRsExclusions.holds c ()

private def covidRepeatDocumentation (paragraph page : String) (test : CovidTest) :
    Rule CovidContext Bool :=
  ⟨"notice/D023/paragraph/" ++ paragraph ++ "/a",
    notice ("PDF" ++ page ++ "頁 D023(" ++ paragraph ++ ")ア 摘要"), fun c documented =>
      c.performance.item = test → c.prior = some 1 → documented = true⟩

def covidSingleDocumentation := covidRepeatDocumentation "28" "393" .single
def covidInfluenzaDocumentation := covidRepeatDocumentation "29" "394" .influenza
def covidRsDocumentation := covidRepeatDocumentation "30" "394" .rs
def covidInfluenzaRsDocumentation := covidRepeatDocumentation "31" "394" .influenzaRs

inductive HepatitisBPresentation where
  | acute | chronic
  deriving DecidableEq

structure HbvVariantContext where
  performance : Performance Unit
  presentation : Option HepatitisBPresentation := none
  pcr : Option Bool := none
  suspectedFulminantHepatitis : Option Bool := none
  suspectedWorseningDuringFollowUp : Option Bool := none
  forSelectingAntiviralTreatment : Option Bool := none
  /-- 第17項の当該検査だけを照合した患者通算の履歴。 -/
  history : ClaimHistory Unit

def hbvAcute : Rule HbvVariantContext Unit :=
  ⟨"notice/D023/paragraph/21/i", notice "PDF392頁 D023(21)イ", fun c _ =>
    c.presentation = some .acute ∧ c.suspectedFulminantHepatitis = some true ∧
    withinLimit c.history ⟨c.performance.site.patient, none, Period.through c.performance.site.date⟩
      (fun _ => true) 0 = some true⟩

def hbvChronic : Rule HbvVariantContext Unit :=
  ⟨"notice/D023/paragraph/21/u", notice "PDF392頁 D023(21)ウ", fun c _ =>
    c.presentation = some .chronic ∧ c.suspectedWorseningDuringFollowUp = some true ∧
    c.forSelectingAntiviralTreatment = some true⟩

def hbvMethod : Rule HbvVariantContext Unit :=
  ⟨"notice/D023/paragraph/21/a", notice "PDF392頁 D023(21)ア", fun c _ =>
    c.pcr = some true ∧ (hbvAcute.holds c () ∨ hbvChronic.holds c ())⟩

def hbvVariant : Rule HbvVariantContext Unit :=
  ⟨"notice/D023/paragraph/21", notice "PDF392頁 D023(21)", hbvMethod.holds⟩

structure HbvRelatedTest where
  molecular : HbvVariantContext
  serology : D013.Context
  /-- 同日の順序を含む、基準となる実施以降かの照合結果。 -/
  atOrAfterMolecular : Option Bool := none
  toAssessAntiviralEffect : Option Bool := none

def hbvLaterTesting : Rule HbvRelatedTest Bool :=
  ⟨"notice/D023/paragraph/21/u", notice "PDF392頁 D023(21)ウ D013", fun c billed =>
    hbvMethod.holds c.molecular () → hbvChronic.holds c.molecular () →
    c.serology.performance.site.patient = c.molecular.performance.site.patient →
    c.serology.performance.item ∈
      [D013.Item.hbsAntigenSimple, .hbsAntibodyQual, .hbsAntibodySemi, .hbsAntigen, .hbsAntibody,
        .hbeAntigen, .hbeAntibody, .hbcAntibody, .hbcIgM, .hbcrAntigen, .hbvGenotype] →
    billed = true → c.atOrAfterMolecular = some false ∨ c.toAssessAntiviralEffect = some true⟩

inductive SarsSpecimen where
  | stool | nasopharyngealSwab | other
  deriving DecidableEq

structure SarsContext where
  performance : Performance Unit
  lamp : Option Bool := none
  specimen : Option SarsSpecimen := none
  stronglySuspectedUnderReportingCriteria : Option Bool := none
  awaitingConfirmedDiagnosis : Option Bool := none
  noOtherDiagnosisWithinTenDays : Option Bool := none
  diagnosticScope : Scope
  claims : ClaimHistory Nat

def SarsContext.prior (c : SarsContext) : Option Nat := do
  let episode ← c.performance.series
  if c.diagnosticScope.institution = some c.performance.site.institution ∧
      c.diagnosticScope.Includes c.performance.site = true then
    count c.claims c.diagnosticScope (· == episode)
  else none

private def notice392 (id : String) : SourceRef := notice ("PDF392頁 D023 " ++ id)

def sarsMethod : Rule SarsContext Unit :=
  ⟨"notice/D023/paragraph/23/a", notice392 "(23)ア", fun c _ => c.lamp = some true⟩

def sarsSample : Rule SarsContext Unit :=
  ⟨"notice/D023/paragraph/23/i", notice392 "(23)イ", fun c _ =>
    c.specimen ∈ [some .stool, some .nasopharyngealSwab]⟩

def sarsIndication : Rule SarsContext Unit :=
  ⟨"notice/D023/paragraph/23/u", notice392 "(23)ウ", fun c _ =>
    c.stronglySuspectedUnderReportingCriteria = some true ∧
    c.awaitingConfirmedDiagnosis = some true ∧
    (c.prior = some 0 ∨ (c.prior = some 1 ∧ c.noOtherDiagnosisWithinTenDays = some true))⟩

def sars : Rule SarsContext Unit :=
  ⟨"notice/D023/paragraph/23", notice392 "(23)", fun c _ =>
    sarsMethod.holds c () ∧ sarsSample.holds c () ∧ sarsIndication.holds c ()⟩

inductive EbvPurpose where
  | diagnosis | monitor | determineEbvStatus | assessTreatment
  deriving DecidableEq

inductive EbvLimit where
  | weekly | monthly | quarterly | diagnosisOnce | treatmentOnce
  deriving DecidableEq, Repr

structure EbvWindow where
  /-- 当該通知の起算日・端点を照合した算定対象期間。 -/
  scope : Scope
  limit : EbvLimit

structure EbvContext where
  performance : Performance Unit
  realTimePcr : Option Bool := none
  organTransplant : Option Bool := none
  hematopoieticTransplant : Option Bool := none
  hlaMismatch : Option Bool := none
  atgForTransplant : Option Bool := none
  atgForAcuteRejectionOrGvhd : Option Bool := none
  highEbvDuringFirstYearAfterTransplant : Option Bool := none
  suspectedOrConfirmedPtld : Option Bool := none
  lymphomaOrLeukemia : Option Bool := none
  ebvPositive : Option Bool := none
  aplasticAnemiaTreatedWithAtg : Option Bool := none
  suspectedOrConfirmedChronicActiveEbv : Option Bool := none
  suspectedOrConfirmedNasopharyngealCancer : Option Bool := none
  purpose : Option EbvPurpose := none
  /-- 経過した段階と頻度の照会窓を、各起算事由ごとに確認して入力する。 -/
  transplantThroughThreeMonths : Option EbvWindow := none
  transplantAfterThreeThroughTwelveMonths : Option EbvWindow := none
  transplantAfterTwelveMonths : Option EbvWindow := none
  atgThroughTwoMonths : Option EbvWindow := none
  atgAfterTwoThroughSixMonths : Option EbvWindow := none
  ptldThroughOneMonth : Option EbvWindow := none
  ptldAfterOneThroughSixMonths : Option EbvWindow := none
  lymphomaThroughTwelveMonths : Option EbvWindow := none
  chronicEbvMonthly : Option EbvWindow := none
  nasopharyngealCancer : Option EbvWindow := none
  /-- 一般枠の検査履歴と、上咽頭癌の診断・治療効果判定の回数を別に射影する。 -/
  claims : ClaimHistory Unit
  nasopharyngealClaims : ClaimHistory EbvPurpose
  combinedSelection : Option (Option Nat) := none

private def EbvWithin (c : EbvContext) (window : Option EbvWindow) (limit : EbvLimit) : Prop :=
  ∃ w, window = some w ∧ w.limit = limit ∧ w.scope.Includes c.performance.site = true ∧
    withinLimit c.claims w.scope (fun _ => true) 0 = some true

private def EbvAtg (c : EbvContext) : Prop :=
  EbvWithin c c.atgThroughTwoMonths .weekly ∨
    EbvWithin c c.atgAfterTwoThroughSixMonths .monthly

private def EbvTransplant (c : EbvContext) : Prop :=
  EbvWithin c c.transplantThroughThreeMonths .weekly ∨
    EbvWithin c c.transplantAfterThreeThroughTwelveMonths .monthly

private def ebvBranch (suffix page : String) (p : EbvContext → Prop) : Rule EbvContext Unit :=
  ⟨"notice/D023/paragraph/8/" ++ suffix, notice ("PDF" ++ page ++ "頁 D023(8) " ++ suffix),
    fun c _ => p c⟩

def ebvOrganTransplant := ebvBranch "a" "389–390" fun c =>
  c.organTransplant = some true ∧
    (EbvTransplant c ∨ (c.highEbvDuringFirstYearAfterTransplant = some true ∧
      EbvWithin c c.transplantAfterTwelveMonths .quarterly))

def ebvHematopoieticTransplant := ebvBranch "i" "390" fun c =>
  c.hematopoieticTransplant = some true ∧
    (c.hlaMismatch = some true ∨ c.atgForTransplant = some true) ∧ EbvTransplant c

def ebvAcuteRejection := ebvBranch "u" "390" fun c =>
  c.atgForAcuteRejectionOrGvhd = some true ∧ EbvAtg c

def ebvPtld := ebvBranch "e" "390" fun c =>
  c.suspectedOrConfirmedPtld = some true ∧
    (c.purpose = some .diagnosis ∨ (c.purpose = some .monitor ∧
      (EbvWithin c c.ptldThroughOneMonth .weekly ∨ EbvWithin c c.ptldAfterOneThroughSixMonths .monthly)))

def ebvLymphoma := ebvBranch "o" "390" fun c =>
  c.lymphomaOrLeukemia = some true ∧
    (c.purpose = some .determineEbvStatus ∨
      (c.purpose = some .monitor ∧ c.ebvPositive = some true ∧
        EbvWithin c c.lymphomaThroughTwelveMonths .monthly))

def ebvAplasticAnemia := ebvBranch "ka" "390" fun c =>
  c.aplasticAnemiaTreatedWithAtg = some true ∧ EbvAtg c

def ebvChronicActive := ebvBranch "ki" "390" fun c =>
  c.suspectedOrConfirmedChronicActiveEbv = some true ∧
    c.purpose ∈ [some .diagnosis, some .monitor] ∧ EbvWithin c c.chronicEbvMonthly .monthly

def ebvNasopharyngeal := ebvBranch "ku" "390" fun c =>
  c.suspectedOrConfirmedNasopharyngealCancer = some true ∧
    (∃ w purpose limit, c.nasopharyngealCancer = some w ∧ c.purpose = some purpose ∧
      ((purpose = .diagnosis ∧ limit = .diagnosisOnce) ∨
        (purpose = .assessTreatment ∧ limit = .treatmentOnce)) ∧
      w.limit = limit ∧ w.scope.Includes c.performance.site = true ∧
      withinLimit c.nasopharyngealClaims w.scope (· == purpose) 0 = some true) ∧
    (c.combinedSelection = some none ∨ c.combinedSelection = some (some c.performance.id))

def ebvQuantity : Rule EbvContext Unit :=
  ⟨"notice/D023/paragraph/8", notice "PDF389–390頁 D023(8)", fun c _ =>
    c.realTimePcr = some true ∧
    (ebvOrganTransplant.holds c () ∨ ebvHematopoieticTransplant.holds c () ∨
      ebvAcuteRejection.holds c () ∨ ebvPtld.holds c () ∨ ebvLymphoma.holds c () ∨
      ebvAplasticAnemia.holds c () ∨ ebvChronicActive.holds c () ∨ ebvNasopharyngeal.holds c ())⟩

def EbvNasopharyngealCombination (c : EbvContext) (antibody : D012.Context)
    (combined : D012.Combined) (antibodyBilled : Bool) : Prop :=
  c.realTimePcr = some true ∧ ebvNasopharyngeal.holds c () ∧
  antibody.performance.item ∈
    [D012.RelatedTest.local .viralTiter, .local .classSpecificTiter] ∧
  antibody.target = some .eb ∧ antibody.combined = some combined ∧ combined.Valid antibody.performance ∧
  c.performance.site.patient = antibody.performance.site.patient ∧
  c.performance.site.institution = antibody.performance.site.institution ∧
  c.performance.id ≠ antibody.performance.id ∧
  c.combinedSelection = some (some c.performance.id) ∧
  ∃ ids, combined.selected = some ids ∧ c.performance.id ∈ ids ∧
    antibody.performance.id ∉ ids ∧ antibodyBilled = false

end Sanri.MedicalFee.D023
