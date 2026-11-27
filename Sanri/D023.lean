import Sanri.D023Other
import Sanri.D023References

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
    (Performance.simultaneousWith { c.performance with item := .multiplexD023_25 } a.performance =
      some true ∨ Performance.sameSeries { c.performance with item := .multiplexD023_25 }
        a.performance = some true) → separate = false⟩

def panelAntigenExclusionWithoutCovid : Rule (RespiratoryPanelContext × D012.Context) Bool :=
  ⟨"notice/D023/paragraph/37/e/yo", notice "PDF399頁 D023(37)エ(ヨ)", fun (c, a) separate =>
    c.performance.item = false → a.performance.item = .local .pertussisAntigen →
    (Performance.simultaneousWith { c.performance with item := .multiplexD023_25 } a.performance =
      some true ∨ Performance.sameSeries { c.performance with item := .multiplexD023_25 }
        a.performance = some true) → separate = false⟩

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

end Sanri.MedicalFee.D023
