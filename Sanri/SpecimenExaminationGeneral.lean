import Sanri.SpecimenOutpatientDay

namespace Sanri.MedicalFee.SpecimenExaminationGeneral

open Sanri.History Sanri.Logic

private def primary (locator : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF173頁 " ++ locator, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (locator : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", locator,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

structure Charges where
  ordinary : Nat
  drugs : Examinations.Drugs
  designatedMaterials : List Nat

structure Components where
  withDrug : Nat
  withMaterials : Nat

def drugAddition : Rule Charges Components :=
  ⟨"primary/ch2-part3/general/2", primary "第3部通則2", fun c r =>
    r.withDrug = c.ordinary + c.drugs.points⟩

def materialAddition : Rule Charges Components :=
  ⟨"primary/ch2-part3/general/3", primary "第3部通則3", fun c r =>
    r.withMaterials = r.withDrug + c.designatedMaterials.sum⟩

def chargeRules := [drugAddition, materialAddition]

theorem charges_determine (c : Charges) : DeterminesAt chargeRules c := by
  let subtotal := c.ordinary + c.drugs.points
  refine ⟨⟨⟨subtotal, subtotal + c.designatedMaterials.sum⟩, by
    simp [chargeRules, satisfies_cons, satisfies_nil, drugAddition, materialAddition, subtotal]⟩, ?_⟩
  intro a b ha hb
  cases a
  cases b
  simp [chargeRules, satisfies_cons, satisfies_nil, drugAddition, materialAddition] at *
  grind

structure Anesthesia where
  performed : Bool
  techniqueChargeable : Bool
  resolvedTechniquePoints : Option Nat
  resolvedSection5DrugPoints : Option Nat

def anesthesia : Rule Anesthesia (Nat × Nat) :=
  ⟨"notice/ch2-part3/general/7", notice "PDF327頁 第3部通則7",
    fun c (technique, drugs) => c.performed = true →
      (c.techniqueChargeable = true → c.resolvedTechniquePoints = some technique) ∧
      (c.techniqueChargeable = false → technique = 0 ∧ c.resolvedSection5DrugPoints = some drugs)⟩

structure Reference where
  specialUnlisted : Bool
  ministerialClosestExecution : Option Nat
  correspondingJudgment : Option Nat
  outsideDelegation : Bool
  outsourcingPoints : Option Nat

def closest : Rule Reference Nat :=
  ⟨"primary/ch2-part3/general/4", primary "第3部通則4",
    fun c points => c.specialUnlisted = true → c.ministerialClosestExecution = some points⟩

def closestNotice : Rule Reference (Nat × Nat) :=
  ⟨"notice/ch2-part3/general/5", notice "PDF327頁 第3部通則5",
    fun c (execution, judgment) => c.specialUnlisted = true →
      c.ministerialClosestExecution = some execution ∧ c.correspondingJudgment = some judgment⟩

structure Paired where
  concernsPairedOrgan : Bool
  scheduledPoints : Nat
  resolvedSpecialProvision : Option Nat

def paired : Rule Paired Nat :=
  ⟨"primary/ch2-part3/general/5", primary "第3部通則5",
    fun c p => c.concernsPairedOrgan = true →
      p = c.resolvedSpecialProvision.getD c.scheduledPoints⟩

def outsourcing : Rule Reference Nat :=
  ⟨"primary/ch2-part3/general/6", primary "第3部通則6",
    fun c p => c.outsideDelegation = true → c.outsourcingPoints = some p⟩

structure Remote where
  site : Site
  authorizedInstruction : Bool
  telemedicineWithNurseOrAssistantNurse : Bool
  performedByEligibleNurse : Bool
  /-- 第3・4節で該当する種類。当日の残りの対象実施を渡す。 -/
  kinds : List Nat
  previouslyClaimed : Option Bool

structure RemoteResult where
  ordinarySectionThreeAndFour : Nat
  replacement : Nat
  responsibleInstitution : Nat
  materialsSupplied : Bool

def Remote.Qualified (c : Remote) : Prop :=
  c.authorizedInstruction = true ∧ c.telemedicineWithNurseOrAssistantNurse = true ∧
  c.performedByEligibleNurse = true ∧ c.kinds ≠ []

def remoteRate : Rule Remote RemoteResult :=
  ⟨"primary/ch2-part3/general/7", primary "第3部通則7",
    fun c r => c.Qualified →
      r.ordinarySectionThreeAndFour = 0 ∧
      ((c.previouslyClaimed = some false ∧ c.kinds.eraseDups.length = 1 → r.replacement = 100) ∧
       (c.previouslyClaimed = some false ∧ 2 ≤ c.kinds.eraseDups.length → r.replacement = 150) ∧
       (c.previouslyClaimed = some true → r.replacement = 0))⟩

def remoteOneKind : Rule Remote RemoteResult :=
  ⟨"primary/ch2-part3/general/7/i", primary "第3部通則7イ",
    fun c r => c.Qualified → c.previouslyClaimed = some false →
      c.kinds.eraseDups.length = 1 → r.replacement = 100⟩

def remoteMultipleKinds : Rule Remote RemoteResult :=
  ⟨"primary/ch2-part3/general/7/ro", primary "第3部通則7ロ",
    fun c r => c.Qualified → c.previouslyClaimed = some false →
      2 ≤ c.kinds.eraseDups.length → r.replacement = 150⟩

def remoteNotice : Rule Remote RemoteResult :=
  ⟨"notice/ch2-part3/general/19", notice "PDF329頁 第3部通則19",
    fun c r => c.Qualified → r.responsibleInstitution = c.site.institution ∧ r.materialsSupplied = true⟩

def remoteDocumentation : Rule Remote (List Nat) :=
  ⟨"notice/ch2-part3/general/19", notice "PDF329頁 第3部通則19・摘要欄",
    fun c entry => c.Qualified → ∀ kind ∈ c.kinds, kind ∈ entry⟩

def remoteRules := [remoteRate, remoteNotice]

theorem remote_determine (c : Remote) (qualified : c.Qualified)
    (known : c.previouslyClaimed.isSome = true) : DeterminesAt remoteRules c := by
  have nonempty : 0 < c.kinds.eraseDups.length := by
    cases h : c.kinds with
    | nil => exact False.elim (qualified.2.2.2 h)
    | cons head tail =>
      have member : head ∈ (head :: tail).eraseDups := by simp
      exact List.length_pos_of_mem member
  obtain ⟨prior, hp⟩ := Option.isSome_iff_exists.mp known
  let points := if prior then 0 else if c.kinds.eraseDups.length = 1 then 100 else 150
  have holds : Satisfies remoteRules c ⟨0, points, c.site.institution, true⟩ := by
    cases prior <;>
      simp [remoteRules, satisfies_cons, satisfies_nil, remoteRate, remoteNotice, qualified,
        hp, points] <;> omega
  refine ⟨⟨_, holds⟩, ?_⟩
  intro a b ha hb
  cases a
  cases b
  simp [remoteRules, satisfies_cons, satisfies_nil, remoteRate, remoteNotice, qualified, hp] at *
  cases prior <;> by_cases count : c.kinds.eraseDups.length = 1 <;> grind

/-- 検体検査の日次内訳から、第4節の所定点数を通則7の置換額に差し替える。
第3節との混合日は置換を共有するため、両節を含む上位の集計へ渡す。 -/
def withRemoteCollection (c : SpecimenOutpatientDay.Context) (remote : Remote)
    (result : RemoteResult) (_ : c.site = remote.site)
    (_ : remote.Qualified) (_ : Satisfies remoteRules remote result) :
    SpecimenOutpatientDay.Context :=
  { c with collections := [result.replacement] }

structure RelatedCosts where
  routinePersonnelAndSupplies : Nat
  prescribingDispensingOrInjection : Nat
  electronicMedia : Nat
  simpleUnlistedTest : Nat

def embeddedExpenses : Rule Unit RelatedCosts :=
  ⟨"notice/ch2-part3/general/1", notice "PDF325頁 第3部通則1",
    fun _ r => r.routinePersonnelAndSupplies = 0⟩

def noSeparateDrugHandling : Rule Unit RelatedCosts :=
  ⟨"notice/ch2-part3/general/2", notice "PDF325頁 第3部通則2",
    fun _ r => r.prescribingDispensingOrInjection = 0⟩

structure DrugApproval where
  administeredOrReagent : Bool
  approved : Bool
  establishedException : Bool

def approval : Rule DrugApproval Unit :=
  ⟨"notice/ch2-part3/general/2", notice "PDF325頁 第3部通則2・医薬品の承認",
    fun c _ => c.administeredOrReagent = true →
      c.approved = true ∨ c.establishedException = true⟩

def electronicMedia : Rule Unit RelatedCosts :=
  ⟨"notice/ch2-part3/general/3", notice "PDF325頁 第3部通則3",
    fun _ r => r.electronicMedia = 0⟩

def simpleUnlisted : Rule Unit RelatedCosts :=
  ⟨"notice/ch2-part3/general/4", notice "PDF325–327頁 第3部通則4",
    fun _ r => r.simpleUnlistedTest = 0⟩

/-- 基本診療料に含まれる例の識別子。生体検査の個別算定はここでは評価しない。 -/
inductive SimpleUnlistedExample where
  | bloodPressure | simpleVisualFieldAndFundus | simpleOphthalmology | simpleHearingOutsideD244Item3
  | semenPh | DavisCancerReaction | eardrumMovement | icterometerJaundice
  | simpleCirculatory | autonomicFunction | drinkingTestObservation | skinImpedance
  | ecgUnderSixLeads | urineBromvalerylurea | SawadaReaction | SchmidtMercuricChloride
  | StollEggCount | meningealPermeability | YokotaReaction | euglobulinTotalPlasmin
  | syphilisComplementFixation | ovalbuminHemagglutination | lactoalbuminHemagglutination | MillerKurzrok
  | Schick | Dick | Frei | Mitsuda
  | Matsubara | Ito | infectiousIntradermalTest | whealAbsorption
  | diazo | indican | bloodSpecificGravity | Brachet
  | Ribiere | niacin | rphaAfp | rheumatoidFactorScreen
  | alpha1AcidGlycoprotein | betaLipoprotein | monoamineOxidase | Widal
  | hcgBetaQualitative | antiDnaByAgglutinationOrStaining | wholeBloodClotLysis | serumTotalPlasmin
  | sludge | nailfoldCapillary | mucocutaneousImaging | coldBloodPressure
  | Bickenbach | histamine | Regitine | peripheralVenousPressure
  | cutaneousThermometry | GibbonLandis | simplifiedBasalMetabolism | cutaneousTemperatureResting
  | cutaneousTemperatureChallenge

def simpleExampleRule (item : SimpleUnlistedExample) : Rule SimpleUnlistedExample Nat :=
  let (path, page) := match item with
    | .bloodPressure => ("1", 325)
    | .simpleVisualFieldAndFundus => ("2", 325)
    | .simpleOphthalmology => ("3", 325)
    | .simpleHearingOutsideD244Item3 => ("4", 325)
    | .semenPh => ("5", 325)
    | .DavisCancerReaction => ("6", 325)
    | .eardrumMovement => ("7", 325)
    | .icterometerJaundice => ("8", 325)
    | .simpleCirculatory => ("9", 325)
    | .autonomicFunction => ("10", 326)
    | .drinkingTestObservation => ("11", 326)
    | .skinImpedance => ("12", 326)
    | .ecgUnderSixLeads => ("13", 326)
    | .urineBromvalerylurea => ("14", 326)
    | .SawadaReaction => ("15", 326)
    | .SchmidtMercuricChloride => ("16", 326)
    | .StollEggCount => ("17", 326)
    | .meningealPermeability => ("18", 326)
    | .YokotaReaction => ("19", 326)
    | .euglobulinTotalPlasmin => ("20", 326)
    | .syphilisComplementFixation => ("21", 326)
    | .ovalbuminHemagglutination => ("22", 326)
    | .lactoalbuminHemagglutination => ("23", 326)
    | .MillerKurzrok => ("24", 326)
    | .Schick => ("25", 326)
    | .Dick => ("26", 326)
    | .Frei => ("27", 326)
    | .Mitsuda => ("28", 326)
    | .Matsubara => ("29", 326)
    | .Ito => ("30", 326)
    | .infectiousIntradermalTest => ("31", 326)
    | .whealAbsorption => ("32", 326)
    | .diazo => ("33", 326)
    | .indican => ("34", 326)
    | .bloodSpecificGravity => ("35", 326)
    | .Brachet => ("36", 326)
    | .Ribiere => ("37", 326)
    | .niacin => ("38", 326)
    | .rphaAfp => ("39", 327)
    | .rheumatoidFactorScreen => ("40", 327)
    | .alpha1AcidGlycoprotein => ("41", 327)
    | .betaLipoprotein => ("42", 327)
    | .monoamineOxidase => ("43", 327)
    | .Widal => ("44", 327)
    | .hcgBetaQualitative => ("45", 327)
    | .antiDnaByAgglutinationOrStaining => ("46", 327)
    | .wholeBloodClotLysis => ("47", 327)
    | .serumTotalPlasmin => ("48", 327)
    | .sludge => ("9/a", 325)
    | .nailfoldCapillary => ("9/i", 325)
    | .mucocutaneousImaging => ("9/u", 325)
    | .coldBloodPressure => ("9/e", 325)
    | .Bickenbach => ("9/o", 325)
    | .histamine => ("9/ka", 326)
    | .Regitine => ("9/ki", 326)
    | .peripheralVenousPressure => ("9/ku", 326)
    | .cutaneousThermometry => ("9/ke", 326)
    | .GibbonLandis => ("9/ko", 326)
    | .simplifiedBasalMetabolism => ("9/sa", 326)
    | .cutaneousTemperatureResting => ("9/ke/a", 326)
    | .cutaneousTemperatureChallenge => ("9/ke/b", 326)
  ⟨"notice/ch2-part3/general/4/" ++ path,
    notice ("PDF" ++ toString page ++ "頁 第3部通則4・" ++ path),
    fun candidate points => candidate = item → points = 0⟩

structure ExamGrouping where
  conjunctiveComponentsComplete : Bool
  specialConjunctiveProvision : Bool
  /-- 同一検体の定性等、またはスクリーニングと一連の検査の組。
  同じ区分内の主たる検査を確認してから渡す。 -/
  mainInSameCode : Option Nat
  withinSameCodeGroup : Bool
  quantifiedFractionsOfSameSpecimen : Bool
  hasStatedQuantitation : Bool
  quantitativePerformed : Bool
  /-- 方法が指定されない検査の所定点数。 -/
  unspecifiedMethodScheduled : Option Nat
  derivedFromOtherSimultaneousOrSeriesTests : Bool
  reductionAfterFirst : Bool
  baseBeforeReduction : Nat
  notesBeforeReduction : Nat
  repeatedWithDifferentMethod : Bool
  preferredMethod : Option Nat

structure GroupResult where
  points : Nat
  scheduledForUnspecifiedMethod : Nat
  chargedUnits : Nat
  reductionBasis : Nat

def conjunctive : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/6", notice "PDF327頁 第3部通則6",
    fun c r => c.conjunctiveComponentsComplete = false → c.specialConjunctiveProvision = false →
      r.points = 0⟩

def mainTest : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/8", notice "PDF327頁 第3部通則8",
    fun c r => c.withinSameCodeGroup = true → c.mainInSameCode = some r.points⟩

def fractions : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/9", notice "PDF327頁 第3部通則9",
    fun c r => c.quantifiedFractionsOfSameSpecimen = true → r.chargedUnits ≤ 1⟩

def quantitative : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/10", notice "PDF327頁 第3部通則10",
    fun c r => c.hasStatedQuantitation = false → c.quantitativePerformed = false → r.points = 0⟩

def unspecifiedMethod : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/11", notice "PDF327頁 第3部通則11",
    fun c r => ∀ p, c.unspecifiedMethodScheduled = some p → r.scheduledForUnspecifiedMethod = p⟩

def derivedResult : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/12", notice "PDF327頁 第3部通則12",
    fun c r => c.derivedFromOtherSimultaneousOrSeriesTests = true → r.points = 0⟩

def reductionBase : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/13", notice "PDF327頁 第3部通則13",
    fun c r => c.reductionAfterFirst = true → r.reductionBasis = c.baseBeforeReduction + c.notesBeforeReduction⟩

def mainMethod : Rule ExamGrouping GroupResult :=
  ⟨"notice/ch2-part3/general/14", notice "PDF327頁 第3部通則14",
    fun c r => c.repeatedWithDifferentMethod = true → c.preferredMethod = some r.points⟩

inductive Remarks where
  | first | previous (date : Date)

def previousDate : Rule (Option Date × Bool) Remarks :=
  ⟨"notice/ch2-part3/general/15", notice "PDF327頁 第3部通則15",
    fun (prior, verified) entry => verified = true →
      match entry with
      | .first => prior = none
      | .previous date => prior = some date⟩

/-! 通知の測定法の同定。各検査の測定法要件は個別の規則で扱う。 -/
inductive MethodDesignation where
  | passiveHemagglutination | reversePassiveHemagglutination | latexAgglutination
  | latexPhotometricImmunoassay | particleCountingImmunoassay | particleMediatedImmunoassay
  | immuneAdherenceHemagglutination | radioimmunoassay | radioimmunosorbent
  | radioallergosorbent | radioassay | radioreceptorAssay
  | competitiveProteinBinding | enzymeImmunoassay | enzymeLinkedImmunosorbent
  | fluorescentAntibody | fluorescencePolarization | fluorescencePolarizationImmunoassay
  | timeResolvedFluorescenceImmunoassay | immunoradiometric | singleRadialImmunodiffusion
  | counterimmunoelectrophoresis | turbidimetricImmunoassay | highPerformanceLiquidChromatography
  | gasLiquidChromatography | gasChromatography | chemiluminescentImmunoassay
  | chemiluminescentEnzymeImmunoassay | electrochemiluminescentImmunoassay | splitImmunoassay
  | polymeraseChainReaction | reverseSequenceSpecificOligonucleotidePcr | evanescentWaveFluorescenceImmunoassay
  | fluorescenceImmunoassay | liquidPhaseBindingAssay | fluorescenceInSituHybridization
  | silverInSituHybridization | loopMediatedIsothermalAmplification | transcriptionMediatedAmplification
  | strandDisplacementAmplification | singleStrandConformationPolymorphism | restrictionFragmentLengthPolymorphism
  | ligaseChainReaction | histocultureDrugResponse | collagenDropletDrugSensitivity
  | transcriptionReverseTranscriptionConcerted

def MethodDesignation.abbreviation : MethodDesignation → String
  | .passiveHemagglutination => "PHA"
  | .reversePassiveHemagglutination => "RPHA"
  | .latexAgglutination => "LA"
  | .latexPhotometricImmunoassay => "LPIA"
  | .particleCountingImmunoassay => "PCIA"
  | .particleMediatedImmunoassay => "PAMIA"
  | .immuneAdherenceHemagglutination => "IAHA"
  | .radioimmunoassay => "RIA"
  | .radioimmunosorbent => "RIST"
  | .radioallergosorbent => "RAST"
  | .radioassay => "RA"
  | .radioreceptorAssay => "RRA"
  | .competitiveProteinBinding => "CPBA"
  | .enzymeImmunoassay => "EIA"
  | .enzymeLinkedImmunosorbent => "ELISA"
  | .fluorescentAntibody => "FA"
  | .fluorescencePolarization => "FPA"
  | .fluorescencePolarizationImmunoassay => "FPIA"
  | .timeResolvedFluorescenceImmunoassay => "TR-FIA"
  | .immunoradiometric => "IRMA"
  | .singleRadialImmunodiffusion => "SRID"
  | .counterimmunoelectrophoresis => "ES"
  | .turbidimetricImmunoassay => "TIA"
  | .highPerformanceLiquidChromatography => "HPLC"
  | .gasLiquidChromatography => "GLC"
  | .gasChromatography => "GC"
  | .chemiluminescentImmunoassay => "CLIA"
  | .chemiluminescentEnzymeImmunoassay => "CLEIA"
  | .electrochemiluminescentImmunoassay => "ECLIA"
  | .splitImmunoassay => "SIA"
  | .polymeraseChainReaction => "PCR"
  | .reverseSequenceSpecificOligonucleotidePcr => "PCR-rSSO"
  | .evanescentWaveFluorescenceImmunoassay => "EV-FIA"
  | .fluorescenceImmunoassay => "FIA"
  | .liquidPhaseBindingAssay => "LBA"
  | .fluorescenceInSituHybridization => "FISH"
  | .silverInSituHybridization => "SISH"
  | .loopMediatedIsothermalAmplification => "LAMP"
  | .transcriptionMediatedAmplification => "TMA"
  | .strandDisplacementAmplification => "SDA"
  | .singleStrandConformationPolymorphism => "SSCP"
  | .restrictionFragmentLengthPolymorphism => "RFLP"
  | .ligaseChainReaction => "LCR"
  | .histocultureDrugResponse => "HDRA"
  | .collagenDropletDrugSensitivity => "CD-DST"
  | .transcriptionReverseTranscriptionConcerted => "TRC"

def methodGlossary : Rule MethodDesignation String :=
  ⟨"notice/ch2-part3/general/16", notice "PDF327–329頁 第3部通則16",
    fun m label => label = m.abbreviation⟩

structure InstrumentLatex where
  antigenAntibodyAgglutination : Bool
  opticalInstrumentQuantitation : Bool

def instrumentLatex : Rule InstrumentLatex Bool :=
  ⟨"notice/ch2-part3/general/16", notice "PDF329頁 第3部通則16・LAの注",
    fun c applies => applies = (c.antigenAntibodyAgglutination && c.opticalInstrumentQuantitation)⟩

inductive Measurement where
  | qualitative | semiquantitative | quantitative
  deriving DecidableEq

structure MeasurementFacts where
  presence : Bool
  classifiedByRelativeLevel : Bool
  preciseByComparisonToStandard : Bool

def definition17 : Rule MeasurementFacts Measurement :=
  ⟨"notice/ch2-part3/general/17", notice "PDF329頁 第3部通則17",
    fun c m => match m with
    | .qualitative => c.presence = true
    | .semiquantitative => c.classifiedByRelativeLevel = true
    | .quantitative => c.preciseByComparisonToStandard = true⟩

end Sanri.MedicalFee.SpecimenExaminationGeneral
