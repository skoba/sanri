import Sanri.Logic
import Sanri.D007
import Sanri.BloodChemistry
import Sanri.BloodChemistryFurther
import Sanri.SpecimenJudgment
import Sanri.UrineFecalTests

namespace Sanri.MedicalFee.BloodChemistryLate

open Sanri.Logic

abbrev Item := D007.ScopedItem .late

def Item.points : Item → Nat
  | .typeIVCollagen | .myoglobinQualitative | .myoglobinQuantitative | .hFabpQualitative | .hFabpQuantitative => 131
  | .zinc => 132
  | .unboundBilirubin => 135
  | .procollagenIII | .ace | .vitaminB12 => 136
  | .selenium => 144
  | .folate => 146
  | .typeIVCollagen7S => 148
  | .pyruvateKinase => 150
  | .remnantLipoproteinCholesterol => 174
  | .igfbp1Qualitative => 175
  | .hyaluronicAcid => 179
  | .alpIsoenzymesPag | .acetaminophen => 180
  | .cardiacMyosinLightChainI => 184
  | .trypsin => 189
  | .mac2 | .mdaLdl | .autotaxin | .ck18f | .elfScore => 194
  | .phospholipaseA2 => 204
  | .erythrocyteCoproporphyrin => 210
  | .lipoproteinLipase => 219
  | .hgf => 227
  | .vitaminB2 => 231
  | .vitaminB1 => 239
  | .lrg => 268
  | .erythrocyteProtoporphyrin => 272
  | .procalcitoninQuantitative | .procalcitoninSemiquantitative => 276
  | .vitaminC => 296
  | .presepsin => 301
  | .infliximabQualitative => 310
  | .vitaminD125 => 388
  | .vegf | .cochlinTomoprotein => 460
  | .fgf23 => 788

inductive Method where
  | elisa | immunochromatography | latexTurbidimetry | latexAgglutination
  | immunoadsorptionEnzymatic | enzymatic
  | sandwichBindingProtein | competitiveI125BindingProtein | instrumentLatex | lba
  | twoStepSandwichCleia | sandwichFluorescenceEnzyme | cleia
  | oneStepSandwichEnzymeImmunoassay | chemiluminescentImmunoassay
  | radioreceptor | ria | other
  deriving DecidableEq, Repr

/-- 条項が指定する実施関係と、同じ関係について外部で確定した選択。 -/
inductive Principal where
  | separate | selected (item : Item) | external
  deriving DecidableEq, Repr

private def Principal.allows (item : Item) : Principal → Bool
  | .separate => true
  | .selected choice => item == choice
  | .external => false

private def allowed (value : Option Method) (methods : List Method) : Option Bool :=
  value.map methods.contains

/-- 適用できる経路のいずれかが確認済みであれば適用可能。 -/
private def either : Option Bool → Option Bool → Option Bool
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

private def both : Option Bool → Option Bool → Option Bool
  | some false, _ | _, some false => some false
  | some true, some true => some true
  | _, _ => none

inductive SeleniumRiskGroup where
  | longTermParenteralNutrition | longTermElementalEnteralNutrition
  | childUsingFormula | severeMotorAndIntellectualDisability | other
  deriving DecidableEq, Repr

inductive VitaminDIndication where
  | chronicRenalFailure | idiopathicHypoparathyroidism | pseudohypoparathyroidism
  | vitaminDDependentRicketsTypeI | hypophosphatemicVitaminDResistantRickets | other
  deriving DecidableEq, Repr

inductive VitaminDPhase where
  | diagnosis | firstTreatmentMonth | laterTreatment
  deriving DecidableEq, Repr

inductive FgfPhase where
  | diagnosis | afterTumorRemoval | afterSuspectDrugWithdrawal | otherTreatmentAssessment
  deriving DecidableEq, Repr

/-- 一つの外来実施を評価する。各併施欄は当該通知に列挙された相手群と
実施の関係を確認した結果であり、別検査を個別に評価する場合も同じ選択から射影する。 -/
structure Context where
  item : Item
  method : Option Method := none
  acuteInfarctionDiagnosis : Option Bool := none
  hFabpMyoglobinSelection : Option Principal := none
  collagenSelection : Option Principal := none
  kernicterusRisk : Option Bool := none
  neonatalFollowUp : Option Bool := none
  withinTwoWeeksOfBirth : Option Bool := none
  prematureWithinTermEquivalent : Option Bool := none
  correctedWeekRecorded : Option Bool := none
  seleniumRiskGroup : Option SeleniumRiskGroup := none
  seleniumDeficiencyDiagnosisOrFollowUp : Option Bool := none
  /-- 同一患者の暦に基づく算定間隔。 -/
  remnantThreeMonthInterval : Option Bool := none
  rupturedMembranesDiagnosis : Option Bool := none
  completedGestationalWeeks : Option Nat := none
  fibronectinSelection : Option Principal := none
  chronicHepatitis : Option Bool := none
  chronicHepatitisFollowUpAndBiopsyAssessment : Option Bool := none
  alpSelection : Option Principal := none
  /-- 同一患者の１月以内の測定のうち初回。 -/
  acetaminophenFirstMeasurement : Option Bool := none
  /-- 同一患者同一日の算定枠に選択された測定。 -/
  myosinDailySelection : Option Bool := none
  diabetes : Option Bool := none
  coronaryDiseaseHistory : Option Bool := none
  coronaryPrognosis : Option Bool := none
  mdaThreeMonthInterval : Option Bool := none
  preAngioplastyRestenosisPrognosis : Option Bool := none
  mdaFirstPreoperativeMeasurement : Option Bool := none
  chronicHepatitisOrCirrhosisIncludingSuspected : Option Bool := none
  hepaticFibrosisProgressionDiagnosis : Option Bool := none
  mac2Selection : Option Principal := none
  autotaxinSelection : Option Principal := none
  fattyLiverIncludingSuspected : Option Bool := none
  steatohepatitisDiagnosis : Option Bool := none
  ck18fSelection : Option Principal := none
  chronicLiverDiseaseIncludingSuspected : Option Bool := none
  hepaticFibrosisFollowUp : Option Bool := none
  elfComponentsMeasuredAndScoreCalculated : Option Bool := none
  elfSixMonthInterval : Option Bool := none
  /-- ELFの測定構成要素として行われたP-III-P又はヒアルロン酸。 -/
  includedInElf : Option Bool := none
  elfSelection : Option Principal := none
  hypertriglyceridemiaAndSuspectedLplDeficiency : Option Bool := none
  lplDifferentialDiagnosis : Option Bool := none
  suspectedFulminantHepatitisOrFollowUp : Option Bool := none
  inflammatoryBowelDiseaseAssessment : Option Bool := none
  lrgThreeMonthInterval : Option Bool := none
  lrgOneMonthInterval : Option Bool := none
  lrgMonthlyMedicalNecessity : Option Bool := none
  lrgReasonAndResultInChart : Option Bool := none
  lrgReasonAndResultInClaim : Option Bool := none
  /-- 同一暦月内のD003の9又はD313との選択。 -/
  lrgMonthlySelection : Option Principal := none
  suspectedBacterialSepsis : Option Bool := none
  endotoxinSelection : Option Principal := none
  presepsinSelection : Option Principal := none
  rheumatoidArthritis : Option Bool := none
  infliximabDoseDecision : Option Bool := none
  /-- 当該患者の既算定回数。 -/
  infliximabPriorClaims : Option Nat := none
  vitaminDIndication : Option VitaminDIndication := none
  vitaminDPhase : Option VitaminDPhase := none
  vitaminDFirstMonthPriorClaims : Option Nat := none
  vitaminDLaterThreeMonthInterval : Option Bool := none
  poemsDiagnosisOrFollowUp : Option Bool := none
  vegfPriorClaimsThisCalendarMonth : Option Nat := none
  suspectedPerilymphaticFistulaForDiagnosis : Option Bool := none
  middleEarLavage : Option Bool := none
  ctpGuidelineFollowed : Option Bool := none
  fgfListedDisease : Option Bool := none
  fgfPhase : Option FgfPhase := none
  /-- 診断枠、又は確認した腫瘍摘出・被疑薬中止後の評価枠に対応する既算定回数。 -/
  fgfPriorClaimsInPhase : Option Nat := none
  deriving DecidableEq, Repr

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

/-- 一つの条項が課す確認事項。併施制約の入力は、指定された組に該当しないか、
その組で当該検査が主たるものと確認した場合に真となる。 -/
private structure Clause where
  suffix : String
  location : String
  items : List Item
  checks : Context → List (Option Bool)

private def clauses : List Clause := [
  ⟨"27", "PDF358頁 D007(27) 本則", [.hFabpQualitative, .hFabpQuantitative],
    fun c => [allowed c.method [.elisa, .immunochromatography, .latexTurbidimetry, .latexAgglutination],
      c.acuteInfarctionDiagnosis]⟩,
  ⟨"27", "PDF358頁 D007(27) ただし書",
    [.hFabpQualitative, .hFabpQuantitative, .myoglobinQualitative, .myoglobinQuantitative],
    fun c => [c.hFabpMyoglobinSelection.map (Principal.allows c.item)]⟩,
  ⟨"30", "PDF358頁 D007(30)", [.typeIVCollagen, .typeIVCollagen7S, .procollagenIII, .mac2],
    fun c => [c.collagenSelection.map (Principal.allows c.item)]⟩,
  ⟨"31", "PDF358頁 D007(31)", [.unboundBilirubin], fun c =>
    [c.kernicterusRisk, c.neonatalFollowUp,
      c.withinTwoWeeksOfBirth.bind fun within =>
        if within then some true else
          c.prematureWithinTermEquivalent.bind fun premature =>
            if premature then c.correctedWeekRecorded else some false]⟩,
  ⟨"32", "PDF358頁 D007(32)", [.selenium], fun c =>
    [c.seleniumRiskGroup.map (· != .other), c.seleniumDeficiencyDiagnosisOrFollowUp]⟩,
  ⟨"33", "PDF358頁 D007(33)", [.remnantLipoproteinCholesterol], fun c =>
    [allowed c.method [.immunoadsorptionEnzymatic, .enzymatic], c.remnantThreeMonthInterval]⟩,
  ⟨"34/a", "PDF358頁 D007(34)ア", [.igfbp1Qualitative], fun c =>
    [allowed c.method [.immunochromatography], c.rupturedMembranesDiagnosis,
      c.completedGestationalWeeks.map fun weeks => 22 ≤ weeks && weeks < 37]⟩,
  ⟨"34/i", "PDF358頁 D007(34)イ", [.igfbp1Qualitative], fun c =>
    [c.fibronectinSelection.map (Principal.allows c.item)]⟩,
  ⟨"35", "PDF358〜359頁 D007(35)", [.hyaluronicAcid], fun c =>
    [allowed c.method [.sandwichBindingProtein, .competitiveI125BindingProtein, .instrumentLatex, .lba],
      c.chronicHepatitis, c.chronicHepatitisFollowUpAndBiopsyAssessment]⟩,
  ⟨"36", "PDF359頁 D007(36)", [.alpIsoenzymesPag], fun c =>
    [c.alpSelection.map (Principal.allows c.item)]⟩,
  ⟨"37", "PDF359頁 D007(37)", [.acetaminophen], fun c => [c.acetaminophenFirstMeasurement]⟩,
  ⟨"38", "PDF359頁 D007(38)", [.cardiacMyosinLightChainI], fun c => [c.myosinDailySelection]⟩,
  ⟨"39", "PDF359頁 D007(39)", [.mdaLdl], fun c =>
    [c.diabetes, either
      (both c.coronaryDiseaseHistory (both c.coronaryPrognosis c.mdaThreeMonthInterval))
      (both c.preAngioplastyRestenosisPrognosis c.mdaFirstPreoperativeMeasurement)]⟩,
  ⟨"40/a", "PDF359頁 D007(40)ア", [.mac2], fun c =>
    [allowed c.method [.twoStepSandwichCleia], c.chronicHepatitisOrCirrhosisIncludingSuspected,
      c.hepaticFibrosisProgressionDiagnosis]⟩,
  ⟨"40/i", "PDF359頁 D007(40)イ",
    [.mac2, .typeIVCollagen, .procollagenIII, .typeIVCollagen7S, .hyaluronicAcid], fun c =>
    [c.mac2Selection.map (Principal.allows c.item)]⟩,
  ⟨"41/a", "PDF359頁 D007(41)ア", [.autotaxin], fun c =>
    [allowed c.method [.sandwichFluorescenceEnzyme, .cleia, .enzymatic],
      c.chronicHepatitisOrCirrhosisIncludingSuspected, c.hepaticFibrosisProgressionDiagnosis]⟩,
  ⟨"41/i", "PDF359頁 D007(41)イ",
    [.autotaxin, .typeIVCollagen, .procollagenIII, .typeIVCollagen7S, .hyaluronicAcid, .mac2],
    fun c => [c.autotaxinSelection.map (Principal.allows c.item)]⟩,
  ⟨"42/a", "PDF359頁 D007(42)ア", [.ck18f], fun c =>
    [allowed c.method [.oneStepSandwichEnzymeImmunoassay],
      c.fattyLiverIncludingSuspected, c.steatohepatitisDiagnosis]⟩,
  ⟨"42/i", "PDF359頁 D007(42)イ",
    [.ck18f, .typeIVCollagen, .procollagenIII, .typeIVCollagen7S, .hyaluronicAcid, .mac2, .autotaxin],
    fun c => [c.ck18fSelection.map (Principal.allows c.item)]⟩,
  ⟨"43/a", "PDF359〜360頁 D007(43)ア", [.elfScore], fun c =>
    [allowed c.method [.chemiluminescentImmunoassay], c.chronicLiverDiseaseIncludingSuspected,
      either c.hepaticFibrosisProgressionDiagnosis c.hepaticFibrosisFollowUp,
      c.elfComponentsMeasuredAndScoreCalculated, c.elfSixMonthInterval]⟩,
  ⟨"43/i", "PDF360頁 D007(43)イ", [.procollagenIII, .hyaluronicAcid], fun c =>
    [c.includedInElf.map not]⟩,
  ⟨"43/u", "PDF360頁 D007(43)ウ",
    [.elfScore, .typeIVCollagen, .typeIVCollagen7S, .mac2, .autotaxin, .ck18f], fun c =>
    [c.elfSelection.map (Principal.allows c.item)]⟩,
  ⟨"44", "PDF360頁 D007(44) 検査の条件", [.lipoproteinLipase], fun c =>
    [c.hypertriglyceridemiaAndSuspectedLplDeficiency, c.lplDifferentialDiagnosis]⟩,
  ⟨"45", "PDF360頁 D007(45)", [.hgf], fun c =>
    [allowed c.method [.elisa], c.suspectedFulminantHepatitisOrFollowUp]⟩,
  ⟨"46/a", "PDF360頁 D007(46)ア", [.lrg], fun c =>
    [c.inflammatoryBowelDiseaseAssessment, either c.lrgThreeMonthInterval
      (both c.lrgOneMonthInterval (both c.lrgMonthlyMedicalNecessity
        (both c.lrgReasonAndResultInChart c.lrgReasonAndResultInClaim)))]⟩,
  ⟨"46/i", "PDF360頁 D007(46)イ", [.lrg], fun c =>
    [c.lrgMonthlySelection.map (Principal.allows c.item)]⟩,
  ⟨"47", "PDF360頁 D007(47) 本則", [.procalcitoninQuantitative, .procalcitoninSemiquantitative],
    fun c => [c.suspectedBacterialSepsis]⟩,
  ⟨"47", "PDF360頁 D007(47) ただし書",
    [.procalcitoninQuantitative, .procalcitoninSemiquantitative], fun c =>
    [c.endotoxinSelection.map (Principal.allows c.item)]⟩,
  ⟨"48/a", "PDF360頁 D007(48)ア", [.presepsin], fun c => [c.suspectedBacterialSepsis]⟩,
  ⟨"48/i", "PDF360頁 D007(48)イ",
    [.presepsin, .procalcitoninQuantitative, .procalcitoninSemiquantitative], fun c =>
    [c.presepsinSelection.map (Principal.allows c.item)]⟩,
  ⟨"49", "PDF360頁 D007(49)", [.infliximabQualitative], fun c =>
    [allowed c.method [.immunochromatography], c.rheumatoidArthritis, c.infliximabDoseDecision,
      c.infliximabPriorClaims.map (· < 3)]⟩,
  ⟨"50", "PDF360頁 D007(50)", [.vitaminD125], fun c =>
    [allowed c.method [.radioreceptor, .ria, .elisa], c.vitaminDIndication.map (· != .other),
      c.vitaminDPhase.bind fun phase =>
        match phase with
        | .diagnosis => some true
        | .firstTreatmentMonth => c.vitaminDFirstMonthPriorClaims.map (· < 2)
        | .laterTreatment => c.vitaminDLaterThreeMonthInterval]⟩,
  ⟨"51", "PDF360〜361頁 D007(51)", [.vegf], fun c =>
    [allowed c.method [.elisa], c.poemsDiagnosisOrFollowUp,
      c.vegfPriorClaimsThisCalendarMonth.map (· == 0)]⟩,
  ⟨"52/a", "PDF361頁 D007(52)ア", [.cochlinTomoprotein], fun c =>
    [allowed c.method [.elisa], c.suspectedPerilymphaticFistulaForDiagnosis,
      c.middleEarLavage, c.ctpGuidelineFollowed]⟩,
  ⟨"53", "PDF361頁 D007(53)", [.fgf23], fun c =>
    [allowed c.method [.cleia], c.fgfListedDisease,
      c.fgfPhase.bind fun phase =>
        match phase with
        | .diagnosis | .afterTumorRemoval | .afterSuspectDrugWithdrawal =>
          c.fgfPriorClaimsInPhase.map (· == 0)
        | .otherTreatmentAssessment => none]⟩
]

private def Clause.required (clause : Clause) (c : Context) : List (Option Bool) :=
  if clause.items.contains c.item then clause.checks c else []

private def Clause.rule (clause : Clause) : Rule Context Nat :=
  ⟨"notice/D007/paragraph/" ++ clause.suffix, notice clause.location,
    fun c _ => ∀ fact ∈ clause.required c, fact = some true⟩

private def itemRule (number : Nat) : Rule Context Nat :=
  let page := if number ≤ 57 then "180" else "181"
  ⟨"primary/D007/item/" ++ toString number, primary ("PDF" ++ page ++ "頁 D007の" ++ toString number),
    fun c p => c.item.number = number → p = c.item.points⟩

private def numbers := List.range' 35 30

def rules : List (Rule Context Nat) :=
  numbers.map itemRule ++ clauses.map Clause.rule

/-- 対象条項の前提がすべて確認されている個別実施。 -/
def Eligible (c : Context) : Prop :=
  ∀ fact ∈ clauses.flatMap (·.required c), fact = some true

private theorem item_number (item : Item) : item.number ∈ numbers := by
  cases item <;> decide

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ Eligible c ∧ p = c.item.points := by
  rw [rules, satisfies_append]
  constructor
  · rintro ⟨price, conditions⟩
    refine ⟨?_, price (itemRule c.item.number) (List.mem_map.mpr ⟨_, item_number c.item, rfl⟩) rfl⟩
    intro fact member
    obtain ⟨clause, active, required⟩ := List.mem_flatMap.mp member
    exact conditions clause.rule (List.mem_map.mpr ⟨clause, active, rfl⟩) fact required
  · rintro ⟨conditions, rfl⟩
    constructor
    · intro rule member
      obtain ⟨number, _, rfl⟩ := List.mem_map.mp member
      exact fun _ => rfl
    · intro rule member
      obtain ⟨clause, active, rfl⟩ := List.mem_map.mp member
      exact fun fact required => conditions fact (List.mem_flatMap.mpr ⟨clause, active, required⟩)

theorem determines_on : DeterminesOn Eligible rules := by
  intro c h
  refine ⟨⟨c.item.points, (satisfies_iff _ _).mpr ⟨h, rfl⟩⟩, ?_⟩
  intro first second hf hs
  exact ((satisfies_iff _ _).mp hf).2.trans ((satisfies_iff _ _).mp hs).2.symm

inductive Assessment where
  | payable (points : Nat)
  | ineligible
  | unresolved
  deriving DecidableEq, Repr

def assess (c : Context) : Assessment :=
  let facts := clauses.flatMap (·.required c)
  if facts.all (· == some true) then .payable c.item.points
  else if facts.contains (some false) then .ineligible else .unresolved

theorem payable_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ assess c = .payable p := by
  rw [satisfies_iff]
  simp only [assess, Eligible, List.all_eq_true, beq_iff_eq]
  split
  next h => exact ⟨fun hp => congrArg Assessment.payable hp.2.symm, fun hp => ⟨h, (Assessment.payable.inj hp).symm⟩⟩
  next h => split <;> simp only [h, false_and, reduceCtorEq]

example : assess { item := .zinc } = .payable 132 := by decide
example : assess { item := .hFabpQualitative } = .unresolved := by decide
example : assess { item := .hFabpQualitative, method := some .other } = .ineligible := by decide
example : DeterminesAt rules { item := .zinc } :=
  determines_on _ (by simp [Eligible, clauses, Clause.required])

example : assess {
    item := .igfbp1Qualitative, method := some .immunochromatography,
    completedGestationalWeeks := some 22, rupturedMembranesDiagnosis := some true,
    fibronectinSelection := some .separate } = .payable 175 := by decide

example : assess {
    item := .igfbp1Qualitative, method := some .immunochromatography,
    completedGestationalWeeks := some 37, rupturedMembranesDiagnosis := some true,
    fibronectinSelection := some .separate } = .ineligible := by decide

/-- (44)のヘパリン負荷に付随する費目。D500の薬剤価格等は別途評価する。 -/
def lplHeparinRule : Rule Bool (Bool × Bool) :=
  ⟨"notice/D007/paragraph/44", notice "PDF360頁 D007(44) ヘパリン負荷",
    fun challenged (drug, injection) =>
      (drug = true → challenged = true) ∧ (challenged = true → injection = false)⟩

def ctpJudgmentRule : Rule Unit SpecimenJudgment.Category :=
  ⟨"notice/D007/paragraph/52/i", notice "PDF361頁 D007(52)イ",
    fun _ category => category = .urineFecal⟩

/-- 実施したCTPを既存のD026振分けに渡す。月内履歴はD026側で扱う。 -/
def ctpJudgmentTest : SpecimenJudgment.Test :=
  { major := 7, number := 63, ordinaryCategory := .urineFecal }

theorem ctp_judgment_sound_complete (category : SpecimenJudgment.Category) :
    ctpJudgmentRule.holds () category ↔
      SpecimenJudgment.categoryFor ctpJudgmentTest = some category := by
  change category = .urineFecal ↔ _
  simp [SpecimenJudgment.categoryFor, SpecimenJudgment.geneRouting, ctpJudgmentTest, eq_comm]

example : assess {
    item := .fgf23, method := some .cleia, fgfListedDisease := some true,
    fgfPhase := some .diagnosis, fgfPriorClaimsInPhase := some 0 } = .payable 788 := by decide

example : assess {
    item := .fgf23, method := some .cleia, fgfListedDisease := some true,
    fgfPhase := some .diagnosis, fgfPriorClaimsInPhase := some 1 } = .ineligible := by decide

example : assess {
    item := .fgf23, method := some .cleia, fgfListedDisease := some true,
    fgfPhase := some .diagnosis } = .unresolved := by decide

/-- (28)の構成測定。血色素だけは同時測定の有無で扱う。 -/
inductive GasComponent where
  | sodium | potassium | chloride | ph | po2 | pco2 | bicarbonate
  deriving DecidableEq, Repr

structure GasMeasurements where
  components : List GasComponent
  simultaneousHemoglobin : Bool

def gasInclusionRule : Rule GasMeasurements (List GasComponent × Bool) :=
  ⟨"notice/D007/paragraph/28", notice "PDF358頁 D007(28) 包括",
    fun performed (separate, hemoglobinCharged) =>
      (∀ component ∈ performed.components, component ∉ separate) ∧
      (performed.simultaneousHemoglobin = true → hemoglobinCharged = false)⟩

def GasComponent.drawItem : GasComponent → Option BloodChemistry.Item
  | .sodium => some .sodium
  | .potassium => some .potassium
  | .chloride => some .chloride
  | _ => none

/-- 一採血モデルの入力から分析に含まれた実施を除く。同成分の別実施は、
既存の反復なしのモデル外。血算全体はここで除外しない。 -/
def drawWithoutGasComponents (draw : BloodChemistry.Draw)
    (components : List GasComponent) : BloodChemistry.Draw :=
  { draw with
    performed := draw.performed.filter
      (fun item => !(components.filterMap GasComponent.drawItem).contains item) }

def GasCombination (measurements : GasMeasurements) (sameSpecimen : Bool)
    (choice : BloodChemistryFurther.Choice) (separate : List GasComponent × Bool) : Prop :=
  gasInclusionRule.holds measurements separate ∧
    BloodChemistryFurther.Pair.bicarbonateAndBloodGas.rule.holds sameSpecimen choice

inductive GasSite where
  | inHouse | contractedInHouse | externalReportOnly | emergencyPartner
  deriving DecidableEq, Repr

structure GasContext where
  site : Option GasSite := none
  homeOxygenAtClinicWithoutBeds : Option Bool := none
  emergencyNeed : Option Bool := none
  closePartnerWithBeds : Option Bool := none
  promptTestAfterDraw : Option Bool := none
  promptReport : Option Bool := none
  deriving DecidableEq, Repr

private def GasContext.emergencyFacts (c : GasContext) : List (Option Bool) :=
  [c.homeOxygenAtClinicWithoutBeds, c.emergencyNeed, c.closePartnerWithBeds,
    c.promptTestAfterDraw, c.promptReport]

def gasFixedPointsRule : Rule GasContext Nat :=
  ⟨"notice/D007/paragraph/28", notice "PDF358頁 D007(28) 所定点数",
    fun _ p => BloodChemistryFurther.Item.scheduledPoints .bloodGas = some p⟩

def gasSiteRule : Rule GasContext Nat :=
  ⟨"notice/D007/paragraph/29", notice "PDF358頁 D007(29) 院内・院外報告のみ",
    fun c _ => c.site ≠ none ∧ c.site ≠ some .externalReportOnly⟩

def gasContractRule : Rule GasContext Nat :=
  ⟨"notice/D007/paragraph/29", notice "PDF358頁 D007(29) 院内委託",
    fun c _ => c.site = some .contractedInHouse → c.promptReport = some true⟩

def gasEmergencyRule : Rule GasContext Nat :=
  ⟨"notice/D007/paragraph/29", notice "PDF358頁 D007(29) 在宅酸素療法の緊急時",
    fun c _ => c.site = some .emergencyPartner →
      ∀ fact ∈ c.emergencyFacts, fact = some true⟩

def gasRules := [gasFixedPointsRule, gasSiteRule, gasContractRule, gasEmergencyRule]

def GasEligible (c : GasContext) : Prop :=
  gasSiteRule.holds c 0 ∧ gasContractRule.holds c 0 ∧ gasEmergencyRule.holds c 0

theorem gas_satisfies_iff (c : GasContext) (p : Nat) :
    Satisfies gasRules c p ↔ GasEligible c ∧ p = 131 := by
  simp only [gasRules, satisfies_cons, satisfies_nil, gasFixedPointsRule,
    GasEligible, gasSiteRule, gasContractRule, gasEmergencyRule,
    BloodChemistryFurther.Item.scheduledPoints, Option.some.injEq, and_true]
  constructor
  · rintro ⟨hp, site, contracted, emergency⟩
    exact ⟨⟨site, contracted, emergency⟩, hp.symm⟩
  · rintro ⟨⟨site, contracted, emergency⟩, hp⟩
    exact ⟨hp.symm, site, contracted, emergency⟩

theorem determines_gas_on : DeterminesOn GasEligible gasRules := by
  intro c h
  refine ⟨⟨131, (gas_satisfies_iff _ _).mpr ⟨h, rfl⟩⟩, ?_⟩
  intro a b ha hb
  exact ((gas_satisfies_iff _ _).mp ha).2.trans ((gas_satisfies_iff _ _).mp hb).2.symm

theorem gas_in_house_iff (p : Nat) :
    Satisfies gasRules { site := some .inHouse } p ↔
    BloodChemistryFurther.assess { item := .bloodGas, bloodGasInHouse := some true } =
      .payable p := by
  rw [gas_satisfies_iff]
  simp [GasEligible, gasSiteRule, gasContractRule, gasEmergencyRule,
    BloodChemistryFurther.assess, BloodChemistryFurther.eligible,
    BloodChemistryFurther.Item.scheduledPoints, eq_comm]

example : Satisfies gasRules {
    site := some .emergencyPartner, homeOxygenAtClinicWithoutBeds := some true,
    emergencyNeed := some true, closePartnerWithBeds := some true,
    promptTestAfterDraw := some true, promptReport := some true } 131 := by
  simp [gas_satisfies_iff, GasEligible, gasSiteRule, gasContractRule, gasEmergencyRule,
    GasContext.emergencyFacts]

example : ¬ SatisfiableAt gasRules { site := some .externalReportOnly } := by
  simp [SatisfiableAt, gas_satisfies_iff, GasEligible, gasSiteRule]

example : ¬ SatisfiableAt gasRules { site := some .contractedInHouse } := by
  simp [SatisfiableAt, gas_satisfies_iff, GasEligible, gasContractRule]

/-- (36)の三者の併施と、(18)の項24・D008の二者の併施を区別する。 -/
inductive AlpTest where
  | d007Pag | d007IsoenzymesAndBap | d008Bap
  deriving DecidableEq, Repr

structure AlpCombination where
  allThreeTogether : Bool
  principal : AlpTest

def alpCombinationRule : Rule AlpCombination (List AlpTest) :=
  ⟨"notice/D007/paragraph/36", notice "PDF359頁 D007(36)",
    fun c charged => c.allThreeTogether = true → ∀ item ∈ charged, item = c.principal⟩

def AlpSelections (c : AlpCombination) (bapTogether : Bool)
    (bapChoice : BloodChemistryFurther.Choice) (charged : List AlpTest) : Prop :=
  alpCombinationRule.holds c charged ∧
    BloodChemistryFurther.Pair.bapAndD008.rule.holds bapTogether bapChoice ∧
    (.d007IsoenzymesAndBap ∈ charged → bapChoice ≠ .second) ∧
    (.d008Bap ∈ charged → bapChoice ≠ .first)

/-- 元区分で準用の適格性と包括群への所属を確認済みの実施。 -/
structure BundleReference where
  target : BloodChemistry.Item
  occurrence : Nat
  deriving DecidableEq, Repr

structure BundleContext where
  /-- 既存の一採血モデルで選別・正規化した項目。 -/
  native : List BloodChemistry.Item
  references : Option (List BundleReference)

def bundleReferenceRule : Rule BundleContext (List BloodChemistry.Item) :=
  ⟨"notice/D007/paragraph/54", notice "PDF361頁 D007(54)",
    fun c items => ∃ references, c.references = some references ∧
      items = c.native ++ references.map BundleReference.target⟩

def bundleNoteRule : Rule (List BloodChemistry.Item) Nat :=
  ⟨"primary/D007/note/unnumbered/1", primary "PDF181頁 D007注", fun items p =>
    (items.length < 5 → p = (items.map BloodChemistry.Item.points).sum) ∧
    (5 ≤ items.length ∧ items.length < 8 → p = 93) ∧
    (8 ≤ items.length ∧ items.length < 10 → p = 99) ∧
    (10 ≤ items.length → p = 103)⟩

theorem bundle_note_iff (items : List BloodChemistry.Item) (p : Nat) :
    bundleNoteRule.holds items p ↔ p = BloodChemistry.pointsForItems items :=
  BloodChemistry.pointsRule_iff items p

def BundlePoints (c : BundleContext) (p : Nat) : Prop :=
  c.native ≠ [] ∧ ∃ items, bundleReferenceRule.holds c items ∧ bundleNoteRule.holds items p

/-- 元のD001モデルでD007準用に該当したことと、当該包括群への所属を照合する。
検査種類からD007の準用先を求める対応表は外部入力。 -/
def D001BundleReference (urine : UrineFecalTests.Context) (group : BundleContext)
    (reference : BundleReference) : Prop :=
  UrineFecalTests.assess urine = some (.requiresReference (.other .d007) true) ∧
    ∃ refs, group.references = some refs ∧ reference ∈ refs

example : D001BundleReference
    { item := .specialUrine (.other .d007) }
    { native := [.bun], references := some [⟨.creatinine, 1⟩] }
    ⟨.creatinine, 1⟩ := by
  exact ⟨rfl, _, rfl, by simp⟩

def BundleScope (c : BundleContext) : Prop :=
  c.native ≠ [] ∧ ∃ refs, c.references = some refs ∧ (refs.map BundleReference.occurrence).Nodup

theorem determines_bundle_on (c : BundleContext) (h : BundleScope c) :
    (∃ p, BundlePoints c p) ∧
    ∀ first second, BundlePoints c first → BundlePoints c second → first = second := by
  obtain ⟨native, refs, known, _⟩ := h
  let items := c.native ++ refs.map BundleReference.target
  refine ⟨⟨BloodChemistry.pointsForItems items, native, items, ⟨refs, known, rfl⟩,
    (bundle_note_iff _ _).mpr rfl⟩, ?_⟩
  rintro first second ⟨_, _, ⟨firstRefs, firstKnown, rfl⟩, hf⟩
    ⟨_, _, ⟨secondRefs, secondKnown, rfl⟩, hs⟩
  have equal : firstRefs = secondRefs := Option.some.inj (firstKnown.symm.trans secondKnown)
  subst secondRefs
  exact ((bundle_note_iff _ _).mp hf).trans
    ((bundle_note_iff _ _).mp hs).symm

example : BundlePoints {
    native := [.bun, .glucose, .uricAcid, .ast], references := some [⟨.lipase, 1⟩] } 93 := by
  exact ⟨by simp, _, ⟨_, rfl, rfl⟩, (bundle_note_iff _ _).mpr rfl⟩

example : ¬ ∃ p, BundlePoints { native := [.bun], references := none } p := by
  simp [BundlePoints, bundleReferenceRule]

example : BloodChemistry.points
    (drawWithoutGasComponents { performed := [.sodium, .chloride, .glucose] }
      [.sodium, .chloride]) = some 11 := by decide

example : ¬ GasCombination ⟨[.bicarbonate], true⟩ true .both ([], false) := by
  intro h
  have bad := h.2 rfl
  cases bad

example : assess {
    item := .myoglobinQuantitative, hFabpMyoglobinSelection := some (.selected .hFabpQuantitative)
    } = .ineligible := by decide


end Sanri.MedicalFee.BloodChemistryLate
