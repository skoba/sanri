import Sanri.D023Early
import Sanri.D023Additional

namespace Sanri.MedicalFee.D023

open Sanri.Logic

/-- 準用元の二件は別型で保持し、告示の検査を実施したことに置き換えない。 -/
inductive OutpatientTest where
  | genitourinary (evidence : GenitourinaryContext)
  | groupStrep (evidence : GroupAStrepContext)
  | hbv (evidence : HbvContext)
  | mycoplasma
  | influenza (evidence : InfluenzaContext)
  | rsVirus (evidence : RsContext)
  | legionella
  | ebv (evidence : EbvContext)
  | hcv (evidence : HcvContext)
  | hpv (evidence : HpvContext)
  | genital (evidence : (GenitalTest × GenitalTestContext))
  | pertussis (evidence : PertussisContext)
  | pneumoniae (evidence : PneumoniaeContext)
  | pylori (evidence : PyloriContext)
  | mycobacterialIdentification (evidence : (Option MycobacterialMethod))
  | tuberculosis (evidence : (Option MycobacterialMethod))
  | mac (evidence : MacContext)
  | hbvVariant (evidence : HbvVariantContext)
  | methicillin (evidence : MethicillinContext)
  | sars (evidence : SarsContext)
  | htlv (evidence : HtlvContext)
  | herpes (evidence : HerpesQuantityContext)
  | cmvQuantity (evidence : CmvQuantityContext)
  | hivQuantity (evidence : HivQuantityContext)
  | covid (evidence : CovidContext)
  | mpox (evidence : MpoxContext)
  | cmvDetection (evidence : CmvDetectionContext)
  | tbSingle (evidence : (Fin 3 × TbResistanceContext))
  | tbDual (evidence : TbResistanceContext)
  | pneumoniaPanel (evidence : PneumoniaPanelContext)
  | panel (evidence : RespiratoryPanelAssessment)
  | csf (evidence : CsfPanelContext)
  | sepsis (evidence : (SepsisPanelContext × D023Schedule.Evidence))
  | hpvGenotype (evidence : HpvGenotypeContext)
  | hivGenotype (evidence : HivGenotypeContext)

def OutpatientTest.tier : OutpatientTest → D023Schedule.Tier
  | .genitourinary e => match e.performance.item with
    | .trachomatis => .trachomatis
    | .gonococcus => .gonococcus
    | .combined => .gonococcusTrachomatis
  | .groupStrep _ => .groupAStrep
  | .hbv _ => .hbvQuantity
  | .mycoplasma => .respiratorySingle
  | .influenza _ => .respiratorySingle
  | .rsVirus _ => .respiratorySingle
  | .legionella => .legionella
  | .ebv _ => .ebvQuantity
  | .hcv e => match e.performance.item with | .detection => .hcvDetection | .quantity => .hcvQuantity
  | .hpv e => match e.performance.item with | .detection => .hpv | .simpleGenotype => .hpvSimpleGenotype
  | .genital _ => .genitalCombination
  | .pertussis _ => .pertussisGroup
  | .pneumoniae _ => .pertussisGroup
  | .pylori _ => .pertussisGroup
  | .mycobacterialIdentification _ => .mycobacteriaGroup
  | .tuberculosis _ => .mycobacteriaGroup
  | .mac _ => .mac
  | .hbvVariant _ => .viralOrMethicillinGroup
  | .methicillin _ => .viralOrMethicillinGroup
  | .sars _ => .viralOrMethicillinGroup
  | .htlv _ => .viralOrMethicillinGroup
  | .herpes _ => .viralOrMethicillinGroup
  | .cmvQuantity _ => .viralOrMethicillinGroup
  | .hivQuantity _ => .hivQuantity
  | .covid e => match e.performance.item with | .single => .covid | _ => .covidPanelOrMpox
  | .mpox _ => .covidPanelOrMpox
  | .cmvDetection _ => .cmvDetection
  | .tbSingle _ => .tbSingleResistance
  | .tbDual _ => .tbDualResistance
  | .pneumoniaPanel _ => .pneumoniaResistancePanel
  | .panel e => e.panel.tier
  | .csf _ => .sepsisOrCsfPanel
  | .sepsis _ => .sepsisOrCsfPanel
  | .hpvGenotype _ => .hpvGenotype
  | .hivGenotype _ => .hivGenotype

def OutpatientTest.variant : OutpatientTest → Nat
  | .influenza _ => 1
  | .rsVirus _ => 2
  | .genital e => e.1.variant
  | .pertussis e => match e.performance.item with | .pertussis => 0 | .pertussisAndParapertussis => 2
  | .pneumoniae _ => 1
  | .pylori _ => 3
  | .tuberculosis _ => 1
  | .methicillin _ => 1
  | .sars _ => 2
  | .htlv _ => 3
  | .herpes _ => 4
  | .cmvQuantity _ => 5
  | .covid e => match e.performance.item with | .single | .influenza => 0 | .rs => 1 | .influenzaRs => 2
  | .mpox _ => 3
  | .tbSingle e => e.1.val
  | .csf _ => 1
  | _ => 0

/-- 個別算定の適格性。摘要欄・文書などの記載は各規則の出力に保持する。 -/
def OutpatientTest.Eligible : OutpatientTest → Prop
  | .genitourinary e => match e.performance.item with
    | .trachomatis => trachomatis.holds e ()
    | .gonococcus => gonococcus.holds e ()
    | .combined => combinedGenitourinary.holds e ()
  | .groupStrep e => groupAStrep.holds e ()
  | .hbv e => hbvQuantity.holds e ()
  | .mycoplasma => True
  | .influenza e => D023.influenza.holds e ()
  | .rsVirus e => rs.holds e ()
  | .legionella => True
  | .ebv e => ebvQuantity.holds e ()
  | .hcv e => match e.performance.item with
    | .detection => hcvDetection.holds e ()
    | .quantity => hcvQuantity.holds e ()
  | .hpv e => HpvEligible e
  | .genital e => (genitalRules e.1).holds e.2 ()
  | .pertussis e => PertussisEligible e
  | .pneumoniae e => D023.pneumoniae.holds e true
  | .pylori e => D023.pylori.holds e ()
  | .mycobacterialIdentification e => D023.mycobacterialIdentification.holds e ()
  | .tuberculosis e => tuberculosisMethod.holds e ()
  | .mac e => D023.mac.holds e ()
  | .hbvVariant e => D023.hbvVariant.holds e ()
  | .methicillin e => methicillinIndication.holds e ()
  | .sars e => D023.sars.holds e ()
  | .htlv e => D023.htlv.holds e ()
  | .herpes e => herpesQuantity.holds e ()
  | .cmvQuantity e => D023.cmvQuantity.holds e ()
  | .hivQuantity e => D023.hivQuantity.holds e ()
  | .covid e => Satisfies [covidSingle, covidInfluenza, covidRs, covidInfluenzaRs] e ()
  | .mpox e => D023.mpox.holds e ()
  | .cmvDetection e => D023.cmvDetection.holds e ()
  | .tbSingle e => singleResistance.holds e.2 ()
  | .tbDual e => dualResistance.holds e ()
  | .pneumoniaPanel e => PneumoniaPanelEligible e
  | .panel e => RespiratoryPanelEligible e
  | .csf e => CsfPanelEligible e
  | .sepsis e => D023.sepsis.holds e.1 () ∧ e.2.tier = .sepsisOrCsfPanel ∧
    e.2.csfPanel = some false ∧ D023Schedule.sepsisPanelFacility.holds e.2 ()
  | .hpvGenotype e => D023.hpvGenotype.holds e ()
  | .hivGenotype e => D023.hivGenotype.holds e ()

def OutpatientTest.rapidTarget : OutpatientTest → Bool
  | .mycoplasma | .legionella | .pertussis _ | .tuberculosis _ => true
  | _ => false

structure OutpatientInput where
  test : OutpatientTest
  insuranceMedicalInstitution : Bool
  status : ConsultationGeneralRules.PatientStatus
  ultracentrifugalConcentration : Option Bool := none
  explainedOnTestDay : Option Bool := none
  suppliedWrittenResults : Option Bool := none

def OutpatientInput.evidence (c : OutpatientInput) : D023Schedule.Evidence :=
  { tier := c.test.tier, ultracentrifugalConcentration := c.ultracentrifugalConcentration }

def OutpatientEligible (c : OutpatientInput) : Prop :=
  c.insuranceMedicalInstitution = true ∧ c.status = .outpatient ∧ c.test.Eligible ∧
    (c.test.tier = .hivQuantity → c.ultracentrifugalConcentration.isSome = true) ∧
    (c.test.rapidTarget = true → c.explainedOnTestDay.isSome = true ∧
      c.suppliedWrittenResults.isSome = true) ∧
    (∀ evidence, c.test = .pertussis evidence →
      c.explainedOnTestDay = some evidence.explainedOnTestDay ∧
      c.suppliedWrittenResults = some evidence.suppliedWrittenResults)

def outpatientRapid : Rule OutpatientInput Nat :=
  ⟨"primary/D023/note/unnumbered/1", otherRapid.source, fun c p =>
    (c.test.rapidTarget = true ∧ c.explainedOnTestDay = some true ∧
      c.suppliedWrittenResults = some true ∧ p = rapidPoints) ∨
    ((c.test.rapidTarget = false ∨ c.explainedOnTestDay = some false ∨
      c.suppliedWrittenResults = some false) ∧ p = 0)⟩

def outpatientConcentration : Rule OutpatientInput Nat :=
  ⟨D023Schedule.concentration.id, D023Schedule.concentration.source,
    fun c p => D023Schedule.concentration.holds c.evidence p⟩

def PermitsOutpatientPoints (c : OutpatientInput) (p : Nat) : Prop :=
  ∃ base concentration rapid, Satisfies D023Schedule.rates c.test.tier base ∧
    outpatientConcentration.holds c concentration ∧ outpatientRapid.holds c rapid ∧
    p = base + concentration + rapid

def OutpatientInput.selectedRapid (c : OutpatientInput) : Bool :=
  c.test.rapidTarget && c.explainedOnTestDay == some true && c.suppliedWrittenResults == some true

def OutpatientInput.selectedConcentration (c : OutpatientInput) : Bool :=
  c.test.tier == .hivQuantity && c.ultracentrifugalConcentration == some true

def OutpatientInput.points (c : OutpatientInput) : Nat :=
  c.test.tier.base + (if c.selectedConcentration then D023Schedule.concentrationPoints else 0) +
    (if c.selectedRapid then rapidPoints else 0)

private theorem outpatient_concentration_iff (c : OutpatientInput)
    (h : OutpatientEligible c) (p : Nat) : outpatientConcentration.holds c p ↔
      p = (if c.selectedConcentration then D023Schedule.concentrationPoints else 0) := by
  by_cases tier : c.test.tier = .hivQuantity
  · have known := h.2.2.2.1 tier
    cases eq : c.ultracentrifugalConcentration with
    | none => simp [eq] at known
    | some value =>
      cases value <;>
        simp [outpatientConcentration, D023Schedule.concentration, OutpatientInput.evidence,
          OutpatientInput.selectedConcentration, tier, eq]
  · simp [outpatientConcentration, D023Schedule.concentration, OutpatientInput.evidence,
      OutpatientInput.selectedConcentration, tier]

private theorem outpatient_rapid_iff (c : OutpatientInput) (h : OutpatientEligible c) (p : Nat) :
    outpatientRapid.holds c p ↔ p = (if c.selectedRapid then rapidPoints else 0) := by
  cases target : c.test.rapidTarget with
  | false => simp [outpatientRapid, OutpatientInput.selectedRapid, target]
  | true =>
    obtain ⟨explained, supplied⟩ := h.2.2.2.2.1 target
    cases he : c.explainedOnTestDay <;> cases hw : c.suppliedWrittenResults <;>
      simp_all only [Option.isSome_none, Bool.false_eq_true, Option.isSome_some]
    rename_i e w
    cases e <;> cases w <;>
      simp [outpatientRapid, OutpatientInput.selectedRapid, target, he, hw]

theorem outpatient_points_iff (c : OutpatientInput) (h : OutpatientEligible c) (p : Nat) :
    PermitsOutpatientPoints c p ↔ p = c.points := by
  unfold PermitsOutpatientPoints OutpatientInput.points
  simp only [D023Schedule.rates_iff, outpatient_concentration_iff c h,
    outpatient_rapid_iff c h]
  constructor
  · rintro ⟨_, _, _, rfl, rfl, rfl, rfl⟩
    rfl
  · intro hp
    exact ⟨_, _, _, rfl, rfl, rfl, hp⟩

theorem outpatient_points_determines (c : OutpatientInput) (h : OutpatientEligible c) :
    ∃ p, PermitsOutpatientPoints c p ∧ ∀ other, PermitsOutpatientPoints c other → other = p :=
  ⟨c.points, (outpatient_points_iff c h _).mpr rfl, fun _ hp => (outpatient_points_iff c h _).mp hp⟩

/-- 旧関数に渡す施設・患者フラグは旧入力を保持し、加算の事実は標準形から射影する。 -/
def OutpatientInput.legacyRequest (c : OutpatientInput) (conditions : SpecimenTests.Conditions) :
    SpecimenTests.Request :=
  { code := .d023
    number := c.test.tier.number
    branch := c.test.tier.branch
    variant := c.test.variant
    conditions := { conditions with
      ultracentrifugalConcentration := c.selectedConcentration
      resultsExplainedOnTestDay := c.explainedOnTestDay == some true
      writtenResultsProvided := c.suppliedWrittenResults == some true } }

set_option maxRecDepth 2048 in
private theorem outpatient_catalog_variant (t : OutpatientTest) :
    ∃ entry, SpecimenTests.lookup .d023 t.tier.number t.tier.branch = some entry ∧
      t.variant < entry.variants.length ∧ entry.points = some t.tier.base := by
  cases t
  case genitourinary e =>
    cases he : e.performance.item <;>
      simp only [OutpatientTest.tier, OutpatientTest.variant, he] <;> exact ⟨_, rfl, by decide, rfl⟩
  case hcv e =>
    cases he : e.performance.item <;>
      simp only [OutpatientTest.tier, OutpatientTest.variant, he] <;> exact ⟨_, rfl, by decide, rfl⟩
  case hpv e =>
    cases he : e.performance.item <;>
      simp only [OutpatientTest.tier, OutpatientTest.variant, he] <;> exact ⟨_, rfl, by decide, rfl⟩
  case genital e =>
    cases he : e.1 <;>
      simp only [OutpatientTest.tier, OutpatientTest.variant, he] <;> exact ⟨_, rfl, by decide, rfl⟩
  case pertussis e =>
    cases he : e.performance.item <;>
      simp only [OutpatientTest.tier, OutpatientTest.variant, he] <;> exact ⟨_, rfl, by decide, rfl⟩
  case covid e =>
    cases he : e.performance.item <;>
      simp only [OutpatientTest.tier, OutpatientTest.variant, he] <;> exact ⟨_, rfl, by decide, rfl⟩
  case tbSingle e =>
    exact ⟨_, rfl, e.1.isLt, rfl⟩
  case panel e =>
    cases he : e.panel.performance.item <;>
      simp only [OutpatientTest.tier, OutpatientTest.variant, RespiratoryPanelContext.tier, he,
        Bool.false_eq_true, ite_false, ite_true] <;> exact ⟨_, rfl, by decide, rfl⟩
  all_goals
    simp only [OutpatientTest.tier, OutpatientTest.variant]
    exact ⟨_, rfl, by decide, rfl⟩

private theorem outpatient_legacy_rapid_target (t : OutpatientTest) :
    (decide (t.tier.number = 6 ∧ t.variant = 0) || decide (t.tier.number = 7) ||
      decide (t.tier.number = 13 ∧ (t.variant = 0 ∨ t.variant = 2)) ||
      decide (t.tier.number = 14 ∧ t.variant = 1)) = t.rapidTarget := by
  cases t <;> try rfl
  all_goals
    first | cases he : (by assumption : GenitourinaryContext).performance.item
          | cases he : (by assumption : HcvContext).performance.item
          | cases he : (by assumption : HpvContext).performance.item
          | cases he : (by assumption : PertussisContext).performance.item
          | cases he : (by assumption : CovidContext).performance.item
          | cases he : (by assumption : RespiratoryPanelAssessment).panel.performance.item
  all_goals simp [OutpatientTest.tier, OutpatientTest.variant, OutpatientTest.rapidTarget,
    RespiratoryPanelContext.tier, D023Schedule.Tier.number, he]

private def chargedPoints : SpecimenTests.ItemResult → Option Nat
  | .charged base extra => some (base + extra)
  | _ => none

/-- 旧関数の施設等の入力も整合する射影で、旧評価の点数と標準形の解が一致する。 -/
theorem outpatient_legacy_iff (c : OutpatientInput) (h : OutpatientEligible c)
    (conditions : SpecimenTests.Conditions)
    (compatible : SpecimenTests.eligible (c.legacyRequest conditions) = true) (p : Nat) :
    PermitsOutpatientPoints c p ↔
      (SpecimenTests.assessOne (c.legacyRequest conditions)).bind chargedPoints = some p := by
  obtain ⟨entry, catalog, variant, rate⟩ := outpatient_catalog_variant c.test
  have rapid : SpecimenTests.rapidMicrobialEligible (c.legacyRequest conditions) = c.selectedRapid := by
    simp only [SpecimenTests.rapidMicrobialEligible, OutpatientInput.legacyRequest,
      OutpatientInput.selectedRapid, decide_true, Bool.true_and]
    exact congrArg
      (fun target => target && c.explainedOnTestDay == some true &&
        c.suppliedWrittenResults == some true) (outpatient_legacy_rapid_target c.test)
  have concentration : (c.test.tier.number = 18 ∧ c.selectedConcentration = true) ↔
      c.selectedConcentration = true := by
    refine ⟨And.right, fun selected => ⟨?_, selected⟩⟩
    have tier : c.test.tier = .hivQuantity := by
      simpa [OutpatientInput.selectedConcentration, Bool.and_eq_true] using
        (show (c.test.tier == .hivQuantity) = true from (Bool.and_eq_true_iff.mp selected).1)
    simp [tier, D023Schedule.Tier.number]
  rw [outpatient_points_iff c h]
  have additions : SpecimenTests.additions (c.legacyRequest conditions) =
      (if c.selectedConcentration then D023Schedule.concentrationPoints else 0) +
      (if c.selectedRapid then rapidPoints else 0) := by
    unfold SpecimenTests.additions
    rw [rapid]
    simp [OutpatientInput.legacyRequest, concentration, D023Schedule.concentrationPoints, rapidPoints]
  simp only [SpecimenTests.assessOne,
    show (c.legacyRequest conditions).code = .d023 from rfl,
    show (c.legacyRequest conditions).number = c.test.tier.number from rfl,
    show (c.legacyRequest conditions).branch = c.test.tier.branch from rfl,
    show (c.legacyRequest conditions).variant = c.test.variant from rfl,
    catalog, Nat.not_le.mpr variant, ite_false, compatible, Bool.not_true, reduceCtorEq,
    false_and, rate, additions, Option.bind_some, chargedPoints, Option.some.injEq,
    OutpatientInput.points]
  rw [Nat.add_assoc, eq_comm]

def OutpatientTest.judgmentTest (t : OutpatientTest) : SpecimenJudgment.Test :=
  { major := 23, number := t.tier.number, variant := t.variant, ordinaryCategory := .microbiological }

theorem outpatient_routes (t : OutpatientTest) :
    SpecimenJudgment.standardizedCategoryFor t.judgmentTest = some .microbiological := rfl

/-- 検査実施の点数を第1節の既存の実施料集計へ渡す。 -/
def OutpatientInput.toSpecimenItem (c : OutpatientInput) (_ : OutpatientEligible c) (kind : Nat) :
    Examinations.SpecimenItem :=
  { kind, executionPoints := c.points }

private def outpatientLegionella : OutpatientInput :=
  ⟨.legionella, true, .outpatient, none, some true, some true⟩

example : OutpatientEligible outpatientLegionella := by
  simp [OutpatientEligible, outpatientLegionella, OutpatientTest.Eligible, OutpatientTest.tier,
    OutpatientTest.rapidTarget]

example : outpatientLegionella.points = 396 := rfl

example : ¬ OutpatientEligible { outpatientLegionella with explainedOnTestDay := none } := by
  simp [OutpatientEligible, outpatientLegionella, OutpatientTest.Eligible, OutpatientTest.tier,
    OutpatientTest.rapidTarget]

end Sanri.MedicalFee.D023
