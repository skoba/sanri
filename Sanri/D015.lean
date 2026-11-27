import Sanri.BloodChemistryLate
import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment

/-! D015、基準診療日2026-10-22の外来検体検査実施料。 -/
namespace Sanri.MedicalFee.D015

open Sanri.Logic Sanri.History

inductive Item where
  | crpQual
  | crp
  | coproporphyrin
  | phosphatase
  | g6pd
  | protoporphyrin
  | ch50
  | immunoglobulin
  | cryoglobulinQual
  | cryoglobulinQuant
  | saa
  | transferrin
  | c3
  | c4
  | ceruloplasmin
  | beta2Microglobulin
  | igeSemi
  | igeQuant
  | transthyretin
  | specificIge
  | alpha1Microglobulin
  | haptoglobin
  | rbp
  | c3Proactivator
  | wholeAntiserum
  | il6
  | tarc
  | hemopexin
  | apr
  | atopyScreen
  | benceJones
  | fibronectin
  | specificAntiserum
  | c1Inactivator
  | scca2
  | lightChain
  | ifnLambda3
  | sfltPlgf
  | freeLightChain
  | tuberculosis
  | drugImmunofixation
  | concizumab
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .crpQual => 1
  | .crp => 1
  | .coproporphyrin => 2
  | .phosphatase => 2
  | .g6pd => 3
  | .protoporphyrin => 3
  | .ch50 => 4
  | .immunoglobulin => 4
  | .cryoglobulinQual => 5
  | .cryoglobulinQuant => 5
  | .saa => 6
  | .transferrin => 7
  | .c3 => 8
  | .c4 => 8
  | .ceruloplasmin => 9
  | .beta2Microglobulin => 10
  | .igeSemi => 11
  | .igeQuant => 11
  | .transthyretin => 12
  | .specificIge => 13
  | .alpha1Microglobulin => 14
  | .haptoglobin => 14
  | .rbp => 14
  | .c3Proactivator => 15
  | .wholeAntiserum => 16
  | .il6 => 16
  | .tarc => 17
  | .hemopexin => 18
  | .apr => 19
  | .atopyScreen => 20
  | .benceJones => 21
  | .fibronectin => 22
  | .specificAntiserum => 23
  | .c1Inactivator => 24
  | .scca2 => 25
  | .lightChain => 26
  | .ifnLambda3 => 27
  | .sfltPlgf => 27
  | .freeLightChain => 28
  | .tuberculosis => 29
  | .drugImmunofixation => 30
  | .concizumab => 31

def Item.variant : Item → Nat
  | .crp => 1
  | .phosphatase => 1
  | .protoporphyrin => 1
  | .immunoglobulin => 1
  | .cryoglobulinQuant => 1
  | .c4 => 1
  | .igeQuant => 1
  | .haptoglobin => 1
  | .rbp => 2
  | .il6 => 1
  | .sfltPlgf => 1
  | _ => 0

def Item.points : Item → Nat
  | .crpQual => 16
  | .crp => 16
  | .coproporphyrin => 30
  | .phosphatase => 30
  | .g6pd => 34
  | .protoporphyrin => 34
  | .ch50 => 38
  | .immunoglobulin => 38
  | .cryoglobulinQual => 42
  | .cryoglobulinQuant => 42
  | .saa => 47
  | .transferrin => 60
  | .c3 => 70
  | .c4 => 70
  | .ceruloplasmin => 90
  | .beta2Microglobulin => 98
  | .igeSemi => 100
  | .igeQuant => 100
  | .transthyretin => 101
  | .specificIge => 110
  | .alpha1Microglobulin => 129
  | .haptoglobin => 129
  | .rbp => 129
  | .c3Proactivator => 160
  | .wholeAntiserum => 170
  | .il6 => 170
  | .tarc => 179
  | .hemopexin => 180
  | .apr => 191
  | .atopyScreen => 194
  | .benceJones => 201
  | .fibronectin => 204
  | .specificAntiserum => 218
  | .c1Inactivator => 253
  | .scca2 => 300
  | .lightChain => 330
  | .ifnLambda3 => 340
  | .sfltPlgf => 340
  | .freeLightChain => 388
  | .tuberculosis => 593
  | .drugImmunofixation => 776
  | .concizumab => 12850

def ledgerItems : List Item :=
  [.crpQual, .crp, .coproporphyrin, .phosphatase, .g6pd, .protoporphyrin,
   .ch50, .immunoglobulin, .cryoglobulinQual, .cryoglobulinQuant, .saa, .transferrin,
   .c3, .c4, .ceruloplasmin, .beta2Microglobulin, .igeSemi, .igeQuant,
   .transthyretin, .specificIge, .alpha1Microglobulin, .haptoglobin, .rbp, .c3Proactivator,
   .wholeAntiserum, .il6, .tarc, .hemopexin, .apr, .atopyScreen,
   .benceJones, .fibronectin, .specificAntiserum, .c1Inactivator, .scca2, .lightChain,
   .ifnLambda3, .sfltPlgf, .freeLightChain, .tuberculosis, .drugImmunofixation, .concizumab]

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF188頁 D015 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (pages : String) (n : Nat) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF" ++ pages ++ "頁 D015(" ++ toString n ++ ")", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def rateRule (i : Item) : Rule Item Nat :=
  ⟨"primary/D015/item/" ++ toString i.number,
    primary (toString i.number), fun item p => item = i → p = i.points⟩

def rates := ledgerItems.map rateRule

theorem rate_iff (i : Item) (p : Nat) : Satisfies rates i p ↔ p = i.points := by
  constructor
  · intro h
    have hi : i ∈ ledgerItems := by cases i <;> decide
    exact h (rateRule i) (List.mem_map.mpr ⟨i, hi, rfl⟩) rfl
  · intro h r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro eq
    simpa [eq] using h

inductive Method where
  | sridOrEquivalent | immunoelectrophoresis | immunofixation | eclia | clia | cleia
  | elisa | nephelometry | twoStepSandwichCleia
  deriving DecidableEq

inductive Specimen where
  | serum | plasma
  deriving DecidableEq

inductive Immunoglobulin where
  | igg | iga | igm | igd
  deriving DecidableEq

inductive Allergen where
  | dPteronyssinus | dFarinae | cat | dog | bermuda | orchard | ragweed | mugwort
  | birch | cedar | candida | alternaria
  deriving DecidableEq

inductive Purpose where
  | atopicSeverity | drugSensitivityDifferential | covidRisk | rupture | threatenedPreterm
  deriving DecidableEq

inductive Finding where
  | approvedAvoidsDaratumumabInterference | treatedWithDaratumumab | myelomaOrAlResponse
  | sirsSeverity | il6RepeatNecessary | serumTarcQuantified | drugHypersensitivitySuspected
  | tarcRepeatNecessary | covidConfirmed | respiratoryFailureManagement | aprThreeMeasured
  | evaluatesHypergammaglobulinemia | ifnPreviousBelowThreshold | sfltAndPlgfMeasuredAndRatioCalculated
  | suspectedPreeclampsia | proteinuria | preeclampsiaSigns | fetalGrowthRestriction
  | fetalGrowthRestrictionFindings | pregnancyExceptionNecessary | tuberculosisStronglySuspected
  | beforeBiologicAsRequiredByLabel
  | congenitalHemophiliaOnConcizumab | determinesConcizumabDose | concizumabRepeatNecessary
  deriving DecidableEq

inductive Remark where
  | il6Date | il6DetailedReason | tarcDetailedReason | pregnancyRisk | pregnancyRiskBasis
  | pregnancyDetailedReason | concizumabReason
  deriving DecidableEq

structure Context where
  performance : Performance Item
  method : Option Method := none
  specimen : Option Specimen := none
  purpose : Option Purpose := none
  finding : Finding → Option Bool := fun _ => none
  immunoglobulin : Option Immunoglobulin := none
  allergens : Option (List Allergen) := none
  gestationalWeeks : Option Nat := none
  ageYears : Option Nat := none
  systolic : Option Nat := none
  diastolic : Option Nat := none
  otherSelected : Option (List (Performance Item)) := none
  /-- 確認済み一連の現在候補より前に算定された実施。 -/
  previousInSeries : Option (List (Performance Item)) := none
  priorClaims : Option (ClaimHistory Item) := none
  purposeClaims : Option (ClaimHistory Item) := none
  /-- D007(44)との併施確認、およびD015を主検査とする選択。 -/
  d007Partner : Option Bool := none
  d015Main : Option Bool := none
  atopyTarcOrSccaSameMonth : Option Bool := none
  atopyTarcOrSccaMain : Option Bool := none

def Context.item (c : Context) := c.performance.item

def Confirmed (c : Context) (f : Finding) : Prop := c.finding f = some true

def Uses (c : Context) (methods : List Method) : Prop := ∃ m ∈ methods, c.method = some m

def prior (c : Context) (history : Option (ClaimHistory Item)) (period : Period) : Option Nat :=
  history.bind fun h => count h ⟨c.performance.site.patient, none, period⟩ (· == c.item)

def Context.totalPrior (c : Context) := prior c c.priorClaims (Period.through c.performance.site.date)

def SeriesCount (c : Context) (n : Nat) : Prop :=
  c.performance.series.isSome = true ∧ ∃ records, c.previousInSeries = some records ∧
    (records.map Performance.id).Nodup ∧ records.length = n ∧
    ∀ r ∈ records, r.item = c.item ∧ r.id ≠ c.performance.id ∧
      c.performance.sameSeries r = some true

private def condition (n : Nat) (suffix pages : String) (p : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D015/paragraph/" ++ toString n ++ suffix, notice pages n, fun c _ => p c⟩

private def documentation (n : Nat) (suffix pages : String)
    (p : Context → (Remark → Prop) → Prop) : Rule Context (Remark → Prop) :=
  ⟨"notice/D015/paragraph/" ++ toString n ++ suffix, notice pages n, p⟩

def immunoglobulins := condition 1 "" "383" fun c => c.item = .immunoglobulin →
  ∃ target, c.immunoglobulin = some target

def Excludes (c : Context) (items : List Item)
    (related : Performance Item → Performance Item → Option Bool) : Prop :=
  ∃ records, c.otherSelected = some records ∧
    ∀ e ∈ records, e.item ∈ items → related c.performance e = some false

def saaChoice := condition 2 "" "383" fun c =>
  (c.item = .saa → Excludes c [.crpQual, .crp] (fun _ _ => some true)) ∧
  (c.item ∈ [.crpQual, .crp] → Excludes c [.saa] (fun _ _ => some true))

def transferrinMethod := condition 3 "" "383" fun c => c.item ∈ [.transferrin, .c3, .c4] →
  c.method = some .sridOrEquivalent

def electrophoresisItems : List Item := [.wholeAntiserum, .specificAntiserum, .drugImmunofixation]

def electrophoresisParagraph := condition 4 "" "384" fun c => c.item ∈ electrophoresisItems →
  c.performance.specimen.isSome = true

def electrophoresisOnce := condition 4 "/a" "384" fun c => c.item ∈ electrophoresisItems →
  Excludes c [c.item] Performance.sameSpecimen

def electrophoresisChoice := condition 4 "/i" "384" fun c => c.item ∈ electrophoresisItems →
  Excludes c (electrophoresisItems.filter (· != c.item)) Performance.sameSpecimen

theorem electrophoresisChoice_holds (c : Context) :
    electrophoresisChoice.holds c () ↔ (c.item ∈ electrophoresisItems →
      Excludes c (electrophoresisItems.filter (· != c.item)) Performance.sameSpecimen) :=
  Iff.rfl

def specificSerum := condition 4 "/u" "384" fun c => c.item = .specificAntiserum →
  Uses c [.immunoelectrophoresis, .immunofixation]

def drugImmunofixation := condition 4 "/e" "384" fun c => c.item = .drugImmunofixation →
  c.method = some .immunofixation ∧ Confirmed c .approvedAvoidsDaratumumabInterference ∧
    Confirmed c .treatedWithDaratumumab ∧ Confirmed c .myelomaOrAlResponse

def il6 := condition 5 "" "384" fun c => c.item = .il6 →
  Confirmed c .sirsSeverity ∧ (c.specimen = some .serum ∨ c.specimen = some .plasma) ∧
    Uses c [.eclia, .clia, .cleia] ∧
    ∃ n, SeriesCount c n ∧ (n < 2 ∨ Confirmed c .il6RepeatNecessary)

def il6Documentation := documentation 5 "" "384" fun c recorded => c.item = .il6 →
  recorded .il6Date ∧ (∀ n, SeriesCount c n → 2 ≤ n → recorded .il6DetailedReason)

def CovidRisk (c : Context) : Prop :=
  Confirmed c .covidConfirmed ∧ c.finding .respiratoryFailureManagement = some false

def tarcParagraph := condition 6 "" "384" fun c => c.item = .tarc →
  c.specimen = some .serum ∧ Confirmed c .serumTarcQuantified ∧
    (c.purpose = some .atopicSeverity ∨ c.purpose = some .drugSensitivityDifferential ∨ c.purpose = some .covidRisk)

def tarcAtopy := condition 6 "/a" "384" fun c =>
  c.item = .tarc → c.purpose = some .atopicSeverity →
    prior c c.purposeClaims (Period.month c.performance.site.date.month) = some 0

def tarcDrug := condition 6 "/i" "384" fun c =>
  c.item = .tarc → c.purpose = some .drugSensitivityDifferential →
    Confirmed c .drugHypersensitivitySuspected ∧
      ∃ n, SeriesCount c n ∧ (n = 0 ∨ Confirmed c .tarcRepeatNecessary)

def tarcDocumentation := documentation 6 "/i" "384" fun c recorded =>
  c.item = .tarc → c.purpose = some .drugSensitivityDifferential →
    ∀ n, SeriesCount c n → 0 < n → recorded .tarcDetailedReason

def tarcCovid := condition 6 "/u" "384" fun c =>
  c.item = .tarc → c.purpose = some .covidRisk → CovidRisk c ∧ SeriesCount c 0

def apr := condition 7 "" "384" fun c => c.item = .apr → Confirmed c .aprThreeMeasured

private def atopyAllergens : List Allergen :=
  [.dPteronyssinus, .dFarinae, .cat, .dog, .bermuda, .orchard, .ragweed, .mugwort,
    .birch, .cedar, .candida, .alternaria]

def atopyScreen := condition 8 "" "384" fun c => c.item = .atopyScreen →
  ∃ measured, c.allergens = some measured ∧ measured.Nodup ∧
    ∀ a, a ∈ measured ↔ a ∈ atopyAllergens

def fibronectin := condition 9 "" "384" fun c => c.item = .fibronectin →
  ∃ weeks, c.gestationalWeeks = some weeks ∧ 22 ≤ weeks ∧
    ((c.purpose = some .rupture ∧ weeks < 37) ∨ (c.purpose = some .threatenedPreterm ∧ weeks < 33))

def fibronectinChoice := condition 10 "" "385" fun c => c.item = .fibronectin →
  c.d007Partner = some false ∨ (c.d007Partner = some true ∧ c.d015Main = some true)

/-- D007(34)イとD015(10)へ、同じ併施判断と主検査の選択を渡す。 -/
inductive FibronectinRelation where
  | separate | mainD007 | mainD015

def applyFibronectinRelation (relation : FibronectinRelation) (d015 : Context)
    (d007 : BloodChemistryLate.Context) : Context × BloodChemistryLate.Context :=
  match relation with
  | .separate => ({ d015 with d007Partner := some false },
      { d007 with fibronectinSelection := some .separate })
  | .mainD007 => ({ d015 with d007Partner := some true, d015Main := some false },
      { d007 with fibronectinSelection := some (.selected .igfbp1Qualitative) })
  | .mainD015 => ({ d015 with d007Partner := some true, d015Main := some true },
      { d007 with fibronectinSelection := some .external })

def sccaParagraph := condition 11 "" "385" fun c => c.item = .scca2 → c.purpose = some .atopicSeverity

def sccaClinical := condition 11 "/a" "385" fun c => c.item = .scca2 →
  c.purpose = some .atopicSeverity ∧ c.method = some .elisa ∧
    (∃ age, c.ageYears = some age ∧ age ≤ 15) ∧
    prior c c.priorClaims (Period.month c.performance.site.date.month) = some 0

def sccaChoice := condition 11 "/i" "385" fun c =>
  c.item ∈ [.scca2, .tarc] → c.purpose = some .atopicSeverity →
    c.atopyTarcOrSccaSameMonth = some false ∨
      (c.atopyTarcOrSccaSameMonth = some true ∧ c.atopyTarcOrSccaMain = some true)

def lightChainParagraph := condition 12 "" "385" fun c => c.item = .lightChain →
  Confirmed c .evaluatesHypergammaglobulinemia

def lightChainClinical := condition 12 "/a" "385" fun c => c.item = .lightChain →
  c.method = some .nephelometry ∧ Confirmed c .evaluatesHypergammaglobulinemia

def lightChainChoice := condition 12 "/i" "385" fun c =>
  (c.item = .lightChain → Excludes c [.wholeAntiserum, .specificAntiserum] Performance.simultaneousWith) ∧
  (c.item ∈ [.wholeAntiserum, .specificAntiserum] → Excludes c [.lightChain] Performance.simultaneousWith)

def ifnParagraph := condition 13 "" "385" fun c => c.item = .ifnLambda3 → c.purpose = some .covidRisk

def ifnClinical := condition 13 "/a" "385" fun c => c.item = .ifnLambda3 →
  c.purpose = some .covidRisk ∧ CovidRisk c ∧ c.method = some .twoStepSandwichCleia

def ifnRepeat := condition 13 "/i" "385" fun c => c.item = .ifnLambda3 →
  c.totalPrior = some 0 ∨ (∃ n, c.totalPrior = some n ∧ 0 < n ∧ Confirmed c .ifnPreviousBelowThreshold)

def pregnancyParagraph := condition 14 "" "385" fun c => c.item = .sfltPlgf →
  Confirmed c .suspectedPreeclampsia

def pregnancyMethod := condition 14 "/a" "385" fun c => c.item = .sfltPlgf →
  c.specimen = some .serum ∧ c.method = some .eclia ∧ Confirmed c .sfltAndPlgfMeasuredAndRatioCalculated

def pressureRisk (c : Context) : Option Bool := do
  let systolic ← c.systolic
  let diastolic ← c.diastolic
  return decide (130 ≤ systolic ∨ 80 ≤ diastolic)

def risks (c : Context) : List (Option Bool) :=
  [pressureRisk c, c.finding .proteinuria, c.finding .preeclampsiaSigns,
    c.finding .fetalGrowthRestriction, c.finding .fetalGrowthRestrictionFindings]

def RiskCount (c : Context) (n : Nat) : Prop :=
  none ∉ risks c ∧ ((risks c).filter (· == some true)).length = n

inductive Risk where
  | pressure | proteinuria | signs | growthRestriction | growthRestrictionFindings

private def riskClassification (suffix : String) (risk : Risk) (value : Context → Option Bool) :
    Rule Context (Risk → Option Bool) :=
  ⟨"notice/D015/paragraph/14/i/" ++ suffix, notice "385" 14,
    fun c measured => c.item = .sfltPlgf → measured risk = value c⟩

def pressureRiskRule := riskClassification "i" .pressure pressureRisk
def proteinuriaRiskRule := riskClassification "ro" .proteinuria (·.finding .proteinuria)
def signsRiskRule := riskClassification "ha" .signs (·.finding .preeclampsiaSigns)
def growthRiskRule := riskClassification "ni" .growthRestriction (·.finding .fetalGrowthRestriction)
def growthFindingsRiskRule :=
  riskClassification "ho" .growthRestrictionFindings (·.finding .fetalGrowthRestrictionFindings)

def pregnancyClinical := condition 14 "/i" "385" fun c => c.item = .sfltPlgf →
  Confirmed c .suspectedPreeclampsia ∧ (∃ weeks, c.gestationalWeeks = some weeks ∧ 18 ≤ weeks ∧ weeks < 36) ∧
    ∃ count n, RiskCount c count ∧ 0 < count ∧ SeriesCount c n ∧
      ((count = 1 ∧ n = 0) ∨ Confirmed c .pregnancyExceptionNecessary)

def pregnancyDocumentation := documentation 14 "/u" "385" fun c recorded => c.item = .sfltPlgf →
  recorded .pregnancyRisk ∧
    ((Confirmed c .preeclampsiaSigns ∨ Confirmed c .fetalGrowthRestrictionFindings) → recorded .pregnancyRiskBasis) ∧
    (∀ n count, SeriesCount c n → RiskCount c count → (0 < n ∨ 2 ≤ count) → recorded .pregnancyDetailedReason)

def tuberculosis := condition 15 "" "386" fun c => c.item = .tuberculosis →
  Confirmed c .tuberculosisStronglySuspected ∨ Confirmed c .beforeBiologicAsRequiredByLabel

def tuberculosisClarification : Rule Context Unit :=
  ⟨"clarification/r08-03/question/9",
    ⟨.clarification, "疑義解釈資料の送付について（その3）", "2026-04-20",
      "別添1 PDF4頁 問9", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001693874.pdf"⟩,
    fun c _ => c.item = .tuberculosis → Confirmed c .beforeBiologicAsRequiredByLabel →
      tuberculosis.holds c ()⟩

def concizumab := condition 16 "" "386" fun c => c.item = .concizumab →
  c.method = some .elisa ∧ Confirmed c .congenitalHemophiliaOnConcizumab ∧
    Confirmed c .determinesConcizumabDose ∧
    (c.totalPrior = some 0 ∨ (∃ n, c.totalPrior = some n ∧ 0 < n ∧ Confirmed c .concizumabRepeatNecessary))

def concizumabDocumentation := documentation 16 "" "386" fun c recorded =>
  c.item = .concizumab → (∃ n, c.totalPrior = some n ∧ 0 < n) → recorded .concizumabReason

def eligibilityRules :=
  [immunoglobulins, saaChoice, transferrinMethod, electrophoresisParagraph, electrophoresisOnce,
   electrophoresisChoice, specificSerum, drugImmunofixation, il6, tarcParagraph, tarcAtopy,
   tarcDrug, tarcCovid, apr, atopyScreen, fibronectin, fibronectinChoice, sccaParagraph,
   sccaClinical, sccaChoice, lightChainParagraph, lightChainClinical, lightChainChoice,
   ifnParagraph, ifnClinical, ifnRepeat, pregnancyParagraph, pregnancyMethod, pregnancyClinical,
   tuberculosis, tuberculosisClarification, concizumab]

def documentationRules :=
  [il6Documentation, tarcDocumentation, pregnancyDocumentation, concizumabDocumentation]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()
def PermitsRate (c : Context) (p : Nat) : Prop := Eligible c ∧ Satisfies rates c.item p

def legacyRequest (i : Item) : SpecimenTests.Request :=
  { code := .d015, number := i.number, variant := i.variant }

theorem legacy_rate (i : Item) :
    SpecimenTests.assessOne (legacyRequest i) = some (.charged i.points 0) := by
  cases i <;> decide

theorem legacy_iff (c : Context) (p : Nat) :
    PermitsRate c p ↔ Eligible c ∧
      SpecimenTests.assessOne (legacyRequest c.item) = some (.charged p 0) := by
  simp [PermitsRate, rate_iff, legacy_rate, eq_comm]

theorem determines (c : Context) (h : Eligible c) :
    (∃ p, PermitsRate c p) ∧ (∀ p q, PermitsRate c p → PermitsRate c q → p = q) :=
  ⟨⟨c.item.points, h, (rate_iff _ _).mpr rfl⟩, fun _ _ hp hq =>
    ((rate_iff _ _).mp hp.2).trans ((rate_iff _ _).mp hq.2).symm⟩

structure IgeDraw where
  anchor : Performance Item
  tests : List (Performance Item × Nat)

def IgeDraw.Assessed (g : IgeDraw) : Prop :=
  g.tests ≠ [] ∧ (g.tests.map Prod.snd).Nodup ∧
    ∀ row ∈ g.tests, row.1.item = .specificIge ∧ g.anchor.sameDraw row.1 = some true

def IgeDraw.uncapped (g : IgeDraw) := 110 * g.tests.length

def igeCapPoints : Nat := 1430

def igeCap : Rule IgeDraw Nat :=
  ⟨"primary/D015/item/13/note", primary "13 注", fun g p =>
    (g.uncapped ≤ igeCapPoints → p = g.uncapped) ∧
      (igeCapPoints ≤ g.uncapped → p = igeCapPoints)⟩

def igeRules := [igeCap]

theorem ige_legacy_iff (g : IgeDraw) (p : Nat) :
    Satisfies igeRules g p ↔ p = SpecimenTests.groupedBase .specificIgE g.tests.length 0 := by
  simp only [igeRules, satisfies_cons, satisfies_nil, and_true, igeCap,
    SpecimenTests.groupedBase, IgeDraw.uncapped, igeCapPoints]
  by_cases h : 110 * g.tests.length ≤ 1430
  · rw [Nat.min_eq_right h]
    omega
  · rw [Nat.min_eq_left (by omega)]
    omega

theorem ige_determines : DeterminesOn IgeDraw.Assessed igeRules := by
  intro g _
  let p := SpecimenTests.groupedBase .specificIgE g.tests.length 0
  exact ⟨⟨p, (ige_legacy_iff _ _).mpr rfl⟩, fun _ _ hx hy =>
    ((ige_legacy_iff _ _).mp hx).trans ((ige_legacy_iff _ _).mp hy).symm⟩

def judgmentTest (i : Item) (specialistWrittenReport : Bool) : SpecimenJudgment.Test :=
  { major := 15, number := i.number, variant := i.variant, ordinaryCategory := .immunological
    specialistWrittenReport := specialistWrittenReport &&
      decide (i = .wholeAntiserum ∨ i = .specificAntiserum ∨ i = .drugImmunofixation) }

def execution (kind : Nat) (c : Context) (p : Nat) (_ : PermitsRate c p) :
    Examinations.SpecimenItem :=
  { kind := kind, executionPoints := p }

def igeExecution (kind : Nat) (g : IgeDraw) (p : Nat) (_ : g.Assessed)
    (_ : Satisfies igeRules g p) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := p }

/-- D001の準用について、D015で求めた所定点数を既存の準用評価へ渡す。 -/
def urineReference (urine : UrineFecalTests.Context) (i : Item) (p : Nat)
    (_ : Satisfies rates i p) : Option UrineFecalTests.Assessment :=
  match UrineFecalTests.pointRule urine.item with
  | .reference .d015 false =>
    UrineFecalTests.assess { urine with referenceResolution := some ⟨.d015, p, false⟩ }
  | _ => none

private def sample (i : Item) : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, i, some 1, none, none, none⟩ }

example : PermitsRate { sample .fibronectin with
    purpose := some .rupture
    gestationalWeeks := some 22
    d007Partner := some false } 204 := by
  refine ⟨?_, (rate_iff _ _).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, condition, Context.item, sample,
    immunoglobulins, saaChoice, transferrinMethod, electrophoresisParagraph, electrophoresisOnce,
    electrophoresisChoice, specificSerum, drugImmunofixation, il6, tarcParagraph, tarcAtopy,
    tarcDrug, tarcCovid, apr, atopyScreen, fibronectin, fibronectinChoice, sccaParagraph,
    sccaClinical, sccaChoice, lightChainParagraph, lightChainClinical, lightChainChoice,
    ifnParagraph, ifnClinical, ifnRepeat, pregnancyParagraph, pregnancyMethod, pregnancyClinical,
    tuberculosis, tuberculosisClarification, concizumab, electrophoresisItems]

example : ¬ fibronectin.holds { sample .fibronectin with
    purpose := some .rupture, gestationalWeeks := some 37 } () := by
  simp [fibronectin, condition, Context.item, sample]

example : Satisfies igeRules ⟨(sample .specificIge).performance,
    (List.range 14).map fun n => ((sample .specificIge).performance, n)⟩ 1430 :=
  (ige_legacy_iff _ _).mpr rfl

end Sanri.MedicalFee.D015
