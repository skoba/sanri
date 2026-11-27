import Sanri.History
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D006Profiling

open Sanri.Logic Sanri.History

inductive Item where
  | solid | hematologic
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.solid, .hematologic]

def Item.number : Item → Nat
  | .solid => 1
  | .hematologic => 2

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem item_range (n : Nat) : (∃ i, ItemAt n i) ↔ n = 1 ∨ n = 2 := by
  constructor
  · rintro ⟨i, rfl⟩
    cases i <;> simp [Item.number]
  · rintro (rfl | rfl)
    · exact ⟨.solid, rfl⟩
    · exact ⟨.hematologic, rfl⟩

def points : Nat := 44000

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 19, number := i.number, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

inductive Specimen where
  | solidCells | hematologicCells | blood | marrow | cavityFluid
  deriving DecidableEq

inductive Disease where
  | aml | all | mds | myeloproliferative | histiocyticDendritic
  | aggressiveB | indolentB | tCell | nkCell | myeloma | phPositiveAll | cll | unexplainedCytopenia
  deriving DecidableEq

inductive Indication where
  | initial | initialDifficult | relapsedOrRefractory | relapsedOrRefractoryDifficult | undiagnosed
  deriving DecidableEq

inductive Cancer where
  | lung | colorectal | breast | solid | melanoma | biliary | ovarian | prostate | nonLungSolid
  deriving DecidableEq

inductive Marker where
  | egfr | ros1Fusion | alkFusion | ras | her2 | braf | msi | metEx14 | ntrkFusion | tmb
  | retFusion | fgfr2Fusion | brca1And2 | akt1 | pik3ca | pten | esr1
  deriving DecidableEq

structure EarlierTest where
  cancer : Cancer
  marker : Marker
  date : Date
  points : Nat
  treatmentSelection : Option Bool := none
  profileObtainedTogether : Option Bool := none
  afterStandardTreatmentOrExpectedCompletion : Option Bool := none
  expertPanelReviewed : Option Bool := none
  writtenExplanation : Option Bool := none

inductive Prior where
  | solidCells | solidBlood | hematologic (diseaseId : Nat)
  deriving DecidableEq

inductive Path where
  | submission | deduction (test : EarlierTest)

structure Context where
  site : Site
  item : Item
  path : Option Path := none
  specimen : Option Specimen := none
  facilityComplies : Option Bool := none
  facilityNotified : Option Bool := none
  approvedOrCertifiedNgs : Option Bool := none
  coveredGenes : Option Nat := none
  comprehensiveProfiling : Option Bool := none
  atSubmission : Option Bool := none
  prior : Option (ClaimHistory Prior) := none
  medicalDifficultyWithTissue : Option Bool := none
  earlierTissueFailed : Option Bool := none
  noStandardTreatment : Option Bool := none
  locallyAdvancedOrMetastatic : Option Bool := none
  standardTreatmentEndedOrExpected : Option Bool := none
  likelyChemotherapyPerGuidelines : Option Bool := none
  b011_5FromEarlierResult : Option Bool := none
  ccAtSubmissionConsent : Option Bool := none
  ccAtSecondaryUseConsent : Option Bool := none
  ccAtDataSent : Option Bool := none
  writtenConsentExplanation : Option Bool := none
  privacyLawCompliance : Option Bool := none
  consentProcedureFollowed : Option Bool := none
  disease : Option Disease := none
  diseaseId : Option Nat := none
  indication : Option Indication := none
  conventionalSearchUnavailable : Option Bool := none
  differentialDiagnosisDifficult : Option Bool := none
  noDefinitiveDiagnosis : Option Bool := none
  treatmentDecisionDifficult : Option Bool := none

def priorCount (c : Context) (accepts : Prior → Bool) : Option Nat :=
  c.prior.bind fun h => count h ⟨c.site.patient, none, Period.through c.site.date⟩ accepts

def IsSolidPrior : Prior → Bool
  | .solidCells | .solidBlood => true
  | .hematologic _ => false

def Technology (c : Context) : Prop :=
  c.approvedOrCertifiedNgs = some true ∧
  (∃ n, c.coveredGenes = some n ∧ 100 ≤ n) ∧ c.comprehensiveProfiling = some true

def Facility (c : Context) : Prop := c.facilityComplies = some true ∧ c.facilityNotified = some true

def SolidPatient (c : Context) : Prop :=
  (c.noStandardTreatment = some true ∨
    (c.locallyAdvancedOrMetastatic = some true ∧ c.standardTreatmentEndedOrExpected = some true)) ∧
  c.likelyChemotherapyPerGuidelines = some true

def CcatProcedure (c : Context) : Prop :=
  c.writtenConsentExplanation = some true ∧ c.privacyLawCompliance = some true

def CcatDisposition (c : Context) : Prop :=
  (c.ccAtSubmissionConsent = some true ∧ c.ccAtSecondaryUseConsent = some true ∧
    c.ccAtDataSent = some true) ∨
  c.ccAtSubmissionConsent = some false ∨ c.ccAtSecondaryUseConsent = some false

def AddedAlkTest (t : EarlierTest) : Prop :=
  (t.cancer ∈ [.colorectal, .breast, .melanoma, .biliary, .ovarian, .prostate, .nonLungSolid] ∧
    t.marker = .alkFusion)

def Deduction (c : Context) (t : EarlierTest) : Prop :=
  (c.specimen = some .solidCells ∨ c.specimen = some .blood) ∧ Technology c ∧
  t.treatmentSelection = some true ∧ t.profileObtainedTogether = some true ∧
  t.afterStandardTreatmentOrExpectedCompletion = some true ∧ t.expertPanelReviewed = some true ∧
  t.writtenExplanation = some true ∧ t.date.key ≤ c.site.date.key

def Difficult (c : Context) : Prop :=
  c.conventionalSearchUnavailable = some true ∨ c.differentialDiagnosisDifficult = some true

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF178頁 D006-19 " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

/-- カの各枝は先行検査の該当範囲を記述する。どれか一つで足りる。
この型のがん分類はすべて固形癌の範囲内。 -/
def earlierRule1 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/1", notice "PDF348頁 D006-19(1)カ①",
    fun t _ => t.cancer = .lung ∧ t.marker ∈ [.egfr, .ros1Fusion, .alkFusion, .ras, .her2]⟩

def earlierRule2 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/2", notice "PDF348頁 D006-19(1)カ②",
    fun t _ => t.cancer = .colorectal ∧ t.marker ∈ [.ras, .her2, .braf]⟩

def earlierRule3 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/3", notice "PDF348頁 D006-19(1)カ③",
    fun t _ => t.cancer = .breast ∧ t.marker = .her2⟩

def earlierRule4 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/4", notice "PDF348頁 D006-19(1)カ④",
    fun t _ => t.marker = .msi⟩

def earlierRule5 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/5", notice "PDF348頁 D006-19(1)カ⑤",
    fun t _ => t.cancer = .lung ∧ t.marker = .metEx14⟩

def earlierRule6 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/6", notice "PDF348頁 D006-19(1)カ⑥",
    fun t _ => t.cancer = .melanoma ∧ t.marker = .braf⟩

def earlierRule7 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/7", notice "PDF348頁 D006-19(1)カ⑦",
    fun t _ => t.marker ∈ [.ntrkFusion, .tmb, .retFusion]⟩

def earlierRule8 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/8", notice "PDF348頁 D006-19(1)カ⑧",
    fun t _ => t.cancer = .biliary ∧ t.marker = .fgfr2Fusion⟩

def earlierRule9 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/9", notice "PDF348頁 D006-19(1)カ⑨",
    fun t _ => t.cancer ∈ [.ovarian, .prostate] ∧ t.marker = .brca1And2⟩

def earlierRule10 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/10", notice "PDF348頁 D006-19(1)カ⑩",
    fun t _ => t.cancer = .breast ∧ t.marker ∈ [.akt1, .pik3ca, .pten]⟩

def earlierRule11 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/11", notice "PDF348頁 D006-19(1)カ⑪",
    fun t _ => t.marker = .her2⟩

def earlierRule12 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/12", notice "PDF348頁 D006-19(1)カ⑫",
    fun t _ => t.cancer = .breast ∧ t.marker = .esr1⟩

def earlierTestRules : List (Rule EarlierTest Unit) :=
  [earlierRule1, earlierRule2, earlierRule3, earlierRule4, earlierRule5, earlierRule6,
    earlierRule7, earlierRule8, earlierRule9, earlierRule10, earlierRule11, earlierRule12]

def ListedEarlierTest (t : EarlierTest) : Prop :=
  ∃ rule ∈ earlierTestRules, rule.holds t ()

def earlierRule13 : Rule EarlierTest Unit :=
  ⟨"notice/D006-19/paragraph/1/ka/13",
    ⟨.notification, "保医発0430第4号・05-18差替版", "2026-06-01適用",
      "PDF10頁 D006-19(1)カ⑬", .checkedAgainstSource,
      some "https://kouseikyoku.mhlw.go.jp/kantoshinetsu/080525_016.pdf"⟩,
    fun t _ => AddedAlkTest t⟩

def ListedDeduction (t : EarlierTest) : Prop :=
  ListedEarlierTest t ∨ earlierRule13.holds t ()

def tissueDifficultyRule : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/1/a/i", notice "PDF347頁 D006-19(1)ア(イ)",
    fun c _ => c.medicalDifficultyWithTissue = some true ∧ priorCount c IsSolidPrior = some 0⟩

def tissueFailureRule : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/1/a/ro", notice "PDF347頁 D006-19(1)ア(ロ)",
    fun c _ => c.earlierTissueFailed = some true ∧ priorCount c IsSolidPrior = some 1 ∧
      priorCount c (· == .solidCells) = some 1⟩

def hematologic_i_1 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/i/1", notice "PDF348頁 D006-19(2)ア(イ)①",
    fun c _ => c.disease = some .aml⟩

def hematologic_i_2 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/i/2", notice "PDF348頁 D006-19(2)ア(イ)②",
    fun c _ => c.disease = some .all⟩

def hematologic_i_3 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/i/3", notice "PDF348頁 D006-19(2)ア(イ)③",
    fun c _ => c.disease = some .mds⟩

def hematologic_i_4 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/i/4", notice "PDF349頁 D006-19(2)ア(イ)④",
    fun c _ => c.disease = some .myeloproliferative⟩

def hematologic_i_5 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/i/5", notice "PDF349頁 D006-19(2)ア(イ)⑤",
    fun c _ => c.disease = some .histiocyticDendritic⟩

def hematologic_i_diseases : List (Rule Context Unit) :=
  [hematologic_i_1, hematologic_i_2, hematologic_i_3, hematologic_i_4, hematologic_i_5]

def hematologic_i : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/i", notice "PDF348–349頁 D006-19(2)ア(イ)",
    fun c _ => c.indication = some .initial ∧ ∃ rule ∈ hematologic_i_diseases, rule.holds c ()⟩

def hematologic_ro_1 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ro/1", notice "PDF349頁 D006-19(2)ア(ロ)①",
    fun c _ => c.disease = some .aggressiveB⟩

def hematologic_ro_2 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ro/2", notice "PDF349頁 D006-19(2)ア(ロ)②",
    fun c _ => c.disease = some .indolentB⟩

def hematologic_ro_3 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ro/3", notice "PDF349頁 D006-19(2)ア(ロ)③",
    fun c _ => c.disease = some .tCell⟩

def hematologic_ro_4 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ro/4", notice "PDF349頁 D006-19(2)ア(ロ)④",
    fun c _ => c.disease = some .nkCell⟩

def hematologic_ro_5 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ro/5", notice "PDF349頁 D006-19(2)ア(ロ)⑤",
    fun c _ => c.disease = some .myeloma⟩

def hematologic_ro_diseases : List (Rule Context Unit) :=
  [hematologic_ro_1, hematologic_ro_2, hematologic_ro_3, hematologic_ro_4, hematologic_ro_5]

def hematologic_ro : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ro", notice "PDF349頁 D006-19(2)ア(ロ)",
    fun c _ => c.indication = some .initialDifficult ∧ Difficult c ∧ ∃ rule ∈ hematologic_ro_diseases, rule.holds c ()⟩

def hematologic_ha : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ha", notice "PDF349頁 D006-19(2)ア(ハ)",
    fun c _ => c.indication = some .relapsedOrRefractory ∧ c.disease = some .aml⟩

def hematologic_ni_1 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ni/1", notice "PDF349頁 D006-19(2)ア(ニ)①",
    fun c _ => c.disease = some .phPositiveAll⟩

def hematologic_ni_2 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ni/2", notice "PDF349頁 D006-19(2)ア(ニ)②",
    fun c _ => c.disease = some .indolentB⟩

def hematologic_ni_3 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ni/3", notice "PDF349頁 D006-19(2)ア(ニ)③",
    fun c _ => c.disease = some .tCell⟩

def hematologic_ni_4 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ni/4", notice "PDF349頁 D006-19(2)ア(ニ)④",
    fun c _ => c.disease = some .nkCell⟩

def hematologic_ni_5 : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ni/5", notice "PDF349頁 D006-19(2)ア(ニ)⑤",
    fun c _ => c.disease = some .cll⟩

def hematologic_ni_diseases : List (Rule Context Unit) :=
  [hematologic_ni_1, hematologic_ni_2, hematologic_ni_3, hematologic_ni_4, hematologic_ni_5]

def hematologic_ni : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ni", notice "PDF349頁 D006-19(2)ア(ニ)",
    fun c _ => c.indication = some .relapsedOrRefractoryDifficult ∧ Difficult c ∧ ∃ rule ∈ hematologic_ni_diseases, rule.holds c ()⟩

def hematologic_ho : Rule Context Unit :=
  ⟨"notice/D006-19/paragraph/2/a/ho", notice "PDF349頁 D006-19(2)ア(ホ)",
    fun c _ => c.indication = some .undiagnosed ∧ c.noDefinitiveDiagnosis = some true ∧
      c.treatmentDecisionDifficult = some true ∧ c.disease = some .unexplainedCytopenia⟩

def HematologicPatient (c : Context) : Prop :=
  hematologic_i.holds c () ∨ hematologic_ro.holds c () ∨ hematologic_ha.holds c () ∨
    hematologic_ni.holds c () ∨ hematologic_ho.holds c ()

def SolidSubmission (c : Context) : Prop :=
  c.atSubmission = some true ∧ Technology c ∧
  ((c.specimen = some .solidCells ∧ priorCount c IsSolidPrior = some 0) ∨
   (c.specimen = some .blood ∧
    (tissueDifficultyRule.holds c () ∨ tissueFailureRule.holds c ())))

def HematologicSubmission (c : Context) : Prop :=
  c.atSubmission = some true ∧ Technology c ∧
  (∃ s ∈ [Specimen.hematologicCells, .blood, .marrow, .cavityFluid], c.specimen = some s) ∧
  (∃ id, c.diseaseId = some id ∧ priorCount c (· == .hematologic id) = some 0) ∧ HematologicPatient c

def solidRate : Rule Context Nat :=
  ⟨"primary/D006-19/item/1", primary "1",
    fun c p => c.item = .solid → c.path = some .submission → p = 44000⟩

def hematologicRate : Rule Context Nat :=
  ⟨"primary/D006-19/item/2", primary "2",
    fun c p => c.item = .hematologic → c.path = some .submission → p = 44000⟩

def facilityRule : Rule Context Nat :=
  ⟨"primary/D006-19/note/1", primary "注1", fun c _ => Facility c⟩

def deductionRate : Rule Context Nat :=
  ⟨"primary/D006-19/note/2", primary "注2", fun c p =>
    (c.path = some .submission → c.b011_5FromEarlierResult = some false) ∧
    (∀ t, c.path = some (.deduction t) → c.b011_5FromEarlierResult = some true ∧
      p + t.points = 44000)⟩

def solidPathRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1", notice "PDF347–348頁 D006-19(1)",
    fun c _ => c.item = .solid → ∃ path, c.path = some path⟩

def solidRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1/a", notice "PDF347頁 D006-19(1)ア",
    fun c _ => c.item = .solid → c.path = some .submission → SolidSubmission c⟩

def solidPatientRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1/i", notice "PDF347頁 D006-19(1)イ",
    fun c _ => c.item = .solid → SolidPatient c⟩

def ccatProcedureRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1/u", notice "PDF347頁 D006-19(1)ウ",
    fun c _ => CcatProcedure c⟩

def ccatDispositionRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1/e", notice "PDF347–348頁 D006-19(1)エ",
    fun c _ => CcatDisposition c⟩

def consentRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1/o", notice "PDF348頁 D006-19(1)オ",
    fun c _ => c.consentProcedureFollowed = some true⟩

def solidDeductionRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1/ka", notice "PDF348頁 D006-19(1)カ",
    fun c _ => ∀ t, c.path = some (.deduction t) → c.item = .solid ∧ Deduction c t⟩

def listedDeductionRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/1/ka", notice "PDF348頁 D006-19(1)カ",
    fun c _ => ∀ t, c.path = some (.deduction t) → ListedDeduction t⟩

def hematologicPathRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/2", notice "PDF348–349頁 D006-19(2)",
    fun c _ => c.item = .hematologic → c.path = some .submission⟩

def hematologicRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/2/a", notice "PDF348–349頁 D006-19(2)ア",
    fun c _ => c.item = .hematologic → c.path = some .submission ∧ HematologicSubmission c⟩

def hematologicConsentRule : Rule Context Nat :=
  ⟨"notice/D006-19/paragraph/2/i", notice "PDF349頁 D006-19(2)イ",
    fun c _ => c.item = .hematologic →
      CcatProcedure c ∧ CcatDisposition c ∧ c.consentProcedureFollowed = some true⟩

inductive Entry where
  | tissueDifficulty | tissueFailure | consentStatus | noConsent | medicalNecessity
  | earlierTestDate (date : Date)

structure Documentation where
  chart : Entry → Prop
  registry : Entry → Prop
  claimRemarks : Entry → Prop

def tissueDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-19/paragraph/1/a", notice "PDF347頁 D006-19(1)ア 記載",
    fun c d => c.item = .solid → c.path = some .submission → c.specimen = some .blood →
      (priorCount c IsSolidPrior = some 0 → d.chart .tissueDifficulty ∧ d.claimRemarks .tissueDifficulty) ∧
      (priorCount c IsSolidPrior = some 1 → d.chart .tissueFailure ∧ d.claimRemarks .tissueFailure)⟩

def consentDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-19/paragraph/1/u", notice "PDF347頁 D006-19(1)ウ 記載",
    fun _ d => d.chart .consentStatus ∧ d.registry .consentStatus⟩

def refusalDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-19/paragraph/1/e", notice "PDF347–348頁 D006-19(1)エ 記載",
    fun c d => c.ccAtSubmissionConsent = some false ∨ c.ccAtSecondaryUseConsent = some false →
      d.chart .noConsent ∧ d.registry .noConsent⟩

def deductionDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-19/paragraph/1/ka", notice "PDF348頁 D006-19(1)カ 記載",
    fun c d => ∀ t, c.path = some (.deduction t) → d.claimRemarks (.earlierTestDate t.date)⟩

def hematologicDocumentation : Rule Context Documentation :=
  ⟨"notice/D006-19/paragraph/2/a", notice "PDF348頁 D006-19(2)ア 記載",
    fun c d => c.item = .hematologic →
      (∃ i ∈ [Indication.initialDifficult, .relapsedOrRefractoryDifficult, .undiagnosed],
        c.indication = some i) → d.claimRemarks .medicalNecessity⟩

def rules : List (Rule Context Nat) :=
  [solidRate, hematologicRate, facilityRule, deductionRate, solidPathRule, solidRule, solidPatientRule,
    ccatProcedureRule, ccatDispositionRule, consentRule, solidDeductionRule, listedDeductionRule,
    hematologicPathRule, hematologicRule, hematologicConsentRule]

def Eligible (c : Context) : Prop :=
  Facility c ∧ CcatProcedure c ∧ CcatDisposition c ∧ c.consentProcedureFollowed = some true ∧
  ((c.path = some .submission ∧ c.b011_5FromEarlierResult = some false ∧
    ((c.item = .solid ∧ SolidSubmission c ∧ SolidPatient c) ∨
     (c.item = .hematologic ∧ HematologicSubmission c))) ∨
   (∃ t, c.path = some (.deduction t) ∧ c.item = .solid ∧ SolidPatient c ∧
    Deduction c t ∧ ListedDeduction t ∧ c.b011_5FromEarlierResult = some true ∧ t.points ≤ 44000))

theorem no_result_without_path (c : Context) (h : c.path = none) : ¬ SatisfiableAt rules c := by
  rintro ⟨p, hp⟩
  cases i : c.item
  · obtain ⟨_, path⟩ := hp solidPathRule (by simp [rules]) i
    simp [h] at path
  · have path := (hp hematologicRule (by simp [rules]) i).1
    simp [h] at path

private theorem submission_iff (c : Context) (p : Nat) (h : c.path = some .submission) :
    Satisfies rules c p ↔ p = points ∧ Eligible c := by
  cases i : c.item <;>
    simp [rules, satisfies_cons, satisfies_nil, solidRate, hematologicRate, facilityRule,
      deductionRate, solidPathRule, solidRule, solidPatientRule, ccatProcedureRule, ccatDispositionRule,
      consentRule, solidDeductionRule, listedDeductionRule, hematologicPathRule, hematologicRule, hematologicConsentRule,
      Eligible, points, h, i, and_comm, and_left_comm, and_assoc]

private theorem deduction_iff (c : Context) (t : EarlierTest) (p : Nat)
    (h : c.path = some (.deduction t)) :
    Satisfies rules c p ↔ p + t.points = points ∧ Eligible c := by
  cases i : c.item
  · simp [rules, satisfies_cons, satisfies_nil, solidRate, hematologicRate, facilityRule,
      deductionRate, solidPathRule, solidRule, solidPatientRule, ccatProcedureRule, ccatDispositionRule,
      consentRule, solidDeductionRule, listedDeductionRule, hematologicPathRule, hematologicRule, hematologicConsentRule,
      Eligible, points, h, i]
    constructor
    · intro h
      obtain ⟨f, ⟨b, eq⟩, s, proc, disp, cons, d, listed⟩ := h
      exact ⟨eq, f, proc, disp, cons, s, d, listed, b, by omega⟩
    · rintro ⟨eq, f, proc, disp, cons, s, d, listed, b, _⟩
      exact ⟨f, ⟨b, eq⟩, s, proc, disp, cons, d, listed⟩
  · simp [rules, satisfies_cons, satisfies_nil, hematologicPathRule, Eligible, h, i]

theorem determines : DeterminesOn Eligible rules := by
  intro c hc
  rcases hc.2.2.2.2 with ⟨h, _, _⟩ | ⟨t, h, _, _, _, _, _, le⟩
  · exact ⟨⟨points, (submission_iff _ _ h).mpr ⟨rfl, hc⟩⟩,
      fun a b ha hb => ((submission_iff _ _ h).mp ha).1.trans ((submission_iff _ _ h).mp hb).1.symm⟩
  · refine ⟨⟨points - t.points, (deduction_iff _ _ _ h).mpr ⟨?_, hc⟩⟩, ?_⟩
    · unfold points
      omega
    · intro a b ha hb
      have ea := ((deduction_iff _ _ _ h).mp ha).1
      have eb := ((deduction_iff _ _ _ h).mp hb).1
      omega

private def site : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def solidExample : Context :=
  { site, item := .solid, path := some .submission, specimen := some .solidCells
    facilityComplies := some true, facilityNotified := some true
    approvedOrCertifiedNgs := some true, coveredGenes := some 100, comprehensiveProfiling := some true
    atSubmission := some true
    prior := some ⟨⟨⟨site.patient, none, Period.through site.date⟩, []⟩, by simp⟩
    noStandardTreatment := some true, likelyChemotherapyPerGuidelines := some true
    b011_5FromEarlierResult := some false, writtenConsentExplanation := some true
    privacyLawCompliance := some true, consentProcedureFollowed := some true
    ccAtSubmissionConsent := some false }

example : Satisfies rules solidExample 44000 := by
  refine (submission_iff _ _ rfl).mpr ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    Or.inr (Or.inl rfl), rfl, Or.inl ⟨rfl, rfl, Or.inl ⟨rfl, ?_, ?_⟩⟩⟩
  · exact ⟨rfl, ⟨rfl, ⟨100, rfl, by decide⟩, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl rfl, rfl⟩

example : ¬ SatisfiableAt rules { solidExample with facilityNotified := some false } := by
  rintro ⟨p, hp⟩
  have h := ((submission_iff _ _ rfl).mp hp).2.1.2
  cases h

example : ¬ SatisfiableAt rules { solidExample with prior := none } := by
  rintro ⟨p, hp⟩
  have h := ((submission_iff _ _ rfl).mp hp).2.2.2.2.2
  simp [SolidSubmission, priorCount, solidExample] at h

private def earlierAlk : EarlierTest :=
  { cancer := .nonLungSolid, marker := .alkFusion, date := site.date, points := 2500
    treatmentSelection := some true, profileObtainedTogether := some true
    afterStandardTreatmentOrExpectedCompletion := some true, expertPanelReviewed := some true
    writtenExplanation := some true }

private def deductionExample : Context :=
  { solidExample with path := some (.deduction earlierAlk), b011_5FromEarlierResult := some true }

example : Satisfies rules deductionExample 41500 := by
  refine (deduction_iff _ _ _ rfl).mpr ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, Or.inr (Or.inl rfl), rfl,
    Or.inr ⟨earlierAlk, rfl, rfl, ⟨Or.inl rfl, rfl⟩, ?_, Or.inr ?_, rfl, by decide⟩⟩
  · exact ⟨Or.inl rfl, ⟨rfl, ⟨100, rfl, by decide⟩, rfl⟩, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  · simp [earlierRule13, AddedAlkTest, earlierAlk]

private def hematologicExample : Context :=
  { solidExample with
    item := .hematologic
    specimen := some .marrow
    disease := some .aml
    diseaseId := some 1
    indication := some .initial }

example : Satisfies rules hematologicExample 44000 := by
  refine (submission_iff _ _ rfl).mpr ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, Or.inr (Or.inl rfl),
    rfl, Or.inl ⟨rfl, rfl, Or.inr ⟨rfl, rfl, ⟨rfl, ⟨100, rfl, by decide⟩, rfl⟩,
      ⟨.marrow, by simp, rfl⟩, ⟨1, rfl, rfl⟩, Or.inl ⟨rfl, hematologic_i_1, by simp [hematologic_i_diseases], rfl⟩⟩⟩⟩

end Sanri.MedicalFee.D006Profiling
