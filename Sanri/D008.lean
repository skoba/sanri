import Sanri.D004
import Sanri.BloodChemistryLate

/-! D008、令和8年度の2026-10-22外来。個別の適格性と検体をまとめた実施料を扱う。 -/
namespace Sanri.MedicalFee.D008

open Sanri.Logic Sanri.History

inductive Item where
  | hcgQualitative
  | ohcs11
  | hva
  | vma
  | hiaa5
  | prolactin | tsh
  | t3
  | reninActivity | insulin
  | reninQuantitative
  | growthHormone
  | t4
  | fsh | cPeptide | lh
  | testosterone
  | ft4 | ft3 | cortisol
  | aldosterone
  | calcitonin
  | thyroglobulin
  | hcgBeta
  | tbg | bnp | hcgQuantitative | hcgSemiquantitative
  | antiGad
  | ntProBnp
  | tbc
  | progesterone
  | glucagon | ucOc
  | ntx | osteocalcin
  | tracp5b | freeTestosterone
  | bap
  | pinp
  | pth | catecholamineFractions | camp
  | intactPinp
  | dheaS
  | hcgLowUnitSemiquantitative
  | estradiol
  | urineBetaCtx
  | betaCtx
  | estriol | estrogenSemiquantitative | estrogenQuantitative | cPthrp
  | acth | catecholamine
  | pthrp
  | urineDpd
  | kgs17
  | erythropoietin
  | somatomedinC
  | ks17Fractions | ohp17Alpha | antiIa2 | pregnanediol
  | metanephrine
  | kgs17Fractions | metanephrineFractions
  | anp
  | adh
  | pregnanetriol
  | normetanephrine
  | igfbp3
  | gastrin
  | freeMetanephrineFractions
  | amh
  | leptin
  deriving DecidableEq, Repr

def ledgerItems : List Item :=
  [.hcgQualitative, .ohcs11, .hva, .vma,
    .hiaa5, .prolactin, .tsh, .t3, .reninActivity, .insulin,
    .reninQuantitative, .growthHormone, .t4, .fsh, .cPeptide, .lh,
    .testosterone, .ft4, .ft3, .cortisol, .aldosterone, .calcitonin,
    .thyroglobulin, .hcgBeta, .tbg, .bnp, .hcgQuantitative, .hcgSemiquantitative, .antiGad,
    .ntProBnp, .tbc, .progesterone, .glucagon, .ucOc,
    .ntx, .osteocalcin, .tracp5b, .freeTestosterone, .bap, .pinp,
    .pth, .catecholamineFractions, .camp, .intactPinp, .dheaS, .hcgLowUnitSemiquantitative,
    .estradiol, .urineBetaCtx, .betaCtx, .estriol, .estrogenSemiquantitative, .estrogenQuantitative, .cPthrp,
    .acth, .catecholamine, .pthrp, .urineDpd, .kgs17,
    .erythropoietin, .somatomedinC, .ks17Fractions, .ohp17Alpha, .antiIa2, .pregnanediol, .metanephrine,
    .kgs17Fractions, .metanephrineFractions, .anp, .adh, .pregnanetriol,
    .normetanephrine, .igfbp3, .gastrin, .freeMetanephrineFractions,
    .amh, .leptin]

def Item.number : Item → Nat
  | .hcgQualitative => 1
  | .ohcs11 => 2
  | .hva => 3
  | .vma => 4
  | .hiaa5 => 5
  | .prolactin | .tsh => 6
  | .t3 => 7
  | .reninActivity | .insulin => 8
  | .reninQuantitative => 9
  | .growthHormone => 10
  | .t4 => 11
  | .fsh | .cPeptide | .lh => 12
  | .testosterone => 13
  | .ft4 | .ft3 | .cortisol => 14
  | .aldosterone => 15
  | .calcitonin => 16
  | .thyroglobulin => 17
  | .hcgBeta => 18
  | .tbg | .bnp | .hcgQuantitative | .hcgSemiquantitative => 19
  | .antiGad => 20
  | .ntProBnp => 21
  | .tbc => 22
  | .progesterone => 23
  | .glucagon | .ucOc => 24
  | .ntx | .osteocalcin => 25
  | .tracp5b | .freeTestosterone => 26
  | .bap => 27
  | .pinp => 28
  | .pth | .catecholamineFractions | .camp => 29
  | .intactPinp => 30
  | .dheaS => 31
  | .hcgLowUnitSemiquantitative => 32
  | .estradiol => 33
  | .urineBetaCtx => 34
  | .betaCtx => 35
  | .estriol | .estrogenSemiquantitative | .estrogenQuantitative | .cPthrp => 36
  | .acth | .catecholamine => 37
  | .pthrp => 38
  | .urineDpd => 39
  | .kgs17 => 40
  | .erythropoietin => 41
  | .somatomedinC => 42
  | .ks17Fractions | .ohp17Alpha | .antiIa2 | .pregnanediol => 43
  | .metanephrine => 44
  | .kgs17Fractions | .metanephrineFractions => 45
  | .anp => 46
  | .adh => 47
  | .pregnanetriol => 48
  | .normetanephrine => 49
  | .igfbp3 => 50
  | .gastrin => 51
  | .freeMetanephrineFractions => 52
  | .amh => 53
  | .leptin => 54

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem item_range (n : Nat) : (∃ i, ItemAt n i) ↔ 1 ≤ n ∧ n ≤ 54 := by
  constructor
  · rintro ⟨i, rfl⟩
    cases i <;> decide
  · intro h
    have bound : n < 55 := by omega
    -- 54を上限とする型に移し、列挙表が各項を含むことを検査する。
    have complete : ∀ k : Fin 55, 1 ≤ k.val →
        ledgerItems.any (fun i => i.number == k.val) = true := by decide
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp (complete ⟨n, bound⟩ h.1)
    exact ⟨i, beq_iff_eq.mp hi⟩

def Item.points : Item → Nat
  | .hcgQualitative => 55
  | .ohcs11 => 60
  | .hva => 69
  | .vma => 90
  | .hiaa5 => 95
  | .prolactin | .tsh => 98
  | .t3 => 99
  | .reninActivity | .insulin => 100
  | .reninQuantitative => 102
  | .growthHormone => 104
  | .t4 => 105
  | .fsh | .cPeptide | .lh => 105
  | .testosterone => 119
  | .ft4 | .ft3 | .cortisol => 121
  | .aldosterone => 122
  | .calcitonin => 127
  | .thyroglobulin => 128
  | .hcgBeta => 129
  | .tbg | .bnp | .hcgQuantitative | .hcgSemiquantitative => 130
  | .antiGad => 134
  | .ntProBnp => 136
  | .tbc => 137
  | .progesterone => 139
  | .glucagon | .ucOc => 150
  | .ntx | .osteocalcin => 153
  | .tracp5b | .freeTestosterone => 156
  | .bap => 157
  | .pinp => 160
  | .pth | .catecholamineFractions | .camp => 161
  | .intactPinp => 163
  | .dheaS => 164
  | .hcgLowUnitSemiquantitative => 165
  | .estradiol => 167
  | .urineBetaCtx => 169
  | .betaCtx => 170
  | .estriol | .estrogenSemiquantitative | .estrogenQuantitative | .cPthrp => 180
  | .acth | .catecholamine => 184
  | .pthrp => 185
  | .urineDpd => 191
  | .kgs17 => 200
  | .erythropoietin => 209
  | .somatomedinC => 212
  | .ks17Fractions | .ohp17Alpha | .antiIa2 | .pregnanediol => 213
  | .metanephrine => 217
  | .kgs17Fractions | .metanephrineFractions => 220
  | .anp => 221
  | .adh => 224
  | .pregnanetriol => 232
  | .normetanephrine => 250
  | .igfbp3 => 280
  | .gastrin => 380
  | .freeMetanephrineFractions => 585
  | .amh => 597
  | .leptin => 1000

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 8, number := i.number, ordinaryCategory := .biochemicalII }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .biochemicalII := rfl

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def rateRule (i : Item) : Rule Item Nat :=
  ⟨"primary/D008/item/" ++ toString i.number,
    primary ((if i.number ≤ 28 then "PDF181頁" else "PDF182頁") ++ " D008 項" ++ toString i.number),
    fun item p => item = i → p = i.points⟩

inductive Sample where
  | wholeBlood | serum | plasma | urine | puncture | other
  deriving DecidableEq

inductive Method where
  | laOrEquivalent | eia | cleia | eclia | clia | elisa | other
  deriving DecidableEq

inductive Purpose where
  | heartFailureDiagnosis | heartFailureStatus
  | type1DiabetesDiagnosis | autoimmuneEncephalitisOrEncephalopathy
  | osteoporosisVitaminK2Choice | osteoporosisVitaminK2Monitoring
  | primaryParathyroidSurgery | secondaryParathyroidSurgery
  | parathyroidPostoperativeEffect | parathyroidAdenomaHyperplasiaPostoperativeEffect
  | osteoporosisDrugChoice | osteoporosisDrugEffect
  | metabolicBoneDiseaseDiagnosis | boneMetastasisDiagnosis | boneTreatmentMonitoring
  | osteoporosisAntiresorptiveBaseline | osteoporosisAntiresorptiveEffect | osteoporosisAntiresorptiveMonitoring
  | hypercalcemiaDifferential | malignantHypercalcemiaEffect
  | erythrocytosisDifferential | renalAnemiaDiagnosis | mdsAnemiaTherapyChoice
  | congenitalAdrenalHyperplasiaDiagnosis | congenitalAdrenalHyperplasiaEffect
  | pheochromocytomaDiagnosis | pheochromocytomaPostoperativeEffect | pheochromocytomaDifferential
  | growthHormoneDeficiencyDiagnosisAndTreatmentEligibility
  | infertilityOvarianFunctionAndTherapyChoice | pcosDiagnosticAid | lipodystrophyDiagnosticAid
  deriving DecidableEq

inductive Phase where
  | beforeTreatment | followUp | changedTreatment | atDiagnosis
  deriving DecidableEq

/-- 併施・同時・日から起算する期間は別の確認済み範囲として渡す。 -/
inductive CombinationItem where
  | endocrine (item : Item) (sample : Sample)
  | d007Pag | d007IsoenzymesAndBap
  deriving DecidableEq

def CombinationItem.testKind : CombinationItem → CombinationItem
  | .endocrine item _ => .endocrine item .other
  | item => item

structure Survey where
  performed : List (Performance CombinationItem)
  charged : List Nat := []

def Survey.kindCount (s : Survey) (select : CombinationItem → Bool) : Nat :=
  ((s.performed.filter (select ∘ Performance.item)).map (·.item.testKind)).eraseDups.length

structure Context where
  performance : Performance Item
  sample : Option Sample := none
  purpose : Option Purpose := none
  method : Option Method := none
  diurnal : Option Bool := none
  appropriateDiurnalCount : Option Bool := none
  hcgProducingTumor : Option Bool := none
  diabetesConfirmed : Option Bool := none
  negativeGadDate : Option Date := none
  history : Option (ClaimHistory Item) := none
  phase : Option Phase := none
  /-- 基準となる治療開始・変更、期間の起算と帰属を確認済み。 -/
  treatmentWindow : Option Period := none
  frequencyInstitution : Option (Option Nat) := none
  metabolicBoneDiseaseAbsent : Option Bool := none
  fractureAbsent : Option Bool := none
  lungBreastOrProstateCancer : Option Bool := none
  plannedTumorManagementFromTest : Option Bool := none
  severeChronicRenalFailure : Option Bool := none
  dialysisBeforeListedDrug : Option Bool := none
  growthHormoneGuidanceSatisfied : Option Bool := none
  pheochromocytomaGuidelineFollowed : Option Bool := none
  infertile : Option Bool := none
  suspectedPcos : Option Bool := none
  ultrasoundDiagnosisDifficult : Option Bool := none
  lipoatrophy : Option Bool := none
  increasedAppetite : Option Bool := none
  insulinResistance : Option Bool := none
  dyslipidemia : Option Bool := none
  lipodystrophyGuidelineFollowed : Option Bool := none
  together : Option Survey := none
  simultaneous : Option Survey := none
  natriureticWeek : Option Survey := none
  alpPrincipality : Option BloodChemistryLate.AlpTest := none

def AtPurpose (c : Context) (purposes : List Purpose) : Prop :=
  ∃ p ∈ purposes, c.purpose = some p

def prior (c : Context) (period : Period) : Option Nat := do
  let h ← c.history
  let institution ← c.frequencyInstitution
  count h ⟨c.performance.site.patient, institution, period⟩ (· == c.performance.item)

def OneLifetime (c : Context) : Prop :=
  ∃ h, c.history = some h ∧ count h
    ⟨c.performance.site.patient, none, Period.through c.performance.site.date⟩
    (· == c.performance.item) = some 0

def Monthly (c : Context) : Prop :=
  prior c (Period.month c.performance.site.date.month) = some 0

def ConfirmedWindow (c : Context) : Prop :=
  ∃ period, c.treatmentWindow = some period ∧ period.Contains c.performance.site.date ∧
    prior c period = some 0

def PhaseWindow (c : Context) (phases : List Phase) : Prop :=
  (∃ phase ∈ phases, c.phase = some phase) ∧ ConfirmedWindow c

def SamePatientSurvey (c : Context) (survey : Survey) : Prop :=
  (survey.performed.map Performance.id).Nodup ∧
  (∀ p ∈ survey.performed, p.site.patient = c.performance.site.patient) ∧
  ∃ sample p, c.sample = some sample ∧ p ∈ survey.performed ∧
    p.id = c.performance.id ∧ p.site = c.performance.site ∧
    p.item = .endocrine c.performance.item sample

def OnlySelected (c : Context) (s : Survey) (select : CombinationItem → Bool) : Prop :=
  c.performance.id ∈ s.charged ∧
    ∀ p ∈ s.performed, select p.item = true → p.id ∈ s.charged → p.id = c.performance.id

def endorses (c : Context) (evidence : Option Survey)
    (select : CombinationItem → Bool) : Prop :=
  ∃ s, evidence = some s ∧ SamePatientSurvey c s ∧
    (s.kindCount select ≤ 1 ∨ OnlySelected c s select)

def noCounterpart (c : Context) (evidence : Option Survey)
    (select : CombinationItem → Bool) : Prop :=
  ∃ s, evidence = some s ∧ SamePatientSurvey c s ∧
    ∀ p ∈ s.performed, select p.item = false

def endocrineGroup (items : List Item) : CombinationItem → Bool
  | .endocrine i _ => items.contains i
  | _ => false

private def hcg : List Item := [.hcgBeta, .hcgQualitative, .hcgQuantitative, .hcgSemiquantitative]
private def renin : List Item := [.reninActivity, .reninQuantitative]
private def natriuretic : List Item := [.bnp, .ntProBnp, .anp]
private def boneMarker : List Item := [.ntx, .osteocalcin, .urineDpd]
private def alpMarker : List Item := [.bap, .pinp, .intactPinp]
private def betaCtxItems : List Item := [.urineBetaCtx, .betaCtx]
private def metanephrines : List Item := [.metanephrine, .metanephrineFractions, .normetanephrine,
  .freeMetanephrineFractions]

private def alpGroup : CombinationItem → Bool
  | .d007Pag => true
  | p => endocrineGroup alpMarker p

def Diurnal (c : Context) : Prop :=
  c.diurnal = some false ∨ (c.diurnal = some true ∧ c.appropriateDiurnalCount = some true)

def natriureticChoice (c : Context) : Prop :=
  endorses c c.natriureticWeek (endocrineGroup natriuretic)

private def cprBlood : CombinationItem → Bool
  | .endocrine .cPeptide .wholeBlood | .endocrine .cPeptide .serum |
    .endocrine .cPeptide .plasma => true
  | _ => false

def CprSelection (c : Context) : Prop :=
  c.sample = some .wholeBlood ∨ c.sample = some .serum ∨ c.sample = some .plasma ∨
    (c.sample = some .urine ∧ noCounterpart c c.simultaneous cprBlood)

inductive Classification where
  | immunologicalPregnancyTest | includesTubeHcgLh
  deriving DecidableEq

def pregnancyRule : Rule Item (Classification → Prop) :=
  ⟨"notice/D008/paragraph/2", notice "PDF361頁 D008(2)", fun i classes =>
    i ∈ [.hcgQualitative, .hcgBeta] → classes .immunologicalPregnancyTest⟩

def hcgTubeRule : Rule Item (Classification → Prop) :=
  ⟨"notice/D008/paragraph/8", notice "PDF362頁 D008(8)", fun i classes =>
    i ∈ [.hcgQuantitative, .hcgSemiquantitative] → classes .includesTubeHcgLh⟩

def diurnalRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/1", notice "PDF361頁 D008 1",
    fun c _ => Diurnal c⟩

def reninRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/3", notice "PDF361頁 D008 3",
    fun c _ => c.performance.item ∈ [.reninActivity, .reninQuantitative] →
      endorses c c.together (endocrineGroup renin)⟩

def cprRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/4", notice "PDF361頁 D008 4",
    fun c _ => c.performance.item = .cPeptide →
      CprSelection c⟩

def lhRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/5", notice "PDF361頁 D008 5",
    fun c _ => c.performance.item = .lh →
      c.method = some .laOrEquivalent⟩

def hcgBetaRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/6/a", notice "PDF361頁 D008 6/a",
    fun c _ => c.performance.item = .hcgBeta →
      c.hcgProducingTumor = some true⟩

def hcgChoiceRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/6/i", notice "PDF361頁 D008 6/i",
    fun c _ => c.performance.item ∈ [.hcgBeta, .hcgQualitative, .hcgQuantitative, .hcgSemiquantitative] →
      endorses c c.together (endocrineGroup hcg)⟩

def hcgParagraph : Rule Context Unit :=
  ⟨"notice/D008/paragraph/6", notice "PDF361頁 D008 6",
    fun c _ => c.performance.item = .hcgBeta →
      hcgBetaRule.holds c () ∧ hcgChoiceRule.holds c ()⟩

def bnpIndication : Rule Context Unit :=
  ⟨"notice/D008/paragraph/7/a", notice "PDF361–362頁 D008 7/a",
    fun c _ => c.performance.item = .bnp →
      AtPurpose c [.heartFailureDiagnosis, .heartFailureStatus] ∧ Monthly c⟩

def bnpChoice : Rule Context Unit :=
  ⟨"notice/D008/paragraph/7/i", notice "PDF362頁 D008 7/i",
    fun c _ => c.performance.item = .bnp →
      natriureticChoice c⟩

def bnpParagraph : Rule Context Unit :=
  ⟨"notice/D008/paragraph/7", notice "PDF361–362頁 D008 7",
    fun c _ => c.performance.item = .bnp →
      bnpIndication.holds c () ∧ bnpChoice.holds c ()⟩

def antiGadRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/9", notice "PDF362頁 D008 9",
    fun c _ => c.performance.item = .antiGad →
      (c.diabetesConfirmed = some true ∧ c.purpose = some .type1DiabetesDiagnosis) ∨
      c.purpose = some .autoimmuneEncephalitisOrEncephalopathy⟩

def ntProBnpIndication : Rule Context Unit :=
  ⟨"notice/D008/paragraph/10/a", notice "PDF362頁 D008 10/a",
    fun c _ => c.performance.item = .ntProBnp →
      AtPurpose c [.heartFailureDiagnosis, .heartFailureStatus] ∧ Monthly c⟩

def ntProBnpChoice : Rule Context Unit :=
  ⟨"notice/D008/paragraph/10/i", notice "PDF362頁 D008 10/i",
    fun c _ => c.performance.item = .ntProBnp →
      natriureticChoice c⟩

def ntProBnpParagraph : Rule Context Unit :=
  ⟨"notice/D008/paragraph/10", notice "PDF362頁 D008 10",
    fun c _ => c.performance.item = .ntProBnp →
      ntProBnpIndication.holds c () ∧ ntProBnpChoice.holds c ()⟩

def ucOcRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/11", notice "PDF362頁 D008 11",
    fun c _ => c.performance.item = .ucOc →
      (c.purpose = some .osteoporosisVitaminK2Choice ∧ PhaseWindow c [.beforeTreatment]) ∨
      (c.purpose = some .osteoporosisVitaminK2Monitoring ∧ PhaseWindow c [.followUp])⟩

def ntxDpdRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/12", notice "PDF362頁 D008 12",
    fun c _ => c.performance.item ∈ [.ntx, .urineDpd] →
      AtPurpose c [.primaryParathyroidSurgery, .parathyroidPostoperativeEffect] ∨
      (c.purpose = some .osteoporosisDrugChoice ∧ PhaseWindow c [.beforeTreatment]) ∨
      (c.purpose = some .osteoporosisDrugEffect ∧ PhaseWindow c [.followUp, .changedTreatment])⟩

def boneMarkerRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/13", notice "PDF362頁 D008 13",
    fun c _ => c.performance.item ∈ [.ntx, .osteocalcin, .urineDpd] →
      endorses c c.together (endocrineGroup boneMarker)⟩

def osteocalcinRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/14", notice "PDF362頁 D008 14",
    fun c _ => c.performance.item = .osteocalcin →
      AtPurpose c [.secondaryParathyroidSurgery, .parathyroidAdenomaHyperplasiaPostoperativeEffect]⟩

def tracpRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/15", notice "PDF363頁 D008 15",
    fun c _ => c.performance.item = .tracp5b →
      ((AtPurpose c [.metabolicBoneDiseaseDiagnosis, .boneMetastasisDiagnosis] ∧
        PhaseWindow c [.beforeTreatment]) ∨
       (c.purpose = some .boneTreatmentMonitoring ∧ PhaseWindow c [.followUp, .changedTreatment])) ∧
      (c.purpose = some .boneMetastasisDiagnosis →
        c.metabolicBoneDiseaseAbsent = some true ∧ c.fractureAbsent = some true ∧
        c.lungBreastOrProstateCancer = some true ∧ c.plannedTumorManagementFromTest = some false)⟩

def tracpChoiceRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/15", notice "PDF363頁 D008 15",
    fun c _ => c.performance.item ∈ [.ntx, .osteocalcin, .urineDpd, .tracp5b] →
      ∃ s, c.together = some s ∧ SamePatientSurvey c s ∧
        ((∀ p ∈ s.performed, endocrineGroup [.tracp5b] p.item = false) ∨
         (∀ p ∈ s.performed, endocrineGroup boneMarker p.item = false) ∨
         OnlySelected c s (endocrineGroup (.tracp5b :: boneMarker)))⟩

def alpRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/16", notice "PDF363頁 D008 16",
    fun c _ => c.performance.item ∈ [.bap, .pinp, .intactPinp] →
      endorses c c.together alpGroup⟩

def urineBetaCtxRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/17", notice "PDF363頁 D008 17",
    fun c _ => c.performance.item = .urineBetaCtx →
      (c.purpose = some .osteoporosisAntiresorptiveBaseline ∧ PhaseWindow c [.beforeTreatment]) ∨
      (AtPurpose c [.osteoporosisAntiresorptiveEffect, .osteoporosisAntiresorptiveMonitoring] ∧
        PhaseWindow c [.followUp])⟩

def betaCtxRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/18", notice "PDF363頁 D008 18",
    fun c _ => c.performance.item = .betaCtx →
      (c.purpose = some .osteoporosisAntiresorptiveBaseline ∧ PhaseWindow c [.beforeTreatment]) ∨
      (AtPurpose c [.osteoporosisAntiresorptiveEffect, .osteoporosisAntiresorptiveMonitoring] ∧
        PhaseWindow c [.followUp])⟩

def betaCtxChoice : Rule Context Unit :=
  ⟨"notice/D008/paragraph/18", notice "PDF363頁 D008 18",
    fun c _ => c.performance.item ∈ [.urineBetaCtx, .betaCtx] →
      endorses c c.together (endocrineGroup betaCtxItems)⟩

def estrogenRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/19", notice "PDF363頁 D008 19",
    fun c _ => c.performance.item ∈ [.estrogenSemiquantitative, .estrogenQuantitative] →
      noCounterpart c c.simultaneous (endocrineGroup [.estriol, .estradiol])⟩

def pthrpRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/20", notice "PDF363頁 D008 20",
    fun c _ => c.performance.item ∈ [.cPthrp, .pthrp] →
      AtPurpose c [.hypercalcemiaDifferential, .malignantHypercalcemiaEffect]⟩

def epoDifferential : Rule Context Unit :=
  ⟨"notice/D008/paragraph/21/a", notice "PDF363頁 D008 21/a",
    fun c _ => c.purpose = some .erythrocytosisDifferential⟩

def epoRenal : Rule Context Unit :=
  ⟨"notice/D008/paragraph/21/i", notice "PDF363頁 D008 21/i",
    fun c _ => c.purpose = some .renalAnemiaDiagnosis ∧
      (c.severeChronicRenalFailure = some true ∨ c.dialysisBeforeListedDrug = some true)⟩

def epoMds : Rule Context Unit :=
  ⟨"notice/D008/paragraph/21/u", notice "PDF363頁 D008 21/u",
    fun c _ => c.purpose = some .mdsAnemiaTherapyChoice⟩

def epoRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/21", notice "PDF363頁 D008 21",
    fun c _ => c.performance.item = .erythropoietin →
      epoDifferential.holds c () ∨ epoRenal.holds c () ∨ epoMds.holds c ()⟩

def antiIa2Rule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/22", notice "PDF363–364頁 D008 22",
    fun c _ => c.performance.item = .antiIa2 →
      c.purpose = some .type1DiabetesDiagnosis ∧ c.diabetesConfirmed = some true ∧
      ∃ date, c.negativeGadDate = some date ∧ date.key ≤ c.performance.site.date.key⟩

def ohpRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/23", notice "PDF364頁 D008 23",
    fun c _ => c.performance.item = .ohp17Alpha →
      AtPurpose c [.congenitalAdrenalHyperplasiaDiagnosis, .congenitalAdrenalHyperplasiaEffect]⟩

def anpChoice : Rule Context Unit :=
  ⟨"notice/D008/paragraph/24", notice "PDF364頁 D008 24",
    fun c _ => c.performance.item = .anp →
      natriureticChoice c⟩

def normetanephrineRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/25", notice "PDF364頁 D008 25",
    fun c _ =>
      (c.performance.item = .normetanephrine →
        AtPurpose c [.pheochromocytomaDiagnosis, .pheochromocytomaPostoperativeEffect]) ∧
      (c.performance.item ∈ [.metanephrine, .normetanephrine] →
        endorses c c.together (endocrineGroup [.metanephrine, .normetanephrine]))⟩

def igfbp3Indication : Rule Context Unit :=
  ⟨"notice/D008/paragraph/26/a", notice "PDF364頁 D008 26/a",
    fun c _ => c.performance.item = .igfbp3 →
      c.purpose = some .growthHormoneDeficiencyDiagnosisAndTreatmentEligibility ∧
      c.growthHormoneGuidanceSatisfied = some true⟩

def igfbp3Choice : Rule Context Unit :=
  ⟨"notice/D008/paragraph/26/i", notice "PDF364頁 D008 26/i",
    fun c _ => c.performance.item ∈ [.igfbp3, .somatomedinC] →
      endorses c c.together (endocrineGroup [.igfbp3, .somatomedinC])⟩

def igfbp3Paragraph : Rule Context Unit :=
  ⟨"notice/D008/paragraph/26", notice "PDF364頁 D008 26",
    fun c _ => c.performance.item = .igfbp3 →
      igfbp3Indication.holds c () ∧ igfbp3Choice.holds c ()⟩

def freeMetanephrineIndication : Rule Context Unit :=
  ⟨"notice/D008/paragraph/27/a", notice "PDF364頁 D008 27/a",
    fun c _ => c.performance.item = .freeMetanephrineFractions →
      c.purpose = some .pheochromocytomaDifferential ∧ OneLifetime c ∧
      c.pheochromocytomaGuidelineFollowed = some true⟩

def freeMetanephrineChoice : Rule Context Unit :=
  ⟨"notice/D008/paragraph/27/i", notice "PDF364頁 D008 27/i",
    fun c _ => c.performance.item ∈ [.metanephrine, .metanephrineFractions, .normetanephrine, .freeMetanephrineFractions] →
      ∃ s, c.together = some s ∧ SamePatientSurvey c s ∧
        ((∀ p ∈ s.performed, endocrineGroup [.freeMetanephrineFractions] p.item = false) ∨
          s.kindCount (endocrineGroup metanephrines) ≤ 1 ∨
          OnlySelected c s (endocrineGroup metanephrines))⟩

def freeMetanephrineParagraph : Rule Context Unit :=
  ⟨"notice/D008/paragraph/27", notice "PDF364頁 D008 27",
    fun c _ => c.performance.item = .freeMetanephrineFractions →
      freeMetanephrineIndication.holds c () ∧ freeMetanephrineChoice.holds c ()⟩

def amhRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/28", notice "PDF364頁 D008 28",
    fun c _ => c.performance.item = .amh →
      (c.sample = some .serum ∨ c.sample = some .plasma) ∧
      (∃ method ∈ [Method.eia, .cleia, .eclia, .clia], c.method = some method) ∧
      ((c.purpose = some .infertilityOvarianFunctionAndTherapyChoice ∧ c.infertile = some true ∧
          ConfirmedWindow c) ∨
       (c.purpose = some .pcosDiagnosticAid ∧ c.suspectedPcos = some true ∧
          c.ultrasoundDiagnosisDifficult = some true ∧ PhaseWindow c [.atDiagnosis]))⟩

def leptinIndication : Rule Context Unit :=
  ⟨"notice/D008/paragraph/29/a", notice "PDF364頁 D008 29/a",
    fun c _ => c.performance.item = .leptin →
      c.lipoatrophy = some true ∧ c.increasedAppetite = some true ∧
      c.insulinResistance = some true ∧ c.diabetesConfirmed = some true ∧
      c.dyslipidemia = some true ∧ c.purpose = some .lipodystrophyDiagnosticAid ∧
      c.method = some .elisa ∧ OneLifetime c⟩

def leptinGuidance : Rule Context Unit :=
  ⟨"notice/D008/paragraph/29/i", notice "PDF364頁 D008 29/i",
    fun c _ => c.performance.item = .leptin →
      c.lipodystrophyGuidelineFollowed = some true⟩

def leptinParagraph : Rule Context Unit :=
  ⟨"notice/D008/paragraph/29", notice "PDF364頁 D008 29",
    fun c _ => c.performance.item = .leptin →
      leptinIndication.holds c () ∧ leptinGuidance.holds c ()⟩


inductive Entry where
  | natriureticDate (id : Nat) (date : Date) | negativeGadDate (date : Date) | suspectedPheochromocytoma
  | lipoatrophyOnset | suspectedLipodystrophy

structure Documentation where
  chart : Entry → Prop
  claimRemarks : Entry → Prop

def NatriureticDates (c : Context) (dates : Documentation) (reportedTogether : Survey) : Prop :=
  SamePatientSurvey c reportedTogether →
    2 ≤ reportedTogether.kindCount (endocrineGroup natriuretic) →
    ∀ p ∈ reportedTogether.performed, endocrineGroup natriuretic p.item = true →
      dates.claimRemarks (.natriureticDate p.id p.site.date)

def bnpDocumentation : Rule (Context × Survey) Documentation :=
  ⟨"notice/D008/paragraph/7/u", notice "PDF362頁 D008(7)ウ", fun (c, survey) d =>
    c.performance.item = .bnp → NatriureticDates c d survey⟩

def ntProBnpDocumentation : Rule (Context × Survey) Documentation :=
  ⟨"notice/D008/paragraph/10/u", notice "PDF362頁 D008(10)ウ", fun (c, survey) d =>
    c.performance.item = .ntProBnp → NatriureticDates c d survey⟩

def antiIa2Documentation : Rule Context Documentation :=
  ⟨"notice/D008/paragraph/22", notice "PDF363–364頁 D008(22) 記載", fun c d =>
    c.performance.item = .antiIa2 → ∀ date, c.negativeGadDate = some date →
      d.claimRemarks (.negativeGadDate date)⟩

def freeMetanephrineDocumentation : Rule Context Documentation :=
  ⟨"notice/D008/paragraph/27/a", notice "PDF364頁 D008(27)ア 記載", fun c d =>
    c.performance.item = .freeMetanephrineFractions → d.chart .suspectedPheochromocytoma⟩

def leptinDocumentation : Rule Context Documentation :=
  ⟨"notice/D008/paragraph/29/i", notice "PDF364頁 D008(29)イ 記載", fun c d =>
    c.performance.item = .leptin → d.claimRemarks .lipoatrophyOnset ∧ d.claimRemarks .suspectedLipodystrophy⟩

def eligibilityRules : List (Rule Context Unit) :=
  [diurnalRule, reninRule, cprRule, lhRule,
    hcgBetaRule, hcgChoiceRule, hcgParagraph, bnpIndication,
    bnpChoice, bnpParagraph, antiGadRule, ntProBnpIndication,
    ntProBnpChoice, ntProBnpParagraph, ucOcRule, ntxDpdRule,
    boneMarkerRule, osteocalcinRule, tracpRule, tracpChoiceRule,
    alpRule, urineBetaCtxRule, betaCtxRule, betaCtxChoice,
    estrogenRule, pthrpRule, epoRule, antiIa2Rule,
    ohpRule, anpChoice, normetanephrineRule, igfbp3Indication,
    igfbp3Choice, igfbp3Paragraph, freeMetanephrineIndication, freeMetanephrineChoice,
    freeMetanephrineParagraph, amhRule, leptinIndication, leptinGuidance,
    leptinParagraph]

private def alpCounterpart : CombinationItem → Option BloodChemistryLate.AlpTest
  | .endocrine .bap _ => some .d008Bap
  | .d007Pag => some .d007Pag
  | .d007IsoenzymesAndBap => some .d007IsoenzymesAndBap
  | _ => none

def AlpEligible (c : Context) : Prop :=
  c.performance.item = .bap →
    ∃ survey, c.together = some survey ∧ SamePatientSurvey c survey ∧
      let performed := survey.performed.filterMap (alpCounterpart ∘ Performance.item)
      let charged := (survey.performed.filter (fun p => survey.charged.contains p.id)).filterMap
        (alpCounterpart ∘ Performance.item)
      let bapTogether := performed.contains .d007IsoenzymesAndBap
      let allThree := bapTogether && performed.contains .d007Pag
      .d008Bap ∈ charged ∧
      (allThree = true → c.alpPrincipality.isSome = true) ∧
      BloodChemistryLate.AlpSelections
        ⟨allThree, c.alpPrincipality.getD .d008Bap⟩ bapTogether .second charged

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c () ∧ AlpEligible c

def individualRules : List (Rule Item Nat) := ledgerItems.map rateRule

theorem individual_iff (i : Item) (p : Nat) :
    Satisfies individualRules i p ↔ p = i.points := by
  constructor
  · intro h
    exact h (rateRule i) (List.mem_map.mpr ⟨i, by cases i <;> simp [ledgerItems], rfl⟩) rfl
  · intro h r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro e
    simpa [e] using h

def PermitsIndividual (c : Context) (p : Nat) : Prop :=
  Eligible c ∧ Satisfies individualRules c.performance.item p

theorem individual_determines (c : Context) (h : Eligible c) :
    (∃ p, PermitsIndividual c p) ∧
    ∀ a b, PermitsIndividual c a → PermitsIndividual c b → a = b :=
  ⟨⟨c.performance.item.points, h, (individual_iff _ _).mpr rfl⟩,
    fun _ _ ha hb => ((individual_iff _ _).mp ha.2).trans ((individual_iff _ _).mp hb.2).symm⟩

/-- 通知(15)の悪性腫瘍特異物質治療管理料に移る条件。B001側の点数は評価しない。 -/
def tumorManagementRule : Rule Context Unit :=
  ⟨"notice/D008/paragraph/15", notice "PDF363頁 D008(15) B001参照",
    fun c _ => c.performance.item = .tracp5b ∧ c.purpose = some .boneMetastasisDiagnosis ∧
      c.lungBreastOrProstateCancer = some true ∧ c.plannedTumorManagementFromTest = some true⟩

/-- D007(18)・(36)の選択制約を同じ算定候補へ適用する。 -/
def AllowsAlpCrossSection (c : Context) (allThreeTogether bapTogether : Bool)
    (principal : BloodChemistryLate.AlpTest) (pairChoice : BloodChemistryFurther.Choice)
    (charged : List BloodChemistryLate.AlpTest) : Prop :=
  c.performance.item = .bap ∧ BloodChemistryLate.AlpTest.d008Bap ∈ charged ∧
    BloodChemistryLate.AlpSelections ⟨allThreeTogether, principal⟩ bapTogether pairChoice charged

theorem alp_pair_excludes_both (c : Context) (allThree : Bool)
    (principal : BloodChemistryLate.AlpTest) (choice : BloodChemistryFurther.Choice)
    (charged : List BloodChemistryLate.AlpTest)
    (h : AllowsAlpCrossSection c allThree true principal choice charged) :
    choice ≠ .both :=
  h.2.2.2.1 rfl

/-- D008(16)のD007側の候補。D007個別条件は既存モデルで評価する。 -/
def PagAllowed (s : Survey) (p : Performance CombinationItem) : Prop :=
  p.item = .d007Pag ∧ p ∈ s.performed ∧
    (s.kindCount alpGroup ≤ 1 ∨
      (p.id ∈ s.charged ∧ ∀ q ∈ s.performed, alpGroup q.item = true →
        q.id ∈ s.charged → q.id = p.id))

def PagPoints (survey : Survey) (p : Performance CombinationItem)
    (c : BloodChemistryLate.Context) (n : Nat) : Prop :=
  PagAllowed survey p ∧ c.item = .alpIsoenzymesPag ∧
    Satisfies BloodChemistryLate.rules c n

inductive BundleSource where
  | blood
  | urine
  | puncture
  deriving DecidableEq, Repr

/-- 検査種の点数と、当該包括に合流する検体の区別。 -/
structure BundleItem where
  item : Item
  source : BundleSource
  deriving DecidableEq, Repr

def BundleItem.inNote (x : BundleItem) : Bool :=
  decide (12 ≤ x.item.number ∧ x.item.number ≤ 51)

private def covered (xs : List BundleItem) : List BundleItem := xs.filter BundleItem.inNote

private def sumPoints (xs : List BundleItem) : Nat := (xs.map (·.item.points)).sum

private def outside (xs : List BundleItem) : Nat :=
  sumPoints (xs.filter (fun x => !x.inNote))

def noteRule : Rule (List BundleItem) Nat :=
  ⟨"primary/D008/note/unnumbered/1", primary "PDF182頁 D008 注", fun xs p =>
    (covered xs).length < 3 → p = sumPoints xs⟩

def noteI : Rule (List BundleItem) Nat :=
  ⟨"primary/D008/note/i", primary "PDF182頁 D008 注イ", fun xs p =>
    3 ≤ (covered xs).length → (covered xs).length ≤ 5 → p = outside xs + 410⟩

def noteRo : Rule (List BundleItem) Nat :=
  ⟨"primary/D008/note/ro", primary "PDF182頁 D008 注ロ", fun xs p =>
    6 ≤ (covered xs).length → (covered xs).length ≤ 7 → p = outside xs + 623⟩

def noteHa : Rule (List BundleItem) Nat :=
  ⟨"primary/D008/note/ha", primary "PDF182頁 D008 注ハ", fun xs p =>
    8 ≤ (covered xs).length → p = outside xs + 900⟩

def bundleRules := [noteRule, noteI, noteRo, noteHa]

def bundlePoints (xs : List BundleItem) : Nat :=
  let n := (covered xs).length
  if n < 3 then sumPoints xs
  else if n ≤ 5 then outside xs + 410
  else if n ≤ 7 then outside xs + 623
  else outside xs + 900

theorem bundle_iff (xs : List BundleItem) (p : Nat) :
    Satisfies bundleRules xs p ↔ p = bundlePoints xs := by
  simp only [bundleRules, satisfies_cons, satisfies_nil, noteRule, noteI, noteRo, noteHa, and_true,
    bundlePoints]
  generalize (covered xs).length = n
  generalize sumPoints xs = base
  generalize outside xs = extra
  by_cases h3 : n < 3
  · simp only [ite_eq_left h3]
    omega
  by_cases h5 : n ≤ 5
  · simp only [ite_eq_right h3, ite_eq_left h5]
    omega
  by_cases h7 : n ≤ 7
  · simp only [ite_eq_right h3, ite_eq_right h5, ite_eq_left h7]
    omega
  · simp only [ite_eq_right h3, ite_eq_right h5, ite_eq_right h7]
    omega

theorem bundle_determines : DeterminesOn (fun _ => True) bundleRules := by
  intro xs _
  exact ⟨⟨bundlePoints xs, (bundle_iff _ _).mpr rfl⟩,
    fun _ _ ha hb => ((bundle_iff _ _).mp ha).trans ((bundle_iff _ _).mp hb).symm⟩

/-- 採血に由来する適格な実施だけを受ける。期間は当該採血由来の全実施を含む確認範囲。 -/
structure BloodDraw where
  anchor : Performance Item
  history : Snapshot (Performance Item)
  period : Period
  contexts : Nat → Option Context

def BloodDraw.members (d : BloodDraw) : Option (List (Performance Item)) := do
  let site := d.anchor.site
  let entries ← d.history.select Performance.site ⟨site.patient, some site.institution, d.period⟩
    (fun _ => true)
  if !entries.contains d.anchor then none else entries.filterM d.anchor.sameDraw

def BloodDraw.Assessed (d : BloodDraw) (xs : List BundleItem) : Prop :=
  ∃ ps, d.members = some ps ∧ (ps.map Performance.item).Nodup ∧
    xs = ps.map (fun p => ⟨p.item, .blood⟩) ∧
    ∀ p ∈ ps, ∃ c, d.contexts p.id = some c ∧ c.performance = p ∧ Eligible c ∧
      (c.sample = some .wholeBlood ∨ c.sample = some .serum ∨ c.sample = some .plasma)

theorem BloodDraw.determines_points (d : BloodDraw) (xs : List BundleItem) (_ : d.Assessed xs) :
    DeterminesAt bundleRules xs := bundle_determines xs trivial

theorem BloodDraw.assessed_unique (d : BloodDraw) (a b : List BundleItem)
    (ha : d.Assessed a) (hb : d.Assessed b) : a = b := by
  obtain ⟨pa, hpa, _, rfl, _⟩ := ha
  obtain ⟨pb, hpb, _, rfl, _⟩ := hb
  rw [Option.some.inj (hpa.symm.trans hpb)]

def SameDay := D004.SameDayBundle BundleItem

private def GroupPoints : List (List BundleItem) → List Nat → Prop
  | [], [] => True
  | group :: groups, p :: ps => Satisfies bundleRules group p ∧ GroupPoints groups ps
  | _, _ => False

/-- D004(14)の同日包括の並びを使い、最初の採血群へ尿・穿刺液を合流させる。 -/
def sameDayPoints (d : SameDay) (points : List Nat) : Prop :=
  ∃ groups, (D004.sameDayBundleRule BundleItem).holds d groups ∧
    GroupPoints groups points

theorem sameDay_iff (d : SameDay) (points : List Nat) :
    sameDayPoints d points ↔
      points = ((d.urine ++ d.puncture ++ d.firstBloodDraw) :: d.laterBloodDraws).map bundlePoints := by
  have group_iff (xs : List BundleItem) : ∀ p, Satisfies bundleRules xs p ↔ p = bundlePoints xs :=
    bundle_iff xs
  have go (groups : List (List BundleItem)) (ps : List Nat) :
      GroupPoints groups ps ↔ ps = groups.map bundlePoints := by
    induction groups generalizing ps with
    | nil => cases ps <;> simp [GroupPoints]
    | cons group rest ih =>
      cases ps <;> simp [GroupPoints, group_iff, ih]
  simp [sameDayPoints, D004.sameDayBundleRule, go]

/-- 準用名とD008の具体的な検査の対応は採取記録から外部確認する。 -/
def D001Reference (urine : UrineFecalTests.Context) (c : Context) (d : SameDay) : Prop :=
  UrineFecalTests.assess urine = some (.requiresReference (.other .d008) true) ∧
    c.performance.site = d.site ∧ c.sample = some .urine ∧ Eligible c ∧
    ⟨c.performance.item, .urine⟩ ∈ d.urine

def D004Reference (puncture : D004.Context) (c : Context) (d : SameDay) : Prop :=
  puncture.item = .other ∧ c.performance.site = d.site ∧ c.sample = some .puncture ∧ Eligible c ∧
    ⟨c.performance.item, .puncture⟩ ∈ d.puncture ∧
    ∃ r, puncture.reference = some r ∧ r.target = .other .d008 ∧
      r.sectionNotesAppliedAndSatisfied = true

/-- 尿・穿刺液および採血の順序を確認した、D004(14)の評価入力。 -/
structure SameDayEvidence where
  urines : List (UrineFecalTests.Context × Context)
  punctures : List (D004.Context × Context)
  first : BloodDraw
  later : List BloodDraw

def SameDayEvidence.Assesses (e : SameDayEvidence) (d : SameDay) : Prop :=
  d.urine = e.urines.map (fun (_, c) => ⟨c.performance.item, .urine⟩) ∧
  d.puncture = e.punctures.map (fun (_, c) => ⟨c.performance.item, .puncture⟩) ∧
  (∀ pair ∈ e.urines, D001Reference pair.1 pair.2 d) ∧
  (∀ pair ∈ e.punctures, D004Reference pair.1 pair.2 d) ∧
  e.first.anchor.site = d.site ∧ e.first.Assessed d.firstBloodDraw ∧
  e.later.length = d.laterBloodDraws.length ∧
  (∀ pair ∈ e.later.zip d.laterBloodDraws, pair.1.anchor.site = d.site ∧ pair.1.Assessed pair.2) ∧
  ((e.first :: e.later).map (·.anchor.draw)).Nodup ∧
  (((d.urine ++ d.puncture ++ d.firstBloodDraw).map BundleItem.item).Nodup)

theorem sameDay_determines (e : SameDayEvidence) (d : SameDay) (_ : e.Assesses d) :
    (∃ ps, sameDayPoints d ps) ∧
    ∀ a b, sameDayPoints d a → sameDayPoints d b → a = b :=
  ⟨⟨_, (sameDay_iff _ _).mpr rfl⟩,
    fun _ _ ha hb => ((sameDay_iff _ _).mp ha).trans ((sameDay_iff _ _).mp hb).symm⟩

private def site : Site := ⟨1, 1, ⟨⟨2026, 10⟩, ⟨22, by decide⟩⟩⟩

private def exampleContext : Context :=
  { performance := { id := 1, site, item := .tsh }
    sample := some .serum
    diurnal := some false }

example : PermitsIndividual exampleContext 98 := by
  refine ⟨?_, (individual_iff _ _).mpr rfl⟩
  simp [Eligible, AlpEligible, eligibilityRules, satisfies_cons, satisfies_nil, exampleContext, diurnalRule,
    Diurnal, reninRule, cprRule, lhRule, hcgBetaRule, hcgChoiceRule, hcgParagraph, bnpIndication,
    bnpChoice, bnpParagraph, antiGadRule, ntProBnpIndication, ntProBnpChoice, ntProBnpParagraph,
    ucOcRule, ntxDpdRule, boneMarkerRule, osteocalcinRule, tracpRule, tracpChoiceRule, alpRule,
    urineBetaCtxRule, betaCtxRule, betaCtxChoice, estrogenRule, pthrpRule, epoRule, antiIa2Rule,
    ohpRule, anpChoice, normetanephrineRule, igfbp3Indication, igfbp3Choice, igfbp3Paragraph,
    freeMetanephrineIndication, freeMetanephrineChoice, freeMetanephrineParagraph, amhRule,
    leptinIndication, leptinGuidance, leptinParagraph]

example : ¬ Eligible { exampleContext with diurnal := some true, appropriateDiurnalCount := some false } := by
  intro h
  have he := h.1 diurnalRule (by simp [eligibilityRules])
  simp [diurnalRule, Diurnal, exampleContext] at he

example : ¬ Eligible { exampleContext with diurnal := none } := by
  intro h
  have he := h.1 diurnalRule (by simp [eligibilityRules])
  simp [diurnalRule, Diurnal, exampleContext] at he

example : bundlePoints [⟨.fsh, .blood⟩, ⟨.lh, .blood⟩] = 210 := rfl

example : bundlePoints [⟨.fsh, .blood⟩, ⟨.lh, .blood⟩, ⟨.cortisol, .blood⟩,
    ⟨.tsh, .blood⟩] = 508 := rfl

example : sameDayPoints
    ⟨site, [⟨.cPeptide, .urine⟩], [⟨.cortisol, .puncture⟩], [⟨.lh, .blood⟩],
      [[⟨.fsh, .blood⟩]]⟩ [410, 105] := by
  exact (sameDay_iff _ _).mpr rfl

end Sanri.MedicalFee.D008
