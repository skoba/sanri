import Sanri.D001

namespace Sanri.MedicalFee.D003

open Sanri.Logic Sanri.History UrineFecalTests

inductive HemoglobinMethod where
  | immunochromatography | quantitativeGoldColloid | otherConfirmed
  deriving DecidableEq

inductive CalprotectinMethod where
  | elisa | feia | immunochromatography | latexAgglutination | goldColloid
  deriving DecidableEq

inductive Purpose where
  | diagnosis | ulcerativeColitisMonitoring | crohnMonitoring
  deriving DecidableEq

structure Context where
  performance : Performance Fecal
  /-- D017へ振り分ける細菌・原虫検査かを確認した結果。 -/
  d017BacteriaOrProtozoa : Option Bool
  hemoglobinMethod : Option HemoglobinMethod := none
  calprotectinMethod : Option CalprotectinMethod := none
  purpose : Option Purpose := none
  intestinalInfectionExcluded : Prop := False
  symptomsPersistedAtLeastThreeMonths : Prop := False
  noVisibleBloodyStool : Prop := False
  chronicIbdSuspected : Prop := False
  preEndoscopyDiagnosticAid : Prop := False
  threeMonthWindow : Option Period := none
  /-- 病態把握に帰属すると事前確認した算定履歴。 -/
  history : Option (ClaimHistory Fecal) := none
  medicallyNecessaryMonthlyMonitoring : Prop := False
  /-- 同月の大腸内視鏡との併施と選択を確認した結果。 -/
  colonoscopyMonthlySelection : Prop := False
  /-- 潰瘍性大腸炎の病態把握におけるD001(6)イの選択。 -/
  pgeMonthlySelection : Prop := False

def itemNumber : Fecal → Nat
  | .concentratedOvaDetection | .urobilin => 1
  | .smearMicroscopy => 2
  | .parasiteDetection => 3
  | .lipids => 4
  | .hemoglobinQualitative => 5
  | .ovaCulture => 6
  | .hemoglobin => 7
  | .hemoglobinAndTransferrinQualitativeQuantitative => 8
  | .calprotectin => 9

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF174頁 D003 " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def itemRule (n points : Nat) : Rule Context Nat :=
  ⟨"primary/D003/item/" ++ toString n, primary (toString n),
    fun c r => itemNumber c.performance.item = n → r = points⟩

def primaryRules :=
  [itemRule 1 15, itemRule 2 20, itemRule 3 23, itemRule 4 25, itemRule 5 37, itemRule 6 40,
    itemRule 7 41, itemRule 8 56, itemRule 9 268]

private def condition (id loc : String) (holds : Context → Prop) : Rule Context Nat :=
  ⟨"notice/D003/paragraph/" ++ id, notice loc, fun c _ => holds c⟩

def d017Rule : Rule Context Nat :=
  condition "1" "PDF333頁 D003(1)" fun c => c.d017BacteriaOrProtozoa = some false

def HemoglobinItem (t : Fecal) : Prop :=
  t = .hemoglobinQualitative ∨ t = .hemoglobin

def qualitativeRule : Rule Context Nat :=
  condition "2" "PDF333頁 D003(2)" fun c =>
    HemoglobinItem c.performance.item → c.hemoglobinMethod.isSome = true ∧
      (c.hemoglobinMethod = some .immunochromatography → c.performance.item = .hemoglobinQualitative)

def quantitativeRule : Rule Context Nat :=
  condition "3" "PDF333頁 D003(3)" fun c =>
    HemoglobinItem c.performance.item →
      c.hemoglobinMethod = some .quantitativeGoldColloid → c.performance.item = .hemoglobin

def purposeRule : Rule Context Nat :=
  condition "4" "PDF333–334頁 D003(4)" fun c =>
    c.performance.item = .calprotectin → c.purpose.isSome = true

def diagnosisRule : Rule Context Nat :=
  condition "4/a" "PDF333頁 D003(4)ア" fun c =>
    c.performance.item = .calprotectin → c.purpose = some .diagnosis →
      c.calprotectinMethod.isSome = true ∧ c.intestinalInfectionExcluded ∧
      c.symptomsPersistedAtLeastThreeMonths ∧ c.noVisibleBloodyStool ∧ c.chronicIbdSuspected ∧
      c.preEndoscopyDiagnosticAid

def Within (c : Context) (window : Option Period) : Prop :=
  ∃ h p, c.history = some h ∧ window = some p ∧ p.Contains c.performance.site.date ∧
    withinLimit h ⟨c.performance.site.patient, none, p⟩ (· == .calprotectin) 0 = some true

def monitoringRule : Rule Context Nat :=
  condition "4/i" "PDF333–334頁 D003(4)イ" fun c =>
    c.performance.item = .calprotectin →
      (c.purpose = some .ulcerativeColitisMonitoring ∨ c.purpose = some .crohnMonitoring) →
      c.calprotectinMethod.isSome = true ∧
        (Within c c.threeMonthWindow ∨
          (c.medicallyNecessaryMonthlyMonitoring ∧ Within c (some (Period.month c.performance.site.date.month))))

def colonoscopyRule : Rule Context Nat :=
  condition "4/u" "PDF334頁 D003(4)ウ" fun c =>
    c.performance.item = .calprotectin → c.colonoscopyMonthlySelection

def urinaryPgeSelectionRule : Rule Context Nat :=
  ⟨D001.colitisRule.id, D001.colitisRule.source, fun c _ =>
    c.performance.item = .calprotectin → c.purpose = some .ulcerativeColitisMonitoring →
      c.pgeMonthlySelection⟩

/-- 同月の潰瘍性大腸炎の病態把握にD001の主検査選択を共用する。 -/
def SharedColitisSelection (urine : D001.Context) (stool : Context) (mainPerformanceId : Nat) : Prop :=
  urine.performance.item = .prostaglandinEMajorMetabolite ∧
  stool.performance.item = .calprotectin ∧ stool.purpose = some .ulcerativeColitisMonitoring ∧
  urine.performance.site.patient = stool.performance.site.patient ∧
  urine.performance.site.date.month = stool.performance.site.date.month ∧
  urine.performance.id ≠ stool.performance.id ∧
  (urine.colitisMonthlySelection ↔ mainPerformanceId = urine.performance.id) ∧
  (stool.pgeMonthlySelection ↔ mainPerformanceId = stool.performance.id)

theorem sharedColitisSelection_exclusive
    (h : SharedColitisSelection urine stool main) :
    ¬ (urine.colitisMonthlySelection ∧ stool.pgeMonthlySelection) := by
  obtain ⟨_, _, _, _, _, distinct, hu, hs⟩ := h
  exact fun ⟨u, s⟩ => distinct ((hu.mp u).symm.trans (hs.mp s))

structure Documentation where
  diagnosisSummaryInChartAndClaim : Prop
  monitoringReasonAndResultInChartAndClaim : Prop

def documentationMet (c : Context) (d : Documentation) : Prop :=
  (c.performance.item = .calprotectin → c.purpose = some .diagnosis → d.diagnosisSummaryInChartAndClaim) ∧
  (c.performance.item = .calprotectin →
    (c.purpose = some .ulcerativeColitisMonitoring ∨ c.purpose = some .crohnMonitoring) →
    ¬ Within c c.threeMonthWindow → d.monitoringReasonAndResultInChartAndClaim)

def conditions :=
  [d017Rule, qualitativeRule, quantitativeRule, purposeRule, diagnosisRule, monitoringRule, colonoscopyRule, urinaryPgeSelectionRule]

def rules := primaryRules ++ conditions

def Eligible (c : Context) : Prop := Satisfies conditions c 0

def legacyInput (c : Context) : UrineFecalTests.Context :=
  { item := .fecal c.performance.item }

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ Eligible c ∧ assess (legacyInput c) = some (.charged ⟨p, 0⟩) := by
  have price : Satisfies primaryRules c p ↔ assess (legacyInput c) = some (.charged ⟨p, 0⟩) := by
    cases ht : c.performance.item <;>
      simp [Satisfies, primaryRules, itemRule, ht, itemNumber, legacyInput, assess, pointRule,
        requiresInHouse, isSediment, fecalPoints] <;> omega
  have criteria : Satisfies conditions c p ↔ Eligible c := by
    simp [Satisfies, Eligible, conditions, d017Rule, qualitativeRule, quantitativeRule, purposeRule,
      diagnosisRule, monitoringRule, colonoscopyRule, urinaryPgeSelectionRule, condition]
  constructor
  · intro h
    exact ⟨criteria.mp (fun r hr => h r (by simp [rules, hr])),
      price.mp (fun r hr => h r (by simp [rules, hr]))⟩
  · rintro ⟨hc, hp⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact price.mpr hp r hr
    · exact criteria.mpr hc r hr

theorem determines : DeterminesOn Eligible rules := by
  intro c eligible
  let p := fecalPoints c.performance.item
  have hp : assess (legacyInput c) = some (.charged ⟨p, 0⟩) := rfl
  refine ⟨⟨p, (satisfies_iff ..).mpr ⟨eligible, hp⟩⟩, ?_⟩
  intro a b ha hb
  have eq := ((satisfies_iff c a).mp ha).2.symm.trans ((satisfies_iff c b).mp hb).2
  simpa using eq

def judgmentTest (c : Context) : SpecimenJudgment.Test :=
  { major := 3, number := itemNumber c.performance.item, ordinaryCategory := .urineFecal }

def toSpecimenItem (kind points : Nat) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := points }

private def sample : Context :=
  { performance := ⟨1, ⟨2, 3, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩,
      .hemoglobinQualitative, none, some 4, none, none⟩
    d017BacteriaOrProtozoa := some false
    hemoglobinMethod := some .immunochromatography }

example : Satisfies rules sample 37 := by
  apply (satisfies_iff ..).mpr
  refine ⟨?_, rfl⟩
  simp [Eligible, Satisfies, conditions, d017Rule, qualitativeRule, quantitativeRule, purposeRule,
    diagnosisRule, monitoringRule, colonoscopyRule, urinaryPgeSelectionRule, condition, sample]

private def calprotectinSample : Context :=
  { sample with
    performance := { sample.performance with item := .calprotectin }
    purpose := some .diagnosis
    calprotectinMethod := some .elisa
    intestinalInfectionExcluded := True
    symptomsPersistedAtLeastThreeMonths := True
    noVisibleBloodyStool := True
    chronicIbdSuspected := True
    preEndoscopyDiagnosticAid := True
    colonoscopyMonthlySelection := True }

example : Satisfies rules calprotectinSample 268 := by
  apply (satisfies_iff ..).mpr
  refine ⟨?_, rfl⟩
  simp [Eligible, Satisfies, conditions, d017Rule, qualitativeRule, quantitativeRule, purposeRule,
    diagnosisRule, monitoringRule, colonoscopyRule, urinaryPgeSelectionRule, condition,
    HemoglobinItem, calprotectinSample, sample]

example : ¬ SatisfiableAt rules { calprotectinSample with noVisibleBloodyStool := False } := by
  rintro ⟨p, hp⟩
  exact (hp diagnosisRule (by simp [rules, conditions]) rfl rfl).2.2.2.1

example : ¬ SatisfiableAt rules { sample with hemoglobinMethod := some .quantitativeGoldColloid } := by
  rintro ⟨p, hp⟩
  exact Fecal.noConfusion (hp quantitativeRule (by simp [rules, conditions]) (Or.inl rfl) rfl)

end Sanri.MedicalFee.D003
