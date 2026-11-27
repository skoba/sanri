import Sanri.BloodMorphology
import Sanri.History

namespace Sanri.MedicalFee.D006

open Sanri.Logic Sanri.History

inductive Item where
  | bleedingTime
  | prothrombinTime
  | clotRetraction | capillaryResistance
  | fibrinogenSemi | fibrinogenQuant | cryofibrinogen
  | thrombinTime
  | snakeVenom | thromboelastograph | heparinResistance
  | aptt
  | plateletAdhesion
  | antithrombinActivity | antithrombinAntigen
  | fdpQual | fdpSemi | plasmin | plasminActivity | alpha1Antitrypsin
  | fibrinMonomerQual
  | fdpQuant
  | plasminogenActivity | plasminogenAntigen | inhibitorQual
  | dDimerQual
  | vwfActivity
  | dDimer
  | antiplasmin | dDimerSemi
  | alpha2Macroglobulin
  | pivkaII
  | inhibitorVIII | inhibitorIX
  | vwfAntigen
  | pic
  | proteinSAntigen
  | proteinSActivity
  | tat
  | betaThromboglobulin
  | plateletFactor4
  | prothrombinFragment
  | thrombomodulin
  | fibrinMonomer
  | proteinCAntigen
  | factorII | factorV | factorVII | factorVIII | factorIX | factorX | factorXI | factorXII | factorXIII
  | proteinCActivity
  | tpaPai1
  | adamtsActivity
  | plateletDifferential | plateletOther
  | adamtsInhibitor
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .bleedingTime => 1
  | .prothrombinTime => 2
  | .clotRetraction | .capillaryResistance => 3
  | .fibrinogenSemi | .fibrinogenQuant | .cryofibrinogen => 4
  | .thrombinTime => 5
  | .snakeVenom | .thromboelastograph | .heparinResistance => 6
  | .aptt => 7
  | .plateletAdhesion => 8
  | .antithrombinActivity | .antithrombinAntigen => 9
  | .fdpQual | .fdpSemi | .plasmin | .plasminActivity | .alpha1Antitrypsin => 10
  | .fibrinMonomerQual => 11
  | .fdpQuant => 12
  | .plasminogenActivity | .plasminogenAntigen | .inhibitorQual => 13
  | .dDimerQual => 14
  | .vwfActivity => 15
  | .dDimer => 16
  | .antiplasmin | .dDimerSemi => 17
  | .alpha2Macroglobulin => 18
  | .pivkaII => 19
  | .inhibitorVIII | .inhibitorIX => 20
  | .vwfAntigen => 21
  | .pic => 22
  | .proteinSAntigen => 23
  | .proteinSActivity => 24
  | .tat => 25
  | .betaThromboglobulin => 26
  | .plateletFactor4 => 27
  | .prothrombinFragment => 28
  | .thrombomodulin => 29
  | .fibrinMonomer => 30
  | .proteinCAntigen => 31
  | .factorII | .factorV | .factorVII | .factorVIII | .factorIX | .factorX | .factorXI | .factorXII | .factorXIII => 32
  | .proteinCActivity => 33
  | .tpaPai1 => 34
  | .adamtsActivity => 35
  | .plateletDifferential | .plateletOther => 36
  | .adamtsInhibitor => 37

def Item.points : Item → Nat
  | .bleedingTime => 15
  | .prothrombinTime => 18
  | .clotRetraction | .capillaryResistance => 19
  | .fibrinogenSemi | .fibrinogenQuant | .cryofibrinogen => 23
  | .thrombinTime => 25
  | .snakeVenom | .thromboelastograph | .heparinResistance => 28
  | .aptt => 29
  | .plateletAdhesion => 64
  | .antithrombinActivity | .antithrombinAntigen => 70
  | .fdpQual | .fdpSemi | .plasmin | .plasminActivity | .alpha1Antitrypsin => 80
  | .fibrinMonomerQual => 93
  | .fdpQuant => 95
  | .plasminogenActivity | .plasminogenAntigen | .inhibitorQual => 100
  | .dDimerQual => 121
  | .vwfActivity => 126
  | .dDimer => 127
  | .antiplasmin | .dDimerSemi => 128
  | .alpha2Macroglobulin => 138
  | .pivkaII => 143
  | .inhibitorVIII | .inhibitorIX => 144
  | .vwfAntigen => 147
  | .pic => 150
  | .proteinSAntigen => 152
  | .proteinSActivity => 163
  | .tat => 166
  | .betaThromboglobulin => 171
  | .plateletFactor4 => 173
  | .prothrombinFragment => 192
  | .thrombomodulin => 204
  | .fibrinMonomer => 215
  | .proteinCAntigen => 220
  | .factorII | .factorV | .factorVII | .factorVIII | .factorIX | .factorX | .factorXI | .factorXII | .factorXIII => 223
  | .proteinCActivity => 227
  | .tpaPai1 => 240
  | .adamtsActivity => 400
  | .plateletDifferential => 450
  | .adamtsInhibitor => 1000
  | .plateletOther => 50

def ledgerItems : List Item := [
  .bleedingTime,
  .prothrombinTime,
  .clotRetraction, .capillaryResistance,
  .fibrinogenSemi, .fibrinogenQuant, .cryofibrinogen,
  .thrombinTime,
  .snakeVenom, .thromboelastograph, .heparinResistance,
  .aptt,
  .plateletAdhesion,
  .antithrombinActivity, .antithrombinAntigen,
  .fdpQual, .fdpSemi, .plasmin, .plasminActivity, .alpha1Antitrypsin,
  .fibrinMonomerQual,
  .fdpQuant,
  .plasminogenActivity, .plasminogenAntigen, .inhibitorQual,
  .dDimerQual,
  .vwfActivity,
  .dDimer,
  .antiplasmin, .dDimerSemi,
  .alpha2Macroglobulin,
  .pivkaII,
  .inhibitorVIII, .inhibitorIX,
  .vwfAntigen,
  .pic,
  .proteinSAntigen,
  .proteinSActivity,
  .tat,
  .betaThromboglobulin,
  .plateletFactor4,
  .prothrombinFragment,
  .thrombomodulin,
  .fibrinMonomer,
  .proteinCAntigen,
  .factorII, .factorV, .factorVII, .factorVIII, .factorIX, .factorX, .factorXI, .factorXII, .factorXIII,
  .proteinCActivity,
  .tpaPai1,
  .adamtsActivity,
  .plateletDifferential, .plateletOther,
  .adamtsInhibitor]

example : (ledgerItems.map Item.number).eraseDups = List.range' 1 37 := by decide

theorem item_mem (item : Item) : item ∈ ledgerItems := by cases item <;> decide

inductive VwfMethod where
  | srid | rocketImmunoelectrophoresis | otherConfirmed
  deriving DecidableEq, Repr

inductive ThrombomodulinPurpose where
  | connectiveTissueDiagnosis | connectiveTissueFollowup | dicObservation | subsequentMofObservation
  deriving DecidableEq, Repr

inductive Thrombosis where
  | dic | venous | pulmonaryEmbolism | other
  deriving DecidableEq, Repr

inductive AdamtsUse where
  | diagnosticAid | suspectedRecurrence | firstMonthFollowup | treatmentContinuation
  deriving DecidableEq, Repr

structure Followup where
  onset : Date
  oneMonthWindow : Option Bool := none
  week : Option Period := none
  acquiredTtp : Option Bool := none

structure Context where
  performance : Performance Item
  acquiredHypofibrinogenemia : Option Bool := none
  fibrinogenTreatmentDecision : Option Bool := none
  operatingRoomOrEquivalent : Option Bool := none
  deviceOutsideLaboratory : Option Bool := none
  guidelineFollowed : Option Bool := none
  unexplainedPtProlongation : Option Bool := none
  unexplainedApttProlongation : Option Bool := none
  bleedingCoagulationPurpose : Option Bool := none
  inhibitorQuantitationConfirmed : Option Bool := none
  vwfMethod : Option VwfMethod := none
  thrombomodulinPurpose : Option ThrombomodulinPurpose := none
  fibrinMonomerTarget : Option Thrombosis := none
  fibrinMonomerDiagnosisAndFollowup : Option Bool := none
  simultaneousSurvey : Option (List (Performance Item)) := none
  principalPerformance : Option Nat := none
  adamtsUse : Option AdamtsUse := none
  unexplainedThrombocytopenia : Option Bool := none
  severeAdamtsReduction : Option Bool := none
  followup : Option Followup := none
  plasmaExchange : Option Bool := none
  immunosuppression : Option Bool := none
  caplacizumab : Option Bool := none
  suspectedCongenitalPlateletDysfunction : Option Bool := none
  differentialDiagnosisAid : Option Bool := none
  reagentTypes : Option Nat := none
  repeatMedicalNecessity : Option Bool := none
  priorClaims : Option (ClaimHistory Item) := none

def Context.item (c : Context) : Item := c.performance.item

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF176〜177頁 D006 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF339〜340頁 D006 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def condition (id : String) (applies required : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D006/paragraph/" ++ id, notice id, fun c _ => applies c → required c⟩

def priorCount (c : Context) (period : Period) : Option Nat :=
  c.priorClaims.bind fun h =>
    count h ⟨c.performance.site.patient, none, period⟩ (· == c.item)

def FibrinogenAddOnIndication (c : Context) : Prop :=
  c.item ∈ [.fibrinogenSemi, .fibrinogenQuant] ∧
  c.acquiredHypofibrinogenemia = some true ∧ c.fibrinogenTreatmentDecision = some true ∧
  c.operatingRoomOrEquivalent = some true

def rapidFibrinogenPoints : Nat := 150

def FibrinogenPrimaryFailure (c : Context) : Prop :=
  c.item ∉ [.fibrinogenSemi, .fibrinogenQuant] ∨
  c.acquiredHypofibrinogenemia = some false ∨ c.fibrinogenTreatmentDecision = some false ∨
  c.operatingRoomOrEquivalent = some false

def FibrinogenNoticeConfirmed (c : Context) : Prop :=
  c.deviceOutsideLaboratory = some true ∧ c.guidelineFollowed = some true

def FibrinogenNoticeFailure (c : Context) : Prop :=
  c.deviceOutsideLaboratory = some false ∨ c.guidelineFollowed = some false

def fibrinogenNoteRule : Rule Context Nat :=
  ⟨"primary/D006/item/4/note", primary "項4 注", fun c addition =>
    addition > 0 → FibrinogenAddOnIndication c ∧ addition = rapidFibrinogenPoints⟩

def fibrinogenNoticeRule : Rule Context Nat :=
  ⟨"notice/D006/paragraph/2", notice "(2)", fun c addition =>
    addition > 0 → FibrinogenNoticeConfirmed c⟩

def AddOnKnown (c : Context) : Prop :=
  (FibrinogenAddOnIndication c ∧ FibrinogenNoticeConfirmed c) ∨
    FibrinogenPrimaryFailure c ∨ FibrinogenNoticeFailure c

def noAdditionRule : Rule Context Nat :=
  ⟨"unclassified/D006/confirmed-no-addition",
    ⟨.manualInterpretation, "D006 加算の確定条件", "2026-10-22", "加算要件不成立の確認", .unchecked, none⟩,
    fun c addition => addition = 0 → FibrinogenPrimaryFailure c ∨ FibrinogenNoticeFailure c⟩

def addOnRules : List (Rule Context Nat) :=
  [fibrinogenNoteRule, fibrinogenNoticeRule, noAdditionRule]

theorem addition_satisfies_iff (c : Context) (p : Nat) :
    Satisfies addOnRules c p ↔
      (p = rapidFibrinogenPoints ∧ FibrinogenAddOnIndication c ∧ FibrinogenNoticeConfirmed c) ∨
      (p = 0 ∧ (FibrinogenPrimaryFailure c ∨ FibrinogenNoticeFailure c)) := by
  simp only [addOnRules, satisfies_cons, satisfies_nil, and_true, fibrinogenNoteRule,
    fibrinogenNoticeRule, noAdditionRule]
  cases p with
  | zero => simp [rapidFibrinogenPoints]
  | succ p => simp [and_comm, and_assoc]

private theorem addOn_disjoint (c : Context)
    (yes : FibrinogenAddOnIndication c ∧ FibrinogenNoticeConfirmed c)
    (no : FibrinogenPrimaryFailure c ∨ FibrinogenNoticeFailure c) : False := by
  rcases yes with ⟨⟨item, diagnosis, purpose, room⟩, equipment, guideline⟩
  simp [FibrinogenPrimaryFailure, FibrinogenNoticeFailure, item, diagnosis, purpose, room,
    equipment, guideline] at no

theorem addition_determines : DeterminesOn AddOnKnown addOnRules := by
  intro c known
  refine ⟨?_, ?_⟩
  · rcases known with yes | no
    · exact ⟨_, (addition_satisfies_iff _ _).mpr (.inl ⟨rfl, yes⟩)⟩
    · exact ⟨0, (addition_satisfies_iff _ _).mpr (.inr ⟨rfl, no⟩)⟩
  · intro a b ha hb
    rcases (addition_satisfies_iff _ _).mp ha with ⟨rfl, yes⟩ | ⟨rfl, no⟩ <;>
      rcases (addition_satisfies_iff _ _).mp hb with ⟨rfl, yes'⟩ | ⟨rfl, no'⟩
    · rfl
    · exact (addOn_disjoint c yes no').elim
    · exact (addOn_disjoint c yes' no).elim
    · rfl

def bleedingTimeRule : Rule Context Bool :=
  ⟨"notice/D006/paragraph/1", notice "(1)",
    fun c earLobeCollectionSeparatelyCharged =>
      c.item = .bleedingTime → earLobeCollectionSeparatelyCharged = false⟩

def crossMixingRule : Rule Context Unit :=
  condition "3" (fun c => c.item = .inhibitorQual) fun c =>
    c.unexplainedPtProlongation = some true ∨ c.unexplainedApttProlongation = some true

def pivkaRule : Rule Context Unit :=
  condition "4" (fun c => c.item = .pivkaII) (fun c => c.bleedingCoagulationPurpose = some true)

def inhibitorQuantitationRule : Rule Context Unit :=
  condition "5" (fun c => c.item ∈ [.inhibitorVIII, .inhibitorIX])
    (fun c => c.inhibitorQuantitationConfirmed = some true)

def vwfRule : Rule Context Unit :=
  condition "6" (fun c => c.item = .vwfAntigen) (fun c => c.vwfMethod.isSome = true)

def thrombomodulinRule : Rule Context Unit :=
  condition "7" (fun c => c.item = .thrombomodulin) (fun c => c.thrombomodulinPurpose.isSome = true)

def fibrinMonomerRule : Rule Context Unit :=
  condition "8/a" (fun c => c.item = .fibrinMonomer) fun c =>
    (∃ target ∈ [Thrombosis.dic, .venous, .pulmonaryEmbolism], c.fibrinMonomerTarget = some target) ∧
    c.fibrinMonomerDiagnosisAndFollowup = some true

private def competingMarkers : List Item := [.tat, .prothrombinFragment, .fibrinMonomer]

def MarkerSelection (c : Context) : Prop :=
  ∃ surveyed, c.simultaneousSurvey = some surveyed ∧
    ∀ p ∈ surveyed, p.item ∈ competingMarkers → p.id ≠ c.performance.id →
      c.performance.simultaneousWith p = some false ∨
        (c.performance.simultaneousWith p = some true ∧ c.principalPerformance = some c.performance.id)

def markerCombinationRule : Rule Context Unit :=
  condition "8/i" (fun c => c.item ∈ competingMarkers) MarkerSelection

def fibrinMonomerParagraph : Rule Context Unit :=
  ⟨"notice/D006/paragraph/8", notice "(8)", fun c _ =>
    fibrinMonomerRule.holds c () ∧ markerCombinationRule.holds c ()⟩

def DiagnosticUse (c : Context) : Prop :=
  c.adamtsUse = some .diagnosticAid ∨ c.adamtsUse = some .suspectedRecurrence

def ConfirmedWeekUnused (c : Context) (f : Followup) : Prop :=
  ∃ week, f.week = some week ∧ week.Contains c.performance.site.date ∧ priorCount c week = some 0

def FirstMonth (c : Context) (acquiredOnly : Bool) : Prop :=
  ∃ f, c.followup = some f ∧ f.onset.key ≤ c.performance.site.date.key ∧
    f.oneMonthWindow = some true ∧ (acquiredOnly = true → f.acquiredTtp = some true) ∧
    ConfirmedWeekUnused c f

def TreatmentContinuation (c : Context) : Prop :=
  c.plasmaExchange = some true ∧ c.immunosuppression = some true ∧ c.caplacizumab = some true ∧
  ∃ f, c.followup = some f ∧ f.onset.key ≤ c.performance.site.date.key ∧ ConfirmedWeekUnused c f

def activityDiagnosticRule : Rule Context Unit :=
  condition "9/a" (fun c => c.item = .adamtsActivity ∧ DiagnosticUse c)
    (fun c => c.unexplainedThrombocytopenia = some true)

def activityFollowupRule : Rule Context Unit :=
  condition "9/i" (fun c => c.item = .adamtsActivity ∧ c.adamtsUse = some .firstMonthFollowup)
    (fun c => FirstMonth c false)

def activityTreatmentRule : Rule Context Unit :=
  condition "9/u" (fun c => c.item = .adamtsActivity ∧ c.adamtsUse = some .treatmentContinuation)
    TreatmentContinuation

def activityParagraph : Rule Context Unit :=
  condition "9" (fun c => c.item = .adamtsActivity) fun c =>
    (DiagnosticUse c ∨ c.adamtsUse = some .firstMonthFollowup ∨ c.adamtsUse = some .treatmentContinuation) ∧
    activityDiagnosticRule.holds c () ∧ activityFollowupRule.holds c () ∧ activityTreatmentRule.holds c ()

def plateletCount (c : Context) : Option Nat :=
  priorCount c (Period.through c.performance.site.date)

def plateletDifferentialRule : Rule Context Unit :=
  condition "10/a" (fun c => c.item = .plateletDifferential) fun c =>
    c.suspectedCongenitalPlateletDysfunction = some true ∧
    c.differentialDiagnosisAid = some true ∧ (∃ n, c.reagentTypes = some n ∧ 3 ≤ n) ∧
    (plateletCount c = some 0 ∨ (∃ n, plateletCount c = some n ∧ 0 < n ∧
      c.repeatMedicalNecessity = some true))

def plateletInclusionRule : Rule Context (List BloodMorphology.Item) :=
  ⟨"notice/D006/paragraph/10/i", notice "(10)イ", fun c separate =>
    c.item.number = 36 → .completeBloodCount ∉ separate⟩

def plateletParagraph : Rule Context (List BloodMorphology.Item) :=
  ⟨"notice/D006/paragraph/10", notice "(10)", fun c separate =>
    plateletDifferentialRule.holds c () ∧ plateletInclusionRule.holds c separate⟩

def inhibitorDiagnosticRule : Rule Context Unit :=
  condition "11/a" (fun c => c.item = .adamtsInhibitor ∧ DiagnosticUse c)
    (fun c => c.severeAdamtsReduction = some true)

def inhibitorFollowupRule : Rule Context Unit :=
  condition "11/i" (fun c => c.item = .adamtsInhibitor ∧ c.adamtsUse = some .firstMonthFollowup)
    (fun c => FirstMonth c true)

def inhibitorParagraph : Rule Context Unit :=
  condition "11" (fun c => c.item = .adamtsInhibitor) fun c =>
    (DiagnosticUse c ∨ c.adamtsUse = some .firstMonthFollowup) ∧
    inhibitorDiagnosticRule.holds c () ∧ inhibitorFollowupRule.holds c ()

structure Documentation where
  diagnosisOrRecurrenceDate : Option Date := none
  medicalNecessityRecorded : Bool := false

def activityFollowupDocumentation : Rule Context Documentation :=
  ⟨"notice/D006/paragraph/9/i", notice "(9)イ", fun c d =>
    c.item = .adamtsActivity → c.adamtsUse = some .firstMonthFollowup →
      ∀ f, c.followup = some f → d.diagnosisOrRecurrenceDate = some f.onset⟩

def activityTreatmentDocumentation : Rule Context Documentation :=
  ⟨"notice/D006/paragraph/9/u", notice "(9)ウ", fun c d =>
    c.item = .adamtsActivity → c.adamtsUse = some .treatmentContinuation →
      d.medicalNecessityRecorded = true⟩

def inhibitorFollowupDocumentation : Rule Context Documentation :=
  ⟨"notice/D006/paragraph/11/i", notice "(11)イ", fun c d =>
    c.item = .adamtsInhibitor → c.adamtsUse = some .firstMonthFollowup →
      ∀ f, c.followup = some f → d.diagnosisOrRecurrenceDate = some f.onset⟩

def plateletDocumentation : Rule Context Documentation :=
  ⟨"notice/D006/paragraph/10/a", notice "(10)ア", fun c d =>
    c.item = .plateletDifferential → ∀ n, plateletCount c = some n →
      0 < n → d.medicalNecessityRecorded = true⟩

def eligibilityRules : List (Rule Context Unit) :=
  [crossMixingRule, pivkaRule, inhibitorQuantitationRule, vwfRule, thrombomodulinRule,
    fibrinMonomerParagraph, activityParagraph, plateletDifferentialRule, inhibitorParagraph]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def Item.bundleEligible (i : Item) : Bool := decide (14 ≤ i.number ∧ i.number ≤ 34)

structure DrawGroup where
  anchor : Performance Item
  tests : List Context

def DrawGroup.Valid (g : DrawGroup) : Prop :=
  g.tests ≠ [] ∧ (g.tests.map fun c => c.performance.id).Nodup ∧
  ((g.tests.filter fun c => c.item.bundleEligible).map Context.item).Nodup ∧
  ∀ c ∈ g.tests, Eligible c ∧ g.anchor.sameDraw c.performance = some true

def DrawGroup.bundled (g : DrawGroup) : List Context :=
  g.tests.filter fun c => c.item.bundleEligible

def DrawGroup.other (g : DrawGroup) : List Context :=
  g.tests.filter fun c => !c.item.bundleEligible

def bundlePoints : Nat → Option Nat
  | 0 | 1 | 2 => none
  | 3 | 4 => some 530
  | _ => some 722

private def baseSum (tests : List Context) : Nat :=
  (tests.map fun c => c.item.points).sum

def drawPoints (g : DrawGroup) : Nat :=
  baseSum g.other + (bundlePoints g.bundled.length).getD (baseSum g.bundled)

/-- 個々の所定点数は項ごとに参照する。群の包括が成立する場合は群の点数を別に評価する。 -/
private def itemRule (number : Nat) : Rule Context Nat :=
  ⟨"primary/D006/item/" ++ toString number, primary ("項" ++ toString number),
    fun c p => c.item.number = number → p = c.item.points⟩

def itemRules : List (Rule Context Nat) := (List.range' 1 37).map itemRule

theorem item_satisfies_iff (c : Context) (p : Nat) :
    Satisfies itemRules c p ↔ p = c.item.points := by
  constructor
  · intro h
    have hn : c.item.number ∈ List.range' 1 37 := by
      rw [← show (ledgerItems.map Item.number).eraseDups = List.range' 1 37 by decide]
      exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨_, item_mem c.item, rfl⟩)
    exact h (itemRule c.item.number) (List.mem_map.mpr ⟨_, hn, rfl⟩) rfl
  · rintro rfl rule member
    rcases List.mem_map.mp member with ⟨_, _, rfl⟩
    intro _
    rfl

structure DrawResult where
  groupPoints : Nat
  otherPoints : Nat
  total : Nat
  deriving DecidableEq, Repr

def drawBaseRule : Rule DrawGroup DrawResult :=
  ⟨"primary/D006/item/14..34", primary "項14〜34", fun g r =>
    (g.bundled.length < 3 → r.groupPoints = baseSum g.bundled) ∧
      r.otherPoints = baseSum g.other⟩

def drawBundleRule : Rule DrawGroup DrawResult :=
  ⟨"primary/D006/note/unnumbered/1+primary/D006/note/i+primary/D006/note/ro",
    primary "区分注・イ・ロ", fun g r =>
    (∀ n, bundlePoints g.bundled.length = some n → r.groupPoints = n) ∧
      r.total = r.otherPoints + r.groupPoints⟩

def drawScopeRule : Rule DrawGroup DrawResult :=
  ⟨"unclassified/D006/confirmed-draw",
    ⟨.manualInterpretation, "D006 外来モデルの入力範囲", "2026-10-22", "採血・項目・適格性", .unchecked, none⟩,
    fun g _ => g.Valid⟩

def drawRules : List (Rule DrawGroup DrawResult) := [drawBaseRule, drawBundleRule, drawScopeRule]

private theorem bundle_iff (n base p : Nat) :
    ((n < 3 → p = base) ∧ (∀ v, bundlePoints n = some v → p = v)) ↔
      p = (bundlePoints n).getD base := by
  rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | n⟩⟩⟩⟩ <;> simp [bundlePoints] <;> omega

theorem draw_satisfies_iff (g : DrawGroup) (r : DrawResult) :
    Satisfies drawRules g r ↔
      g.Valid ∧ r.groupPoints = (bundlePoints g.bundled.length).getD (baseSum g.bundled) ∧
      r.otherPoints = baseSum g.other ∧ r.total = drawPoints g := by
  simp only [drawRules, satisfies_cons, satisfies_nil, and_true, drawBaseRule, drawBundleRule, drawScopeRule]
  constructor
  · rintro ⟨⟨base, other⟩, ⟨bundle, total⟩, valid⟩
    have points := (bundle_iff _ _ _).mp ⟨base, bundle⟩
    exact ⟨valid, points, other, by simp [drawPoints, total, other, points]⟩
  · rintro ⟨valid, points, other, total⟩
    have ⟨base, bundle⟩ := (bundle_iff _ _ _).mpr points
    exact ⟨⟨base, other⟩, ⟨bundle, by simp [drawPoints, total, other, points]⟩, valid⟩

theorem draw_determines : DeterminesOn DrawGroup.Valid drawRules := by
  intro g valid
  refine ⟨⟨⟨_, _, drawPoints g⟩, (draw_satisfies_iff _ _).mpr ⟨valid, rfl, rfl, rfl⟩⟩, ?_⟩
  intro a b ha hb
  have ha' := (draw_satisfies_iff _ _).mp ha
  have hb' := (draw_satisfies_iff _ _).mp hb
  cases a
  cases b
  simp_all

/-- 加算は適格な個別実施ごとに決め、同一採血の所定点数へ加える。 -/
def Additions : List Context → Nat → Prop
  | [], p => p = 0
  | c :: rest, p => ∃ addition tail, Satisfies addOnRules c addition ∧
      Additions rest tail ∧ p = addition + tail

theorem additions_unique (tests : List Context) (known : ∀ c ∈ tests, AddOnKnown c) :
    ∃ p, Additions tests p ∧ ∀ q, Additions tests q → q = p := by
  induction tests with
  | nil => exact ⟨0, rfl, fun _ h => h⟩
  | cons c rest ih =>
    have ⟨⟨a, ha⟩, ua⟩ := addition_determines c (known c (by simp))
    have ⟨t, ht, ut⟩ := ih (fun other h => known other (by simp [h]))
    refine ⟨a + t, ⟨a, t, ha, ht, rfl⟩, ?_⟩
    rintro _ ⟨a', t', ha', ht', rfl⟩
    rw [ua _ _ ha' ha, ut _ ht']

def Payable (g : DrawGroup) (p : Nat) : Prop :=
  ∃ base addition, Satisfies drawRules g base ∧ Additions g.tests addition ∧
    p = base.total + addition

theorem payable_determines (g : DrawGroup) (valid : g.Valid)
    (known : ∀ c ∈ g.tests, AddOnKnown c) : ∃ p, Payable g p ∧ ∀ q, Payable g q → q = p := by
  have ⟨⟨base, hb⟩, ub⟩ := draw_determines g valid
  have ⟨add, ha, ua⟩ := additions_unique g.tests known
  refine ⟨base.total + add, ⟨base, add, hb, ha, rfl⟩, ?_⟩
  rintro _ ⟨b, a, hb', ha', rfl⟩
  rw [ub _ _ hb' hb, ua _ ha']

def judgmentTest (item : Item) : SpecimenJudgment.Test :=
  { major := 6, number := item.number, ordinaryCategory := .hematological }

theorem judgment_category (item : Item) :
    SpecimenJudgment.categoryFor (judgmentTest item) = some .hematological := rfl

private def exampleSite : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def exampleTest (id : Nat) (item : Item) : Context :=
  { performance := { id := id, site := exampleSite, item := item, draw := some 7 } }

private def bundleExample : DrawGroup :=
  { anchor := (exampleTest 0 .prothrombinTime).performance
    tests := [exampleTest 1 .dDimer, exampleTest 2 .vwfActivity, exampleTest 3 .factorVIII] }

private theorem exampleEligible (id : Nat) (item : Item)
    (member : item ∈ [Item.dDimer, .vwfActivity, .factorVIII]) : Eligible (exampleTest id item) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, exampleTest, Context.item,
      condition, crossMixingRule, pivkaRule, inhibitorQuantitationRule, vwfRule, thrombomodulinRule,
      fibrinMonomerParagraph, fibrinMonomerRule, markerCombinationRule, competingMarkers,
      activityParagraph, plateletDifferentialRule, inhibitorParagraph]

private theorem bundle_example_valid : bundleExample.Valid := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro c h
  simp only [bundleExample, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨exampleEligible _ _ (by decide), rfl⟩
  · exact ⟨exampleEligible _ _ (by decide), rfl⟩
  · exact ⟨exampleEligible _ _ (by decide), rfl⟩

example : Satisfies drawRules bundleExample ⟨530, 0, 530⟩ :=
  (draw_satisfies_iff _ _).mpr ⟨bundle_example_valid, rfl, rfl, rfl⟩

private def rapidExample : Context :=
  { exampleTest 1 .fibrinogenQuant with
    acquiredHypofibrinogenemia := some true
    fibrinogenTreatmentDecision := some true
    operatingRoomOrEquivalent := some true
    deviceOutsideLaboratory := some true
    guidelineFollowed := some true }

example : Satisfies addOnRules rapidExample 150 :=
  (addition_satisfies_iff _ _).mpr (.inl ⟨rfl, ⟨by decide, rfl, rfl, rfl⟩, rfl, rfl⟩)

example : Satisfies addOnRules { rapidExample with guidelineFollowed := some false } 0 :=
  (addition_satisfies_iff _ _).mpr (.inr ⟨rfl, .inr (.inr rfl)⟩)

example : ¬ SatisfiableAt addOnRules { rapidExample with guidelineFollowed := none } := by
  simp [SatisfiableAt, addition_satisfies_iff, FibrinogenNoticeConfirmed,
    FibrinogenPrimaryFailure, FibrinogenNoticeFailure, rapidExample, exampleTest, Context.item]

end Sanri.MedicalFee.D006
