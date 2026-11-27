import Sanri.BloodChemistryLate
import Sanri.SpecimenJudgment
import Sanri.SpecimenRules
import Sanri.History

namespace Sanri.MedicalFee.D004

open Sanri.Logic Sanri.History

/-! 2026-10-22 の外来実施料。併施時の選択を固定した個別算定と、別の結果型を持つ包括・記載要件を扱う。 -/

inductive Item where
  | huhner
  | jointFluid
  | gastricDuodenal
  | semen
  | cervicalMucus
  | csfGeneral
  | elastaseQualitative
  | tearIgE
  | elastase
  | microbubble
  | iggIndex
  | oligoclonal
  | mbp
  | tau
  | phosphoTau
  | amyloidRatio
  | phosphoTauAmyloidRatio
  | csfImmunology
  | csfSmear
  | other
  | cxcl10
  deriving DecidableEq, Repr

/-- 通知で追加された準用検査には本文の項番を割り当てない。 -/
def Item.number : Item → Option Nat
  | .huhner => some 1
  | .jointFluid => some 2
  | .gastricDuodenal => some 3
  | .semen => some 4
  | .cervicalMucus => some 5
  | .csfGeneral => some 6
  | .elastaseQualitative => some 7
  | .tearIgE => some 7
  | .elastase => some 8
  | .microbubble => some 9
  | .iggIndex => some 10
  | .oligoclonal => some 11
  | .mbp => some 12
  | .tau => some 13
  | .phosphoTau => some 14
  | .amyloidRatio => some 15
  | .phosphoTauAmyloidRatio => some 15
  | .csfImmunology => some 16
  | .csfSmear => some 17
  | .other => some 18
  | .cxcl10 => none

theorem number_range (item : Item) :
    item.number = none ∨ ∃ n, item.number = some n ∧ 1 ≤ n ∧ n ≤ 18 := by
  cases item <;> first | (left; rfl) | (right; exact ⟨_, rfl, by decide, by decide⟩)

def Item.fixedPoints : Item → Option Nat
  | .huhner => some 20
  | .jointFluid => some 50
  | .gastricDuodenal => some 55
  | .semen => some 70
  | .cervicalMucus => some 75
  | .csfGeneral => some 77
  | .elastaseQualitative => some 100
  | .tearIgE => some 100
  | .elastase => some 113
  | .microbubble => some 200
  | .iggIndex => some 390
  | .oligoclonal => some 507
  | .mbp => some 570
  | .tau => some 622
  | .phosphoTau => some 641
  | .amyloidRatio => some 1282
  | .phosphoTauAmyloidRatio => some 1282
  | _ => none

def ledgerItems : List Item :=
  [.huhner, .jointFluid, .gastricDuodenal, .semen, .cervicalMucus, .csfGeneral, .elastaseQualitative, .tearIgE, .elastase, .microbubble, .iggIndex, .oligoclonal, .mbp, .tau, .phosphoTau, .amyloidRatio, .phosphoTauAmyloidRatio, .csfImmunology, .csfSmear, .other]

example : (ledgerItems.filterMap Item.number).eraseDups = List.range' 1 18 := by decide
theorem ledger_complete (item : Item) (h : item ≠ .cxcl10) : item ∈ ledgerItems := by
  cases item <;> first | contradiction | decide

inductive Method where
  | redLatexFlowThrough | cleia | eclia | elisa | other
  deriving DecidableEq, Repr

inductive HamPatient where
  | newlyDiagnosed | establishedHighOrModerate | other
  deriving DecidableEq, Repr

inductive ReferenceTarget where
  | d015 | d017 | other (division : UrineFecalTests.OtherReference)
  deriving DecidableEq, Repr

structure ReferenceResolution where
  target : ReferenceTarget
  points : Nat
  sectionNotesAppliedAndSatisfied : Bool
  deriving DecidableEq, Repr

structure Context where
  item : Item
  reference : Option ReferenceResolution := none
  jointEffusion : Option Bool := none
  suspectedCrystalArthritis : Option Bool := none
  jointPriorClaimsInSeries : Option Nat := none
  jointAloneOrPrincipalAgainstD017 : Option Bool := none
  method : Option Method := none
  chorioamnionitisDiagnosis : Option Bool := none
  gestationCompletedWeeks : Option Nat := none
  suspectedThreatenedPretermBirth : Option Bool := none
  allergicConjunctivitisDiagnosticAid : Option Bool := none
  tearIgEMonthPriorClaims : Option Nat := none
  pregnantOrNewborn : Option Bool := none
  priorClaimsInConfirmedWeek : Option Nat := none
  multipleSclerosisDiagnosis : Option Bool := none
  cjdDiagnosis : Option Bool := none
  dementiaDiagnosis : Option Bool := none
  patientPriorClaims : Option Nat := none
  guidelineFollowed : Option Bool := none
  eligibleAlzheimerPatient : Option Bool := none
  amyloidPathologyForDrugDecision : Option Bool := none
  /-- 測定法に対応する二成分を髄液で同時に測定したこと。 -/
  csfSimultaneousAnalytes : Option Bool := none
  restartingAfterDiscontinuationAndOver18Months : Option Bool := none
  aloneOrPrincipalAmongTauRatios : Option Bool := none
  hamActivityAssessment : Option Bool := none
  hamPatient : Option HamPatient := none
  hamPriorClaimsInConfirmedYear : Option Nat := none
  medicallyNecessaryRepeat : Option Bool := none
  deriving DecidableEq, Repr

/-- 既算定履歴からの射影。候補自身を履歴から除いた状態で照会する。 -/
def patientClaims (site : Site) (history : ClaimHistory Item) (items : List Item) : Option Nat :=
  count history ⟨site.patient, none, .through site.date⟩ items.contains

def tearIgEMonthClaims (site : Site) (history : ClaimHistory Item) : Option Nat :=
  count history ⟨site.patient, none, .month site.date.month⟩ (· == .tearIgE)

/-- 起算を確定した週・年を受け取る。期間と網羅範囲のどちらが不足しても未確定。 -/
def claimsInConfirmedPeriod (site : Site) (history : ClaimHistory Item) (item : Item)
    (period : Option Period) : Option Nat := do
  let span ← period
  if span.Contains site.date then
    count history ⟨site.patient, none, span⟩ (· == item)
  else none

private def primary : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF175頁 D004", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def amendment : SourceRef :=
  ⟨.notification, "保医発0930第2号・別添1", "2026-10-01適用",
    "PDF2頁 指示1 D004(15)", .checkedAgainstSource, none⟩

def referenceTarget (i : Item) (r : ReferenceTarget) : Prop :=
  match i, r with
  | .csfImmunology, .d015 | .csfSmear, .d017 => True
  | .other, .other _ => True
  | _, _ => False

private def referencePoints (c : Context) : Option Nat :=
  c.reference.map ReferenceResolution.points

private def cxcl10Tariff : Option Nat :=
  Item.phosphoTau.fixedPoints.bind fun p => Item.amyloidRatio.fixedPoints.map (p + ·)

def scheduled (c : Context) : Option Nat :=
  match c.item with
  | .cxcl10 => cxcl10Tariff
  | .csfImmunology | .csfSmear | .other => referencePoints c
  | i => i.fixedPoints

private def itemRule (n : Nat) : Rule Context Nat :=
  ⟨"primary/D004/item/" ++ toString n,
    { primary with location := primary.location ++ " 項" ++ toString n }, fun c p =>
    c.item.number = some n → c.item.fixedPoints = some p⟩

private def referenceRule (n : Nat) : Rule Context Nat :=
  ⟨"primary/D004/item/" ++ toString n,
    { primary with location := primary.location ++ " 項" ++ toString n }, fun c p =>
    c.item.number = some n → ∃ r, c.reference = some r ∧ referenceTarget c.item r.target ∧ r.points = p⟩

def referenceNoteRule : Rule Context Nat :=
  ⟨"primary/D004/item/18/note", primary, fun c _ =>
    c.item = .other → ∃ r, c.reference = some r ∧ r.sectionNotesAppliedAndSatisfied = true⟩

private structure Clause where
  suffix : String
  source : SourceRef
  items : List Item
  checks : Context → List (Option Bool)

private def Clause.required (a : Clause) (c : Context) : List (Option Bool) :=
  if a.items.contains c.item then a.checks c else []

private def Clause.rule (a : Clause) : Rule Context Nat :=
  ⟨"notice/D004/paragraph/" ++ a.suffix, a.source,
    fun c _ => ∀ fact ∈ a.required c, fact = some true⟩

private def obstetricChecks (c : Context) : List (Option Bool) :=
  [c.chorioamnionitisDiagnosis, c.gestationCompletedWeeks.map (fun w => decide (22 ≤ w ∧ w < 37)),
    c.suspectedThreatenedPretermBirth]

private def ratioMethods (c : Context) : Option Bool :=
  c.method.map fun method =>
    (c.item == .amyloidRatio && method == .cleia) ||
    (c.item == .phosphoTauAmyloidRatio && method == .eclia)

private def amyloidClaimLimit (c : Context) : Option Bool :=
  match c.patientPriorClaims with
  | some 0 => some true
  | some 1 => c.restartingAfterDiscontinuationAndOver18Months
  | some (_ + 2) => some false
  | none => none

private def hamClaimLimit (c : Context) : Option Bool :=
  match c.hamPriorClaimsInConfirmedYear with
  | some 0 => some true
  | some 1 => c.medicallyNecessaryRepeat
  | some (_ + 2) => some false
  | none => none

private def amyloidChecks (c : Context) : List (Option Bool) :=
  [c.guidelineFollowed, c.eligibleAlzheimerPatient, c.amyloidPathologyForDrugDecision,
    ratioMethods c, c.csfSimultaneousAnalytes, amyloidClaimLimit c]

private def clauses : List Clause := [
  ⟨"1", notice "PDF334頁 D004(1)", [.jointFluid], fun c =>
    [c.jointEffusion, c.suspectedCrystalArthritis, c.jointPriorClaimsInSeries.map (· == 0),
      c.jointAloneOrPrincipalAgainstD017]⟩,
  ⟨"6", notice "PDF334頁 D004(6)", [.elastaseQualitative], fun c =>
    c.method.map (· == .redLatexFlowThrough) :: obstetricChecks c⟩,
  ⟨"7", notice "PDF334頁 D004(7)", [.tearIgE], fun c =>
    [c.allergicConjunctivitisDiagnosticAid, c.tearIgEMonthPriorClaims.map (· == 0)]⟩,
  ⟨"8", notice "PDF334頁 D004(8)", [.elastase], obstetricChecks⟩,
  ⟨"9", notice "PDF334頁 D004(9)", [.microbubble], fun c =>
    [c.pregnantOrNewborn, c.priorClaimsInConfirmedWeek.map (· == 0)]⟩,
  ⟨"10", notice "PDF334頁 D004(10)", [.iggIndex, .oligoclonal, .mbp], fun c =>
    [c.multipleSclerosisDiagnosis]⟩,
  ⟨"11", notice "PDF334頁 D004(11)", [.tau], fun c =>
    [c.cjdDiagnosis, c.patientPriorClaims.map (· == 0)]⟩,
  ⟨"12", notice "PDF334頁 D004(12)", [.phosphoTau], fun c =>
    [c.dementiaDiagnosis, c.patientPriorClaims.map (· == 0)]⟩,
  ⟨"13/a", notice "PDF334–335頁 D004(13)ア", [.amyloidRatio, .phosphoTauAmyloidRatio],
    amyloidChecks⟩,
  ⟨"13/i", notice "PDF335頁 D004(13)イ", [.phosphoTau, .amyloidRatio, .phosphoTauAmyloidRatio],
    fun c => [c.aloneOrPrincipalAmongTauRatios]⟩]

/-- 親段落の見出しが指定する二検査の範囲。 -/
def ratioScopeRule : Rule Item Bool :=
  ⟨"notice/D004/paragraph/13", notice "PDF334頁 D004(13) 見出し",
    fun item member => member = true ↔ item = .amyloidRatio ∨ item = .phosphoTauAmyloidRatio⟩

def hamNewPatientRule : Rule Context Bool :=
  ⟨"notice/D004/paragraph/15/a", amendment, fun c inBranch =>
    c.item = .cxcl10 → ∃ patient, c.hamPatient = some patient ∧
      (inBranch = true ↔ patient = .newlyDiagnosed)⟩

def hamEstablishedPatientRule : Rule Context Bool :=
  ⟨"notice/D004/paragraph/15/i", amendment, fun c inBranch =>
    c.item = .cxcl10 → ∃ patient, c.hamPatient = some patient ∧
      (inBranch = true ↔ patient = .establishedHighOrModerate)⟩

private def HamEligible (c : Context) : Prop :=
  hamNewPatientRule.holds c true ∨ hamEstablishedPatientRule.holds c true

def cxcl10Rule : Rule Context Nat :=
  ⟨"notice/D004/paragraph/15", amendment, fun c p =>
    c.item = .cxcl10 → c.method = some .elisa ∧ c.hamActivityAssessment = some true ∧
      hamClaimLimit c = some true ∧ HamEligible c ∧ some p = cxcl10Tariff⟩

def rules : List (Rule Context Nat) :=
  (List.range' 1 15).map itemRule ++ [referenceRule 16, referenceRule 17, referenceRule 18,
    referenceNoteRule, cxcl10Rule] ++ clauses.map Clause.rule

/-- 診断等の入力と通知上の算定条件を確認した、個別実施料の対象範囲。 -/
def Eligible (c : Context) : Prop :=
  (∀ fact ∈ clauses.flatMap (·.required c), fact = some true) ∧
  ((c.item = .csfImmunology ∨ c.item = .csfSmear ∨ c.item = .other) →
    ∃ r, c.reference = some r ∧ referenceTarget c.item r.target ∧
      (c.item = .other → r.sectionNotesAppliedAndSatisfied = true)) ∧
  (c.item = .cxcl10 → c.method = some .elisa ∧ c.hamActivityAssessment = some true ∧
    hamClaimLimit c = some true ∧ HamEligible c)

private theorem fixed_scheduled (c : Context) (n : Nat) (h : c.item.number = some n)
    (hn : n ∈ List.range' 1 15) : scheduled c = c.item.fixedPoints := by
  cases hi : c.item <;> simp_all [Item.number, scheduled, List.mem_range'] <;> omega

private theorem reference_scheduled (c : Context) (n : Nat) (h : c.item.number = some n)
    (hn : n = 16 ∨ n = 17 ∨ n = 18) : scheduled c = referencePoints c := by
  cases hi : c.item <;> simp_all [Item.number, scheduled] <;> omega

theorem sound_on (c : Context) (p : Nat) (h : Eligible c) (price : scheduled c = some p) :
    Satisfies rules c p := by
  simp only [rules, satisfies_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r member
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp member
    intro active
    exact (fixed_scheduled c n active hn).symm.trans price
  · have ref (n : Nat) (hn : n = 16 ∨ n = 17 ∨ n = 18) :
        (referenceRule n).holds c p := by
      intro active
      have target : c.item = .csfImmunology ∨ c.item = .csfSmear ∨ c.item = .other := by
        cases hi : c.item <;> simp_all [Item.number] <;> omega
      obtain ⟨r, hr, ht, _⟩ := h.2.1 target
      refine ⟨r, hr, ht, ?_⟩
      rw [reference_scheduled c n active hn] at price
      simpa [referencePoints, hr] using price
    intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ref 16 (.inl rfl)
    · exact ref 17 (.inr (.inl rfl))
    · exact ref 18 (.inr (.inr rfl))
    · intro active
      obtain ⟨ref, hr, _, notes⟩ := h.2.1 (.inr (.inr active))
      exact ⟨ref, hr, notes active⟩
    · intro active
      obtain ⟨method, purpose, limit, patient⟩ := h.2.2 active
      exact ⟨method, purpose, limit, patient, by simpa [scheduled, active] using price.symm⟩
  · intro r member
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    exact fun fact hf => h.1 fact (List.mem_flatMap.mpr ⟨a, ha, hf⟩)

theorem result_points (c : Context) (p : Nat) (h : Satisfies rules c p) :
    scheduled c = some p := by
  simp only [rules, satisfies_append] at h
  have ref (n : Nat) (hn : n = 16 ∨ n = 17 ∨ n = 18)
      (member : referenceRule n ∈ [referenceRule 16, referenceRule 17, referenceRule 18,
        referenceNoteRule, cxcl10Rule]) (active : c.item.number = some n) : scheduled c = some p := by
    obtain ⟨r, hr, _, hp⟩ := h.1.2 _ member active
    rw [reference_scheduled c n active hn]
    simp [referencePoints, hr, hp]
  cases hi : c.item
  case cxcl10 =>
    have hp := (h.1.2 cxcl10Rule (by simp) hi).2.2.2.2
    simpa [scheduled, hi] using hp.symm
  case csfImmunology => exact ref 16 (.inl rfl) (by simp) (by simp [hi, Item.number])
  case csfSmear => exact ref 17 (.inr (.inl rfl)) (by simp) (by simp [hi, Item.number])
  case other => exact ref 18 (.inr (.inr rfl)) (by simp) (by simp [hi, Item.number])
  all_goals
    have hn : c.item.number = some (c.item.number.getD 0) := by simp [hi, Item.number]
    have hm : c.item.number.getD 0 ∈ List.range' 1 15 := by
      rw [hi]
      decide
    exact (fixed_scheduled c _ hn hm).trans
      (h.1.1 _ (List.mem_map.mpr ⟨_, hm, rfl⟩) hn)

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ Eligible c ∧ scheduled c = some p := by
  refine ⟨fun h => ⟨?_, result_points c p h⟩, fun ⟨h, price⟩ => sound_on c p h price⟩
  simp only [rules, satisfies_append] at h
  refine ⟨?_, ?_, ?_⟩
  · intro fact member
    obtain ⟨a, ha, hf⟩ := List.mem_flatMap.mp member
    exact h.2 _ (List.mem_map.mpr ⟨a, ha, rfl⟩) fact hf
  · intro target
    have ref (n : Nat) (member : referenceRule n ∈ [referenceRule 16, referenceRule 17,
        referenceRule 18, referenceNoteRule, cxcl10Rule]) (active : c.item.number = some n) :
        ∃ r, c.reference = some r ∧ referenceTarget c.item r.target ∧
          (c.item = .other → r.sectionNotesAppliedAndSatisfied = true) := by
      obtain ⟨r, hr, ht, _⟩ := h.1.2 _ member active
      refine ⟨r, hr, ht, fun other => ?_⟩
      obtain ⟨r', hr', notes⟩ := h.1.2 referenceNoteRule (by simp) other
      exact (Option.some.inj (hr'.symm.trans hr)) ▸ notes
    rcases target with hi | hi | hi
    · exact ref 16 (by simp) (by simp [hi, Item.number])
    · exact ref 17 (by simp) (by simp [hi, Item.number])
    · exact ref 18 (by simp) (by simp [hi, Item.number])
  · intro active
    obtain ⟨method, purpose, limit, patient, _⟩ := h.1.2 cxcl10Rule (by simp) active
    exact ⟨method, purpose, limit, patient⟩

theorem determines_on : DeterminesOn Eligible rules := by
  intro c h
  have price : ∃ p, scheduled c = some p := by
    cases hi : c.item
    case cxcl10 => exact ⟨1923, by simp [scheduled, hi, cxcl10Tariff, Item.fixedPoints]⟩
    case csfImmunology =>
      obtain ⟨r, hr, _, _⟩ := h.2.1 (.inl hi)
      exact ⟨r.points, by simp [scheduled, hi, referencePoints, hr]⟩
    case csfSmear =>
      obtain ⟨r, hr, _, _⟩ := h.2.1 (.inr (.inl hi))
      exact ⟨r.points, by simp [scheduled, hi, referencePoints, hr]⟩
    case other =>
      obtain ⟨r, hr, _, _⟩ := h.2.1 (.inr (.inr hi))
      exact ⟨r.points, by simp [scheduled, hi, referencePoints, hr]⟩
    all_goals simp [scheduled, hi, Item.fixedPoints]
  obtain ⟨p, hp⟩ := price
  exact ⟨⟨p, sound_on c p h hp⟩, fun _ _ a b =>
    Option.some.inj ((result_points _ _ a).symm.trans (result_points _ _ b))⟩

private def catalogReferenceTarget : SpecimenTests.Code → Option ReferenceTarget
  | .d015 => some .d015
  | .d017 => some .d017
  | .d009 => some (.other .d009)
  | .d010 => some (.other .d010)
  | _ => none

/-- D009・D010・D015・D017の既存評価で算定される準用先との対応。
具体的な検査種類を準用先の項番・枝へ同定する作業は入力側で行う。 -/
def CatalogReference (c : Context) (requests : List SpecimenTests.Request) : Prop :=
  ∃ r, c.reference = some r ∧ referenceTarget c.item r.target ∧
    requests ≠ [] ∧
    (∀ request ∈ requests, catalogReferenceTarget request.code = some r.target ∧
      ∃ base extra, SpecimenTests.assessOne request = some (.charged base extra)) ∧
    SpecimenTests.points requests = some r.points ∧
    (c.item = .other → r.sectionNotesAppliedAndSatisfied = true)

/-- 一般検査の費用に含める、通知に例示された構成検査の分類。 -/
inductive Component where
  | volume | color | turbidity | mucusAmount | odor | acidity | pepsin | lactate
  | rennin | proteinColorReaction | toxin | occultBlood | ova | urobilin | cholesterol
  | fluidSubstanceQualitativeOrSemiquantitative
  | spermCount | spermMorphology | spermMotility | viscosity | driedSmearMicroscopy
  | appearance | specificGravity | globulinReaction | tryptophanReaction | cellCount | cellTyping
  | csfProteinGlucoseBilirubinKetonesQualitativeOrSemiquantitative
  deriving DecidableEq, Repr

private def inclusionRule (paragraph : String) (item : Item) (components : List Component) :
    Rule Item (List Component) :=
  ⟨"notice/D004/paragraph/" ++ paragraph, notice ("PDF334頁 D004(" ++ paragraph ++ ")"),
    fun i separatelyCharged => i = item → ∀ c ∈ components, c ∉ separatelyCharged⟩

def inclusionRules : List (Rule Item (List Component)) := [
  inclusionRule "2" .gastricDuodenal [.volume, .color, .turbidity, .mucusAmount, .odor,
    .acidity, .pepsin, .lactate, .rennin, .proteinColorReaction, .toxin, .occultBlood, .ova,
    .urobilin, .cholesterol, .fluidSubstanceQualitativeOrSemiquantitative],
  inclusionRule "3" .semen [.volume, .spermCount, .spermMorphology, .spermMotility],
  inclusionRule "4" .cervicalMucus [.volume, .viscosity, .color, .driedSmearMicroscopy],
  inclusionRule "5" .csfGeneral [.appearance, .specificGravity, .globulinReaction, .tryptophanReaction,
    .cellCount, .cellTyping, .csfProteinGlucoseBilirubinKetonesQualitativeOrSemiquantitative]]

inductive Documentation where
  | amyloidRepeatMedicalBasis | hamPatientCategory | hamMedicalNecessity
  deriving DecidableEq, Repr

def amyloidDocumentationRule : Rule Context (List Documentation) :=
  ⟨"notice/D004/paragraph/13/a", notice "PDF335頁 D004(13)ア 摘要欄",
    fun c notes =>
      (c.item = .amyloidRatio ∨ c.item = .phosphoTauAmyloidRatio) →
      c.patientPriorClaims = some 1 → .amyloidRepeatMedicalBasis ∈ notes⟩

def hamDocumentationRule : Rule Context (List Documentation) :=
  ⟨"notice/D004/paragraph/15", amendment, fun c notes =>
    c.item = .cxcl10 → .hamPatientCategory ∈ notes ∧ .hamMedicalNecessity ∈ notes⟩

/-- 群ごとに適格性と項目の同定を確認した実施。採取順は同日内で確認済みのものを受ける。 -/
structure SameDayBundle (Test : Type) where
  site : Site
  urine : List Test
  puncture : List Test
  firstBloodDraw : List Test
  laterBloodDraws : List (List Test)

def sameDayBundleRule (Test : Type) : Rule (SameDayBundle Test) (List (List Test)) :=
  ⟨"notice/D004/paragraph/14", notice "PDF335頁 D004(14)", fun c blocks =>
    blocks = (c.urine ++ c.puncture ++ c.firstBloodDraw) :: c.laterBloodDraws⟩

def d007BundlePoints (c : SameDayBundle BloodChemistry.Item) (points : List Nat) : Prop :=
  ∃ groups, (sameDayBundleRule BloodChemistry.Item).holds c groups ∧
    points = groups.map BloodChemistry.pointsForItems

/-- D004の検体をD007の既存包括計算に渡す。準用点数を包括点数へ重ねて加算しない。 -/
def d004BundleReference (puncture : Context) (group : SameDayBundle BloodChemistry.Item)
    (item : BloodChemistry.Item) : Prop :=
  puncture.item = .other ∧
    (∃ r, puncture.reference = some r ∧ r.target = .other .d007 ∧
      r.sectionNotesAppliedAndSatisfied = true) ∧ item ∈ group.puncture

/-- D001の準用を確認した尿検査をD007の同日包括への入力に対応付ける。
準用先の具体的な項目との対応は呼出元で確認する。 -/
def d001BundleReference (urine : UrineFecalTests.Context)
    (group : SameDayBundle BloodChemistry.Item) (item : BloodChemistry.Item) : Prop :=
  UrineFecalTests.assess urine = some (.requiresReference (.other .d007) true) ∧ item ∈ group.urine

example : DeterminesAt rules { item := .huhner } :=
  determines_on _ (by simp [Eligible, clauses, Clause.required])

private def hamExample : Context :=
  { item := .cxcl10, method := some .elisa, hamActivityAssessment := some true,
    hamPatient := some .newlyDiagnosed, hamPriorClaimsInConfirmedYear := some 0 }

example : Satisfies rules hamExample 1923 :=
  sound_on _ _ (by simp [hamExample, Eligible, clauses, Clause.required, hamClaimLimit, HamEligible, hamNewPatientRule]) rfl

example : ¬ SatisfiableAt rules { hamExample with hamPriorClaimsInConfirmedYear := none } := by
  rintro ⟨p, hp⟩
  have h := hp cxcl10Rule (by simp [rules]) rfl
  simp [hamExample, hamClaimLimit] at h

example : ¬ SatisfiableAt rules { hamExample with hamPriorClaimsInConfirmedYear := some 2 } := by
  rintro ⟨p, hp⟩
  have h := hp cxcl10Rule (by simp [rules]) rfl
  simp [hamExample, hamClaimLimit] at h

example (site : Site) :
    d007BundlePoints {
      site := site
      urine := [.bun]
      puncture := [.creatinine]
      firstBloodDraw := [.glucose, .albumin, .totalProtein]
      laterBloodDraws := [[.bun]] } [93, 11] := by
  refine ⟨_, rfl, ?_⟩
  rfl

def judgmentTest (item : Item) (category : SpecimenJudgment.Category) : SpecimenJudgment.Test :=
  { major := 4, number := item.number.getD 0, ordinaryCategory := category,
    variant := if item = .tearIgE ∨ item = .phosphoTauAmyloidRatio then 1 else 0 }

theorem judgment_category (item : Item) (category : SpecimenJudgment.Category) :
    SpecimenJudgment.categoryFor (judgmentTest item category) = some category := by
  cases item <;> simp [judgmentTest, SpecimenJudgment.categoryFor, SpecimenJudgment.geneRouting]

end Sanri.MedicalFee.D004
