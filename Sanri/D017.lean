import Sanri.UrineSediment
import Sanri.SpecimenJudgment

/-! D017、基準診療日2026-10-22の外来検体検査実施料。 -/
namespace Sanri.MedicalFee.D017

open Sanri.Logic Sanri.History

inductive Item where
  | specializedMicroscopy | heatedAmoeba | otherMicroscopy
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.specializedMicroscopy, .heatedAmoeba, .otherMicroscopy]

def Item.number : Item → Nat
  | .specializedMicroscopy => 1
  | .heatedAmoeba => 2
  | .otherMicroscopy => 3

def Item.points : Item → Nat
  | .specializedMicroscopy => 65
  | .heatedAmoeba => 45
  | .otherMicroscopy => 67

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF189頁 D017 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (n : Nat) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF386頁 D017(" ++ toString n ++ ")", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

inductive Material where
  | urine | feces | sputum | aspirate | gastricFluid | duodenalFluid | bile | pus
  | eyeSecretion | nasalFluid | throatFluid | oralFluid | otherEligibleExudate
  deriving DecidableEq

inductive SedimentRelation where
  | noCombinedPerformance
  | combined (exam : Performance UrineSediment.Method) (main : Option UrineFecalTests.MainTest)
  deriving DecidableEq

structure Context where
  performance : Performance Item
  material : Option Material := none
  examinesBacteriaOrProtozoaOrSimilar : Option Bool := none
  concentrationSmear : Option Bool := none
  sediment : Option SedimentRelation := none
  /-- 同じ検査として識別した方法違いの実施と、その中から選んだ算定候補。 -/
  selectedInExamination : Option (List (Performance Item)) := none
  sameCauseSuspectedAcrossSites : Option Bool := none
  chosenSiteForCausativeSearch : Option Bool := none
  /-- 同日に実際に算定した尿沈渣の実施記録。 -/
  billedSediment : Option (List (Performance UrineSediment.Method)) := none

def Context.item (c : Context) := c.performance.item

def Context.sameSpecimen (c : Context) (exam : Performance UrineSediment.Method) : Option Bool :=
  c.performance.sameSpecimen { exam with item := c.item }

def Context.suppressed (c : Context) : Option Bool := do
  match ← c.sediment with
  | .noCombinedPerformance => return false
  | .combined exam main =>
    if ← c.sameSpecimen exam then
      match ← main with
      | .urineSediment => return true
      | .d017BacterialMicroscopy => return false
    else return false

def smearPoints : Nat := 35

/-- none は尿沈渣を主検査とした場合の包括。 -/
abbrev Result := Option (Nat × Nat)

def rate (i : Item) : Rule Context Result :=
  ⟨"primary/D017/item/" ++ toString i.number, primary (toString i.number),
    fun c r => c.item = i → ∀ base extra, r = some (base, extra) → base = i.points⟩

def sedimentChoice : Rule Context Result :=
  ⟨"primary/D017/note/unnumbered/1", primary "末尾注",
    fun c r => (c.suppressed = some true ∧ r = none) ∨
      (c.suppressed = some false ∧ r.isSome = true)⟩

def SmearKnown (c : Context) : Prop :=
  c.item = .specializedMicroscopy → c.concentrationSmear.isSome = true

def smear : Rule Context Result :=
  ⟨"primary/D017/item/1/note", primary "1 注", fun c r =>
    ∀ base extra, r = some (base, extra) →
      (c.item = .specializedMicroscopy ∧ c.concentrationSmear = some true ∧ extra = smearPoints) ∨
      ((c.item ≠ .specializedMicroscopy ∨ c.concentrationSmear = some false) ∧ extra = 0)⟩

def materialRule : Rule Context Unit :=
  ⟨"notice/D017/paragraph/1", notice 1, fun c _ =>
    c.material.isSome = true ∧ c.examinesBacteriaOrProtozoaOrSimilar = some true⟩

def oneExamination : Rule Context Unit :=
  ⟨"notice/D017/paragraph/2", notice 2, fun c _ =>
    c.performance.series.isSome = true ∧ c.selectedInExamination = some [c.performance]⟩

def documentation : Rule Context (Material → Prop) :=
  ⟨"notice/D017/paragraph/3", notice 3, fun c recorded =>
    ∃ rows, c.billedSediment = some rows ∧ ∀ e ∈ rows,
      c.performance.site.patient = e.site.patient →
      c.performance.site.institution = e.site.institution →
      c.performance.site.sameDay e.site = true →
      ∃ m, c.material = some m ∧ recorded m⟩

def causativeSite : Rule Context Unit :=
  ⟨"notice/D017/paragraph/4", notice 4, fun c _ =>
    c.sameCauseSuspectedAcrossSites = some false ∨
      (c.sameCauseSuspectedAcrossSites = some true ∧ c.chosenSiteForCausativeSearch = some true)⟩

def eligibilityRules := [materialRule, oneExamination, causativeSite]
def resultRules := [sedimentChoice, smear, rate .specializedMicroscopy, rate .heatedAmoeba,
  rate .otherMicroscopy]

def InScope (c : Context) : Prop :=
  Satisfies eligibilityRules c () ∧ c.suppressed.isSome = true ∧
    (c.suppressed = some false → SmearKnown c)

def legacyRequest (c : Context) (suppressed : Bool) : SpecimenTests.Request :=
  { code := .d017, number := c.item.number
    conditions := { concentrationSmear := c.concentrationSmear == some true
                    sameSpecimenUrineSediment := suppressed
                    urineSedimentIsMain := suppressed } }

def legacyResult : Result → SpecimenTests.ItemResult
  | none => .suppressedByMainUrineSediment
  | some (base, extra) => .charged base extra

theorem legacy_eval (c : Context) (suppressed : Bool) :
    SpecimenTests.assessOne (legacyRequest c suppressed) =
      if suppressed then some .suppressedByMainUrineSediment else
        some (.charged c.item.points
          (if c.item = .specializedMicroscopy ∧ c.concentrationSmear = some true then smearPoints else 0)) := by
  unfold legacyRequest
  cases h : c.item <;> cases suppressed <;> cases s : c.concentrationSmear with
  | none => rfl
  | some x => cases x <;> rfl

theorem legacy_iff (c : Context) (r : Result) (h : InScope c) (b : Bool)
    (hb : c.suppressed = some b) :
    Satisfies resultRules c r ↔
      SpecimenTests.assessOne (legacyRequest c b) = some (legacyResult r) := by
  rw [legacy_eval]
  cases b with
  | true =>
    cases r <;> simp [resultRules, satisfies_cons, satisfies_nil, sedimentChoice, smear, rate,
      hb, legacyResult]
  | false =>
    cases r with
    | none =>
      simp [resultRules, satisfies_cons, satisfies_nil, sedimentChoice, hb, legacyResult]
    | some value =>
      obtain ⟨base, extra⟩ := value
      cases hi : c.item <;> try {
        simp [resultRules, satisfies_cons, satisfies_nil, sedimentChoice, smear, rate, hi, hb,
          legacyResult, Item.points] <;> omega }
      have hs := h.2.2 hb hi
      cases hm : c.concentrationSmear with
      | none => simp [hm] at hs
      | some method =>
        cases method <;> simp [resultRules, satisfies_cons, satisfies_nil, sedimentChoice,
          smear, rate, hi, hb, hm, legacyResult, Item.points] <;> omega

theorem determines : DeterminesOn InScope resultRules := by
  intro c h
  have known := h.2.1
  cases hb : c.suppressed with
  | none => simp [hb] at known
  | some b =>
    let result : Result := if b then none else some (c.item.points,
      if c.item = .specializedMicroscopy ∧ c.concentrationSmear = some true then smearPoints else 0)
    have witness := (legacy_iff c result h b hb).mpr (by
      rw [legacy_eval]
      cases b <;> rfl)
    refine ⟨⟨result, witness⟩, ?_⟩
    intro a d ha hd
    have same := ((legacy_iff _ _ h b hb).mp ha).symm.trans ((legacy_iff _ _ h b hb).mp hd)
    cases a <;> cases d <;> simp_all [legacyResult]
    exact Prod.ext same.1 same.2

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 17, number := i.number, ordinaryCategory := .microbiological }

def execution (kind : Nat) (r : Result) : Option Examinations.SpecimenItem :=
  r.map fun (base, extra) => { kind := kind, executionPoints := base + extra }

/-- 双方の実施、選択および点数を同じ組で検証する。 -/
def SedimentPair (c : Context) (urine : UrineSediment.Context)
    (r : Result) (u : UrineSediment.Result) : Prop :=
  InScope c ∧ Satisfies resultRules c r ∧
  UrineSediment.InScope urine.performance.item urine ∧
  Satisfies (UrineSediment.resultRules urine.performance.item) urine u ∧
  ∃ main, c.sediment = some (.combined urine.performance (some main)) ∧
    c.sameSpecimen urine.performance = some true ∧
    urine.d017 = some (.combined { c.performance with item := () } (some main))

private def samplePerformance : Performance Item :=
  ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .specializedMicroscopy, none, some 1, some 2, none⟩

private def sample : Context :=
  { performance := samplePerformance
    material := some .sputum
    examinesBacteriaOrProtozoaOrSimilar := some true
    concentrationSmear := some true
    sediment := some .noCombinedPerformance
    selectedInExamination := some [samplePerformance]
    sameCauseSuspectedAcrossSites := some false }

private theorem sampleScope : InScope sample := by
  simp [InScope, eligibilityRules, satisfies_cons, satisfies_nil, materialRule, oneExamination,
    causativeSite, Context.suppressed, SmearKnown, Context.item, sample, samplePerformance]

example : Satisfies resultRules sample (some (65, 35)) :=
  (legacy_iff _ _ sampleScope false rfl).mpr rfl

example : ¬ InScope { sample with sediment := none } := by
  simp [InScope, Context.suppressed]

end Sanri.MedicalFee.D017
