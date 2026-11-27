import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment

/-! D013、基準診療日2026-10-22の外来検体検査実施料。 -/
namespace Sanri.MedicalFee.D013

open Sanri.Logic Sanri.History

inductive Item where
  | hbsAntigenSimple
  | hbsAntibodyQual
  | hbsAntibodySemi
  | hbsAntigen
  | hbsAntibody
  | hbeAntigen
  | hbeAntibody
  | hcvAntibody
  | hcvCore
  | hcvCombo
  | hbcAntibody
  | hcvCoreAntibody
  | haIgM
  | haAntibody
  | hbcIgM
  | hcvProteinQual
  | hcvProteinSemi
  | heIgA
  | hcvSerotype
  | hbcrAntigen
  | deltaAntibody
  | hcvSpecific
  | hbvGenotype
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .hbsAntigenSimple => 1
  | .hbsAntibodyQual => 2
  | .hbsAntibodySemi => 2
  | .hbsAntigen => 3
  | .hbsAntibody => 3
  | .hbeAntigen => 4
  | .hbeAntibody => 4
  | .hcvAntibody => 5
  | .hcvCore => 5
  | .hcvCombo => 5
  | .hbcAntibody => 6
  | .hcvCoreAntibody => 7
  | .haIgM => 8
  | .haAntibody => 8
  | .hbcIgM => 8
  | .hcvProteinQual => 9
  | .hcvProteinSemi => 9
  | .heIgA => 10
  | .hcvSerotype => 11
  | .hbcrAntigen => 12
  | .deltaAntibody => 13
  | .hcvSpecific => 14
  | .hbvGenotype => 14

def Item.variant : Item → Nat
  | .hbsAntigenSimple => 0
  | .hbsAntibodyQual => 0
  | .hbsAntibodySemi => 1
  | .hbsAntigen => 0
  | .hbsAntibody => 1
  | .hbeAntigen => 0
  | .hbeAntibody => 1
  | .hcvAntibody => 0
  | .hcvCore => 1
  | .hcvCombo => 2
  | .hbcAntibody => 0
  | .hcvCoreAntibody => 0
  | .haIgM => 0
  | .haAntibody => 1
  | .hbcIgM => 2
  | .hcvProteinQual => 0
  | .hcvProteinSemi => 1
  | .heIgA => 0
  | .hcvSerotype => 0
  | .hbcrAntigen => 0
  | .deltaAntibody => 0
  | .hcvSpecific => 0
  | .hbvGenotype => 1

def Item.points : Item → Nat
  | .hbsAntigenSimple => 29
  | .hbsAntibodyQual => 32
  | .hbsAntibodySemi => 32
  | .hbsAntigen => 88
  | .hbsAntibody => 88
  | .hbeAntigen => 98
  | .hbeAntibody => 98
  | .hcvAntibody => 102
  | .hcvCore => 102
  | .hcvCombo => 102
  | .hbcAntibody => 130
  | .hcvCoreAntibody => 143
  | .haIgM => 146
  | .haAntibody => 146
  | .hbcIgM => 146
  | .hcvProteinQual => 160
  | .hcvProteinSemi => 160
  | .heIgA => 210
  | .hcvSerotype => 215
  | .hbcrAntigen => 246
  | .deltaAntibody => 330
  | .hcvSpecific => 340
  | .hbvGenotype => 340

def ledgerItems : List Item :=
  [.hbsAntigenSimple, .hbsAntibodyQual, .hbsAntibodySemi, .hbsAntigen, .hbsAntibody,
   .hbeAntigen, .hbeAntibody, .hcvAntibody, .hcvCore, .hcvCombo,
   .hbcAntibody, .hcvCoreAntibody, .haIgM, .haAntibody, .hbcIgM,
   .hcvProteinQual, .hcvProteinSemi, .heIgA, .hcvSerotype, .hbcrAntigen,
   .deltaAntibody, .hcvSpecific, .hbvGenotype]

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF186頁 D013 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (n : Nat) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF379頁 D013(" ++ toString n ++ ")", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def rateRule (i : Item) : Rule Item Nat :=
  ⟨"primary/D013/item/" ++ toString i.number, primary (toString i.number),
    fun item points => item = i → points = i.points⟩

def rates := ledgerItems.map rateRule

theorem rate_iff (i : Item) (p : Nat) : Satisfies rates i p ↔ p = i.points := by
  constructor
  · intro h
    have mem : i ∈ ledgerItems := by cases i <;> decide
    exact h (rateRule i) (List.mem_map.mpr ⟨i, mem, rfl⟩) rfl
  · intro h r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro eq
    simpa [eq] using h

inductive Method where
  | immunochromatography | hemagglutination | particleAgglutination | simpleEia
  | goldColloidAgglutination | eia | irma | eclia
  deriving DecidableEq

inductive Specimen where
  | serum | plasma
  deriving DecidableEq

/-- 選択された算定候補と外来で確認した事実。
同時実施の候補リストは関連する検査を確認した場合に渡す。 -/
structure Context where
  performance : Performance Item
  method : Option Method := none
  specimen : Option Specimen := none
  reactorScreenBeforeTreatment : Option Bool := none
  simultaneousLocal : Option (List (Performance Item)) := none
  otherPayableLocal : Option (List (Performance Item)) := none
  priorClaims : Option (ClaimHistory Item) := none
  confirmedHcv : Option Bool := none
  confirmedHbv : Option Bool := none
  choosesTreatment : Option Bool := none
  diagnosisOrResponsePurpose : Option Bool := none
  simultaneousHbvDna : Option Bool := none
  mainWhenHbvDnaMeasured : Option Bool := none

def Context.item (c : Context) := c.performance.item

def noPrior (c : Context) (period : Period) : Prop :=
  ∃ h, c.priorClaims = some h ∧
    count h ⟨c.performance.site.patient, none, period⟩ (· == c.item) = some 0

private def commonMethods : List Method :=
  [.hemagglutination, .particleAgglutination, .simpleEia, .goldColloidAgglutination]

def antigenMethod : Rule Context Unit :=
  ⟨"notice/D013/paragraph/1", notice 1, fun c _ => c.item = .hbsAntigenSimple →
    ∃ m ∈ .immunochromatography :: commonMethods, c.method = some m⟩

def antibodyMethod : Rule Context Unit :=
  ⟨"notice/D013/paragraph/2", notice 2, fun c _ => c.item = .hbsAntibodySemi →
    ∃ m ∈ commonMethods, c.method = some m⟩

private def screeningItems : List Item := [.hbsAntigen, .hbsAntibody, .hbcAntibody]

def reactivationScreen : Rule Context Unit :=
  ⟨"notice/D013/paragraph/3", notice 3, fun c _ => c.item ∈ screeningItems →
    c.reactorScreenBeforeTreatment = some false ∨
      (c.reactorScreenBeforeTreatment = some true ∧ ∃ records,
        c.simultaneousLocal = some records ∧ c.performance.simultaneous.isSome = true ∧
        (∀ e ∈ records, e.item ∈ screeningItems →
          (c.performance.simultaneousWith e).isSome = true) ∧
        ((∀ i ∈ screeningItems, i = c.item ∨ ∃ e ∈ records,
          e.item = i ∧ c.performance.simultaneousWith e = some true) →
          noPrior c (Period.through c.performance.site.date)))⟩

def coreMethod : Rule Context Unit :=
  ⟨"notice/D013/paragraph/4", notice 4, fun c _ =>
    (c.item = .hcvCore → c.method = some .eia ∨ c.method = some .irma) ∧
    (c.item = .hcvCombo → c.method = some .eclia)⟩

/-- 同時実施された二種類から選ばれた結果を入力に取り、点数による優先順位は設けない。 -/
def SingleChoice (a b : Item) (c : Context) : Prop :=
  ∀ i, (c.item = a ∧ i = b) ∨ (c.item = b ∧ i = a) →
    ∃ records, c.otherPayableLocal = some records ∧
      ∀ r ∈ records, r.item = i → c.performance.simultaneousWith r = some false

def hbCoreChoice : Rule Context Unit :=
  ⟨"notice/D013/paragraph/5", notice 5, fun c _ => SingleChoice .hbcAntibody .hbcIgM c⟩

def haChoice : Rule Context Unit :=
  ⟨"notice/D013/paragraph/6", notice 6, fun c _ => SingleChoice .haAntibody .haIgM c⟩

def serotype : Rule Context Unit :=
  ⟨"notice/D013/paragraph/7", notice 7, fun c _ => c.item = .hcvSerotype →
    c.method = some .eia ∧ c.confirmedHcv = some true ∧ c.choosesTreatment = some true ∧
      noPrior c (Period.through c.performance.site.date)⟩

def coreRelatedAntigen : Rule Context Unit :=
  ⟨"notice/D013/paragraph/8", notice 8, fun c _ => c.item = .hbcrAntigen →
    c.diagnosisOrResponsePurpose = some true ∧
    (c.specimen = some .serum ∨ c.specimen = some .plasma) ∧
    noPrior c (Period.month c.performance.site.date.month) ∧
    (c.simultaneousHbvDna = some false ∨
      (c.simultaneousHbvDna = some true ∧ c.mainWhenHbvDnaMeasured = some true))⟩

def genotype : Rule Context Unit :=
  ⟨"notice/D013/paragraph/9", notice 9, fun c _ => c.item = .hbvGenotype →
    c.confirmedHbv = some true ∧ c.choosesTreatment = some true ∧
      noPrior c (Period.through c.performance.site.date)⟩

def eligibilityRules :=
  [antigenMethod, antibodyMethod, reactivationScreen, coreMethod, hbCoreChoice,
   haChoice, serotype, coreRelatedAntigen, genotype]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def PermitsRate (c : Context) (p : Nat) : Prop :=
  Eligible c ∧ Satisfies rates c.item p

def legacyRequest (i : Item) : SpecimenTests.Request :=
  { code := .d013, number := i.number, variant := i.variant }

theorem legacy_rate (i : Item) :
    SpecimenTests.assessOne (legacyRequest i) = some (.charged i.points 0) := by
  cases i <;> decide

theorem legacy_iff (c : Context) (p : Nat) :
    PermitsRate c p ↔ Eligible c ∧
      SpecimenTests.assessOne (legacyRequest c.item) = some (.charged p 0) := by
  simp [PermitsRate, rate_iff, legacy_rate, eq_comm]

theorem determines (c : Context) (h : Eligible c) : (∃ p, PermitsRate c p) ∧ (∀ p q, PermitsRate c p → PermitsRate c q → p = q) := by
  exact ⟨⟨c.item.points, h, (rate_iff _ _).mpr rfl⟩, fun p q hp hq =>
    ((rate_iff _ _).mp hp.2).trans ((rate_iff _ _).mp hq.2).symm⟩

structure DrawGroup where
  anchor : Performance Item
  tests : List Context

def DrawGroup.Assessed (g : DrawGroup) : Prop :=
  g.tests ≠ [] ∧ (g.tests.map Context.item).Nodup ∧
    ∀ c ∈ g.tests, Eligible c ∧ g.anchor.sameDraw c.performance = some true ∧
      3 ≤ c.item.number ∧ c.item.number ≤ 14

def DrawGroup.count (g : DrawGroup) : Nat := g.tests.length

def DrawGroup.standardSum (g : DrawGroup) : Nat :=
  (g.tests.map fun c => c.item.points).sum

def threeItemPoints : Nat := 290
def fourItemPoints : Nat := 360
def fiveOrMorePoints : Nat := 425

def bundleNote : Rule DrawGroup Nat :=
  ⟨"primary/D013/note/unnumbered/1", primary "注", fun g p =>
    g.count < 3 → p = g.standardSum⟩

def bundleThree : Rule DrawGroup Nat :=
  ⟨"primary/D013/note/i", primary "注イ", fun g p => g.count = 3 → p = threeItemPoints⟩

def bundleFour : Rule DrawGroup Nat :=
  ⟨"primary/D013/note/ro", primary "注ロ", fun g p => g.count = 4 → p = fourItemPoints⟩

def bundleFiveOrMore : Rule DrawGroup Nat :=
  ⟨"primary/D013/note/ha", primary "注ハ", fun g p => 5 ≤ g.count → p = fiveOrMorePoints⟩

def bundleRules := [bundleNote, bundleThree, bundleFour, bundleFiveOrMore]

theorem bundle_iff (g : DrawGroup) (p : Nat) :
    Satisfies bundleRules g p ↔
      p = SpecimenTests.groupedBase .hepatitis g.count g.standardSum := by
  simp only [bundleRules, satisfies_cons, satisfies_nil, and_true, bundleNote,
    bundleThree, bundleFour, bundleFiveOrMore, SpecimenTests.groupedBase, threeItemPoints, fourItemPoints, fiveOrMorePoints]
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem bundle_determines : DeterminesOn DrawGroup.Assessed bundleRules := by
  intro g _
  let p := SpecimenTests.groupedBase .hepatitis g.count g.standardSum
  exact ⟨⟨p, (bundle_iff _ _).mpr rfl⟩, fun x y hx hy =>
    ((bundle_iff _ _).mp hx).trans ((bundle_iff _ _).mp hy).symm⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 13, number := i.number, ordinaryCategory := .immunological }

def execution (kind : Nat) (c : Context) (p : Nat) (_ : PermitsRate c p) :
    Examinations.SpecimenItem :=
  { kind := kind, executionPoints := p }

def drawExecution (kind : Nat) (g : DrawGroup) (p : Nat) (_ : g.Assessed)
    (_ : Satisfies bundleRules g p) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := p }

private def sample (i : Item) : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, i, some 1, none, none, none⟩ }

example : PermitsRate { sample .hbsAntigenSimple with method := some .immunochromatography } 29 := by
  refine ⟨?_, (rate_iff _ _).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, antigenMethod, antibodyMethod,
    reactivationScreen, coreMethod, hbCoreChoice, haChoice, serotype, coreRelatedAntigen,
    genotype, SingleChoice, screeningItems, Context.item, sample]

example : ¬ Eligible (sample .hcvSerotype) := by
  intro h
  have hr := h serotype (by simp [eligibilityRules])
  have hm := (hr rfl).1
  contradiction

example : Satisfies bundleRules ⟨(sample .hbeAntigen).performance,
    [sample .hbeAntigen, sample .hbeAntibody, sample .hcvAntibody]⟩ 290 :=
  (bundle_iff _ _).mpr rfl

end Sanri.MedicalFee.D013
