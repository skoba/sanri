import Sanri.D012

namespace Sanri.MedicalFee.D018

open Sanri.Logic Sanri.History

inductive Item where
  | respiratory | gastrointestinal | bloodOrPuncture | genitourinary | other | simple
  deriving DecidableEq, Repr

def ledgerItems : List Item :=
  [.respiratory, .gastrointestinal, .bloodOrPuncture, .genitourinary, .other, .simple]

def Item.number : Item → Nat
  | .respiratory => 1
  | .gastrointestinal => 2
  | .bloodOrPuncture => 3
  | .genitourinary => 4
  | .other => 5
  | .simple => 6

def Item.points : Item → Nat
  | .respiratory | .other => 180
  | .gastrointestinal => 200
  | .bloodOrPuncture => 240
  | .genitourinary => 190
  | .simple => 60

inductive Material where
  | respiratory | gastrointestinal | blood | pleural | ascitic | cerebrospinal
  | synovial | genitourinary | other
  deriving DecidableEq

def Material.ordinaryItem : Material → Item
  | .respiratory => .respiratory
  | .gastrointestinal => .gastrointestinal
  | .blood | .pleural | .ascitic | .cerebrospinal | .synovial => .bloodOrPuncture
  | .genitourinary => .genitourinary
  | .other => .other

inductive Method where
  | plannedIdentification | simpleCulture | urineBacteriaTestStrip
  deriving DecidableEq

structure SearchSelection where
  /-- 確認済みの同一起因菌検索で算定する検体。主部位の選択を含む。 -/
  selected : List (Performance Item × Material)
  distinctBloodSites : Option Bool := none

structure Context where
  performance : Performance Item
  material : Material
  method : Method
  targetExcludesMycobacteria : Option Bool := none
  ordinaryOnSameSpecimen : Option Bool := none
  /-- 検体単位で照合した一般・嫌気性・真菌培養の実施。 -/
  generalCulture : Bool
  anaerobicCulture : Bool
  fungalCulture : Bool
  searchSelection : Option SearchSelection := none

def Context.item (c : Context) := c.performance.item

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF189頁 D018 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

structure Result where
  base : Nat
  anaerobic : Nat
  fungal : Nat
  massSpectrometry : Nat

def Result.total (r : Result) := r.base + r.anaerobic + r.fungal + r.massSpectrometry

def rate (i : Item) : Rule Context Result :=
  ⟨"primary/D018/item/" ++ toString i.number, primary (toString i.number),
    fun c r => c.item = i → r.base = i.points⟩

def anaerobicPoints : Nat := 137
def fungalPoints : Nat := 122

def anaerobic : Rule Context Result :=
  ⟨"primary/D018/note/1", primary "注1",
    fun c r => r.anaerobic = if c.generalCulture && c.anaerobicCulture then anaerobicPoints else 0⟩

def fungal : Rule Context Result :=
  ⟨"primary/D018/note/2", primary "注2",
    fun c r => r.fungal = if c.generalCulture && c.fungalCulture then fungalPoints else 0⟩

def outpatientNote : Rule Context Result :=
  ⟨"primary/D018/note/3", primary "注3", fun _ r => r.massSpectrometry = 0⟩

private def condition (suffix page : String) (p : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D018/paragraph/" ++ suffix, notice ("PDF" ++ page ++ "頁 D018 " ++ suffix),
    fun c _ => p c⟩

def identification : Rule Context Unit :=
  condition "1/a" "386" fun c => c.targetExcludesMycobacteria = some true

def purpose : Rule Context Unit :=
  condition "1/i" "386–387" fun c =>
    (c.method = .plannedIdentification ∧ c.item ≠ .simple) ∨
    (c.method = .simpleCulture ∧ c.item = .simple)

def perSpecimen : Rule Context Unit :=
  condition "1/u" "387" fun c => c.performance.specimen.isSome = true ∧
    (c.item = .simple → c.ordinaryOnSameSpecimen = some false)

def selectedSite : Rule Context Unit :=
  condition "1/e" "387" fun c => ∃ s, c.searchSelection = some s ∧
    (c.performance, c.material) ∈ s.selected ∧
    (s.selected = [(c.performance, c.material)] ∨
      ∃ a b, s.selected = [(a, .blood), (b, .blood)] ∧
        a.id ≠ b.id ∧ a.sameSpecimen b = some false ∧
        a.site.patient = b.site.patient ∧ a.site.institution = b.site.institution ∧
        a.item = .bloodOrPuncture ∧ b.item = .bloodOrPuncture ∧
        s.distinctBloodSites = some true)

def quantitativeIncluded : Rule Context (Bool → Prop) :=
  ⟨"notice/D018/paragraph/1/o", notice "PDF387頁 D018(1)オ",
    fun _ included => included true⟩

def cultureClassification : Rule Context Unit :=
  condition "1" "386–387" fun c =>
    identification.holds c () ∧ purpose.holds c () ∧
      perSpecimen.holds c () ∧ selectedSite.holds c ()

def materialClassification : Rule Context Unit :=
  condition "2" "387" fun c => c.item ≠ .simple → c.item = c.material.ordinaryItem

def simpleMethod : Rule Context Unit :=
  condition "3/a" "387" fun c => c.item = .simple → c.method = .simpleCulture

def stripsIncluded : Rule Context Unit :=
  condition "3/i" "387" fun c => c.method ≠ .urineBacteriaTestStrip

def simpleClassification : Rule Context Unit :=
  condition "3" "387" fun c => simpleMethod.holds c () ∧ stripsIncluded.holds c ()

def noGeneralAdditions : Rule Context Result :=
  ⟨"notice/D018/paragraph/4", notice "PDF387頁 D018(4)",
    fun c r => c.generalCulture = false → r.anaerobic = 0 ∧ r.fungal = 0⟩

def inpatientOnly : Rule Context Result :=
  ⟨"notice/D018/paragraph/5", notice "PDF387頁 D018(5)", fun _ r => r.massSpectrometry = 0⟩

def eligibilityRules := [cultureClassification, materialClassification, simpleClassification]
def InScope (c : Context) := Satisfies eligibilityRules c ()
def rates : List (Rule Context Result) := ledgerItems.map rate
def resultRules := anaerobic :: fungal :: outpatientNote :: noGeneralAdditions :: inpatientOnly :: rates

def legacyRequest (c : Context) : SpecimenTests.Request :=
  { code := .d018, number := c.item.number, conditions := {
      generalCulture := c.generalCulture, anaerobicCulture := c.anaerobicCulture
      fungalCulture := c.fungalCulture } }

def assessedResult (c : Context) : Result :=
  ⟨c.item.points, (if c.generalCulture && c.anaerobicCulture then anaerobicPoints else 0),
    (if c.generalCulture && c.fungalCulture then fungalPoints else 0), 0⟩

theorem result_iff (c : Context) (r : Result) :
    Satisfies resultRules c r ↔ r = assessedResult c := by
  cases r
  cases h : c.item <;>
    simp [resultRules, rates, ledgerItems, satisfies_cons, satisfies_nil, rate, h, Item.points,
      anaerobic, fungal, outpatientNote, noGeneralAdditions, inpatientOnly, assessedResult] <;>
    cases c.generalCulture <;> simp_all <;> simp [and_assoc, and_left_comm, and_comm]

theorem determines : DeterminesOn InScope resultRules := by
  intro c _
  exact ⟨⟨assessedResult c, (result_iff _ _).mpr rfl⟩, fun a b ha hb =>
    ((result_iff _ _).mp ha).trans ((result_iff _ _).mp hb).symm⟩

def Result.toLegacy (r : Result) : SpecimenTests.ItemResult :=
  .charged r.base (r.anaerobic + r.fungal + r.massSpectrometry)

theorem legacy_eval (c : Context) :
    SpecimenTests.assessOne (legacyRequest c) = some (assessedResult c).toLegacy := by
  unfold legacyRequest assessedResult
  cases c.generalCulture <;> cases c.anaerobicCulture <;> cases c.fungalCulture <;>
    cases c.item <;> rfl

theorem legacy_of_satisfies (c : Context) (r : Result) (h : Satisfies resultRules c r) :
    SpecimenTests.assessOne (legacyRequest c) = some r.toLegacy := by
  rw [(result_iff _ _).mp h, legacy_eval]

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 18, number := i.number, ordinaryCategory := .microbiological }

def execution (kind : Nat) (r : Result) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := r.total }

def StrepCulturePair (c : Context) (r : Result) (pair : D012.StrepCulture) : Prop :=
  InScope c ∧ Satisfies resultRules c r ∧ c.item ≠ .simple ∧
  pair.rapid.item = .local .rapidGroupAStrep ∧
  pair.culture = { c.performance with item := .bacterialCultureD018 } ∧
  D012.strepCultureRule.holds pair true

def GonococcusCulturePair (c : Context) (r : Result) (antigen : D012.Context)
    (g : D012.Combined) : Prop :=
  InScope c ∧ Satisfies resultRules c r ∧ c.item ≠ .simple ∧
  antigen.performance.item = .local .gonococcusAntigen ∧
  antigen.combined = some g ∧ g.Valid antigen.performance ∧
  ({ c.performance with item := .bacterialCultureD018 } : Performance D012.RelatedTest) ∈ g.members ∧
  D012.gonococcusCultureRule.holds antigen ()

def GastrointestinalCulturePair (c : Context) (r : Result) (antigen : D012.Context)
    (g : D012.Combined) (billedCulture : Bool) : Prop :=
  InScope c ∧ Satisfies resultRules c r ∧ c.item = .gastrointestinal ∧
  antigen.performance.item ∈ [.local .ecoliO157Antibody, .local .ecoliO157Antigen] ∧
  antigen.combined = some g ∧ g.Valid antigen.performance ∧
  let culture : Performance D012.RelatedTest := { c.performance with item := .gastrointestinalCultureD018 }
  g.Valid culture ∧
  ∃ ids, g.selected = some ids ∧
    (billedCulture = true ↔ culture.id ∈ ids) ∧
    (D012.o157Rule.holds antigen () ∨
      (billedCulture = true ∧
        D012.o157Rule.holds { antigen with performance := culture } ()))

theorem legacy_iff (c : Context) (r : SpecimenTests.ItemResult) :
    (∃ result, Satisfies resultRules c result ∧ result.toLegacy = r) ↔
      SpecimenTests.assessOne (legacyRequest c) = some r := by
  rw [legacy_eval]
  simp [result_iff]

private def samplePerformance : Performance Item :=
  ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .bloodOrPuncture, none, some 1, none, none⟩

private def sample : Context :=
  { performance := samplePerformance, material := .blood, method := .plannedIdentification
    targetExcludesMycobacteria := some true, generalCulture := true, anaerobicCulture := true
    fungalCulture := false, searchSelection := some ⟨[(samplePerformance, .blood)], none⟩ }

example : InScope sample := by
  simp [InScope, eligibilityRules, satisfies_cons, satisfies_nil, cultureClassification,
    identification, purpose, perSpecimen, selectedSite, materialClassification, simpleClassification,
    simpleMethod, stripsIncluded, condition, sample, samplePerformance, Context.item, Material.ordinaryItem]

example : Satisfies resultRules sample ⟨240, 137, 0, 0⟩ :=
  (result_iff _ _).mpr rfl

example : ¬ Satisfies resultRules { sample with generalCulture := false } ⟨240, 137, 0, 0⟩ := by
  rw [result_iff]
  intro h
  have he := congrArg Result.anaerobic h
  contradiction

end Sanri.MedicalFee.D018
