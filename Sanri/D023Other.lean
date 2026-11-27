import Sanri.D018

namespace Sanri.MedicalFee.D023Other

open Sanri.Logic Sanri.History

inductive Item where
  | pbp2 | breath | verotoxin | rapidPbp2 | difficile
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.pbp2, .breath, .verotoxin, .rapidPbp2, .difficile]
def Item.number : Item → Nat
  | .pbp2 => 1
  | .breath => 2
  | .verotoxin => 3
  | .rapidPbp2 => 4
  | .difficile => 5
def Item.points : Item → Nat
  | .pbp2 => 55
  | .breath => 70
  | .verotoxin => 184
  | .rapidPbp2 => 291
  | .difficile => 450

inductive Pbp2Choice where
  | noCombinedTest | thisTest | d023MethicillinGene
  deriving DecidableEq

structure CultureEvidence where
  culture : D018.Context
  ecoliIdentified : Bool
  suspectedPathogenicEcoli : Bool

structure Context where
  performance : Performance Item
  staphDetectedByBloodCulture : Option Bool := none
  immunodeficientWithStrongMrsaSuspicion : Option Bool := none
  pbp2Choice : Option Pbp2Choice := none
  positiveBloodCultureBroth : Option Bool := none
  immunochromatography : Option Bool := none
  d023MethicillinGeneCanBePerformed : Option Bool := none
  separatelyBilledPbp2 : Option Bool := none
  pyloriNotificationSatisfied : Option Bool := none
  cultureEvidence : Option CultureEvidence := none
  directStoolElisa : Option Bool := none
  stronglySuspectedEnterohemorrhagicEcoli : Option Bool := none
  facilityStandardMet : Option Bool := none

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF191頁 D023-2 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (suffix page : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF" ++ page ++ "頁 D023-2 " ++ suffix, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def condition (suffix page : String) (p : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D023-2/paragraph/" ++ suffix, notice suffix page, fun c _ => p c⟩

def rate (i : Item) : Rule Context Nat :=
  ⟨"primary/D023-2/item/" ++ toString i.number, primary (toString i.number),
    fun c p => c.performance.item = i → p = i.points⟩

def facility : Rule Context Unit :=
  ⟨"primary/D023-2/item/5/note", primary "5 注", fun c _ =>
    c.performance.item = .difficile → c.facilityStandardMet = some true⟩

def Pbp2Indication (c : Context) : Prop :=
  c.staphDetectedByBloodCulture = some true ∨
    c.immunodeficientWithStrongMrsaSuspicion = some true

def pbp2Indication : Rule Context Unit :=
  condition "1/a" "401" fun c => c.performance.item = .pbp2 → Pbp2Indication c

def pbp2Main : Rule Context Unit :=
  condition "1/i" "401" fun c => c.performance.item = .pbp2 →
    c.pbp2Choice ∈ [some .noCombinedTest, some .thisTest]

def pbp2 : Rule Context Unit :=
  condition "1" "401" fun c => pbp2Indication.holds c () ∧ pbp2Main.holds c ()

def breath : Rule Context Unit :=
  condition "2" "401" fun c => c.performance.item = .breath →
    c.pyloriNotificationSatisfied = some true

def CultureRoute (c : Context) : Prop :=
  ∃ e, c.cultureEvidence = some e ∧ e.ecoliIdentified = true ∧
    e.suspectedPathogenicEcoli = true ∧
    e.culture.method = .plannedIdentification ∧
    D018.identification.holds e.culture () ∧ D018.purpose.holds e.culture () ∧
    D018.materialClassification.holds e.culture () ∧
    e.culture.performance.site.patient = c.performance.site.patient

def DirectRoute (c : Context) : Prop :=
  c.directStoolElisa = some true ∧ c.stronglySuspectedEnterohemorrhagicEcoli = some true

def verotoxinCulture : Rule Context Unit :=
  condition "3/a" "401" fun c => c.performance.item = .verotoxin →
    c.directStoolElisa = some false → CultureRoute c

def verotoxinDirect : Rule Context Unit :=
  condition "3/i" "401" fun c => c.performance.item = .verotoxin →
    c.directStoolElisa = some true → CultureRoute c ∨ DirectRoute c

def verotoxin : Rule Context Unit :=
  condition "3" "401" fun c => c.performance.item = .verotoxin →
    c.directStoolElisa.isSome = true ∧ verotoxinCulture.holds c () ∧ verotoxinDirect.holds c ()

def rapidPbp2Method : Rule Context Unit :=
  condition "4/a" "401" fun c => c.performance.item = .rapidPbp2 →
    Pbp2Indication c ∧ c.positiveBloodCultureBroth = some true ∧
    c.immunochromatography = some true

def rapidPbp2Exclusion : Rule Context Unit :=
  condition "4/i" "401" fun c => c.performance.item = .rapidPbp2 →
    c.d023MethicillinGeneCanBePerformed = some false ∧ c.separatelyBilledPbp2 = some false

def rapidPbp2 : Rule Context Unit :=
  condition "4" "401" fun c => rapidPbp2Method.holds c () ∧ rapidPbp2Exclusion.holds c ()

def difficileInpatient : Rule Context Unit :=
  condition "5/a" "401" fun c => c.performance.item ≠ .difficile

def difficile : Rule Context Unit :=
  condition "5" "401–402" fun c => difficileInpatient.holds c ()

def eligibilityRules := [facility, pbp2, breath, verotoxin, rapidPbp2, difficile]
def InScope (c : Context) := Satisfies eligibilityRules c ()
def rates := ledgerItems.map rate

theorem rates_iff (c : Context) (p : Nat) :
    Satisfies rates c p ↔ p = c.performance.item.points := by
  cases h : c.performance.item <;>
    simp [rates, ledgerItems, satisfies_cons, satisfies_nil, rate, h, Item.points]

theorem determines : DeterminesOn InScope rates := by
  intro c _
  exact ⟨⟨_, (rates_iff _ _).mpr rfl⟩, fun a b ha hb =>
    ((rates_iff _ _).mp ha).trans ((rates_iff _ _).mp hb).symm⟩

def legacyRequest (c : Context) : SpecimenTests.Request :=
  { code := .d023_2, number := c.performance.item.number }

theorem legacy_eval (c : Context) (h : InScope c) :
    SpecimenTests.assessOne (legacyRequest c) = some (.charged c.performance.item.points 0) := by
  have hx := h difficile (by simp [eligibilityRules])
  change c.performance.item ≠ .difficile at hx
  unfold legacyRequest
  cases hi : c.performance.item <;> try rfl
  exact (hx hi).elim

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 23, suffix := 2, number := i.number, ordinaryCategory := .microbiological }

theorem legacy_iff (c : Context) (p : Nat) (h : InScope c) :
    Satisfies rates c p ↔ SpecimenTests.assessOne (legacyRequest c) = some (.charged p 0) := by
  rw [rates_iff, legacy_eval c h]
  simp [@eq_comm Nat c.performance.item.points p]

/-- 対になる血清型検査と、同一患者のベロトキシン確認を結び付ける。
菌培養の費用はD012(30)の関係で評価する。 -/
def SerotypePair (c : Context) (p : Nat) (serotype : D012.Context)
    (confirmedVerotoxin : Bool) (billCulture : Bool) : Prop :=
  c.performance.item = .verotoxin ∧ InScope c ∧ Satisfies rates c p ∧
  c.performance.site.patient = serotype.performance.site.patient ∧
  serotype.performance.item = .local .ecoliSerotype ∧ confirmedVerotoxin = true ∧
  serotype.confirmed .verotoxinConfirmedByD023_2 = some confirmedVerotoxin ∧
  D012.ecoliSerotypeRule.holds serotype () ∧ D012.ecoliCultureIncluded.holds serotype billCulture

private def sample : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩,
      .verotoxin, none, some 1, none, none⟩
    directStoolElisa := some true, stronglySuspectedEnterohemorrhagicEcoli := some true }

example : InScope sample ∧ Satisfies rates sample 184 := by
  constructor
  · simp [InScope, eligibilityRules, facility, pbp2, pbp2Indication, pbp2Main, breath,
      verotoxin, verotoxinCulture, verotoxinDirect, DirectRoute, rapidPbp2, rapidPbp2Method,
      rapidPbp2Exclusion, difficile, difficileInpatient, condition, sample, satisfies_cons, satisfies_nil]
  · exact (rates_iff _ _).mpr rfl

example : ¬ InScope { sample with performance := { sample.performance with item := .difficile } } := by
  intro h
  have hd := h difficile (by simp [eligibilityRules])
  exact hd rfl

end Sanri.MedicalFee.D023Other
