import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D023Schedule

open Sanri.Logic

/-- 告示の単価行。複数の検査が同じ行を共有する場合は通知側で区別する。 -/
inductive Tier where
  | trachomatis
  | gonococcus
  | groupAStrep
  | hbvQuantity
  | gonococcusTrachomatis
  | respiratorySingle
  | legionella
  | ebvQuantity
  | hcvDetection
  | hpv
  | hpvSimpleGenotype
  | genitalCombination
  | pertussisGroup
  | mycobacteriaGroup
  | hcvQuantity
  | mac
  | viralOrMethicillinGroup
  | hivQuantity
  | covid
  | covidPanelOrMpox
  | cmvDetection
  | tbSingleResistance
  | tbDualResistance
  | pneumoniaResistancePanel
  | respiratoryPanelCovid
  | respiratoryPanelWithoutCovid
  | sepsisOrCsfPanel
  | hpvGenotype
  | hivGenotype
  deriving DecidableEq, Repr

def ledgerTiers : List Tier := [
  .trachomatis, .gonococcus, .groupAStrep, .hbvQuantity,
  .gonococcusTrachomatis, .respiratorySingle, .legionella, .ebvQuantity,
  .hcvDetection, .hpv, .hpvSimpleGenotype, .genitalCombination,
  .pertussisGroup, .mycobacteriaGroup, .hcvQuantity, .mac,
  .viralOrMethicillinGroup, .hivQuantity, .covid, .covidPanelOrMpox,
  .cmvDetection, .tbSingleResistance, .tbDualResistance, .pneumoniaResistancePanel,
  .respiratoryPanelCovid, .respiratoryPanelWithoutCovid, .sepsisOrCsfPanel, .hpvGenotype,
  .hivGenotype]

def Tier.number : Tier → Nat
  | .trachomatis => 1
  | .gonococcus => 2
  | .groupAStrep => 3
  | .hbvQuantity => 4
  | .gonococcusTrachomatis => 5
  | .respiratorySingle => 6
  | .legionella => 7
  | .ebvQuantity => 8
  | .hcvDetection => 9
  | .hpv => 10
  | .hpvSimpleGenotype => 11
  | .genitalCombination => 12
  | .pertussisGroup => 13
  | .mycobacteriaGroup => 14
  | .hcvQuantity => 15
  | .mac => 16
  | .viralOrMethicillinGroup => 17
  | .hivQuantity => 18
  | .covid => 19
  | .covidPanelOrMpox => 20
  | .cmvDetection => 21
  | .tbSingleResistance => 22
  | .tbDualResistance => 23
  | .pneumoniaResistancePanel => 24
  | .respiratoryPanelCovid => 25
  | .respiratoryPanelWithoutCovid => 25
  | .sepsisOrCsfPanel => 26
  | .hpvGenotype => 27
  | .hivGenotype => 28


def Tier.branch : Tier → Nat
  | .respiratoryPanelCovid => 1
  | .respiratoryPanelWithoutCovid => 2
  | _ => 0

def Tier.base : Tier → Nat
  | .trachomatis => 188
  | .gonococcus => 198
  | .groupAStrep => 204
  | .hbvQuantity => 256
  | .gonococcusTrachomatis => 262
  | .respiratorySingle => 291
  | .legionella => 296
  | .ebvQuantity => 310
  | .hcvDetection => 330
  | .hpv => 347
  | .hpvSimpleGenotype => 347
  | .genitalCombination => 350
  | .pertussisGroup => 360
  | .mycobacteriaGroup => 410
  | .hcvQuantity => 412
  | .mac => 421
  | .viralOrMethicillinGroup => 450
  | .hivQuantity => 520
  | .covid => 650
  | .covidPanelOrMpox => 700
  | .cmvDetection => 777
  | .tbSingleResistance => 850
  | .tbDualResistance => 963
  | .pneumoniaResistancePanel => 1273
  | .respiratoryPanelCovid => 1350
  | .respiratoryPanelWithoutCovid => 963
  | .sepsisOrCsfPanel => 1700
  | .hpvGenotype => 2000
  | .hivGenotype => 6000

private def primary (page location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF" ++ page ++ "頁 D023 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

def rate (i : Tier) : Rule Tier Nat :=
  let page := if i.number ≤ 10 then "189" else if i.number ≤ 26 then "190" else "191"
  let suffix := match i with
    | .respiratoryPanelCovid => "/a"
    | .respiratoryPanelWithoutCovid => "/i"
    | _ => ""
  ⟨"primary/D023/item/" ++ toString i.number,
    primary page (toString i.number ++ suffix), fun c p => c = i → p = i.base⟩

def panelRate : Rule Tier Nat :=
  ⟨"primary/D023/item/25", primary "190" "25", fun c p =>
    (c = .respiratoryPanelCovid → p = 1350) ∧
    (c = .respiratoryPanelWithoutCovid → p = 963)⟩

def rates := panelRate :: ledgerTiers.map rate

theorem rates_iff (i : Tier) (p : Nat) : Satisfies rates i p ↔ p = i.base := by
  constructor
  · intro h
    exact h (rate i) (by
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨i, by cases i <;> decide, rfl⟩) rfl
  · intro h
    subst p
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact ⟨fun e => by rw [e]; rfl, fun e => by rw [e]; rfl⟩
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
      intro e
      rw [e]

theorem base_determines : DeterminesOn (fun _ => True) rates := by
  intro i _
  exact ⟨⟨i.base, (rates_iff _ _).mpr rfl⟩, fun a b ha hb =>
    ((rates_iff _ _).mp ha).trans ((rates_iff _ _).mp hb).symm⟩

theorem legacy_catalog (i : Tier) :
    (SpecimenTests.lookup .d023 i.number i.branch).bind (·.points) = some i.base := by
  cases i <;> rfl

structure Evidence where
  tier : Tier
  priorSpecifiedCervicalProcedure : Option Bool := none
  ascUs : Option Bool := none
  facilityStandardMet : Option Bool := none
  facilityNotified : Option Bool := none
  designatedPatient : Option Bool := none
  csfPanel : Option Bool := none
  ultracentrifugalConcentration : Option Bool := none

private def HpvCriteria (c : Evidence) : Prop :=
  c.facilityStandardMet = some true ∧ c.facilityNotified = some true ∧
    (c.ascUs = some true ∨ c.priorSpecifiedCervicalProcedure = some true)

def hpvEligibility : Rule Evidence Unit :=
  ⟨"primary/D023/item/10/note", primary "190" "10注", fun c _ =>
    c.tier = .hpv → HpvCriteria c⟩

def hpvSimpleEligibility : Rule Evidence Unit :=
  ⟨"primary/D023/item/11/note", primary "190" "11注", fun c _ =>
    c.tier = .hpvSimpleGenotype → HpvCriteria c⟩

def concentrationPoints : Nat := 130

def concentration : Rule Evidence Nat :=
  ⟨"primary/D023/item/18/note", primary "190" "18注", fun c p =>
    (c.tier = .hivQuantity ∧ c.ultracentrifugalConcentration = some true ∧ p = concentrationPoints) ∨
    ((c.tier ≠ .hivQuantity ∨ c.ultracentrifugalConcentration = some false) ∧ p = 0)⟩

private def PanelCriteria (c : Evidence) : Prop :=
  c.facilityStandardMet = some true ∧ c.facilityNotified = some true ∧ c.designatedPatient = some true

def pneumoniaPanelFacility : Rule Evidence Unit :=
  ⟨"primary/D023/item/24/note", primary "190" "24注", fun c _ =>
    c.tier = .pneumoniaResistancePanel → PanelCriteria c⟩

def respiratoryPanelFacility : Rule Evidence Unit :=
  ⟨"primary/D023/item/25/note", primary "190" "25注", fun c _ =>
    c.tier ∈ [.respiratoryPanelCovid, .respiratoryPanelWithoutCovid] → PanelCriteria c⟩

def sepsisPanelFacility : Rule Evidence Unit :=
  ⟨"primary/D023/item/26/note/1", primary "190–191" "26注1", fun c _ =>
    c.tier = .sepsisOrCsfPanel → c.csfPanel = some true ∨
      (c.csfPanel = some false ∧ c.facilityStandardMet = some true)⟩

def csfPanelFacility : Rule Evidence Unit :=
  ⟨"primary/D023/item/26/note/2", primary "191" "26注2", fun c _ =>
    c.tier = .sepsisOrCsfPanel → c.csfPanel = some false ∨
      (c.csfPanel = some true ∧ c.facilityStandardMet = some true ∧ c.facilityNotified = some true)⟩

end Sanri.MedicalFee.D023Schedule
