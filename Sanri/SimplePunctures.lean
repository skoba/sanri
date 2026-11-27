import Sanri.D400

namespace Sanri.MedicalFee.SimplePunctures

open Sanri.Logic Sanri.History

inductive Item where
  | ventricular | suboccipital | lumbar | thoracic | cervical
  | sternalMarrow | otherMarrow | marrowBiopsy | joint | maxillary | peritonsillar
  | renalCyst | douglas | lymphNode | breastNeedle | breastOther | thyroid
  deriving DecidableEq, Repr

def Item.legacy : Item → SpecimenCollection.Item
  | .ventricular => .ventricularPuncture
  | .suboccipital => .suboccipitalPuncture
  | .lumbar => .lumbarPuncture
  | .thoracic => .thoracicPuncture
  | .cervical => .cervicalPuncture
  | .sternalMarrow => .sternalMarrowPuncture
  | .otherMarrow => .otherMarrowPuncture
  | .marrowBiopsy => .marrowBiopsy
  | .joint => .jointPuncture
  | .maxillary => .maxillarySinusPuncture
  | .peritonsillar => .peritonsillarTrialPuncture
  | .renalCyst => .renalCystHydronephrosisPuncture
  | .douglas => .douglasPuncture
  | .lymphNode => .lymphNodeNeedleBiopsy
  | .breastNeedle => .breastBiopsyNeedle
  | .breastOther => .breastOther
  | .thyroid => .thyroidNeedleBiopsy

/-- 一つの算定候補。部位IDは患者・医療機関内で照合済みとする。 -/
structure Context where
  performance : Performance Item
  ageYears : Nat
  siteId : Nat
  sides : SpecimenCollection.Sides
  duringSurgery : Bool
  treatmentSelected : Bool
  /-- 当該単位の代表実施として選択済み。同一部位の複数穿刺を重複算定しない。 -/
  representative : Bool
  /-- 骨髄生検針の使用を確認した結果。 -/
  biopsyNeedle : Option Bool

def Context.separate (c : Context) : Prop :=
  c.duringSurgery = false ∧ c.treatmentSelected = false ∧ c.representative = true

structure Result where
  base : Nat
  infant : Nat
  deriving DecidableEq, Repr

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF210頁 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def baseRule (code path : String) (applies : Item → Prop) (price : Nat)
    (unilateral : Bool := false) : Rule Context Result :=
  ⟨"primary/" ++ code ++ "/" ++ path, primary (code ++ " " ++ path), fun c r =>
    c.separate → applies c.performance.item →
      r.base = (if unilateral && decide (c.sides = .both) then 2 else 1) * price⟩

private def infantRule (code : String) (applies : Item → Prop)
    (ageLimit : Nat) (unilateral : Bool := false) : Rule Context Result :=
  ⟨"primary/" ++ code ++ "/note/unnumbered/1", primary (code ++ " 注"), fun c r =>
    c.separate → applies c.performance.item →
      r.infant = (if unilateral && decide (c.sides = .both) then 2 else 1) *
        (if c.ageYears < ageLimit then 100 else 0)⟩

-- 台帳では各告示項に固有のIDを保持する。
def ventricular := baseRule "D401" "heading" (· = .ventricular) 600
def suboccipital := baseRule "D402" "heading" (· = .suboccipital) 300
private def Spine (i : Item) : Prop := i = .lumbar ∨ i = .thoracic ∨ i = .cervical
def spine := baseRule "D403" "heading" Spine 312
def sternal := baseRule "D404" "item/1" (· = .sternalMarrow) 260
def otherMarrow := baseRule "D404" "item/2" (· = .otherMarrow) 300
def marrowBiopsy := baseRule "D404-2" "heading" (· = .marrowBiopsy) 730
def joint := baseRule "D405" "heading" (· = .joint) 100 true
def maxillary := baseRule "D406" "heading" (· = .maxillary) 60 true
def peritonsillar := baseRule "D406-2" "heading" (· = .peritonsillar) 180 true
def renalCyst := baseRule "D407" "heading" (· = .renalCyst) 240
def douglas := baseRule "D408" "heading" (· = .douglas) 240
def lymphNode := baseRule "D409" "heading" (· = .lymphNode) 240
def breastNeedle := baseRule "D410" "item/1" (· = .breastNeedle) 690 true
def breastOther := baseRule "D410" "item/2" (· = .breastOther) 200 true
def thyroid := baseRule "D411" "heading" (· = .thyroid) 150

def ventricularInfant := infantRule "D401" (· = .ventricular) 6
def suboccipitalInfant := infantRule "D402" (· = .suboccipital) 6
def spineInfant := infantRule "D403" Spine 6
def marrowInfant := infantRule "D404" (fun i => i = .sternalMarrow ∨ i = .otherMarrow) 6
def marrowBiopsyInfant := infantRule "D404-2" (· = .marrowBiopsy) 6
def jointInfant := infantRule "D405" (· = .joint) 3 true
def renalCystInfant := infantRule "D407" (· = .renalCyst) 6

def biopsyNeedleRule : Rule Context Result :=
  ⟨"notice/D404-2/paragraph/unnumbered", notice "PDF446頁 D404-2",
    fun c _ => c.performance.item = .marrowBiopsy → c.biopsyNeedle = some true⟩

def sameSiteRule : Rule Context Result :=
  ⟨"notice/ch2-part3-section4/general/1", notice "PDF445頁 第4節通則1",
    fun c r => c.representative = false → r = ⟨0, 0⟩⟩

def surgeryRule : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", primary "第4節通則1",
    fun c r => c.duringSurgery = true → r = ⟨0, 0⟩⟩

def treatmentRule : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", primary "第4節通則2",
    fun c r => c.treatmentSelected = true → r = ⟨0, 0⟩⟩

private def noInfantRule : Rule Context Result :=
  ⟨"unclassified/simple-punctures-infant-component",
    ⟨.manualInterpretation, "採取料内訳", "2026-10-22", "固定乳幼児加算の適用区分", .unchecked, none⟩,
    fun c r => c.performance.item ∈ [.maxillary, .peritonsillar, .douglas, .lymphNode,
      .breastNeedle, .breastOther, .thyroid] → r.infant = 0⟩

def rules : List (Rule Context Result) :=
  [ventricular, suboccipital, spine, sternal, otherMarrow, marrowBiopsy, joint,
    maxillary, peritonsillar, renalCyst, douglas, lymphNode, breastNeedle, breastOther,
    thyroid, ventricularInfant, suboccipitalInfant, spineInfant, marrowInfant, marrowBiopsyInfant,
    jointInfant, renalCystInfant, biopsyNeedleRule, sameSiteRule, surgeryRule, treatmentRule, noInfantRule]

def assess (c : Context) : Option Result := do
  if c.performance.item = .marrowBiopsy && c.biopsyNeedle != some true then none
  else if !c.representative then some ⟨0, 0⟩
  else
    let a ← SpecimenCollection.assess {
      item := c.performance.item.legacy
      ageYears := c.ageYears
      sides := c.sides
      duringSurgery := c.duringSurgery
      commonProcedureClaimedSameDay := c.treatmentSelected }
    return ⟨a.base, a.infant⟩

set_option maxHeartbeats 2000000 in
theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ assess c = some r := by
  simp only [rules, satisfies_cons, satisfies_nil, and_true, ventricular, suboccipital, spine,
    sternal, otherMarrow, marrowBiopsy, joint, maxillary, peritonsillar, renalCyst, douglas,
    lymphNode, breastNeedle, breastOther, thyroid, ventricularInfant, suboccipitalInfant, spineInfant,
    marrowInfant, marrowBiopsyInfant, jointInfant, renalCystInfant, baseRule, infantRule,
    biopsyNeedleRule, sameSiteRule, surgeryRule, treatmentRule, noInfantRule]
  cases hm : c.performance.item <;> cases hs : c.duringSurgery <;>
    cases ht : c.treatmentSelected <;> cases hr : c.representative <;>
    simp [Context.separate, hm, hs, ht, hr, Spine, assess, Item.legacy,
      SpecimenCollection.assess, SpecimenCollection.notSeparateReason, SpecimenCollection.isD400,
      SpecimenCollection.isDaily, SpecimenCollection.isSeries, SpecimenCollection.isUnilateral,
      SpecimenCollection.eligible, SpecimenCollection.basePoints, SpecimenCollection.infantPoints,
      SpecimenCollection.isD417] <;>
    (cases r; simp_all)
  all_goals
    try exact and_congr eq_comm eq_comm
  all_goals
    have rates : (if c.ageYears < 6 then 100 else 0) =
        (if 6 ≤ c.ageYears then 0 else 100) := by
      split <;> split <;> omega
    try rw [rates]
    try exact and_congr eq_comm eq_comm
  all_goals
    by_cases needle : c.biopsyNeedle = some true <;> simp_all <;>
      exact and_congr eq_comm eq_comm

set_option maxHeartbeats 1700000 in
theorem determines (c : Context)
    (needle : c.performance.item = .marrowBiopsy → c.biopsyNeedle = some true) : DeterminesAt rules c := by
  have calculated : ∃ r, assess c = some r := by
    cases hm : c.performance.item <;> cases hs : c.duringSurgery <;>
      cases ht : c.treatmentSelected <;> cases hr : c.representative <;>
      simp [hm, hs, ht, hr, assess, Item.legacy, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.isD400,
        SpecimenCollection.isDaily, SpecimenCollection.isSeries, SpecimenCollection.eligible] at *
    all_goals exact needle
  obtain ⟨r, hr⟩ := calculated
  refine ⟨⟨r, (satisfies_iff c r).2 hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a).1 ha).symm.trans ((satisfies_iff c b).1 hb))

private def sample : Context :=
  ⟨⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .joint, none, none, none, none⟩,
    2, 1, .both, false, false, true, none⟩

example : assess sample = some ⟨200, 200⟩ := by decide
example : assess { sample with ageYears := 3 } = some ⟨200, 0⟩ := by decide
example : assess { sample with representative := false } = some ⟨0, 0⟩ := by decide

end Sanri.MedicalFee.SimplePunctures
