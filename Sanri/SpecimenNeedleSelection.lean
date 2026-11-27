import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.SpecimenNeedleSelection

open Sanri.History Sanri.Logic

inductive Method where
  | combinedSentinel | singleSentinel | fusionProstate | otherProstate
  deriving DecidableEq

def Method.sentinel (m : Method) : Prop := m = .combinedSentinel ∨ m = .singleSentinel
instance (m : Method) : Decidable m.sentinel := by unfold Method.sentinel; infer_instance

def Method.item : Method → SpecimenCollection.Item
  | .combinedSentinel => .sentinelCombined
  | .singleSentinel => .sentinelSingle
  | .fusionProstate => .prostateMriUltrasoundFusion
  | .otherProstate => .prostateOther

structure Context where
  performance : Performance Method
  facilityComplies : Bool
  validFiling : Bool
  breastCancer : Bool
  surgeryPlannedWithoutAxillaryMetastasis : Bool
  breastCancerSurgerySameDay : Bool
  isotopeUsed : Bool
  dyeUsed : Bool
  sides : SpecimenCollection.Sides
  ministerDesignatedProstatePatient : Bool
  fusionGuidanceUsed : Bool
  mriOnlyLesionIncluded : Bool
  duringOtherSurgery : Bool
  commonProcedureSameDay : Bool

def Separate (c : Context) : Prop :=
  c.duringOtherSurgery = false ∧ c.commonProcedureSameDay = false ∧
    (c.performance.item.sentinel → c.breastCancerSurgerySameDay = false)

structure RelatedFees where
  dye : Nat
  isotopeDrug : Option Nat
  isotopeDetection : Option Nat
  pathology : Option Nat
  fusionMaterials : Nat
  /-- K476注の適用を外部の手術側に渡す。 -/
  routeToBreastSurgery : Bool

private def primary (locator : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度", locator,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (locator : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", locator,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def combined : Rule Context Nat :=
  ⟨"primary/D409-2/item/1", primary "PDF210頁 D409-2の1",
    fun c p => Separate c → c.performance.item = .combinedSentinel →
      p = if c.sides = .both then 10000 else 5000⟩

def single : Rule Context Nat :=
  ⟨"primary/D409-2/item/2", primary "PDF210頁 D409-2の2",
    fun c p => Separate c → c.performance.item = .singleSentinel →
      p = if c.sides = .both then 6000 else 3000⟩

def sentinelFacility : Rule Context Nat :=
  ⟨"primary/D409-2/note/unnumbered/1", primary "PDF210頁 D409-2注",
    fun c _ => c.performance.item.sentinel →
      c.facilityComplies = true ∧ c.validFiling = true ∧ c.breastCancer = true ∧
      (c.performance.item = .combinedSentinel → c.isotopeUsed = true ∧ c.dyeUsed = true) ∧
      (c.performance.item = .singleSentinel → c.isotopeUsed ≠ c.dyeUsed)⟩

def dyeIncluded : Rule Context RelatedFees :=
  ⟨"primary/D409-2/note/unnumbered/1", primary "PDF210頁 D409-2注ただし書",
    fun c r => c.performance.item.sentinel → r.dye = 0⟩

def plannedSurgery : Rule Context Nat :=
  ⟨"notice/D409-2/paragraph/1", notice "PDF446頁 D409-2(1)",
    fun c _ => c.performance.item.sentinel → c.surgeryPlannedWithoutAxillaryMetastasis = true⟩

def surgerySameDay : Rule Context Nat :=
  ⟨"notice/D409-2/paragraph/2", notice "PDF446頁 D409-2(2)",
    fun c p => c.performance.item.sentinel → c.breastCancerSurgerySameDay = true → p = 0⟩

def routeToBreastSurgery : Rule Context RelatedFees :=
  ⟨"notice/D409-2/paragraph/2", notice "PDF446頁 D409-2(2) K476",
    fun c r => c.performance.item.sentinel →
      r.routeToBreastSurgery = c.breastCancerSurgerySameDay⟩

def isotopeDrug : Rule Context RelatedFees :=
  ⟨"notice/D409-2/paragraph/3", notice "PDF446頁 D409-2(3) D500",
    fun c r => Separate c → c.performance.item.sentinel → c.isotopeUsed = true →
      r.isotopeDrug.isSome = true⟩

def isotopeDetection : Rule Context RelatedFees :=
  ⟨"notice/D409-2/paragraph/4", notice "PDF446頁 D409-2(4) E100の1",
    fun c r => Separate c → c.performance.item.sentinel → c.isotopeUsed = true →
      r.isotopeDetection.isSome = true⟩

def pathology : Rule Context RelatedFees :=
  ⟨"notice/D409-2/paragraph/5", notice "PDF446頁 D409-2(5) 第13部",
    fun c r => Separate c → c.performance.item.sentinel → r.pathology.isSome = true⟩

def fusion : Rule Context Nat :=
  ⟨"primary/D413/item/1", primary "PDF211頁 D413の1",
    fun c p => Separate c → c.performance.item = .fusionProstate → p = 8210⟩

def prostate : Rule Context Nat :=
  ⟨"primary/D413/item/2", primary "PDF211頁 D413の2",
    fun c p => Separate c → c.performance.item = .otherProstate → p = 1848⟩

def fusionFacility : Rule Context Nat :=
  ⟨"primary/D413/note/unnumbered/1", primary "PDF211頁 D413注",
    fun c _ => c.performance.item = .fusionProstate →
      c.facilityComplies = true ∧ c.validFiling = true ∧ c.ministerDesignatedProstatePatient = true⟩

def fusionMethod : Rule Context Nat :=
  ⟨"notice/D413/paragraph/1", notice "PDF447頁 D413(1)",
    fun c _ => c.performance.item = .fusionProstate → c.fusionGuidanceUsed = true⟩

def fusionMaterials : Rule Context RelatedFees :=
  ⟨"notice/D413/paragraph/1", notice "PDF447頁 D413(1) 採取材料",
    fun c r => Separate c → c.performance.item = .fusionProstate → r.fusionMaterials = 0⟩

def fusionLesion : Rule Context Nat :=
  ⟨"notice/D413/paragraph/2", notice "PDF447頁 D413(2)",
    fun c _ => c.performance.item = .fusionProstate → c.mriOnlyLesionIncluded = true⟩

def surgery : Rule Context Nat :=
  ⟨"primary/ch2-part3-section4/general/1", primary "PDF210頁 第4節通則1",
    fun c p => c.duringOtherSurgery = true → p = 0⟩

def treatment : Rule Context Nat :=
  ⟨"primary/ch2-part3-section4/general/2", primary "PDF210頁 第4節通則2",
    fun c p => c.commonProcedureSameDay = true → p = 0⟩

def eligibilityRules :=
  [sentinelFacility, plannedSurgery, fusionFacility, fusionMethod, fusionLesion]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c 0

def rules :=
  [combined, single, surgerySameDay, fusion, prostate, surgery, treatment] ++ eligibilityRules

def assess (c : Context) : Option Nat :=
  SpecimenCollection.points {
    item := c.performance.item.item
    sides := c.sides
    duringSurgery := c.duringOtherSurgery ||
      (decide c.performance.item.sentinel && c.breastCancerSurgerySameDay)
    commonProcedureClaimedSameDay := c.commonProcedureSameDay
    facilityStandardNotified := c.facilityComplies && c.validFiling
    breastCancerPatient := c.breastCancer
    radioisotopeUsed := c.isotopeUsed
    dyeUsed := c.dyeUsed
    designatedProstatePatient := c.ministerDesignatedProstatePatient }

set_option maxHeartbeats 1200000 in
theorem satisfies_iff (c : Context) (p : Nat) (h : Eligible c) :
    Satisfies rules c p ↔ assess c = some p := by
  simp only [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, and_true,
    sentinelFacility, plannedSurgery, fusionFacility, fusionMethod, fusionLesion] at h
  simp only [rules, eligibilityRules, List.cons_append, List.nil_append, satisfies_cons,
    satisfies_nil, and_true, combined, single, surgerySameDay, fusion, prostate, surgery, treatment,
    sentinelFacility, plannedSurgery, fusionFacility, fusionMethod, fusionLesion]
  cases hm : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
    cases ht : c.commonProcedureSameDay <;> cases hd : c.breastCancerSurgerySameDay <;>
    cases sides : c.sides <;>
    simp [hm, hs, ht, hd, sides, Separate, assess, Method.sentinel, Method.item,
      SpecimenCollection.points, SpecimenCollection.assess, SpecimenCollection.notSeparateReason,
      SpecimenCollection.eligible, SpecimenCollection.isD400, SpecimenCollection.isDaily,
      SpecimenCollection.isSeries, SpecimenCollection.isUnilateral, SpecimenCollection.basePoints,
      SpecimenCollection.infantPoints, SpecimenCollection.Assessment.total,
      eq_comm (a := p)] at *
  all_goals
    cases hiso : c.isotopeUsed <;> cases hdye : c.dyeUsed <;> simp_all

set_option maxHeartbeats 1700000 in
theorem determines (c : Context) (valid : Eligible c) : DeterminesAt rules c := by
  have calculated : ∃ p, assess c = some p := by
    have checked := valid
    simp only [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, and_true,
      sentinelFacility, plannedSurgery, fusionFacility, fusionMethod, fusionLesion] at checked
    cases hm : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
      cases ht : c.commonProcedureSameDay <;> cases hd : c.breastCancerSurgerySameDay <;>
      simp [hm, hs, ht, hd, assess, Method.sentinel, Method.item, SpecimenCollection.points,
        SpecimenCollection.assess, SpecimenCollection.notSeparateReason, SpecimenCollection.isD400,
        SpecimenCollection.isDaily, SpecimenCollection.isSeries, SpecimenCollection.eligible] at *
    all_goals
      cases hi : c.isotopeUsed <;> cases hdye : c.dyeUsed <;> simp_all
  obtain ⟨p, hp⟩ := calculated
  refine ⟨⟨p, (satisfies_iff c p valid).2 hp⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a valid).1 ha).symm.trans ((satisfies_iff c b valid).1 hb))

end Sanri.MedicalFee.SpecimenNeedleSelection
