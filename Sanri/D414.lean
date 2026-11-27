import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D414

open Sanri.History Sanri.Logic

inductive Method where
  | endoscopic | eusFna
  deriving DecidableEq

structure Context where
  performance : Performance Method
  /-- N000の臓器区分との照合を終えた、実際に採取した臓器ID。 -/
  organs : List Nat
  convexEndoscope : Bool
  transDigestiveTract : Bool
  /-- 部位に応じた主たる内視鏡検査と確認した外部点数。 -/
  mainEndoscopyPoints : Option Nat
  duringOtherSurgery : Bool
  commonProcedureSameDay : Bool

def Separate (c : Context) : Prop :=
  c.duringOtherSurgery = false ∧ c.commonProcedureSameDay = false
instance (c : Context) : Decidable (Separate c) := by unfold Separate; infer_instance

structure Result where
  biopsy : Nat
  endoscopy : Nat
  ultrasoundEndoscopyAddition : Nat
  deriving DecidableEq

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def endoscopic : Rule Context Result :=
  ⟨"primary/D414/heading", primary "PDF211頁 D414",
    fun c r => Separate c → c.performance.item = .endoscopic →
      r.biopsy = 310 * c.organs.eraseDups.length⟩

def organ : Rule Context Result :=
  ⟨"notice/D414/paragraph/unnumbered", notice "PDF447頁 D414",
    fun c _ => c.performance.item = .endoscopic → c.organs ≠ []⟩

def eus : Rule Context Result :=
  ⟨"primary/D414-2/heading", primary "PDF211頁 D414-2",
    fun c r => Separate c → c.performance.item = .eusFna → r.biopsy = 5760⟩

def eusMethod : Rule Context Result :=
  ⟨"notice/D414-2/paragraph/1", notice "PDF447頁 D414-2(1)",
    fun c _ => c.performance.item = .eusFna →
      c.convexEndoscope = true ∧ c.transDigestiveTract = true⟩

def eusCombination : Rule Context Result :=
  ⟨"notice/D414-2/paragraph/2", notice "PDF447頁 D414-2(2)",
    fun c r => Separate c → c.performance.item = .eusFna →
      c.mainEndoscopyPoints = some r.endoscopy ∧ r.ultrasoundEndoscopyAddition = 0⟩

def surgery : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", primary "PDF210頁 第4節通則1",
    fun c r => c.duringOtherSurgery = true → r = ⟨0, 0, 0⟩⟩

def commonProcedure : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", primary "PDF210頁 第4節通則2",
    fun c r => c.commonProcedureSameDay = true → r = ⟨0, 0, 0⟩⟩

private def separateComponents : Rule Context Result :=
  ⟨"unclassified/d414-composition-scope",
    ⟨.manualInterpretation, "採取料内訳", "2026-10-22", "EUS-FNAに固有の併施構成", .unchecked, none⟩,
    fun c r => c.performance.item = .endoscopic → r.endoscopy = 0 ∧ r.ultrasoundEndoscopyAddition = 0⟩

def rules := [endoscopic, organ, eus, eusMethod, eusCombination, surgery, commonProcedure, separateComponents]

def Eligible (c : Context) : Prop :=
  (c.performance.item = .endoscopic → c.organs ≠ []) ∧
  (c.performance.item = .eusFna →
    c.convexEndoscope = true ∧ c.transDigestiveTract = true ∧
      (Separate c → c.mainEndoscopyPoints.isSome = true))

def legacyBase (c : Context) : Option Nat :=
  SpecimenCollection.points {
    item := if c.performance.item = .endoscopic then .endoscopicBiopsy else .eusFna
    organs := c.organs
    duringSurgery := c.duringOtherSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay }

theorem satisfies_iff (c : Context) (r : Result) (valid : Eligible c) :
    Satisfies rules c r ↔ legacyBase c = some r.biopsy ∧
      (Separate c → c.performance.item = .eusFna → c.mainEndoscopyPoints = some r.endoscopy) ∧
      (¬ Separate c ∨ c.performance.item = .endoscopic → r.endoscopy = 0) ∧
      r.ultrasoundEndoscopyAddition = 0 := by
  obtain ⟨nonempty, eusOK⟩ := valid
  cases hi : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
    cases hp : c.commonProcedureSameDay <;> cases r <;>
    simp [rules, satisfies_cons, satisfies_nil, endoscopic, organ, eus, eusMethod, eusCombination,
      surgery, commonProcedure, separateComponents, Separate, legacyBase, hi, hs, hp,
      SpecimenCollection.points, SpecimenCollection.assess, SpecimenCollection.notSeparateReason,
      SpecimenCollection.eligible, SpecimenCollection.isD400, SpecimenCollection.isDaily,
      SpecimenCollection.isSeries, SpecimenCollection.isUnilateral, SpecimenCollection.basePoints,
      SpecimenCollection.infantPoints, SpecimenCollection.Assessment.total,
      Nat.mul_comm] at * <;> grind

theorem determines : DeterminesOn Eligible rules := by
  intro c valid
  obtain ⟨nonempty, eusOK⟩ := valid
  let r : Result := if Separate c then
    match c.performance.item with
    | .endoscopic => ⟨310 * c.organs.eraseDups.length, 0, 0⟩
    | .eusFna => ⟨5760, c.mainEndoscopyPoints.getD 0, 0⟩
    else ⟨0, 0, 0⟩
  have valid : Eligible c := ⟨nonempty, eusOK⟩
  have hr : Satisfies rules c r := by
    have main (h : c.mainEndoscopyPoints.isSome = true) :
        c.mainEndoscopyPoints = some (c.mainEndoscopyPoints.getD 0) := by
      cases hmain : c.mainEndoscopyPoints <;> simp_all
    cases hi : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
      cases hp : c.commonProcedureSameDay <;>
      simp [rules, satisfies_cons, satisfies_nil, endoscopic, organ, eus, eusMethod, eusCombination,
        surgery, commonProcedure, separateComponents, Separate, hi, hs, hp, r] at * <;> grind
  refine ⟨⟨r, hr⟩, ?_⟩
  intro a b ha hb
  obtain ⟨ab, ae, az, au⟩ := (satisfies_iff c a valid).1 ha
  obtain ⟨bb, be, bz, bu⟩ := (satisfies_iff c b valid).1 hb
  have base := Option.some.inj (ab.symm.trans bb)
  have endo : a.endoscopy = b.endoscopy := by
    by_cases sep : Separate c
    · cases hi : c.performance.item
      · exact (az (.inr hi)).trans (bz (.inr hi)).symm
      · exact Option.some.inj ((ae sep hi).symm.trans (be sep hi))
    · exact (az (.inl sep)).trans (bz (.inl sep)).symm
  cases a
  cases b
  simp_all

end Sanri.MedicalFee.D414
