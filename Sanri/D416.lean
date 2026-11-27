import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D416

open Sanri.History Sanri.Logic

inductive Approach where
  | thoracotomy | laparotomy
  deriving DecidableEq

structure Context where
  performance : Performance Approach
  /-- 開腹採取の同一実施をまとめて確認した単位。 -/
  collectionUnit : Nat
  ageYears : Nat
  duringOtherSurgery : Bool
  commonProcedureSameDay : Bool

def Separate (c : Context) : Prop :=
  c.duringOtherSurgery = false ∧ c.commonProcedureSameDay = false

structure Result where
  units : Nat
  base : Nat
  infant : Nat
  deriving DecidableEq

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

def thoracotomy : Rule Context Result :=
  ⟨"primary/D416/item/1", primary "PDF211頁 D416の1",
    fun c r => Separate c → c.performance.item = .thoracotomy → r.units = 1 ∧ r.base = 9070⟩

def laparotomy : Rule Context Result :=
  ⟨"primary/D416/item/2", primary "PDF211頁 D416の2",
    fun c r => Separate c → c.performance.item = .laparotomy → r.base = 5550⟩

def infant : Rule Context Result :=
  ⟨"primary/D416/note/unnumbered/1", primary "PDF211頁 D416注",
    fun c r => Separate c → r.infant = (if c.ageYears < 6 then 2000 else 0)⟩

def laparotomyUnit : Rule Context Result :=
  ⟨"notice/D416/paragraph/unnumbered",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", "PDF448頁 D416",
      .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
     fun c r => Separate c → c.performance.item = .laparotomy → r.units = 1⟩

def surgery : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", primary "PDF210頁 第4節通則1",
    fun c r => c.duringOtherSurgery = true → r = ⟨0, 0, 0⟩⟩

def commonProcedure : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", primary "PDF210頁 第4節通則2",
    fun c r => c.commonProcedureSameDay = true → r = ⟨0, 0, 0⟩⟩

def rules := [thoracotomy, laparotomy, infant, laparotomyUnit, surgery, commonProcedure]

def assess (c : Context) : Option Result :=
  let item := match c.performance.item with
    | .thoracotomy => SpecimenCollection.Item.thoracotomyTissue
    | .laparotomy => SpecimenCollection.Item.laparotomyTissue
  (SpecimenCollection.assess {
    item := item
    ageYears := c.ageYears
    duringSurgery := c.duringOtherSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay }).map (fun a => ⟨a.units, a.base, a.infant⟩)

set_option maxHeartbeats 500000 in
theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ assess c = some r := by
  have rate : (if c.ageYears < 6 then 2000 else 0) =
      (if 6 ≤ c.ageYears then 0 else 2000) := by split <;> split <;> omega
  cases hi : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
    cases hp : c.commonProcedureSameDay <;> cases r <;>
    simp [rules, satisfies_cons, satisfies_nil, thoracotomy, laparotomy, infant,
      laparotomyUnit, surgery, commonProcedure, Separate, assess, hi, hs, hp, rate,
      SpecimenCollection.assess, SpecimenCollection.notSeparateReason,
      SpecimenCollection.isD400, SpecimenCollection.isDaily, SpecimenCollection.isSeries,
      SpecimenCollection.isUnilateral, SpecimenCollection.eligible, SpecimenCollection.basePoints,
      SpecimenCollection.infantPoints, SpecimenCollection.isD417] <;> grind

theorem determines (c : Context) : DeterminesAt rules c := by
  have evaluated : ∃ r, assess c = some r := by
    cases hi : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
      cases hp : c.commonProcedureSameDay <;>
      simp [assess, hi, hs, hp, SpecimenCollection.assess, SpecimenCollection.notSeparateReason,
        SpecimenCollection.isD400, SpecimenCollection.isDaily, SpecimenCollection.isSeries,
        SpecimenCollection.eligible]
  obtain ⟨r, hr⟩ := evaluated
  refine ⟨⟨r, (satisfies_iff c r).2 hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a).1 ha).symm.trans ((satisfies_iff c b).1 hb))

end Sanri.MedicalFee.D416
