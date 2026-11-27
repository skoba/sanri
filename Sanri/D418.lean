import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D418

open Sanri.History Sanri.Logic

inductive Item where
  | cervicalMucus | vaginalCervicalTissue | endometrialTissue | vaginalVaultCytology
  deriving DecidableEq

structure Context where
  performance : Performance Item
  afterTotalHysterectomy : Bool
  duringSurgery : Bool
  commonProcedureSameDay : Bool

def Separate (c : Context) : Prop :=
  c.duringSurgery = false ∧ c.commonProcedureSameDay = false

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def itemRule (number : Nat) (item : Item) (price : Nat) : Rule Context Nat :=
  ⟨"primary/D418/item/" ++ toString number, primary ("PDF212頁 D418の" ++ toString number),
    fun c p => Separate c → c.performance.item = item → p = price⟩

def mucus := itemRule 1 .cervicalMucus 40
def vaginal := itemRule 2 .vaginalCervicalTissue 200
def endometrial := itemRule 3 .endometrialTissue 370

def vault : Rule Context Nat :=
  ⟨"notice/D418/paragraph/unnumbered",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF448頁 D418", .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c p => c.performance.item = .vaginalVaultCytology →
      c.afterTotalHysterectomy = true ∧ (Separate c → p = 40)⟩

def surgery : Rule Context Nat :=
  ⟨"primary/ch2-part3-section4/general/1", primary "PDF210頁 第4節通則1",
    fun c p => c.duringSurgery = true → p = 0⟩

def commonProcedure : Rule Context Nat :=
  ⟨"primary/ch2-part3-section4/general/2", primary "PDF210頁 第4節通則2",
    fun c p => c.commonProcedureSameDay = true → p = 0⟩

def rules := [mucus, vaginal, endometrial, vault, surgery, commonProcedure]

def Eligible (c : Context) : Prop :=
  c.performance.item = .vaginalVaultCytology → c.afterTotalHysterectomy = true

def assess (c : Context) : Option Nat :=
  let item : SpecimenCollection.Item := match c.performance.item with
    | .cervicalMucus | .vaginalVaultCytology => .cervicalMucus
    | .vaginalCervicalTissue => .vaginalCervicalTissue
    | .endometrialTissue => .endometrialTissue
  if c.performance.item = .vaginalVaultCytology && !c.afterTotalHysterectomy then none
  else SpecimenCollection.points {
    item := item
    duringSurgery := c.duringSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay }

set_option maxHeartbeats 650000 in
theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ assess c = some p := by
  simp only [rules, satisfies_cons, satisfies_nil, and_true, mucus, vaginal, endometrial,
    itemRule, vault, surgery, commonProcedure]
  cases hi : c.performance.item <;> cases hh : c.afterTotalHysterectomy <;>
    cases hs : c.duringSurgery <;> cases hp : c.commonProcedureSameDay <;>
    simp [Separate, hi, hh, hs, hp, assess, SpecimenCollection.points, SpecimenCollection.assess,
      SpecimenCollection.notSeparateReason, SpecimenCollection.isD400, SpecimenCollection.isDaily,
      SpecimenCollection.isSeries, SpecimenCollection.eligible, SpecimenCollection.Assessment.total,
      SpecimenCollection.basePoints, SpecimenCollection.infantPoints,
      SpecimenCollection.isUnilateral, eq_comm (a := p)] <;> omega

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  have evaluated : ∃ p, assess c = some p := by
    cases hi : c.performance.item <;> cases hh : c.afterTotalHysterectomy <;>
      cases hs : c.duringSurgery <;> cases hp : c.commonProcedureSameDay <;>
      simp [Eligible, hi, hh] at h <;>
      simp [assess, hi, hh, hs, hp, SpecimenCollection.points, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.isD400,
        SpecimenCollection.isDaily, SpecimenCollection.isSeries, SpecimenCollection.eligible]
  obtain ⟨p, hp⟩ := evaluated
  refine ⟨⟨p, (satisfies_iff c p).2 hp⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a).1 ha).symm.trans ((satisfies_iff c b).1 hb))

private def sample : Context :=
  ⟨⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .vaginalVaultCytology, none, none, none, none⟩,
    true, false, false⟩

example : assess sample = some 40 := by decide
example : assess { sample with afterTotalHysterectomy := false } = none := by decide

end Sanri.MedicalFee.D418
