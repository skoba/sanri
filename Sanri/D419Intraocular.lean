import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D419Intraocular

open Sanri.Logic Sanri.History

inductive Fluid where
  | aqueous | vitreous
  deriving DecidableEq

structure Context where
  performance : Performance Fluid
  lymphomaDiagnosisPurpose : Bool
  il10ByElisa : Bool
  il6ByCleia : Bool
  duringSurgery : Bool
  commonProcedureSameDay : Bool

structure Result where
  examination : Nat
  sameSpecimenCollection : Nat
  deriving DecidableEq

def Eligible (c : Context) : Prop :=
  c.lymphomaDiagnosisPurpose = true ∧ c.il10ByElisa = true ∧ c.il6ByCleia = true

def heading : Rule Context Result :=
  ⟨"primary/D419-2/heading",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度", "PDF212頁 D419-2",
      .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun c r => r.examination = if c.duringSurgery || c.commonProcedureSameDay then 0 else 1000⟩

/-- 当該眼内液検査に用いた採取の費用に限る。別検体の採取費用はこの結果型の範囲外。 -/
def testAndCollection : Rule Context Result :=
  ⟨"notice/D419-2/paragraph/unnumbered",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", "PDF449頁 D419-2",
      .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c r => Eligible c ∧ r.sameSpecimenCollection = 0⟩

def rules := [heading, testAndCollection]

def assess (c : Context) : Option Result :=
  if c.lymphomaDiagnosisPurpose && c.il10ByElisa && c.il6ByCleia then
    (SpecimenCollection.points {
      item := .intraocularFluidExamination
      duringSurgery := c.duringSurgery
      commonProcedureClaimedSameDay := c.commonProcedureSameDay }).map (fun p => ⟨p, 0⟩)
  else none

theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ assess c = some r := by
  cases r with
  | mk p collection =>
    cases hc : c.lymphomaDiagnosisPurpose <;> cases he : c.il10ByElisa <;>
      cases hl : c.il6ByCleia <;> cases hs : c.duringSurgery <;> cases ht : c.commonProcedureSameDay <;>
      simp [rules, satisfies_cons, satisfies_nil, heading, testAndCollection, Eligible, assess,
        hc, he, hl, hs, ht, SpecimenCollection.points, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.isD400, SpecimenCollection.isDaily,
        SpecimenCollection.isSeries, SpecimenCollection.eligible, SpecimenCollection.Assessment.total,
        SpecimenCollection.basePoints, SpecimenCollection.infantPoints, SpecimenCollection.isUnilateral,
        eq_comm (a := p), eq_comm (a := collection)]

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  let r : Result := ⟨if c.duringSurgery || c.commonProcedureSameDay then 0 else 1000, 0⟩
  have hr : Satisfies rules c r := by
    simp [rules, satisfies_cons, satisfies_nil, heading, testAndCollection, r, h]
  refine ⟨⟨r, hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a).1 ha).symm.trans ((satisfies_iff c b).1 hb))

private def sample : Context :=
  ⟨⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .aqueous, none, some 1, none, none⟩,
    true, true, true, false, false⟩

example : assess sample = some ⟨1000, 0⟩ := by decide
example : assess { sample with il6ByCleia := false } = none := by decide

end Sanri.MedicalFee.D419Intraocular
