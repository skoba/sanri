import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D417

open Sanri.History Sanri.Logic

inductive Item where
  | skin | muscle | bone | posteriorEye | otherEye | ear | nasal | oral | pharynx
  | thyroid | breast | rectum | testis | nerve | myocardium
  deriving DecidableEq

def Item.legacy : Item → SpecimenCollection.Item
  | .skin => .skinTissue
  | .muscle => .muscleTissue
  | .bone => .bonePelvisSpineTissue
  | .posteriorEye => .posteriorEyeTissue
  | .otherEye => .otherEyeTissue
  | .ear => .earTissue
  | .nasal => .nasalSinusTissue
  | .oral => .oralTissue
  | .pharynx => .pharyngolaryngealTissue
  | .thyroid => .thyroidTissue
  | .breast => .breastTissue
  | .rectum => .rectalTissue
  | .testis => .testisEpididymisTissue
  | .nerve => .peripheralNerveTissue
  | .myocardium => .myocardiumTissue

structure Context where
  performance : Performance Item
  ageYears : Nat
  duringSurgery : Bool
  commonProcedureSameDay : Bool

structure Result where
  base : Nat
  infant : Nat
  deriving DecidableEq

def Separate (c : Context) : Prop :=
  c.duringSurgery = false ∧ c.commonProcedureSameDay = false

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def itemRule (path : String) (page : Nat) (item : Item) (price : Nat) : Rule Context Result :=
  ⟨"primary/D417/item/" ++ path, primary ("PDF" ++ toString page ++ "頁 D417の" ++ path),
    fun c r => Separate c → c.performance.item = item → r.base = price⟩

def skin := itemRule "1" 211 .skin 500
def muscle := itemRule "2" 211 .muscle 1500
def bone := itemRule "3" 211 .bone 4600
def posteriorEye := itemRule "4/i" 211 .posteriorEye 650
def otherEye := itemRule "4/ro" 211 .otherEye 350
def ear := itemRule "5" 211 .ear 400
def nasal := itemRule "6" 211 .nasal 400
def oral := itemRule "7" 211 .oral 400
def pharynx := itemRule "8" 211 .pharynx 650
def thyroid := itemRule "9" 211 .thyroid 650
def breast := itemRule "10" 211 .breast 650
def rectum := itemRule "11" 212 .rectum 780
def testis := itemRule "12" 212 .testis 400
def nerve := itemRule "13" 212 .nerve 1620
def myocardium := itemRule "14" 212 .myocardium 6000

def eye : Rule Context Result :=
  ⟨"primary/D417/item/4", primary "PDF211頁 D417の4",
    fun c r => Separate c →
      (c.performance.item = .posteriorEye ∨ c.performance.item = .otherEye) →
        r.base = if c.performance.item = .posteriorEye then 650 else 350⟩

def infant : Rule Context Result :=
  ⟨"primary/D417/note/unnumbered/1", primary "PDF212頁 D417注",
    fun c r => Separate c → r.infant = if c.ageYears < 6 then 100 else 0⟩

def surgery : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", primary "PDF210頁 第4節通則1",
    fun c r => c.duringSurgery = true → r = ⟨0, 0⟩⟩

def commonProcedure : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", primary "PDF210頁 第4節通則2",
    fun c r => c.commonProcedureSameDay = true → r = ⟨0, 0⟩⟩

def rules := [skin, muscle, bone, eye, posteriorEye, otherEye, ear, nasal, oral, pharynx,
  thyroid, breast, rectum, testis, nerve, myocardium, infant, surgery, commonProcedure]

def assess (c : Context) : Option Result :=
  (SpecimenCollection.assess {
    item := c.performance.item.legacy
    ageYears := c.ageYears
    duringSurgery := c.duringSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay }).map (fun a => ⟨a.base, a.infant⟩)

set_option maxHeartbeats 1400000 in
theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ assess c = some r := by
  have rate : (if c.ageYears < 6 then 100 else 0) =
      (if 6 ≤ c.ageYears then 0 else 100) := by split <;> split <;> omega
  simp only [rules, satisfies_cons, satisfies_nil, and_true, skin, muscle, bone, eye,
    posteriorEye, otherEye, ear, nasal, oral, pharynx, thyroid, breast, rectum, testis, nerve,
    myocardium, infant, surgery, commonProcedure, itemRule]
  cases hi : c.performance.item <;> cases hs : c.duringSurgery <;>
    cases hp : c.commonProcedureSameDay <;> cases r <;>
    simp [Separate, assess, hi, hs, hp, rate, Item.legacy,
      SpecimenCollection.assess, SpecimenCollection.notSeparateReason,
      SpecimenCollection.isD400, SpecimenCollection.isDaily, SpecimenCollection.isSeries,
      SpecimenCollection.isUnilateral, SpecimenCollection.eligible, SpecimenCollection.basePoints,
      SpecimenCollection.infantPoints, SpecimenCollection.isD417] <;>
    exact and_congr eq_comm eq_comm

theorem determines (c : Context) : DeterminesAt rules c := by
  have evaluated : ∃ r, assess c = some r := by
    cases hi : c.performance.item <;> cases hs : c.duringSurgery <;>
      cases hp : c.commonProcedureSameDay <;>
      simp [assess, hi, hs, hp, Item.legacy, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.isD400, SpecimenCollection.isDaily,
        SpecimenCollection.isSeries, SpecimenCollection.eligible]
  obtain ⟨r, hr⟩ := evaluated
  refine ⟨⟨r, (satisfies_iff c r).2 hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a).1 ha).symm.trans ((satisfies_iff c b).1 hb))

end Sanri.MedicalFee.D417
