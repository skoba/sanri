import Sanri.SimplePunctures

namespace Sanri.MedicalFee.SpecimenCollectionGeneral

open Sanri.History Sanri.Logic

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

structure WoundCare where
  collection : Site
  woundCare : Site
  sameCollectionWound : Bool

def woundRule : Rule WoundCare Bool :=
  ⟨"notice/ch2-part3-section4/general/2", notice "PDF445頁 第4節通則2・J000",
    fun c eligible => c.sameCollectionWound = true →
      (eligible = true ↔ c.collection.date.key < c.woundCare.date.key)⟩

structure SharedPuncture where
  collection : Site
  treatment : Site
  item : SimplePunctures.Item
  /-- 同じ処置としての穿刺であることを照合済み。 -/
  sameProcedure : Bool

structure Choice where
  collection : Bool
  treatment : Bool

def Covers (c : SharedPuncture) : Prop :=
  c.collection = c.treatment ∧ c.sameProcedure = true ∧ c.item ≠ .marrowBiopsy

def exclusive : Rule SharedPuncture Choice :=
  ⟨"notice/ch2-part3-section4/general/3", notice "PDF445–446頁 第4節通則3",
    fun c r => Covers c → r.collection = false ∨ r.treatment = false⟩

private def procedureRule (number : Nat) (applies : SimplePunctures.Item → Prop) :
    Rule SharedPuncture Choice :=
  let id := toString number
  ⟨"notice/ch2-part3-section4/general/3/" ++ id, notice ("PDF446頁 第4節通則3(" ++ id ++ ")"),
    fun c r => Covers c → applies c.item → r.collection = false ∨ r.treatment = false⟩

def ventricular := procedureRule 1 (· = .ventricular)
def suboccipital := procedureRule 2 (· = .suboccipital)
def spine := procedureRule 3 (fun i => i = .lumbar ∨ i = .thoracic ∨ i = .cervical)
def marrow := procedureRule 4 (fun i => i = .sternalMarrow ∨ i = .otherMarrow)
def joint := procedureRule 5 (· = .joint)
def sinusOrTonsil := procedureRule 6 (fun i => i = .maxillary ∨ i = .peritonsillar)
def renal := procedureRule 7 (· = .renalCyst)
def douglas := procedureRule 8 (· = .douglas)
def lymph := procedureRule 9 (· = .lymphNode)
def breast := procedureRule 10 (fun i => i = .breastNeedle ∨ i = .breastOther)
def thyroid := procedureRule 11 (· = .thyroid)

structure CtGuidance where
  inD409ThroughD413 : Bool
  ctGuidancePerformed : Bool
  e200ResolvedPoints : Option Nat
  imagingGeneral2Applies : Bool
  imagingGeneral2ResolvedPoints : Option Nat

def ctSeparate : Rule CtGuidance Nat :=
  ⟨"notice/ch2-part3-section4/general/4", notice "PDF446頁 第4節通則4・E200",
    fun c p => c.inD409ThroughD413 = true → c.ctGuidancePerformed = true →
      (c.imagingGeneral2Applies = true → c.imagingGeneral2ResolvedPoints = some p) ∧
      (c.imagingGeneral2Applies = false → c.e200ResolvedPoints = some p)⟩

end Sanri.MedicalFee.SpecimenCollectionGeneral
