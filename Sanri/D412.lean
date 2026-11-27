import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D412

open Sanri.Logic Sanri.History

inductive Method where
  | percutaneousOtherOrgan | percutaneousRenal | transjugularLiver
  deriving DecidableEq

structure Context where
  performance : Performance Method
  /-- D404-2・D409〜D411・D412-2・D413の対象に当たるかの照合結果。 -/
  otherListedNeedleBiopsy : Bool
  liverBiopsyContraindication : Bool
  facilityComplies : Bool
  validFiling : Bool
  duringOtherSurgery : Bool
  commonProcedureSameDay : Bool
  /-- 写真診断のフィルムに対する解決済み点数。写真診断なしは0。 -/
  filmPoints : Nat

def Separate (c : Context) : Prop :=
  c.duringOtherSurgery = false ∧ c.commonProcedureSameDay = false

structure Result where
  biopsy : Nat
  film : Nat
  deriving DecidableEq

inductive RelatedFee where
  | xrayFluoroscopy | electrocardiography | ultrasound | simultaneousContrastInjection
  | imaging | imageDiagnosis
  deriving DecidableEq

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF211頁 " ++ loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def percutaneous : Rule Context Result :=
  ⟨"primary/D412/heading", primary "D412",
    fun c r => Separate c → c.performance.item = .percutaneousOtherOrgan → r = ⟨1920, 0⟩⟩

def renal : Rule Context Result :=
  ⟨"primary/D412-2/heading", primary "D412-2",
    fun c r => Separate c → c.performance.item = .percutaneousRenal → r = ⟨2400, 0⟩⟩

def liver : Rule Context Result :=
  ⟨"primary/D412-3/heading", primary "D412-3",
    fun c r => Separate c → c.performance.item = .transjugularLiver → r.biopsy = 13000⟩

def liverFacility : Rule Context Result :=
  ⟨"primary/D412-3/note/unnumbered/1", primary "D412-3注",
    fun c _ => c.performance.item = .transjugularLiver →
      c.facilityComplies = true ∧ c.validFiling = true⟩

def percutaneousScope : Rule Context Result :=
  ⟨"notice/D412/paragraph/unnumbered", notice "PDF446頁 D412",
    fun c _ => c.performance.item = .percutaneousOtherOrgan → c.otherListedNeedleBiopsy = false⟩

def percutaneousIncluded : Rule Context (RelatedFee → Nat) :=
  ⟨"notice/D412/paragraph/unnumbered", notice "PDF446頁 D412",
    fun c fees => Separate c → c.performance.item = .percutaneousOtherOrgan →
      fees .xrayFluoroscopy = 0 ∧ fees .electrocardiography = 0 ∧ fees .ultrasound = 0⟩

def renalIncluded : Rule Context (RelatedFee → Nat) :=
  ⟨"notice/D412-2/paragraph/unnumbered", notice "PDF447頁 D412-2",
    fun c fees => Separate c → c.performance.item = .percutaneousRenal →
      fees .electrocardiography = 0 ∧ fees .ultrasound = 0⟩

def liverEligibility : Rule Context Result :=
  ⟨"notice/D412-3/paragraph/1", notice "PDF447頁 D412-3(1)",
    fun c _ => c.performance.item = .transjugularLiver → c.liverBiopsyContraindication = true⟩

def liverFilm : Rule Context Result :=
  ⟨"notice/D412-3/paragraph/2", notice "PDF447頁 D412-3(2)",
    fun c r => Separate c → c.performance.item = .transjugularLiver → r.film = c.filmPoints⟩

/-- 同時実施または当該写真診断に伴う費用のみを入力する。 -/
def liverIncluded : Rule Context (RelatedFee → Nat) :=
  ⟨"notice/D412-3/paragraph/2", notice "PDF447頁 D412-3(2)",
    fun c fees => Separate c → c.performance.item = .transjugularLiver →
      fees .xrayFluoroscopy = 0 ∧ fees .simultaneousContrastInjection = 0 ∧
      fees .imaging = 0 ∧ fees .imageDiagnosis = 0⟩

/-- 一つの生検実施について、部位数を乗じない。 -/
def liverUnit : Rule Context Result :=
  ⟨"notice/D412-3/paragraph/3", notice "PDF447頁 D412-3(3)",
    fun c r => Separate c → c.performance.item = .transjugularLiver → r.biopsy = 13000⟩

def surgery : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", { primary "" with location := "PDF210頁 第4節通則1" },
    fun c r => c.duringOtherSurgery = true → r = ⟨0, 0⟩⟩

def commonProcedure : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", { primary "" with location := "PDF210頁 第4節通則2" },
    fun c r => c.commonProcedureSameDay = true → r = ⟨0, 0⟩⟩

def rules := [percutaneous, renal, liver, liverFacility, percutaneousScope, liverEligibility,
  liverFilm, liverUnit, surgery, commonProcedure]

def Eligible (c : Context) : Prop :=
  (c.performance.item = .percutaneousOtherOrgan → c.otherListedNeedleBiopsy = false) ∧
  (c.performance.item = .transjugularLiver →
    c.facilityComplies = true ∧ c.validFiling = true ∧ c.liverBiopsyContraindication = true)

def assess (c : Context) : Option Result := do
  let item ← match c.performance.item with
    | .percutaneousOtherOrgan =>
      if c.otherListedNeedleBiopsy then none else some SpecimenCollection.Item.percutaneousNeedleBiopsy
    | .percutaneousRenal => some .percutaneousRenalBiopsy
    | .transjugularLiver =>
      if c.facilityComplies && c.validFiling && c.liverBiopsyContraindication then
        some .transjugularLiverBiopsy else none
  let a ← SpecimenCollection.assess {
    item := item
    facilityStandardNotified := c.validFiling
    duringSurgery := c.duringOtherSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay }
  return ⟨a.base, if a.notSeparate.isNone && c.performance.item = .transjugularLiver then c.filmPoints else 0⟩

set_option maxHeartbeats 1000000 in
theorem satisfies_iff (c : Context) (r : Result) : Satisfies rules c r ↔ assess c = some r := by
  simp only [rules, satisfies_cons, satisfies_nil, and_true, percutaneous, renal, liver,
    liverFacility, percutaneousScope, liverEligibility, liverFilm, liverUnit, surgery, commonProcedure]
  cases hi : c.performance.item
  · cases ho : c.otherListedNeedleBiopsy <;> cases hs : c.duringOtherSurgery <;>
      cases hp : c.commonProcedureSameDay <;> cases r <;>
      simp [hi, ho, hs, hp, Separate, assess, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.eligible,
        SpecimenCollection.isD400, SpecimenCollection.isDaily, SpecimenCollection.isSeries,
        SpecimenCollection.isUnilateral, SpecimenCollection.basePoints] <;>
      exact and_congr eq_comm eq_comm
  · cases hs : c.duringOtherSurgery <;> cases hp : c.commonProcedureSameDay <;> cases r <;>
      simp [hi, hs, hp, Separate, assess, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.eligible,
        SpecimenCollection.isD400, SpecimenCollection.isDaily, SpecimenCollection.isSeries,
        SpecimenCollection.isUnilateral, SpecimenCollection.basePoints] <;>
      exact and_congr eq_comm eq_comm
  · cases hc : c.facilityComplies <;> cases hf : c.validFiling <;>
      cases he : c.liverBiopsyContraindication <;> cases hs : c.duringOtherSurgery <;>
      cases hp : c.commonProcedureSameDay <;> cases r <;>
      simp [hi, hc, hf, he, hs, hp, Separate, assess, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.eligible,
        SpecimenCollection.isD400, SpecimenCollection.isDaily, SpecimenCollection.isSeries,
        SpecimenCollection.isUnilateral, SpecimenCollection.basePoints] <;>
      grind

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  let r : Result := if c.duringOtherSurgery || c.commonProcedureSameDay then ⟨0, 0⟩
    else match c.performance.item with
      | .percutaneousOtherOrgan => ⟨1920, 0⟩
      | .percutaneousRenal => ⟨2400, 0⟩
      | .transjugularLiver => ⟨13000, c.filmPoints⟩
  obtain ⟨other, liverOK⟩ := h
  have hr : Satisfies rules c r := by
    cases hi : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
      cases hp : c.commonProcedureSameDay <;>
      simp_all [rules, satisfies_cons, satisfies_nil, percutaneous, renal, liver, liverFacility,
        percutaneousScope, liverEligibility, liverFilm, liverUnit, surgery, commonProcedure, Separate, r]
  refine ⟨⟨r, hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a).1 ha).symm.trans ((satisfies_iff c b).1 hb))

end Sanri.MedicalFee.D412
