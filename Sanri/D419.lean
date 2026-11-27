import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D419

open Sanri.History Sanri.Logic

inductive Item where
  | gastric | pleuralAscitic | arterial | anteriorChamber | adrenal | swab
  deriving DecidableEq

def Item.legacy : Item → SpecimenCollection.Item
  | .gastric => .gastricDuodenalFluid
  | .pleuralAscitic => .pleuralAsciticFluid
  | .arterial => .arterialBlood
  | .anteriorChamber => .anteriorChamberFluid
  | .adrenal => .adrenalVenousSampling
  | .swab => .nasalPharyngealSwab

structure Context where
  performance : Performance Item
  ageYears : Nat
  duringSurgery : Bool
  commonProcedureSameDay : Bool
  bloodCircuit : Bool
  /-- 一連の範囲まで確認した履歴。一連IDが揃わない場合は none。 -/
  priorSeriesClaim : Option Bool
  dayClaims : ClaimHistory Item
  smearMicroscopyPerformed : Bool
  fluidChemistryPerformed : Bool
  cytologyPerformed : Bool
  intraocularDiagnosisPurpose : Bool
  adrenalIndication : Bool
  catheterReachedAdrenalVeins : Bool
  sampledBothAdrenalVeins : Bool
  adrenalFilmPoints : Nat

def daily (c : Context) : Option Bool :=
  let site := c.performance.site
  withinLimit c.dayClaims ⟨site.patient, some site.institution, Period.day site.date⟩ (· == .arterial) 0

def Separate (c : Context) : Prop :=
  c.duringSurgery = false ∧ c.commonProcedureSameDay = false ∧
  (c.performance.item = .arterial → c.bloodCircuit = false ∧ daily c = some true) ∧
  (c.performance.item = .gastric ∨ c.performance.item = .adrenal → c.priorSeriesClaim = some false)

structure Result where
  base : Nat
  infant : Nat
  film : Nat
  deriving DecidableEq

private def primary (locator : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度", locator,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (locator : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", locator,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def price (number : Nat) (item : Item) (points : Nat) : Rule Context Result :=
  let loc := toString number
  ⟨"primary/D419/item/" ++ loc, primary ("PDF212頁 D419の" ++ loc),
    fun c r => Separate c → c.performance.item = item → r.base = points⟩

def gastric := price 1 .gastric 210
def pleural := price 2 .pleuralAscitic 220
def arterial := price 3 .arterial 60
def anterior := price 4 .anteriorChamber 504
def adrenal := price 5 .adrenal 4800
def swab := price 6 .swab 25

private def infant (path : String) (item : Item) (points : Nat) : Rule Context Result :=
  ⟨"primary/D419/item/" ++ path, primary ("PDF212頁 D419の" ++ path),
    fun c r => Separate c → c.performance.item = item →
      r.infant = if c.ageYears < 6 then points else 0⟩

def pleuralInfant := infant "2/note" .pleuralAscitic 60
def arterialInfant := infant "3/note/2" .arterial 35
def anteriorInfant := infant "4/note" .anteriorChamber 90
def adrenalInfant := infant "5/note/3" .adrenal 1000

def circuit : Rule Context Result :=
  ⟨"primary/D419/item/3/note/1", primary "PDF212頁 D419の3注1",
    fun c r => c.performance.item = .arterial → c.bloodCircuit = true → r = ⟨0, 0, 0⟩⟩

def arterialDaily : Rule Context Result :=
  ⟨"primary/D419/item/3", primary "PDF212頁 D419の3 日次",
    fun c r => c.performance.item = .arterial → daily c = some false → r = ⟨0, 0, 0⟩⟩

def circuitNotice : Rule Context Result :=
  ⟨"notice/D419/paragraph/4", notice "PDF448頁 D419(4)",
    fun c r => c.performance.item = .arterial → c.bloodCircuit = true → r.base = 0⟩

def adrenalSeries : Rule Context Result :=
  ⟨"primary/D419/item/5/note/1", primary "PDF212頁 D419の5注1",
    fun c r => c.performance.item = .adrenal → c.priorSeriesClaim = some true → r = ⟨0, 0, 0⟩⟩

def film : Rule Context Result :=
  ⟨"primary/D419/item/5/note/2", primary "PDF212頁 D419の5注2",
    fun c r => Separate c → c.performance.item = .adrenal → r.film = c.adrenalFilmPoints⟩

structure Related where
  fluoroscopy : Nat
  simpleFluidTest : Nat
  smearMicroscopyD017 : Option Nat
  fluidChemistryD004 : Option Nat
  cytologyN004 : Option Nat
  contrastInjection : Nat
  contrastImage : Nat
  xrayDiagnosis : Nat
  additionalBloodCollection : Nat

def gastricSeries : Rule Context Result :=
  ⟨"notice/D419/paragraph/1", notice "PDF448頁 D419(1)",
    fun c r => c.performance.item = .gastric → c.priorSeriesClaim = some true → r = ⟨0, 0, 0⟩⟩

def gastricFluoroscopy : Rule Context Related :=
  ⟨"notice/D419/paragraph/1", notice "PDF448頁 D419(1) ゾンデ挿入時",
    fun c r => Separate c → c.performance.item = .gastric → r.fluoroscopy = 0⟩

def fluids : Rule Context Related :=
  ⟨"notice/D419/paragraph/2", notice "PDF448頁 D419(2) D017・D004の18・N004",
    fun c r => Separate c → c.performance.item = .pleuralAscitic →
      r.simpleFluidTest = 0 ∧
      (c.smearMicroscopyPerformed = true → r.smearMicroscopyD017.isSome = true) ∧
      (c.fluidChemistryPerformed = true → r.fluidChemistryD004.isSome = true) ∧
      (c.cytologyPerformed = true → r.cytologyN004.isSome = true)⟩

def anteriorPurpose : Rule Context Result :=
  ⟨"notice/D419/paragraph/3", notice "PDF448頁 D419(3)",
    fun c _ => c.performance.item = .anteriorChamber → c.intraocularDiagnosisPurpose = true⟩

def adrenalNotice : Rule Context Result :=
  ⟨"notice/D419/paragraph/5", notice "PDF449頁 D419(5)",
    fun c r => Separate c → c.performance.item = .adrenal → r.base = 4800⟩

def adrenalEligibility : Rule Context Result :=
  ⟨"notice/D419/paragraph/5/a", notice "PDF449頁 D419(5)ア",
    fun c _ => c.performance.item = .adrenal → c.adrenalIndication = true ∧
      c.catheterReachedAdrenalVeins = true ∧ c.sampledBothAdrenalVeins = true⟩

def adrenalIncluded : Rule Context Related :=
  ⟨"primary/D419/item/5/note/1", primary "PDF212頁 D419の5注1 包括費用",
    fun c r => Separate c → c.performance.item = .adrenal →
      r.fluoroscopy = 0 ∧ r.contrastInjection = 0 ∧ r.contrastImage = 0 ∧ r.xrayDiagnosis = 0⟩

def adrenalImaging : Rule Context Related :=
  ⟨"notice/D419/paragraph/5/i", notice "PDF449頁 D419(5)イ",
    fun c r => Separate c → c.performance.item = .adrenal → r.xrayDiagnosis = 0⟩

def adrenalBlood : Rule Context Related :=
  ⟨"notice/D419/paragraph/5/u", notice "PDF449頁 D419(5)ウ",
    fun c r => Separate c → c.performance.item = .adrenal → r.additionalBloodCollection = 0⟩

def surgery : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", primary "PDF210頁 第4節通則1",
    fun c r => c.duringSurgery = true → r = ⟨0, 0, 0⟩⟩

def treatment : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", primary "PDF210頁 第4節通則2",
    fun c r => c.commonProcedureSameDay = true → r = ⟨0, 0, 0⟩⟩

private def components : Rule Context Result :=
  ⟨"unclassified/d419-collection-components",
    ⟨.manualInterpretation, "採取料内訳", "2026-10-22", "加算等の適用項", .unchecked, none⟩,
    fun c r => (c.performance.item = .gastric ∨ c.performance.item = .swab → r.infant = 0) ∧
      (c.performance.item ≠ .adrenal → r.film = 0)⟩

def rules := [gastric, pleural, arterial, anterior, adrenal, swab, pleuralInfant,
  arterialInfant, anteriorInfant, adrenalInfant, circuit, arterialDaily, circuitNotice, adrenalSeries,
  film, gastricSeries, anteriorPurpose, adrenalNotice, adrenalEligibility, surgery, treatment, components]

def Eligible (c : Context) : Prop :=
  (c.performance.item = .anteriorChamber → c.intraocularDiagnosisPurpose = true) ∧
  (c.performance.item = .adrenal → c.adrenalIndication = true ∧
    c.catheterReachedAdrenalVeins = true ∧ c.sampledBothAdrenalVeins = true) ∧
  (c.performance.item = .arterial → (daily c).isSome = true) ∧
  (c.performance.item = .gastric ∨ c.performance.item = .adrenal → c.priorSeriesClaim.isSome = true)

def assess (c : Context) : Option Result := do
  let dayAvailable ← if c.performance.item = .arterial then daily c else some true
  let seriesUsed ← if c.performance.item = .gastric ∨ c.performance.item = .adrenal
    then c.priorSeriesClaim else some false
  let a ← SpecimenCollection.assess {
    item := c.performance.item.legacy
    ageYears := c.ageYears
    duringSurgery := c.duringSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay
    bloodCircuitSampling := c.bloodCircuit
    dailyAlreadyClaimed := !dayAvailable
    seriesAlreadyClaimed := seriesUsed
    filmPoints := c.adrenalFilmPoints }
  return ⟨a.base, a.infant, a.film⟩

set_option maxHeartbeats 3500000 in
theorem satisfies_iff (c : Context) (r : Result) (valid : Eligible c) :
    Satisfies rules c r ↔ assess c = some r := by
  obtain ⟨eye, adrenalOK, hd, hseries⟩ := valid
  simp only [rules, satisfies_cons, satisfies_nil, and_true, gastric, pleural, arterial, anterior,
    adrenal, swab, price, pleuralInfant, arterialInfant, anteriorInfant, adrenalInfant, infant, circuit,
    arterialDaily, circuitNotice, adrenalSeries, film, gastricSeries, anteriorPurpose, adrenalNotice,
    adrenalEligibility, surgery, treatment, components]
  have rate (n : Nat) : (if c.ageYears < 6 then n else 0) =
      (if 6 ≤ c.ageYears then 0 else n) := by split <;> split <;> omega
  cases hm : c.performance.item <;> cases hs : c.duringSurgery <;>
    cases ht : c.commonProcedureSameDay <;> cases r <;>
    simp [hm, hs, ht, Separate, assess, Item.legacy, SpecimenCollection.assess,
      SpecimenCollection.notSeparateReason, SpecimenCollection.isD400, SpecimenCollection.isDaily,
      SpecimenCollection.isSeries, SpecimenCollection.isD417, SpecimenCollection.isUnilateral,
      SpecimenCollection.basePoints, SpecimenCollection.eligible, SpecimenCollection.infantPoints,
      rate] at *
  all_goals
    first
    | grind
    | (cases hday : daily c <;> simp_all <;> rename_i available <;> cases available <;>
        cases hc : c.bloodCircuit <;> simp_all <;> grind)
    | (cases hprior : c.priorSeriesClaim <;> simp_all <;> rename_i prior <;> cases prior <;>
        simp_all <;> grind)

set_option maxHeartbeats 1700000 in
theorem determines (c : Context) (valid : Eligible c) : DeterminesAt rules c := by
  have calculated : ∃ r, assess c = some r := by
    obtain ⟨_, _, day, series⟩ := valid
    cases hm : c.performance.item <;> cases hs : c.duringSurgery <;>
      cases ht : c.commonProcedureSameDay <;>
      simp [hm, hs, ht, assess, Item.legacy, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.isD400,
        SpecimenCollection.isDaily, SpecimenCollection.isSeries, SpecimenCollection.eligible] at *
    all_goals
      first
      | ((cases h : daily c <;> simp_all) <;> rename_i available <;> cases available <;>
          cases c.bloodCircuit <;> simp_all)
      | ((cases h : c.priorSeriesClaim <;> simp_all) <;> rename_i prior <;> cases prior <;> simp_all)
  obtain ⟨r, hr⟩ := calculated
  refine ⟨⟨r, (satisfies_iff c r valid).2 hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a valid).1 ha).symm.trans ((satisfies_iff c b valid).1 hb))

end Sanri.MedicalFee.D419
