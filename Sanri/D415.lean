import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D415

open Sanri.History Sanri.Logic

inductive Method where
  | transbronchial | ebus | navigated | virtual | cryobiopsy | pleuralCryobiopsy
  deriving DecidableEq

def Method.item : Method → SpecimenCollection.Item
  | .transbronchial => .transbronchialLungBiopsy
  | .ebus => .ebusTbna
  | .navigated => .navigatedLungBiopsy
  | .virtual => .virtualBronchoscopyBiopsy
  | .cryobiopsy => .transbronchialCryobiopsy
  | .pleuralCryobiopsy => .parietalPleuralCryobiopsy

structure Context where
  performance : Performance Method
  duringOtherSurgery : Bool
  commonProcedureSameDay : Bool
  guideSheathUltrasound : Bool
  continuousCt : Bool
  ctFacilityComplies : Bool
  ctValidFiling : Bool
  probeConfocal : Bool
  convexUltrasoundBronchoscope : Bool
  peripheralShadowAtMostTwoCm : Bool
  difficultPeripheralLesion : Bool
  electromagneticNavigationFromCt : Bool
  virtualBronchoscopeFromCt : Bool
  frozenLungTissue : Bool
  cryobiopsyFacilityComplies : Bool
  cryobiopsyValidFiling : Bool

def Separate (c : Context) : Prop :=
  c.duringOtherSurgery = false ∧ c.commonProcedureSameDay = false

structure Result where
  base : Nat
  guideSheath : Nat
  ctAddition : Nat
  endomicroscopy : Nat
  deriving DecidableEq

private def primary (locator : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度", locator,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (locator : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", locator,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def priceRule (code : String) (method : Method) (price : Nat) : Rule Context Result :=
  ⟨"primary/" ++ code ++ "/heading", primary ("PDF211頁 " ++ code),
    fun c r => Separate c → c.performance.item = method → r.base = price⟩

def transbronchial := priceRule "D415" .transbronchial 4800
def ebus := priceRule "D415-2" .ebus 5500
def navigated := priceRule "D415-3" .navigated 5500
def virtual := priceRule "D415-4" .virtual 5000
def cryobiopsy := priceRule "D415-5" .cryobiopsy 5500
def pleuralCryobiopsy := priceRule "D415-6" .pleuralCryobiopsy 15800

def guide : Rule Context Result :=
  ⟨"primary/D415/note/1", primary "PDF211頁 D415注1",
    fun c r => Separate c → c.performance.item = .transbronchial → c.probeConfocal = false →
      r.guideSheath = if c.guideSheathUltrasound then 500 else 0⟩

def ct : Rule Context Result :=
  ⟨"primary/D415/note/2", primary "PDF211頁 D415注2",
    fun c r => Separate c → c.performance.item = .transbronchial →
      r.ctAddition = if c.continuousCt && c.ctFacilityComplies && c.ctValidFiling then 1000 else 0⟩

def probe : Rule Context Result :=
  ⟨"primary/D415/note/3", primary "PDF211頁 D415注3",
    fun c r => Separate c → c.performance.item = .transbronchial →
      r.endomicroscopy = (if c.probeConfocal then 1500 else 0) ∧
      (c.probeConfocal = true → r.guideSheath = 0)⟩

def virtualGuide : Rule Context Result :=
  ⟨"primary/D415-4/note/unnumbered/1", primary "PDF211頁 D415-4注",
    fun c r => Separate c → c.performance.item = .virtual →
      r.guideSheath = if c.guideSheathUltrasound then 500 else 0⟩

private def facilityRule (code : String) (method : Method) : Rule Context Result :=
  ⟨"primary/" ++ code ++ "/note/unnumbered/1", primary ("PDF211頁 " ++ code ++ "注"),
    fun c _ => c.performance.item = method →
      c.cryobiopsyFacilityComplies = true ∧ c.cryobiopsyValidFiling = true⟩

def cryobiopsyFacility := facilityRule "D415-5" .cryobiopsy
def pleuralFacility := facilityRule "D415-6" .pleuralCryobiopsy

inductive Related where
  | fluoroscopy | photography | imageDiagnosis | bronchoscopy | ultrasound | thoracoscopy
  deriving DecidableEq

private def relatedRule (code : String) (number : Nat) (page : Nat) (method : Method)
    (services : List Related) : Rule Context (Related → Nat) :=
  ⟨"notice/" ++ code ++ "/paragraph/" ++ toString number,
    notice ("PDF" ++ toString page ++ "頁 " ++ code ++ "(" ++ toString number ++ ")"),
    fun c fees => Separate c → c.performance.item = method → ∀ service ∈ services, fees service = 0⟩

/-- 同時透視・当該写真診断に対応する費用を入力する。フィルムとCTは別に評価する。 -/
def transbronchialFluoroscopy :=
  relatedRule "D415" 1 447 .transbronchial [.fluoroscopy, .photography, .imageDiagnosis]
def transbronchialBronchoscopy := relatedRule "D415" 3 447 .transbronchial [.bronchoscopy]
def ebusServices := relatedRule "D415-2" 1 447 .ebus [.bronchoscopy, .ultrasound]
def ebusFluoroscopy := relatedRule "D415-2" 3 447 .ebus [.fluoroscopy, .photography, .imageDiagnosis]
def navigatedBronchoscopy := relatedRule "D415-3" 3 448 .navigated [.bronchoscopy]
def virtualBronchoscopy := relatedRule "D415-4" 3 448 .virtual [.bronchoscopy]
def cryobiopsyFluoroscopy :=
  relatedRule "D415-5" 2 448 .cryobiopsy [.fluoroscopy, .photography, .imageDiagnosis]
def cryobiopsyBronchoscopy := relatedRule "D415-5" 4 448 .cryobiopsy [.bronchoscopy]
def pleuralThoracoscopy := relatedRule "D415-6" 2 448 .pleuralCryobiopsy [.thoracoscopy]

private def unitRule (code : String) (number page : Nat) (method : Method) : Rule Context Nat :=
  ⟨"notice/" ++ code ++ "/paragraph/" ++ toString number,
    notice ("PDF" ++ toString page ++ "頁 " ++ code ++ "(" ++ toString number ++ ")"),
    fun c units => Separate c → c.performance.item = method → units = 1⟩

def transbronchialUnit := unitRule "D415" 2 447 .transbronchial
def ebusUnit := unitRule "D415-2" 2 447 .ebus
def navigatedUnit := unitRule "D415-3" 2 448 .navigated
def virtualUnit := unitRule "D415-4" 2 448 .virtual
def cryobiopsyUnit := unitRule "D415-5" 3 448 .cryobiopsy
def pleuralUnit := unitRule "D415-6" 1 448 .pleuralCryobiopsy

def ctContinuous : Rule Context Result :=
  ⟨"notice/D415/paragraph/4", notice "PDF447頁 D415(4)",
    fun c r => c.performance.item = .transbronchial → 0 < r.ctAddition → c.continuousCt = true⟩

def convex : Rule Context Result :=
  ⟨"notice/D415-2/paragraph/1", notice "PDF447頁 D415-2(1)",
    fun c _ => c.performance.item = .ebus → c.convexUltrasoundBronchoscope = true⟩

def Peripheral (c : Context) : Prop :=
  c.peripheralShadowAtMostTwoCm = true ∨ c.difficultPeripheralLesion = true

def navigation : Rule Context Result :=
  ⟨"notice/D415-3/paragraph/1", notice "PDF447–448頁 D415-3(1)",
    fun c _ => c.performance.item = .navigated → Peripheral c ∧ c.electromagneticNavigationFromCt = true⟩

def virtualImaging : Rule Context Result :=
  ⟨"notice/D415-4/paragraph/1", notice "PDF448頁 D415-4(1)",
    fun c _ => c.performance.item = .virtual → Peripheral c ∧ c.virtualBronchoscopeFromCt = true⟩

def freezing : Rule Context Result :=
  ⟨"notice/D415-5/paragraph/1", notice "PDF448頁 D415-5(1)",
    fun c _ => c.performance.item = .cryobiopsy → c.frozenLungTissue = true⟩

def surgery : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", primary "PDF210頁 第4節通則1",
    fun c r => c.duringOtherSurgery = true → r = ⟨0, 0, 0, 0⟩⟩

def commonProcedure : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", primary "PDF210頁 第4節通則2",
    fun c r => c.commonProcedureSameDay = true → r = ⟨0, 0, 0, 0⟩⟩

private def components : Rule Context Result :=
  ⟨"unclassified/d415-addition-components",
    ⟨.manualInterpretation, "採取料内訳", "2026-10-22", "加算の適用区分", .unchecked, none⟩,
    fun c r =>
      (c.performance.item ≠ .transbronchial → r.ctAddition = 0 ∧ r.endomicroscopy = 0) ∧
      (c.performance.item ≠ .transbronchial → c.performance.item ≠ .virtual → r.guideSheath = 0)⟩

def eligibilityRules :=
  [cryobiopsyFacility, pleuralFacility, convex, navigation, virtualImaging, freezing]

def rules :=
  [transbronchial, ebus, navigated, virtual, cryobiopsy, pleuralCryobiopsy, guide, ct, probe,
    virtualGuide, ctContinuous, surgery, commonProcedure, components] ++ eligibilityRules

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ⟨0, 0, 0, 0⟩

def legacyInput (c : Context) : SpecimenCollection.Context :=
  { item := c.performance.item.item
    duringSurgery := c.duringOtherSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay
    facilityStandardNotified := c.cryobiopsyFacilityComplies && c.cryobiopsyValidFiling
    guideSheathUltrasoundPerformed := c.guideSheathUltrasound
    ctFluoroscopicBronchoscopy := c.continuousCt && c.ctFacilityComplies && c.ctValidFiling
    ctFluoroscopyStandardNotified := c.ctFacilityComplies && c.ctValidFiling
    probeConfocalEndomicroscopy := c.probeConfocal }

def assess (c : Context) : Option Result :=
  (SpecimenCollection.assess (legacyInput c)).map
    (fun a => ⟨a.base, a.guideSheath, a.ctFluoroscopy, a.endomicroscopy⟩)

set_option maxHeartbeats 1200000 in
theorem satisfies_iff (c : Context) (r : Result) (valid : Eligible c) :
    Satisfies rules c r ↔ assess c = some r := by
  simp only [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, and_true,
    cryobiopsyFacility, pleuralFacility, facilityRule, convex, navigation, virtualImaging,
    freezing] at valid
  simp only [rules, eligibilityRules, List.cons_append, List.nil_append, satisfies_cons,
    satisfies_nil, and_true, transbronchial, ebus, navigated, virtual, cryobiopsy,
    pleuralCryobiopsy, priceRule, guide, ct, probe, virtualGuide, ctContinuous, surgery,
    commonProcedure, components, cryobiopsyFacility, pleuralFacility, facilityRule,
    convex, navigation, virtualImaging, freezing]
  cases hi : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
    cases hp : c.commonProcedureSameDay <;> cases r <;>
    simp [hi, hs, hp, Separate, assess, legacyInput, Method.item, SpecimenCollection.assess,
      SpecimenCollection.notSeparateReason, SpecimenCollection.eligible, SpecimenCollection.isD400,
      SpecimenCollection.isDaily, SpecimenCollection.isSeries, SpecimenCollection.isUnilateral,
      SpecimenCollection.basePoints] at *
  all_goals
    first
    | grind
    | (cases hct : c.continuousCt <;> cases hc : c.ctFacilityComplies <;>
         cases hf : c.ctValidFiling <;> cases hprobe : c.probeConfocal <;>
         simp [hct, hc, hf, hprobe] at * <;> grind)

set_option maxHeartbeats 1700000 in
theorem determines (c : Context) (valid : Eligible c) : DeterminesAt rules c := by
  have calculated : ∃ r, assess c = some r := by
    have checked := valid
    simp only [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, and_true,
      cryobiopsyFacility, pleuralFacility, facilityRule, convex, navigation, virtualImaging,
      freezing] at checked
    cases hm : c.performance.item <;> cases hs : c.duringOtherSurgery <;>
      cases ht : c.commonProcedureSameDay <;>
      simp [hm, hs, ht, assess, legacyInput, Method.item, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.isD400, SpecimenCollection.isDaily,
        SpecimenCollection.isSeries, SpecimenCollection.eligible] at *
    all_goals
      first
      | grind
      | (cases c.continuousCt <;> cases c.ctFacilityComplies <;> cases c.ctValidFiling <;> simp_all)
  obtain ⟨r, hr⟩ := calculated
  refine ⟨⟨r, (satisfies_iff c r valid).2 hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a valid).1 ha).symm.trans ((satisfies_iff c b valid).1 hb))

end Sanri.MedicalFee.D415
