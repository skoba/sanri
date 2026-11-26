import Sanri.Logic
import Sanri.D007

namespace Sanri.MedicalFee.BloodChemistryFurther

open Sanri.Logic

/-! D007の9〜24の外来実施料と、通知が参照する35の血液ガス分析。
17・21の糖代謝検査は GlycemicTests の月内モデルを使う。 -/

abbrev Apolipoprotein := D007.Apolipoprotein
namespace Apolipoprotein
export D007.Apolipoprotein (aI aII b cII cIII e)
end Apolipoprotein

abbrev OrganicAcid := D007.OrganicAcid
namespace OrganicAcid
export D007.OrganicAcid (glutathione lactate pyruvate alphaKetoglutarate)
end OrganicAcid

abbrev Item := D007.ScopedItem .further

namespace Item
export D007.ScopedItem (
  ketoneBodies apolipoproteins adenosineDeaminase guanase organicAcid
  bileAcids urinarySulfatedBileAcids alpIsoenzymes amylaseIsoenzymes gammaGTIsoenzymes
  ldIsoenzymes bicarbonate astIsoenzymes lipoproteinFraction ammonia
  ckIsoenzymes cholesterolFraction ketoneFractions freeFattyAcids lcat
  g6pd lipoproteinPag glycocholicAcid ckMbMass ldIsoenzyme1
  totalCarnitine freeCarnitine alpIsoenzymesAndBap bloodGas)
end Item

def apolipoproteinPoints (measured : List Apolipoprotein) : Option Nat :=
  match measured.eraseDups.length with
  | 0 => none
  | 1 => some 31
  | 2 => some 62
  | _ => some 94

def Item.scheduledPoints : Item → Option Nat
  | .apolipoproteins measured => apolipoproteinPoints measured
  | .ketoneBodies => some 30
  | .adenosineDeaminase => some 32
  | .guanase => some 35
  | .organicAcid _ | .bileAcids => some 47
  | .alpIsoenzymes | .amylaseIsoenzymes | .gammaGTIsoenzymes | .ldIsoenzymes | .bicarbonate => some 48
  | .astIsoenzymes | .lipoproteinFraction => some 49
  | .ammonia => some 50
  | .ckIsoenzymes => some 55
  | .cholesterolFraction | .urinarySulfatedBileAcids => some 57
  | .ketoneFractions | .freeFattyAcids => some 59
  | .lcat => some 70
  | .g6pd | .lipoproteinPag | .glycocholicAcid => some 80
  | .ckMbMass => some 90
  | .ldIsoenzyme1 | .totalCarnitine | .freeCarnitine => some 95
  | .alpIsoenzymesAndBap => some 96
  | .bloodGas => some 131

inductive CarnitineIndication where
  | congenitalMetabolicDisorder
  | listedCarnitineDeficiencyRisk
  | other
  deriving DecidableEq, Repr

structure CarnitineContext where
  /-- 通知(17)イ・ウの対象及び診断補助・経過観察の目的を確認した区分。 -/
  indication : Option CarnitineIndication
  followsGuidelines : Option Bool
  enzymaticCycling : Option Bool
  /-- 月1回又は6月1回に対応する、対象期間内の既算定の確認。 -/
  alreadyClaimedThisMonth : Option Bool := none
  sixMonthLimitAllows : Option Bool := none
  deriving DecidableEq, Repr

def CarnitineContext.eligible (c : CarnitineContext) : Option Bool := do
  if !(← c.followsGuidelines) || !(← c.enzymaticCycling) then return false
  match ← c.indication with
  | .congenitalMetabolicDisorder => c.alreadyClaimedThisMonth.map (! ·)
  | .listedCarnitineDeficiencyRisk => c.sixMonthLimitAllows
  | .other => none

structure Context where
  item : Item
  carnitine : Option CarnitineContext := none
  enzymeInhibition : Option Bool := none
  agaroseElectrophoresis : Option Bool := none
  simultaneousInSameSeries : Option Bool := none
  urinaryBileAcidsForHepatobiliaryDiagnosis : Option Bool := none
  urinaryBileAcidsEnzymaticMethod : Option Bool := none
  bloodGasInHouse : Option Bool := none
  deriving DecidableEq, Repr

private def both (first second : Option Bool) : Option Bool := do
  if ← first then second else return false

def eligible (c : Context) : Option Bool :=
  match c.item with
  | .urinarySulfatedBileAcids =>
    both c.urinaryBileAcidsForHepatobiliaryDiagnosis c.urinaryBileAcidsEnzymaticMethod
  | .ldIsoenzyme1 => c.enzymeInhibition
  | .totalCarnitine | .freeCarnitine => c.carnitine.bind CarnitineContext.eligible
  | .alpIsoenzymesAndBap => both c.agaroseElectrophoresis c.simultaneousInSameSeries
  | .bloodGas => c.bloodGasInHouse
  | .apolipoproteins measured => some (!measured.isEmpty)
  | _ => some true

inductive Assessment where
  | payable (points : Nat)
  | ineligible
  | conflictingSelection
  | unresolved
  deriving DecidableEq, Repr

/-- 個別実施料。併施時は下記の組合せ制約も適用する。 -/
def assess (c : Context) : Assessment :=
  match eligible c, c.item.scheduledPoints with
  | some true, some p => .payable p
  | some false, _ => .ineligible
  | _, _ => .unresolved

/-- 組合せを列挙する順序は制約での第一・第二を表す。 -/
inductive Pair where
  | ketones                 -- 9、19
  | bicarbonateAndBloodGas  -- 14、35
  | bileAcids               -- 13、通知(15)の尿中測定
  | carnitineAndD010        -- 23のカルニチン、D010の8
  | bapAndD008              -- 24、D008の27
  | cystatinAndPentosidine -- 29、31
  | inulinAndCreatinineClearance -- 32、1（腎クリアランス目的で血清・尿を同時測定）
  deriving DecidableEq, Repr

inductive Choice where
  | first | second | both
  deriving DecidableEq, Repr

/-- 通知の実施関係を検査の同一日から推定しない。
ケトン体・BAPは併施、尿中測定は同時、重炭酸塩とカルニチンは同一検体での併施を入力する。 -/
def Pair.permits (pair : Pair) (linked : Bool) (choice : Choice) : Prop :=
  linked = true →
    match pair with
    | .ketones | .bicarbonateAndBloodGas => choice = .second
    | .bileAcids | .carnitineAndD010 | .bapAndD008
    | .cystatinAndPentosidine | .inulinAndCreatinineClearance => choice ≠ .both

instance (pair : Pair) (linked : Bool) (choice : Choice) :
    Decidable (pair.permits linked choice) := by
  cases pair <;> unfold Pair.permits <;> infer_instance

/-- 順序は Pair の定義に従う。相手区分の個別評価は該当区分から渡す。 -/
def Pair.assess (pair : Pair) (linked : Option Bool) (choice : Choice)
    (first second : Assessment) : Assessment :=
  match linked with
  | none => .unresolved
  | some linked =>
    if !decide (pair.permits linked choice) then .conflictingSelection else
      match choice, first, second with
      | .first, first, _ => first
      | .second, _, second => second
      | .both, .payable a, .payable b => .payable (a + b)
      | .both, .conflictingSelection, _ | .both, _, .conflictingSelection => .conflictingSelection
      | .both, .ineligible, _ | .both, _, .ineligible => .ineligible
      | .both, _, _ => .unresolved

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def Pair.rule (pair : Pair) : Rule Bool Choice :=
  let (id, location) := match pair with
    | .ketones => ("D007.9-notice", "PDF356頁 D007(9)")
    | .bicarbonateAndBloodGas => ("D007.12-notice", "PDF356頁 D007(12)")
    | .bileAcids => ("D007.15-notice", "PDF356頁 D007(15)")
    | .carnitineAndD010 => ("D007.17e-notice", "PDF357頁 D007(17)エ")
    | .bapAndD008 => ("D007.18-notice", "PDF357頁 D007(18)")
    | .cystatinAndPentosidine => ("D007.23i-25-notice", "PDF357頁 D007(23)イ・(25)")
    | .inulinAndCreatinineClearance => ("D007.26-notice", "PDF357頁 D007(26)")
  ⟨id, notice location, pair.permits⟩

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "2026-10-22取得版",
    location, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

def pointsRule : Rule Context Nat :=
  ⟨"D007.9-24-and-35", primary "PDF179〜180頁 D007の9〜24及び35の血液ガス分析",
    fun c p => c.item ≠ .urinarySulfatedBileAcids → c.item.scheduledPoints = some p⟩

def urinaryReferenceRule : Rule Context Nat :=
  ⟨"D007.15-reference", notice "PDF356頁 D007(15)", fun c p =>
    c.item = .urinarySulfatedBileAcids → Item.scheduledPoints Item.cholesterolFraction = some p⟩

def CarnitineContext.Requirements (c : CarnitineContext) : Prop :=
  c.followsGuidelines = some true ∧ c.enzymaticCycling = some true ∧
    ((c.indication = some .congenitalMetabolicDisorder ∧
      c.alreadyClaimedThisMonth = some false) ∨
     (c.indication = some .listedCarnitineDeficiencyRisk ∧ c.sixMonthLimitAllows = some true))

theorem CarnitineContext.requirements_iff (c : CarnitineContext) :
    c.Requirements ↔ c.eligible = some true := by
  cases c
  rename_i indication guidelines cycling month six
  cases guidelines with
  | none => simp [Requirements, eligible]
  | some g =>
    cases g <;> simp [Requirements, eligible]
    case false => cases cycling <;> simp
    case true =>
      cases cycling with
      | none => simp
      | some e =>
        cases e <;> simp
        case true =>
          cases indication with
          | none => simp
          | some indication =>
            cases indication <;> simp

def urinaryBileAcidMethodRule : Rule Context Unit :=
  ⟨"D007(15)-urinaryBileAcidMethod", notice "PDF356頁 D007(15)", fun c _ =>
    c.item = .urinarySulfatedBileAcids →
    c.urinaryBileAcidsForHepatobiliaryDiagnosis = some true ∧
    c.urinaryBileAcidsEnzymaticMethod = some true⟩

def ldIsoenzymeMethodRule : Rule Context Unit :=
  ⟨"D007(16)-ldIsoenzymeMethod", notice "PDF356頁 D007(16)", fun c _ =>
    c.item = .ldIsoenzyme1 → c.enzymeInhibition = some true⟩

def carnitineRule : Rule Context Unit :=
  ⟨"D007(17)ア〜ウ-carnitine", notice "PDF356〜357頁 D007(17)ア〜ウ", fun c _ =>
    c.item = .totalCarnitine ∨ c.item = .freeCarnitine →
    ∃ details, c.carnitine = some details ∧ details.Requirements⟩

def alpMethodRule : Rule Context Unit :=
  ⟨"D007(18)-alpMethod", notice "PDF357頁 D007(18)", fun c _ =>
    c.item = .alpIsoenzymesAndBap →
    c.agaroseElectrophoresis = some true ∧ c.simultaneousInSameSeries = some true⟩

def apolipoproteinRule : Rule Context Unit :=
  ⟨"D007(10)-apolipoprotein", notice "PDF356頁 D007(10)", fun c _ =>
    ∀ measured, c.item = .apolipoproteins measured → measured ≠ []⟩

def eligibilityRules : List (Rule Context Unit) :=
  [urinaryBileAcidMethodRule, ldIsoenzymeMethodRule, carnitineRule,
    alpMethodRule, apolipoproteinRule]

def Eligibility (c : Context) : Prop :=
  Satisfies eligibilityRules c () ∧
    (c.item = .bloodGas → c.bloodGasInHouse = some true)

private theorem both_iff (a b : Option Bool) :
    both a b = some true ↔ a = some true ∧ b = some true := by
  cases a with
  | none => simp [both]
  | some value => cases value <;> simp [both]

theorem eligibility_iff (c : Context) : Eligibility c ↔ eligible c = some true := by
  cases hi : c.item <;> simp [Eligibility, eligibilityRules, satisfies_cons, satisfies_nil,
    urinaryBileAcidMethodRule, ldIsoenzymeMethodRule, carnitineRule,
    alpMethodRule, apolipoproteinRule, eligible, hi, both_iff]
  all_goals cases hc : c.carnitine <;> simp [CarnitineContext.requirements_iff]

def eligibilityRule : Rule Context Nat :=
  ⟨"D007.eligibility-9-24", notice "PDF356〜357頁 D007(10)・(15)〜(18)",
    fun c _ => c.item ≠ .bloodGas → Eligibility c⟩

def bloodGasRule : Rule Context Nat :=
  ⟨"D007.35-note", primary "PDF180頁 D007の35の注",
    fun c _ => c.item = .bloodGas → c.bloodGasInHouse = some true⟩

def individualRules := [pointsRule, urinaryReferenceRule, eligibilityRule, bloodGasRule]

theorem scheduled_of_rules (c : Context) (p : Nat) (h : Satisfies individualRules c p) :
    c.item.scheduledPoints = some p := by
  by_cases item : c.item = .urinarySulfatedBileAcids
  · have hp := h urinaryReferenceRule (by simp [individualRules])
    have ref := hp item
    simpa [item, Item.scheduledPoints] using ref
  · exact h pointsRule (by simp [individualRules]) item

theorem payable_iff (c : Context) (p : Nat) :
    Satisfies individualRules c p ↔ assess c = .payable p := by
  have hs : Satisfies individualRules c p ↔
      Eligibility c ∧ c.item.scheduledPoints = some p := by
    constructor
    · intro h
      refine ⟨?_, scheduled_of_rules c p h⟩
      by_cases item : c.item = .bloodGas
      · have location := h bloodGasRule (by simp [individualRules]) item
        simpa [eligibility_iff, eligible, item] using location
      · exact h eligibilityRule (by simp [individualRules]) item
    · rintro ⟨he, hp⟩
      simp only [individualRules, satisfies_cons, satisfies_nil]
      refine ⟨fun _ => hp, ?_, fun _ => he, ?_, trivial⟩
      · intro item
        simpa [item, Item.scheduledPoints] using hp
      · intro item
        simpa [eligibility_iff, eligible, item] using he
  rw [hs, eligibility_iff]
  cases he : eligible c with
  | none => simp [assess, he]
  | some value => cases value <;> cases hp : c.item.scheduledPoints <;> simp [assess, he, hp]

theorem determines_individual (c : Context) (p : Nat) (h : assess c = .payable p) :
    DeterminesAt individualRules c := by
  refine ⟨⟨p, (payable_iff c p).mpr h⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj ((scheduled_of_rules c a ha).symm.trans (scheduled_of_rules c b hb))

theorem determines_individual_on :
    DeterminesOn (fun c => Eligibility c ∧ ∃ p, c.item.scheduledPoints = some p)
      individualRules := by
  rintro c ⟨he, p, hp⟩
  exact determines_individual c p (by simp [assess, (eligibility_iff c).mp he, hp])

example : [[], [.aI], [.aI, .b], [.aI, .b, .e], [.aI, .aI]].map apolipoproteinPoints =
    [none, some 31, some 62, some 94, some 31] := by decide

example : Pair.ketones.rule.holds true .second := by
  intro _
  rfl

example : ¬ Pair.bicarbonateAndBloodGas.rule.holds true .both := by
  intro h
  have bad := h rfl
  cases bad

example : assess { item := .bloodGas, bloodGasInHouse := some false } = .ineligible := by decide
example : Pair.ketones.assess (some true) .second
    (assess { item := .ketoneBodies }) (assess { item := .ketoneFractions }) = .payable 59 := by decide
example : Pair.ketones.assess (some false) .both
    (assess { item := .ketoneBodies }) (assess { item := .ketoneFractions }) = .payable 89 := by decide
example : Pair.bicarbonateAndBloodGas.assess (some true) .both
    (assess { item := .bicarbonate }) (assess { item := .bloodGas, bloodGasInHouse := some true }) =
    .conflictingSelection := by decide
example : assess { item := .totalCarnitine } = .unresolved := by decide
example : assess {
    item := .totalCarnitine
    carnitine := some ⟨some .congenitalMetabolicDisorder, some true, some true, some false, none⟩ } =
    .payable 95 := by decide

example : assess {
    item := .freeCarnitine
    carnitine := some ⟨some .listedCarnitineDeficiencyRisk, some true, some true, none, some false⟩ } =
    .ineligible := by decide

example : Eligibility { item := .apolipoproteins [.aI, .aII, .b] } ∧
    ∃ p, Item.scheduledPoints (.apolipoproteins [.aI, .aII, .b]) = some p :=
  ⟨(eligibility_iff _).mpr rfl, 94, rfl⟩

example : ¬ Eligibility { item := .bloodGas, bloodGasInHouse := some false } := by
  rw [eligibility_iff]
  decide

example : DeterminesAt individualRules { item := .apolipoproteins [.aI, .aII, .b] } :=
  determines_individual _ 94 rfl

end Sanri.MedicalFee.BloodChemistryFurther
