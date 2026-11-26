import Sanri.BloodChemistryFurther

namespace Sanri.MedicalFee.BloodChemistryAdditional

open Sanri.Logic
open BloodChemistryFurther (Assessment)

/-! D007の25〜34と、通知(21)の組合せが参照する38のSP-D。
一患者の外来実施を扱う。暦上の間隔は当該検査の履歴から確認した結果を受け取る。 -/

inductive Item where
  | ferritinSemiquantitative | ferritinQuantitative | ethanol | lipoproteinA
  | heparin | kl6 | troponinI | troponinTQualitative | troponinTQuantitative
  | aluminium | cystatinC | vitaminD25 | pentosidine | inulin | lipoproteinHplc
  | surfactantProteinA | galactose | surfactantProteinD
  deriving DecidableEq, Repr

def Item.points : Item → Nat
  | .ferritinSemiquantitative | .ferritinQuantitative => 102
  | .ethanol => 105
  | .lipoproteinA => 107
  | .heparin | .kl6 => 108
  | .troponinI | .troponinTQualitative | .troponinTQuantitative | .aluminium | .cystatinC => 109
  | .vitaminD25 => 117
  | .pentosidine => 118
  | .inulin => 120
  | .lipoproteinHplc => 129
  | .surfactantProteinA | .galactose => 130
  | .surfactantProteinD => 136

inductive Method where
  | eia | eclia | clia | cleia | latexAgglutinationTurbidimetry | latexImmunoturbidimetry
  | colloidalGoldAgglutination | nephelometry | other
  deriving DecidableEq, Repr

inductive VitaminDIndication where
  | primaryOsteoporosisTreatmentSelection
  | deficiencyDiagnosis
  | deficiencyTreatment
  | other
  deriving DecidableEq, Repr

structure Context where
  item : Item
  method : Option Method := none
  suspectedRenalDeclineFromBunOrCreatinine : Option Bool := none
  dueToDiabeticNephropathy : Option Bool := none
  threeMonthLimitAllows : Option Bool := none
  sixMonthLimitAllows : Option Bool := none
  /-- 同一患者の1月以内の測定群のうち、今回が第1回か。暦月集計とは別。 -/
  heparinFirstInWindow : Option Bool := none
  /-- 欠乏症経路はビタミンD欠乏性くる病又は骨軟化症について確認する。 -/
  vitaminDIndication : Option VitaminDIndication := none
  followsVitaminDGuidelines : Option Bool := none
  vitaminDFirstForIndication : Option Bool := none
  deriving DecidableEq, Repr

private def requires (condition next : Option Bool) : Option Bool := do
  if ← condition then next else return false

private def vitaminDEligible (c : Context) : Option Bool := do
  if !([.eclia, .clia, .cleia] : List Method).contains (← c.method) then return false
  match ← c.vitaminDIndication with
  | .primaryOsteoporosisTreatmentSelection =>
    requires c.followsVitaminDGuidelines c.vitaminDFirstForIndication
  | .deficiencyDiagnosis => c.vitaminDFirstForIndication
  | .deficiencyTreatment => c.threeMonthLimitAllows
  | .other => some false

def eligible (c : Context) : Option Bool :=
  match c.item with
  | .lipoproteinA => c.threeMonthLimitAllows
  | .heparin => c.heparinFirstInWindow
  | .kl6 => c.method.map ([.eia, .eclia, .latexAgglutinationTurbidimetry].contains ·)
  | .surfactantProteinA => c.method.map (· == .eia)
  | .surfactantProteinD => c.method.map ([.eia, .latexImmunoturbidimetry].contains ·)
  | .cystatinC => requires
    (c.method.map ([.eia, .latexAgglutinationTurbidimetry, .colloidalGoldAgglutination, .nephelometry].contains ·))
    (requires c.suspectedRenalDeclineFromBunOrCreatinine c.threeMonthLimitAllows)
  | .vitaminD25 => vitaminDEligible c
  | .pentosidine => requires c.suspectedRenalDeclineFromBunOrCreatinine
    (requires (c.dueToDiabeticNephropathy.map (! ·)) c.threeMonthLimitAllows)
  | .inulin => requires c.suspectedRenalDeclineFromBunOrCreatinine c.sixMonthLimitAllows
  | _ => some true

def assess (c : Context) : Assessment :=
  match eligible c with
  | some true => .payable c.item.points
  | some false => .ineligible
  | none => .unresolved

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def pointsRule : Rule Context Nat :=
  ⟨"D007.25-34-and-SP-D",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "2026-10-22取得版",
      "PDF180頁 D007の25〜34及び38のSP-D", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun c p => p = c.item.points⟩

private def MethodIn (method : Option Method) (allowed : List Method) : Prop :=
  ∃ m, method = some m ∧ m ∈ allowed

private theorem methodIn_iff (method : Option Method) (allowed : List Method) :
    MethodIn method allowed ↔ method.map (allowed.contains ·) = some true := by
  cases method <;> simp [MethodIn]

private theorem requires_iff (a b : Option Bool) :
    requires a b = some true ↔ a = some true ∧ b = some true := by
  cases a with
  | none => simp [requires]
  | some value => cases value <;> simp [requires]

def VitaminDRequirements (c : Context) : Prop :=
  MethodIn c.method [.eclia, .clia, .cleia] ∧
  ((c.vitaminDIndication = some .primaryOsteoporosisTreatmentSelection ∧
    c.followsVitaminDGuidelines = some true ∧ c.vitaminDFirstForIndication = some true) ∨
   (c.vitaminDIndication = some .deficiencyDiagnosis ∧
    c.vitaminDFirstForIndication = some true) ∨
   (c.vitaminDIndication = some .deficiencyTreatment ∧ c.threeMonthLimitAllows = some true))

private theorem vitaminD_iff (c : Context) :
    VitaminDRequirements c ↔ vitaminDEligible c = some true := by
  cases hm : c.method with
  | none => simp [VitaminDRequirements, MethodIn, vitaminDEligible, hm]
  | some m =>
    cases hi : c.vitaminDIndication with
    | none => cases m <;> simp [VitaminDRequirements, MethodIn, vitaminDEligible, hm, hi]
    | some indication =>
      cases indication <;> cases m <;>
        simp [VitaminDRequirements, MethodIn, vitaminDEligible, hm, hi, requires_iff]

def lipoproteinIntervalRule : Rule Context Unit :=
  ⟨"D007(19)-lipoproteinInterval", notice "PDF357頁 D007(19)", fun c _ =>
    c.item = .lipoproteinA → c.threeMonthLimitAllows = some true⟩

def heparinWindowRule : Rule Context Unit :=
  ⟨"D007(20)-heparinWindow", notice "PDF357頁 D007(20)", fun c _ =>
    c.item = .heparin → c.heparinFirstInWindow = some true⟩

def lungMarkerMethodsRule : Rule Context Unit :=
  ⟨"D007(21)-lungMarkerMethods", notice "PDF357頁 D007(21)", fun c _ =>
    (c.item = .kl6 → MethodIn c.method [.eia, .eclia, .latexAgglutinationTurbidimetry]) ∧
      (c.item = .surfactantProteinA → c.method = some .eia) ∧
      (c.item = .surfactantProteinD → MethodIn c.method [.eia, .latexImmunoturbidimetry])⟩

def cystatinMethodAndIntervalRule : Rule Context Unit :=
  ⟨"D007(23)ア-cystatinMethodAndInterval", notice "PDF357頁 D007(23)ア", fun c _ =>
    c.item = .cystatinC →
    MethodIn c.method [.eia, .latexAgglutinationTurbidimetry, .colloidalGoldAgglutination,
      .nephelometry] ∧ c.suspectedRenalDeclineFromBunOrCreatinine = some true ∧
      c.threeMonthLimitAllows = some true⟩

def vitaminDRule : Rule Context Unit :=
  ⟨"D007(24)-vitaminD", notice "PDF357頁 D007(24)", fun c _ =>
    c.item = .vitaminD25 → VitaminDRequirements c⟩

def pentosidineRule : Rule Context Unit :=
  ⟨"D007(25)-pentosidine", notice "PDF357頁 D007(25)", fun c _ =>
    c.item = .pentosidine → c.suspectedRenalDeclineFromBunOrCreatinine = some true ∧
    c.dueToDiabeticNephropathy = some false ∧ c.threeMonthLimitAllows = some true⟩

def inulinRule : Rule Context Unit :=
  ⟨"D007(26)-inulin", notice "PDF357頁 D007(26)", fun c _ =>
    c.item = .inulin → c.suspectedRenalDeclineFromBunOrCreatinine = some true ∧
    c.sixMonthLimitAllows = some true⟩

def eligibilityRules : List (Rule Context Unit) :=
  [lipoproteinIntervalRule, heparinWindowRule, lungMarkerMethodsRule,
    cystatinMethodAndIntervalRule, vitaminDRule, pentosidineRule,
    inulinRule]

def Eligibility (c : Context) : Prop :=
  Satisfies eligibilityRules c ()

theorem eligibility_iff (c : Context) : Eligibility c ↔ eligible c = some true := by
  cases hi : c.item <;>
    simp [Eligibility, eligibilityRules, satisfies_cons, satisfies_nil,
    lipoproteinIntervalRule, heparinWindowRule, lungMarkerMethodsRule,
    cystatinMethodAndIntervalRule, vitaminDRule, pentosidineRule, inulinRule, eligible, hi, methodIn_iff, vitaminD_iff, requires_iff]

def eligibilityRule : Rule Context Nat :=
  ⟨"D007.19-26-notice", notice "PDF357頁 D007(19)〜(21)・(23)〜(26)の個別条件",
    fun c _ => Eligibility c⟩

def individualRules := [pointsRule, eligibilityRule]

theorem determines_individual (c : Context) (h : eligible c = some true) :
    DeterminesAt individualRules c := by
  refine ⟨⟨c.item.points, ?_⟩, ?_⟩
  · simp only [individualRules, satisfies_cons, satisfies_nil]
    exact ⟨rfl, (eligibility_iff c).mpr h, trivial⟩
  · intro a b ha hb
    exact (ha pointsRule (by simp [individualRules])).trans (hb pointsRule (by simp [individualRules])).symm

theorem payable_iff (c : Context) (p : Nat) :
    Satisfies individualRules c p ↔ assess c = .payable p := by
  simp only [individualRules, satisfies_cons, satisfies_nil, and_true,
    pointsRule, eligibilityRule, eligibility_iff]
  cases h : eligible c with
  | none => simp [assess, h]
  | some value => cases value <;> simp [assess, h, eq_comm]

theorem determines_individual_on : DeterminesOn Eligibility individualRules := by
  intro c h
  exact determines_individual c ((eligibility_iff c).mp h)

/-- (21)の併施群、又は(22)の同一暦月のトロポニンI・Tの実施群を入力する。 -/
inductive Group where
  | lungMarkers
  | monthlyTroponins
  deriving DecidableEq, Repr

def Group.items : Group → List Item
  | .lungMarkers => [.kl6, .surfactantProteinA, .surfactantProteinD]
  | .monthlyTroponins => [.troponinI, .troponinTQualitative, .troponinTQuantitative]

def Group.restricts (group : Group) (performed : List Item) : Bool :=
  match group with
  | .lungMarkers => 2 ≤ ((performed.filter group.items.contains).eraseDups.length)
  | .monthlyTroponins => performed.contains .troponinI &&
      (performed.contains .troponinTQualitative || performed.contains .troponinTQuantitative)

def Group.rule (group : Group) : Rule (List Item) (List Item) :=
  let (id, location) := match group with
    | .lungMarkers => ("D007.21-notice", "PDF357頁 D007(21)")
    | .monthlyTroponins => ("D007.22-notice", "PDF357頁 D007(22)")
  ⟨id, notice location, fun performed selected =>
    group.restricts performed = true →
      ∃ item, item ∈ performed ∧ item ∈ group.items ∧ selected = [item]⟩

/-- 主たる検査の選択を固定した併施群の点数。選択した実施の個別条件も確認する。 -/
def Group.assessPrincipal (group : Group) (performed : Option (List Item))
    (principal : Option Context) : Assessment :=
  match performed, principal with
  | some performed, some principal =>
    if !group.restricts performed then .unresolved
    else if group.items.contains principal.item && performed.contains principal.item then assess principal
    else .conflictingSelection
  | _, _ => .unresolved

private def renal : Context :=
  { item := .cystatinC, method := some .nephelometry,
    suspectedRenalDeclineFromBunOrCreatinine := some true, threeMonthLimitAllows := some true }

example : DeterminesAt individualRules renal := determines_individual _ rfl
example : assess renal = .payable 109 := by decide
example : assess { renal with threeMonthLimitAllows := none } = .unresolved := by decide
example : assess { renal with item := .pentosidine, dueToDiabeticNephropathy := some true } =
    .ineligible := by decide
example : assess { item := .heparin, heparinFirstInWindow := some false } = .ineligible := by decide

example : assess {
    item := .vitaminD25
    method := some .cleia
    vitaminDIndication := some .deficiencyTreatment
    threeMonthLimitAllows := some true } = .payable 117 := by decide

example : assess {
    item := .vitaminD25
    method := some .eclia
    vitaminDIndication := some .primaryOsteoporosisTreatmentSelection
    vitaminDFirstForIndication := some true } = .unresolved := by decide

example : Group.lungMarkers.assessPrincipal (some [.kl6, .surfactantProteinD])
    (some { item := .surfactantProteinD, method := some .latexImmunoturbidimetry }) =
    .payable 136 := by decide

example : Group.monthlyTroponins.assessPrincipal (some [.troponinI, .troponinTQuantitative])
    (some { item := .troponinTQuantitative }) = .payable 109 := by decide
example : ¬ Group.monthlyTroponins.rule.holds [.troponinI, .troponinTQuantitative]
    [.troponinI, .troponinTQuantitative] := by
  intro h
  obtain ⟨_, _, _, eq⟩ := h rfl
  cases eq

example : BloodChemistryFurther.Pair.cystatinAndPentosidine.assess (some true) .both
    (assess renal) (assess { renal with item := .pentosidine, dueToDiabeticNephropathy := some false }) =
    .conflictingSelection := by decide

end Sanri.MedicalFee.BloodChemistryAdditional
