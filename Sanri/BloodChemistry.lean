import Sanri.Logic
import Sanri.D007

namespace Sanri.MedicalFee.BloodChemistry

open Sanri.Logic

/-! D007の1〜8の外来実施料。一回の採血に由来する結果を評価する。
同時・併測の事実は採血IDから導かず、組合せごとに入力する。
別採血にまたがる同時測定、同一採血内の同じ検査の反復、入院時初回加算は別の課題。 -/

abbrev Item := D007.ScopedItem .draw

namespace Item
export D007.ScopedItem (
  totalBilirubin directOrConjugatedBilirubin totalProtein albumin bun
  creatinine uricAcid alp cholinesterase gammaGT
  triglycerides sodium chloride potassium calcium
  magnesium creatine glucose ld amylase
  lap ck aldolase freeCholesterol iron
  bloodKetoneGlucoseChloride uibcColorimetric tibcColorimetric phospholipids hdlCholesterol
  inorganicPhosphorus phosphate totalCholesterol ast alt
  ldlCholesterol proteinFractionation copper lipase ionizedCalcium
  manganese)
end Item

def Item.number (item : Item) : Nat := D007.ScopedItem.number item

def Item.points (item : Item) : Nat :=
  match item.number with
  | 1 => 11
  | 2 => 15
  | 3 => 17
  | 4 => 18
  | 5 => 23
  | 6 => 24
  | 7 => 26
  | _ => 27

structure ManganeseContext where
  reducedBiliaryExcretion : Bool
  /-- 高カロリー静脈栄養の継続期間を暦で確認した結果。 -/
  atLeastOneMonth : Option Bool
  atLeastTwoWeeks : Option Bool
  /-- 当該患者の3月に1回の算定間隔を満たすことを履歴から確認した結果。 -/
  intervalAllows : Option Bool
  deriving DecidableEq, Repr

def ManganeseContext.eligible (c : ManganeseContext) : Option Bool := do
  let duration ← if c.reducedBiliaryExcretion then c.atLeastTwoWeeks else c.atLeastOneMonth
  if duration then c.intervalAllows else some false

structure Combination where
  /-- 対象検査を同時又は併せて測定したこと。 -/
  together : Option Bool := none
  /-- 制限の対象になった場合に算定から外す1項目。 -/
  excluded : Option Item := none
  deriving DecidableEq, Repr

structure Draw where
  performed : List Item
  albuminByModifiedBCP : Option Bool := none
  creatinineByJaffe : Option Bool := none
  /-- 本文の1が掲げる試験紙法・アンプル法・固定化酵素電極のいずれかに該当。 -/
  ketoneGlucoseChlorideMethodAllowed : Option Bool := none
  manganese : Option ManganeseContext := none
  calcium : Combination := {}
  ironBinding : Combination := {}
  cholesterol : Combination := {}
  protein : Combination := {}
  deriving DecidableEq, Repr

def Draw.eligible (c : Draw) : Item → Option Bool
  | .albumin => c.albuminByModifiedBCP
  | .creatinine => c.creatinineByJaffe.map (! ·)
  | .bloodKetoneGlucoseChloride => c.ketoneGlucoseChlorideMethodAllowed
  | .manganese => c.manganese.bind ManganeseContext.eligible
  | _ => some true

/-- 同点で一項目にまとめる二組の代表元。 -/
def Item.billingItem : Item → Item
  | .chloride => .sodium
  | .phosphate => .inorganicPhosphorus
  | item => item

/-- 全項目がそろい、同時・併測の条件を満たす場合に選択を適用する。 -/
def Combination.apply (choice : Combination) (group items : List Item) : Option (List Item) := do
  if !group.all items.contains then return items
  if !(← choice.together) then return items
  let excluded ← choice.excluded
  if group.contains excluded then return items.filter (· != excluded) else none

private def calciumGroup : List Item := [.calcium, .ionizedCalcium]
private def ironBindingGroup : List Item := [.uibcColorimetric, .tibcColorimetric]
private def cholesterolGroup : List Item := [.hdlCholesterol, .totalCholesterol, .ldlCholesterol]
private def proteinGroup : List Item := [.proteinFractionation, .totalProtein, .albumin]

/-- 組合せが既知の一採血。none は情報不足、未対応の反復、又は不適切な選択。 -/
def billableItems (c : Draw) : Option (List Item) := do
  if c.performed.eraseDups != c.performed then none else
    let items ← c.performed.filterM c.eligible
    let items ← c.calcium.apply calciumGroup items
    let items ← c.ironBinding.apply ironBindingGroup items
    let items ← c.cholesterol.apply cholesterolGroup items
    let items ← c.protein.apply proteinGroup items
    return (items.map Item.billingItem).eraseDups

/-- 適格性と組合せを解決済みの、同一採血の算定項目に適用する。 -/
def pointsForItems (items : List Item) : Nat :=
  if 10 ≤ items.length then 103
  else if 8 ≤ items.length then 99
  else if 5 ≤ items.length then 93
  else (items.map Item.points).sum

def points (c : Draw) : Option Nat :=
  (billableItems c).map pointsForItems

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def ManganeseContext.Requirements (c : ManganeseContext) : Prop :=
  (c.reducedBiliaryExcretion = true → c.atLeastTwoWeeks = some true) ∧
  (c.reducedBiliaryExcretion = false → c.atLeastOneMonth = some true) ∧
  c.intervalAllows = some true

theorem ManganeseContext.requirements_iff (c : ManganeseContext) :
    c.Requirements ↔ c.eligible = some true := by
  cases hb : c.reducedBiliaryExcretion <;>
    simp [Requirements, eligible, hb]
  · cases hd : c.atLeastOneMonth with
    | none => simp
    | some duration => cases duration <;> simp
  · cases hd : c.atLeastTwoWeeks with
    | none => simp
    | some duration => cases duration <;> simp

private def methodsSource : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "2026-10-22取得版",
    "PDF179頁 D007の1", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

def albuminRule : Rule Draw Item :=
  ⟨"D007.1-albumin-method", methodsSource,
    fun c item => item = .albumin → c.albuminByModifiedBCP = some true⟩

def creatinineRule : Rule Draw Item :=
  ⟨"D007.4", notice "PDF356頁 D007(4)",
    fun c item => item = .creatinine → c.creatinineByJaffe = some false⟩

def ketoneGlucoseChlorideRule : Rule Draw Item :=
  ⟨"D007.1-ketone-glucose-chloride-method", methodsSource, fun c item =>
    item = .bloodKetoneGlucoseChloride → c.ketoneGlucoseChlorideMethodAllowed = some true⟩

def manganeseRule : Rule Draw Item :=
  ⟨"D007.8", notice "PDF356頁 D007(8)", fun c item =>
    item = .manganese → ∃ details, c.manganese = some details ∧ details.Requirements⟩

def eligibilityRules := [albuminRule, creatinineRule, ketoneGlucoseChlorideRule, manganeseRule]

theorem eligible_iff (c : Draw) (item : Item) :
    Satisfies eligibilityRules c item ↔ c.eligible item = some true := by
  cases item <;> simp [eligibilityRules, satisfies_cons, satisfies_nil,
    albuminRule, creatinineRule, ketoneGlucoseChlorideRule, manganeseRule, Draw.eligible]
  · cases c.manganese <;> simp [ManganeseContext.requirements_iff]

/-- 組合せ選択後の一採血で、二組それぞれに算定対象があるかを表す。 -/
def sodiumChlorideRule : Rule (List Item) (Bool × Bool) :=
  ⟨"D007.1-notice", notice "PDF355頁 D007(1)", fun items presence =>
    presence.1 = true ↔ .sodium ∈ items ∨ .chloride ∈ items⟩

def phosphorusPhosphateRule : Rule (List Item) (Bool × Bool) :=
  ⟨"D007.6-notice", notice "PDF356頁 D007(6)", fun items presence =>
    presence.2 = true ↔ .inorganicPhosphorus ∈ items ∨ .phosphate ∈ items⟩

def mergedItemRules := [sodiumChlorideRule, phosphorusPhosphateRule]

/-- 既存の代表元への変換と重複除去が、各組の有無を保存する。 -/
theorem mergedItemRules_iff (items : List Item) (presence : Bool × Bool) :
    Satisfies mergedItemRules items presence ↔
      presence = (((items.map Item.billingItem).eraseDups).contains .sodium,
        ((items.map Item.billingItem).eraseDups).contains .inorganicPhosphorus) := by
  have hs (item : Item) : item.billingItem = .sodium ↔ item = .sodium ∨ item = .chloride := by
    cases item <;> decide
  have hp (item : Item) :
      item.billingItem = .inorganicPhosphorus ↔ item = .inorganicPhosphorus ∨ item = .phosphate := by
    cases item <;> decide
  have sodium : .sodium ∈ (items.map Item.billingItem).eraseDups ↔
      .sodium ∈ items ∨ .chloride ∈ items := by
    simp [List.mem_map, hs, and_or_left, exists_or]
  have phosphorus : .inorganicPhosphorus ∈ (items.map Item.billingItem).eraseDups ↔
      .inorganicPhosphorus ∈ items ∨ .phosphate ∈ items := by
    simp [List.mem_map, hp, and_or_left, exists_or]
  rcases presence with ⟨s, p⟩
  simp only [mergedItemRules, satisfies_cons, satisfies_nil, sodiumChlorideRule,
    phosphorusPhosphateRule, and_true, Prod.mk.injEq, ← sodium, ← phosphorus]
  simp only [List.contains_eq_mem]
  cases s <;> cases p <;> simp

theorem determines_merged_items_on : DeterminesOn (fun _ => True) mergedItemRules := by
  intro items _
  refine ⟨⟨_, (mergedItemRules_iff items _).mpr rfl⟩, ?_⟩
  intro a b ha hb
  exact ((mergedItemRules_iff items a).mp ha).trans ((mergedItemRules_iff items b).mp hb).symm

/-- 算定対象に整理済みの項目から、出典本文の各点数帯を関係として表す。 -/
def pointsRule : Rule (List Item) Nat :=
  ⟨"D007.1-8-note",
   ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "2026-10-22取得版",
     "PDF179頁 D007の1〜8・181頁 D007注イ〜ハ", .checkedAgainstSource,
     some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
   fun items p =>
     (items.length < 5 → p = (items.map Item.points).sum) ∧
     (5 ≤ items.length ∧ items.length < 8 → p = 93) ∧
     (8 ≤ items.length ∧ items.length < 10 → p = 99) ∧
     (10 ≤ items.length → p = 103)⟩

theorem pointsRule_iff (items : List Item) (p : Nat) :
    pointsRule.holds items p ↔ p = pointsForItems items := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  unfold pointsForItems
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem determines_points (items : List Item) : DeterminesAt [pointsRule] items := by
  refine ⟨⟨pointsForItems items, ?_⟩, ?_⟩
  · exact (satisfies_cons _ _ _ _).2 ⟨(pointsRule_iff _ _).2 rfl, satisfies_nil _ _⟩
  · intro a b ha hb
    exact ((pointsRule_iff _ _).1 (ha pointsRule (by simp))).trans
      (((pointsRule_iff _ _).1 (hb pointsRule (by simp))).symm)

theorem determines_points_on : DeterminesOn (fun _ => True) [pointsRule] :=
  fun items _ => determines_points items

/-- 同時・併測の事実を固定した場合に、組合せから算定する件数。 -/
private def pairedRule (id location : String) (group : List Item) (count : Nat) :
    Rule (List Item) (List Item) :=
  ⟨id, notice location, fun eligibleItems charged =>
    group.all eligibleItems.contains = true → (charged.filter group.contains).length = count⟩

def calciumRule := pairedRule "D007.2" "PDF355頁 D007(2)" calciumGroup 1
def ironBindingRule := pairedRule "D007.3" "PDF355頁 D007(3)" ironBindingGroup 1
def cholesterolRule := pairedRule "D007.5" "PDF356頁 D007(5)" cholesterolGroup 2
def proteinRule := pairedRule "D007.7" "PDF356頁 D007(7)" proteinGroup 2

/-- 結果を未確認とする場合と、個別要件の不成立が確定する場合を区別する。 -/
private def Rejected (c : Draw) : Item → Prop
  | .albumin => c.albuminByModifiedBCP = some false
  | .creatinine => c.creatinineByJaffe = some true
  | .bloodKetoneGlucoseChloride => c.ketoneGlucoseChlorideMethodAllowed = some false
  | .manganese => ∃ details, c.manganese = some details ∧
      let duration := if details.reducedBiliaryExcretion then
        details.atLeastTwoWeeks else details.atLeastOneMonth
      duration = some false ∨ duration = some true ∧ details.intervalAllows = some false
  | _ => False

private theorem rejected_iff (c : Draw) (item : Item) :
    Rejected c item ↔ c.eligible item = some false := by
  cases item <;> simp [Rejected, Draw.eligible]
  cases hc : c.manganese with
  | none => simp
  | some details =>
    simp only [Option.some.injEq, exists_eq_left', Option.bind_some]
    cases hb : details.reducedBiliaryExcretion
    · cases hd : details.atLeastOneMonth with
      | none => simp [ManganeseContext.eligible, hb, hd]
      | some allows => cases allows <;> simp [ManganeseContext.eligible, hb, hd]
    · cases hd : details.atLeastTwoWeeks with
      | none => simp [ManganeseContext.eligible, hb, hd]
      | some allows => cases allows <;> simp [ManganeseContext.eligible, hb, hd]

/-- 適格性が未確認の項目があれば、この採血の選別結果は確定しない。 -/
private def Classified (c : Draw) : List Item → List Item → Prop
  | [], selected => selected = []
  | item :: rest, selected =>
      (∃ tail, Satisfies eligibilityRules c item ∧ Classified c rest tail ∧
        selected = item :: tail) ∨
      (Rejected c item ∧ Classified c rest selected)

private theorem classified_iff (c : Draw) (performed selected : List Item) :
    Classified c performed selected ↔ performed.filterM c.eligible = some selected := by
  induction performed generalizing selected with
  | nil => change selected = [] ↔ some [] = some selected
           simp [eq_comm]
  | cons item rest ih =>
    simp only [Classified, eligible_iff, rejected_iff, ih, option_filterM_cons, Option.bind_eq_some_iff,
      Option.map_eq_some_iff]
    cases c.eligible item with
    | none => simp
    | some b => cases b <;> simp [eq_comm]

/-- 同時・併測の条件と、入力で指定された除外項目を一段について記述する。
対象がそろわない場合は、同時・併測の入力を要求しない。 -/
private def combinationSelectionRule (base : Rule (List Item) (List Item)) (group : List Item) :
    Rule (Combination × List Item) (List Item) :=
  ⟨base.id, base.source, fun (choice, items) selected =>
    ((group.all items.contains = false ∨ choice.together = some false) ∧ selected = items) ∨
    (group.all items.contains = true ∧ choice.together = some true ∧
      ∃ excluded, choice.excluded = some excluded ∧ excluded ∈ group ∧
        selected = items.filter (· != excluded))⟩

private theorem combinationSelection_iff (base : Rule (List Item) (List Item))
    (group : List Item) (choice : Combination) (items selected : List Item) :
    (combinationSelectionRule base group).holds (choice, items) selected ↔
      choice.apply group items = some selected := by
  unfold combinationSelectionRule
  dsimp only
  cases hg : group.all items.contains with
  | false => simp [Combination.apply, hg, eq_comm (a := selected)]
  | true =>
    cases ht : choice.together with
    | none => simp [Combination.apply, hg, ht]
    | some together =>
      cases together
      · simp [Combination.apply, hg, ht, eq_comm (a := selected)]
      · cases he : choice.excluded with
        | none => simp [Combination.apply, hg, ht, he]
        | some excluded =>
          by_cases hm : excluded ∈ group <;>
            simp [Combination.apply, hg, ht, he, hm, List.contains_eq_mem, eq_comm (a := selected)]

/-- 既存の同一採血モデルの制約群。反復なしと代表元への正規化はモデルの条件。
各段は明示された組合せ入力を用い、入力から選択を作らない。 -/
def DrawPoints (c : Draw) (p : Nat) : Prop :=
  c.performed.eraseDups = c.performed ∧
    ∃ eligible calcium iron cholesterol protein,
      Classified c c.performed eligible ∧
      (combinationSelectionRule calciumRule calciumGroup).holds (c.calcium, eligible) calcium ∧
      (combinationSelectionRule ironBindingRule ironBindingGroup).holds (c.ironBinding, calcium) iron ∧
      (combinationSelectionRule cholesterolRule cholesterolGroup).holds (c.cholesterol, iron) cholesterol ∧
      (combinationSelectionRule proteinRule proteinGroup).holds (c.protein, cholesterol) protein ∧
      pointsRule.holds ((protein.map Item.billingItem).eraseDups) p

/-- 一採血での選別・固定した組合せ選択・合算点数についての健全性と完全性。 -/
theorem drawPoints_iff (c : Draw) (p : Nat) : DrawPoints c p ↔ points c = some p := by
  simp only [DrawPoints, classified_iff, combinationSelection_iff, pointsRule_iff,
    points, billableItems, bne_iff_ne, ne_eq]
  by_cases h : c.performed.eraseDups = c.performed
  · simp only [h, not_true_eq_false, ite_false, true_and]
    change _ ↔ Option.map pointsForItems
      (((c.performed.filterM c.eligible).bind fun eligible =>
        (c.calcium.apply calciumGroup eligible).bind fun calcium =>
        (c.ironBinding.apply ironBindingGroup calcium).bind fun iron =>
        (c.cholesterol.apply cholesterolGroup iron).bind fun cholesterol =>
        (c.protein.apply proteinGroup cholesterol).bind fun protein =>
        some (protein.map Item.billingItem).eraseDups)) = some p
    simp only [Option.map_eq_bind, Option.bind_eq_some_iff, Function.comp_apply, Option.some.injEq]
    constructor
    · rintro ⟨eligible, calcium, iron, cholesterol, protein, h₁, h₂, h₃, h₄, h₅, hp⟩
      exact ⟨_, ⟨eligible, h₁, calcium, h₂, iron, h₃, cholesterol, h₄, protein, h₅, rfl⟩, hp.symm⟩
    · rintro ⟨_, ⟨eligible, h₁, calcium, h₂, iron, h₃, cholesterol, h₄, protein, h₅, rfl⟩, hp⟩
      exact ⟨eligible, calcium, iron, cholesterol, protein, h₁, h₂, h₃, h₄, h₅, hp.symm⟩
  · simp [h]

example : DrawPoints
    { performed := [.calcium, .ionizedCalcium], calcium := ⟨some true, some .calcium⟩ }
    26 := by
  rw [drawPoints_iff]
  decide

example : ¬ ∃ p, DrawPoints { performed := [.calcium, .ionizedCalcium] } p := by
  simp only [drawPoints_iff]
  have h : points { performed := [.calcium, .ionizedCalcium] } = none := by decide
  simp [h]

-- 両定理の入力範囲は全リスト。採血全体の判定には別途、選択情報が必要。
example : DeterminesAt mergedItemRules [.sodium, .chloride] :=
  determines_merged_items_on _ trivial

example : DeterminesAt [pointsRule] [.sodium] ∧ pointsRule.holds [.sodium] 11 :=
  ⟨determines_points_on _ trivial, (pointsRule_iff _ _).mpr rfl⟩

private def ten : List Item :=
  [.bun, .uricAcid, .ast, .alt, .totalProtein, .gammaGT, .potassium, .lipase, .copper, .glucose]

example : (List.range 7).map (fun n => points { performed := ten.take (n + 4) }) =
    [some 56, some 93, some 93, some 93, some 99, some 99, some 103] := by decide
example : points { performed := [.sodium, .chloride, .phosphate, .inorganicPhosphorus] } =
    some 28 := by decide
example : points { performed := [.sodium, .chloride, .bun, .uricAcid, .ast] } =
    some 50 := by decide
example : points { performed := [.calcium, .ionizedCalcium] } = none := by decide
example : points { performed := [.calcium, .ionizedCalcium], calcium := ⟨some false, none⟩ } =
    some 37 := by decide
example : points { performed := [.calcium, .ionizedCalcium], calcium := ⟨some true, some .calcium⟩ } =
    some 26 := by decide
example : points {
    performed := [.hdlCholesterol, .totalCholesterol, .ldlCholesterol]
    cholesterol := ⟨some true, some .ldlCholesterol⟩ } = some 34 := by decide
example : points {
    performed := [.hdlCholesterol, .totalCholesterol, .ldlCholesterol]
    cholesterol := ⟨some true, some .hdlCholesterol⟩ } = some 35 := by decide
example : points {
    performed := [.uibcColorimetric, .tibcColorimetric]
    ironBinding := ⟨some true, some .tibcColorimetric⟩ } = some 11 := by decide
example : points {
    performed := [.proteinFractionation, .totalProtein, .albumin]
    albuminByModifiedBCP := some true
    protein := ⟨some true, some .proteinFractionation⟩ } = some 22 := by decide
example : cholesterolRule.holds [.hdlCholesterol, .totalCholesterol, .ldlCholesterol]
    [.totalCholesterol, .ldlCholesterol] := by
  intro _
  rfl
example : ¬ cholesterolRule.holds [.hdlCholesterol, .totalCholesterol, .ldlCholesterol]
    [.hdlCholesterol, .totalCholesterol, .ldlCholesterol] := by
  intro h
  have wrong : 3 = 2 := h rfl
  cases wrong
example : points { performed := [.creatinine], creatinineByJaffe := some true } = some 0 := by decide
example : points {
    performed := [.manganese]
    manganese := some ⟨true, none, some true, some false⟩ } = some 0 := by decide
example : points {
    performed := [.manganese]
    manganese := some ⟨true, none, some true, some true⟩ } = some 27 := by decide

end Sanri.MedicalFee.BloodChemistry
