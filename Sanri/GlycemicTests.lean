import Sanri.BloodMorphology
import Sanri.D007

namespace Sanri.MedicalFee.GlycemicTests

open Sanri.Logic

/-- D007(13)で区別する測定法。 -/
inductive AlbuminMethod where
  | hplcTwoColumns | hplcOneColumnColorimetric | affinityChromatography
  | immunoturbidimetry | eia | enzymatic | other
  deriving DecidableEq, Repr

inductive Item where
  | a1c
  | glycatedAlbumin (method : Option AlbuminMethod)
  | anhydroglucitol
  deriving DecidableEq, Repr

/-- D007側への射影。グリコアルブミンの測定法はこのモジュールの入力に保持する。 -/
def Item.toD007 : Item → Option D007.Item
  | .a1c => none
  | .glycatedAlbumin _ => some ⟨.glycemic, .glycatedAlbumin⟩
  | .anhydroglucitol => some ⟨.glycemic, .anhydroglucitol⟩

def Item.points : Item → Nat
  | .a1c => BloodMorphology.Item.hemoglobinA1c.basePoints
  | .glycatedAlbumin _ => 55
  | .anhydroglucitol => 80

def Item.methodAllowed : Item → Option Bool
  | .glycatedAlbumin method => method.map (· != .other)
  | _ => some true

def Item.isA1c : Item → Bool
  | .a1c => true
  | _ => false

structure Performance where
  id : Nat
  item : Item
  deriving DecidableEq, Repr

inductive Exception where
  | none
  | clinical
  | clozapine
  /-- 一般例外とクロザピン例外の重複。両方を用いた追加算定は未確定。 -/
  | both
  deriving DecidableEq, Repr

/-- 同一患者・同一医療機関の、一暦月分の三検査の全実施。
算定しない実施も含める。実施IDは検体IDや日付とは独立する。
一般例外の「等」および6月以内への該当は確認済みの外部入力。 -/
structure Month where
  performed : List Performance
  exception : Option Exception
  deriving DecidableEq, Repr

structure Selection where
  /-- 主たる検査として選んだ実施。 -/
  principal : Nat
  additional : Option Nat := none
  deriving DecidableEq, Repr

inductive Assessment where
  | resolved (principal : Performance) (additional : Option Performance)
  | invalidSelection
  | unresolved
  deriving DecidableEq, Repr

def Month.find (m : Month) (id : Nat) : Option Performance :=
  m.performed.find? (·.id == id)

def Month.uniqueIds (m : Month) : Bool :=
  let ids := m.performed.map Performance.id
  ids.eraseDups == ids

/-- 追加1件の評価。両例外に該当し、追加の扱いが問題になるときは未確定を返す。 -/
def extraAllowed (m : Month) (item : Item) : Option Bool := do
  match ← m.exception with
  | .none => return false
  | .clinical => return true
  | .clozapine => return item.isA1c
  | .both => none

def Assessment.points : Assessment → Option Nat
  | .resolved principal extra =>
    some (principal.item.points + (extra.map (·.item.points)).getD 0)
  | _ => none

def assess (history : Option Month) (s : Selection) : Assessment := Id.run do
  let some m := history | return .unresolved
  if !m.uniqueIds then return .unresolved
  let some principal := m.find s.principal | return .invalidSelection
  match principal.item.methodAllowed with
  | none => return .unresolved
  | some false => return .invalidSelection
  | some true =>
    let some id := s.additional | return .resolved principal none
    if s.principal == id then return .invalidSelection
    let some extra := m.find id | return .invalidSelection
    match extra.item.methodAllowed, extraAllowed m extra.item with
    | some false, _ | _, some false => return .invalidSelection
    | some true, some true => return .resolved principal (some extra)
    | _, _ => return .unresolved

/-- D005側に既存の判定入力として渡す。未確定・不整合な算定案からは判定しない。 -/
def a1cAllowance (a : Assessment) (id : Nat) : Option Bool :=
  match a with
  | .resolved principal extra =>
    some ((principal.id == id && principal.item.isA1c) ||
      extra.any (fun e => e.id == id && e.item.isA1c))
  | _ => none

def assessA1c (history : Option Month) (s : Selection) (id : Nat) :
    BloodMorphology.Assessment :=
  BloodMorphology.assess { item := .hemoglobinA1c, a1cMonthlyAllowance := a1cAllowance (assess history s) id }

/-- 月内に二回以上実施し、追加が許されない場合の算定件数制約の射影。 -/
def principalOnly (m : Month) (charged : List Nat) : Prop :=
  m.performed.length ≥ 2 → charged.length ≤ 1

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", location,
    .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

/-- 追加枠を用いる場合の例外条件。重複例外の解釈はこの制約の対象範囲外。 -/
def additionalRule : Rule Month (Option Performance) :=
  ⟨"D005.9-additional", notice "PDF339頁 D005(9) ただし書及び末文", fun month extra =>
    ∀ item, extra = some item →
      month.exception = some .clinical ∨
        (month.exception = some .clozapine ∧ item.item.isA1c = true)⟩

def MethodAllowed : Item → Prop
  | .glycatedAlbumin method => ∃ m, method = some m ∧ m ≠ .other
  | _ => True

theorem methodAllowed_iff (item : Item) : MethodAllowed item ↔ item.methodAllowed = some true := by
  cases item with
  | glycatedAlbumin method => cases method <;> simp [MethodAllowed, Item.methodAllowed]
  | _ => simp [MethodAllowed, Item.methodAllowed]

private theorem additional_iff (m : Month) (extra : Performance) :
    additionalRule.holds m (some extra) ↔ extraAllowed m extra.item = some true := by
  change (∀ item, some extra = some item → _) ↔ _
  simp only [Option.some.injEq, forall_eq']
  cases hm : m.exception with
  | none => simp [extraAllowed, hm]
  | some e => cases e <;> simp [extraAllowed, hm]

def albuminMethodRule : Rule Unit Item :=
  ⟨"D007.13", notice "PDF356頁 D007(13)",
    fun _ item => MethodAllowed item⟩

/-- 二つの通知が共通して定める、例外のない場合の上限。 -/
def ordinaryRules : List (Rule Month (List Nat)) :=
  [⟨"D005.9-ordinary", notice "PDF339頁 D005(9)", fun m charged =>
      m.exception = some .none → principalOnly m charged⟩,
   ⟨"D007.14-ordinary", notice "PDF356頁 D007(14)", fun m charged =>
      m.exception = some .none → principalOnly m charged⟩]

theorem ordinary_no_two (m : Month) (charged : List Nat)
    (hm : m.exception = some .none) (performed : m.performed.length ≥ 2)
    (h : Satisfies ordinaryRules m charged) : charged.length ≤ 1 := by
  simp only [ordinaryRules, satisfies_cons] at h
  exact h.1 hm performed

/-- 固定した算定案に対応する実施と、その方法・例外条件。 -/
def Selected (history : Option Month) (s : Selection)
    (principal : Performance) (extra : Option Performance) : Prop :=
  ∃ m, history = some m ∧ m.uniqueIds = true ∧
    m.find s.principal = some principal ∧ albuminMethodRule.holds () principal.item ∧
    (s.additional = none ∧ extra = none ∨
      ∃ id e, s.additional = some id ∧ s.principal ≠ id ∧
        m.find id = some e ∧ extra = some e ∧
        albuminMethodRule.holds () e.item ∧ additionalRule.holds m extra)

theorem selected_iff (history : Option Month) (s : Selection)
    (principal : Performance) (extra : Option Performance) :
    Selected history s principal extra ↔ assess history s = .resolved principal extra := by
  cases history with
  | none => simp [Selected, assess]
  | some m =>
    cases hu : m.uniqueIds <;> simp [Selected, assess, hu]
    cases hf : m.find s.principal <;> simp
    rename_i main
    have hm (e : Performance) :
        albuminMethodRule.holds () e.item ↔ e.item.methodAllowed = some true :=
      methodAllowed_iff _
    simp only [hm, Id.run, pure]
    cases hp : main.item.methodAllowed with
    | none => grind
    | some allowed =>
      cases allowed
      · grind
      · cases he : s.additional
        · simp
          grind
        · rename_i id
          by_cases hd : s.principal = id
          · simp [hd]
          · cases hx : m.find id
            · simp [hd, hx]
            · rename_i e
              simp [hd, hx]
              cases extra with
              | none => split <;> simp_all
              | some extra =>
                simp only [additional_iff]
                split <;> simp_all <;> grind

/-- 上限でなく、実施IDと主たる検査を固定した算定案の点数の射影。 -/
def pointsRule : Rule (Option Month × Selection) Nat :=
  ⟨"D005.D007-glycemic-points",
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "2026-10-22取得版",
      "PDF176頁 D005の9及び180頁 D007の17・21", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun (m, s) p => ∃ principal extra, Selected m s principal extra ∧
      p = principal.item.points + (extra.map (·.item.points)).getD 0⟩

theorem pointsRule_iff (m : Option Month) (s : Selection) (p : Nat) :
    pointsRule.holds (m, s) p ↔ (assess m s).points = some p := by
  change (∃ principal extra, Selected m s principal extra ∧ _) ↔ _
  simp only [selected_iff]
  cases assess m s <;> simp [Assessment.points, eq_comm, and_assoc]

theorem determines_selected_points (m : Option Month) (s : Selection) (p : Nat)
    (h : (assess m s).points = some p) : DeterminesAt [pointsRule] (m, s) := by
  refine ⟨⟨p, ?_⟩, ?_⟩
  · exact (satisfies_cons _ _ _ _).2 ⟨(pointsRule_iff m s p).mpr h, satisfies_nil _ _⟩
  · intro a b ha hb
    have first := (pointsRule_iff m s a).mp (ha pointsRule (by simp))
    have second := (pointsRule_iff m s b).mp (hb pointsRule (by simp))
    exact Option.some.inj (first.symm.trans second)

theorem determines_selected_points_on :
    DeterminesOn (fun (m, s) => ∃ main extra, Selected m s main extra) [pointsRule] := by
  rintro ⟨m, s⟩ ⟨main, extra, h⟩
  exact determines_selected_points m s
    (main.item.points + (extra.map (·.item.points)).getD 0)
    (by simp [(selected_iff m s main extra).mp h, Assessment.points])

private def monthWith (exception : Exception) : Month :=
  ⟨[⟨1, .a1c⟩, ⟨2, .glycatedAlbumin (some .enzymatic)⟩, ⟨3, .anhydroglucitol⟩], some exception⟩

example : ∃ main extra, Selected (some (monthWith .none)) ⟨2, none⟩ main extra :=
  ⟨⟨2, .glycatedAlbumin (some .enzymatic)⟩, none, (selected_iff _ _ _ _).mpr rfl⟩

example : ¬ ∃ main extra, Selected none ⟨2, none⟩ main extra := by
  simp [Selected]

example : (assess (some (monthWith .none)) ⟨2, none⟩).points = some 55 := by decide
example : assess (some (monthWith .none)) ⟨2, some 1⟩ = .invalidSelection := by decide
example : (assess (some (monthWith .clinical)) ⟨2, some 3⟩).points = some 135 := by decide
example : (assess (some (monthWith .clozapine)) ⟨2, some 1⟩).points = some 104 := by decide
example : assess (some (monthWith .clozapine)) ⟨1, some 2⟩ = .invalidSelection := by decide
example : assess (some (monthWith .both)) ⟨2, some 1⟩ = .unresolved := by decide
example : assess none ⟨2, none⟩ = .unresolved := by decide
example : assess (some ⟨[⟨1, .a1c⟩, ⟨2, .a1c⟩], some .none⟩) ⟨1, some 2⟩ =
    .invalidSelection := by decide
example : assess (some ⟨[⟨1, .a1c⟩, ⟨1, .anhydroglucitol⟩], some .none⟩) ⟨1, none⟩ =
    .unresolved := by decide
example : assessA1c (some (monthWith .clozapine)) ⟨2, some 1⟩ 1 = .payable 49 0 := by decide
example : assessA1c (some (monthWith .none)) ⟨2, none⟩ 1 = .ineligible := by decide
example : assess (some ⟨[⟨1, .glycatedAlbumin none⟩], none⟩) ⟨1, none⟩ = .unresolved := by decide
example : assess (some ⟨[⟨1, .glycatedAlbumin (some .other)⟩], none⟩) ⟨1, none⟩ =
    .invalidSelection := by decide

example : DeterminesAt [pointsRule] (some (monthWith .clozapine), ⟨2, some 1⟩) :=
  determines_selected_points _ _ 104 rfl

example : Satisfies [additionalRule] (monthWith .clozapine) (some ⟨1, .a1c⟩) := by
  rw [satisfies_cons]
  refine ⟨?_, satisfies_nil _ _⟩
  intro item h
  cases Option.some.inj h
  exact Or.inr ⟨rfl, rfl⟩

example : ¬ Satisfies [additionalRule] (monthWith .clozapine) (some ⟨3, .anhydroglucitol⟩) := by
  intro h
  have condition := (satisfies_cons _ _ _ _).1 h
  rcases condition.1 _ rfl with hc | ⟨_, ha⟩
  · change some Exception.clozapine = some Exception.clinical at hc
    cases hc
  · change false = true at ha
    cases ha

-- 主たる検査を固定する前の候補には、異なる点数があり得る。
example : ∃ a b : Selection, (assess (some (monthWith .none)) a).points = some 49 ∧
    (assess (some (monthWith .none)) b).points = some 80 :=
  ⟨⟨1, none⟩, ⟨3, none⟩, rfl, rfl⟩

end Sanri.MedicalFee.GlycemicTests
