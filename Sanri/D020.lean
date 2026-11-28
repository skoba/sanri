import Sanri.SpecimenJudgment
import Sanri.History

namespace Sanri.MedicalFee.D020

open Sanri.Logic Sanri.History

inductive Item where
  | liquid | other
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.liquid, .other]
def Item.number : Item → Nat | .liquid => 1 | .other => 2
def Item.points : Item → Nat | .liquid => 315 | .other => 224

inductive Detection where
  | oxygenSensitiveFluorescentSensor | carbonDioxideSensor | redoxDye | other
  deriving DecidableEq

structure Context where
  performance : Performance Item
  liquidMedium : Option Bool := none
  detection : Option Detection := none
  /-- 同時採取又は一連の採取として照合した実施群。 -/
  collection : Option (List (Performance Item)) := none
  /-- 確認済みの採取群における唯一の算定候補。 -/
  selected : Option (List (Performance Item)) := none

def Liquid (c : Context) : Prop :=
  c.liquidMedium = some true ∧
    c.detection ∈ [some .oxygenSensitiveFluorescentSensor, some .carbonDioxideSensor, some .redoxDye]

def Other (c : Context) : Prop :=
  c.liquidMedium = some false ∨ (c.liquidMedium = some true ∧ c.detection = some .other)

def sameCollection (a b : Performance Item) : Prop :=
  a.simultaneousWith b = some true ∨ a.sameSeries b = some true

private def condition (n : Nat) (page : String) (p : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D020/paragraph/" ++ toString n,
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF" ++ page ++ "頁 D020(" ++ toString n ++ ")", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c _ => p c⟩

def collectionLimit : Rule Context Unit :=
  condition 1 "387" fun c =>
    ∃ group, c.collection = some group ∧ c.performance ∈ group ∧
      (∀ p ∈ group, sameCollection c.performance p) ∧ c.selected = some [c.performance]

/-- 同時又は一連が全組で成り立つ読みと、算定候補との関係を確認する読み。 -/
inductive CollectionReading where
  | pairwise | relativeToSelection
  deriving DecidableEq

private def related (a b : Performance Item) : Bool :=
  a.simultaneousWith b == some true || a.sameSeries b == some true

/-- 採取範囲の確認値を使う。未知の関係だけから群を確定しない。 -/
def collectionFromReading (c : Context) (rows : List (Performance Item))
    (reading : Option CollectionReading) : Option Context :=
  match reading with
  | none => none
  | some reading =>
    let ids := rows.map Performance.id
    let confirmed := match reading with
      | .pairwise => rows.all fun a => rows.all (related a)
      | .relativeToSelection => rows.all (related c.performance)
    if rows.contains c.performance && ids.eraseDups == ids && confirmed then
      some { c with collection := some rows, selected := some [c.performance] }
    else none

private theorem related_sound {a b : Performance Item} (h : related a b = true) :
    sameCollection a b := by
  simpa [related, sameCollection, Bool.or_eq_true] using h

theorem collectionFromReading_sound {c checked : Context} {rows reading}
    (h : collectionFromReading c rows reading = some checked) : collectionLimit.holds checked () := by
  cases reading with
  | none => simp [collectionFromReading] at h
  | some reading =>
    cases reading <;>
      simp only [collectionFromReading, Bool.and_eq_true, List.contains_iff_mem,
        beq_iff_eq] at h
    all_goals
      split at h
      · rename_i facts
        obtain rfl := Option.some.inj h.symm
        refine ⟨rows, rfl, facts.1.1, ?_, rfl⟩
        intro row member
        first
        | exact related_sound (List.all_eq_true.mp (List.all_eq_true.mp facts.2 _ facts.1.1) _ member)
        | exact related_sound (List.all_eq_true.mp facts.2 _ member)
      · contradiction

def liquidMethod : Rule Context Unit :=
  condition 2 "388" fun c => c.performance.item = .liquid → Liquid c

def otherMethod : Rule Context Unit :=
  condition 3 "388" fun c => c.performance.item = .other → Other c

/-- 退院判断目的の頻回実施を扱う段落の外来への射影。 -/
def dischargeException : Rule Bool Unit :=
  ⟨"notice/D020/paragraph/4",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
      "PDF388頁 D020(4)", .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun usesInpatientDischargeException _ => usesInpatientDischargeException = false⟩

def rate (i : Item) : Rule Context Nat :=
  ⟨"primary/D020/item/" ++ toString i.number,
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
      "PDF189頁 D020 " ++ toString i.number, .checkedAgainstSource,
      some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩,
    fun c p => c.performance.item = i → p = i.points⟩

def rates := ledgerItems.map rate
def InScope (c : Context) := Satisfies [collectionLimit, liquidMethod, otherMethod] c ()

theorem legacy_iff (c : Context) (p : Nat) :
    Satisfies rates c p ↔ SpecimenTests.assessOne { code := .d020, number := c.performance.item.number } = some (.charged p 0) := by
  cases h : c.performance.item
  · change Satisfies rates c p ↔ SpecimenTests.assessOne { code := .d020, number := 1 } = some (.charged p 0)
    change Satisfies rates c p ↔ some (SpecimenTests.ItemResult.charged 315 0) = some (.charged p 0)
    simp [rates, ledgerItems, satisfies_cons, satisfies_nil, rate, h, Item.points, eq_comm]
  · change Satisfies rates c p ↔ SpecimenTests.assessOne { code := .d020, number := 2 } = some (.charged p 0)
    change Satisfies rates c p ↔ some (SpecimenTests.ItemResult.charged 224 0) = some (.charged p 0)
    simp [rates, ledgerItems, satisfies_cons, satisfies_nil, rate, h, Item.points, eq_comm]

theorem determines : DeterminesOn InScope rates := by
  intro c _
  cases h : c.performance.item <;>
    simp [rates, ledgerItems, satisfies_cons, satisfies_nil, rate, h, Item.points,
      DeterminesAt, SatisfiableAt, UniqueAt]

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 20, number := i.number, ordinaryCategory := .microbiological }

private def performed : Performance Item :=
  ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .liquid, none, some 1, none, some 1⟩

private def sample : Context :=
  { performance := performed, liquidMedium := some true,
    detection := some .redoxDye, collection := some [performed], selected := some [performed] }

example :
    let middle := { performed with id := 2, simultaneous := some 2, series := some 2 }
    let first := { performed with id := 1, simultaneous := some 2, series := some 1 }
    let last := { performed with id := 3, simultaneous := some 3, series := some 2 }
    let c := { sample with performance := middle }
    let rows := [first, middle, last]
    ((collectionFromReading c rows (some .pairwise)).isNone,
      (collectionFromReading c rows (some .relativeToSelection)).isSome,
      (collectionFromReading c rows none).isNone) = (true, true, true) := by decide

example : InScope sample ∧ Satisfies rates sample 315 := by
  constructor
  · simp [InScope, collectionLimit, liquidMethod, otherMethod, condition, Liquid, sample, performed, sameCollection, Performance.simultaneousWith,
      Performance.sameSeries, Performance.sameGroup,
      satisfies_cons, satisfies_nil]
  · exact (legacy_iff _ _).mpr rfl

example : ¬ InScope { sample with detection := none } := by
  simp [InScope, collectionLimit, liquidMethod, otherMethod, condition, Liquid, sample, performed, sameCollection, Performance.simultaneousWith,
      Performance.sameSeries, Performance.sameGroup,
    satisfies_cons, satisfies_nil]

end Sanri.MedicalFee.D020
