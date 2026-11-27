import Std

/-! 外来の履歴を射影するための暦・識別・確認範囲。 -/
namespace Sanri.History

def isLeap (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

abbrev Year := Nat

/-- 月・日は0始まり。1月・1日はそれぞれ0で表す。 -/
structure Month where
  year : Year
  index : Fin 12
  deriving DecidableEq, Repr

def Month.days (m : Month) : Nat :=
  match m.index.val with
  | 1 => if isLeap m.year then 29 else 28
  | 3 | 5 | 8 | 10 => 30
  | _ => 31

theorem Month.days_pos (m : Month) : 0 < m.days := by
  unfold Month.days
  split <;> first | omega | split <;> omega

structure Date where
  month : Month
  day : Fin month.days
  deriving DecidableEq, Repr

/-- 通常の年月日表記から作る。存在しない月日を未確定として返す。 -/
def Date.ofParts (year : Year) (month day : Nat) : Option Date :=
  if monthPositive : 0 < month then
    if monthBound : month ≤ 12 then
      let m : Month := ⟨year, ⟨month - 1, by omega⟩⟩
      if dayPositive : 0 < day then
        if dayBound : day ≤ m.days then
          some ⟨m, ⟨day - 1, by omega⟩⟩
        else none
      else none
    else none
  else none

def Date.year (d : Date) : Year := d.month.year

/-- 順序比較用の符号。差を日数として使わない。 -/
def Date.key (d : Date) : Nat :=
  (d.year * 12 + d.month.index.val) * 32 + d.day.val

def Month.shift (m : Month) (n : Nat) : Month :=
  let index := m.year * 12 + m.index.val + n
  ⟨index / 12, ⟨index % 12, Nat.mod_lt _ (by decide)⟩⟩

/-- 応当日が存在しない場合に月末を用いる方式。採用は個別条項で決める。 -/
def Date.shiftClamped (d : Date) (n : Nat) : Date :=
  let month := d.month.shift n
  ⟨month, ⟨min d.day.val (month.days - 1), by
    have positive := month.days_pos
    omega⟩⟩

structure Period where
  first : Date
  last : Date
  ordered : first.key ≤ last.key
  deriving Repr

def Period.Contains (p : Period) (day : Date) : Prop :=
  p.first.key ≤ day.key ∧ day.key ≤ p.last.key

instance (p : Period) (day : Date) : Decidable (p.Contains day) := by
  unfold Period.Contains
  infer_instance

def Period.Within (inner outer : Period) : Prop :=
  outer.first.key ≤ inner.first.key ∧ inner.last.key ≤ outer.last.key

instance (inner outer : Period) : Decidable (inner.Within outer) := by
  unfold Period.Within
  infer_instance

theorem Period.Within.contains {inner outer : Period} {day : Date} (h : inner.Within outer) (hd : inner.Contains day) :
    outer.Contains day := ⟨Nat.le_trans h.1 hd.1, Nat.le_trans hd.2 h.2⟩

theorem Period.contains_first (p : Period) : p.Contains p.first := ⟨Nat.le_refl _, p.ordered⟩

theorem Period.contains_last (p : Period) : p.Contains p.last := ⟨p.ordered, Nat.le_refl _⟩

def Period.day (date : Date) : Period := ⟨date, date, Nat.le_refl _⟩

def Period.month (m : Month) : Period :=
  have positive := m.days_pos
  ⟨⟨m, ⟨0, positive⟩⟩, ⟨m, ⟨m.days - 1, by omega⟩⟩, by simp [Date.key, Date.year]⟩

def Period.year (year : Year) : Period :=
  ⟨⟨⟨year, 0⟩, ⟨0, by change 0 < 31; decide⟩⟩, ⟨⟨year, 11⟩, ⟨30, by change 30 < 31; decide⟩⟩, by simp [Date.key, Date.year]; omega⟩

/-- 表現可能な最初の日から指定日まで。患者通算の照会に使う。 -/
def Period.through (date : Date) : Period :=
  ⟨⟨⟨0, 0⟩, ⟨0, by decide⟩⟩, date, Nat.zero_le _⟩

/-- 開始月から n 暦月。開始月を含み、終了月の初日を含まない。 -/
def InCalendarMonths (start : Month) (n : Nat) (date : Date) : Prop :=
  let elapsed := date.year * 12 + date.month.index.val
  let base := start.year * 12 + start.index.val
  base ≤ elapsed ∧ elapsed < base + n

/-- 実施日から応当日までの半開区間。月末補正を採用する場合の方式。 -/
def InClampedAnniversaryMonths (start : Date) (n : Nat) (date : Date) : Prop :=
  start.key ≤ date.key ∧ date.key < (start.shiftClamped n).key

structure Site where
  patient : Nat
  institution : Nat
  date : Date
  deriving DecidableEq, Repr

structure Performance (Item : Type) where
  id : Nat
  site : Site
  item : Item
  draw : Option Nat := none
  specimen : Option Nat := none
  series : Option Nat := none
  simultaneous : Option Nat := none
  deriving DecidableEq, Repr

structure Claim (Item : Type) where
  id : Nat
  site : Site
  item : Item
  performance : Option Nat := none
  deriving DecidableEq, Repr

/-- 局所IDは患者・機関の組の中で一意とする。欠落したID同士の関係は未確定。 -/
def Performance.sameGroup (field : Performance Item → Option Nat)
    (a b : Performance Item) : Option Bool := do
  if a.site.patient != b.site.patient || a.site.institution != b.site.institution then
    return false
  return (← field a) == (← field b)

theorem Performance.sameGroup_sameSite (field : Performance Item → Option Nat)
    (a b : Performance Item) (patient : a.site.patient = b.site.patient)
    (institution : a.site.institution = b.site.institution) :
    a.sameGroup field b = (field a).bind (fun x => (field b).map (x == ·)) := by
  simp [Performance.sameGroup, patient, institution]
  cases field a <;> cases field b <;> rfl

def Performance.sameDraw (a b : Performance Item) : Option Bool :=
  a.sameGroup Performance.draw b

def Performance.sameSpecimen (a b : Performance Item) : Option Bool :=
  a.sameGroup Performance.specimen b

def Performance.sameSeries (a b : Performance Item) : Option Bool :=
  a.sameGroup Performance.series b

def Performance.simultaneousWith (a b : Performance Item) : Option Bool :=
  a.sameGroup Performance.simultaneous b

def Site.sameDay (a b : Site) : Bool :=
  a.date == b.date

structure Scope where
  patient : Nat
  /-- none は全医療機関を確認したという明示的な範囲。 -/
  institution : Option Nat
  period : Period

def Site.monthScope (site : Site) : Scope :=
  ⟨site.patient, some site.institution, Period.month site.date.month⟩

def Scope.Includes (s : Scope) (site : Site) : Bool :=
  s.patient == site.patient &&
    (s.institution.isNone || s.institution == some site.institution) &&
    decide (s.period.Contains site.date)

def Scope.Covers (coverage query : Scope) : Prop :=
  coverage.patient = query.patient ∧
    (coverage.institution = none ∨ coverage.institution = query.institution) ∧
    query.period.Within coverage.period

instance (coverage query : Scope) : Decidable (coverage.Covers query) := by
  unfold Scope.Covers
  infer_instance

/-- 一つの確認済み範囲と記録。実施と算定は別々に網羅性を確認する。
算定履歴に照会中の候補を含めるかは、個別の射影側で定める。 -/
structure Snapshot (Entry : Type) where
  coverage : Scope
  entries : List Entry

def Snapshot.select (h : Snapshot Entry) (site : Entry → Site) (query : Scope)
    (accepts : Entry → Bool) : Option (List Entry) :=
  if h.coverage.Covers query then
    some (h.entries.filter fun entry => query.Includes (site entry) && accepts entry)
  else none

structure ClaimHistory (Item : Type) extends Snapshot (Claim Item) where
  distinctIds : (entries.map Claim.id).Nodup

def count (h : ClaimHistory Item) (query : Scope) (accepts : Item → Bool) : Option Nat :=
  (h.toSnapshot.select Claim.site query (fun claim => accepts claim.item)).map List.length

def withinLimit (h : ClaimHistory Item) (query : Scope) (accepts : Item → Bool)
    (limit : Nat) : Option Bool :=
  (count h query accepts).map (fun n => decide (n ≤ limit))

theorem withinLimit_iff :
    withinLimit h query accepts limit = some true ↔ ∃ n, count h query accepts = some n ∧ n ≤ limit := by
  unfold withinLimit
  cases count h query accepts <;> simp

theorem withinLimit_false_iff :
    withinLimit h query accepts limit = some false ↔
      ∃ n, count h query accepts = some n ∧ limit < n := by
  unfold withinLimit
  cases count h query accepts <;> simp [Nat.not_le]

theorem count_uncovered {h : ClaimHistory Item} (missing : ¬ h.coverage.Covers query) :
    count h query accepts = none := by simp [count, Snapshot.select, missing]

theorem withinLimit_uncovered {h : ClaimHistory Item} (missing : ¬ h.coverage.Covers query) :
    withinLimit h query accepts limit = none := by
  simp [withinLimit, count_uncovered (accepts := accepts) missing]

theorem empty_withinLimit (coverage query : Scope) (accepts : Item → Bool)
    (covered : coverage.Covers query) (limit : Nat) :
    withinLimit ⟨⟨coverage, []⟩, by simp⟩ query accepts limit = some true := by
  simp [withinLimit, count, Snapshot.select, covered]

theorem filtered_length_mono (entries : List Entry) (p q : Entry → Bool)
    (included : ∀ e, p e = true → q e = true) :
    (entries.filter p).length ≤ (entries.filter q).length := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
    cases hp : p head <;> cases hq : q head <;> simp_all <;> omega

/-- 固定した患者・医療機関・項目の期間を狭めると、選ばれる記録数は増えない。 -/
theorem period_length_mono (entries : List Entry) (site : Entry → Site)
    (wide : Scope) (narrow : Period) (contained : narrow.Within wide.period)
    (accepts : Entry → Bool) :
    (entries.filter (fun e => ({ wide with period := narrow } : Scope).Includes (site e) &&
      accepts e)).length ≤
    (entries.filter (fun e => wide.Includes (site e) && accepts e)).length := by
  apply filtered_length_mono
  intro e
  simp only [Scope.Includes, Bool.and_eq_true, decide_eq_true_eq]
  rintro ⟨⟨⟨patient, institution⟩, day⟩, accepts⟩
  exact ⟨⟨⟨patient, institution⟩, contained.contains day⟩, accepts⟩

theorem count_period_mono (h : ClaimHistory Item) (wide : Scope) (narrow : Period)
    (contained : narrow.Within wide.period) (covered : h.coverage.Covers wide)
    (accepts : Item → Bool) :
    ∃ smaller larger, count h { wide with period := narrow } accepts = some smaller ∧
      count h wide accepts = some larger ∧ smaller ≤ larger := by
  have narrowCovered : h.coverage.Covers { wide with period := narrow } :=
    ⟨covered.1, covered.2.1,
      Nat.le_trans covered.2.2.1 contained.1, Nat.le_trans contained.2 covered.2.2.2⟩
  exact ⟨_, _, by simp [count, Snapshot.select, narrowCovered],
    by simp [count, Snapshot.select, covered],
    period_length_mono h.entries Claim.site wide narrow contained (fun c => accepts c.item)⟩

example : InCalendarMonths ⟨2024, 0⟩ 2 ⟨⟨2024, 1⟩, ⟨28, by decide⟩⟩ := by
  unfold InCalendarMonths Date.year
  decide
example : ¬ InClampedAnniversaryMonths ⟨⟨2024, 0⟩, ⟨30, by decide⟩⟩ 1
    ⟨⟨2024, 1⟩, ⟨28, by decide⟩⟩ := by
  unfold InClampedAnniversaryMonths
  decide
example : (Period.month ⟨2024, 1⟩).Contains ⟨⟨2024, 1⟩, ⟨28, by decide⟩⟩ := by decide
example : ¬ (Period.month ⟨2024, 1⟩).Contains ⟨⟨2024, 2⟩, ⟨0, by decide⟩⟩ := by decide
example : Date.ofParts 2100 2 29 = none := by decide
example : (Date.ofParts 2000 2 29).isSome = true := by decide
example : Date.ofParts 2026 4 31 = none := by decide
example : (Period.year 2026).Contains ⟨⟨2026, 11⟩, ⟨30, by decide⟩⟩ := by decide
example : ¬ (Period.year 2026).Contains ⟨⟨2027, 0⟩, ⟨0, by decide⟩⟩ := by decide
example : (⟨⟨2024, 0⟩, ⟨30, by decide⟩⟩ : Date).shiftClamped 1 = ⟨⟨2024, 1⟩, ⟨28, by decide⟩⟩ := by decide

private def firstDraw : Performance Unit :=
  { id := 1, site := ⟨2, 3, ⟨⟨2026, 9⟩, ⟨0, by decide⟩⟩⟩,
    item := (), draw := some 4 }

example : firstDraw.sameDraw { firstDraw with id := 2 } = some true := by decide
example : firstDraw.sameSpecimen { firstDraw with id := 2 } = none := by decide
example : firstDraw.sameDraw { firstDraw with site := { firstDraw.site with institution := 5 } } =
    some false := by decide

end Sanri.History
