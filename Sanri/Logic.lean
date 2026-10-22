/-!
# 出典付き制約による診療報酬規則の研究基盤

各条項を独立した制約として保持する。出典の種類やリストの順序から、
上書き・法的優先順位・ただし書の適用関係を自動的に導入しない。
例外や適用範囲は個々の `Rule.holds` に明示する必要がある。

ここでの定理は記述された制約の性質を示すものであり、原文から制約への
翻訳の正しさや、未収載の関連資料の不存在を保証しない。
-/
namespace Sanri.Logic

/-- 出典の区別。種別自体は規則間の優先関係を意味しない。 -/
inductive SourceKind where
  | primaryText
  | notification
  | clarification
  | electronicTable
  | manualInterpretation
  | syntheticExample
  deriving DecidableEq, Repr

/-- 原文との対応確認の作業状態。Lean の証明や法的な正当性とは異なる。 -/
inductive SourceVerification where
  | unchecked
  | transcribed
  | checkedAgainstSource
  deriving DecidableEq, Repr

/-- 原文を転載せずに、条項・版・確認状態を追跡するための参照情報。 -/
structure SourceRef where
  kind : SourceKind
  identifier : String
  edition : String
  location : String
  verification : SourceVerification := .unchecked
  url : Option String := none
  deriving DecidableEq, Repr

/-- ある状況と算定結果が、特定の出典から形式化した条項を満たすという関係。 -/
structure Rule (Context : Type u) (Result : Type v) where
  id : String
  source : SourceRef
  holds : Context → Result → Prop

variable {Context : Type u} {Result : Type v}

/-- 列挙した全条項を満たす。リストの順序による優先順位は設けない。 -/
def Satisfies (rules : List (Rule Context Result))
    (context : Context) (result : Result) : Prop :=
  ∀ rule, rule ∈ rules → rule.holds context result

/-- この入力について、全条項を満たす結果が少なくとも一つ存在する。 -/
def SatisfiableAt (rules : List (Rule Context Result)) (context : Context) : Prop :=
  ∃ result, Satisfies rules context result

/-- この入力の結果は高々一つ。解が存在しない場合にも成立する。 -/
def UniqueAt (rules : List (Rule Context Result)) (context : Context) : Prop :=
  ∀ first second, Satisfies rules context first → Satisfies rules context second →
    first = second

/-- この入力について、全条項を満たす結果が存在し、かつ一意に定まる。 -/
def DeterminesAt (rules : List (Rule Context Result)) (context : Context) : Prop :=
  SatisfiableAt rules context ∧ UniqueAt rules context

/-- 対象とする入力範囲のすべてで結果が存在する。 -/
def SatisfiableOn (scope : Context → Prop) (rules : List (Rule Context Result)) : Prop :=
  ∀ context, scope context → SatisfiableAt rules context

/-- 対象とする入力範囲のすべてで結果が存在し、一意に定まる。 -/
def DeterminesOn (scope : Context → Prop) (rules : List (Rule Context Result)) : Prop :=
  ∀ context, scope context → DeterminesAt rules context

/-- 対象範囲で `stronger` の解はすべて `weaker` の解でもある。 -/
def RefinesOn (scope : Context → Prop)
    (stronger weaker : List (Rule Context Result)) : Prop :=
  ∀ context, scope context → ∀ result,
    Satisfies stronger context result → Satisfies weaker context result

/-- 対象範囲で二つの規則群の解集合が一致する。 -/
def EquivalentOn (scope : Context → Prop)
    (left right : List (Rule Context Result)) : Prop :=
  RefinesOn scope left right ∧ RefinesOn scope right left

/-- 同じ入力と結果に対し、一方の規則群だけが許容する具体的な差。 -/
def DisagreesAt (left right : List (Rule Context Result)) (context : Context) : Prop :=
  ∃ result,
    (Satisfies left context result ∧ ¬ Satisfies right context result) ∨
    (Satisfies right context result ∧ ¬ Satisfies left context result)

theorem satisfies_nil (context : Context) (result : Result) :
    Satisfies ([] : List (Rule Context Result)) context result := by
  intro rule h
  cases h

theorem satisfies_cons (rule : Rule Context Result)
    (rules : List (Rule Context Result)) (context : Context) (result : Result) :
    Satisfies (rule :: rules) context result ↔
      rule.holds context result ∧ Satisfies rules context result := by
  constructor
  · intro h
    exact ⟨h rule (by simp), fun other member => h other (by simp [member])⟩
  · intro h other member
    rcases List.mem_cons.mp member with same | member
    · subst other
      exact h.1
    · exact h.2 other member

theorem satisfies_append (left right : List (Rule Context Result))
    (context : Context) (result : Result) :
    Satisfies (left ++ right) context result ↔
      Satisfies left context result ∧ Satisfies right context result := by
  constructor
  · intro h
    exact ⟨fun rule member => h rule (List.mem_append.mpr (.inl member)),
      fun rule member => h rule (List.mem_append.mpr (.inr member))⟩
  · intro h rule member
    rcases List.mem_append.mp member with member | member
    · exact h.1 rule member
    · exact h.2 rule member

/-- 制約を増やした規則群の解は、元の規則群も満たす。 -/
theorem satisfies_of_subset {base extended : List (Rule Context Result)}
    (subset : ∀ rule, rule ∈ base → rule ∈ extended)
    {context : Context} {result : Result}
    (h : Satisfies extended context result) : Satisfies base context result := by
  intro rule member
  exact h rule (subset rule member)

/-- 同じ制約を含むリストは、順序や重複回数が違っても同じ解集合をもつ。 -/
theorem satisfies_iff_of_same_rules {left right : List (Rule Context Result)}
    (same : ∀ rule, rule ∈ left ↔ rule ∈ right)
    (context : Context) (result : Result) :
    Satisfies left context result ↔ Satisfies right context result := by
  constructor
  · exact satisfies_of_subset (fun rule member => (same rule).mpr member)
  · exact satisfies_of_subset (fun rule member => (same rule).mp member)

theorem adding_rule_refines (scope : Context → Prop)
    (rule : Rule Context Result) (rules : List (Rule Context Result)) :
    RefinesOn scope (rule :: rules) rules := by
  intro context _ result h
  exact (satisfies_cons rule rules context result).mp h |>.2

theorem adding_rules_refines (scope : Context → Prop)
    (base extra : List (Rule Context Result)) :
    RefinesOn scope (base ++ extra) base := by
  intro context _ result h
  exact (satisfies_append base extra context result).mp h |>.1

/-- 制約追加後に解があるなら、追加前にも解がある。逆向きは一般に成り立たない。 -/
theorem satisfiableAt_of_subset {base extended : List (Rule Context Result)}
    (subset : ∀ rule, rule ∈ base → rule ∈ extended) {context : Context}
    (h : SatisfiableAt extended context) : SatisfiableAt base context := by
  obtain ⟨result, h⟩ := h
  exact ⟨result, satisfies_of_subset subset h⟩

/-- 充足不能な規則群は、制約を追加するだけでは充足可能にならない。
通知や疑義解釈による「解決」が例外・適用範囲・語義の修正を伴う場合、
旧制約をそのまま保持して新制約を追加する操作では表せない。
その場合は解釈の改訂を明示した別仕様を作り、改訂前後を比較する。 -/
theorem not_satisfiableAt_of_subset {base extended : List (Rule Context Result)}
    (subset : ∀ rule, rule ∈ base → rule ∈ extended) {context : Context}
    (h : ¬ SatisfiableAt base context) : ¬ SatisfiableAt extended context := by
  intro solution
  exact h (satisfiableAt_of_subset subset solution)

/-- 制約追加は高々一解である性質を保つが、解の存在は保つとは限らない。 -/
theorem uniqueAt_of_subset {base extended : List (Rule Context Result)}
    (subset : ∀ rule, rule ∈ base → rule ∈ extended) {context : Context}
    (h : UniqueAt base context) : UniqueAt extended context := by
  intro first second hfirst hsecond
  exact h first second (satisfies_of_subset subset hfirst) (satisfies_of_subset subset hsecond)

/-- 解がない場合も高々一解である。`UniqueAt` だけでは決定性を示さない。 -/
theorem uniqueAt_of_not_satisfiableAt {rules : List (Rule Context Result)}
    {context : Context} (h : ¬ SatisfiableAt rules context) : UniqueAt rules context := by
  intro first _ hfirst _
  exact False.elim (h ⟨first, hfirst⟩)

theorem not_determinesAt_of_not_satisfiableAt {rules : List (Rule Context Result)}
    {context : Context} (h : ¬ SatisfiableAt rules context) : ¬ DeterminesAt rules context := by
  intro determines
  exact h determines.1

theorem not_uniqueAt_of_two_results {rules : List (Rule Context Result)}
    {context : Context} {first second : Result}
    (hfirst : Satisfies rules context first) (hsecond : Satisfies rules context second)
    (different : first ≠ second) : ¬ UniqueAt rules context := by
  intro unique
  exact different (unique first second hfirst hsecond)

/-- 同時に成立しない二条項がともに適用される入力には、解が存在しない。 -/
theorem not_satisfiableAt_of_conflicting_rules {rules : List (Rule Context Result)}
    {context : Context} (first second : Rule Context Result)
    (hfirst : first ∈ rules) (hsecond : second ∈ rules)
    (conflict : ∀ result, first.holds context result → second.holds context result → False) :
    ¬ SatisfiableAt rules context := by
  rintro ⟨result, h⟩
  exact conflict result (h first hfirst) (h second hsecond)

theorem refinesOn_refl (scope : Context → Prop) (rules : List (Rule Context Result)) :
    RefinesOn scope rules rules := by
  intro _ _ _ h
  exact h

theorem refinesOn_trans {scope : Context → Prop}
    {first second third : List (Rule Context Result)}
    (hfirst : RefinesOn scope first second) (hsecond : RefinesOn scope second third) :
    RefinesOn scope first third := by
  intro context hscope result h
  exact hsecond context hscope result (hfirst context hscope result h)

theorem equivalentOn_iff {scope : Context → Prop}
    {left right : List (Rule Context Result)} :
    EquivalentOn scope left right ↔
      ∀ context, scope context → ∀ result,
        (Satisfies left context result ↔ Satisfies right context result) := by
  constructor
  · intro h context hscope result
    exact ⟨h.1 context hscope result, h.2 context hscope result⟩
  · intro h
    exact ⟨fun context hscope result => (h context hscope result).mp,
      fun context hscope result => (h context hscope result).mpr⟩

theorem not_equivalentOn_of_disagreement {scope : Context → Prop}
    {left right : List (Rule Context Result)} {context : Context}
    (hscope : scope context) (difference : DisagreesAt left right context) :
    ¬ EquivalentOn scope left right := by
  intro equivalent
  obtain ⟨result, (⟨hleft, hright⟩ | ⟨hright, hleft⟩)⟩ := difference
  · exact hright (equivalent.1 context hscope result hleft)
  · exact hleft (equivalent.2 context hscope result hright)

/-- 同じ解集合をもつ二つの仕様では、存在と一意性も一致する。 -/
theorem determinesAt_iff_of_equivalentOn {scope : Context → Prop}
    {left right : List (Rule Context Result)} (h : EquivalentOn scope left right)
    {context : Context} (hscope : scope context) :
    DeterminesAt left context ↔ DeterminesAt right context := by
  constructor
  · rintro ⟨⟨result, solution⟩, unique⟩
    refine ⟨⟨result, h.1 context hscope result solution⟩, ?_⟩
    intro first second hfirst hsecond
    exact unique first second (h.2 context hscope first hfirst) (h.2 context hscope second hsecond)
  · rintro ⟨⟨result, solution⟩, unique⟩
    refine ⟨⟨result, h.2 context hscope result solution⟩, ?_⟩
    intro first second hfirst hsecond
    exact unique first second (h.1 context hscope first hfirst) (h.1 context hscope second hsecond)

/-! 以下は論理基盤の性質を示す合成例であり、実在の診療報酬規則ではない。 -/
namespace SyntheticExamples

def source : SourceRef := {
  kind := .syntheticExample
  identifier := "logic-vacuity-example"
  edition := "1"
  location := "Sanri/Logic.lean: SyntheticExamples"
}

def requireZero : Rule Unit Nat := {
  id := "require-zero"
  source := source
  holds := fun _ result => result = 0
}

def requireOne : Rule Unit Nat := {
  id := "require-one"
  source := source
  holds := fun _ result => result = 1
}

theorem contradictory_rules_unsatisfiable :
    ¬ SatisfiableAt [requireZero, requireOne] () := by
  apply not_satisfiableAt_of_conflicting_rules requireZero requireOne (by simp) (by simp)
  intro result zero one
  change result = 0 at zero
  change result = 1 at one
  have impossible : (0 : Nat) = 1 := zero.symm.trans one
  cases impossible

/-- 矛盾した仕様でも高々一解は空虚に成立し、存在かつ一意とは区別される。 -/
theorem vacuous_uniqueness_is_not_determination :
    UniqueAt [requireZero, requireOne] () ∧
      ¬ DeterminesAt [requireZero, requireOne] () :=
  ⟨uniqueAt_of_not_satisfiableAt contradictory_rules_unsatisfiable,
    not_determinesAt_of_not_satisfiableAt contradictory_rules_unsatisfiable⟩

/-- 条項の順序を入れ替えても同じ解集合となる。 -/
theorem reordered_rules_same_solutions (result : Nat) :
    Satisfies [requireZero, requireOne] () result ↔
      Satisfies [requireOne, requireZero] () result := by
  apply satisfies_iff_of_same_rules
  intro rule
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact or_comm

end SyntheticExamples

end Sanri.Logic
