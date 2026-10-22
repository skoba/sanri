import Sanri.Logic

namespace Sanri.CaseStudies.FilingClarification

/-!
疑義解釈資料（令和8年3月23日・その1）別添1の医科問3を使う限定事例。
対象は、2026年5月31日時点で医療DX推進体制整備加算及び診療録管理体制加算の
施設基準を届け出ている医療機関が、6月1日以降に電子的診療情報連携体制整備加算を
算定する際の「改めて届出が必要か」という一論点だけである。

結果型は点数でも全算定可否でもなく、必要な届出の種類を表す。
`FilingPartMet` はこの部分に対応する届出事実だけを確認し、その他の施設基準、
届出の受理・効力発生時点、経過措置、患者条件等は確認しない。
したがって、この部分を満たしても加算全体の算定可能性は結論できない。

`notYetReviewed` は、この問の資料をまだ確認していない分析段階を表す。
本文全体に制約が存在しない、制度が未決定又は矛盾している、という主張ではない。
疑義解釈を追加したことにより、未確認だった論点の条件が特定される例である。
出典の種類だけを使った優先順位や、既存条項の上書きは行わない。
-/

open Sanri.Logic

def clarificationSource : SourceRef := {
  kind := .clarification
  identifier := "MHLW-2026-03-23-clarification-1-medical-Q3"
  edition := "令和8年度・2026年3月23日保険局医療課事務連絡・その1"
  location := "別添1 医科診療報酬点数表関係 問3・PDF第3頁（医－2）"
  verification := .checkedAgainstSource
  url := some "https://www.mhlw.go.jp/content/12400000/001678310.pdf"
}

/-- 問3の対象範囲と届出事実。日付計算・届出の実質要件は別仕様とする。 -/
structure Context where
  medicalDXFiledOn20260531 : Bool
  recordManagementFiledOn20260531 : Bool
  newAdditionRequestedFrom20260601 : Bool
  separateNewAdditionFiling : Bool
  deriving DecidableEq, Repr

def InScope (context : Context) : Prop :=
  context.medicalDXFiledOn20260531 = true ∧
    context.recordManagementFiledOn20260531 = true ∧
    context.newAdditionRequestedFrom20260601 = true

inductive FilingRequirement where
  | oldFilingMayBeReused
  | separateFilingRequired
  deriving DecidableEq, Repr

/-- この論点に限った届出事実の充足。加算全体の施設基準充足とは異なる。 -/
def FilingPartMet (context : Context) : FilingRequirement → Prop
  | .oldFilingMayBeReused =>
      context.medicalDXFiledOn20260531 = true ∧
        context.recordManagementFiledOn20260531 = true
  | .separateFilingRequired => context.separateNewAdditionFiling = true

/-- 原文を確認する前に、旧届出をそのまま流用できるとは仮定しない。 -/
def notYetReviewed : List (Rule Context FilingRequirement) := []

/-- 問3の範囲に限り、別途の届出が必要という回答を制約として追加する。 -/
def clarificationRule : Rule Context FilingRequirement where
  id := "electronic-information.new-filing-required.2026-Q3"
  source := clarificationSource
  holds := fun context requirement =>
    InScope context → requirement = .separateFilingRequired

def reviewed : List (Rule Context FilingRequirement) :=
  notYetReviewed ++ [clarificationRule]

theorem reviewed_iff (context : Context) (requirement : FilingRequirement) :
    Satisfies reviewed context requirement ↔
      (InScope context → requirement = .separateFilingRequired) := by
  constructor
  · intro h
    exact h clarificationRule (by simp [reviewed, notYetReviewed])
  · intro h rule member
    have eq : rule = clarificationRule := by
      simpa [reviewed, notYetReviewed] using member
    subst rule
    exact h

/-- 対象範囲では、資料確認後に届出の種類が一意に決まる。 -/
theorem reviewed_determines_filing_requirement (context : Context)
    (scope : InScope context) : DeterminesAt reviewed context := by
  constructor
  · refine ⟨.separateFilingRequired, ?_⟩
    exact (reviewed_iff context .separateFilingRequired).mpr (fun _ => rfl)
  · intro first second hfirst hsecond
    exact ((reviewed_iff context first).mp hfirst scope).trans
      ((reviewed_iff context second).mp hsecond scope).symm

/-- 独自の合成例：二つの旧届出はあるが、新加算の別途届出はまだない。 -/
def oldFilingsOnly : Context := {
  medicalDXFiledOn20260531 := true
  recordManagementFiledOn20260531 := true
  newAdditionRequestedFrom20260601 := true
  separateNewAdditionFiling := false
}

/-- 独自の合成例：同じ対象条件に加え、新加算の別途届出を行った事実がある。 -/
def withSeparateFiling : Context :=
  { oldFilingsOnly with separateNewAdditionFiling := true }

theorem old_only_in_scope : InScope oldFilingsOnly := by
  unfold InScope
  decide

theorem separate_filing_in_scope : InScope withSeparateFiling := by
  unfold InScope
  decide

/-- 未確認の部分仕様だけでは、この論点について二つの結果を区別できない。 -/
theorem unreviewed_filing_question_is_undetermined :
    ¬ DeterminesAt notYetReviewed oldFilingsOnly := by
  intro determined
  have different : FilingRequirement.oldFilingMayBeReused ≠
      .separateFilingRequired := by decide
  exact different (determined.2 _ _ (satisfies_nil _ _) (satisfies_nil _ _))

/-- 旧届出を流用可能とする仮説は、確認した問3の対象範囲では排除される。 -/
theorem old_filing_reuse_is_excluded :
    ¬ Satisfies reviewed oldFilingsOnly .oldFilingMayBeReused := by
  intro h
  have impossible := (reviewed_iff oldFilingsOnly .oldFilingMayBeReused).mp h
    old_only_in_scope
  cases impossible

/-- 旧届出だけの例は、問3で必要とされた別途届出の部分を満たさない。 -/
theorem old_filings_do_not_meet_new_filing_part :
    ¬ FilingPartMet oldFilingsOnly .separateFilingRequired := by
  unfold FilingPartMet
  decide

/-- 別途届出の事実がある例は、この届出部分を満たす。全算定可否は含まない。 -/
theorem separate_filing_meets_new_filing_part :
    FilingPartMet withSeparateFiling .separateFilingRequired := by
  unfold FilingPartMet
  decide

/-- 対象範囲に入るという事実から、新しい届出の存在は導けない。 -/
theorem old_filings_do_not_entail_separate_filing :
    ¬ (∀ context, InScope context → context.separateNewAdditionFiling = true) := by
  intro h
  have impossible := h oldFilingsOnly old_only_in_scope
  change false = true at impossible
  cases impossible

/-- 問3は、別途届出が未実施の事例でも必要な手続を特定する。制度矛盾ではない。 -/
theorem clarification_identifies_missing_filing :
    DeterminesAt reviewed oldFilingsOnly ∧
      ¬ FilingPartMet oldFilingsOnly .separateFilingRequired :=
  ⟨reviewed_determines_filing_requirement oldFilingsOnly old_only_in_scope,
    old_filings_do_not_meet_new_filing_part⟩

end Sanri.CaseStudies.FilingClarification
