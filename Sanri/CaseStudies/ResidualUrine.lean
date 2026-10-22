import Sanri.Logic
import Sanri.UltrasoundMonitoring

namespace Sanri.CaseStudies.ResidualUrine

/-!
一患者・一医療機関・一暦月内の算定回数だけを比較する限定モデル。
本文の患者単位上限と、コード別上限への射影の違いを検証する。

対象患者・実施事実等の条件を満たすという前提の下で、この二制約だけを扱う。
公式CSVのレコードを埋め込まず、上限と出典はパラメータにする。
この定理だけで公式データ全体の誤り、他資料の不存在、全算定条件との
一致を主張することはできない。同日制約の参照先は留意事項のD216-2(2)。
疑義解釈による追加・変更の有無は、この事例では確認を終えていない。
-/

open Sanri.Logic

inductive Method where
  | ultrasound
  | catheter
  deriving DecidableEq, Repr

/-- day は同じ暦月内の日の識別子。日付計算や月境界はこの事例の対象外。 -/
structure Measurement where
  day : Nat
  method : Method
  deriving DecidableEq, Repr

abbrev MonthlyClaims := List Measurement

def methodCount (method : Method) : MonthlyClaims → Nat
  | [] => 0
  | measurement :: rest =>
      (if measurement.method = method then 1 else 0) + methodCount method rest

def PatientMonthlyLimit (limit : Nat) (claims : MonthlyClaims) : Prop :=
  claims.length ≤ limit

def CodeMonthlyLimits (limit : Nat) (claims : MonthlyClaims) : Prop :=
  methodCount .ultrasound claims ≤ limit ∧ methodCount .catheter claims ≤ limit

/-- 同日異方法の併算定を除外する。月内の合計上限とは別の制約。 -/
def NoMixedMethodsOnSameDay (claims : MonthlyClaims) : Prop :=
  claims.Pairwise (fun first second => first.day ≠ second.day ∨ first.method = second.method)

def patientLimitRule (source : SourceRef) (limit : Nat) : Rule Unit MonthlyClaims where
  id := "residual-urine.patient-monthly-limit"
  source := source
  holds := fun _ claims => PatientMonthlyLimit limit claims

def codeLimitsRule (source : SourceRef) (limit : Nat) : Rule Unit MonthlyClaims where
  id := "residual-urine.code-monthly-limits-projection"
  source := source
  holds := fun _ claims => CodeMonthlyLimits limit claims

def sameDayRule (source : SourceRef) : Rule Unit MonthlyClaims where
  id := "residual-urine.same-day-principal-method"
  source := source
  holds := fun _ claims => NoMixedMethodsOnSameDay claims

theorem methodCount_le_length (method : Method) (claims : MonthlyClaims) :
    methodCount method claims ≤ claims.length := by
  induction claims with
  | nil => exact Nat.le_refl 0
  | cons measurement rest ih =>
      simp only [methodCount, List.length_cons]
      split
      · simpa [Nat.add_comm] using Nat.succ_le_succ ih
      · simpa using Nat.le_trans ih (Nat.le_succ rest.length)

/-- 患者合計の上限を満たせば、同じ上限での各方法の上限も満たす。 -/
theorem patient_limit_implies_code_limits (limit : Nat) (claims : MonthlyClaims)
    (h : PatientMonthlyLimit limit claims) : CodeMonthlyLimits limit claims := by
  exact ⟨Nat.le_trans (methodCount_le_length .ultrasound claims) h,
    Nat.le_trans (methodCount_le_length .catheter claims) h⟩

theorem patient_rule_refines_code_rule (textSource tableSource : SourceRef) (limit : Nat) :
    RefinesOn (fun _ : Unit => True)
      [patientLimitRule textSource limit] [codeLimitsRule tableSource limit] := by
  intro context _ claims h rule member
  have shared := h (patientLimitRule textSource limit) (by simp)
  have separate := patient_limit_implies_code_limits limit claims shared
  have eq : rule = codeLimitsRule tableSource limit := by simpa using member
  subst rule
  exact separate

/-- 別日の三実施という独自の小さな検証例。CSVの抜粋ではない。 -/
def witness : MonthlyClaims :=
  [⟨1, .ultrasound⟩, ⟨2, .ultrasound⟩, ⟨3, .catheter⟩]

theorem witness_meets_code_limits : CodeMonthlyLimits 2 witness := by
  unfold CodeMonthlyLimits
  decide

theorem witness_violates_patient_limit : ¬ PatientMonthlyLimit 2 witness := by
  unfold PatientMonthlyLimit
  decide

theorem witness_meets_day_exclusion : NoMixedMethodsOnSameDay witness := by
  unfold NoMixedMethodsOnSameDay
  decide

/-- 同日背反を加えても、別日に分散した三回を合計二回には制限できない。 -/
theorem separate_limits_and_day_exclusion_are_insufficient :
    ∃ claims, CodeMonthlyLimits 2 claims ∧ NoMixedMethodsOnSameDay claims ∧
      ¬ PatientMonthlyLimit 2 claims :=
  ⟨witness, witness_meets_code_limits, witness_meets_day_exclusion,
    witness_violates_patient_limit⟩

theorem monthly_rules_disagree (textSource tableSource : SourceRef) :
    DisagreesAt [patientLimitRule textSource 2] [codeLimitsRule tableSource 2] () := by
  refine ⟨witness, Or.inr ⟨?_, ?_⟩⟩
  · intro rule member
    have eq : rule = codeLimitsRule tableSource 2 := by simpa using member
    subst rule
    exact witness_meets_code_limits
  · intro h
    exact witness_violates_patient_limit
      (h (patientLimitRule textSource 2) (by simp))

theorem monthly_rules_not_equivalent (textSource tableSource : SourceRef) :
    ¬ EquivalentOn (fun _ : Unit => True)
      [patientLimitRule textSource 2] [codeLimitsRule tableSource 2] :=
  not_equivalentOn_of_disagreement True.intro (monthly_rules_disagree textSource tableSource)

/-- 通知の同日制約を両モデルへ明示的に追加しても、月上限の差は残る。 -/
theorem notification_does_not_close_monthly_gap
    (textSource tableSource notificationSource : SourceRef) :
    DisagreesAt
      [patientLimitRule textSource 2, sameDayRule notificationSource]
      [codeLimitsRule tableSource 2, sameDayRule notificationSource] () := by
  refine ⟨witness, Or.inr ⟨?_, ?_⟩⟩
  · intro rule member
    rcases List.mem_cons.mp member with eq | member
    · subst rule
      exact witness_meets_code_limits
    · have eq : rule = sameDayRule notificationSource := by simpa using member
      subst rule
      exact witness_meets_day_exclusion
  · intro h
    exact witness_violates_patient_limit
      (h (patientLimitRule textSource 2) (by simp))

/-- 患者合計上限を補うと、コード別上限との共通部分は患者合計上限と一致する。 -/
theorem restoring_shared_limit (claims : MonthlyClaims) (limit : Nat) :
    (CodeMonthlyLimits limit claims ∧ PatientMonthlyLimit limit claims) ↔
      PatientMonthlyLimit limit claims := by
  constructor
  · exact And.right
  · intro h
    exact ⟨patient_limit_implies_code_limits limit claims h, h⟩

/-- 三回未満では合計二回上限への反例にならない。上の例は回数について最小。 -/
theorem violating_claims_have_at_least_three (claims : MonthlyClaims)
    (h : ¬ PatientMonthlyLimit 2 claims) : 3 ≤ claims.length :=
  Nat.lt_of_not_ge h

/-! 既存の計算モデルへの限定した接続。
既存モデルは方法を横断した算定済回数を受け取り、第三回を除外している。
以下は当該入力への確認であり、既存モデル全体の同値性の証明ではない。 -/

private def thirdMeasurement : Sanri.MedicalFee.UltrasoundMonitoring.Context :=
  { item := .residualUrineCatheter, residualUrineClaimsThisMonth := 2 }

theorem legacy_model_rejects_third_measurement :
    Sanri.MedicalFee.UltrasoundMonitoring.eligible thirdMeasurement = false := by decide

end Sanri.CaseStudies.ResidualUrine
