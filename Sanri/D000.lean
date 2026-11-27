import Sanri.UrineFecalTests
import Sanri.SpecimenJudgment
import Sanri.History

/-! 基準診療日2026-10-22の外来D000。一回の実施を評価する。 -/
namespace Sanri.MedicalFee.D000

open Sanri.Logic Sanri.History

inductive Method where
  | strip | ampoule | tablet | instrumentReadingOfReagent
  deriving DecidableEq

inductive Analyte where
  | specificGravity | ph | qualitativeProtein | glucose | urobilinogen | qualitativeUrobilin
  | bilirubin | ketones | occultBlood | stripNitrite | sodiumChloride | stripLeukocyteEsterase
  | albumin
  deriving DecidableEq

inductive Arrangement where
  | direct
  | contracted (promptReport : Option Bool)
  deriving DecidableEq

structure Context where
  /-- 実施記録の医療機関は患者の診療を担う保険医療機関。 -/
  performance : Performance Unit
  performingInstitution : Option Nat
  method : Option Method
  analytes : List Analyte
  arrangement : Option Arrangement

structure Result where
  charge : UrineFecalTests.Charge
  judgmentCategory : Option SpecimenJudgment.Category
  separateAnalytePoints : Analyte → Nat

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF173頁 D000 " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def InHouse (c : Context) : Prop :=
  c.performingInstitution = some c.performance.site.institution

def ReportConfirmed (c : Context) : Prop :=
  c.arrangement = some .direct ∨ c.arrangement = some (.contracted (some true))

def Eligible (c : Context) : Prop :=
  InHouse c ∧ c.analytes ≠ [] ∧ c.method.isSome = true ∧ ReportConfirmed c

def points : Nat := 26

def headingRule : Rule Context Result :=
  ⟨"primary/D000/heading", primary "見出し", fun _ r => r.charge = ⟨points, 0⟩⟩

def inHouseRule : Rule Context Result :=
  ⟨"primary/D000/note/unnumbered/1", primary "注", fun c _ => InHouse c⟩

def judgmentRule : Rule Context Result :=
  ⟨"notice/D000/paragraph/1", notice "PDF330頁 D000(1)",
    fun _ r => r.judgmentCategory = none⟩

def performanceRule : Rule Context Result :=
  ⟨"notice/D000/paragraph/2", notice "PDF330–331頁 D000(2)",
    fun c _ => c.analytes ≠ []⟩

def methodRule : Rule Context Result :=
  ⟨"notice/D000/paragraph/2/a", notice "PDF330–331頁 D000(2)ア",
    fun c _ => c.method.isSome = true⟩

def includedAnalytesRule : Rule Context Result :=
  ⟨"notice/D000/paragraph/2/i", notice "PDF331頁 D000(2)イ",
    fun c r => ∀ analyte ∈ c.analytes, r.separateAnalytePoints analyte = 0⟩

/-- 各枝は同じ実施の構成項目を指定する。対象外の検査の単独評価には用いない。 -/
def analyteRule (analyte : Analyte) : Rule Context Result :=
  let (suffix, loc) := match analyte with
    | .specificGravity => ("i", "イ")
    | .ph => ("ro", "ロ")
    | .qualitativeProtein => ("ha", "ハ")
    | .glucose => ("ni", "ニ")
    | .urobilinogen => ("ho", "ホ")
    | .qualitativeUrobilin => ("he", "へ")
    | .bilirubin => ("to", "ト")
    | .ketones => ("chi", "チ")
    | .occultBlood => ("ri", "リ")
    | .stripNitrite => ("nu", "ヌ")
    | .sodiumChloride => ("ru", "ル")
    | .stripLeukocyteEsterase => ("wo", "ヲ")
    | .albumin => ("wa", "ワ")
  ⟨"notice/D000/paragraph/2/i/" ++ suffix, notice ("PDF331頁 D000(2)イ(" ++ loc ++ ")"),
    fun _ r => r.separateAnalytePoints analyte = 0⟩

def contractorRule : Rule Context Result :=
  ⟨"notice/D000/paragraph/3", notice "PDF331頁 D000(3)",
    fun c _ => InHouse c ∧ ReportConfirmed c⟩

def rules : List (Rule Context Result) :=
  [headingRule, inHouseRule, judgmentRule, performanceRule, methodRule, includedAnalytesRule,
    contractorRule, analyteRule .specificGravity, analyteRule .ph,
    analyteRule .qualitativeProtein, analyteRule .glucose, analyteRule .urobilinogen,
    analyteRule .qualitativeUrobilin, analyteRule .bilirubin, analyteRule .ketones,
    analyteRule .occultBlood, analyteRule .stripNitrite, analyteRule .sodiumChloride,
    analyteRule .stripLeukocyteEsterase, analyteRule .albumin]

def legacyInput (c : Context) : UrineFecalTests.Context :=
  { item := .generalUrine
    performedInsideInstitution := c.performingInstitution == some c.performance.site.institution }

def judgmentTest : SpecimenJudgment.Test :=
  { major := 0, ordinaryCategory := .urineFecal }

private theorem legacy_charge (c : Context) (house : InHouse c) :
    UrineFecalTests.assess (legacyInput c) = some (.charged ⟨points, 0⟩) := by
  change c.performingInstitution = some c.performance.site.institution at house
  simp [legacyInput, house, points, UrineFecalTests.assess, UrineFecalTests.requiresInHouse,
    UrineFecalTests.isSediment, UrineFecalTests.pointRule]

theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ Eligible c ∧
      UrineFecalTests.assess (legacyInput c) = some (.charged r.charge) ∧
      r.judgmentCategory = SpecimenJudgment.categoryFor judgmentTest ∧
      r.separateAnalytePoints = fun _ => 0 := by
  constructor
  · intro h
    have house : InHouse c := h inHouseRule (by simp [rules])
    have eligible : Eligible c :=
      ⟨house, h performanceRule (by simp [rules]), h methodRule (by simp [rules]),
        (show InHouse c ∧ ReportConfirmed c from h contractorRule (by simp [rules])).2⟩
    have charge : r.charge = ⟨points, 0⟩ := h headingRule (by simp [rules])
    have included (a : Analyte) : r.separateAnalytePoints a = 0 := by
      apply h (analyteRule a)
      cases a <;> simp [rules]
    exact ⟨eligible, charge ▸ legacy_charge c house,
      h judgmentRule (by simp [rules]), funext included⟩
  · rintro ⟨⟨house, performed, method, report⟩, legacy, judgment, included⟩
    have charge : r.charge = ⟨points, 0⟩ := by
      rw [legacy_charge c house] at legacy
      injection legacy with legacy
      injection legacy with legacy
      exact legacy.symm
    intro rule membership
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact charge
      | exact house
      | exact judgment
      | exact performed
      | exact method
      | exact ⟨house, report⟩
      | simp [includedAnalytesRule, analyteRule, included]

theorem determines (c : Context) (eligible : Eligible c) : DeterminesAt rules c := by
  have legacy := legacy_charge c eligible.1
  refine ⟨⟨⟨⟨26, 0⟩, none, fun _ => 0⟩, (satisfies_iff ..).mpr
    ⟨eligible, legacy, rfl, rfl⟩⟩, ?_⟩
  intro a b ha hb
  obtain ⟨_, aCharge, aJudgment, aIncluded⟩ := (satisfies_iff c a).mp ha
  obtain ⟨_, bCharge, bJudgment, bIncluded⟩ := (satisfies_iff c b).mp hb
  cases a
  cases b
  simp_all

def toSpecimenItem (r : Result) (kind : Nat) : Option Examinations.SpecimenItem :=
  (UrineFecalTests.Assessment.charged r.charge).toSpecimenItem kind

private def sample : Context :=
  ⟨{ id := 1, site := ⟨2, 3, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, item := () }, some 3, some .strip,
    [.glucose, .ph], some (.contracted (some true))⟩

example : Eligible sample := ⟨rfl, by decide, rfl, Or.inr rfl⟩

example : Satisfies rules sample ⟨⟨26, 0⟩, none, fun _ => 0⟩ :=
  (satisfies_iff ..).mpr ⟨⟨rfl, by decide, rfl, Or.inr rfl⟩, rfl, rfl, rfl⟩

example : ¬ SatisfiableAt rules { sample with performingInstitution := some 4 } := by
  rintro ⟨r, h⟩
  have house := ((satisfies_iff _ r).mp h).1.1
  simp [InHouse, sample] at house

example : ¬ SatisfiableAt rules { sample with arrangement := some (.contracted none) } := by
  rintro ⟨r, h⟩
  have report := ((satisfies_iff _ r).mp h).1.2.2.2
  simp [ReportConfirmed] at report

example : toSpecimenItem ⟨⟨26, 0⟩, none, fun _ => 0⟩ 1 =
    some { kind := 1, executionPoints := 26 } := rfl

example : OutpatientConsultation.includedByNote6 (UrineFecalTests.outpatientService .generalUrine) =
    true := rfl

end Sanri.MedicalFee.D000
