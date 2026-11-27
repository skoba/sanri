import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment

/-! D016、基準診療日2026-10-22の外来検体検査実施料。 -/
namespace Sanri.MedicalFee.D016

open Sanri.Logic Sanri.History

inductive Item where
  | bSurface
  | tSubset
  | percentages
  | granulocyteFunction
  | granulocyteScreen
  | redCellNeutrophil
  | lstOne
  | lstTwo
  | lstThreeOrMore
  | granulocyteAntigen
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .bSurface => 1
  | .tSubset => 2
  | .percentages => 3
  | .granulocyteFunction => 4
  | .granulocyteScreen => 5
  | .redCellNeutrophil => 6
  | .lstOne => 7
  | .lstTwo => 7
  | .lstThreeOrMore => 7
  | .granulocyteAntigen => 8

def Item.branch : Item → Nat
  | .bSurface => 0
  | .tSubset => 0
  | .percentages => 0
  | .granulocyteFunction => 0
  | .granulocyteScreen => 0
  | .redCellNeutrophil => 0
  | .lstOne => 1
  | .lstTwo => 2
  | .lstThreeOrMore => 3
  | .granulocyteAntigen => 0

def Item.points : Item → Nat
  | .bSurface => 155
  | .tSubset => 185
  | .percentages => 193
  | .granulocyteFunction => 200
  | .granulocyteScreen => 220
  | .redCellNeutrophil => 320
  | .lstOne => 345
  | .lstTwo => 425
  | .lstThreeOrMore => 700
  | .granulocyteAntigen => 640

def ledgerItems : List Item :=
  [.bSurface, .tSubset, .percentages, .granulocyteFunction, .granulocyteScreen, .redCellNeutrophil,
   .lstOne, .lstTwo, .lstThreeOrMore, .granulocyteAntigen]

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度改定・2026-10-22取得版",
    "PDF188–189頁 D016 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (n : Nat) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF386頁 D016(" ++ toString n ++ ")", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def rateRule (i : Item) : Rule Item Nat :=
  ⟨"primary/D016/item/" ++ toString i.number,
    primary (toString i.number ++ (if i.branch = 0 then "" else " 枝" ++ toString i.branch)),
    fun item p => item = i → p = i.points⟩

def rates := ledgerItems.map rateRule

theorem rate_iff (i : Item) (p : Nat) : Satisfies rates i p ↔ p = i.points := by
  constructor
  · intro h
    have hi : i ∈ ledgerItems := by cases i <;> decide
    exact h (rateRule i) (List.mem_map.mpr ⟨i, hi, rfl⟩) rfl
  · intro h r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro eq
    simpa [eq] using h

inductive Procedure where
  | inkPhagocytosis | nbtReduction | chemotaxis | bacteria | photochemical
  | conA | pha | suspectedDrug
  deriving DecidableEq

structure Context where
  performance : Performance Item
  procedure : Option Procedure := none
  drugs : Option (List Nat) := none
  /-- 同じ一連について算定対象に選んだ他の実施を確認した結果。 -/
  otherSelected : Option (List (Performance Item)) := none
  investigatesImmunodeficiency : Option Bool := none
  pnhDifferential : Option Bool := none
  monoclonalCount : Option Nat := none
  bothRedCellsAndNeutrophilsExamined : Option Bool := none
  suspectedGpiDeficiencyUnderCriteria : Option Bool := none
  diagnosesGpiDeficiency : Option Bool := none
  granulocyteSurfaceAntigenWithMonoclonal : Option Bool := none

def Context.item (c : Context) := c.performance.item

def SeriesUnit (c : Context) : Prop :=
  c.performance.series.isSome = true ∧ ∃ others, c.otherSelected = some others ∧
    ∀ e ∈ others, e.item = c.item → c.performance.sameSeries e = some false

def seriesRule : Rule Context Unit :=
  ⟨"notice/D016/paragraph/1", notice 1, fun c _ =>
    (c.item = .tSubset → c.investigatesImmunodeficiency = some true ∧ SeriesUnit c) ∧
    (c.item = .granulocyteScreen →
      (c.procedure = some .inkPhagocytosis ∨ c.procedure = some .nbtReduction) ∧ SeriesUnit c) ∧
    (c.item = .granulocyteFunction →
      (c.procedure = some .chemotaxis ∨ c.procedure = some .bacteria ∨
        c.procedure = some .photochemical) ∧ SeriesUnit c)⟩

def surfaceRule : Rule Context Unit :=
  ⟨"notice/D016/paragraph/2", notice 2, fun c _ => c.item = .redCellNeutrophil →
    c.pnhDifferential = some true ∧ c.monoclonalCount = some 2 ∧
      c.bothRedCellsAndNeutrophilsExamined = some true⟩

def DrugCount (i : Item) (n : Nat) : Prop :=
  (i = .lstOne ∧ n = 1) ∨ (i = .lstTwo ∧ n = 2) ∨ (i = .lstThreeOrMore ∧ 3 ≤ n)

def lstBranches : Rule Context Unit :=
  ⟨"primary/D016/item/7", primary "7 イ・ロ・ハ", fun c _ =>
    c.item.number = 7 → ∃ drugs, c.drugs = some drugs ∧ drugs.Nodup ∧
      DrugCount c.item drugs.length⟩

def lstMethod : Rule Context Unit :=
  ⟨"notice/D016/paragraph/3", notice 3, fun c _ => c.item.number = 7 →
    c.procedure = some .conA ∨ c.procedure = some .pha ∨ c.procedure = some .suspectedDrug⟩

def gpiRule : Rule Context Unit :=
  ⟨"notice/D016/paragraph/4", notice 4, fun c _ => c.item = .granulocyteAntigen →
    c.suspectedGpiDeficiencyUnderCriteria = some true ∧ c.diagnosesGpiDeficiency = some true ∧
      c.granulocyteSurfaceAntigenWithMonoclonal = some true⟩

inductive Remark where
  | basisForGpiSuspicion
  deriving DecidableEq

def gpiDocumentation : Rule Context (Remark → Prop) :=
  ⟨"notice/D016/paragraph/4", notice 4, fun c documented =>
    c.item = .granulocyteAntigen → documented .basisForGpiSuspicion⟩

def eligibilityRules := [seriesRule, surfaceRule, lstBranches, lstMethod, gpiRule]
def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def PermitsRate (c : Context) (p : Nat) : Prop := Eligible c ∧ Satisfies rates c.item p

def legacyRequest (i : Item) (n : Nat) : SpecimenTests.Request :=
  { code := .d016, number := i.number, branch := i.branch, quantity := n }

theorem legacy_rate (i : Item) (n : Nat) (h : i.number = 7 → DrugCount i n) :
    SpecimenTests.assessOne (legacyRequest i n) = some (.charged i.points 0) := by
  cases i <;> first
    | rfl
    | have hd := h rfl
      simp [DrugCount] at hd
      subst n
      rfl
    | have hd := h rfl
      simp [DrugCount] at hd
      change (if !(decide (3 ≤ n)) then none
        else some (SpecimenTests.ItemResult.charged 700 0)) = _
      simp [hd, Item.points]

theorem legacy_iff (c : Context) (p : Nat) (n : Nat)
    (h : c.item.number = 7 → DrugCount c.item n) :
    PermitsRate c p ↔ Eligible c ∧
      SpecimenTests.assessOne (legacyRequest c.item n) = some (.charged p 0) := by
  simp [PermitsRate, rate_iff, legacy_rate _ _ h, eq_comm]

theorem determines (c : Context) (h : Eligible c) :
    (∃ p, PermitsRate c p) ∧ (∀ p q, PermitsRate c p → PermitsRate c q → p = q) :=
  ⟨⟨c.item.points, h, (rate_iff _ _).mpr rfl⟩, fun _ _ hp hq =>
    ((rate_iff _ _).mp hp.2).trans ((rate_iff _ _).mp hq.2).symm⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 16, number := i.number, ordinaryCategory := .immunological }

def execution (kind : Nat) (c : Context) (p : Nat) (_ : PermitsRate c p) :
    Examinations.SpecimenItem :=
  { kind := kind, executionPoints := p }

private def sample : Context :=
  { performance := ⟨1, ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .lstThreeOrMore, none, none, none, none⟩
    procedure := some .suspectedDrug
    drugs := some [1, 2, 3] }

example : PermitsRate sample 700 := by
  refine ⟨?_, (rate_iff _ _).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, seriesRule, surfaceRule,
    lstBranches, lstMethod, gpiRule, sample, Context.item, Item.number, DrugCount]

example : ¬ DrugCount .lstThreeOrMore 2 := by simp [DrugCount]

end Sanri.MedicalFee.D016
