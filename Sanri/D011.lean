import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D011

open Sanri.Logic Sanri.History

inductive Item where
  | abo | rhD | directCoombs | indirectCoombs | otherRh | irregularAntibody
  | aboTransferase | plateletIgG | aboSubtype | antiplateletAntibody
  | pf4IgG | pf4IgGmA | pf4Qualitative
  deriving DecidableEq

def Item.number : Item → Nat
  | .abo | .rhD => 1 | .directCoombs | .indirectCoombs => 2
  | .otherRh => 3 | .irregularAntibody => 4 | .aboTransferase => 5 | .plateletIgG => 6
  | .aboSubtype => 7 | .antiplateletAntibody => 8
  | .pf4IgG => 9 | .pf4IgGmA => 10 | .pf4Qualitative => 11

def Item.branch : Item → Nat
  | .directCoombs => 1 | .indirectCoombs => 2 | _ => 0

def Item.variant : Item → Nat
  | .rhD => 1 | _ => 0

def Item.points : Item → Nat
  | .abo | .rhD => 39 | .directCoombs => 34 | .indirectCoombs => 47
  | .otherRh => 163 | .irregularAntibody => 174 | .aboTransferase => 176 | .plateletIgG => 190
  | .aboSubtype => 260 | .antiplateletAntibody => 261
  | .pf4IgG => 376 | .pf4IgGmA => 390 | .pf4Qualitative => 420

def ledgerItems : List Item :=
  [.abo, .rhD, .directCoombs, .indirectCoombs, .otherRh, .irregularAntibody, .aboTransferase,
    .plateletIgG, .aboSubtype, .antiplateletAntibody, .pf4IgG, .pf4IgGmA, .pf4Qualitative]

def Item.isPf4 (i : Item) : Bool := decide (i ∈ [.pf4IgG, .pf4IgGmA, .pf4Qualitative])

inductive Surgery where
  | thoracic | cardiovascular | abdominal | k877 | k879 | k889 | k898 | k912
  deriving DecidableEq

structure Operation where
  site : Site
  procedure : Surgery
  transfused : Option Bool
  /-- 輸血時のD011とK920注6の選択。 -/
  chooseD011 : Option Bool

structure Context where
  performance : Performance Item
  operation : Option Operation := none
  priorTransfusion : Prop := False
  priorPregnancy : Prop := False
  itpDiagnosisOrFollowup : Prop := False
  hitDiagnosis : Prop := False
  immunochromatography : Prop := False
  /-- 同一検体の因子検査をまとめた候補と、確認済みのその内訳。 -/
  rhFactors : Option (List (Performance Nat)) := none
  /-- 一連の全PF4検査の確認済み記録と主検査の実施ID。 -/
  pf4Series : Option (List (Performance Item)) := none
  mainPf4 : Option Nat := none

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度・2026-06-01適用",
    "PDF184頁 D011 " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def itemRule (i : Item) : Rule Context Nat :=
  let n := toString i.number
  let loc := match i with
    | .directCoombs => n ++ "イ" | .indirectCoombs => n ++ "ロ" | _ => n
  ⟨"primary/D011/item/" ++ n, primary loc, fun c p =>
    c.performance.item = i → p = i.points⟩

def surgeryRule : Rule Context Unit :=
  ⟨"primary/D011/item/4/note", primary "4 注", fun c _ =>
    c.performance.item = .irregularAntibody → c.operation.isSome = true⟩

private def condition (id loc : String) (holds : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D011/paragraph/" ++ id, notice loc, fun c _ => holds c⟩

def rhSpecimenRule : Rule Context Unit :=
  condition "1" "PDF369頁 D011(1)" fun c => c.performance.item = .otherRh →
    ∃ xs, c.rhFactors = some xs ∧ xs ≠ [] ∧ ∀ f ∈ xs,
      let p := { id := f.id, site := f.site, item := c.performance.item, specimen := f.specimen }
      c.performance.sameSpecimen p = some true

def transfusionSelection (o : Operation) : Prop :=
  o.transfused = some false ∨ (o.transfused = some true ∧ o.chooseD011 = some true)

def irregularRule : Rule Context Unit :=
  condition "2" "PDF369頁 D011(2)" fun c => c.performance.item = .irregularAntibody →
    (c.priorTransfusion ∨ c.priorPregnancy) ∧
      ∃ o, c.operation = some o ∧ c.performance.site = o.site ∧ transfusionSelection o

structure Documentation where
  priorTransfusionRecorded : Prop
  priorPregnancyRecorded : Prop

def irregularDocumentation : Rule Context Documentation :=
  ⟨"notice/D011/paragraph/2", notice "PDF369頁 D011(2)", fun c d =>
    c.performance.item = .irregularAntibody →
      (c.priorTransfusion ∧ d.priorTransfusionRecorded) ∨ (c.priorPregnancy ∧ d.priorPregnancyRecorded)⟩

def plateletIgGRule : Rule Context Unit :=
  condition "3" "PDF369頁 D011(3)" fun c => c.performance.item = .plateletIgG →
    c.itpDiagnosisOrFollowup

def pf4Paragraph : Rule Context Unit :=
  condition "4" "PDF369–370頁 D011(4)" fun c =>
    c.performance.item.isPf4 = true → c.hitDiagnosis

def pf4Indication : Rule Context Unit :=
  condition "4/a" "PDF369–370頁 D011(4)ア" fun c =>
    c.performance.item.isPf4 = true → c.hitDiagnosis

def pf4Method : Rule Context Unit :=
  condition "4/i" "PDF370頁 D011(4)イ" fun c =>
    c.performance.item = .pf4Qualitative → c.immunochromatography

def pf4Choice : Rule Context Unit :=
  condition "4/u" "PDF370頁 D011(4)ウ" fun c =>
    c.performance.item.isPf4 = true → ∃ xs, c.pf4Series = some xs ∧
      c.performance ∈ xs ∧ (xs.map (·.id)).Nodup ∧
      (∀ x ∈ xs, x.item.isPf4 = true ∧ c.performance.sameSeries x = some true) ∧
      ((∃ a ∈ xs, a.item = .pf4IgG) → (∃ b ∈ xs, b.item = .pf4IgGmA) →
        (∃ d ∈ xs, d.item = .pf4Qualitative) → c.mainPf4 = some c.performance.id)

def eligibilityRules :=
  [surgeryRule, rhSpecimenRule, irregularRule, plateletIgGRule,
    pf4Paragraph, pf4Indication, pf4Method, pf4Choice]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def rules : List (Rule Context Nat) := ledgerItems.map itemRule

theorem rate_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ p = c.performance.item.points := by
  constructor
  · intro h
    exact h _ (List.mem_map.mpr ⟨_, by cases c.performance.item <;> simp [ledgerItems], rfl⟩) rfl
  · intro h _ hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    intro hi
    simpa [hi] using h

def legacyRequest (i : Item) : SpecimenTests.Request :=
  { code := .d011, number := i.number, branch := i.branch, variant := i.variant
    conditions := { surgery := .thoracicPart10Section7 } }

theorem legacy_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔
      SpecimenTests.assessOne (legacyRequest c.performance.item) = some (.charged p 0) := by
  have evaluated (i : Item) :
      SpecimenTests.assessOne (legacyRequest i) = some (.charged i.points 0) := by cases i <;> rfl
  rw [rate_iff, evaluated]
  simp [eq_comm]

theorem determines : DeterminesOn Eligible rules := by
  intro c _
  exact ⟨⟨c.performance.item.points, (rate_iff ..).mpr rfl⟩,
    fun a b ha hb => ((rate_iff c a).mp ha).trans ((rate_iff c b).mp hb).symm⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 11, number := i.number, variant := i.variant, ordinaryCategory := .immunological }

def toSpecimenItem (kind points : Nat) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := points }

private def sample : Context :=
  { performance := ⟨1, ⟨2, 3, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩,
      .irregularAntibody, none, none, none, none⟩
    operation := some ⟨⟨2, 3, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .k898, some true, some true⟩
    priorPregnancy := True }

example : Eligible sample ∧ Satisfies rules sample 174 := by
  refine ⟨?_, (rate_iff ..).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, surgeryRule, rhSpecimenRule,
    irregularRule, plateletIgGRule, pf4Paragraph, pf4Indication, pf4Method, pf4Choice, condition,
    sample, transfusionSelection, Item.isPf4]

example : ¬ Eligible { sample with operation := none } := by
  intro h
  have surgery := h surgeryRule (by simp [eligibilityRules]) rfl
  cases surgery

end Sanri.MedicalFee.D011
