import Sanri.Examinations

namespace Sanri.MedicalFee.ExaminationDrugsMaterials

/-! Ｄ５００・Ｄ６００。薬価・材料価格は大臣の定めにより解決済みの金額を入力する。
金額は非負有理数（円）とし、15円の判定前に丸めない。算定単位は呼出元が解決する。 -/
structure Amount where
  numerator : Nat
  denominator : Nat
  positiveDenominator : 0 < denominator
  deriving DecidableEq, Repr

/-- Ｄ５００：15円以下は０、超過分÷10を切り上げて１点を加える。 -/
def drugPoints (price : Amount) : Nat :=
  if price.numerator ≤ 15 * price.denominator then 0 else
    let excess := price.numerator - 15 * price.denominator
    let divisor := 10 * price.denominator
    (excess + divisor - 1) / divisor + 1

/-- 点数にも非負有理数を使い、材料の端数を丸めない。 -/
abbrev Points := Amount

def materialPoints (price : Amount) : Points :=
  ⟨price.numerator, 10 * price.denominator, Nat.mul_pos (by decide) price.positiveDenominator⟩

def add (a b : Points) : Points :=
  ⟨a.numerator * b.denominator + b.numerator * a.denominator,
   a.denominator * b.denominator, Nat.mul_pos a.positiveDenominator b.positiveDenominator⟩

def wholePoints (n : Nat) : Points := ⟨n, 1, by decide⟩
def totalMaterials (prices : List Amount) : Points :=
  (prices.map materialPoints).foldl add (wholePoints 0)

structure Assessment where
  general : Examinations.Assessment
  drugs : Nat
  materials : Points
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Points :=
  add (wholePoints (a.general.total + a.drugs)) a.materials

inductive Result where
  | calculated (details : Assessment)
  | requiresOutsourcingRule
  deriving DecidableEq, Repr

/-- 二重合算を防ぐため既存の日次入力の薬剤・材料欄は空にして使う。
特則がある薬剤はＤ５００の通常式に入れず、別の特則モデルで解決する。 -/
def assessDaily (existing : Examinations.DailyContext) (drugPrices materialPrices : List Amount) :
    Option Result := do
  if existing.drugs != .none || !existing.section6MaterialPoints.isEmpty then none else
    match ← Examinations.assess existing with
    | .requiresOutsourcingRule => some .requiresOutsourcingRule
    | .calculated general => some (.calculated {
        general := general
        drugs := (drugPrices.map drugPoints).sum
        materials := totalMaterials materialPrices })

example : (List.map (fun yen => drugPoints ⟨yen, 1, by decide⟩) [0, 14, 15, 16, 25, 26, 35, 36]) =
    [0, 0, 0, 2, 2, 3, 3, 4] := by decide
example : drugPoints ⟨1501, 100, by decide⟩ = 2 := by decide
example : drugPoints ⟨2501, 100, by decide⟩ = 3 := by decide
example : materialPoints ⟨15, 1, by decide⟩ = ⟨15, 10, by decide⟩ := rfl
example : (assessDaily {} [⟨26, 1, by decide⟩] [⟨15, 1, by decide⟩]) =
    some (.calculated ⟨⟨0, 0, 0, 0, 0, 0⟩, 3, ⟨15, 10, by decide⟩⟩) := by decide
example : assessDaily { drugs := .ordinary 3 } [] [] = none := by decide
example : assessDaily { section6MaterialPoints := [1] } [] [] = none := by decide

end Sanri.MedicalFee.ExaminationDrugsMaterials
