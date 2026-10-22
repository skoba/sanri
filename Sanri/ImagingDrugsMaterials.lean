import Sanri.ExaminationDrugsMaterials
import Sanri.Imaging

namespace Sanri.MedicalFee.ImagingDrugsMaterials

/-! Ｅ３００・Ｅ４００・Ｅ４０１。価格は大臣の定めに従って解決済みの算定単位の値。
検査料と同じ薬剤式・有理数の演算を再利用し、画像診断の点数と区分を区別する。 -/
abbrev Amount := ExaminationDrugsMaterials.Amount
abbrev Points := ExaminationDrugsMaterials.Points

def drugPoints (price : Amount) : Nat := ExaminationDrugsMaterials.drugPoints price

def materialPoints (price : Amount) : Points := ExaminationDrugsMaterials.materialPoints price

inductive Region where
  | chest | abdomen | other
  deriving DecidableEq, Repr

structure Film where
  price : Amount
  ageYears : Nat := 20
  plainImaging : Bool := false
  region : Region := .other
  /-- 電子画像管理加算によりフィルム費用を算定できない一連か。 -/
  electronicImageManagementApplies : Bool := false
  deriving DecidableEq, Repr

/-- Ｅ４００：６歳未満の胸部・腹部単純撮影だけ材料価格を1.1倍する。 -/
def filmPoints (f : Film) : Option Points :=
  if f.electronicImageManagementApplies then none
  else if f.ageYears < 6 ∧ f.plainImaging = true ∧ (f.region = .chest ∨ f.region = .abdomen) then
    some ⟨11 * f.price.numerator, 100 * f.price.denominator,
      Nat.mul_pos (by decide) f.price.positiveDenominator⟩
  else some (materialPoints f.price)

structure Context where
  drugPrices : List Amount := []
  films : List Film := []
  /-- フィルム以外の指定材料だけを含める。 -/
  otherMaterialPrices : List Amount := []
  deriving DecidableEq, Repr

structure Assessment where
  drugs : Nat
  films : Points
  otherMaterials : Points
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Points :=
  ExaminationDrugsMaterials.add (ExaminationDrugsMaterials.wholePoints a.drugs)
    (ExaminationDrugsMaterials.add a.films a.otherMaterials)

def assess (c : Context) : Option Assessment := do
  let films ← c.films.mapM filmPoints
  some {
    drugs := (c.drugPrices.map drugPoints).sum
    films := films.foldl ExaminationDrugsMaterials.add (ExaminationDrugsMaterials.wholePoints 0)
    otherMaterials := ExaminationDrugsMaterials.totalMaterials c.otherMaterialPrices }

/-- 分数点数の撮影モデルとも丸めず合算する。base に今回の価格分を二重に含めない。 -/
def Assessment.addTo (a : Assessment) (base : Points) : Points :=
  ExaminationDrugsMaterials.add base a.total

structure CombinedAssessment where
  general : Imaging.Assessment
  prices : Assessment
  deriving DecidableEq, Repr

def CombinedAssessment.total (a : CombinedAssessment) : Points :=
  a.prices.addTo (ExaminationDrugsMaterials.wholePoints a.general.total)

/-- 第４部通則と価格を接続。二重計上を防ぐため既存の第４・５節欄は空を要求する。
電子画像管理の有無は Film 入力にも同じ一連の事実を反映する。 -/
def assessWithGeneralRules (existing : Imaging.Context) (c : Context) : Option CombinedAssessment := do
  if !existing.section4Points.isEmpty || !existing.section5MaterialPoints.isEmpty then none else
    let general ← Imaging.assess existing
    let prices ← assess c
    some ⟨general, prices⟩

example : (List.map (fun yen => drugPoints ⟨yen, 1, by decide⟩) [15, 16, 25, 26]) = [0, 2, 2, 3] := by decide
example : filmPoints { price := ⟨100, 1, by decide⟩, ageYears := 5, plainImaging := true, region := .chest } =
    some ⟨1100, 100, by decide⟩ := by decide
example : filmPoints { price := ⟨100, 1, by decide⟩, ageYears := 5, plainImaging := true, region := .abdomen } =
    some ⟨1100, 100, by decide⟩ := by decide
example : filmPoints { price := ⟨100, 1, by decide⟩, ageYears := 6, plainImaging := true, region := .chest } =
    some ⟨100, 10, by decide⟩ := by decide
example : filmPoints { price := ⟨100, 1, by decide⟩, ageYears := 5, region := .chest } =
    some ⟨100, 10, by decide⟩ := by decide
example : filmPoints { price := ⟨15, 1, by decide⟩, electronicImageManagementApplies := true } = none := by decide
example : materialPoints ⟨15, 1, by decide⟩ = ⟨15, 10, by decide⟩ := rfl

end Sanri.MedicalFee.ImagingDrugsMaterials
