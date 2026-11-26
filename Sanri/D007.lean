namespace Sanri.MedicalFee.D007

inductive Apolipoprotein where
  | aI | aII | b | cII | cIII | e
  deriving DecidableEq, Repr

inductive OrganicAcid where
  | glutathione | lactate | pyruvate | alphaKetoglutarate
  deriving DecidableEq, Repr

/-- 既存の評価器が受け付ける入力の範囲。 -/
inductive Scope where
  | draw | further | additional | glycemic
  deriving DecidableEq, Repr

/-- D007の項目型。添字で評価器に必要な入力範囲を保つ。 -/
inductive ScopedItem : Scope → Type where
  | totalBilirubin : ScopedItem .draw
  | directOrConjugatedBilirubin : ScopedItem .draw
  | totalProtein : ScopedItem .draw
  | albumin : ScopedItem .draw
  | bun : ScopedItem .draw
  | creatinine : ScopedItem .draw
  | uricAcid : ScopedItem .draw
  | alp : ScopedItem .draw
  | cholinesterase : ScopedItem .draw
  | gammaGT : ScopedItem .draw
  | triglycerides : ScopedItem .draw
  | sodium : ScopedItem .draw
  | chloride : ScopedItem .draw
  | potassium : ScopedItem .draw
  | calcium : ScopedItem .draw
  | magnesium : ScopedItem .draw
  | creatine : ScopedItem .draw
  | glucose : ScopedItem .draw
  | ld : ScopedItem .draw
  | amylase : ScopedItem .draw
  | lap : ScopedItem .draw
  | ck : ScopedItem .draw
  | aldolase : ScopedItem .draw
  | freeCholesterol : ScopedItem .draw
  | iron : ScopedItem .draw
  | bloodKetoneGlucoseChloride : ScopedItem .draw
  | uibcColorimetric : ScopedItem .draw
  | tibcColorimetric : ScopedItem .draw
  | phospholipids : ScopedItem .draw
  | hdlCholesterol : ScopedItem .draw
  | inorganicPhosphorus : ScopedItem .draw
  | phosphate : ScopedItem .draw
  | totalCholesterol : ScopedItem .draw
  | ast : ScopedItem .draw
  | alt : ScopedItem .draw
  | ldlCholesterol : ScopedItem .draw
  | proteinFractionation : ScopedItem .draw
  | copper : ScopedItem .draw
  | lipase : ScopedItem .draw
  | ionizedCalcium : ScopedItem .draw
  | manganese : ScopedItem .draw
  | ketoneBodies : ScopedItem .further
  | apolipoproteins (measured : List Apolipoprotein) : ScopedItem .further
  | adenosineDeaminase : ScopedItem .further
  | guanase : ScopedItem .further
  | organicAcid (substance : OrganicAcid) : ScopedItem .further
  | bileAcids : ScopedItem .further
  | urinarySulfatedBileAcids : ScopedItem .further
  | alpIsoenzymes : ScopedItem .further
  | amylaseIsoenzymes : ScopedItem .further
  | gammaGTIsoenzymes : ScopedItem .further
  | ldIsoenzymes : ScopedItem .further
  | bicarbonate : ScopedItem .further
  | astIsoenzymes : ScopedItem .further
  | lipoproteinFraction : ScopedItem .further
  | ammonia : ScopedItem .further
  | ckIsoenzymes : ScopedItem .further
  | cholesterolFraction : ScopedItem .further
  | ketoneFractions : ScopedItem .further
  | freeFattyAcids : ScopedItem .further
  | lcat : ScopedItem .further
  | g6pd : ScopedItem .further
  | lipoproteinPag : ScopedItem .further
  | glycocholicAcid : ScopedItem .further
  | ckMbMass : ScopedItem .further
  | ldIsoenzyme1 : ScopedItem .further
  | totalCarnitine : ScopedItem .further
  | freeCarnitine : ScopedItem .further
  | alpIsoenzymesAndBap : ScopedItem .further
  | bloodGas : ScopedItem .further
  | ferritinSemiquantitative : ScopedItem .additional
  | ferritinQuantitative : ScopedItem .additional
  | ethanol : ScopedItem .additional
  | lipoproteinA : ScopedItem .additional
  | heparin : ScopedItem .additional
  | kl6 : ScopedItem .additional
  | troponinI : ScopedItem .additional
  | troponinTQualitative : ScopedItem .additional
  | troponinTQuantitative : ScopedItem .additional
  | aluminium : ScopedItem .additional
  | cystatinC : ScopedItem .additional
  | vitaminD25 : ScopedItem .additional
  | pentosidine : ScopedItem .additional
  | inulin : ScopedItem .additional
  | lipoproteinHplc : ScopedItem .additional
  | surfactantProteinA : ScopedItem .additional
  | galactose : ScopedItem .additional
  | surfactantProteinD : ScopedItem .additional
  | glycatedAlbumin : ScopedItem .glycemic
  | anhydroglucitol : ScopedItem .glycemic
  deriving DecidableEq, Repr

/-- 評価器をまたいで扱うときのD007の項目。 -/
abbrev Item := Σ scope, ScopedItem scope

/-- 尿中硫酸抱合型胆汁酸測定の項番は、通知(15)の算定準用先である18を返す。 -/
def ScopedItem.number : ScopedItem scope → Nat
  | .totalBilirubin | .directOrConjugatedBilirubin | .totalProtein | .albumin | .bun | .creatinine | .uricAcid => 1
  | .alp | .cholinesterase | .gammaGT | .triglycerides | .sodium | .chloride | .potassium => 1
  | .calcium | .magnesium | .creatine | .glucose | .ld | .amylase | .lap => 1
  | .ck | .aldolase | .freeCholesterol | .iron | .bloodKetoneGlucoseChloride | .uibcColorimetric | .tibcColorimetric => 1
  | .phospholipids => 2
  | .hdlCholesterol | .inorganicPhosphorus | .phosphate | .totalCholesterol | .ast | .alt => 3
  | .ldlCholesterol | .proteinFractionation => 4
  | .copper => 5
  | .lipase => 6
  | .ionizedCalcium => 7
  | .manganese => 8
  | .ketoneBodies => 9
  | .apolipoproteins _ => 10
  | .adenosineDeaminase => 11
  | .guanase => 12
  | .organicAcid _ | .bileAcids => 13
  | .alpIsoenzymes | .amylaseIsoenzymes | .gammaGTIsoenzymes | .ldIsoenzymes | .bicarbonate => 14
  | .astIsoenzymes | .lipoproteinFraction => 15
  | .ammonia => 16
  | .ckIsoenzymes | .glycatedAlbumin => 17
  | .cholesterolFraction | .urinarySulfatedBileAcids => 18
  | .ketoneFractions | .freeFattyAcids => 19
  | .lcat => 20
  | .g6pd | .lipoproteinPag | .glycocholicAcid | .anhydroglucitol => 21
  | .ckMbMass => 22
  | .ldIsoenzyme1 | .totalCarnitine | .freeCarnitine => 23
  | .alpIsoenzymesAndBap => 24
  | .ferritinSemiquantitative | .ferritinQuantitative => 25
  | .ethanol => 26
  | .lipoproteinA => 27
  | .heparin | .kl6 => 28
  | .troponinI | .troponinTQualitative | .troponinTQuantitative | .aluminium | .cystatinC => 29
  | .vitaminD25 => 30
  | .pentosidine => 31
  | .inulin => 32
  | .lipoproteinHplc => 33
  | .surfactantProteinA | .galactose => 34
  | .bloodGas => 35
  | .surfactantProteinD => 38

def Item.number (item : Item) : Nat := item.2.number

/-- 同じ項番の各項目を引くための関係。 -/
def ItemAt (number : Nat) (item : Item) : Prop := item.number = number

theorem modeled_number (item : Item) :
    (1 ≤ item.number ∧ item.number ≤ 35) ∨ item.number = 38 := by
  obtain ⟨scope, item⟩ := item
  cases item <;> simp [Item.number, ScopedItem.number]

example : ItemAt 18 ⟨.further, .urinarySulfatedBileAcids⟩ := rfl

-- 項番ごとにモデル内の代表を一つ用いた合成例。
example : ([
    ⟨.draw, .totalBilirubin⟩, ⟨.draw, .phospholipids⟩, ⟨.draw, .hdlCholesterol⟩,
    ⟨.draw, .ldlCholesterol⟩, ⟨.draw, .copper⟩, ⟨.draw, .lipase⟩,
    ⟨.draw, .ionizedCalcium⟩, ⟨.draw, .manganese⟩, ⟨.further, .ketoneBodies⟩,
    ⟨.further, .apolipoproteins [.aI]⟩, ⟨.further, .adenosineDeaminase⟩, ⟨.further, .guanase⟩,
    ⟨.further, .organicAcid .lactate⟩, ⟨.further, .alpIsoenzymes⟩, ⟨.further, .astIsoenzymes⟩,
    ⟨.further, .ammonia⟩, ⟨.further, .ckIsoenzymes⟩, ⟨.further, .cholesterolFraction⟩,
    ⟨.further, .ketoneFractions⟩, ⟨.further, .lcat⟩, ⟨.further, .g6pd⟩,
    ⟨.further, .ckMbMass⟩, ⟨.further, .ldIsoenzyme1⟩, ⟨.further, .alpIsoenzymesAndBap⟩,
    ⟨.additional, .ferritinSemiquantitative⟩, ⟨.additional, .ethanol⟩, ⟨.additional, .lipoproteinA⟩,
    ⟨.additional, .heparin⟩, ⟨.additional, .troponinI⟩, ⟨.additional, .vitaminD25⟩,
    ⟨.additional, .pentosidine⟩, ⟨.additional, .inulin⟩, ⟨.additional, .lipoproteinHplc⟩,
    ⟨.additional, .surfactantProteinA⟩, ⟨.further, .bloodGas⟩, ⟨.additional, .surfactantProteinD⟩
    ] : List Item).map Item.number = List.range' 1 35 ++ [38] := by decide

end Sanri.MedicalFee.D007
