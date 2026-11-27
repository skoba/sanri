import Sanri.D000
import Sanri.D001
import Sanri.UrineSediment
import Sanri.D003
import Sanri.D004
import Sanri.D004Tumor
import Sanri.D004Methylation
import Sanri.BloodMorphology
import Sanri.D006
import Sanri.D006Leukemia
import Sanri.D006Genetic
import Sanri.D006Chromosome
import Sanri.D006GeneTests
import Sanri.D006Oncology
import Sanri.D006Profiling
import Sanri.D006Targeted
import Sanri.D006PlasmaPanel
import Sanri.D006Late
import Sanri.D007
import Sanri.D008
import Sanri.D009
import Sanri.D010
import Sanri.D011
import Sanri.D012
import Sanri.D013
import Sanri.D014
import Sanri.D015
import Sanri.D016
import Sanri.D017
import Sanri.D018
import Sanri.D019
import Sanri.D019Yeast
import Sanri.D020
import Sanri.D021
import Sanri.D022
import Sanri.D023Outpatient
import Sanri.D023Other

namespace Sanri.MedicalFee

def UrineSediment.Context.judgmentTest (c : UrineSediment.Context) : SpecimenJudgment.Test :=
  { major := 2, suffix := if c.performance.item = .flow then 2 else 0
    ordinaryCategory := .urineFecal }

def D007.Item.judgmentTest (item : D007.Item) : SpecimenJudgment.Test :=
  { major := 7, number := item.number, ordinaryCategory := .biochemicalI }

namespace SpecimenJudgment

/-! 通常区分の振分けと、各実施料モジュールが公開する既存の入力の一致。 -/

theorem routing_D000 :
    standardizedCategoryFor (D000.judgmentTest) = categoryFor (D000.judgmentTest) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D001 (c : D001.Context) :
    standardizedCategoryFor (D001.judgmentTest c) = categoryFor (D001.judgmentTest c) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_UrineSediment (c : UrineSediment.Context) :
    standardizedCategoryFor (c.judgmentTest) = categoryFor (c.judgmentTest) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D003 (c : D003.Context) :
    standardizedCategoryFor (D003.judgmentTest c) = categoryFor (D003.judgmentTest c) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D004 (i : D004.Item) (ordinary : Category) :
    standardizedCategoryFor (D004.judgmentTest i ordinary) = categoryFor (D004.judgmentTest i ordinary) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D004Tumor (i : D004Tumor.Item) (ordinary : Category) :
    standardizedCategoryFor (D004Tumor.judgmentTest i ordinary) = categoryFor (D004Tumor.judgmentTest i ordinary) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D004Methylation (ordinary : Category) :
    standardizedCategoryFor (D004Methylation.judgmentTest ordinary) = categoryFor (D004Methylation.judgmentTest ordinary) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_BloodMorphology (i : BloodMorphology.Item) (reported : Bool) :
    standardizedCategoryFor (i.judgmentTest reported) = categoryFor (i.judgmentTest reported) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006 (i : D006.Item) :
    standardizedCategoryFor (D006.judgmentTest i) = categoryFor (D006.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006_2 (ordinary : Category) :
    standardizedCategoryFor (D006Leukemia.D006_2.judgmentTest ordinary) = categoryFor (D006Leukemia.D006_2.judgmentTest ordinary) :=
  by cases ordinary <;> rfl

theorem routing_D006_3 (i : D006Leukemia.D006_3.Item) (ordinary : Category) :
    standardizedCategoryFor (D006Leukemia.D006_3.judgmentTest i ordinary) = categoryFor (D006Leukemia.D006_3.judgmentTest i ordinary) :=
  by cases ordinary <;> rfl

theorem routing_D006Genetic (i : D006Genetic.Item) :
    standardizedCategoryFor (D006Genetic.judgmentTest i) = categoryFor (D006Genetic.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006Chromosome (i : D006Chromosome.Item) :
    standardizedCategoryFor (D006Chromosome.judgmentTest i) = categoryFor (D006Chromosome.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006_6_to_9 (i : D006GeneTests.Item) :
    standardizedCategoryFor (D006GeneTests.judgmentTest i) = categoryFor (D006GeneTests.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006_10 :
    standardizedCategoryFor (D006GeneTests.Ccr4.judgmentTest) = categoryFor (D006GeneTests.Ccr4.judgmentTest) :=
  rfl

theorem routing_D006_11 :
    standardizedCategoryFor (D006GeneTests.Fusion.judgmentTest) = categoryFor (D006GeneTests.Fusion.judgmentTest) :=
  rfl

theorem routing_D006_12 :
    standardizedCategoryFor (D006GeneTests.Egfr.judgmentTest) = categoryFor (D006GeneTests.Egfr.judgmentTest) :=
  rfl

theorem routing_D006_13 (i : D006GeneTests.ResidualDisease.Item) :
    standardizedCategoryFor (D006GeneTests.ResidualDisease.judgmentTest i) = categoryFor (D006GeneTests.ResidualDisease.judgmentTest i) :=
  rfl

theorem routing_D006_14_to_16 (i : D006Oncology.Item) :
    standardizedCategoryFor (D006Oncology.judgmentTest i) = categoryFor (D006Oncology.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006_17 (i : D006Oncology.Pharmacogenetics.Item) :
    standardizedCategoryFor (D006Oncology.Pharmacogenetics.judgmentTest i) = categoryFor (D006Oncology.Pharmacogenetics.judgmentTest i) :=
  rfl

theorem routing_D006_18 (i : D006Oncology.Brca.Item) :
    standardizedCategoryFor (D006Oncology.Brca.judgmentTest i) = categoryFor (D006Oncology.Brca.judgmentTest i) :=
  rfl

theorem routing_D006Profiling (i : D006Profiling.Item) :
    standardizedCategoryFor (D006Profiling.judgmentTest i) = categoryFor (D006Profiling.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006Targeted (i : D006Targeted.Item) :
    standardizedCategoryFor (D006Targeted.judgmentTest i) = categoryFor (D006Targeted.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006PlasmaPanel (i : D006PlasmaPanel.Item) :
    standardizedCategoryFor (D006PlasmaPanel.judgmentTest i) = categoryFor (D006PlasmaPanel.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D006Late (i : D006Late.Item) :
    standardizedCategoryFor (D006Late.judgmentTest i) = categoryFor (D006Late.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D007 (i : D007.Item) :
    standardizedCategoryFor (i.judgmentTest) = categoryFor (i.judgmentTest) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D008 (i : D008.Item) :
    standardizedCategoryFor (D008.judgmentTest i) = categoryFor (D008.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D009 (i : D009.Item) :
    standardizedCategoryFor (D009.judgmentTest i) = categoryFor (D009.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D010 (i : D010.Item) :
    standardizedCategoryFor (D010.judgmentTest i) = categoryFor (D010.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D011 (i : D011.Item) :
    standardizedCategoryFor (D011.judgmentTest i) = categoryFor (D011.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D012 (i : D012.Item) :
    standardizedCategoryFor (D012.judgmentTest i) = categoryFor (D012.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D013 (i : D013.Item) :
    standardizedCategoryFor (D013.judgmentTest i) = categoryFor (D013.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D014 (i : D014.Item) :
    standardizedCategoryFor (D014.judgmentTest i) = categoryFor (D014.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D015 (i : D015.Item) (reported : Bool) :
    standardizedCategoryFor (D015.judgmentTest i reported) = categoryFor (D015.judgmentTest i reported) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D016 (i : D016.Item) :
    standardizedCategoryFor (D016.judgmentTest i) = categoryFor (D016.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D017 (i : D017.Item) :
    standardizedCategoryFor (D017.judgmentTest i) = categoryFor (D017.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D018 (i : D018.Item) :
    standardizedCategoryFor (D018.judgmentTest i) = categoryFor (D018.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D019 (i : D019.Item) :
    standardizedCategoryFor (D019.judgmentTest i) = categoryFor (D019.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D019Yeast :
    standardizedCategoryFor (D019Yeast.judgmentTest) = categoryFor (D019Yeast.judgmentTest) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D020 (i : D020.Item) :
    standardizedCategoryFor (D020.judgmentTest i) = categoryFor (D020.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D021 :
    standardizedCategoryFor (D021.judgmentTest) = categoryFor (D021.judgmentTest) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D022 :
    standardizedCategoryFor (D022.judgmentTest) = categoryFor (D022.judgmentTest) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D023Outpatient (i : D023.OutpatientTest) :
    standardizedCategoryFor (i.judgmentTest) = categoryFor (i.judgmentTest) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D023Other (i : D023Other.Item) :
    standardizedCategoryFor (D023Other.judgmentTest i) = categoryFor (D023Other.judgmentTest i) :=
  standardizedCategoryFor_legacy _ rfl

theorem routing_D023Reference (r : D023Reference) :
    standardizedCategoryFor r.judgmentTest = some .microbiological := rfl

end SpecimenJudgment
end Sanri.MedicalFee
