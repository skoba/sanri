import Sanri.SpecimenCrossDivision

namespace Sanri.MedicalFee.SpecimenSelectionInventory

open Sanri.Logic Sanri.History SpecimenCrossDivision

abbrev ItemKey := String × String

inductive UnitKind where
  | simultaneous | specimen | draw | day | month | series | week | examination | organism | virus | specimenOrigin | unresolved
  deriving DecidableEq, Repr

structure Entry where
  id : String
  source : SourceRef
  members : List ItemKey
  unit : UnitKind
  /-- 発動する最小件数と算定件数の上限。等号として使えるかは条項ごとに確認する。 -/
  cardinality : Option (Nat × Nat)
  /-- 算定側・除外側の指定が確認されたか。未確認は none。 -/
  directed : Option Bool
  inAuditIndex : Bool

private def entry (id : String) (unit : UnitKind)
    (cardinality : Option (Nat × Nat)) (members : List ItemKey)
    (inAuditIndex : Bool := true) (directed : Option Bool := none) : Entry :=
  let primary := id.startsWith "primary/"
  let source : SourceRef := if primary then
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度", id, .unchecked, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩
  else
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", id, .unchecked, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩
  ⟨id, source, members, unit, cardinality, directed, inAuditIndex⟩

/-- 外部照合索引の構成項目。部分経路の相手や空欄を含む。 -/
def inventory : List Entry := [
  entry "notice/D001/paragraph/3" .simultaneous (some (2, 1))
    [("D001", "albuminQuantitative"), ("D001", "transferrin"), ("D001", "typeIVCollagen")] true (some false),
  entry "notice/D001/paragraph/4/i" .unresolved none
    [("D001", "trypsinogen2"), ("D007", "amylase"), ("D007", "amylaseIsoenzymes"), ("D007", "lipase"), ("D007", "trypsin"), ("D009", "8")],
  entry "notice/D001/paragraph/6/i" .month none
    [("D001", "prostaglandinEMajorMetabolite"), ("D003", "calprotectin")],
  entry "notice/D001/paragraph/9/i" .unresolved none
    [("D001", "lFabp"), ("D001", "ngal")],
  entry "notice/D002/paragraph/5" .unresolved (some (2, 1))
    [("D002", "microscopy"), ("D002-2", "flow")] true (some false),
  entry "notice/D003/paragraph/4/u" .month none
    [],
  entry "notice/D004/paragraph/1" .unresolved none
    [("D004", "jointFluid"), ("D017", "heatedAmoeba"), ("D017", "otherMicroscopy"), ("D017", "specializedMicroscopy")],
  entry "notice/D004/paragraph/13/i" .unresolved none
    [("D004", "amyloidRatio"), ("D004", "phosphoTau"), ("D004", "phosphoTauAmyloidRatio")],
  entry "notice/D004-2/paragraph/7" .month none
    [("D004-2", "complex"), ("D004-2", "drugAid"), ("D004-2", "otherSimple"), ("D006-14", "flt3"), ("D006-16", "jak2"), ("D006-2", "hematopoieticTumorGene"), ("D006-6", "immuneRearrangement")],
  entry "notice/D004-2/paragraph/8" .month none
    [("D004-2", "drugAid"), ("D006-12", "plasmaEgfr"), ("D006-24", "lungPanel")],
  entry "notice/D004-2/paragraph/9" .unresolved none
    [("D004-2", "drugAid"), ("D006-24", "lungPanel")],
  entry "notice/D004-2/paragraph/10" .unresolved none
    [],
  entry "notice/D004-2/paragraph/11" .unresolved none
    [("D004-2", "complex"), ("D004-2", "drugAid"), ("D006-18", "tumorCells")],
  entry "notice/D005/paragraph/3" .specimen (some (2, 1))
    [("D005", "automatedDifferential"), ("D005", "eosinophilCount"), ("D005", "microscopicDifferential")] true (some false),
  entry "notice/D005/paragraph/7" .unresolved none
    [("D005", "bloodMicroorganisms"), ("D005", "dnaContainingRedCellCount")],
  entry "notice/D005/paragraph/9" .month none
    [("D005", "hemoglobinA1c"), ("D007", "anhydroglucitol"), ("D007", "glycatedAlbumin")],
  entry "notice/D006/paragraph/8/i" .simultaneous none
    [("D006", "fibrinMonomer"), ("D006", "prothrombinFragment"), ("D006", "tat")],
  entry "primary/D006-4/note/2" .draw none
    [],
  entry "notice/D006-10/paragraph/unnumbered" .unresolved none
    [("D006-10", "ccr4"), ("N002", "5")] false,
  entry "notice/D006-15/paragraph/3" .simultaneous none
    [("D006-15", "bladder"), ("N004", "2")],
  entry "notice/D006-22/paragraph/3" .month none
    [("D004-2", "drugAid"), ("D004-2", "otherSimple"), ("D006-22", "plasmaRas")],
  entry "notice/D006-24/paragraph/2" .unresolved none
    [("D004-2", "drugAid"), ("D006-12", "plasmaEgfr"), ("D006-24", "lungPanel")],
  entry "notice/D006-27/paragraph/3/e" .unresolved none
    [("D006-27", "alk"), ("N002", "6"), ("N005-2", "heading")] false,
  entry "notice/D006-27/paragraph/5/e" .unresolved none
    [("D006-27", "ntrk"), ("D006-18", "blood"), ("D006-18", "tumorCells")] false,
  entry "notice/D006-27/paragraph/6/e" .unresolved none
    [("D006-27", "ras"), ("D006-22", "plasmaRas")] false (some true),
  entry "notice/D006-27/paragraph/10/u" .unresolved none
    [("D006-27", "microsatellite"), ("D006-18", "tumorCells")] false,
  entry "notice/D007/paragraph/2" .simultaneous (some (2, 1))
    [("D007", "calcium"), ("D007", "ionizedCalcium")] true (some false),
  entry "notice/D007/paragraph/3" .simultaneous (some (2, 1))
    [("D007", "tibcColorimetric"), ("D007", "uibcColorimetric")] true (some false),
  entry "notice/D007/paragraph/5" .unresolved (some (3, 2))
    [("D007", "hdlCholesterol"), ("D007", "ldlCholesterol"), ("D007", "totalCholesterol")] true (some false),
  entry "notice/D007/paragraph/7" .unresolved (some (3, 2))
    [("D007", "albumin"), ("D007", "proteinFractionation"), ("D007", "totalProtein")] true (some false),
  entry "notice/D007/paragraph/9" .unresolved none
    [("D007", "ketoneBodies"), ("D007", "ketoneFractions")],
  entry "notice/D007/paragraph/12" .specimen none
    [("D007", "bicarbonate"), ("D007", "bloodGas")],
  entry "notice/D007/paragraph/15" .simultaneous none
    [("D007", "bileAcids"), ("D007", "urinarySulfatedBileAcids")],
  entry "notice/D007/paragraph/17/e" .specimen none
    [("D007", "freeCarnitine"), ("D007", "totalCarnitine"), ("D010", "8/ha"), ("D010", "8/i"), ("D010", "8/ni"), ("D010", "8/ro")],
  entry "notice/D007/paragraph/18" .unresolved none
    [("D007", "alpIsoenzymesAndBap"), ("D008", "bap")],
  entry "notice/D007/paragraph/21" .unresolved none
    [("D007", "kl6"), ("D007", "surfactantProteinA"), ("D007", "surfactantProteinD")],
  entry "notice/D007/paragraph/22" .month none
    [("D007", "troponinI"), ("D007", "troponinTQualitative"), ("D007", "troponinTQuantitative")],
  entry "notice/D007/paragraph/23/i" .unresolved none
    [("D007", "cystatinC"), ("D007", "pentosidine")],
  entry "notice/D007/paragraph/26" .unresolved none
    [("D007", "creatinine"), ("D007", "inulin")],
  entry "notice/D007/paragraph/27" .unresolved none
    [("D007", "hFabpQualitative"), ("D007", "hFabpQuantitative"), ("D007", "myoglobinQualitative"), ("D007", "myoglobinQuantitative")],
  entry "notice/D007/paragraph/30" .unresolved none
    [("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/38" .day none
    [],
  entry "notice/D007/paragraph/40/i" .unresolved none
    [("D007", "hyaluronicAcid"), ("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/41/i" .unresolved none
    [("D007", "autotaxin"), ("D007", "hyaluronicAcid"), ("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/42/i" .unresolved none
    [("D007", "autotaxin"), ("D007", "ck18f"), ("D007", "hyaluronicAcid"), ("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/43/u" .unresolved none
    [("D007", "autotaxin"), ("D007", "ck18f"), ("D007", "elfScore"), ("D007", "mac2"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/46/i" .month none
    [("D003", "calprotectin"), ("D007", "lrg")],
  entry "notice/D007/paragraph/47" .unresolved none
    [("D007", "procalcitoninQuantitative"), ("D007", "procalcitoninSemiquantitative"), ("D012", "endotoxin")],
  entry "notice/D007/paragraph/48/i" .unresolved none
    [("D007", "presepsin"), ("D007", "procalcitoninQuantitative"), ("D007", "procalcitoninSemiquantitative"), ("D012", "endotoxin")],
  entry "notice/D008/paragraph/3" .unresolved none
    [("D008", "reninActivity"), ("D008", "reninQuantitative")],
  entry "notice/D008/paragraph/4" .simultaneous none
    [],
  entry "notice/D008/paragraph/6/i" .unresolved none
    [("D008", "hcgBeta"), ("D008", "hcgQualitative"), ("D008", "hcgQuantitative"), ("D008", "hcgSemiquantitative")],
  entry "notice/D008/paragraph/7/i" .week none
    [("D008", "anp"), ("D008", "bnp"), ("D008", "ntProBnp")],
  entry "notice/D008/paragraph/13" .unresolved none
    [("D008", "ntx"), ("D008", "osteocalcin"), ("D008", "urineDpd")],
  entry "notice/D008/paragraph/15" .unresolved none
    [("D008", "ntx"), ("D008", "osteocalcin"), ("D008", "tracp5b"), ("D008", "urineDpd")],
  entry "notice/D008/paragraph/16" .unresolved none
    [("D007", "alpIsoenzymesPag"), ("D008", "bap"), ("D008", "intactPinp"), ("D008", "pinp")],
  entry "notice/D008/paragraph/18" .unresolved none
    [("D008", "betaCtx"), ("D008", "urineBetaCtx")],
  entry "notice/D008/paragraph/19" .simultaneous none
    [("D008", "estradiol"), ("D008", "estriol"), ("D008", "estrogenQuantitative"), ("D008", "estrogenSemiquantitative")],
  entry "notice/D008/paragraph/25" .unresolved none
    [("D008", "metanephrine"), ("D008", "normetanephrine")],
  entry "notice/D008/paragraph/26/i" .unresolved none
    [("D008", "igfbp3"), ("D008", "somatomedinC")],
  entry "notice/D008/paragraph/27/i" .unresolved none
    [("D008", "freeMetanephrineFractions"), ("D008", "metanephrine"), ("D008", "metanephrineFractions"), ("D008", "normetanephrine")],
  entry "notice/D009/paragraph/3" .unresolved none
    [("D009", "3"), ("D009", "7")],
  entry "notice/D009/paragraph/5" .unresolved none
    [("D009", "11"), ("D009", "28")],
  entry "notice/D009/paragraph/8" .simultaneous none
    [("D009", "12"), ("D009", "21")],
  entry "notice/D009/paragraph/10/i" .unresolved none
    [("D009", "18"), ("D009", "6")],
  entry "notice/D009/paragraph/15" .unresolved none
    [("D009", "14"), ("D009", "24")],
  entry "notice/D009/paragraph/20/u" .unresolved (some (2, 1))
    [("D009", "17"), ("D009", "31"), ("D009", "32"), ("D009", "9")] true (some false),
  entry "notice/D009/paragraph/21/e" .unresolved (some (2, 1))
    [("D009", "17"), ("D009", "32")] true (some false),
  entry "notice/D009/paragraph/21/u" .unresolved (some (2, 1))
    [("D009", "32"), ("D009", "9")] true (some false),
  entry "notice/D009/paragraph/24/i" .unresolved none
    [("D009", "15"), ("D009", "3"), ("D009", "35"), ("D009", "7")],
  entry "notice/D011/paragraph/4/u" .series none
    [("D011", "pf4IgG"), ("D011", "pf4IgGmA"), ("D011", "pf4Qualitative")],
  entry "notice/D012/paragraph/2" .unresolved none
    [("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi")],
  entry "notice/D012/paragraph/4" .simultaneous none
    [("D012", "stoolAdenovirus"), ("D012", "stoolRotavirusQual"), ("D012", "stoolRotavirusQuant")],
  entry "notice/D012/paragraph/12" .simultaneous none
    [("D012", "rapidGroupAStrep"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D012/paragraph/23" .unresolved none
    [("D012", "pneumoniaeIgA"), ("D012", "pneumoniaeIgG"), ("D012", "pneumoniaeIgM")],
  entry "notice/D012/paragraph/28" .unresolved none
    [("D012", "ecoliO157Antibody"), ("D012", "ecoliO157Antigen"), ("D018", "gastrointestinal")],
  entry "notice/D012/paragraph/30" .unresolved none
    [("D012", "ecoliSerotype"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D012/paragraph/31/i" .unresolved none
    [("D012", "pneumococcusCapsule"), ("D012", "pneumococcusWall")],
  entry "notice/D012/paragraph/32" .simultaneous none
    [("D012", "gonococcusAntigen"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D012/paragraph/34" .unresolved none
    [("D012", "herpesAntigen"), ("D012", "herpesCornea"), ("D012", "herpesGenital"), ("D012", "herpesSkin")],
  entry "notice/D012/paragraph/36" .unresolved none
    [("D012", "arabinitol"), ("D012", "aspergillusAntigen"), ("D012", "aspergillusIgG"), ("D012", "betaGlucan"), ("D012", "candidaQual"), ("D012", "candidaQuant"), ("D012", "candidaSemi"), ("D012", "cryptococcusQual"), ("D012", "cryptococcusSemi")],
  entry "notice/D012/paragraph/38/i" .virus none
    [],
  entry "notice/D012/paragraph/38/u" .unresolved none
    [("D012", "classSpecificTiter"), ("D012", "viralTiter")],
  entry "notice/D012/paragraph/43/i" .unresolved none
    [("D012", "pertussisAntigen"), ("D023", "pertussisGroup"), ("D023", "respiratoryPanelCovid"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D012/paragraph/47/i" .unresolved none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "influenzaAntigen")],
  entry "notice/D012/paragraph/48/e" .unresolved none
    [("D012", "dengueAntigen"), ("D012", "dengueCombo")],
  entry "notice/D012/paragraph/53/i" .unresolved none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "rsAntigen")],
  entry "notice/D012/paragraph/54/i" .unresolved none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "influenzaAntigen"), ("D012", "rsAntigen")],
  entry "notice/D012/paragraph/56" .unresolved none
    [("D012", "toxoplasmaAntibody"), ("D012", "toxoplasmaAvidity")],
  entry "notice/D012/paragraph/59" .unresolved none
    [("D012", "hiv1WesternBlot"), ("D012", "hiv2WesternBlot"), ("D012", "hivSpecific")],
  entry "notice/D013/paragraph/5" .simultaneous none
    [("D013", "hbcAntibody"), ("D013", "hbcIgM")],
  entry "notice/D013/paragraph/6" .simultaneous none
    [("D013", "haAntibody"), ("D013", "haIgM")],
  entry "notice/D013/paragraph/8" .simultaneous none
    [("D013", "hbcrAntigen"), ("D023", "hbvQuantity")],
  entry "notice/D014/paragraph/1" .unresolved (some (3, 2))
    [("D014", "c1q"), ("D014", "galactoseQual"), ("D014", "galactoseQuant"), ("D014", "iggRf"), ("D014", "mmp3"), ("D014", "rf"), ("D014", "rfComplex")] true (some false),
  entry "notice/D014/paragraph/2" .unresolved none
    [("D014", "galactoseQual"), ("D014", "galactoseQuant"), ("D014", "rf")] true (some false),
  entry "notice/D014/paragraph/3" .unresolved none
    [("D014", "microsomal"), ("D014", "tpo")],
  entry "notice/D014/paragraph/6" .unresolved none
    [("D014", "ars"), ("D014", "jo1Qual"), ("D014", "jo1Quant"), ("D014", "jo1Semi")],
  entry "notice/D014/paragraph/7/i" .unresolved (some (2, 1))
    [("D014", "c1q"), ("D014", "ccpQual"), ("D014", "ccpQuant"), ("D014", "galactoseQual"), ("D014", "galactoseQuant"), ("D014", "iggRf"), ("D014", "mmp3"), ("D014", "rfComplex")] true (some false),
  entry "notice/D014/paragraph/8" .simultaneous none
    [("D014", "trab"), ("D014", "tsab")],
  entry "notice/D014/paragraph/10" .unresolved none
    [("D014", "beta2Igg"), ("D014", "beta2Igm"), ("D014", "cardiolipinComplex"), ("D014", "cardiolipinIgg"), ("D014", "cardiolipinIgm")],
  entry "notice/D014/paragraph/12" .unresolved none
    [("D014", "igg2Nephelometry"), ("D014", "igg2Tia")],
  entry "notice/D014/paragraph/16/i" .unresolved none
    [("D014", "dsg1"), ("D014", "dsg3")],
  entry "notice/D014/paragraph/19/i" .unresolved none
    [("D014", "dsg1"), ("D014", "dsg3")],
  entry "notice/D014/paragraph/23/i" .unresolved none
    [("D014", "bp180"), ("D014", "dsg1"), ("D014", "dsg3"), ("D014", "skinCombo")],
  entry "notice/D014/paragraph/24/i" .unresolved none
    [("D014", "achr"), ("D014", "musk")],
  entry "notice/D014/paragraph/27/i" .unresolved none
    [("D014", "achr"), ("D014", "musk")],
  entry "notice/D015/paragraph/2" .unresolved none
    [("D015", "crp"), ("D015", "crpQual"), ("D015", "saa")],
  entry "notice/D015/paragraph/4/i" .specimen none
    [("D015", "drugImmunofixation"), ("D015", "specificAntiserum"), ("D015", "wholeAntiserum")],
  entry "notice/D015/paragraph/10" .unresolved none
    [("D007", "igfbp1Qualitative"), ("D015", "fibronectin")],
  entry "notice/D015/paragraph/11/i" .month none
    [("D015", "scca2"), ("D015", "tarc")],
  entry "notice/D015/paragraph/12/i" .simultaneous none
    [("D015", "lightChain"), ("D015", "specificAntiserum"), ("D015", "wholeAntiserum")],
  entry "primary/D017/note/unnumbered/1" .specimen (some (2, 1))
    [("D002", "microscopy"), ("D002-2", "flow"), ("D017", "heatedAmoeba"), ("D017", "otherMicroscopy"), ("D017", "specializedMicroscopy")] true (some false),
  entry "notice/D017/paragraph/2" .examination none
    [("D017", "heatedAmoeba"), ("D017", "otherMicroscopy"), ("D017", "specializedMicroscopy")],
  entry "notice/D018/paragraph/1/e" .organism none
    [("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "respiratory")],
  entry "notice/D018/paragraph/1/u" .specimen none
    [("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D023/paragraph/1/a" .unresolved none
    [("D012", "trachomatisAntigen"), ("D023", "trachomatis")],
  entry "notice/D023/paragraph/2/a" .unresolved none
    [("D012", "gonococcusAntigen"), ("D023", "gonococcus")],
  entry "notice/D023/paragraph/3" .unresolved none
    [("D012", "rapidGroupAStrep"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple"), ("D023", "groupAStrep")],
  entry "notice/D023/paragraph/5/a" .unresolved none
    [("D012", "gonococcusAntigen"), ("D012", "trachomatisAntigen"), ("D023", "gonococcus"), ("D023", "gonococcusTrachomatis"), ("D023", "trachomatis")],
  entry "notice/D023/paragraph/10/i" .unresolved none
    [("D023", "hpv"), ("D023", "hpvSimpleGenotype")],
  entry "notice/D023/paragraph/16/u" .specimenOrigin none
    [],
  entry "notice/D023/paragraph/36/i" .series none
    [("D012", "influenzaAntigen"), ("D012", "metapneumovirusAntigen"), ("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi"), ("D012", "nonStoolAdenovirus"), ("D012", "pneumococcusCapsule"), ("D012", "rsAntigen"), ("D023", "legionella"), ("D023", "pneumoniaResistancePanel"), ("D023", "respiratorySingle")],
  entry "notice/D023/paragraph/37/e" .series none
    [("D012", "influenzaAntigen"), ("D012", "metapneumovirusAntigen"), ("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi"), ("D012", "nonStoolAdenovirus"), ("D012", "pertussisAntibody"), ("D012", "pertussisAntigen"), ("D012", "pertussisQual"), ("D012", "pertussisSemi"), ("D012", "pneumoniaeIgA"), ("D012", "pneumoniaeIgG"), ("D012", "pneumoniaeIgM"), ("D012", "rsAntigen"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D023/paragraph/37/e/u" .series none
    [("D023", "respiratoryPanelCovid"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D023/paragraph/37/u" .series none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "influenzaAntigen"), ("D012", "metapneumovirusAntigen"), ("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi"), ("D012", "nonStoolAdenovirus"), ("D012", "pertussisAntibody"), ("D012", "pertussisAntigen"), ("D012", "pertussisQual"), ("D012", "pertussisSemi"), ("D012", "pneumoniaeIgA"), ("D012", "pneumoniaeIgG"), ("D012", "pneumoniaeIgM"), ("D012", "rsAntigen"), ("D023", "respiratoryPanelCovid")],
  entry "notice/D023/paragraph/37/u/ko" .series none
    [("D023", "respiratoryPanelCovid"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D023/paragraph/39/i" .series none
    [],
  entry "notice/D023-2/paragraph/1/i" .unresolved none
    [],
  entry "notice/D023-2/paragraph/4/i" .unresolved none
    [("D023-2", "pbp2"), ("D023-2", "rapidPbp2")],
  entry "notice/ch2-part3-section4/general/3" .day none
    []
]

/-- 条項の規則IDは一覧のIDと照合済み。射影は確認した区分別関数名を保持する。
原実施からの生成は SpecimenRawDay で接続した範囲を示す。 -/
structure Evidence where
  unitWording : Option String := none
  projection : Option String := none
  rawGeneration : Bool := false

def Entry.clauseConstraint (g : Entry) : String := g.id

def Entry.evidence (g : Entry) : Evidence :=
  match g.id with
  | "notice/D001/paragraph/3" => ⟨some "同時", some "renalSimultaneousGroup", false⟩
  | "notice/D001/paragraph/4/i" => ⟨some "併せて実施", some "pancreaticGroup", false⟩
  | "notice/D001/paragraph/6/i" => ⟨some "同一月中", some "colitisChoice", false⟩
  | "notice/D001/paragraph/9/i" => ⟨some "併せて実施", some "urineSpecialSelectionInput", false⟩
  | "notice/D002/paragraph/5" => ⟨some "併せて実施", some "sedimentMethodGroup", false⟩
  | "notice/D003/paragraph/4/u" => ⟨some "同一月中", some "colonoscopyGroup", false⟩
  | "notice/D004/paragraph/1" => ⟨some "併せて実施", some "jointFluidGroup", false⟩
  | "notice/D004/paragraph/13/i" => ⟨some "併せて行った", some "csfRatioGroup", false⟩
  | "notice/D004-2/paragraph/7" => ⟨some "同一月中", some "hematologicMonthlyGroup", false⟩
  | "notice/D004-2/paragraph/8" => ⟨some "同一月中", some "tumorMonthlyGroups", false⟩
  | "notice/D004-2/paragraph/9" => ⟨some "併せて行った", some "tumorCombinedGroup", false⟩
  | "notice/D004-2/paragraph/10" => ⟨some "併せて行った", some "tumorCombinedGroup", false⟩
  | "notice/D004-2/paragraph/11" => ⟨some "併せて行った", some "tumorCombinedGroup", false⟩
  | "notice/D005/paragraph/3" => ⟨some "同一検体", some "morphologyGroups", true⟩
  | "notice/D005/paragraph/7" => ⟨some "併せて実施", some "morphologyGroups", false⟩
  | "notice/D005/paragraph/9" => ⟨some "同一月中", none, false⟩
  | "notice/D006/paragraph/8/i" => ⟨some "同時", some "coagulationMarkerGroup", true⟩
  | "primary/D006-4/note/2" => ⟨some "１回の採取", some "geneticDiseaseDraw", false⟩
  | "notice/D006-10/paragraph/unnumbered" => ⟨some "併せて実施", none, false⟩
  | "notice/D006-15/paragraph/3" => ⟨some "同時", some "bladderCytologyGroup", false⟩
  | "notice/D006-22/paragraph/3" => ⟨some "同一月中", some "plasmaRasMonthlyGroup", false⟩
  | "notice/D006-24/paragraph/2" => ⟨some "併せて実施", some "lungPanelGroup", false⟩
  | "notice/D006-27/paragraph/3/e" => ⟨some "併せて行った", none, false⟩
  | "notice/D006-27/paragraph/5/e" => ⟨some "併せて行った", none, false⟩
  | "notice/D006-27/paragraph/6/e" => ⟨some "併せて算定", none, false⟩
  | "notice/D006-27/paragraph/10/u" => ⟨some "併せて行った", none, false⟩
  | "notice/D007/paragraph/2" => ⟨some "同時", some "chemistryCombinationGroup", true⟩
  | "notice/D007/paragraph/3" => ⟨some "同時", some "chemistryCombinationGroup", true⟩
  | "notice/D007/paragraph/5" => ⟨some "併せて測定", some "chemistryCombinationGroup", false⟩
  | "notice/D007/paragraph/7" => ⟨some "併せて測定", some "chemistryCombinationGroup", false⟩
  | "notice/D007/paragraph/9" => ⟨some "併せて実施", some "chemistryPriorityGroup", false⟩
  | "notice/D007/paragraph/12" => ⟨some "同一検体", some "chemistryPriorityGroup", false⟩
  | "notice/D007/paragraph/15" => ⟨some "同時", some "chemistryPairChoice", false⟩
  | "notice/D007/paragraph/17/e" => ⟨some "同一検体", some "carnitineChoice", false⟩
  | "notice/D007/paragraph/18" => ⟨some "併せて実施", none, false⟩
  | "notice/D007/paragraph/21" => ⟨some "併せて実施", some "lungMarkerGroup", false⟩
  | "notice/D007/paragraph/22" => ⟨some "同一月", some "troponinMonthGroup", false⟩
  | "notice/D007/paragraph/23/i" => ⟨some "併せて実施", none, false⟩
  | "notice/D007/paragraph/27" => ⟨some "併せて実施", some "lateChemistryGroup", false⟩
  | "notice/D007/paragraph/30" => ⟨some "併せて行った", some "lateChemistryGroup", false⟩
  | "notice/D007/paragraph/38" => ⟨some "同一日", some "myosinDayGroup", false⟩
  | "notice/D007/paragraph/40/i" => ⟨some "併せて実施", some "lateChemistryGroup", false⟩
  | "notice/D007/paragraph/41/i" => ⟨some "併せて実施", some "lateChemistryGroup", false⟩
  | "notice/D007/paragraph/42/i" => ⟨some "併せて実施", some "lateChemistryGroup", false⟩
  | "notice/D007/paragraph/43/u" => ⟨some "併せて実施", some "lateChemistryGroup", false⟩
  | "notice/D007/paragraph/46/i" => ⟨some "同一月中", none, false⟩
  | "notice/D007/paragraph/47" => ⟨some "併せて実施", none, false⟩
  | "notice/D007/paragraph/48/i" => ⟨some "併せて実施", none, false⟩
  | "notice/D008/paragraph/3" => ⟨some "併せて行った", some "endocrineGroup", false⟩
  | "notice/D008/paragraph/4" => ⟨some "同時", none, false⟩
  | "notice/D008/paragraph/6/i" => ⟨some "併せて実施", some "endocrineGroup", false⟩
  | "notice/D008/paragraph/7/i" => ⟨some "起算して１週間以内", some "natriureticWeekGroup", false⟩
  | "notice/D008/paragraph/13" => ⟨some "併せて実施", some "endocrineGroup", false⟩
  | "notice/D008/paragraph/15" => ⟨some "併せて実施", some "endocrineGroup", false⟩
  | "notice/D008/paragraph/16" => ⟨some "併せて実施", some "endocrineGroup", true⟩
  | "notice/D008/paragraph/18" => ⟨some "併せて実施", some "endocrineGroup", false⟩
  | "notice/D008/paragraph/19" => ⟨some "同時", none, false⟩
  | "notice/D008/paragraph/25" => ⟨some "併せて行った", some "endocrineGroup", false⟩
  | "notice/D008/paragraph/26/i" => ⟨some "併せて実施", some "endocrineGroup", false⟩
  | "notice/D008/paragraph/27/i" => ⟨some "併せて実施", none, false⟩
  | "notice/D009/paragraph/3" => ⟨some "併せて測定", some "markerGroup", false⟩
  | "notice/D009/paragraph/5" => ⟨some "併せて測定", some "markerGroup", false⟩
  | "notice/D009/paragraph/8" => ⟨some "同時", some "markerGroup", false⟩
  | "notice/D009/paragraph/10/i" => ⟨some "併せて測定", some "markerGroup", false⟩
  | "notice/D009/paragraph/15" => ⟨some "併せて実施", some "markerGroup", false⟩
  | "notice/D009/paragraph/20/u" => ⟨some "併せて実施", some "markerGroup", false⟩
  | "notice/D009/paragraph/21/e" => ⟨some "併せて実施", some "markerGroup", false⟩
  | "notice/D009/paragraph/21/u" => ⟨some "併せて実施", some "markerGroup", false⟩
  | "notice/D009/paragraph/24/i" => ⟨some "併せて測定", some "markerGroup", false⟩
  | "notice/D011/paragraph/4/u" => ⟨some "一連の検査", some "pf4SeriesGroup", false⟩
  | "notice/D012/paragraph/2" => ⟨some "併せて実施", some "infectionGroup", false⟩
  | "notice/D012/paragraph/4" => ⟨some "同時", some "infectionGroup", false⟩
  | "notice/D012/paragraph/12" => ⟨some "同時", none, false⟩
  | "notice/D012/paragraph/23" => ⟨some "併せて実施", some "infectionGroup", false⟩
  | "notice/D012/paragraph/31/i" => ⟨some "併せて実施", some "infectionGroup", false⟩
  | "notice/D012/paragraph/32" => ⟨some "同時", none, false⟩
  | "notice/D012/paragraph/34" => ⟨some "併せて算定", none, false⟩
  | "notice/D012/paragraph/36" => ⟨some "併せて実施", none, false⟩
  | "notice/D012/paragraph/38/i" => ⟨some "同一ウイルス", some "virusClassGroup", false⟩
  | "notice/D012/paragraph/38/u" => ⟨some "併せて測定", none, false⟩
  | "notice/D012/paragraph/43/i" => ⟨some "併せて実施", some "infectionGroup", false⟩
  | "notice/D012/paragraph/48/e" => ⟨some "併せて実施", some "infectionGroup", false⟩
  | "notice/D012/paragraph/56" => ⟨some "併せて実施", some "infectionGroup", false⟩
  | "notice/D013/paragraph/5" => ⟨some "同時", some "hepatitisGroup", false⟩
  | "notice/D013/paragraph/6" => ⟨some "同時", some "hepatitisGroup", false⟩
  | "notice/D013/paragraph/8" => ⟨some "同時", some "hepatitisDnaGroup", false⟩
  | "notice/D014/paragraph/1" => ⟨some "併せて実施", none, false⟩
  | "notice/D014/paragraph/2" => ⟨some "併せて実施", none, false⟩
  | "notice/D014/paragraph/3" => ⟨some "併せて実施", none, false⟩
  | "notice/D014/paragraph/6" => ⟨some "併せて実施", none, false⟩
  | "notice/D014/paragraph/7/i" => ⟨some "併せて実施", none, false⟩
  | "notice/D014/paragraph/8" => ⟨some "同時", some "thyroidAntibodyGroup", false⟩
  | "notice/D014/paragraph/10" => ⟨some "併せて実施", none, false⟩
  | "notice/D014/paragraph/12" => ⟨some "併せて実施", some "igg2Choice", false⟩
  | "notice/D014/paragraph/16/i" => ⟨some "併せて測定", none, false⟩
  | "notice/D014/paragraph/19/i" => ⟨some "併せて測定", none, false⟩
  | "notice/D014/paragraph/23/i" => ⟨some "併せて測定", none, false⟩
  | "notice/D014/paragraph/24/i" => ⟨some "併せて測定", none, false⟩
  | "notice/D014/paragraph/27/i" => ⟨some "併せて測定", none, false⟩
  | "notice/D015/paragraph/2" => ⟨some "併せて測定", none, false⟩
  | "notice/D015/paragraph/4/i" => ⟨some "同一検体", some "electrophoresisGroup", false⟩
  | "notice/D015/paragraph/10" => ⟨some "併せて実施", none, false⟩
  | "notice/D015/paragraph/11/i" => ⟨some "同一月中", some "atopyProteinGroup", false⟩
  | "notice/D015/paragraph/12/i" => ⟨some "同時", none, false⟩
  | "primary/D017/note/unnumbered/1" => ⟨some "同一検体", some "sedimentBacteriaGroup", false⟩
  | "notice/D017/paragraph/2" => ⟨some "各種の方法を２以上用いた場合", some "microscopyMethodsGroup", false⟩
  | "notice/D018/paragraph/1/e" => ⟨some "同一起因菌", some "cultureSiteGroup", false⟩
  | "notice/D018/paragraph/1/u" => ⟨some "同一検体", some "cultureChoice", false⟩
  | "notice/D023/paragraph/1/a" => ⟨some "併用", none, false⟩
  | "notice/D023/paragraph/2/a" => ⟨some "併せて実施", none, false⟩
  | "notice/D023/paragraph/3" => ⟨some "併せて実施", none, false⟩
  | "notice/D023/paragraph/5/a" => ⟨some "併せて実施", none, false⟩
  | "notice/D023/paragraph/36/i" => ⟨some "一連の治療期間", none, false⟩
  | "notice/D023/paragraph/37/e" => ⟨some "一連の治療期間", none, false⟩
  | "notice/D023/paragraph/37/e/u" => ⟨some "一連の治療期間", none, false⟩
  | "notice/D023/paragraph/37/u" => ⟨some "一連の治療期間", none, false⟩
  | "notice/D023/paragraph/37/u/ko" => ⟨some "一連の治療期間", none, false⟩
  | "notice/D023/paragraph/39/i" => ⟨some "一連の治療期間", none, false⟩
  | "notice/D023-2/paragraph/1/i" => ⟨some "併せて実施", some "methicillinPbp2Group", false⟩
  | "notice/D023-2/paragraph/4/i" => ⟨some "併せて算定", some "rapidPbp2Group", false⟩
  | "notice/ch2-part3-section4/general/3" => ⟨some "同一日", some "sharedPunctureGroup", false⟩
  | "notice/D007/paragraph/26" => ⟨some "併せて実施", none, false⟩
  | "notice/D012/paragraph/28" => ⟨some "複数測定", some "infectionGroup", false⟩
  | "notice/D012/paragraph/30" => ⟨some "別に算定できない", none, false⟩
  | "notice/D012/paragraph/47/i" | "notice/D012/paragraph/53/i"
  | "notice/D012/paragraph/54/i" | "notice/D012/paragraph/59" =>
    ⟨some "別に算定できない", none, false⟩
  | "notice/D023/paragraph/10/i" => ⟨some "併せて実施", none, false⟩
  | "notice/D023/paragraph/16/u" => ⟨some "廃液を検体として", none, false⟩
  | _ => {}

/-- 外部照合の項目対に展開する前に残る識別。 -/
def Entry.memberGap (g : Entry) : Option String :=
  if !g.members.isEmpty then none else
    match g.id with
    | "notice/D003/paragraph/4/u" => some "D313の実施を検体検査の項目対に登録していない"
    | "notice/D004-2/paragraph/10" => some "HER2の組織検査とN005の標本の枝を照合する必要がある"
    | "primary/D006-4/note/2" => some "対象疾患と等級の構成。項番の組では疾患を区別できない"
    | "notice/D007/paragraph/38" => some "同一項目の反復。構成は採否を適用する日次の実施ID"
    | "notice/D008/paragraph/4" => some "血液と尿で同一項番。同時実施と検体種を区別するキーが必要"
    | "notice/D012/paragraph/38/i" => some "項46の同一ウイルスのIgGとIgM。ウイルスとクラスのキーが必要"
    | "notice/D023/paragraph/16/u" => some "内視鏡廃液由来の検査とD419項1の採取との照合が必要"
    | "notice/D023/paragraph/39/i" => some "対象病原体と核酸検査の種類を枝まで分ける必要がある"
    | "notice/D023-2/paragraph/1/i" => some "相手はD023項17のうちメチシリン耐性遺伝子。検査種類のキーが必要"
    | "notice/ch2-part3-section4/general/3" => some "11種類の穿刺と同一処置に当たる相手行為の組を同定する必要がある"
    | _ => none

def indexedItems : List ItemKey := (inventory.flatMap Entry.members).eraseDups

def indexedGroups : List ChoiceGroup :=
  inventory.map fun group =>
    ⟨group.source, group.members.map indexedItems.idxOf, 0⟩

def overlaps : List (Nat × Nat × List Nat) := overlappingGroups indexedGroups

/-- 到達可能集合を、頂点数回の辺の走査で閉じる。孤立した群は含めない。 -/
def components : List (List Nat) := Id.run do
  let edges := overlaps.map fun (a, b, _) => (a, b)
  let vertices := (edges.flatMap fun (a, b) => [a, b]).eraseDups
  let mut visited := []
  let mut result := []
  for vertex in vertices do
    unless visited.contains vertex do
      let reached := vertices.foldl (fun reached _ =>
        (edges.foldl (fun found (a, b) =>
          if found.contains a || found.contains b then a :: b :: found else found) reached).eraseDups)
        [vertex]
      visited := reached ++ visited
      result := reached :: result
  return result.reverse

/-- 確認済みの併施という仮定で、D009の重複三群を既存の実施ID射影から作る。 -/
def psaScenario : List ChoiceGroup :=
  let site : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩
  let rows : List (Performance D009.Companion) :=
    [⟨1, site, .s23psa, none, none, none, none⟩,
     ⟨2, site, .psa, none, none, none, none⟩,
     ⟨3, site, .freePsaRatio, none, none, none, none⟩,
     ⟨4, site, .phi, none, none, none, none⟩]
  [.s23, .phiPsa, .phiRatio].filterMap (markerGroup · rows)

example : consistentSelections psaScenario [] [] = [[4]] := by decide

/-- 同一検体に三実施。二件制約への展開と、尿沈渣一方式を先に確定する読み。 -/
private def sedimentScenario : List ChoiceGroup :=
  [⟨UrineSediment.microscopySelectionRule.source, [1, 2], 1⟩,
   ⟨D017.sedimentChoice.source, [1, 3], 1⟩,
   ⟨D017.sedimentChoice.source, [2, 3], 1⟩]

example :
    consistentSelections sedimentScenario [] [] = [] ∧
      (List.range 3).all (fun i =>
        !(consistentSelections (sedimentScenario.eraseIdx i) [] []).isEmpty) = true := by decide

example :
    consistentSelections [⟨D017.sedimentChoice.source, [1, 3], 1⟩] [] [] = [[3], [1]] ∧
      consistentSelections [⟨D017.sedimentChoice.source, [2, 3], 1⟩] [] [] = [[3], [2]] := by decide

/-- 9項目を併施したD014(1)(7)イ。件数は上限として扱う。
空の採否も含む上限制約の全解を列挙する。 -/
def d014UpperBoundSelections : List (List Nat) :=
  let ccp : ChoiceGroup := ⟨D014.ccpChoice.source, List.range 8, 1⟩
  let empty := consistentSelections [{ ccp with count := 0 }] [] []
  let one := consistentSelections [ccp] [] []
  (empty ++ one).flatMap fun chosen => [chosen, 8 :: chosen]

example : d014UpperBoundSelections =
    [[], [8], [7], [8, 7], [6], [8, 6], [5], [8, 5], [4], [8, 4],
      [3], [8, 3], [2], [8, 2], [1], [8, 1], [0], [8, 0]] := by decide

/-- D014(2)も適用する同じ九項目の採否。ID 2, 3 はガラクトース欠損IgG、
ID 8 はRF。他の各項目の個別条件は別に確認する。 -/
def d014OverlapSelections : List (List Nat) :=
  d014UpperBoundSelections.filter fun chosen =>
    !(chosen.contains 8 && (chosen.contains 2 || chosen.contains 3))

example : d014OverlapSelections.length = 16 ∧
    [8, 2] ∉ d014OverlapSelections ∧ [8, 3] ∉ d014OverlapSelections := by decide

/-- 既存の条項別射影が返した群を、索引の構成項目と閾値で照合する。
適用単位・例外・算定件数の解釈は条項別射影に保持する。 -/
def checkedProjection (clause : String) (rows : List (Performance ItemKey))
    (existing : ChoiceGroup) : Option ChoiceGroup := do
  let definition ← inventory.find? (fun g => g.id == clause)
  let (threshold, count) ← definition.cardinality
  if threshold ≤ rows.length && rows.all (fun p => definition.members.contains p.item) &&
      rows.map Performance.id == existing.members && count == existing.count then
    some existing
  else none

theorem checked_projection_eq {clause : String} {rows : List (Performance ItemKey)}
    {existing projected : ChoiceGroup} (h : checkedProjection clause rows existing = some projected) :
    projected = existing := by
  cases found : inventory.find? (fun g => g.id == clause) with
  | none => simp [checkedProjection, found] at h
  | some definition =>
    cases cardinality : definition.cardinality with
    | none => simp [checkedProjection, found, cardinality] at h
    | some pair =>
      obtain ⟨threshold, count⟩ := pair
      simp [checkedProjection, found, cardinality] at h
      exact h.2.symm

private def specimenSite : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def recorded (id : Nat) (item : α) : Performance α :=
  ⟨id, specimenSite, item, some 1, some 1, some 1, some 1⟩

/-- 上限一件を二件同時採用の禁止に置き換える。全採否の列挙は不要。 -/
theorem atMostOne_iff_pairwise (ids : List Nat) (keep : Nat → Bool) :
    (ids.filter keep).length ≤ 1 ↔
      ids.Pairwise (fun a b => keep a = true → keep b = false) := by
  induction ids with
  | nil => simp
  | cons id rest ih =>
    cases h : keep id
    · simp [h, ih]
    · simp only [List.filter_cons, h, ite_true, List.length_cons, Nat.succ_le_succ_iff,
        Nat.le_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff, Bool.not_eq_true,
        List.pairwise_cons, forall_const]
      refine ⟨fun all => ⟨all, ?_⟩, And.left⟩
      apply ih.mp
      have empty : rest.filter keep = [] := List.filter_eq_nil_iff.mpr (by simpa using all)
      simp [empty]

/-- D014(24)イ・(27)イの各一実施。併測と確認した場合の上限と、
その単位の外にある場合の採否を比較する。 -/
theorem myasthenia_component :
    let choices := [[], [2], [1], [1, 2]]
    choices.filter (fun ids => ids.length ≤ 1) = [[], [2], [1]] ∧
    consistentSelections
      [⟨D014.achrChoice.source, [1, 2], 1⟩, ⟨D014.muskChoice.source, [1, 2], 1⟩]
      [] [] = [[2], [1]] ∧ choices.length = 4 := by decide

/-- D001(6)イとD007(46)イの三項目を同一月・同目的に実施し、
外部のD313を行っていない場合。登録した部分群と三項目の群で結果を比較する。 -/
theorem colitis_component :
    let urine : ChoiceGroup := ⟨D001.colitisRule.source, [1, 2], 1⟩
    let source := BloodChemistryLate.rules.find? (·.id == "notice/D007/paragraph/46/i")
    source.map (fun rule =>
      let blood : ChoiceGroup := ⟨rule.source, [2, 3], 1⟩
      (consistentSelections [urine, blood] [] [],
        consistentSelections [{ urine with members := [1, 2, 3] }, blood] [] [])) =
      some ([[2], [1, 3]], [[3], [2]]) := by decide

/-- D008(25)(27)イで四項目とも併施の範囲に入る読みと、(27)イが発動しない読み。 -/
theorem metanephrine_component :
    let pair : ChoiceGroup := ⟨D008.normetanephrineRule.source, [1, 2], 1⟩
    let four : ChoiceGroup := ⟨D008.freeMetanephrineChoice.source, [1, 2, 3, 4], 1⟩
    consistentSelections [pair, four] [] [] = [[2], [1]] ∧
      consistentSelections [pair] [3, 4] [] = [[2, 3, 4], [1, 3, 4]] := by decide

/-- D008(13)(15)の四項目。同じ範囲で適用群が発動する場合、主検査を
各群に一つ求めると三つの共通候補が残る。適用範囲は外部で確定する。 -/
theorem bone_marker_component :
    let rows : List (Performance D008.CombinationItem) :=
      [recorded 1 (.endocrine .ntx .other), recorded 2 (.endocrine .osteocalcin .other),
       recorded 3 (.endocrine .urineDpd .other), recorded 4 (.endocrine .tracp5b .other)]
    let groups := [.bone, .tracp].filterMap (endocrineGroup · rows)
    groups.length = 2 ∧ consistentSelections groups [] [] = [[3], [2], [1]] := by decide

/-- D009(3)(24)イの四項目。両条項を一つずつの主検査とする場合と、
(24)イの併測範囲に入らない場合。 -/
theorem cea_apoa_component :
    let rows := [recorded 1 D009.Companion.cea, recorded 2 .dupan2,
      recorded 3 .apoa2, recorded 4 .span1]
    let groups := [.cea, .apoa].filterMap (markerGroup · rows)
    groups.length = 2 ∧ consistentSelections groups [] [] = [[2], [1]] ∧
      consistentSelections (groups.take 1) [3, 4] [] = [[2, 3, 4], [1, 3, 4]] := by decide

example :
    let a : D001.Context := { performance := recorded 1 .albuminQuantitative }
    let peers := [recorded 2 UrineFecalTests.UrineSpecial.transferrin, recorded 3 .typeIVCollagen]
    let indexed := [recorded 1 ("D001", "albuminQuantitative"), recorded 2 ("D001", "transferrin"),
      recorded 3 ("D001", "typeIVCollagen")]
    (renalSimultaneousGroup a peers).bind
      (fun groups => groups.head?.bind (checkedProjection D001.renalRule.id indexed)) =
      some ⟨D001.renalRule.source, [1, 2, 3], 1⟩ := by decide

private def sediment (id : Nat) (method : UrineSediment.Method) : UrineSediment.Context :=
  ⟨recorded id method, none, none, none, none, none, none, []⟩

example :
    (sedimentMethodGroup (sediment 1 .microscopy) (sediment 2 .flow)).bind
      (checkedProjection UrineSediment.microscopySelectionRule.id
        [recorded 1 ("D002", "microscopy"), recorded 2 ("D002-2", "flow")]) =
      some ⟨UrineSediment.microscopySelectionRule.source, [1, 2], 1⟩ := by decide

example :
    (sedimentBacteriaGroup (sediment 1 .microscopy)
      { performance := recorded 3 .specializedMicroscopy }).bind
      (checkedProjection D017.sedimentChoice.id
        [recorded 1 ("D002", "microscopy"), recorded 3 ("D017", "specializedMicroscopy")]) =
      some ⟨D017.sedimentChoice.source, [1, 3], 1⟩ := by decide

private def chemistryProjection (kind : ChemistryCombination)
    (clause : String) (rows : List (BloodChemistry.Item × String)) : Option ChoiceGroup :=
  let typed := rows.zipIdx.map fun ((item, _), i) => recorded i item
  let indexed := rows.zipIdx.map fun ((_, name), i) => recorded i ("D007", name)
  (chemistryCombinationGroup kind typed).bind (checkedProjection clause indexed)

example :
    chemistryProjection .calcium BloodChemistry.calciumRule.id
      [(.calcium, "calcium"), (.ionizedCalcium, "ionizedCalcium")] =
      some ⟨BloodChemistry.calciumRule.source, [0, 1], 1⟩ ∧
    chemistryProjection .ironBinding BloodChemistry.ironBindingRule.id
      [(.uibcColorimetric, "uibcColorimetric"), (.tibcColorimetric, "tibcColorimetric")] =
      some ⟨BloodChemistry.ironBindingRule.source, [0, 1], 1⟩ ∧
    chemistryProjection .cholesterol BloodChemistry.cholesterolRule.id
      [(.hdlCholesterol, "hdlCholesterol"), (.totalCholesterol, "totalCholesterol"),
       (.ldlCholesterol, "ldlCholesterol")] =
      some ⟨BloodChemistry.cholesterolRule.source, [0, 1, 2], 2⟩ ∧
    chemistryProjection .protein BloodChemistry.proteinRule.id
      [(.proteinFractionation, "proteinFractionation"), (.totalProtein, "totalProtein"),
       (.albumin, "albumin")] =
      some ⟨BloodChemistry.proteinRule.source, [0, 1, 2], 2⟩ := by decide

example :
    let a := recorded 1 BloodMorphology.Item.eosinophilCount
    let b := recorded 2 BloodMorphology.Item.automatedDifferential
    (morphologyGroups a b false).bind (fun groups => groups.head?.bind
      (checkedProjection BloodMorphology.eosinophilRule.id
        [recorded 1 ("D005", "eosinophilCount"), recorded 2 ("D005", "automatedDifferential")])) =
      some ⟨BloodMorphology.eosinophilRule.source, [1, 2], 1⟩ := by decide

example :
    let keys := [recorded 1 ("D009", "31"), recorded 2 ("D009", "9"),
      recorded 3 ("D009", "17"), recorded 4 ("D009", "32")]
    let ids := [D009.s23Choice.id, D009.phiPsaChoice.id, D009.phiRatioChoice.id]
    (ids.zip psaScenario).all (fun (clause, group) =>
      (checkedProjection clause (keys.filter fun p => group.members.contains p.id) group).isSome) =
      true := by decide

end Sanri.MedicalFee.SpecimenSelectionInventory
