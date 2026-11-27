import Sanri.SpecimenCrossDivision

namespace Sanri.MedicalFee.SpecimenSelectionInventory

open Sanri.Logic Sanri.History SpecimenCrossDivision

abbrev ItemKey := String × String

inductive UnitKind where
  | simultaneous | specimen | draw | day | month | series | week | unresolved
  deriving DecidableEq, Repr

inductive Connection where
  | complete | partiallyConnected | unconnected
  deriving DecidableEq, Repr

structure Entry where
  id : String
  source : SourceRef
  members : List ItemKey
  unit : UnitKind
  connection : Connection
  /-- 発動する最小件数と算定件数の上限。等号として使えるかは条項ごとに確認する。 -/
  cardinality : Option (Nat × Nat)
  /-- 算定側・除外側の指定が確認されたか。未確認は none。 -/
  directed : Option Bool
  inAuditIndex : Bool

private def entry (id : String) (unit : UnitKind) (connection : Connection)
    (cardinality : Option (Nat × Nat)) (members : List ItemKey)
    (inAuditIndex : Bool := true) (directed : Option Bool := none) : Entry :=
  let primary := id.startsWith "primary/"
  let source : SourceRef := if primary then
    ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度", id, .unchecked, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩
  else
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", id, .unchecked, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩
  ⟨id, source, members, unit, connection, cardinality, directed, inAuditIndex⟩

/-- 外部照合索引の構成項目。部分経路の相手や空欄を含む。 -/
def inventory : List Entry := [
  entry "notice/D001/paragraph/3" .simultaneous .partiallyConnected (some (2, 1))
    [("D001", "albuminQuantitative"), ("D001", "transferrin"), ("D001", "typeIVCollagen")] true (some false),
  entry "notice/D001/paragraph/4/i" .unresolved .unconnected none
    [("D001", "trypsinogen2"), ("D007", "amylase"), ("D007", "amylaseIsoenzymes"), ("D007", "lipase"), ("D007", "trypsin"), ("D009", "8")],
  entry "notice/D001/paragraph/6/i" .month .unconnected none
    [("D001", "prostaglandinEMajorMetabolite"), ("D003", "calprotectin")],
  entry "notice/D001/paragraph/9/i" .unresolved .unconnected none
    [("D001", "lFabp"), ("D001", "ngal")],
  entry "notice/D002/paragraph/5" .unresolved .partiallyConnected (some (2, 1))
    [("D002", "microscopy"), ("D002-2", "flow")] true (some false),
  entry "notice/D003/paragraph/4/u" .unresolved .unconnected none
    [],
  entry "notice/D004/paragraph/1" .unresolved .unconnected none
    [("D004", "jointFluid"), ("D017", "heatedAmoeba"), ("D017", "otherMicroscopy"), ("D017", "specializedMicroscopy")],
  entry "notice/D004/paragraph/13/i" .unresolved .unconnected none
    [("D004", "amyloidRatio"), ("D004", "phosphoTau"), ("D004", "phosphoTauAmyloidRatio")],
  entry "notice/D004-2/paragraph/7" .month .unconnected none
    [("D004-2", "complex"), ("D004-2", "drugAid"), ("D004-2", "otherSimple"), ("D006-14", "flt3"), ("D006-16", "jak2"), ("D006-2", "hematopoieticTumorGene"), ("D006-6", "immuneRearrangement")],
  entry "notice/D004-2/paragraph/8" .month .unconnected none
    [("D004-2", "drugAid"), ("D006-12", "plasmaEgfr"), ("D006-24", "lungPanel")],
  entry "notice/D004-2/paragraph/9" .unresolved .unconnected none
    [("D004-2", "drugAid"), ("D006-24", "lungPanel")],
  entry "notice/D004-2/paragraph/10" .unresolved .unconnected none
    [],
  entry "notice/D004-2/paragraph/11" .unresolved .unconnected none
    [("D004-2", "complex"), ("D004-2", "drugAid"), ("D006-18", "tumorCells")],
  entry "notice/D005/paragraph/3" .specimen .partiallyConnected (some (2, 1))
    [("D005", "automatedDifferential"), ("D005", "eosinophilCount"), ("D005", "microscopicDifferential")] true (some false),
  entry "notice/D005/paragraph/7" .unresolved .unconnected none
    [("D005", "bloodMicroorganisms"), ("D005", "dnaContainingRedCellCount")],
  entry "notice/D005/paragraph/9" .unresolved .unconnected none
    [("D005", "hemoglobinA1c"), ("D007", "anhydroglucitol"), ("D007", "glycatedAlbumin")],
  entry "notice/D006/paragraph/8/i" .simultaneous .unconnected none
    [("D006", "fibrinMonomer"), ("D006", "prothrombinFragment"), ("D006", "tat")],
  entry "primary/D006-4/note/2" .unresolved .unconnected none
    [],
  entry "notice/D006-10/paragraph/unnumbered" .unresolved .unconnected none
    [("D006-10", "ccr4"), ("N002", "5")] false,
  entry "notice/D006-15/paragraph/3" .simultaneous .unconnected none
    [("D006-15", "bladder"), ("N004", "2")],
  entry "notice/D006-22/paragraph/3" .month .unconnected none
    [("D004-2", "drugAid"), ("D004-2", "otherSimple"), ("D006-22", "plasmaRas")],
  entry "notice/D006-24/paragraph/2" .unresolved .unconnected none
    [("D004-2", "drugAid"), ("D006-12", "plasmaEgfr"), ("D006-24", "lungPanel")],
  entry "notice/D006-27/paragraph/3/e" .unresolved .unconnected none
    [("D006-27", "alk"), ("N002", "6"), ("N005-2", "heading")] false,
  entry "notice/D006-27/paragraph/5/e" .unresolved .unconnected none
    [("D006-27", "ntrk"), ("D006-18", "blood"), ("D006-18", "tumorCells")] false,
  entry "notice/D006-27/paragraph/6/e" .unresolved .unconnected none
    [("D006-27", "ras"), ("D006-22", "plasmaRas")] false (some true),
  entry "notice/D006-27/paragraph/10/u" .unresolved .unconnected none
    [("D006-27", "microsatellite"), ("D006-18", "tumorCells")] false,
  entry "notice/D007/paragraph/2" .simultaneous .partiallyConnected (some (2, 1))
    [("D007", "calcium"), ("D007", "ionizedCalcium")] true (some false),
  entry "notice/D007/paragraph/3" .simultaneous .partiallyConnected (some (2, 1))
    [("D007", "tibcColorimetric"), ("D007", "uibcColorimetric")] true (some false),
  entry "notice/D007/paragraph/5" .unresolved .partiallyConnected (some (3, 2))
    [("D007", "hdlCholesterol"), ("D007", "ldlCholesterol"), ("D007", "totalCholesterol")] true (some false),
  entry "notice/D007/paragraph/7" .unresolved .partiallyConnected (some (3, 2))
    [("D007", "albumin"), ("D007", "proteinFractionation"), ("D007", "totalProtein")] true (some false),
  entry "notice/D007/paragraph/9" .unresolved .unconnected none
    [("D007", "ketoneBodies"), ("D007", "ketoneFractions")],
  entry "notice/D007/paragraph/12" .specimen .unconnected none
    [("D007", "bicarbonate"), ("D007", "bloodGas")],
  entry "notice/D007/paragraph/15" .simultaneous .unconnected none
    [("D007", "bileAcids"), ("D007", "urinarySulfatedBileAcids")],
  entry "notice/D007/paragraph/17/e" .unresolved .unconnected none
    [("D007", "freeCarnitine"), ("D007", "totalCarnitine"), ("D010", "8/ha"), ("D010", "8/i"), ("D010", "8/ni"), ("D010", "8/ro")],
  entry "notice/D007/paragraph/18" .unresolved .unconnected none
    [("D007", "alpIsoenzymesAndBap"), ("D008", "bap")],
  entry "notice/D007/paragraph/21" .unresolved .unconnected none
    [("D007", "kl6"), ("D007", "surfactantProteinA"), ("D007", "surfactantProteinD")],
  entry "notice/D007/paragraph/22" .month .unconnected none
    [("D007", "troponinI"), ("D007", "troponinTQualitative"), ("D007", "troponinTQuantitative")],
  entry "notice/D007/paragraph/23/i" .unresolved .unconnected none
    [("D007", "cystatinC"), ("D007", "pentosidine")],
  entry "notice/D007/paragraph/26" .specimen .unconnected none
    [("D007", "creatinine"), ("D007", "inulin")],
  entry "notice/D007/paragraph/27" .unresolved .unconnected none
    [("D007", "hFabpQualitative"), ("D007", "hFabpQuantitative"), ("D007", "myoglobinQualitative"), ("D007", "myoglobinQuantitative")],
  entry "notice/D007/paragraph/30" .unresolved .unconnected none
    [("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/38" .unresolved .unconnected none
    [],
  entry "notice/D007/paragraph/40/i" .unresolved .unconnected none
    [("D007", "hyaluronicAcid"), ("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/41/i" .unresolved .unconnected none
    [("D007", "autotaxin"), ("D007", "hyaluronicAcid"), ("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/42/i" .unresolved .unconnected none
    [("D007", "autotaxin"), ("D007", "ck18f"), ("D007", "hyaluronicAcid"), ("D007", "mac2"), ("D007", "procollagenIII"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/43/u" .unresolved .unconnected none
    [("D007", "autotaxin"), ("D007", "ck18f"), ("D007", "elfScore"), ("D007", "mac2"), ("D007", "typeIVCollagen"), ("D007", "typeIVCollagen7S")],
  entry "notice/D007/paragraph/46/i" .month .unconnected none
    [("D003", "calprotectin"), ("D007", "lrg")],
  entry "notice/D007/paragraph/47" .unresolved .unconnected none
    [("D007", "procalcitoninQuantitative"), ("D007", "procalcitoninSemiquantitative"), ("D012", "endotoxin")],
  entry "notice/D007/paragraph/48/i" .unresolved .unconnected none
    [("D007", "presepsin"), ("D007", "procalcitoninQuantitative"), ("D007", "procalcitoninSemiquantitative"), ("D012", "endotoxin")],
  entry "notice/D008/paragraph/3" .unresolved .unconnected none
    [("D008", "reninActivity"), ("D008", "reninQuantitative")],
  entry "notice/D008/paragraph/4" .unresolved .unconnected none
    [],
  entry "notice/D008/paragraph/6/i" .unresolved .unconnected none
    [("D008", "hcgBeta"), ("D008", "hcgQualitative"), ("D008", "hcgQuantitative"), ("D008", "hcgSemiquantitative")],
  entry "notice/D008/paragraph/7/i" .week .unconnected none
    [("D008", "anp"), ("D008", "bnp"), ("D008", "ntProBnp")],
  entry "notice/D008/paragraph/13" .unresolved .unconnected none
    [("D008", "ntx"), ("D008", "osteocalcin"), ("D008", "urineDpd")],
  entry "notice/D008/paragraph/15" .unresolved .unconnected none
    [("D008", "ntx"), ("D008", "osteocalcin"), ("D008", "tracp5b"), ("D008", "urineDpd")],
  entry "notice/D008/paragraph/16" .unresolved .unconnected none
    [("D007", "alpIsoenzymesPag"), ("D008", "bap"), ("D008", "intactPinp"), ("D008", "pinp")],
  entry "notice/D008/paragraph/18" .unresolved .unconnected none
    [("D008", "betaCtx"), ("D008", "urineBetaCtx")],
  entry "notice/D008/paragraph/19" .unresolved .unconnected none
    [("D008", "estradiol"), ("D008", "estriol"), ("D008", "estrogenQuantitative"), ("D008", "estrogenSemiquantitative")],
  entry "notice/D008/paragraph/25" .unresolved .unconnected none
    [("D008", "metanephrine"), ("D008", "normetanephrine")],
  entry "notice/D008/paragraph/26/i" .unresolved .unconnected none
    [("D008", "igfbp3"), ("D008", "somatomedinC")],
  entry "notice/D008/paragraph/27/i" .unresolved .unconnected none
    [("D008", "freeMetanephrineFractions"), ("D008", "metanephrine"), ("D008", "metanephrineFractions"), ("D008", "normetanephrine")],
  entry "notice/D009/paragraph/3" .unresolved .unconnected none
    [("D009", "3"), ("D009", "7")],
  entry "notice/D009/paragraph/5" .unresolved .unconnected none
    [("D009", "11"), ("D009", "28")],
  entry "notice/D009/paragraph/8" .simultaneous .unconnected none
    [("D009", "12"), ("D009", "21")],
  entry "notice/D009/paragraph/10/i" .unresolved .unconnected none
    [("D009", "18"), ("D009", "6")],
  entry "notice/D009/paragraph/15" .unresolved .unconnected none
    [("D009", "14"), ("D009", "24")],
  entry "notice/D009/paragraph/20/u" .unresolved .partiallyConnected (some (2, 1))
    [("D009", "17"), ("D009", "31"), ("D009", "32"), ("D009", "9")] true (some false),
  entry "notice/D009/paragraph/21/e" .unresolved .partiallyConnected (some (2, 1))
    [("D009", "17"), ("D009", "32")] true (some false),
  entry "notice/D009/paragraph/21/u" .unresolved .partiallyConnected (some (2, 1))
    [("D009", "32"), ("D009", "9")] true (some false),
  entry "notice/D009/paragraph/24/i" .unresolved .unconnected none
    [("D009", "15"), ("D009", "3"), ("D009", "35"), ("D009", "7")],
  entry "notice/D011/paragraph/4/u" .unresolved .unconnected none
    [("D011", "pf4IgG"), ("D011", "pf4IgGmA"), ("D011", "pf4Qualitative")],
  entry "notice/D012/paragraph/2" .unresolved .unconnected none
    [("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi")],
  entry "notice/D012/paragraph/4" .simultaneous .unconnected none
    [("D012", "stoolAdenovirus"), ("D012", "stoolRotavirusQual"), ("D012", "stoolRotavirusQuant")],
  entry "notice/D012/paragraph/12" .simultaneous .unconnected none
    [("D012", "rapidGroupAStrep"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D012/paragraph/23" .unresolved .unconnected none
    [("D012", "pneumoniaeIgA"), ("D012", "pneumoniaeIgG"), ("D012", "pneumoniaeIgM")],
  entry "notice/D012/paragraph/28" .unresolved .unconnected none
    [("D012", "ecoliO157Antibody"), ("D012", "ecoliO157Antigen"), ("D018", "gastrointestinal")],
  entry "notice/D012/paragraph/30" .unresolved .unconnected none
    [("D012", "ecoliSerotype"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D012/paragraph/31/i" .unresolved .unconnected none
    [("D012", "pneumococcusCapsule"), ("D012", "pneumococcusWall")],
  entry "notice/D012/paragraph/32" .simultaneous .unconnected none
    [("D012", "gonococcusAntigen"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D012/paragraph/34" .unresolved .unconnected none
    [("D012", "herpesAntigen"), ("D012", "herpesCornea"), ("D012", "herpesGenital"), ("D012", "herpesSkin")],
  entry "notice/D012/paragraph/36" .unresolved .unconnected none
    [("D012", "arabinitol"), ("D012", "aspergillusAntigen"), ("D012", "aspergillusIgG"), ("D012", "betaGlucan"), ("D012", "candidaQual"), ("D012", "candidaQuant"), ("D012", "candidaSemi"), ("D012", "cryptococcusQual"), ("D012", "cryptococcusSemi")],
  entry "notice/D012/paragraph/38/i" .unresolved .unconnected none
    [],
  entry "notice/D012/paragraph/38/u" .unresolved .unconnected none
    [("D012", "classSpecificTiter"), ("D012", "viralTiter")],
  entry "notice/D012/paragraph/43/i" .unresolved .unconnected none
    [("D012", "pertussisAntigen"), ("D023", "pertussisGroup"), ("D023", "respiratoryPanelCovid"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D012/paragraph/47/i" .unresolved .unconnected none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "influenzaAntigen")],
  entry "notice/D012/paragraph/48/e" .unresolved .unconnected none
    [("D012", "dengueAntigen"), ("D012", "dengueCombo")],
  entry "notice/D012/paragraph/53/i" .unresolved .unconnected none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "rsAntigen")],
  entry "notice/D012/paragraph/54/i" .unresolved .unconnected none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "influenzaAntigen"), ("D012", "rsAntigen")],
  entry "notice/D012/paragraph/56" .unresolved .unconnected none
    [("D012", "toxoplasmaAntibody"), ("D012", "toxoplasmaAvidity")],
  entry "notice/D012/paragraph/59" .unresolved .unconnected none
    [("D012", "hiv1WesternBlot"), ("D012", "hiv2WesternBlot"), ("D012", "hivSpecific")],
  entry "notice/D013/paragraph/5" .simultaneous .unconnected none
    [("D013", "hbcAntibody"), ("D013", "hbcIgM")],
  entry "notice/D013/paragraph/6" .simultaneous .unconnected none
    [("D013", "haAntibody"), ("D013", "haIgM")],
  entry "notice/D013/paragraph/8" .simultaneous .unconnected none
    [("D013", "hbcrAntigen"), ("D023", "hbvQuantity")],
  entry "notice/D014/paragraph/1" .unresolved .partiallyConnected (some (3, 2))
    [("D014", "c1q"), ("D014", "galactoseQual"), ("D014", "galactoseQuant"), ("D014", "iggRf"), ("D014", "mmp3"), ("D014", "rf"), ("D014", "rfComplex")] true (some false),
  entry "notice/D014/paragraph/2" .unresolved .partiallyConnected none
    [("D014", "galactoseQual"), ("D014", "galactoseQuant"), ("D014", "rf")] true (some false),
  entry "notice/D014/paragraph/3" .unresolved .unconnected none
    [("D014", "microsomal"), ("D014", "tpo")],
  entry "notice/D014/paragraph/6" .unresolved .unconnected none
    [("D014", "ars"), ("D014", "jo1Qual"), ("D014", "jo1Quant"), ("D014", "jo1Semi")],
  entry "notice/D014/paragraph/7/i" .unresolved .partiallyConnected (some (2, 1))
    [("D014", "c1q"), ("D014", "ccpQual"), ("D014", "ccpQuant"), ("D014", "galactoseQual"), ("D014", "galactoseQuant"), ("D014", "iggRf"), ("D014", "mmp3"), ("D014", "rfComplex")] true (some false),
  entry "notice/D014/paragraph/8" .simultaneous .unconnected none
    [("D014", "trab"), ("D014", "tsab")],
  entry "notice/D014/paragraph/10" .unresolved .unconnected none
    [("D014", "beta2Igg"), ("D014", "beta2Igm"), ("D014", "cardiolipinComplex"), ("D014", "cardiolipinIgg"), ("D014", "cardiolipinIgm")],
  entry "notice/D014/paragraph/12" .unresolved .unconnected none
    [("D014", "igg2Nephelometry"), ("D014", "igg2Tia")],
  entry "notice/D014/paragraph/16/i" .unresolved .unconnected none
    [("D014", "dsg1"), ("D014", "dsg3")],
  entry "notice/D014/paragraph/19/i" .unresolved .unconnected none
    [("D014", "dsg1"), ("D014", "dsg3")],
  entry "notice/D014/paragraph/23/i" .unresolved .unconnected none
    [("D014", "bp180"), ("D014", "dsg1"), ("D014", "dsg3"), ("D014", "skinCombo")],
  entry "notice/D014/paragraph/24/i" .unresolved .unconnected none
    [("D014", "achr"), ("D014", "musk")],
  entry "notice/D014/paragraph/27/i" .unresolved .unconnected none
    [("D014", "achr"), ("D014", "musk")],
  entry "notice/D015/paragraph/2" .unresolved .unconnected none
    [("D015", "crp"), ("D015", "crpQual"), ("D015", "saa")],
  entry "notice/D015/paragraph/4/i" .specimen .unconnected none
    [("D015", "drugImmunofixation"), ("D015", "specificAntiserum"), ("D015", "wholeAntiserum")],
  entry "notice/D015/paragraph/10" .unresolved .unconnected none
    [("D007", "igfbp1Qualitative"), ("D015", "fibronectin")],
  entry "notice/D015/paragraph/11/i" .month .unconnected none
    [("D015", "scca2"), ("D015", "tarc")],
  entry "notice/D015/paragraph/12/i" .simultaneous .unconnected none
    [("D015", "lightChain"), ("D015", "specificAntiserum"), ("D015", "wholeAntiserum")],
  entry "primary/D017/note/unnumbered/1" .specimen .partiallyConnected (some (2, 1))
    [("D002", "microscopy"), ("D002-2", "flow"), ("D017", "heatedAmoeba"), ("D017", "otherMicroscopy"), ("D017", "specializedMicroscopy")] true (some false),
  entry "notice/D017/paragraph/2" .series .unconnected none
    [("D017", "heatedAmoeba"), ("D017", "otherMicroscopy"), ("D017", "specializedMicroscopy")],
  entry "notice/D018/paragraph/1/e" .unresolved .unconnected none
    [("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "respiratory")],
  entry "notice/D018/paragraph/1/u" .specimen .unconnected none
    [("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "respiratory"), ("D018", "simple")],
  entry "notice/D023/paragraph/1/a" .unresolved .unconnected none
    [("D012", "trachomatisAntigen"), ("D023", "trachomatis")],
  entry "notice/D023/paragraph/2/a" .unresolved .unconnected none
    [("D012", "gonococcusAntigen"), ("D023", "gonococcus")],
  entry "notice/D023/paragraph/3" .unresolved .unconnected none
    [("D012", "rapidGroupAStrep"), ("D018", "bloodOrPuncture"), ("D018", "gastrointestinal"), ("D018", "genitourinary"), ("D018", "other"), ("D018", "respiratory"), ("D018", "simple"), ("D023", "groupAStrep")],
  entry "notice/D023/paragraph/5/a" .unresolved .unconnected none
    [("D012", "gonococcusAntigen"), ("D012", "trachomatisAntigen"), ("D023", "gonococcus"), ("D023", "gonococcusTrachomatis"), ("D023", "trachomatis")],
  entry "notice/D023/paragraph/10/i" .unresolved .unconnected none
    [("D023", "hpv"), ("D023", "hpvSimpleGenotype")],
  entry "notice/D023/paragraph/16/u" .unresolved .unconnected none
    [],
  entry "notice/D023/paragraph/36/i" .series .unconnected none
    [("D012", "influenzaAntigen"), ("D012", "metapneumovirusAntigen"), ("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi"), ("D012", "nonStoolAdenovirus"), ("D012", "pneumococcusCapsule"), ("D012", "rsAntigen"), ("D023", "legionella"), ("D023", "pneumoniaResistancePanel"), ("D023", "respiratorySingle")],
  entry "notice/D023/paragraph/37/e" .series .unconnected none
    [("D012", "influenzaAntigen"), ("D012", "metapneumovirusAntigen"), ("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi"), ("D012", "nonStoolAdenovirus"), ("D012", "pertussisAntibody"), ("D012", "pertussisAntigen"), ("D012", "pertussisQual"), ("D012", "pertussisSemi"), ("D012", "pneumoniaeIgA"), ("D012", "pneumoniaeIgG"), ("D012", "pneumoniaeIgM"), ("D012", "rsAntigen"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D023/paragraph/37/e/u" .series .unconnected none
    [("D023", "respiratoryPanelCovid"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D023/paragraph/37/u" .series .unconnected none
    [("D012", "covidFlu"), ("D012", "covidFluRs"), ("D012", "covidQual"), ("D012", "covidQuant"), ("D012", "covidRs"), ("D012", "influenzaAntigen"), ("D012", "metapneumovirusAntigen"), ("D012", "mycoplasmaChromatography"), ("D012", "mycoplasmaFluorescence"), ("D012", "mycoplasmaQual"), ("D012", "mycoplasmaSemi"), ("D012", "nonStoolAdenovirus"), ("D012", "pertussisAntibody"), ("D012", "pertussisAntigen"), ("D012", "pertussisQual"), ("D012", "pertussisSemi"), ("D012", "pneumoniaeIgA"), ("D012", "pneumoniaeIgG"), ("D012", "pneumoniaeIgM"), ("D012", "rsAntigen"), ("D023", "respiratoryPanelCovid")],
  entry "notice/D023/paragraph/37/u/ko" .series .unconnected none
    [("D023", "respiratoryPanelCovid"), ("D023", "respiratoryPanelWithoutCovid")],
  entry "notice/D023/paragraph/39/i" .unresolved .unconnected none
    [],
  entry "notice/D023-2/paragraph/1/i" .unresolved .unconnected none
    [],
  entry "notice/D023-2/paragraph/4/i" .unresolved .unconnected none
    [("D023-2", "pbp2"), ("D023-2", "rapidPbp2")],
  entry "notice/ch2-part3-section4/general/3" .unresolved .unconnected none
    []
]

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
