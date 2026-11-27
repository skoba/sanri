import Sanri
import Lean

open Lean Lean.Meta Lean.Elab Command
open Sanri.Logic
open Sanri.MedicalFee

private def jsonFields (fields : List (String × String)) : Json :=
  Json.mkObj (fields.map fun (key, value) => (key, toJson value))

private def constructors (type : Name) : MetaM (List Name) := do
  let .inductInfo info ← getConstInfo type | throwError "expected inductive: {type}"
  return info.ctors

-- 有限な列挙型の引数は各値を試し、それ以外は自由変数のままにする。
private def arguments (arg : Expr) : MetaM (List Expr) := do
  let .const type _ ← inferType arg | return [arg]
  let some (.inductInfo info) := (← getEnv).find? type | return [arg]
  if info.numParams != 0 || info.numIndices != 0 then return [arg]
  let ctors ← info.ctors.mapM getConstInfoCtor
  if ctors.isEmpty || ctors.any (·.numFields != 0) then return [arg]
  return info.ctors.map fun name => mkConst name

private unsafe def ruleRow (module name : String) (rule : Expr) : MetaM Json := do
  let id ← whnf (mkProj ``Rule 0 rule)
  let source ← whnf (mkProj ``Rule 1 rule)
  let parameterized := source.hasFVar || id.hasFVar
  let id ← if id.hasFVar then pure "" else evalExpr String (mkConst ``String) id
  let fields := [("module", module), ("definition", name), ("id", id)]
  if parameterized then
    return Json.mkObj ((fields ++ [("classification", "parameterized")]).map
      (fun (key, value) => (key, toJson value)) ++
      ["kind", "identifier", "edition", "location", "verification", "url"].map (·, Json.null))
  let ref ← evalExpr SourceRef (mkConst ``SourceRef) source
  return jsonFields (fields ++ [
    ("kind", (reprStr ref.kind).replace "Sanri.Logic.SourceKind." ""),
    ("identifier", ref.identifier), ("edition", ref.edition), ("location", ref.location),
    ("verification", (reprStr ref.verification).replace "Sanri.Logic.SourceVerification." ""),
    ("url", ref.url.getD "")])

private unsafe def listRows (module name : String) (value : Expr) :
    Nat → MetaM (List Json)
  | index => do
    let value ← whnf value
    if value.isAppOfArity ``List.nil 1 then return []
    unless value.isAppOfArity ``List.cons 3 do
      throwError "cannot enumerate {name}"
    let args := value.getAppArgs
    let tail ← listRows module name args[2]! (index + 1)
    -- 定義名がある要素は定数の列挙で拾う。
    if args[1]!.isConst then return tail
    return (← ruleRow module (name ++ "[" ++ toString index ++ "]") args[1]!) :: tail

private unsafe def rules : MetaM (Array Json) := do
  let env ← getEnv
  let mut rows := #[]
  let defs := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  for (name, info) in defs do
    let .defnInfo info := info | continue
    let some idx := env.getModuleIdxFor? name | continue
    let module := env.header.moduleNames[idx.toNat]!.toString
    unless module.startsWith "Sanri." do continue
    let userName := privateToUserName name
    if userName.isInternalDetail then continue
    let label := userName.toString
    let value := mkConst name (info.levelParams.map Level.param)
    let found ← forallTelescopeReducing info.type fun params type => do
      if type.isAppOfArity ``Rule 2 then
        let choices ← params.toList.mapM arguments
        let instances := choices.foldr (fun values tails =>
          values.flatMap fun arg => tails.map fun tail => arg :: tail) [[]]
        instances.mapM fun args => do
          let specific := args.filterMap (·.constName?)
          let suffix := String.join (specific.map fun n => "/" ++ n.getString!)
          ruleRow module (label ++ suffix) (mkAppN value args.toArray)
      else if params.isEmpty && type.isAppOfArity ``List 1 &&
          type.appArg!.isAppOfArity ``Rule 2 then
        listRows module label value 0
      else pure []
    rows := rows ++ found.toArray
  return rows

private def pointRow (division item kind : String) (number branch : Nat)
    (points : Option Nat) : Json :=
  Json.mkObj [("division", toJson division), ("item", toJson item), ("kind", toJson kind),
    ("number", toJson number), ("branch", toJson branch), ("points", toJson points)]

private unsafe def evalNat (fn : Name) (item : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) (mkApp (mkConst fn) item)

private unsafe def points : MetaM (List Json) := do
  let blood ← (← constructors ``BloodMorphology.Item).mapM fun ctor => do
    let item := mkConst ctor
    let number ← evalNat ``BloodMorphology.Item.number item
    let price ← evalNat ``BloodMorphology.Item.basePoints item
    let stain ← evalNat ``BloodMorphology.Item.stainRate item
    let label := ctor.getString!
    return pointRow "D005" label "base" number 0 (some price) ::
      (if stain == 0 then [] else [pointRow "D005" label "note" number 0 (some stain)])
  let mut chemistry := []
  for ctor in ← constructors ``D007.ScopedItem do
    let label := ctor.getString!
    -- 項番10は種類数による三つの点数帯、項番13は各物質名を保持する。
    let items ← if ctor == ``D007.ScopedItem.apolipoproteins then
        let samples ← constructors ``D007.Apolipoprotein
        [1, 2, 3].mapM fun count => do
          let measured ← mkListLit (mkConst ``D007.Apolipoprotein)
            ((samples.take count).map fun name => mkConst name)
          return (label ++ "/" ++ toString count, mkApp (mkConst ctor) measured)
      else if ctor == ``D007.ScopedItem.organicAcid then
        pure ((← constructors ``D007.OrganicAcid).map fun sub =>
          (label ++ "/" ++ sub.getString!, mkApp (mkConst ctor) (mkConst sub)))
      else pure [(label, mkConst ctor)]
    for (label, item) in items do
      let type ← inferType item
      let scope := type.appArg!
      let number ← evalExpr Nat (mkConst ``Nat) (mkApp2 (mkConst ``D007.ScopedItem.number) scope item)
      let price ←
        if scope.isConstOf ``D007.Scope.draw then
          some <$> evalNat ``BloodChemistry.Item.points item
        else if scope.isConstOf ``D007.Scope.further then
          evalExpr (Option Nat) (mkApp (mkConst ``Option [.zero]) (mkConst ``Nat))
            (mkApp (mkConst ``BloodChemistryFurther.Item.scheduledPoints) item)
        else if scope.isConstOf ``D007.Scope.additional then
          some <$> evalNat ``BloodChemistryAdditional.Item.points item
        else if scope.isConstOf ``D007.Scope.late then
          some <$> evalNat ``BloodChemistryLate.Item.points item
        else if scope.isConstOf ``D007.Scope.glycemic then
          pure (some (if ctor == ``D007.ScopedItem.glycatedAlbumin then
            (GlycemicTests.Item.glycatedAlbumin none).points
            else GlycemicTests.Item.anhydroglucitol.points))
        else continue -- 同じ項目は further に含まれる。
      let kind := if ctor == ``D007.ScopedItem.urinarySulfatedBileAcids then "reference" else "base"
      chemistry := pointRow "D007" label kind number 0 price :: chemistry
  let specimens := (SpecimenTests.catalog.filter fun e => e.code != .d009 && e.code != .d010 && e.code != .d011 &&
      e.code != .d012 && e.code != .d013 && e.code != .d014 && e.code != .d015 &&
      e.code != .d016 && e.code != .d017 && e.code != .d018 && e.code != .d019 &&
      e.code != .d019_2 && e.code != .d020 && e.code != .d021 && e.code != .d022 &&
      e.code != .d023 && e.code != .d023_2).flatMap fun entry =>
    let code := (reprStr entry.code |>.splitOn "." |>.getLast! |>.toUpper).replace "_" "-"
    entry.variants.map fun item => pointRow code item "base" entry.number entry.branch entry.points
  let markers := (List.finRange 36).map fun slot =>
    let item : D009.Item := ⟨slot, 0⟩
    pointRow "D009" (toString item.number) "base" item.number 0 (some item.base)
  let markerBundle := [2, 3, 4].map fun n =>
    pointRow "D009" ("bundle/" ++ toString n) "note" 2 0
      (some (D009.bundlePoints (List.replicate n ⟨1, 0⟩)))
  let special := D010.ledgerItems.map fun item =>
    pointRow "D010" item.path "base" item.number item.branch (some item.rate)
  let immuneBlood := D011.ledgerItems.map fun item =>
    pointRow "D011" (toString item.number) "base" item.number item.branch (some item.points)
  let infection := D012.ledgerItems.map fun item =>
    pointRow "D012" (toString item.number) "base" item.number 0 (some item.points)
  let infectionCap := pointRow "D012" "viralCap" "note" 11 0
    (some D012.viralCapPoints)
  let infectionClassCap := pointRow "D012" "classCap" "note" 46 0
    (some D012.classCapPoints)
  let hepatitis := D013.ledgerItems.map fun i =>
    pointRow "D013" (reprStr i) "base" i.number 0 (some i.points)
  let hepatitisNotes := [(3, D013.threeItemPoints), (4, D013.fourItemPoints), (5, D013.fiveOrMorePoints)].map fun (n, p) =>
    pointRow "D013" ("bundle/" ++ toString n) "note" 0 0 (some p)
  let autoantibodies := D014.ledgerItems.map fun i =>
    pointRow "D014" (reprStr i) "base" i.number 0 (some i.points)
  let autoantibodyNotes := [(2, D014.twoItemPoints), (3, D014.threeOrMorePoints)].map fun (n, p) =>
    pointRow "D014" ("bundle/" ++ toString n) "note" 0 0 (some p)
  let plasmaProteins := D015.ledgerItems.map fun i =>
    pointRow "D015" (reprStr i) "base" i.number 0 (some i.points)
  let igeCap := pointRow "D015" "specificIgeCap" "note" 13 0 (some D015.igeCapPoints)
  let cellular := D016.ledgerItems.map fun i =>
    pointRow "D016" (reprStr i) "base" i.number i.branch (some i.points)
  let bacterialMicroscopy := D017.ledgerItems.map fun i =>
    pointRow "D017" (reprStr i) "base" i.number 0 (some i.points)
  let smear := pointRow "D017" "concentrationSmear" "note" 1 0 (some D017.smearPoints)
  let culture := D018.ledgerItems.map fun i =>
    pointRow "D018" (reprStr i) "base" i.number 0 (some i.points)
  let cultureNotes := [
    pointRow "D018" "anaerobic" "note" 7 0 (some D018.anaerobicPoints),
    pointRow "D018" "fungal" "note" 8 0 (some D018.fungalPoints)]
  let susceptibility := D019.ledgerItems.map fun i =>
    pointRow "D019" (reprStr i) "base" i.number 0 (some i.points)
  let isolation := D020.ledgerItems.map fun i =>
    pointRow "D020" (reprStr i) "base" i.number 0 (some i.points)
  let otherMicrobiology := D023Other.ledgerItems.map fun i =>
    pointRow "D023-2" (reprStr i) "base" i.number 0 (some i.points)
  let microbiologyHeadings := [
    pointRow "D019-2" "yeastSusceptibility" "base" 0 0 (some D019Yeast.points),
    pointRow "D021" "mycobacteriaIdentification" "base" 0 0 (some D021.points),
    pointRow "D022" "mycobacteriaSusceptibility" "base" 0 0 (some D022.points)]
  let nuclearMicrobiology := D023Schedule.ledgerTiers.map fun i =>
    pointRow "D023" (reprStr i) "base" i.number i.branch (some i.base)
  let microbiologyNotes := [
    pointRow "D023" "hivConcentration" "note" 18 0 (some D023Schedule.concentrationPoints),
    pointRow "D023" "rapidNucleicAcid" "note" 29 0 (some D023.rapidPoints)]
  let microbiologyReferences := [
    pointRow "D023" "bk" "reference" 0 0 (some D023References.bkPoints),
    pointRow "D023" "mycobacteria" "reference" 0 0 (some D023References.mycobacteriaPoints)]
  let puncture := D004.ledgerItems.map fun item =>
    let price := item.fixedPoints
    pointRow "D004" (reprStr item |>.splitOn "." |>.getLast!)
      (if price.isSome then "base" else "reference") (item.number.getD 0) 0 price
  let cxcl10 := pointRow "D004" "cxcl10" "reference" 0 0
    (D004.scheduled { item := .cxcl10 })
  let methylation := pointRow "D004-3" "dnaMethylation" "base" 0 0 (some D004Methylation.points)
  let tumor := D004Tumor.ledgerItems.map fun item =>
    pointRow "D004-2" (reprStr item |>.splitOn "." |>.getLast!) "base"
      item.number 0 (some item.points)
  let tumorNotes :=
    ([2, 3, 4].map fun n => pointRow "D004-2" ("simple/" ++ toString n) "note"
      1 0 (D004Tumor.simpleBundlePoints n)) ++
    ([2, 3].map fun n => pointRow "D004-2" ("complex/" ++ toString n) "note"
      1 0 (D004Tumor.complexBundlePoints n))
  let coagulation := D006.ledgerItems.map fun item =>
    pointRow "D006" (reprStr item |>.splitOn "." |>.getLast!) "base"
      item.number 0 (some item.points)
  let coagulationNotes :=
    pointRow "D006" "rapidFibrinogen" "note" 4 0 (some D006.rapidFibrinogenPoints) ::
      ([3, 5].map fun n => pointRow "D006" ("bundle/" ++ toString n) "note"
        0 0 (D006.bundlePoints n))
  let leukemia := pointRow "D006-2" "hematopoieticTumorGene" "base" 0 0
    (some D006Leukemia.D006_2.points)
  let bcrAbl := D006Leukemia.D006_3.ledgerItems.map fun i =>
    pointRow "D006-3" (reprStr i |>.splitOn "." |>.getLast!) "base"
      i.number 0 (some D006Leukemia.D006_3.points)
  let genetic := D006Genetic.ledgerItems.map fun i =>
    pointRow "D006-4" (reprStr i |>.splitOn "." |>.getLast!) "base" i.number 0 (some i.points)
  let geneticBundle := D006Genetic.ledgerItems.map fun i =>
    pointRow "D006-4" (reprStr i |>.splitOn "." |>.getLast!) "note" 2 0
      (some (i.points + i.points / 2))
  let chromosome := D006Chromosome.ledgerItems.map fun i =>
    pointRow "D006-5" (reprStr i |>.splitOn "." |>.getLast!) "base" i.number 0 (some i.points)
  let banding := pointRow "D006-5" "banding" "note" 1 0 (some D006Chromosome.bandingPoints)
  let gene := D006GeneTests.ledgerItems.map fun i =>
    pointRow ("D006-" ++ toString i.suffix) (reprStr i |>.splitOn "." |>.getLast!)
      "base" 0 0 (some i.points)
  let ccr4 := pointRow "D006-10" "ccr4" "base" 0 0 (some D006GeneTests.Ccr4.points)
  let fusion := pointRow "D006-11" "fip1l1Pdgfra" "base" 0 0 (some D006GeneTests.Fusion.points)
  let egfr := pointRow "D006-12" "plasmaEgfr" "base" 0 0 (some D006GeneTests.Egfr.points)
  let egfrReduction := pointRow "D006-12" "monthlyReduction" "note" 0 0
    (some (90 * D006GeneTests.Egfr.points / 100))
  let residualDisease := D006GeneTests.ResidualDisease.ledgerItems.map fun i =>
    pointRow "D006-13" (reprStr i |>.splitOn "." |>.getLast!) "base" i.number 0 (some i.points)
  let oncology := D006Oncology.ledgerItems.map fun i =>
    pointRow ("D006-" ++ toString i.suffix) (reprStr i |>.splitOn "." |>.getLast!)
      "base" 0 0 (some i.points)
  let nudt15 := pointRow "D006-17" "nudt15" "base" 0 0 (some D006Oncology.Pharmacogenetics.points)
  let apoe := pointRow "D006-17" "apoe" "reference" 0 0 (some D006Oncology.Pharmacogenetics.points)
  let brca := D006Oncology.Brca.ledgerItems.map fun i =>
    pointRow "D006-18" (reprStr i |>.splitOn "." |>.getLast!) "base"
      i.number 0 (some D006Oncology.Brca.points)
  let profiling := D006Profiling.ledgerItems.map fun i =>
    pointRow "D006-19" (reprStr i |>.splitOn "." |>.getLast!) "base"
      i.number 0 (some D006Profiling.points)
  let targeted := D006Targeted.ledgerItems.map fun i =>
    pointRow ("D006-" ++ toString i.suffix) (reprStr i |>.splitOn "." |>.getLast!) "base"
      0 0 (some i.points)
  let plasmaPanel := D006PlasmaPanel.ledgerItems.map fun i =>
    pointRow "D006-27" (reprStr i |>.splitOn "." |>.getLast!) "base" i.number 0 (some i.points)
  let plasmaBundles := [4000, 6000, 8000, 12000].map fun p =>
    pointRow "D006-27" ("bundle" ++ toString p) "note" 0 0 (some p)
  let lateGenetic := D006Late.ledgerItems.map fun i =>
    pointRow ("D006-" ++ toString i.suffix) (reprStr i |>.splitOn "." |>.getLast!)
      "base" 0 0 (some i.points)
  let endocrine := D008.ledgerItems.map fun i =>
    pointRow "D008" (reprStr i |>.splitOn "." |>.getLast!) "base" i.number 0 (some i.points)
  let endocrineBundle := [410, 623, 900].map fun p =>
    pointRow "D008" ("bundle" ++ toString p) "note" 0 0 (some p)
  let remote := [1, 2].map fun n =>
    pointRow "D000" ("remote/" ++ toString n) "remote" 0 0 (some (Examinations.remotePoints
      { collections := (List.range n).map fun k => ⟨k, 0, .listed, .notPaired, none⟩
        usingInformationCommunicationEquipment := true
        patientWithNurseEtc := true }))
  let generalUrine := pointRow "D000" "generalUrine" "base" 0 0 (some D000.points)
  let specialUrine ← (← constructors ``UrineFecalTests.UrineSpecial).mapM fun ctor => do
    if ctor == ``UrineFecalTests.UrineSpecial.other then
      return pointRow "D001" "other" "reference" 22 0 none
    let item := mkConst ctor
    let number ← evalNat ``D001.ItemNumber item
    let rule ← evalExpr UrineFecalTests.PointRule (mkConst ``UrineFecalTests.PointRule)
      (mkApp (mkConst ``UrineFecalTests.urineSpecialPointRule) item)
    return match rule with
      | .fixed price => pointRow "D001" ctor.getString! "base" number 0 (some price)
      | .reference .. => pointRow "D001" ctor.getString! "reference" number 0 none
  let stripRatio := pointRow "D001" "stripProteinCreatinineRatio" "reference" 22 0
    (some (BloodChemistry.Item.points .creatinine))
  let sediment :=
    [pointRow "D002" "microscopy" "base" 0 0 (some (UrineSediment.Method.points .microscopy)),
     pointRow "D002" "stainedSpecimen" "note" 3 0 (some UrineSediment.stainPoints),
     pointRow "D002-2" "flow" "base" 0 0 (some (UrineSediment.Method.points .flow))]
  let fecal ← (← constructors ``UrineFecalTests.Fecal).mapM fun ctor => do
    let item := mkConst ctor
    let number ← evalNat ``D003.itemNumber item
    let price ← evalNat ``UrineFecalTests.fecalPoints item
    return pointRow "D003" ctor.getString! "base" number 0 (some price)
  let judgment := SpecimenJudgment.allCategories.map fun category =>
    pointRow "D026" (reprStr category) "base" category.number 0
      (some (SpecimenJudgment.scheduledPoints category))
  let judgmentNotes := [
    pointRow "D026" "managementI" "note" 8 0 (some SpecimenJudgment.managementIPoints),
    pointRow "D026" "marrow" "note" 10 0 (some SpecimenJudgment.marrowPoints),
    pointRow "D026" "electrophoresis" "note" 11 0 (some SpecimenJudgment.electrophoresisPoints)]
  let collectionItems : List (String × Nat × SpecimenCollection.Item) :=
    [("D400", 1, .venousBlood), ("D400", 2, .otherBlood),
      ("D401", 0, .ventricularPuncture), ("D402", 0, .suboccipitalPuncture),
      ("D403", 0, .lumbarPuncture), ("D404", 1, .sternalMarrowPuncture),
      ("D404", 2, .otherMarrowPuncture), ("D404-2", 0, .marrowBiopsy),
      ("D405", 0, .jointPuncture), ("D406", 0, .maxillarySinusPuncture),
      ("D406-2", 0, .peritonsillarTrialPuncture), ("D407", 0, .renalCystHydronephrosisPuncture),
      ("D408", 0, .douglasPuncture), ("D409", 0, .lymphNodeNeedleBiopsy),
      ("D410", 1, .breastBiopsyNeedle), ("D410", 2, .breastOther),
      ("D411", 0, .thyroidNeedleBiopsy), ("D409-2", 1, .sentinelCombined), ("D409-2", 2, .sentinelSingle),
      ("D412", 0, .percutaneousNeedleBiopsy),
      ("D412-2", 0, .percutaneousRenalBiopsy), ("D412-3", 0, .transjugularLiverBiopsy),
      ("D413", 1, .prostateMriUltrasoundFusion), ("D413", 2, .prostateOther),
      ("D414", 0, .endoscopicBiopsy), ("D414-2", 0, .eusFna),
      ("D415", 0, .transbronchialLungBiopsy), ("D415-2", 0, .ebusTbna),
      ("D415-3", 0, .navigatedLungBiopsy), ("D415-4", 0, .virtualBronchoscopyBiopsy),
      ("D415-5", 0, .transbronchialCryobiopsy), ("D415-6", 0, .parietalPleuralCryobiopsy),
      ("D416", 1, .thoracotomyTissue),
      ("D416", 2, .laparotomyTissue), ("D418", 1, .cervicalMucus),
      ("D418", 2, .vaginalCervicalTissue), ("D418", 3, .endometrialTissue),
      ("D419", 1, .gastricDuodenalFluid), ("D419", 2, .pleuralAsciticFluid),
      ("D419", 3, .arterialBlood), ("D419", 4, .anteriorChamberFluid),
      ("D419", 5, .adrenalVenousSampling), ("D419", 6, .nasalPharyngealSwab),
      ("D419-2", 0, .intraocularFluidExamination)]
  let tissueItems : List (Nat × Nat × SpecimenCollection.Item) :=
    [(1, 0, .skinTissue), (2, 0, .muscleTissue), (3, 0, .bonePelvisSpineTissue),
      (4, 1, .posteriorEyeTissue), (4, 2, .otherEyeTissue), (5, 0, .earTissue),
      (6, 0, .nasalSinusTissue), (7, 0, .oralTissue), (8, 0, .pharyngolaryngealTissue),
      (9, 0, .thyroidTissue), (10, 0, .breastTissue), (11, 0, .rectalTissue),
      (12, 0, .testisEpididymisTissue), (13, 0, .peripheralNerveTissue), (14, 0, .myocardiumTissue)]
  let tissue := tissueItems.map fun (number, branch, item) =>
    pointRow "D417" (reprStr item) "base" number branch (some (SpecimenCollection.basePoints item))
  let collections := collectionItems.map fun (code, number, item) =>
    pointRow code (reprStr item) "base" number 0 (some (SpecimenCollection.basePoints item))
  let collectionInfants : List (String × Nat × SpecimenCollection.Item) :=
    [("D400", 2, .venousBlood), ("D401", 0, .ventricularPuncture),
      ("D402", 0, .suboccipitalPuncture), ("D403", 0, .lumbarPuncture),
      ("D404", 0, .sternalMarrowPuncture), ("D404-2", 0, .marrowBiopsy),
      ("D405", 0, .jointPuncture), ("D407", 0, .renalCystHydronephrosisPuncture),
      ("D416", 0, .laparotomyTissue), ("D417", 0, .skinTissue), ("D419", 2, .pleuralAsciticFluid), ("D419", 3, .arterialBlood),
      ("D419", 4, .anteriorChamberFluid), ("D419", 5, .adrenalVenousSampling)]
  let collectionNotes := collectionInfants.map fun (code, noteNumber, item) =>
    pointRow code "infant" "note" noteNumber 0 (some (SpecimenCollection.infantPoints item 0))
  return [generalUrine] ++ remote ++ specialUrine ++ [stripRatio] ++ sediment ++ fecal ++ blood.flatten ++ chemistry.reverse ++ puncture ++ [cxcl10, methylation] ++
    tumor ++ tumorNotes ++ coagulation ++ coagulationNotes ++ [leukemia] ++ bcrAbl ++
    genetic ++ geneticBundle ++ chromosome ++ [banding] ++ gene ++
    [ccr4, fusion, egfr, egfrReduction] ++ residualDisease ++ oncology ++ [nudt15, apoe] ++
    brca ++ profiling ++ targeted ++ plasmaPanel ++ plasmaBundles ++ lateGenetic ++
    endocrine ++ endocrineBundle ++ markers ++ markerBundle ++ special ++ immuneBlood ++ infection ++ [infectionCap, infectionClassCap] ++
    hepatitis ++ hepatitisNotes ++ autoantibodies ++ autoantibodyNotes ++ plasmaProteins ++ [igeCap] ++
    cellular ++ bacterialMicroscopy ++ [smear] ++ culture ++ cultureNotes ++ susceptibility ++
    isolation ++ microbiologyHeadings ++ otherMicrobiology ++ nuclearMicrobiology ++ microbiologyNotes ++ microbiologyReferences ++ judgment ++ judgmentNotes ++ specimens ++ collections ++ tissue ++ collectionNotes ++
    [pointRow "D415" "guideSheath" "note" 1 0 (some 500),
      pointRow "D415" "ctFluoroscopy" "note" 2 0 (some 1000),
      pointRow "D415" "endomicroscopy" "note" 3 0 (some 1500),
      pointRow "D415-4" "guideSheath" "note" 0 0 (some 500)]

private unsafe def exportLedger : CommandElabM Unit := liftTermElabM do
  let result ← MetaM.run' do
    return Json.mkObj [("rules", toJson (← rules)), ("points", toJson (← points))]
  IO.println result.compress

@[implemented_by exportLedger]
private opaque runLedger : CommandElabM Unit := pure ()

elab "#fee_ledger" : command => runLedger
#fee_ledger
