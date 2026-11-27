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
  let id ← if id.hasFVar then pure "" else evalExpr String (mkConst ``String) id
  let fields := [("module", module), ("definition", name), ("id", id)]
  if source.hasFVar then
    return Json.mkObj ((fields ++ [("classification", "parameterized")]).map
      (fun (key, value) => (key, toJson value)) ++
      ["kind", "identifier", "edition", "location", "verification"].map (·, Json.null))
  let ref ← evalExpr SourceRef (mkConst ``SourceRef) source
  return jsonFields (fields ++ [
    ("kind", (reprStr ref.kind).replace "Sanri.Logic.SourceKind." ""),
    ("identifier", ref.identifier), ("edition", ref.edition), ("location", ref.location),
    ("verification", (reprStr ref.verification).replace "Sanri.Logic.SourceVerification." "")])

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
        else continue -- 同じ項目は further に含まれる。
      let kind := if ctor == ``D007.ScopedItem.urinarySulfatedBileAcids then "reference" else "base"
      chemistry := pointRow "D007" label kind number 0 price :: chemistry
  let specimens := SpecimenTests.catalog.flatMap fun entry =>
    let code := (reprStr entry.code |>.splitOn "." |>.getLast! |>.toUpper).replace "_" "-"
    entry.variants.map fun item => pointRow code item "base" entry.number entry.branch entry.points
  let puncture := D004.ledgerItems.map fun item =>
    let price := item.fixedPoints
    pointRow "D004" (reprStr item |>.splitOn "." |>.getLast!)
      (if price.isSome then "base" else "reference") (item.number.getD 0) 0 price
  let cxcl10 := pointRow "D004" "cxcl10" "reference" 0 0
    (D004.scheduled { item := .cxcl10 })
  return blood.flatten ++ chemistry.reverse ++ puncture ++ [cxcl10] ++ specimens

private unsafe def exportLedger : CommandElabM Unit := liftTermElabM do
  let result ← MetaM.run' do
    return Json.mkObj [("rules", toJson (← rules)), ("points", toJson (← points))]
  IO.println result.compress

@[implemented_by exportLedger]
private opaque runLedger : CommandElabM Unit := pure ()

elab "#fee_ledger" : command => runLedger
#fee_ledger
