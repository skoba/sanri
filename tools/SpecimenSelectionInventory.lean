import Sanri.SpecimenRawDay
import Lean

open Lean Sanri.History Sanri.MedicalFee SpecimenSelectionInventory SpecimenSelectionGeneration

private def inventoryRow (g : Entry) :=
  (g.id, g.members)

private def clauseAt (i : Nat) : String :=
  (inventory[i]?.map Entry.id).getD ""

private def statusName : GenerationStatus → String
  | .raw => "raw"
  | .reading => "reading"
  | .confirmed => "confirmed"
  | .pending => "pending"

private def genericStatus (g : Entry) : String :=
  if let some reason := g.outsideReason then "outside/" ++ reprStr reason else
  match mode g with
  | .ok _ =>
    let keys := SpecimenRawDay.checkedSelectionKeys ++ SpecimenRawDay.registeredSelectionKeys
    if !(keys.map Prod.fst).contains g.id then "generated_unchecked"
    else if g.dayRegistration == some .conditional then "generated_conditional"
    else "generated_checked_shape"
  | .error .unknownCardinality => "pending_cardinality"
  | .error reason => "outside/" ++ reprStr reason

private def dayStatus (g : Entry) : GenerationStatus :=
  match g.dayRegistration with
  | some .conditional => .confirmed
  | some .identified => if g.unit == .unresolved then .reading else .raw
  | none => g.generation

private def syntheticSite : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def syntheticRows (keys : List ItemKey) : List Row :=
  keys.zipIdx.map fun (key, id) =>
    { id, site := syntheticSite, item := key, simultaneous := some 1, specimen := some 1, draw := some 1 }

private def registeredBoundaries : Bool :=
  let conditionChecks := (inventory.filter (fun g => g.dayRegistration == some .conditional)).all
    fun g =>
      let rows := syntheticRows g.members
      let generateWith := fun condition => generateRegistered g rows (fun _ => some .simultaneous)
        (fun _ _ => condition)
      let pending := match generateWith none with
        | .error .missingCondition => true
        | _ => false
      (generateWith (some true)).toOption.map List.length == some 1 &&
        (generateWith (some false)).toOption.map List.length == some 0 && pending
  let anchorChecks := (inventory.filter (·.dayAnchor.isSome)).all fun g =>
    let rows := syntheticRows (g.members.filter fun key => g.dayAnchor != some key)
    (generateRegistered g rows (fun _ => none) (fun _ _ => none)).toOption.map List.length == some 0
  conditionChecks && anchorChecks

/-- 登録部分の構成ごとに、同じ実施単位での上限の解を照合する合成入力。 -/
private def componentWitness (is : List Nat) : Json := Id.run do
  let entries := is.filterMap (inventory[·]?)
  let registered := entries.filter (·.dayRegistration.isSome)
  let keys := (entries.flatMap Entry.members).eraseDups
  let rows := syntheticRows keys
  let results := registered.map fun entry =>
    generateRegistered entry rows (fun _ => some .simultaneous)
      (fun id _ => some (id == "notice/D014/paragraph/16/i"))
  let generated := results.flatMap fun result => result.toOption.getD []
  let chosen := (generated.flatMap Instance.members).head?.map (·.id)
  let check := fun (ids : List Nat) =>
    generated.all fun group => group.checkSelection (fun id => some (ids.contains id))
  return Json.mkObj [
    ("clauses", toJson (entries.map Entry.id)),
    ("registered", toJson (registered.map Entry.id)),
    ("generated", toJson generated.length),
    ("all_generated", toJson (results.all (·.isOk))),
    ("empty", toJson (check [])),
    ("singleton", toJson (chosen.map fun id => check [id]))]

private def summary : Json := Json.mkObj [
  ("inventory", toJson ((inventory.filter Entry.inAuditIndex).map inventoryRow)),
  ("outside_index", toJson ((inventory.filter fun g => !g.inAuditIndex).map inventoryRow)),
  ("overlaps", toJson (overlaps.map fun (a, b, ids) =>
    ((clauseAt a, clauseAt b), ids.map fun i => indexedItems[i]!))),
  ("components", toJson (components.map (·.map clauseAt))),
  ("registered_boundaries", toJson registeredBoundaries),
  ("component_witnesses", toJson (components.map componentWitness)),
  ("clause_constraints", toJson inventory.length),
  ("projections", toJson (inventory.countP (·.evidence.projection.isSome))),
  ("raw_generation", toJson (inventory.countP (fun g => g.evidence.rawGeneration || g.dayRegistration.isSome))),
  ("generic_generation", toJson (inventory.map fun g => (g.id, genericStatus g))),
  ("generic_typed_keys", toJson (SpecimenRawDay.checkedSelectionKeys ++ SpecimenRawDay.registeredSelectionKeys)),
  ("generation", toJson (inventory.map fun g => (g.id, statusName (dayStatus g)))),
  ("evidence", toJson (inventory.map fun g =>
    (g.clauseConstraint, g.evidence.unitWording, g.evidence.projection, g.evidence.rawGeneration, g.memberGap))),
  ("unresolved_unit", toJson (inventory.countP (·.unit == .unresolved)))]

#eval IO.println summary.compress
