import Sanri.SpecimenRawDay
import Lean

open Lean Sanri.MedicalFee SpecimenSelectionInventory SpecimenSelectionGeneration

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
  match mode g with
  | .ok _ => if (SpecimenRawDay.checkedSelectionKeys.map Prod.fst).contains g.id
    then "generated_checked_shape" else "generated_unchecked"
  | .error .unknownCardinality => "pending_cardinality"
  | .error reason => "outside/" ++ reprStr reason

private def summary : Json := Json.mkObj [
  ("inventory", toJson ((inventory.filter Entry.inAuditIndex).map inventoryRow)),
  ("outside_index", toJson ((inventory.filter fun g => !g.inAuditIndex).map inventoryRow)),
  ("overlaps", toJson (overlaps.map fun (a, b, ids) =>
    ((clauseAt a, clauseAt b), ids.map fun i => indexedItems[i]!))),
  ("components", toJson (components.map (·.map clauseAt))),
  ("clause_constraints", toJson inventory.length),
  ("projections", toJson (inventory.countP (·.evidence.projection.isSome))),
  ("raw_generation", toJson (inventory.countP (·.evidence.rawGeneration))),
  ("generic_generation", toJson (inventory.map fun g => (g.id, genericStatus g))),
  ("generic_typed_keys", toJson SpecimenRawDay.checkedSelectionKeys),
  ("generation", toJson (inventory.map fun g => (g.id, statusName g.generation))),
  ("evidence", toJson (inventory.map fun g =>
    (g.clauseConstraint, g.evidence.unitWording, g.evidence.projection, g.evidence.rawGeneration, g.memberGap))),
  ("unresolved_unit", toJson (inventory.countP (·.unit == .unresolved)))]

#eval IO.println summary.compress
