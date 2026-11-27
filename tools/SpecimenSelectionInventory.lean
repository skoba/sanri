import Sanri.SpecimenSelectionInventory
import Lean

open Lean Sanri.MedicalFee.SpecimenSelectionInventory

private def inventoryRow (g : Entry) :=
  (g.id, g.members)

private def clauseAt (i : Nat) : String :=
  (inventory[i]?.map Entry.id).getD ""

private def summary : Json := Json.mkObj [
  ("inventory", toJson ((inventory.filter Entry.inAuditIndex).map inventoryRow)),
  ("outside_index", toJson ((inventory.filter fun g => !g.inAuditIndex).map inventoryRow)),
  ("overlaps", toJson (overlaps.map fun (a, b, ids) =>
    ((clauseAt a, clauseAt b), ids.map fun i => indexedItems[i]!))),
  ("components", toJson (components.map (·.map clauseAt))),
  ("complete", toJson (inventory.countP (·.connection == .complete))),
  ("partial", toJson (inventory.countP (·.connection == .partiallyConnected))),
  ("unconnected", toJson (inventory.countP (·.connection == .unconnected))),
  ("unresolved_unit", toJson (inventory.countP (·.unit == .unresolved)))]

#eval IO.println summary.compress
