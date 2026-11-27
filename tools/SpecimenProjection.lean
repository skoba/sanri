import Sanri.CaseStudies.GlycemicTables
import Sanri.CaseStudies.PunctureAgeTables
import Sanri.CaseStudies.RenalTestFrequency
import Sanri.CaseStudies.SpecimenPairwiseTables
import Sanri.CaseStudies.Pf4Tables
import Lean

open Lean Sanri.MedicalFee.CaseStudies TableProjection SpecimenPairwiseTables
deriving instance Repr for Sanri.MedicalFee.D011.Item

private def label [Repr Item] (item : Item) : String :=
  ((reprStr item).splitOn ".").getLast!

private def pairs [Repr Item] (rows : List (Pair Item)) : Json :=
  toJson (rows.map fun r => [toJson (label r.left), toJson (label r.right),
    toJson r.unit, toJson r.direction, toJson r.special])

private def frequencies [Repr Item] (rows : List (Frequency Item)) : Json :=
  toJson (rows.map fun r => [toJson (label r.item), toJson r.unit, toJson r.limit, toJson r.special])

#eval IO.println (Json.mkObj [
  ("glycemic_pairs", pairs GlycemicTables.pairObservation),
  ("glycemic_frequency", frequencies GlycemicTables.frequencyObservation),
  ("renal_frequency", frequencies RenalTestFrequency.frequencyObservation),
  ("puncture_age", toJson [let r := PunctureAgeTables.ageObservation
                           [toJson (label r.target), toJson r.lower, toJson r.upper, toJson r.points]]),
  ("coagulation", pairs coagulationObservation),
  ("electrophoresis", pairs electrophoresisObservation),
  ("pf4", pairs Pf4Tables.observation),
  ("d014", pairs d014Observation),
  ("d014_missing", pairs d014MissingObservation),
  ("pancreatic_missing", pairs pancreaticMissingObservation),
  ("pneumococcus_missing", pairs pneumococcusMissingObservation),
  ("pertussis_missing", pairs pertussisMissingObservation),
  ("respiratory_missing", pairs respiratoryMissingObservation)
]).compress
