import Sanri.SpecimenCrossDivision

namespace Sanri.MedicalFee.CaseStudies.SpecimenPairwiseTables

/-- Three confirmed performances after projecting medical eligibility and time scope. -/
def AtMostOne (a b c : Bool) : Prop :=
  a.toNat + b.toNat + c.toNat ≤ 1

/-- D006(8)イ. Restrict to one performance per item with confirmed simultaneous measurement.
The three symmetric exclusions are an input to the comparison. -/
theorem coagulation_full_pairs :
    ∀ a b c : Bool, AtMostOne a b c ↔
      (a && b) = false ∧ (a && c) = false ∧ (b && c) = false := by
  intro a b c
  cases a <;> cases b <;> cases c <;> unfold AtMostOne <;> decide

/-- D015(4)イ. Restrict to three eligible, simultaneous performances of the same specimen.
The examined table projection retains the first two items' pair. -/
theorem electrophoresis_partial_pairs :
    ∀ a b c : Bool, AtMostOne a b c → (a && b) = false := by
  intro a b c
  cases a <;> cases b <;> cases c <;> unfold AtMostOne <;> decide

theorem electrophoresis_partial_pairs_has_extra_selection :
    ∃ a b c : Bool, (a && b) = false ∧ ¬ AtMostOne a b c := by
  exact ⟨true, false, true, rfl, by unfold AtMostOne; decide⟩

end Sanri.MedicalFee.CaseStudies.SpecimenPairwiseTables
