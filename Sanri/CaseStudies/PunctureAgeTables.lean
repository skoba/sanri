import Sanri.SimplePunctures

namespace Sanri.MedicalFee.CaseStudies.PunctureAgeTables

open Sanri.Logic SimplePunctures

/-- 基本項目の年齢加算欄からD401と共通の加算を参照する。
ここでは年齢区間と参照先の固定加算点数を射影する。 -/
def ageSlot : Rule Context Result :=
  ⟨"puncture/age-slot",
   ⟨.electronicTable, "医科診療行為マスター", "2026-11-02公開版",
    "D402の年齢加算欄からD401の注加算を参照", .checkedAgainstSource, none⟩,
   fun c r => r.infant =
     if c.ageYears < 6 then SpecimenCollection.infantPoints .ventricularPuncture 0 else 0⟩

def Scope (c : Context) : Prop :=
  c.separate ∧ c.performance.item = .suboccipital

theorem age_equivalent :
    EquivalentOn Scope [suboccipitalInfant] [ageSlot] := by
  apply equivalentOn_iff.mpr
  intro c hc r
  simp only [satisfies_cons, satisfies_nil, and_true]
  change (c.separate → c.performance.item = .suboccipital →
     r.infant = 1 * (if c.ageYears < 6 then 100 else 0)) ↔ ageSlot.holds c r
  simp [ageSlot, hc.1, hc.2, SpecimenCollection.infantPoints,
    SpecimenCollection.isD400, SpecimenCollection.isD417]

private def exampleContext (age : Nat) : Context :=
  ⟨{ id := 1, site := ⟨1, 1, ⟨⟨2026, 10, by decide⟩, 22, by decide⟩⟩,
      item := .suboccipital },
    age, 1, .one, false, false, true, none⟩

example : Scope (exampleContext 5) ∧ ageSlot.holds (exampleContext 5) ⟨0, 100⟩ := by
  exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩

example : Scope (exampleContext 6) ∧ ageSlot.holds (exampleContext 6) ⟨0, 0⟩ := by
  exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩

end Sanri.MedicalFee.CaseStudies.PunctureAgeTables
