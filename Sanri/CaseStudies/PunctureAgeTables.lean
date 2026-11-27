import Sanri.SimplePunctures
import Sanri.CaseStudies.TableProjection

namespace Sanri.MedicalFee.CaseStudies.PunctureAgeTables

open Sanri.Logic SimplePunctures TableProjection

inductive Addition where
  | d401Infant
  deriving Repr

def ageObservation : AgeAddition Addition := ⟨.d401Infant, 0, 6, 100⟩

/-- 基本項目の年齢加算欄からD401と共通の加算を参照する。
ここでは年齢区間と参照先の固定加算点数を射影する。 -/
def ageSlot (referencedPoints : Nat) : Rule Context Result :=
  ⟨"puncture/age-slot",
   ⟨.electronicTable, "医科診療行為マスター", "2026-11-02公開版",
    "D402の年齢加算欄からD401の注加算を参照", .checkedAgainstSource, none⟩,
   fun c r => r.infant = ({ ageObservation with points := referencedPoints }).atAge c.ageYears⟩

def Scope (c : Context) : Prop :=
  c.separate ∧ c.performance.item = .suboccipital

/-- 別算定するD402の一実施について、基本行の年齢区間と参照先加算行から
得る加算点数が告示注の加算点数と一致する。参照先の点数は局所照合の前提。 -/
theorem age_equivalent (referencedPoints : Nat) (d401Points : referencedPoints = 100) :
    EquivalentOn Scope [suboccipitalInfant] [ageSlot referencedPoints] := by
  apply equivalentOn_iff.mpr
  intro c hc r
  simp only [satisfies_cons, satisfies_nil, and_true]
  change (c.separate → c.performance.item = .suboccipital →
     r.infant = 1 * (if c.ageYears < 6 then 100 else 0)) ↔ (ageSlot referencedPoints).holds c r
  simp [ageSlot, ageObservation, AgeAddition.atAge, hc.1, hc.2, d401Points]

theorem observed_age_equivalent :
    EquivalentOn Scope [suboccipitalInfant] [ageSlot ageObservation.points] :=
  age_equivalent _ rfl

private def exampleContext (age : Nat) : Context :=
  ⟨{ id := 1, site := ⟨1, 1, ⟨⟨2026, 10, by decide⟩, 22, by decide⟩⟩,
      item := .suboccipital },
    age, 1, .one, false, false, true, none⟩

example : Scope (exampleContext 5) ∧ (ageSlot 100).holds (exampleContext 5) ⟨0, 100⟩ := by
  exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩

example : Scope (exampleContext 6) ∧ (ageSlot 100).holds (exampleContext 6) ⟨0, 0⟩ := by
  exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩

end Sanri.MedicalFee.CaseStudies.PunctureAgeTables
