import Sanri.D023Schedule
import Sanri.History

namespace Sanri.MedicalFee.D023References

open Sanri.Logic Sanri.History
open SpecimenTests

inductive BkIndicationClause where
  | nephropathy | cystitis | treatmentEffect | activation
  deriving DecidableEq

def BkIndicationClause.suffix : BkIndicationClause → String
  | .nephropathy => "a"
  | .cystitis => "i"
  | .treatmentEffect => "u"
  | .activation => "e"

def BkIndicationClause.indication : BkIndicationClause → BkIndication
  | .nephropathy => .suspectedNephropathy
  | .cystitis => .suspectedHemorrhagicCystitis
  | .treatmentEffect => .treatmentEffectAfterBkTreatmentStarted
  | .activation => .activationDuringRejectionOrGvhdTreatment

def bkEligibility (clause : BkIndicationClause) : Rule BkRequest Unit :=
  ⟨"notice/D023/paragraph/42/" ++ clause.suffix, d023BkSource,
    fun r _ => r.indication = some clause.indication⟩

def BkEligible (r : BkRequest) : Prop :=
  r.insuranceMedicalInstitution = true ∧ r.performed = true ∧
  (r.specimen = .plasma ∨ r.specimen = .urine) ∧
  r.organOrHematopoieticCellTransplant = true ∧
  ((bkEligibility .nephropathy).holds r () ∨ (bkEligibility .cystitis).holds r () ∨
    (bkEligibility .treatmentEffect).holds r () ∨ (bkEligibility .activation).holds r ())

def bkPoints : Nat := D023Schedule.Tier.viralOrMethicillinGroup.base

def bkRate : Rule BkRequest Nat :=
  ⟨"notice/D023/paragraph/42", d023BkSource, fun r p => BkEligible r ∧ p = bkPoints⟩

def bkDocumentation : Rule BkRequest (Option BkIndication) :=
  ⟨"notice/D023/paragraph/42", d023BkSource, fun r entry =>
    ∃ indication, r.indication = some indication ∧ entry = some indication⟩

structure MycobacteriaContext where
  request : MycobacteriaRequest
  performance : Performance Unit
  treatmentScope : Scope
  /-- 項目は照合済みの一連の治療ID。 -/
  history : ClaimHistory Nat

def MycobacteriaContext.prior (c : MycobacteriaContext) : Option Nat := do
  let series ← c.performance.series
  if c.treatmentScope.institution = some c.performance.site.institution ∧
      c.treatmentScope.Includes c.performance.site = true then
    count c.history c.treatmentScope (· == series)
  else none

def bcgIndication : Rule MycobacteriaContext Unit :=
  ⟨"notice/D023/paragraph/43/a/i", d023MycobacteriaSource, fun c _ =>
    c.request.indication = some .symptomaticAfterIntravesicalBcgNeedingDifferentiation⟩

def pulmonaryIndication : Rule MycobacteriaContext Unit :=
  ⟨"notice/D023/paragraph/43/a/ro", d023MycobacteriaSource, fun c _ =>
    c.request.indication = some .suspectedPulmonaryTbAndNontuberculousDisease⟩

def mycobacteriaIndication : Rule MycobacteriaContext Unit :=
  ⟨"notice/D023/paragraph/43/a", d023MycobacteriaSource, fun c _ =>
    bcgIndication.holds c () ∨ pulmonaryIndication.holds c ()⟩

def mycobacteriaStaffing : Rule MycobacteriaContext Unit :=
  ⟨"notice/D023/paragraph/43/i", d023MycobacteriaSource, fun c _ =>
    c.request.staffingRequirementMet = true⟩

def MycobacteriaEligible (c : MycobacteriaContext) : Prop :=
  c.request.insuranceMedicalInstitution = true ∧ c.request.performed = true ∧
  (c.request.specimen = .sputum ∨ c.request.specimen = .culturedOrganism) ∧
  c.request.dnaDetectionByPcrRsso = true ∧ 28 ≤ c.request.panelSize ∧
  c.prior = some 0 ∧ mycobacteriaIndication.holds c () ∧ mycobacteriaStaffing.holds c ()

def mycobacteriaPoints : Nat := D023Schedule.Tier.respiratoryPanelWithoutCovid.base

def mycobacteriaRate : Rule MycobacteriaContext Nat :=
  ⟨"notice/D023/paragraph/43", d023MycobacteriaSource, fun c p =>
    MycobacteriaEligible c ∧ p = mycobacteriaPoints⟩

def mycobacteriaDocumentation :
    Rule MycobacteriaContext (Option MycobacteriaIndication × Bool) :=
  ⟨"notice/D023/paragraph/43/a", d023MycobacteriaSource, fun c entry =>
    ∃ indication, c.request.indication = some indication ∧ entry = (some indication, true)⟩

theorem bk_determines : DeterminesOn BkEligible [bkRate] := by
  intro r h
  simp [satisfies_cons, satisfies_nil, bkRate, h, DeterminesAt, SatisfiableAt, UniqueAt]

theorem mycobacteria_determines : DeterminesOn MycobacteriaEligible [mycobacteriaRate] := by
  intro c h
  simp [satisfies_cons, satisfies_nil, mycobacteriaRate, h, DeterminesAt, SatisfiableAt, UniqueAt]

private theorem bkReferenceRate : (lookup .d023 17 0).bind (·.points) = some 450 := rfl

private theorem mycobacteriaReferenceRate : (lookup .d023 25 2).bind (·.points) = some 963 := rfl

theorem bk_legacy (r : BkRequest) (p : Nat)
    (doc : bkDocumentation.holds r r.recordedIndication) :
    bkRate.holds r p ↔ bkReferencePoints r = some p := by
  obtain ⟨indication, hi, hd⟩ := doc
  cases hs : r.specimen <;> cases indication <;>
    simp [bkRate, bkPoints, D023Schedule.Tier.base, BkEligible, bkEligibility, BkIndicationClause.indication,
      bkReferencePoints, hi, hd, hs, BkIndicationClause.suffix, bkReferenceRate, and_assoc, @eq_comm Nat p 450]

theorem mycobacteria_legacy (c : MycobacteriaContext) (p : Nat)
    (history : c.prior = some c.request.claimsInTreatmentSeries)
    (doc : mycobacteriaDocumentation.holds c
      (c.request.recordedIndication, c.request.necessityRecorded)) :
    mycobacteriaRate.holds c p ↔ mycobacteriaReferencePoints c.request = some p := by
  obtain ⟨indication, hi, hd⟩ := doc
  have hr : c.request.recordedIndication = some indication := congrArg Prod.fst hd
  have hn : c.request.necessityRecorded = true := congrArg Prod.snd hd
  cases hs : c.request.specimen <;> cases indication <;>
    simp [mycobacteriaRate, mycobacteriaPoints, D023Schedule.Tier.base, MycobacteriaEligible, mycobacteriaIndication, bcgIndication,
      pulmonaryIndication, mycobacteriaStaffing, mycobacteriaReferencePoints, hi, hr, hn,
      history, hs, mycobacteriaReferenceRate, and_assoc, and_left_comm, and_comm, @eq_comm Nat p 963]

/-- 既存集計に渡す実施と、条項側の確認に使った履歴を保持する。 -/
inductive Assessment where
  | bk (id : Nat) (r : BkRequest)
  | mycobacteria (c : MycobacteriaContext)

def Assessment.legacy : Assessment → Nat × SpecimenJudgment.D023Reference
  | .bk id r => (id, .bk r)
  | .mycobacteria c => (c.performance.id, .mycobacteria c.request)

def Assessment.Valid : Assessment → Prop
  | .bk _ r => ∃ p, bkRate.holds r p ∧ bkDocumentation.holds r r.recordedIndication
  | .mycobacteria c => ∃ p, mycobacteriaRate.holds c p ∧
      c.prior = some c.request.claimsInTreatmentSeries ∧
      mycobacteriaDocumentation.holds c (c.request.recordedIndication, c.request.necessityRecorded)

theorem Assessment.legacy_has_points (a : Assessment) (h : a.Valid) :
    ∃ p, a.legacy.2.points = some p := by
  cases a with
  | bk id r =>
    obtain ⟨p, hp, hd⟩ := h
    exact ⟨p, (bk_legacy r p hd).mp hp⟩
  | mycobacteria c =>
    obtain ⟨p, hp, hh, hd⟩ := h
    exact ⟨p, (mycobacteria_legacy c p hh hd).mp hp⟩

def apply (references : List Assessment) (_ : ∀ a ∈ references, a.Valid)
    (judgment : SpecimenJudgment.Context) (specimen : Examinations.SpecimenContext) :
    Option Examinations.SpecimenContext :=
  SpecimenJudgment.applyD023References (references.map Assessment.legacy) judgment specimen

private def bkSample : BkRequest :=
  ⟨true, true, .urine, true, some .suspectedNephropathy, some .suspectedNephropathy⟩

example : bkRate.holds bkSample 450 := by
  exact (bk_legacy _ _ ⟨_, rfl, rfl⟩).mpr rfl

example : ¬ BkEligible { bkSample with specimen := .other } := by
  simp [BkEligible]

end Sanri.MedicalFee.D023References
