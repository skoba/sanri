namespace Sanri
namespace MedicalFee

inductive Section where
  | generalRules -- Tsusoku
  | basicFees -- Kihon Shinryou-ryo
  | specialFees -- Tokukei Shinryou-ryo
  deriving DecidableEq, Repr

inductive FeeItem where
  | initialConsultation -- Shoshinryou
  | revisitConsultation -- Saishinryou
  | outpatientConsultation -- Gairai Shinryou-ryo
  | prescriptionFee -- Shohousenryou
  deriving DecidableEq, Repr

inductive Facility where
  | clinic
  | hospital (beds : Nat)
  deriving DecidableEq, Repr

structure Claim where
  day : Nat
  item : FeeItem
  deriving DecidableEq, Repr

def sectionOf : FeeItem → Section
  | .initialConsultation => .basicFees
  | .revisitConsultation => .basicFees
  | .outpatientConsultation => .basicFees
  | .prescriptionFee => .specialFees

def pointsAt (facility : Facility) : FeeItem → Option Nat
  | .initialConsultation => some 291
  | .revisitConsultation =>
      match facility with
      | .clinic => some 76
      | .hospital beds => if beds < 200 then some 76 else none
  | .outpatientConsultation =>
      match facility with
      | .clinic => none
      | .hospital beds => if 200 ≤ beds then some 77 else none
  | .prescriptionFee => none

theorem initialConsultation_isBasic :
    sectionOf .initialConsultation = .basicFees := rfl

theorem revisitConsultation_isBasic :
    sectionOf .revisitConsultation = .basicFees := rfl

theorem outpatientConsultation_isBasic :
    sectionOf .outpatientConsultation = .basicFees := rfl

theorem prescriptionFee_isSpecial :
    sectionOf .prescriptionFee = .specialFees := rfl

theorem initialConsultation_points (facility : Facility) :
    pointsAt facility .initialConsultation = some 291 := rfl

theorem clinic_revisitConsultation_points :
    pointsAt .clinic .revisitConsultation = some 76 := rfl

theorem hospital_under200_revisitConsultation_points (beds : Nat)
    (h : beds < 200) :
    pointsAt (.hospital beds) .revisitConsultation = some 76 := by
  simp [pointsAt, h]

theorem hospital_200_or_more_revisitConsultation_unavailable (beds : Nat)
    (h : 200 ≤ beds) :
    pointsAt (.hospital beds) .revisitConsultation = none := by
  simp [pointsAt, Nat.not_lt.mpr h]

theorem hospital_under200_outpatientConsultation_unavailable (beds : Nat)
    (h : beds < 200) :
    pointsAt (.hospital beds) .outpatientConsultation = none := by
  simp [pointsAt, Nat.not_le.mpr h]

theorem hospital_200_or_more_outpatientConsultation_points (beds : Nat)
    (h : 200 ≤ beds) :
    pointsAt (.hospital beds) .outpatientConsultation = some 77 := by
  simp [pointsAt, h]

def NoSameDayInitialAndRevisit (claims : List Claim) : Prop :=
  ∀ day : Nat,
    Claim.mk day .initialConsultation ∈ claims →
    Claim.mk day .revisitConsultation ∉ claims

theorem sameDayInitialAndRevisit_not_allowed
    (claims : List Claim)
    (day : Nat)
    (initialClaim : Claim.mk day .initialConsultation ∈ claims)
    (revisitClaim : Claim.mk day .revisitConsultation ∈ claims) :
    ¬ NoSameDayInitialAndRevisit claims := by
  intro noSameDayClaims
  exact noSameDayClaims day initialClaim revisitClaim

end MedicalFee
end Sanri
