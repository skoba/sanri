import Sanri.UrineFecalTests
import Sanri.SpecimenJudgment
import Sanri.SpecimenRules
import Sanri.D000

namespace Sanri.MedicalFee.UrineSediment

open Sanri.Logic Sanri.History UrineFecalTests

inductive Method where
  | microscopy | flow
  deriving DecidableEq

inductive FlowComponent where
  | redCells | whiteCells | epithelialCells | casts | bacteria

inductive Location where
  | directInHouse
  | contractedInHouse (promptReport : Option Bool)
  | contractedExternal (clinic strongUrinaryDiseaseSuspicion laboratory promptReport : Option Bool)
      (elapsedSeconds : Option Nat)

inductive Indication where
  | generalUrineFinding (exam : Performance Unit)
  | specialUrineFinding (exam : Performance UrineSpecial)
  | medicallyNecessaryOnExamination

inductive D017Relation where
  | noCombinedPerformance
  | combined (exam : Performance Unit) (main : Option MainTest)

structure Context where
  performance : Performance Method
  indication : Option Indication
  location : Option Location
  d017 : Option D017Relation
  otherSedimentPerformed : Option Bool
  chosenSedimentMethod : Option Method
  stained : Option Bool := none
  /-- 実施ごとの測定記録。親実施と同時実施IDを共有する。 -/
  flowMeasurements : List (Performance FlowComponent) := []

def Indicated (c : Context) : Prop :=
  match c.indication with
  | some (.generalUrineFinding prior) =>
    prior.site.patient = c.performance.site.patient ∧ prior.site.date.key ≤ c.performance.site.date.key
  | some (.specialUrineFinding prior) =>
    prior.site.patient = c.performance.site.patient ∧ prior.site.date.key ≤ c.performance.site.date.key
  | some .medicallyNecessaryOnExamination => True
  | none => False

def InHouse (c : Context) : Prop :=
  c.location = some .directInHouse ∨ ∃ report, c.location = some (.contractedInHouse report)

def ConfirmedClinicException (c : Context) : Prop :=
  ∃ elapsed, c.location = some (.contractedExternal (some true) (some true)
    (some true) (some true) (some elapsed)) ∧ elapsed ≤ 4 * 60 * 60

def MicroscopyLocation (c : Context) : Prop :=
  c.location = some .directInHouse ∨ c.location = some (.contractedInHouse (some true)) ∨
    ConfirmedClinicException c

def PreferD017 (c : Context) : Prop :=
  ∃ exam, c.d017 = some (.combined exam (some .d017BacterialMicroscopy)) ∧
    (show Performance Unit from { c.performance with item := () }).sameSpecimen exam = some true

def D017SelectionKnown (c : Context) : Prop :=
  c.d017 = some .noCombinedPerformance ∨
    ∃ exam main, c.d017 = some (.combined exam main) ∧
      ((show Performance Unit from { c.performance with item := () }).sameSpecimen exam = some false ∨
        ((show Performance Unit from { c.performance with item := () }).sameSpecimen exam = some true ∧ main.isSome = true))

def MethodSelectionKnown (method : Method) (c : Context) : Prop :=
  c.otherSedimentPerformed = some false ∨
    (c.otherSedimentPerformed = some true ∧ c.chosenSedimentMethod = some method)

def SimultaneousFlowComponents (c : Context) : Prop :=
  ∀ component, ∃ measurement ∈ c.flowMeasurements,
    measurement.item = component ∧
      Performance.simultaneousWith
        (show Performance FlowComponent from { c.performance with item := component }) measurement = some true

def InScope (method : Method) (c : Context) : Prop :=
  c.performance.item = method ∧ Indicated c ∧ D017SelectionKnown c ∧
    MethodSelectionKnown method c ∧
    match method with
    | .microscopy => MicroscopyLocation c ∧ c.stained.isSome = true
    | .flow => InHouse c ∧ SimultaneousFlowComponents c

private def primary (code loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF174頁 " ++ code ++ " " ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (code loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF333頁 " ++ code ++ loc, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def Method.code : Method → String
  | .microscopy => "D002"
  | .flow => "D002-2"

def Method.points : Method → Nat
  | .microscopy => 27
  | .flow => 24

/-- none は同一検体の主検査D017に譲る結果。 -/
abbrev Result := Option Charge

def headingRule (method : Method) : Rule Context Result :=
  ⟨"primary/" ++ method.code ++ "/heading", primary method.code "見出し", fun c r =>
    c.performance.item = method ∧ ∀ charge, r = some charge → charge.base = method.points⟩

def d017Rule (method : Method) : Rule Context Result :=
  ⟨"primary/" ++ method.code ++ "/note/1", primary method.code "注1", fun c r =>
    D017SelectionKnown c ∧ (r = none ↔ PreferD017 c)⟩

def locationRule (method : Method) : Rule Context Result :=
  ⟨"primary/" ++ method.code ++ "/note/2", primary method.code "注2", fun c _ =>
    InHouse c ∨ (method = .microscopy ∧ ConfirmedClinicException c)⟩

def stainPoints : Nat := 9

def stainRule : Rule Context Result :=
  ⟨"primary/D002/note/3", primary "D002" "注3", fun c r =>
    c.stained.isSome = true ∧ ∀ charge, r = some charge →
      (c.stained = some true → charge.stainedSpecimenAddition = stainPoints) ∧
      (c.stained = some false → charge.stainedSpecimenAddition = 0)⟩

/-- 無染色標本の追加算定額。 -/
def unstainedRule : Rule Context Nat :=
  ⟨"notice/D002/paragraph/1", notice "D002" "(1)", fun _ separate => separate = 0⟩

def indicationRule : Rule Context Result :=
  ⟨"notice/D002/paragraph/2", notice "D002" "(2)", fun c _ => Indicated c⟩

def contractRule : Rule Context Result :=
  ⟨"notice/D002/paragraph/3", notice "D002" "(3)", fun c _ =>
    InHouse c → c.location = some .directInHouse ∨ c.location = some (.contractedInHouse (some true))⟩

def clinicRule : Rule Context Result :=
  ⟨"notice/D002/paragraph/4", notice "D002" "(4)", fun c _ =>
    ¬ InHouse c → ConfirmedClinicException c⟩

def microscopySelectionRule : Rule Context Result :=
  ⟨"notice/D002/paragraph/5", notice "D002" "(5)", fun c _ => MethodSelectionKnown .microscopy c⟩

def flowMeasurementRule : Rule Context Result :=
  ⟨"notice/D002-2/paragraph/1", notice "D002-2" "(1)", fun c r =>
    Indicated c ∧ SimultaneousFlowComponents c ∧
      ∀ charge, r = some charge → charge.stainedSpecimenAddition = 0⟩

def flowSelectionRule : Rule Context Result :=
  ⟨"notice/D002-2/paragraph/2", notice "D002-2" "(2)", fun c _ => MethodSelectionKnown .flow c⟩

def microscopyRules :=
  [headingRule .microscopy, d017Rule .microscopy, locationRule .microscopy, stainRule,
    indicationRule, contractRule, clinicRule, microscopySelectionRule]

def flowRules :=
  [headingRule .flow, d017Rule .flow, locationRule .flow, flowMeasurementRule, flowSelectionRule]

/-- 尿沈渣に準用結果を返す経路はない。 -/
def resultRules (method : Method) : List (Rule Context Result) :=
  match method with
  | .microscopy => microscopyRules
  | .flow => flowRules

def legacyInput (method : Method) (c : Context) (prefer : Bool) : UrineFecalTests.Context :=
  { item := match method with
      | .microscopy => .urineSedimentMicroscopy
      | .flow => .urineSedimentFlowCytometry
    performedInsideInstitution := decideInHouse c
    microscopyClinicException := decideClinicException c
    sameSpecimenD017Performed := prefer
    mainTest := .d017BacterialMicroscopy
    stainedSpecimenExamined := c.stained == some true }
where
  decideInHouse (c : Context) : Bool :=
    match c.location with
    | some .directInHouse | some (.contractedInHouse _) => true
    | _ => false
  decideClinicException (c : Context) : Bool :=
    match c.location with
    | some (.contractedExternal (some true) (some true) (some true) (some true) (some elapsed)) =>
      decide (elapsed ≤ 4 * 60 * 60)
    | _ => false

def LegacyAssessment : Result → Assessment
  | none => .onlyMainD017
  | some charge => .charged charge

def LegacyResult (method : Method) (c : Context) (r : Result) : Prop :=
  ∃ prefer : Bool, (prefer = true ↔ PreferD017 c) ∧
    assess (legacyInput method c prefer) = some (LegacyAssessment r)

private theorem loc_iff (c : Context) : MicroscopyLocation c ↔
    (InHouse c ∨ ConfirmedClinicException c) ∧
    (InHouse c → c.location = some .directInHouse ∨ c.location = some (.contractedInHouse (some true))) ∧
    (¬ InHouse c → ConfirmedClinicException c) := by
  classical
  unfold MicroscopyLocation InHouse ConfirmedClinicException
  grind

private theorem input_house (c : Context) :
    legacyInput.decideInHouse c = true ↔ InHouse c := by
  unfold legacyInput.decideInHouse InHouse
  cases hc : c.location with
  | none => simp
  | some loc => cases loc <;> simp

private theorem input_exception (c : Context) :
    legacyInput.decideClinicException c = true ↔ ConfirmedClinicException c := by
  unfold legacyInput.decideClinicException ConfirmedClinicException
  cases hc : c.location with
  | none => simp
  | some loc =>
    cases loc with
    | directInHouse => simp
    | contractedInHouse => simp
    | contractedExternal clinic suspicion lab report elapsed =>
      cases clinic <;> cases suspicion <;> cases lab <;> cases report <;> cases elapsed <;>
        simp_all <;> split <;> simp_all

private theorem legacy_assess (method : Method) (c : Context) (prefer : Bool)
    (scope : InScope method c) :
    assess (legacyInput method c prefer) =
      if prefer then some .onlyMainD017 else
        some (.charged ⟨method.points, if method = .microscopy ∧ c.stained = some true then 9 else 0⟩) := by
  cases method with
  | microscopy =>
    have loc := (loc_iff c).mp scope.2.2.2.2.1
    rcases loc.1 with house | exception
    · simp [legacyInput, assess, pointRule, requiresInHouse, isSediment, Method.points, (input_house c).mpr house]
    · simp [legacyInput, assess, pointRule, requiresInHouse, isSediment, Method.points, (input_exception c).mpr exception]
  | flow =>
    simp [legacyInput, assess, pointRule, requiresInHouse, isSediment, Method.points, (input_house c).mpr scope.2.2.2.2.1]

private theorem scope_of_satisfies (method : Method) (c : Context) (r : Result)
    (h : Satisfies (resultRules method) c r) : InScope method c := by
  cases method
  · have location := h (locationRule .microscopy) (by simp [resultRules, microscopyRules])
    exact ⟨(h (headingRule .microscopy) (by simp [resultRules, microscopyRules])).1,
      h indicationRule (by simp [resultRules, microscopyRules]),
      (h (d017Rule .microscopy) (by simp [resultRules, microscopyRules])).1,
      h microscopySelectionRule (by simp [resultRules, microscopyRules]),
      (loc_iff c).mpr ⟨by simpa [locationRule] using location,
        h contractRule (by simp [resultRules, microscopyRules]),
        h clinicRule (by simp [resultRules, microscopyRules])⟩,
      (h stainRule (by simp [resultRules, microscopyRules])).1⟩
  · have measurement := h flowMeasurementRule (by simp [resultRules, flowRules])
    have location := h (locationRule .flow) (by simp [resultRules, flowRules])
    exact ⟨(h (headingRule .flow) (by simp [resultRules, flowRules])).1, measurement.1,
      (h (d017Rule .flow) (by simp [resultRules, flowRules])).1,
      h flowSelectionRule (by simp [resultRules, flowRules]),
      by simpa [locationRule] using location,
      measurement.2.1⟩

private theorem satisfies_in_scope (method : Method) (c : Context) (r : Result)
    (scope : InScope method c) : Satisfies (resultRules method) c r ↔
      ((r = none ↔ PreferD017 c) ∧ ∀ charge, r = some charge →
        charge.base = method.points ∧
        charge.stainedSpecimenAddition = (if method = .microscopy ∧ c.stained = some true then 9 else 0)) := by
  rcases scope with ⟨item, indication, known, selected, scope⟩
  cases method with
  | microscopy =>
    have location := (loc_iff c).mp scope.1
    cases hs : c.stained with
    | none => simp [hs] at scope
    | some stain =>
      cases stain <;> simp [Satisfies, resultRules, microscopyRules, headingRule, d017Rule,
        locationRule, stainRule, indicationRule, contractRule, clinicRule, microscopySelectionRule,
        item, indication, known, selected, location.1, hs, stainPoints, or_imp,
        forall_and] <;> grind
  | flow =>
    simp [Satisfies, resultRules, flowRules, headingRule, d017Rule, locationRule,
      flowMeasurementRule, flowSelectionRule, item, indication, known, selected,
      scope.1, scope.2, or_imp, forall_and] <;> grind

theorem satisfies_iff (method : Method) (c : Context) (r : Result) :
    Satisfies (resultRules method) c r ↔ InScope method c ∧ LegacyResult method c r := by
  classical
  have equivalent (scope : InScope method c) :
      Satisfies (resultRules method) c r ↔ LegacyResult method c r := by
    rw [satisfies_in_scope method c r scope]
    unfold LegacyResult
    by_cases h : PreferD017 c <;> cases r <;> simp [h, LegacyAssessment, legacy_assess, scope]
    rename_i charge
    cases charge
    simp [eq_comm (a := method.points), and_comm]
    grind
  exact ⟨fun h => ⟨scope_of_satisfies method c r h, (equivalent (scope_of_satisfies method c r h)).mp h⟩,
    fun ⟨scope, h⟩ => (equivalent scope).mpr h⟩

theorem determines (method : Method) : DeterminesOn (InScope method) (resultRules method) := by
  classical
  intro c scope
  let prefer := decide (PreferD017 c)
  let charge := (⟨method.points, if method = .microscopy ∧ c.stained = some true then 9 else 0⟩ : Charge)
  let r := if prefer then none else some charge
  refine ⟨⟨r, (satisfies_iff ..).mpr ⟨scope, prefer, by simp [prefer], ?_⟩⟩, ?_⟩
  · rw [legacy_assess method c prefer scope]
    simp only [r]
    split <;> simp_all [LegacyAssessment, charge]
  · intro a b ha hb
    have ⟨pa, hpa, ea⟩ := ((satisfies_iff method c a).mp ha).2
    have ⟨pb, hpb, eb⟩ := ((satisfies_iff method c b).mp hb).2
    have eq : pa = pb := by cases pa <;> cases pb <;> simp_all
    rw [eq] at ea
    have same := ea.symm.trans eb
    cases a <;> cases b <;> simp_all [LegacyAssessment]

def judgmentTest (method : Method) : SpecimenJudgment.Test :=
  { major := 2, suffix := if method = .microscopy then 0 else 2, ordinaryCategory := .urineFecal }

def toSpecimenItem (r : Result) (kind : Nat) : Option Examinations.SpecimenItem :=
  (LegacyAssessment r).toSpecimenItem kind

/-- D017の依頼と実施記録の対応は呼出側で確認する。同じ選択を双方へ渡す。 -/
def D017Pair (c : Context) (request : SpecimenTests.Request) (result : Result)
    (bacterial : SpecimenTests.ItemResult) : Prop :=
  Satisfies (resultRules c.performance.item) c result ∧
    ∃ exam main, c.d017 = some (.combined exam (some main)) ∧
      (show Performance Unit from { c.performance with item := () }).sameSpecimen exam = some true ∧
      SpecimenTests.assessSedimentPair (legacyInput c.performance.item c false) request main =
        some (LegacyAssessment result, bacterial)

private def sample : Context :=
  { performance := ⟨1, ⟨2, 3, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩,
      .microscopy, none, some 1, none, none⟩
    indication := some .medicallyNecessaryOnExamination
    location := some (.contractedExternal (some true) (some true) (some true) (some true) (some 14400))
    d017 := some .noCombinedPerformance
    otherSedimentPerformed := some false
    chosenSedimentMethod := none
    stained := some true }

example : Satisfies microscopyRules sample (some ⟨27, 9⟩) := by
  apply (satisfies_iff .microscopy ..).mpr
  exact ⟨⟨rfl, trivial, Or.inl rfl, Or.inl rfl, Or.inr (Or.inr ⟨14400, rfl, by decide⟩), rfl⟩,
    false, by simp [PreferD017, sample], rfl⟩

example : ¬ SatisfiableAt microscopyRules
    { sample with location := some (.contractedExternal (some true) (some true) (some true)
      (some true) (some 14401)) } := by
  rintro ⟨r, hr⟩
  have scope := ((satisfies_iff .microscopy _ r).mp hr).1
  have loc := scope.2.2.2.2.1
  simp [MicroscopyLocation, ConfirmedClinicException] at loc

private def flowSample : Context :=
  { sample with
    performance := { sample.performance with item := .flow, simultaneous := some 2 }
    location := some .directInHouse
    flowMeasurements :=
      [FlowComponent.redCells, .whiteCells, .epithelialCells, .casts, .bacteria].map
        (fun component => { sample.performance with item := component, simultaneous := some 2 }) }

example : Satisfies flowRules flowSample (some ⟨24, 0⟩) := by
  apply (satisfies_iff .flow ..).mpr
  refine ⟨⟨rfl, trivial, Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩,
    false, by simp [PreferD017, flowSample, sample], rfl⟩
  intro component
  refine ⟨{ sample.performance with item := component, simultaneous := some 2 }, ?_, rfl, rfl⟩
  cases component <;> simp [flowSample]

example : ¬ SatisfiableAt flowRules { flowSample with flowMeasurements := [] } := by
  rintro ⟨r, hr⟩
  have h := (((satisfies_iff .flow _ r).mp hr).1.2.2.2.2).2 .bacteria
  obtain ⟨_, member, _⟩ := h
  simp at member

end Sanri.MedicalFee.UrineSediment
