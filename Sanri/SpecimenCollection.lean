import Sanri.Examinations

namespace Sanri.MedicalFee.SpecimenCollection

/-! 第４節通則１・２、Ｄ４００〜Ｄ４１９－２。
片側・臓器・日次・一連の実施と履歴は同一患者について呼出元が管理する。
第３節の率による年齢加算は使わず、この節の各注の固定点数を用いる。 -/

inductive Item where
  | venousBlood | otherBlood | ventricularPuncture | suboccipitalPuncture
  | lumbarPuncture | thoracicPuncture | cervicalPuncture
  | sternalMarrowPuncture | otherMarrowPuncture | marrowBiopsy
  | jointPuncture | maxillarySinusPuncture | peritonsillarTrialPuncture | renalCystHydronephrosisPuncture
  | douglasPuncture | lymphNodeNeedleBiopsy | sentinelCombined | sentinelSingle
  | breastBiopsyNeedle | breastOther | thyroidNeedleBiopsy | percutaneousNeedleBiopsy
  | percutaneousRenalBiopsy | transjugularLiverBiopsy | prostateMriUltrasoundFusion | prostateOther
  | endoscopicBiopsy | eusFna | transbronchialLungBiopsy | ebusTbna | navigatedLungBiopsy
  | virtualBronchoscopyBiopsy | transbronchialCryobiopsy | parietalPleuralCryobiopsy
  | thoracotomyTissue | laparotomyTissue
  | skinTissue | muscleTissue | bonePelvisSpineTissue | posteriorEyeTissue | otherEyeTissue
  | earTissue | nasalSinusTissue | oralTissue | pharyngolaryngealTissue | thyroidTissue
  | breastTissue | rectalTissue | testisEpididymisTissue | peripheralNerveTissue | myocardiumTissue
  | cervicalMucus | vaginalCervicalTissue | endometrialTissue
  | gastricDuodenalFluid | pleuralAsciticFluid | arterialBlood | anteriorChamberFluid
  | adrenalVenousSampling | nasalPharyngealSwab | intraocularFluidExamination
  deriving DecidableEq, Repr

def basePoints : Item → Nat
  | .venousBlood => 40
  | .otherBlood => 6
  | .ventricularPuncture => 600
  | .suboccipitalPuncture => 300
  | .lumbarPuncture | .thoracicPuncture | .cervicalPuncture => 312
  | .sternalMarrowPuncture => 260
  | .otherMarrowPuncture => 300
  | .marrowBiopsy => 730
  | .jointPuncture => 100
  | .maxillarySinusPuncture => 60
  | .peritonsillarTrialPuncture => 180
  | .renalCystHydronephrosisPuncture | .douglasPuncture | .lymphNodeNeedleBiopsy => 240
  | .sentinelCombined => 5000
  | .sentinelSingle => 3000
  | .breastBiopsyNeedle => 690
  | .breastOther => 200
  | .thyroidNeedleBiopsy => 150
  | .percutaneousNeedleBiopsy => 1920
  | .percutaneousRenalBiopsy => 2400
  | .transjugularLiverBiopsy => 13000
  | .prostateMriUltrasoundFusion => 8210
  | .prostateOther => 1848
  | .endoscopicBiopsy => 310
  | .eusFna => 5760
  | .transbronchialLungBiopsy => 4800
  | .ebusTbna | .navigatedLungBiopsy | .transbronchialCryobiopsy => 5500
  | .virtualBronchoscopyBiopsy => 5000
  | .parietalPleuralCryobiopsy => 15800
  | .thoracotomyTissue => 9070
  | .laparotomyTissue => 5550
  | .skinTissue => 500
  | .muscleTissue => 1500
  | .bonePelvisSpineTissue => 4600
  | .posteriorEyeTissue | .pharyngolaryngealTissue | .thyroidTissue | .breastTissue => 650
  | .otherEyeTissue => 350
  | .earTissue | .nasalSinusTissue | .oralTissue | .testisEpididymisTissue => 400
  | .rectalTissue => 780
  | .peripheralNerveTissue => 1620
  | .myocardiumTissue => 6000
  | .cervicalMucus => 40
  | .vaginalCervicalTissue => 200
  | .endometrialTissue => 370
  | .gastricDuodenalFluid => 210
  | .pleuralAsciticFluid => 220
  | .arterialBlood => 60
  | .anteriorChamberFluid => 504
  | .adrenalVenousSampling => 4800
  | .nasalPharyngealSwab => 25
  | .intraocularFluidExamination => 1000

def isD400 (i : Item) : Bool := decide (i = .venousBlood ∨ i = .otherBlood)
def isDaily (i : Item) : Bool := isD400 i || decide (i = .arterialBlood)
def isSeries (i : Item) : Bool := decide (i = .gastricDuodenalFluid ∨ i = .adrenalVenousSampling)
def isUnilateral (i : Item) : Bool := decide (i ∈
  [.jointPuncture, .maxillarySinusPuncture, .peritonsillarTrialPuncture,
   .sentinelCombined, .sentinelSingle, .breastBiopsyNeedle, .breastOther])
def isD417 (i : Item) : Bool := decide (i ∈
  [.skinTissue, .muscleTissue, .bonePelvisSpineTissue, .posteriorEyeTissue, .otherEyeTissue,
   .earTissue, .nasalSinusTissue, .oralTissue, .pharyngolaryngealTissue, .thyroidTissue,
   .breastTissue, .rectalTissue, .testisEpididymisTissue, .peripheralNerveTissue, .myocardiumTissue])

def infantPoints (i : Item) (ageYears : Nat) : Nat :=
  if i = .jointPuncture then if ageYears < 3 then 100 else 0
  else if ageYears ≥ 6 then 0
  else if isD400 i || decide (i = .arterialBlood) then 35
  else if isD417 i || decide (i ∈ [.ventricularPuncture, .suboccipitalPuncture,
      .lumbarPuncture, .thoracicPuncture, .cervicalPuncture, .sternalMarrowPuncture,
      .otherMarrowPuncture, .marrowBiopsy, .renalCystHydronephrosisPuncture]) then 100
  else match i with
    | .thoracotomyTissue | .laparotomyTissue => 2000
    | .pleuralAsciticFluid => 60
    | .anteriorChamberFluid => 90
    | .adrenalVenousSampling => 1000
    | _ => 0

inductive Sides where
  | one | both
  deriving DecidableEq, Repr

structure Context where
  item : Item
  insuranceMedicalInstitution : Bool := true
  performed : Bool := true
  ageYears : Nat := 20
  inpatient : Bool := false
  duringSurgery : Bool := false
  /-- 処置の部にもある共通項目で、同一日にその処置を算定するか。 -/
  commonProcedureClaimedSameDay : Bool := false
  dailyAlreadyClaimed : Bool := false
  seriesAlreadyClaimed : Bool := false
  seriesId : Nat := 0
  bloodCircuitSampling : Bool := false
  sides : Sides := .one
  /-- Ｄ４１４の実際に採取した臓器の識別子。同じ臓器を重複して数えない。 -/
  organs : List Nat := [0]
  facilityStandardNotified : Bool := false
  breastCancerPatient : Bool := false
  radioisotopeUsed : Bool := false
  dyeUsed : Bool := false
  designatedProstatePatient : Bool := false
  guideSheathUltrasoundPerformed : Bool := false
  ctFluoroscopicBronchoscopy : Bool := false
  ctFluoroscopyStandardNotified : Bool := false
  probeConfocalEndomicroscopy : Bool := false
  /-- Ｄ４１９の５：Ｅ４００の規定で解決した、使用フィルムの点数。 -/
  filmPoints : Nat := 0
  deriving DecidableEq, Repr

inductive NotSeparateReason where
  | duringSurgery | commonProcedureSameDay | inpatientBloodCollection | bloodCircuit
  | dailyAlreadyClaimed | seriesAlreadyClaimed
  deriving DecidableEq, Repr

def notSeparateReason (c : Context) : Option NotSeparateReason :=
  if c.duringSurgery then some .duringSurgery
  else if c.commonProcedureClaimedSameDay then some .commonProcedureSameDay
  else if isD400 c.item && c.inpatient then some .inpatientBloodCollection
  else if (isD400 c.item || decide (c.item = .arterialBlood)) && c.bloodCircuitSampling then some .bloodCircuit
  else if isDaily c.item && c.dailyAlreadyClaimed then some .dailyAlreadyClaimed
  else if isSeries c.item && c.seriesAlreadyClaimed then some .seriesAlreadyClaimed
  else none

def eligible (c : Context) : Bool :=
  c.insuranceMedicalInstitution && c.performed &&
  (decide (c.item ∉ [.transjugularLiverBiopsy, .transbronchialCryobiopsy, .parietalPleuralCryobiopsy]) ||
    c.facilityStandardNotified) &&
  (decide (c.item ≠ .prostateMriUltrasoundFusion) || (c.facilityStandardNotified && c.designatedProstatePatient)) &&
  (decide (c.item ≠ .sentinelCombined) ||
    (c.facilityStandardNotified && c.breastCancerPatient && c.radioisotopeUsed && c.dyeUsed)) &&
  (decide (c.item ≠ .sentinelSingle) ||
    (c.facilityStandardNotified && c.breastCancerPatient &&
      ((c.radioisotopeUsed && !c.dyeUsed) || (!c.radioisotopeUsed && c.dyeUsed)))) &&
  (decide (c.item ≠ .endoscopicBiopsy) || !c.organs.isEmpty) &&
  (decide (c.item ≠ .transbronchialLungBiopsy) ||
    !c.ctFluoroscopicBronchoscopy || c.ctFluoroscopyStandardNotified)

structure Assessment where
  notSeparate : Option NotSeparateReason
  units : Nat := 0
  base : Nat := 0
  infant : Nat := 0
  guideSheath : Nat := 0
  ctFluoroscopy : Nat := 0
  endomicroscopy : Nat := 0
  film : Nat := 0
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Nat :=
  a.base + a.infant + a.guideSheath + a.ctFluoroscopy + a.endomicroscopy + a.film

def assess (c : Context) : Option Assessment :=
  if !c.insuranceMedicalInstitution || !c.performed then none else
    match notSeparateReason c with
    | some reason => some { notSeparate := some reason }
    | none =>
      if !eligible c then none else
        let units := if c.item = .endoscopicBiopsy then c.organs.eraseDups.length
          else if isUnilateral c.item && decide (c.sides = .both) then 2 else 1
        let isD415 := decide (c.item = .transbronchialLungBiopsy)
        let micro := isD415 && c.probeConfocalEndomicroscopy
        some {
          notSeparate := none
          units := units
          base := units * basePoints c.item
          infant := units * infantPoints c.item c.ageYears
          guideSheath := if c.guideSheathUltrasoundPerformed &&
            ((isD415 && !micro) || decide (c.item = .virtualBronchoscopyBiopsy)) then 500 else 0
          ctFluoroscopy := if isD415 && c.ctFluoroscopicBronchoscopy then 1000 else 0
          endomicroscopy := if micro then 1500 else 0
          film := if c.item = .adrenalVenousSampling then c.filmPoints else 0 }

def points (c : Context) : Option Nat := (assess c).map Assessment.total

def mixedD400 (contexts : List Context) : Bool :=
  (contexts.any fun c => c.item == .venousBlood) &&
    (contexts.any fun c => c.item == .otherBlood)

def sameLimitedFrame (a b : Context) : Bool :=
  a.item == b.item && (isDaily a.item || (isSeries a.item && a.seriesId == b.seriesId))

private def conflictingCharge (a b : Context) : Bool :=
  sameLimitedFrame a b &&
    match assess a, assess b with
    | some x, some y => x.notSeparate.isNone && y.notSeparate.isNone && x != y
    | _, _ => false

def conflictingLimitedCharges (contexts : List Context) : Bool :=
  contexts.any fun a => contexts.any (conflictingCharge a)

private def dayStep (state : List Context × List Assessment) (original : Context) :
    Option (List Context × List Assessment) := do
  let c := { original with
    dailyAlreadyClaimed := original.dailyAlreadyClaimed || state.1.any (fun x =>
      decide (x.item = original.item))
    seriesAlreadyClaimed := original.seriesAlreadyClaimed || state.1.any (fun x =>
      decide (x.item = original.item ∧ x.seriesId = original.seriesId)) }
  let a ← assess c
  let charged := if a.notSeparate.isNone then state.1 ++ [c] else state.1
  some (charged, state.2 ++ [a])

/-- 同一日・同一患者の一覧。異方式のＤ４００を含む日の本体点数は保留する。 -/
def assessDay (contexts : List Context) : Option (List Assessment) := do
  if mixedD400 contexts then none else
    if conflictingLimitedCharges contexts then none else
      let result ← contexts.foldlM dayStep ([], [])
      some result.2

theorem mixedD400_perm {xs ys : List Context} (h : xs.Perm ys) :
    mixedD400 xs = mixedD400 ys := by
  unfold mixedD400
  rw [h.any_eq, h.any_eq]

theorem assessDay_mixed_perm {xs ys : List Context} (h : xs.Perm ys)
    (mixed : mixedD400 xs = true) : assessDay xs = none ∧ assessDay ys = none := by
  have mixed' : mixedD400 ys = true := (mixedD400_perm h).symm.trans mixed
  simp [assessDay, mixed, mixed']

private theorem conflictingLimitedCharges_perm {xs ys : List Context} (h : xs.Perm ys) :
    conflictingLimitedCharges xs = conflictingLimitedCharges ys := by
  unfold conflictingLimitedCharges
  have inner (a : Context) := h.any_eq (f := conflictingCharge a)
  simp only [inner]
  exact h.any_eq


theorem assessDay_conflicting_perm {xs ys : List Context} (h : xs.Perm ys)
    (conflict : conflictingLimitedCharges xs = true) :
    assessDay xs = none ∧ assessDay ys = none := by
  have conflict' : conflictingLimitedCharges ys = true :=
    (conflictingLimitedCharges_perm h).symm.trans conflict
  simp [assessDay, conflict, conflict']

/-- 前の実施が日次・一連の枠を共有しない場合、単独評価と等しい。 -/
private theorem assess_with_unrelated_charges (charged : List Context) (original : Context)
    (separate : ∀ x ∈ charged, sameLimitedFrame x original = false) :
    assess { original with
      dailyAlreadyClaimed := original.dailyAlreadyClaimed || charged.any (fun x =>
        decide (x.item = original.item))
      seriesAlreadyClaimed := original.seriesAlreadyClaimed || charged.any (fun x =>
        decide (x.item = original.item ∧ x.seriesId = original.seriesId)) } = assess original := by
  have daily : isDaily original.item = true →
      charged.any (fun x => decide (x.item = original.item)) = false := by
    intro hd
    apply List.any_eq_false.mpr
    intro x hx same
    have eq := of_decide_eq_true same
    simpa [sameLimitedFrame, eq, hd] using separate x hx
  have series : isSeries original.item = true →
      charged.any (fun x => decide (x.item = original.item ∧ x.seriesId = original.seriesId)) = false := by
    intro hs
    apply List.any_eq_false.mpr
    intro x hx same
    obtain ⟨item, id⟩ := of_decide_eq_true same
    simpa [sameLimitedFrame, item, id, hs] using separate x hx
  cases hd : isDaily original.item <;> cases hs : isSeries original.item
  all_goals try rw [daily hd]
  all_goals try rw [series hs]
  all_goals simp [assess, notSeparateReason, eligible, hd, hs]

private theorem sameLimitedFrame_flags (x a : Context) (daily series : Bool) :
    sameLimitedFrame { x with dailyAlreadyClaimed := daily, seriesAlreadyClaimed := series } a =
      sameLimitedFrame x a := rfl

private theorem fold_distinct_frames (remaining : List Context) (charged : List Context)
    (entries : List Assessment)
    (separate : remaining.Pairwise (fun a b => sameLimitedFrame a b = false))
    (prior : ∀ a ∈ charged, ∀ b ∈ remaining, sameLimitedFrame a b = false) :
    (remaining.foldlM dayStep (charged, entries)).map Prod.snd =
      (remaining.mapM assess).map (entries ++ ·) := by
  induction remaining generalizing charged entries with
  | nil => simp
  | cons a rest ih =>
    rw [List.pairwise_cons] at separate
    have unmodified := assess_with_unrelated_charges charged a
      (fun x hx => prior x hx a (by simp))
    rw [List.foldlM_cons, List.mapM_cons]
    let updated := { a with
      dailyAlreadyClaimed := a.dailyAlreadyClaimed || charged.any (fun x => decide (x.item = a.item))
      seriesAlreadyClaimed := a.seriesAlreadyClaimed || charged.any (fun x =>
        decide (x.item = a.item ∧ x.seriesId = a.seriesId)) }
    have step : dayStep (charged, entries) a = (assess a).map
        (fun assessment => (if assessment.notSeparate.isNone then charged ++ [updated] else charged,
          entries ++ [assessment])) := by
      change (assess updated).bind _ = _
      have hu : assess updated = assess a := unmodified
      rw [hu]
      cases assess a <;> rfl
    rw [step]
    cases price : assess a with
    | none => rfl
    | some assessment =>
      by_cases chargedNow : assessment.notSeparate.isNone = true
      · simp only [Option.map_some, chargedNow, ite_true, bind, Option.bind]
        rw [ih _ _ separate.2]
        · cases rest.mapM assess <;> simp [List.append_assoc]
        · intro x hx y hy
          rcases List.mem_append.mp hx with hx | hx
          · exact prior x hx y (by simp [hy])
          · obtain rfl := List.mem_singleton.mp hx
            exact separate.1 y hy
      · simp only [Option.map_some, chargedNow, Bool.false_eq_true, ite_false, bind, Option.bind]
        rw [ih _ _ separate.2 (fun x hx y hy => prior x hx y (by simp [hy]))]
        cases rest.mapM assess <;> simp [List.append_assoc]

private theorem mapM_assess_perm {xs ys : List Context} {assessments : List Assessment}
    (h : xs.Perm ys) (ok : xs.mapM assess = some assessments) :
    ∃ other, ys.mapM assess = some other ∧ assessments.Perm other := by
  induction h generalizing assessments with
  | nil => exact ⟨assessments, ok, .refl _⟩
  | @cons x left right _ ih =>
    cases hx : assess x with
    | none => simp [List.mapM_cons, hx] at ok
    | some a =>
      cases ht : left.mapM assess with
      | none => simp [List.mapM_cons, hx, ht] at ok
      | some tail =>
        have eq : a :: tail = assessments := by
          simpa [List.mapM_cons, hx, ht] using ok
        subst assessments
        obtain ⟨other, out, perm⟩ := ih ht
        exact ⟨a :: other, by simp [List.mapM_cons, hx, out], perm.cons a⟩
  | swap x y tail =>
    cases hx : assess x <;> cases hy : assess y <;> cases ht : tail.mapM assess <;>
      simp_all [List.mapM_cons]
    rw [← ok]
    exact .swap ..
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨mid, eq, hmid⟩ := ih₁ ok
    obtain ⟨out, eq', hout⟩ := ih₂ eq
    exact ⟨out, eq', hmid.trans hout⟩

/-- 異方式D400の保留判定を維持し、日次・一連の枠を共有しない採取の内訳を並べ替えられる。 -/
theorem assessDay_perm_of_distinct_frames {xs ys : List Context} {assessments : List Assessment}
    (h : xs.Perm ys)
    (separate : xs.Pairwise (fun a b => sameLimitedFrame a b = false))
    (ok : assessDay xs = some assessments) :
    ∃ other, assessDay ys = some other ∧ assessments.Perm other := by
  have symmetric : ∀ {a b : Context}, sameLimitedFrame a b = false → sameLimitedFrame b a = false := by
    intro a b neq
    by_cases item : a.item = b.item
    · by_cases series : a.seriesId = b.seriesId <;>
        simpa [sameLimitedFrame, item, series, Ne.symm] using neq
    · simp [sameLimitedFrame, Ne.symm item]
  have sepY := (h.pairwise_iff symmetric).mp separate
  have mixed : mixedD400 xs = false := by
    cases eh : mixedD400 xs <;> simp_all [assessDay]
  have conflict : conflictingLimitedCharges xs = false := by
    cases eh : conflictingLimitedCharges xs <;> simp_all [assessDay]
  have evaluation (rows : List Context) (distinct : rows.Pairwise (fun a b => sameLimitedFrame a b = false))
      (m : mixedD400 rows = false) (c : conflictingLimitedCharges rows = false) :
      assessDay rows = rows.mapM assess := by
    have fold := fold_distinct_frames rows [] [] distinct (by simp)
    cases hf : rows.foldlM dayStep ([], []) <;> cases hm : rows.mapM assess <;>
      simp_all [assessDay]
  rw [evaluation xs separate mixed conflict] at ok
  rw [evaluation ys sepY ((mixedD400_perm h).symm.trans mixed)
    ((conflictingLimitedCharges_perm h).symm.trans conflict)]
  exact mapM_assess_perm h ok

private def repeatAssessment (c : Context) : Assessment :=
  { notSeparate := some (if isDaily c.item then .dailyAlreadyClaimed else .seriesAlreadyClaimed) }

private theorem assess_already_charged (a b : Context) (result : Assessment)
    (frame : sameLimitedFrame a b = true)
    (solo : assess b = some result) (billable : result.notSeparate = none) :
    assess { b with
      dailyAlreadyClaimed := b.dailyAlreadyClaimed || decide (a.item = b.item)
      seriesAlreadyClaimed := b.seriesAlreadyClaimed ||
        decide (a.item = b.item ∧ a.seriesId = b.seriesId) } = some (repeatAssessment b) := by
  have performed : (!b.insuranceMedicalInstitution || !b.performed) = false := by
    cases h : (!b.insuranceMedicalInstitution || !b.performed) <;> simp_all [assess]
  have reason : notSeparateReason b = none := by
    cases h : notSeparateReason b <;> simp_all [assess] <;> subst result <;> simp_all
  have item : a.item = b.item := by
    by_cases eq : a.item = b.item
    · exact eq
    · simp [sameLimitedFrame, eq] at frame
  have surgery : b.duringSurgery = false := by
    cases h : b.duringSurgery <;> simp_all [notSeparateReason]
  have procedure : b.commonProcedureClaimedSameDay = false := by
    cases h : b.commonProcedureClaimedSameDay <;> simp_all [notSeparateReason]
  have inpatient : (isD400 b.item && b.inpatient) = false := by
    cases h : (isD400 b.item && b.inpatient) <;> simp_all [notSeparateReason]
  have circuit : ((isD400 b.item || decide (b.item = .arterialBlood)) && b.bloodCircuitSampling) =
      false := by
    cases h : ((isD400 b.item || decide (b.item = .arterialBlood)) && b.bloodCircuitSampling) <;>
      simp_all [notSeparateReason]
  by_cases daily : isDaily b.item = true
  · simp [assess, notSeparateReason, repeatAssessment, performed, surgery, procedure,
      inpatient, circuit, item, daily]
  · have series : isSeries b.item = true ∧ a.seriesId = b.seriesId := by
      simpa [sameLimitedFrame, item, daily] using frame
    simp [assess, notSeparateReason, repeatAssessment, performed, surgery, procedure,
      inpatient, circuit, item, daily, series.1, series.2]

private theorem repeat_tail (anchor : Context) (rest : List Context) (entries : List Assessment)
    (result : Assessment) (billable : result.notSeparate = none)
    (matching : ∀ b ∈ rest, sameLimitedFrame anchor b = true ∧ assess b = some result) :
    rest.foldlM dayStep ([anchor], entries) =
      some ([anchor], entries ++ rest.map repeatAssessment) := by
  induction rest generalizing entries with
  | nil => simp
  | cons b rest ih =>
    have hb := matching b (by simp)
    have h := assess_already_charged anchor b result hb.1 hb.2 billable
    have step : dayStep ([anchor], entries) b = some ([anchor], entries ++ [repeatAssessment b]) := by
      unfold dayStep
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [h]
      simp [repeatAssessment]
    rw [List.foldlM_cons, step]
    change rest.foldlM dayStep ([anchor], entries ++ [repeatAssessment b]) = _
    rw [ih _ (fun c hc => matching c (by simp [hc]))]
    simp [List.append_assoc]

private theorem repeat_result {rows : List Context} (result : Assessment)
    (mixed : mixedD400 rows = false) (conflicts : conflictingLimitedCharges rows = false)
    (solo : ∀ b ∈ rows, assess b = some result) (billable : result.notSeparate = none)
    (frame : ∀ a ∈ rows, ∀ b ∈ rows, sameLimitedFrame a b = true) :
    assessDay rows =
      some (if rows.isEmpty then [] else result :: (rows.drop 1).map repeatAssessment) := by
  cases rows with
  | nil => rfl
  | cons a rest =>
    have ha := solo a (by simp)
    have step : dayStep ([], []) a = some ([a], [result]) := by
      unfold dayStep
      simp [ha, billable]
    unfold assessDay
    simp only [mixed, conflicts, Bool.false_eq_true, ↓reduceIte, List.foldlM_cons, step]
    simp only [bind, Option.bind]
    change (do let out ← rest.foldlM dayStep ([a], [result]); some out.2) = _
    rw [repeat_tail a rest [result] result billable
      (fun b hb => ⟨frame a (by simp) b (by simp [hb]), solo b (by simp [hb])⟩)]
    rfl

/-- 日次又は一連の同一枠だけを反復し、同じ単独の別算定内訳が確認できた場合。
最初の一件がその内訳となり、残りの全件は同じ日次又は一連の理由で包括される。 -/
theorem assessDay_perm_of_repeated_frame {xs ys : List Context} {assessments : List Assessment}
    (perm : xs.Perm ys) (ok : assessDay xs = some assessments)
    (solo : ∃ result, result.notSeparate = none ∧ ∀ b ∈ xs, assess b = some result)
    (frame : ∀ a ∈ xs, ∀ b ∈ xs, sameLimitedFrame a b = true) :
    assessDay ys = some assessments := by
  obtain ⟨result, billable, solo⟩ := solo
  have mixed : mixedD400 xs = false := by
    cases eh : mixedD400 xs <;> simp_all [assessDay]
  have conflict : conflictingLimitedCharges xs = false := by
    cases eh : conflictingLimitedCharges xs <;> simp_all [assessDay]
  rw [repeat_result result mixed conflict solo billable frame] at ok
  rw [repeat_result result ((mixedD400_perm perm).symm.trans mixed)
    ((conflictingLimitedCharges_perm perm).symm.trans conflict)
    (fun b hb => solo b (perm.mem_iff.mpr hb)) billable
    (fun a ha b hb => frame a (perm.mem_iff.mpr ha) b (perm.mem_iff.mpr hb))]
  cases xs with
  | nil => have eq := List.perm_nil.mp perm.symm; subst ys; exact ok
  | cons a left =>
    cases ys with
    | nil => simp at perm
    | cons b right =>
      have hitem : ∀ c ∈ a :: left, c.item = a.item := by
        intro c hc
        have hf := frame a (by simp) c hc
        by_cases h : c.item = a.item
        · exact h
        · simp [sameLimitedFrame, Ne.symm h] at hf
      have output (c : Context) (hc : c ∈ a :: left) : repeatAssessment c = repeatAssessment a := by
        simp [repeatAssessment, hitem c hc]
      have mappedLeft : left.map repeatAssessment = List.replicate left.length (repeatAssessment a) :=
        List.map_eq_replicate_iff.mpr (fun c hc => output c (by simp [hc]))
      have mappedRight : right.map repeatAssessment = List.replicate right.length (repeatAssessment a) :=
        List.map_eq_replicate_iff.mpr (fun c hc => output c (perm.mem_iff.mpr (by simp [hc])))
      have length : left.length = right.length := by simpa using perm.length_eq
      simpa [mappedLeft, mappedRight, length] using ok

/-- 検査通則の第４節に引き渡す。別算定しない採取を種類数に含めない。
Ｅ４００のフィルムは第４節の置換対象に混ぜず、呼出元で別に合算する。 -/
def Assessment.toCollection (a : Assessment) (kind : Nat) : Option Examinations.TestCharge :=
  if a.notSeparate.isSome then none else some { kind := kind, scheduledPoints := a.total - a.film }

inductive IncludedService where
  | cerebrospinalPressure | fluoroscopy | ecg | ultrasound | simpleFluidTest
  | contrastInjection | contrastImaging | xrayDiagnosis | sentinelDye
  deriving DecidableEq, Repr

/-- 包括範囲。false だけでは当該費用の別算定可否を決定しない。 -/
def serviceIncluded (c : Context) (s : IncludedService) : Bool :=
  match s with
  | .cerebrospinalPressure => decide (c.item ∈ [.lumbarPuncture, .thoracicPuncture, .cervicalPuncture])
  | .fluoroscopy => decide (c.item = .percutaneousNeedleBiopsy ∨ c.item = .adrenalVenousSampling)
  | .ecg | .ultrasound => decide (c.item = .percutaneousNeedleBiopsy)
  | .simpleFluidTest => decide (c.item = .pleuralAsciticFluid)
  | .contrastInjection | .contrastImaging | .xrayDiagnosis => decide (c.item = .adrenalVenousSampling)
  | .sentinelDye => decide (c.item = .sentinelCombined ∨ c.item = .sentinelSingle)

private def req (item : Item) : Context := { item := item }
example : points (req .venousBlood) = some 40 := by decide
example : points { req .venousBlood with ageYears := 5 } = some 75 := by decide
example : points { req .venousBlood with ageYears := 6 } = some 40 := by decide
example : points { req .otherBlood with ageYears := 5 } = some 41 := by decide
example : points { req .venousBlood with inpatient := true } = some 0 := by decide
example : points { req .arterialBlood with bloodCircuitSampling := true } = some 0 := by decide
example : points { req .lymphNodeNeedleBiopsy with duringSurgery := true } = some 0 := by decide
example : points { req .jointPuncture with commonProcedureClaimedSameDay := true } = some 0 := by decide
example : points { req .jointPuncture with ageYears := 2 } = some 200 := by decide
example : points { req .jointPuncture with ageYears := 3 } = some 100 := by decide
example : points { req .jointPuncture with sides := .both, ageYears := 2 } = some 400 := by decide
example : points { req .ventricularPuncture with ageYears := 5 } = some 700 := by decide
example : points { req .lumbarPuncture with ageYears := 5 } = some 412 := by decide
example : points { req .marrowBiopsy with ageYears := 5 } = some 830 := by decide
example : points (req .sentinelCombined) = none := by decide
example : points { req .sentinelCombined with facilityStandardNotified := true, breastCancerPatient := true, radioisotopeUsed := true, dyeUsed := true } = some 5000 := by decide
example : points { req .sentinelSingle with facilityStandardNotified := true, breastCancerPatient := true, dyeUsed := true } = some 3000 := by decide
example : points { req .sentinelSingle with facilityStandardNotified := true, breastCancerPatient := true, radioisotopeUsed := true, dyeUsed := true } = none := by decide
example : points (req .transjugularLiverBiopsy) = none := by decide
example : points { req .transjugularLiverBiopsy with facilityStandardNotified := true } = some 13000 := by decide
example : points { req .prostateMriUltrasoundFusion with facilityStandardNotified := true } = none := by decide
example : points { req .prostateMriUltrasoundFusion with facilityStandardNotified := true, designatedProstatePatient := true } = some 8210 := by decide
example : points { req .endoscopicBiopsy with organs := [1, 1, 2] } = some 620 := by decide
example : points { req .endoscopicBiopsy with organs := [] } = none := by decide
example : points { req .transbronchialLungBiopsy with guideSheathUltrasoundPerformed := true } = some 5300 := by decide
example : points { req .transbronchialLungBiopsy with guideSheathUltrasoundPerformed := true, probeConfocalEndomicroscopy := true } = some 6300 := by decide
example : points { req .transbronchialLungBiopsy with ctFluoroscopicBronchoscopy := true } = none := by decide
example : points { req .transbronchialLungBiopsy with ctFluoroscopicBronchoscopy := true, ctFluoroscopyStandardNotified := true, probeConfocalEndomicroscopy := true } = some 7300 := by decide
example : points { req .virtualBronchoscopyBiopsy with guideSheathUltrasoundPerformed := true } = some 5500 := by decide
example : points (req .transbronchialCryobiopsy) = none := by decide
example : points { req .parietalPleuralCryobiopsy with facilityStandardNotified := true } = some 15800 := by decide
example : points { req .thoracotomyTissue with ageYears := 5 } = some 11070 := by decide
example : points { req .myocardiumTissue with ageYears := 5 } = some 6100 := by decide
example : points { req .pleuralAsciticFluid with ageYears := 5 } = some 280 := by decide
example : points { req .anteriorChamberFluid with ageYears := 5 } = some 594 := by decide
example : points { req .adrenalVenousSampling with ageYears := 5, filmPoints := 25 } = some 5825 := by decide
example : points { req .gastricDuodenalFluid with seriesAlreadyClaimed := true } = some 0 := by decide
example : assessDay [req .venousBlood, req .otherBlood] = none := by decide
example :
    let a := req .arterialBlood
    let b := { a with ageYears := 5 }
    assessDay [a, b] = none ∧ assessDay [b, a] = none := by decide
example :
    let a := req .adrenalVenousSampling
    let b := { a with filmPoints := 25 }
    assessDay [a, b] = none ∧ assessDay [b, a] = none := by decide
example : ((assess { req .venousBlood with duringSurgery := true }).bind
    (fun a => a.toCollection 400)) = none := by decide
example : ((assess { req .adrenalVenousSampling with filmPoints := 25 }).bind
    (fun a => a.toCollection 419)).map Examinations.TestCharge.scheduledPoints = some 4800 := by decide
example : serviceIncluded (req .sentinelSingle) .sentinelDye = true := by decide
example : serviceIncluded (req .percutaneousNeedleBiopsy) .ultrasound = true := by decide

end Sanri.MedicalFee.SpecimenCollection
