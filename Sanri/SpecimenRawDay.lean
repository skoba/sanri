import Sanri.SpecimenSelectionInventory
import Sanri.SpecimenRawIndividual

namespace Sanri.MedicalFee.SpecimenRawDay

open Sanri.History Sanri.Logic SpecimenCrossDivision

inductive Item where
  | urine (context : D000.Context)
  | specialUrine (item : UrineFecalTests.UrineSpecial)
  | sediment (method : UrineSediment.Method)
  | fecal (item : UrineFecalTests.Fecal)
  | punctureFluid (item : D004.Item)
  | tumorTissue (item : D004Tumor.Item)
  | morphology (context : BloodMorphology.Context)
  | chemistry (item : BloodChemistry.Item)
  | coagulation (item : D006.Item)
  | endocrine (item : D008.Item)
  | alpPag
  | tumorMarker (item : D009.Item)
  | hepatitis (item : D013.Item)
  | specificIge (antigen : Option Nat)
  | viralTiter (target : D012.Target)
  | classTiter (target : D012.Target) (antibody : D012.AntibodyClass)
  | autoantibody (item : D014.Item)
  | individual (test : SpecimenJudgment.Test)
  | other (key : SpecimenSelectionInventory.ItemKey)

def Item.supported : Item → Bool
  | .urine _ => true
  | .specialUrine i =>
    match i with
    | .trypsinogen2
    | .prostaglandinEMajorMetabolite | .lFabp | .ngal | .proteinImmunology | .other _ => false
    | _ => true
  | .sediment _ => true
  | .fecal i => decide (i ≠ .calprotectin)
  | .punctureFluid i =>
    match i with
    | .jointFluid | .phosphoTau | .amyloidRatio | .phosphoTauAmyloidRatio
    | .csfImmunology | .csfSmear | .other => false
    | _ => true
  | .tumorTissue _ => true
  | .morphology c => [BloodMorphology.Item.completeBloodCount, .eosinophilCount,
      .automatedDifferential, .microscopicDifferential].contains c.item
  | .chemistry i => [BloodChemistry.Item.bun, .uricAcid, .glucose, .ast, .alt, .creatinine,
      .totalProtein, .albumin, .gammaGT, .calcium, .ionizedCalcium,
      .uibcColorimetric, .tibcColorimetric].contains i
  | .coagulation i => [D006.Item.antithrombinActivity, .pic, .dDimer,
      .tat, .prothrombinFragment].contains i
  | .endocrine i => [D008.Item.fsh, .lh, .cortisol, .bap].contains i
  | .alpPag => true
  | .tumorMarker i => [4, 5, 13].contains i.number && i.variant == 0
  | .hepatitis i => [D013.Item.hbeAntigen, .hbeAntibody, .hcvAntibody].contains i
  | .specificIge _ => true
  | .viralTiter t => [D012.Target.rubella, .measles, .mumps, .cytomegalovirus].contains t
  | .classTiter t a =>
    [D012.Target.rubella, .measles, .mumps, .cytomegalovirus].contains t &&
      [D012.AntibodyClass.igg, .igm].contains a
  | .autoantibody i => [D014.Item.rnpQuant, .smQuant, .ssbQuant].contains i
  | .individual _ => true
  | .other _ => false

/-- 検査一覧と、その日を評価するための確認済みの入力。
判断料の対象一覧と加算の検査一覧は実施から組み立てる。採取条件・履歴は別入力。 -/
structure Input where
  judgment : SpecimenJudgment.OutpatientDay
  additions : SpecimenOutpatientDay.AdditionContext
  rows : List (Performance Item)
  collections : List SpecimenCollection.Context
  collectionHistoryConfirmed : Bool
  eligible : Nat → Option Bool
  chemistryFacts : Nat → BloodChemistry.Draw
  coverage : SpecimenJudgment.Test → SpecimenJudgment.IncludedTest
  excludedJudgmentCandidate : Option Bool
  /-- 当日の実施IDに対応する確認済みの加算条件。none は候補なしを確認済み。 -/
  emergency : Nat → Option SpecimenOutpatientDay.EmergencyTest
  rapid : Nat → Option SpecimenOutpatientDay.RapidTest
  /-- 迅速加算の指定と実施項目IDを確認した台帳。some none は指定外を表す。
  指定の資料・適用日と、同じ項目に使うIDは原実施の照合入力。 -/
  rapidDesignation : Nat → Option (Option Nat) := fun _ => none
  /-- 非採用又は通知(2)に列挙されない包括での項目数の扱い。 -/
  rapidOtherBasis : Nat → Option Bool := fun _ => none
  /-- D014注1の適用群が当日の入力に収まるとの確認。 -/
  autoantibodyDayConfirmed : Bool := false
  /-- D007のPAG法とD008のBAPが通知D008(16)の併施範囲に入るか。 -/
  alpPaired : Option Bool := none
  /-- D001の通知条件を、同じ原実施に結び付けた既存の区分入力で確認する。 -/
  specialUrineFacts : (p : Performance UrineFecalTests.UrineSpecial) →
    Option { ctx : D001.Context // ctx.performance = p ∧ D001.Eligible ctx } := fun _ => none
  /-- 鏡検とフローの二件が通知の併施範囲に入るか。 -/
  sedimentPaired : Option Bool := none
  sedimentFacts : (p : Performance UrineSediment.Method) → (paired : Bool) →
    Option { ctx : UrineSediment.Context // ctx.performance = p ∧
      ctx.d017 = some .noCombinedPerformance ∧
      ctx.otherSedimentPerformed = some paired ∧ UrineSediment.InScope p.item ctx } :=
    fun _ _ => none
  fecalFacts : (p : Performance UrineFecalTests.Fecal) →
    Option { ctx : D003.Context // ctx.performance = p ∧ D003.Eligible ctx } := fun _ => none
  punctureFluidFacts : (p : Performance D004.Item) →
    Option ({ ctx : D004.Context // ctx.item = p.item ∧ D004.Eligible ctx } ×
      SpecimenJudgment.Category) := fun _ => none
  /-- 同じ採取の原実施を、確認済みの同一がん種・検査種の群に対応付ける。 -/
  tumorTissueGroup : (rows : List (Performance D004Tumor.Item)) →
    Option { g : D004Tumor.Group // g.Valid ∧ g.tests.map (·.test.performance) = rows } :=
    fun _ => none
  /-- 同一採取に複数がん種があるときの、がん種別に確認した分類。 -/
  tumorTissueGroups : (rows : List (Performance D004Tumor.Item)) →
    Option { gs : List D004Tumor.Group //
      (∀ g ∈ gs, g.Valid) ∧ (gs.map (·.cancer)).Nodup ∧
      (gs.flatMap fun g => g.tests.map (·.test.performance)).Perm rows } :=
    fun _ => none
  tumorSensitivityFacts : (p : Performance D004Tumor.Item) →
    Option ({ ctx : D004Tumor.Classified // ctx.test.performance = p ∧ D004Tumor.Eligible ctx } ×
      SpecimenJudgment.Category) := fun _ => none
  /-- 区分別に確認し、原実施の全識別情報と照合できる個別評価。 -/
  individualFacts : Nat → Option Individual := fun _ => none
  /-- 当日の候補を含め、個別料を変更する別の適用群がないことの確認。
  区分別コンテキストで処理済みの条件は、その確認内容を含む。 -/
  individualStandalone : Nat → Option Bool := fun _ => none
  /-- D006-24(2)の併施範囲を確認した当日の候補。 -/
  lungPanelTogether : List (D006Targeted.LungPanel.Context ×
    List (Performance D006Targeted.LungPanel.Counterpart)) := []
  /-- 共通採否を反映した区分コンテキストで適格性を再確認する。 -/
  lungPanelEligible : (ctx : D006Targeted.LungPanel.Context) →
    Option (PLift (D006Targeted.LungPanel.Eligible ctx)) := fun _ => none
  /-- 検体検査に伴うことを確認した採取。右辺は対応する検査の実施ID。 -/
  collectionRows : List (Performance SpecimenCollection.Context × Nat) := []
  /-- 区分別の適格性と、採取・処置の適用群を確認済みか。 -/
  collectionFactsConfirmed : Nat → Option Bool := fun _ => none

def Input.dayCollections (c : Input) : List SpecimenCollection.Context :=
  c.collections ++ c.collectionRows.map (·.1.item)

def Input.site (c : Input) : Site := c.judgment.day.site

def Input.Supported (c : Input) : Prop :=
  ∀ row ∈ c.rows, row.item.supported = true

private def Input.morphology (c : Input) : List (Performance BloodMorphology.Context) :=
  c.rows.filterMap fun p => match p.item with
    | .morphology ctx => some { p with item := ctx }
    | _ => none

private def Input.chemistry (c : Input) : List (Performance BloodChemistry.Item) :=
  c.rows.filterMap fun p => match p.item with
    | .chemistry i => some { p with item := i }
    | _ => none

private def Input.urine (c : Input) : List D000.Context :=
  c.rows.filterMap fun p => match p.item with
    | .urine ctx => some { ctx with performance := { p with item := () } }
    | _ => none

private def Input.specialUrine (c : Input) : List (Performance UrineFecalTests.UrineSpecial) :=
  c.rows.filterMap fun p => match p.item with
    | .specialUrine i => some { p with item := i }
    | _ => none

private def specialUrinePoints (ctx : D001.Context) : Option Nat :=
  match UrineFecalTests.assess (D001.legacyInput ctx) with
  | some (.charged charge) => some charge.base
  | _ => none

theorem special_urine_projection (ctx : D001.Context) (eligible : D001.Eligible ctx)
    (points : Nat) : specialUrinePoints ctx = some points ↔ Satisfies D001.rules ctx points := by
  rw [D001.satisfies_iff]
  simp only [eligible.1, true_and, specialUrinePoints]
  cases h : UrineFecalTests.assess (D001.legacyInput ctx) with
  | none => simp
  | some assessment =>
    cases assessment with
    | onlyMainD017 => simp
    | requiresReference _ _ => simp
    | charged charge =>
      obtain ⟨⟨p, hp⟩, _⟩ := D001.determines ctx eligible
      have eq := (D001.satisfies_iff ctx p).mp hp
      rw [h] at eq
      have hc : charge = ⟨p, 0⟩ := by simpa using eq.2
      subst charge
      simp

private def Input.sediment (c : Input) : List (Performance UrineSediment.Method) :=
  c.rows.filterMap fun p => match p.item with
    | .sediment method => some { p with item := method }
    | _ => none

private def Input.fecal (c : Input) : List (Performance UrineFecalTests.Fecal) :=
  c.rows.filterMap fun p => match p.item with
    | .fecal i => some { p with item := i }
    | _ => none

private def sedimentContext (p : Performance UrineSediment.Method) : UrineSediment.Context :=
  ⟨p, none, none, none, none, none, none, []⟩

private def Input.sedimentGroups (c : Input) : Option (List ChoiceGroup) := do
  match c.sediment with
  | [] | [_] => some []
  | [a, b] =>
    if a.item = b.item then none else
    if !(← c.sedimentPaired) then some [] else do
      let (microscopy, flow) := if a.item = .microscopy then (a, b) else (b, a)
      let group ← sedimentMethodGroup (sedimentContext microscopy) (sedimentContext flow)
      return [group]
  | _ => none

private def sedimentCharge (ctx : UrineSediment.Context) : Option UrineFecalTests.Charge :=
  match UrineFecalTests.assess (UrineSediment.legacyInput ctx.performance.item ctx false) with
  | some (.charged charge) => some charge
  | _ => none

theorem sediment_projection (ctx : UrineSediment.Context)
    (scope : UrineSediment.InScope ctx.performance.item ctx)
    (isolatedFromD017 : ctx.d017 = some .noCombinedPerformance) (charge : UrineFecalTests.Charge) :
    sedimentCharge ctx = some charge ↔
      Satisfies (UrineSediment.resultRules ctx.performance.item) ctx (some charge) := by
  have absent : ¬ UrineSediment.PreferD017 ctx := by
    simp [UrineSediment.PreferD017, isolatedFromD017]
  rw [UrineSediment.satisfies_iff]
  simp [scope, UrineSediment.LegacyResult, UrineSediment.LegacyAssessment, absent]
  unfold sedimentCharge
  split <;> simp_all

theorem fecal_projection (ctx : D003.Context) (eligible : D003.Eligible ctx) (points : Nat) :
    UrineFecalTests.fecalPoints ctx.performance.item = points ↔ Satisfies D003.rules ctx points := by
  rw [D003.satisfies_iff]
  change _ ↔ D003.Eligible ctx ∧ some (UrineFecalTests.Assessment.charged ⟨_, 0⟩) = some (UrineFecalTests.Assessment.charged ⟨_, 0⟩)
  simp [eligible]

private def Input.punctureFluid (c : Input) : List (Performance D004.Item) :=
  c.rows.filterMap fun p => match p.item with
    | .punctureFluid i => some { p with item := i }
    | _ => none

theorem puncture_fluid_projection (ctx : D004.Context) (eligible : D004.Eligible ctx)
    (points : Nat) : D004.scheduled ctx = some points ↔ Satisfies D004.rules ctx points := by
  rw [D004.satisfies_iff, and_iff_right eligible]

/-- 同じ同時実施群は最小の実施IDから一度だけ列挙する。 -/
private def Input.renalGroups (c : Input) : Option (List ChoiceGroup) := do
  let rows := c.specialUrine
  let perRow ← rows.mapM fun p => renalSimultaneousGroup { performance := p } rows
  let groups := (rows.zip perRow).flatMap fun (p, groups) =>
    groups.filter fun g => g.members.all (p.id ≤ ·)
  if groups.any (fun g =>
      let items := (rows.filter fun p => g.members.contains p.id).map Performance.item
      items.eraseDups.length != items.length) then none else some groups

private def Input.coagulation (c : Input) : List (Performance D006.Item) :=
  c.rows.filterMap fun p => match p.item with
    | .coagulation i => some { p with item := i }
    | _ => none

private def pairs (rows : List α) : List (α × α) :=
  rows.zipIdx.flatMap fun (a, i) => (rows.drop (i + 1)).map (a, ·)

private def indexedPair (id : String) (a b : Performance α) (key : α → String) (division : String)
    (existing : ChoiceGroup) : Option ChoiceGroup :=
  SpecimenSelectionInventory.checkedProjection id
    [{ a with item := (division, key a.item) }, { b with item := (division, key b.item) }] existing

private def morphologyKey : BloodMorphology.Item → String
  | .eosinophilCount => "eosinophilCount"
  | .automatedDifferential => "automatedDifferential"
  | .microscopicDifferential => "microscopicDifferential"
  | _ => ""

private def chemistryKey : BloodChemistry.Item → String
  | .calcium => "calcium"
  | .ionizedCalcium => "ionizedCalcium"
  | .uibcColorimetric => "uibcColorimetric"
  | .tibcColorimetric => "tibcColorimetric"
  | _ => ""

/-- 対象はD007のPAG法とD008のBAPの二項目。併施の時間幅は確認値を使う。 -/
private def Input.alpGroups (c : Input) : Option (List ChoiceGroup) := do
  let rows := c.rows.filterMap fun p => match p.item with
    | .alpPag => some ({ p with item := .d007Pag } : Performance D008.CombinationItem)
    | .endocrine .bap => some { p with item := .endocrine .bap .other }
    | _ => none
  match rows with
  | [] | [_] => some []
  | [a, b] =>
    if a.item == b.item then none else
      (c.alpPaired).bind fun paired =>
        if paired then (endocrineGroup .alp rows).map (· :: []) else some []
  | _ => none

private def lungPanelTest := D006Targeted.judgmentTest .lungPanel

private def Input.lungPanelGroups (c : Input) : Option (List ChoiceGroup) := do
  let anchors := c.lungPanelTogether.map (·.1.performance.id)
  if anchors.eraseDups != anchors then none else
    let groups ← c.lungPanelTogether.mapM fun (context, surveyed) => do
      let anchor := context.performance
      if !c.rows.any (fun row =>
          match row.item with
          | .individual test => test == lungPanelTest && { row with item := () } == anchor
          | _ => false) then none else
        if !surveyed.all (fun other => c.rows.any fun row =>
            { row with item := () } == { other with item := () } &&
            match other.item, row.item with
            | .tissue item _ _, .tumorTissue actual => actual == item
            | .plasmaEgfr _, .individual test => test == D006GeneTests.Egfr.judgmentTest
            | .d006_27Ros1, .individual test => test == D006PlasmaPanel.judgmentTest .ros1
            | .d006_27Alk, .individual test => test == D006PlasmaPanel.judgmentTest .alk
            | .d006_27MetEx14, .individual test => test == D006PlasmaPanel.judgmentTest .metEx14
            | _, _ => false) then none else
          lungPanelGroup context surveyed
    return groups.flatten

/-- 一つの項目が複数の二件群に入るD005(3)の読みはここでは未確定とする。 -/
def Input.groups (c : Input) : Option (List ChoiceGroup) := do
  let morphology ← (pairs c.morphology).mapM fun (left, right) => do
    let a : Performance BloodMorphology.Item := { left with item := left.item.item }
    let b : Performance BloodMorphology.Item := { right with item := right.item.item }
    let existing ← morphologyGroups a b false
    existing.mapM (indexedPair BloodMorphology.eosinophilRule.id a b morphologyKey "D005")
  if !(overlappingGroups morphology.flatten).isEmpty then none else
    let chemistry ← (pairs c.chemistry).mapM fun (a, b) => do
      let kind := if [a.item, b.item].isPerm BloodChemistry.calciumGroup then
          some ("notice/D007/paragraph/2", ChemistryCombination.calcium)
        else if [a.item, b.item].isPerm BloodChemistry.ironBindingGroup then
          some ("notice/D007/paragraph/3", ChemistryCombination.ironBinding)
        else none
      match kind with
      | none => return []
      | some (clause, kind) =>
        if !(← a.simultaneousWith b) then return []
        let existing ← chemistryCombinationGroup kind [a, b]
        let group ← indexedPair clause a b chemistryKey "D007" existing
        return [group]
    let markers := c.coagulation.filter (fun p => D006.competingMarkers.contains p.item)
    if markers.length != (markers.map Performance.item).eraseDups.length then none else
      let coagulation ← match markers with
        | [a, b] => (a.simultaneousWith b).bind fun same =>
          if same then (coagulationMarkerGroup markers).map (· :: []) else some []
        | _ => some []
      let alp ← c.alpGroups
      let sediment ← c.sedimentGroups
      let renal ← c.renalGroups
      let lungPanel ← c.lungPanelGroups
      return morphology.flatten ++ chemistry.flatten ++ coagulation ++ alp ++ sediment ++ renal ++ lungPanel

/-- 指定した採否が全群に共通し、各群の必要件数を満たす場合にだけ射影する。 -/
def resolveChoices (groups : List ChoiceGroup) (selected : Option (List Nat)) :
    Option (List GroupChoice) := do
  if groups.isEmpty then
    if selected.getD [] == [] then some [] else none
  else
    let ids ← selected
    if !(consistentSelections groups [] []).any (·.isPerm ids) then none else
      return groups.map fun g => ⟨g, g.members.filter ids.contains⟩

private def fixedCharge (points : Nat) : Charge :=
  ⟨(· = points), points, rfl, fun _ h => h⟩

private def Input.morphologyPoints (c : Input) (choices : List GroupChoice) : Option (List Nat) :=
  (c.morphology.filter fun p => retained choices p.id).mapM fun p =>
    match BloodMorphology.assess p.item with
    | .payable base stain => some (base + stain)
    | _ => none

private def Input.drawFacts (c : Input) (draw : Nat) : BloodChemistry.Draw :=
  { c.chemistryFacts draw with
    calcium := { together := some false }
    ironBinding := { together := some false } }

private def Input.chemistryDraws (c : Input) (choices : List GroupChoice) :
    Option (List (Nat × List BloodChemistry.Item)) := do
  let ids ← c.chemistry.mapM Performance.draw
  if !(c.chemistry.zip ids).all (fun (row, draw) =>
      (c.drawFacts draw).eligible row.item == some true) then none else
    ids.eraseDups.mapM fun draw => do
      let projected ← chemistryDraw choices c.chemistry c.site draw (c.drawFacts draw)
      let items ← BloodChemistry.billableItems projected
      if items.isEmpty then none else some (draw, items)

private def Input.test (c : Input) (id : Nat) (test : SpecimenJudgment.Test)
    (candidate : Option Bool) : DayTest :=
  ⟨id, c.site, { c.coverage test with test := test }, candidate, c.emergency id, c.rapid id⟩

private def Input.tests (c : Input) (choices : List GroupChoice) : List DayTest :=
  (c.urine.map fun p => c.test p.performance.id D000.judgmentTest (some false)) ++
  (c.specialUrine.map fun p =>
    c.test p.id (D001.judgmentTest { performance := p })
      (if retained choices p.id then some true else c.excludedJudgmentCandidate)) ++
  (c.sediment.map fun p => c.test p.id (UrineSediment.judgmentTest p.item)
    (if retained choices p.id then some true else c.excludedJudgmentCandidate)) ++
  (c.fecal.map fun p =>
    c.test p.id (D003.judgmentTest { performance := p, d017BacteriaOrProtozoa := none }) (some true)) ++
  (c.punctureFluid.filterMap fun p =>
    (c.punctureFluidFacts p).map fun (_, category) =>
      c.test p.id (D004.judgmentTest p.item category) (some true)) ++
  (c.morphology.map fun p => c.test p.id (p.item.item.judgmentTest false)
    (if retained choices p.id then some true else c.excludedJudgmentCandidate)) ++
  (c.chemistry.map fun p => c.test p.id (D007.Item.judgmentTest ⟨.draw, p.item⟩)
    (if retained choices p.id then
      p.draw.bind fun draw => chemistryJudgmentCandidate p c.chemistry choices (c.drawFacts draw)
    else c.excludedJudgmentCandidate)) ++
  c.rows.filterMap (fun p =>
    let test : Option SpecimenJudgment.Test := match p.item with
      | .tumorTissue .sensitivity =>
        (c.tumorSensitivityFacts { p with item := .sensitivity }).map fun (_, category) =>
          D004Tumor.judgmentTest .sensitivity category
      | .tumorTissue i => some (D004Tumor.judgmentTest i .geneticChromosomal)
      | .coagulation i => some (D006.judgmentTest i)
      | .endocrine i => some (D008.judgmentTest i)
      | .alpPag => some (D007.Item.judgmentTest ⟨.late, .alpIsoenzymesPag⟩)
      | .tumorMarker i => some (D009.judgmentTest i)
      | .hepatitis i => some (D013.judgmentTest i)
      | .specificIge _ => some (D015.judgmentTest .specificIge false)
      | .viralTiter _ => some (D012.judgmentTest .viralTiter)
      | .classTiter _ _ => some (D012.judgmentTest .classSpecificTiter)
      | .autoantibody i => some (D014.judgmentTest i)
      | .individual test => some test
      | _ => none
    test.map fun t => c.test p.id t
      (if retained choices p.id then some true else c.excludedJudgmentCandidate))

/-- 区分と採血IDから包括キーを求める。 -/
def Input.assignment (p : Performance Item) : Option BundleKey :=
  match p.item with
  | .tumorTissue .sensitivity => none
  | .tumorTissue _ => bundleKey ⟨4, 2, .draw⟩ p
  | .chemistry _ => bundleKey ⟨7, 0, .draw⟩ p
  | .coagulation _ => bundleKey ⟨6, 0, .draw⟩ p
  | .endocrine _ => bundleKey ⟨8, 0, .draw⟩ p
  | .tumorMarker _ => bundleKey ⟨9, 0, .draw⟩ p
  | .hepatitis _ => bundleKey ⟨13, 0, .draw⟩ p
  | .specificIge _ => bundleKey ⟨15, 13, .draw⟩ p
  | .viralTiter _ => bundleKey ⟨12, 11, .specimen⟩ p
  | .classTiter _ _ => bundleKey ⟨12, 46, .specimen⟩ p
  | .autoantibody _ => bundleKey ⟨14, 0, .day⟩ p
  | _ => none

theorem assignment_disjoint (c : Input) {row : Performance Item} {a b : BundleKey}
    (ha : row ∈ assignedMembers Input.assignment c.rows a)
    (hb : row ∈ assignedMembers Input.assignment c.rows b) : a = b :=
  assigned_members_disjoint _ _ ha hb

private def Item.extraBundle : Item → Bool
  | .tumorTissue i => decide (i ≠ .sensitivity)
  | .coagulation _ | .endocrine _ | .tumorMarker _ | .hepatitis _ | .specificIge _
  | .viralTiter _ | .classTiter _ _ | .autoantibody _ => true
  | _ => false

private def distinctItems (rows : List (Performance α)) [BEq α] : Bool :=
  let items := rows.map Performance.item
  items.length == items.eraseDups.length

private def Input.coagulationContext (c : Input) (choices : List GroupChoice)
    (p : Performance D006.Item) : D006.Context :=
  { performance := p
    simultaneousSurvey := some c.coagulation
    principalPerformance := if retained choices p.id then some p.id else none }

private def Input.extraBundlePoints (c : Input) (choices : List GroupChoice) :
    Option (List Nat) := do
  let rows := c.rows.filter (·.item.extraBundle)
  let viral := rows.any fun p => match p.item with
    | .viralTiter _ => true
    | _ => false
  let classTargets := rows.filterMap fun p => match p.item with
    | .classTiter target _ => some target
    | _ => none
  -- 通知(38)イ・ウの併測範囲が問題となる場合は保留する。
  if (viral && !classTargets.isEmpty) ||
      classTargets.length != classTargets.eraseDups.length then none else
  let keys ← rows.mapM Input.assignment
  let kept := rows.filter fun p => retained choices p.id
  let points ← keys.eraseDups.mapM fun key => do
    let members := assignedMembers Input.assignment kept key
    match members with
    | [] => some []
    | anchor :: _ =>
      match anchor.item with
      | .tumorTissue _ =>
        let typed := members.filterMap fun p => match p.item with
          | .tumorTissue i => some ({ p with item := i } : Performance D004Tumor.Item)
          | _ => none
        match c.tumorTissueGroups typed with
        | some groups => return groups.val.map fun g => (D004Tumor.groupPoints g).total
        | none =>
          let group ← c.tumorTissueGroup typed
          return [(D004Tumor.groupPoints group.val).total]
      | .coagulation item =>
        let typed := members.filterMap fun p => match p.item with
          | .coagulation i => some ({ p with item := i } : Performance D006.Item)
          | _ => none
        if !distinctItems typed then none else
          let rows := typed.map (c.coagulationContext choices)
          let draw ← coagulationDraw { anchor with item := item } rows
          -- 対象の五項目はフィブリノゲン迅速測定加算の対象外。
          return [D006.drawPoints draw]
      | .endocrine _ =>
        let typed := members.filterMap fun p => match p.item with
          | .endocrine i => some ({ p with item := ⟨i, .blood⟩ } : Performance D008.BundleItem)
          | _ => none
        if !distinctItems typed then none else
          let items ← endocrineDraw c.site key.identity none typed
          return [D008.bundlePoints items]
      | .tumorMarker item =>
        let typed := members.filterMap fun p => match p.item with
          | .tumorMarker i => some ({ p with item := i } : Performance D009.Item)
          | _ => none
        if !distinctItems typed then none else
          let rows := typed.map fun p => ({ performance := p, route := .d009, bloodSpecimen := true } : D009.Context)
          let draw ← tumorMarkerDraw { anchor with item := item } rows (fun _ => none)
          return [D009.bundlePoints draw.items]
      | .hepatitis item =>
        let typed := members.filterMap fun p => match p.item with
          | .hepatitis i => some ({ p with item := i } : Performance D013.Item)
          | _ => none
        if !distinctItems typed then none else
          let rows := typed.map fun p => ({ performance := p } : D013.Context)
          let draw ← hepatitisDraw { anchor with item := item } rows
          return [SpecimenTests.groupedBase .hepatitis draw.count draw.standardSum]
      | .specificIge _ =>
        let rows ← members.mapM fun p => do
          let .specificIge antigen := p.item | none
          return (({ p with item := .specificIge } : Performance D015.Item), ← antigen)
        let ids := rows.map Prod.snd
        if ids.eraseDups != ids then none else
          let draw ← specificIgeDraw { anchor with item := .specificIge } rows
          return [SpecimenTests.groupedBase .specificIgE draw.tests.length 0]
      | .viralTiter _ =>
        let rows := members.filterMap fun p => match p.item with
          | .viralTiter t =>
            let test : D012.Context := {
              performance := { p with item := .local .viralTiter }
              target := some t }
            some (test, t)
          | _ => none
        let draw ← viralSpecimen { anchor with item := .local .viralTiter } rows
        return [SpecimenTests.groupedBase .viralAntibodies draw.targetCount 79]
      | .classTiter _ _ =>
        let rows := members.filterMap fun p => match p.item with
          | .classTiter t a =>
            let test : D012.Context := {
              performance := { p with item := .local .classSpecificTiter }
              target := some t
              antibodyClass := some a }
            some (test, t)
          | _ => none
        let draw ← classSpecimen { anchor with item := .local .classSpecificTiter } rows
        return [SpecimenTests.groupedBase .classSpecificViralAntibodies draw.targetCount 200]
      | .autoantibody _ =>
        let typed := members.filterMap fun p => match p.item with
          | .autoantibody i => some ({ p with item := i } : Performance D014.Item)
          | _ => none
        if !c.autoantibodyDayConfirmed || !distinctItems typed then none else
          let rows := typed.map fun p => ({ performance := p } : D014.Context)
          let group ← autoantibodyDay c.site rows
          return [SpecimenTests.groupedBase .autoantibodies group.count group.sum]
      | _ => none
  return points.flatten

private def Input.individuals (c : Input) (choices : List GroupChoice) : Option (List Individual) :=
  (c.rows.filterMap fun row => match row.item with
    | .individual test => if retained choices row.id then some { row with item := test } else none
    | _ => none).mapM fun row => do
    let confirmed ←
      match c.lungPanelTogether.find? (fun pair => pair.1.performance.id == row.id) with
      | none => c.individualFacts row.id
      | some (context, surveyed) => do
        let ctx ← lungPanelInput context surveyed choices
        let eligible ← c.lungPanelEligible ctx
        return Individual.d006_24 ctx eligible.down
    if confirmed.performance == row && c.individualStandalone row.id == some true then
      some confirmed
    else none

private def Input.validCollectionRows (c : Input) : Bool :=
  let ids := c.collectionRows.map (·.1.id)
  ids.eraseDups == ids && c.collectionRows.all fun (p, testId) =>
    p.site == c.site && !p.item.inpatient && c.collectionFactsConfirmed p.id == some true &&
    (!SpecimenCollection.isSeries p.item.item || p.series == some p.item.seriesId) &&
    c.rows.any (fun row => row.id == testId &&
      (!p.specimen.isSome || row.specimen == p.specimen))

/-- D006-12・D006-27を当日確認済みの採血IDごとに集約する。 -/
private def individualPoints (rows : List Individual) : Option (List Nat) := do
  let panel := rows.filterMap fun i =>
    i.plasmaPanelItem.map fun item =>
      ({ performance := { i.performance with item := item }, points := i.points } :
        D006PlasmaPanel.Assessed)
  let draws ← panel.mapM (·.performance.draw)
  let grouped ← draws.eraseDups.mapM fun draw => do
    let members := panel.filter fun p => p.performance.draw == some draw
    let items := members.map (·.performance.item)
    if items.eraseDups != items then none else some (D006PlasmaPanel.bundlePoints members).total
  return (rows.filter fun i => i.plasmaPanelItem.isNone).map Individual.points ++ grouped

private def Input.rapidBasis (c : Input) (choices : List GroupChoice) (id : Nat) :
    Option RapidCountBasis := do
  let row ← c.rows.find? (·.id == id)
  if !retained choices id then return .other (c.rapidOtherBasis id)
  let sameDraw := c.rows.filter fun p => p.draw == row.draw && retained choices p.id
  match row.item with
  | .chemistry item =>
    let p : Performance BloodChemistry.Item := { row with item := item }
    let draw ← p.draw
    chemistryRapidCountBasis p c.chemistry choices (c.drawFacts draw)
  | .coagulation item =>
    let count := (sameDraw.filter fun p => match p.item with
      | .coagulation i => i.bundleEligible
      | _ => false).length
    return if item.bundleEligible && 3 ≤ count then .bundled .coagulation else .individual
  | .endocrine item =>
    let items := sameDraw.filterMap fun p => match p.item with
      | .endocrine i => some (⟨i, .blood⟩ : D008.BundleItem)
      | _ => none
    endocrineRapidCountBasis items ⟨item, .blood⟩
  | .tumorMarker _ =>
    let count := (sameDraw.filter fun p => match p.item with
      | .tumorMarker _ => true
      | _ => false).length
    return if 2 ≤ count then .bundled .tumorMarker else .individual
  | .tumorTissue .sensitivity => some .individual
  | .tumorTissue _ | .hepatitis _ | .specificIge _ | .viralTiter _ | .classTiter _ _ | .autoantibody _ =>
    some (.other (c.rapidOtherBasis id))
  | .individual test =>
    if test.major == 6 && [4, 12, 27].contains test.suffix then
      some (.other (c.rapidOtherBasis id))
    else some .individual
  | _ => some .individual

private def Input.checkedRapid (c : Input) (choices : List GroupChoice) (day : Day)
    (rows : List DayTest) : Option Day := do
  if c.additions.selection != .rapid then return day
  let candidates ← rows.mapM fun row => do
    let designation ← c.rapidDesignation row.id
    match row.rapid, designation with
    | none, _ => some none
    | some t, some key =>
      if t.item != key || !t.designated then none else
        (c.rapidBasis choices row.id).map fun basis => some (t, basis)
    | some t, none =>
      if t.designated then none else some none
  day.withAssessedRapid (candidates.filterMap id)

/-- 元の事実と選択を日次評価へ渡す。対応範囲外・確認不足はいずれも none。 -/
private def Input.prepareFacts (c : Input) (selected : Option (List Nat)) :
    Option (Day × List Nat) := do
  let ids := c.rows.map Performance.id
  if decide (c.judgment.status ≠ .outpatient) ||
      !c.collectionHistoryConfirmed || !c.validCollectionRows || c.collections.length > 1 ||
      !c.collections.all (fun p => SpecimenCollection.isD400 p.item && !p.inpatient) ||
      !c.rows.all (fun p => p.item.supported && p.site == c.site &&
      c.eligible p.id == some true) || ids.eraseDups != ids || c.additions.site != c.site then none
  else
    let choices ← resolveChoices (← c.groups) selected
    if c.morphology.length != (c.morphology.map (·.item.item)).eraseDups.length ||
        c.urine.length > 1 then none else
      let urine ← c.urine.mapM fun p =>
        if p.performingInstitution == some p.performance.site.institution &&
            !p.analytes.isEmpty && p.method.isSome &&
            (p.arrangement == some .direct || p.arrangement == some (.contracted (some true)))
        then some D000.points else none
      let specialUrine ← (c.specialUrine.filter fun p => retained choices p.id).mapM fun p => do
        let confirmed ← c.specialUrineFacts p
        specialUrinePoints confirmed.val
      let sediment ← (c.sediment.filter fun p => retained choices p.id).mapM fun p => do
        let paired := choices.any fun choice =>
          choice.group.source == UrineSediment.microscopySelectionRule.source &&
          choice.group.members.contains p.id
        let confirmed ← c.sedimentFacts p paired
        (sedimentCharge confirmed.val).map UrineFecalTests.Charge.total
      let fecal ← c.fecal.mapM fun p => do
        let confirmed ← c.fecalFacts p
        return UrineFecalTests.fecalPoints confirmed.val.performance.item
      let punctureFluid ← c.punctureFluid.mapM fun p => do
        let (confirmed, _) ← c.punctureFluidFacts p
        D004.scheduled confirmed.val
      let sensitivity ← (c.rows.filterMap fun p => match p.item with
        | .tumorTissue .sensitivity => some ({ p with item := .sensitivity } : Performance D004Tumor.Item)
        | _ => none).mapM fun p => do
          let _ ← c.tumorSensitivityFacts p
          return D004Tumor.Item.sensitivity.points
      let morphology ← c.morphologyPoints choices
      let draws ← c.chemistryDraws choices
      let extra ← c.extraBundlePoints choices
      let pag := c.rows.filterMap fun p => match p.item with
        | .alpPag =>
          if retained choices p.id then some (BloodChemistryLate.Item.points .alpIsoenzymesPag) else none
        | _ => none
      let individuals ← c.individuals choices
      let directPoints ← individualPoints individuals
      let execution := (draws.map fun (_, items) => BloodChemistry.pointsForItems items) ++
        morphology ++ urine ++ specialUrine ++ sediment ++ fecal ++ punctureFluid ++ sensitivity ++ extra ++ pag ++
        directPoints
      let tests := c.tests choices
      let day ← Day.withTests ⟨[], [], c.judgment, c.additions⟩ tests
      let day ← c.checkedRapid choices day tests
      let _ ← day.judgment.points
      return (day, execution)

def Input.prepare (c : Input) (selected : Option (List Nat)) : Option (Day × List Nat) :=
  (c.prepareFacts selected).map fun (day, execution) =>
    ({ day with execution := execution.map fixedCharge }, execution)

theorem tumor_tissue_projection (g : D004Tumor.Group) (valid : g.Valid)
    (points : D004Tumor.GroupResult) :
    Satisfies D004Tumor.groupRules g points ↔ points = D004Tumor.groupPoints g := by
  rw [D004Tumor.group_satisfies_iff, and_iff_right valid]

private theorem prepare_execution {c : Input} {selected : Option (List Nat)} {prep : Day}
    {execution : List Nat} (h : c.prepare selected = some (prep, execution)) :
    prep.execution = execution.map fixedCharge := by
  unfold Input.prepare at h
  obtain ⟨⟨day, points⟩, _, eq⟩ := Option.map_eq_some_iff.mp h
  cases eq
  rfl

private theorem fixed_charges (points : List Nat) :
    ChargeList (points.map fixedCharge) points := by
  induction points with
  | nil => exact .nil
  | cons _ _ ih => exact .cons rfl ih

theorem morphology_projection (c : BloodMorphology.Context) (base stain : Nat)
    (h : BloodMorphology.assess c = .payable base stain) :
    Satisfies BloodMorphology.individualRules c (base, stain) :=
  (BloodMorphology.payable_iff c base stain).2 h

theorem chemistry_projection (c : Input) (choices : List GroupChoice) (draw : Nat)
    (projected : BloodChemistry.Draw) (points : Nat)
    (h : chemistryDraw choices c.chemistry c.site draw (c.drawFacts draw) = some projected) :
    BloodChemistry.DrawPoints projected points ↔
      (chemistryDraw choices c.chemistry c.site draw (c.drawFacts draw)).bind
        BloodChemistry.points = some points :=
  chemistryDraw_points choices c.chemistry c.site draw (c.drawFacts draw) projected points h

/-- D006の限定項目では、群の適格性を確認すれば、採血の本体点数が
加算込みの既存制約を満たし、他の点数は許されない。 -/
theorem coagulation_projection (g : D006.DrawGroup) (valid : g.Valid)
    (noAddition : ∀ c ∈ g.tests, D006.FibrinogenPrimaryFailure c) :
    D006.Payable g (D006.drawPoints g) ∧
      ∀ q, D006.Payable g q → q = D006.drawPoints g := by
  have zero : ∀ tests : List D006.Context,
      (∀ c ∈ tests, D006.FibrinogenPrimaryFailure c) → D006.Additions tests 0 := by
    intro tests
    induction tests with
    | nil => intro _; rfl
    | cons test rest ih =>
      intro h
      exact ⟨0, 0, (D006.addition_satisfies_iff _ _).2 (.inr ⟨rfl, .inl (h test (by simp))⟩),
        ih (fun c hc => h c (by simp [hc])), rfl⟩
  have payable : D006.Payable g (D006.drawPoints g) := by
    refine ⟨⟨_, _, D006.drawPoints g⟩, 0, (D006.draw_satisfies_iff _ _).2 ⟨valid, rfl, rfl, rfl⟩,
      zero _ noAddition, by simp⟩
  obtain ⟨_, _, unique⟩ := coagulationDraw_points g valid
    (fun c hc => .inr (.inl (noAddition c hc)))
  exact ⟨payable, fun q h => (unique q h).trans (unique _ payable).symm⟩

/-- 加算の選択と、その選択に必要な同一検査の証拠・当日の先行履歴。 -/
structure Confirmed (day : Day) : Prop where
  site : day.additions.site = day.judgment.day.site
  judgment : day.judgment.Eligible
  emergency : day.additions.selection = .emergency →
    SpecimenOutpatientDay.EmergencyConfirmed day.additions ∧
    day.additions.emergencyClaimed = some false ∧ day.additions.priorRapidItems = some [] ∧
    day.additions.nightEarlyMorningAddition = false
  rapid : day.additions.selection = .rapid → ∃ prior,
    day.additions.priorRapidItems = some prior ∧ prior.Nodup ∧ prior.length ≤ 5 ∧
    day.additions.emergencyClaimed = some false

def Input.Scope (c : Input) (selected : Option (List Nat)) : Prop :=
  c.Supported ∧ ∃ prep execution day,
    c.prepare selected = some (prep, execution) ∧
    prep.withCollectionContexts c.dayCollections = some day ∧ Confirmed prep

def Input.Permits (c : Input) (selected : Option (List Nat)) (r : Breakdown) : Prop :=
  ∃ prep execution day, c.prepare selected = some (prep, execution) ∧
    prep.withCollectionContexts c.dayCollections = some day ∧ day.Permits r

theorem determines (c : Input) (selected : Option (List Nat)) (scope : c.Scope selected) :
    ∃ r, c.Permits selected r ∧ ∀ other, c.Permits selected other → other = r := by
  obtain ⟨_, prep, execution, day, hp, hd, h⟩ := scope
  obtain ⟨r, hr, unique⟩ := day_determines_from_collection_contexts prep day c.dayCollections hd
    h.site h.judgment h.emergency h.rapid
  refine ⟨r, ⟨prep, execution, day, hp, hd, hr⟩, ?_⟩
  rintro other ⟨prep', execution', day', hp', hd', ho⟩
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
  rw [hd] at hd'
  cases Option.some.inj hd'
  exact unique _ ho

def Input.Allowed (c : Input) (r : Breakdown) : Prop :=
  ∃ selected, c.Scope selected ∧ c.Permits selected r

/-- 加算なしの範囲で使う計算射影。判断料・採取の未確定は伝播する。 -/
def Input.withoutAdditions (c : Input) (selected : Option (List Nat)) : Option Breakdown := do
  let (prep, execution) ← c.prepare selected
  if prep.additions.selection != .none then none else
    let judgment ← prep.judgment.points
    let assessments ← SpecimenCollection.assessDay c.dayCollections
    let collection := assessments.filterMap fun a => (a.toCollection 0).map (·.scheduledPoints)
    let total := SpecimenOutpatientDay.assess ⟨prep.judgment.day.site, execution.sum, judgment, collection, 0, 0⟩
    return ⟨execution, collection, judgment, ⟨0, 0⟩, total⟩

private theorem collection_charges (day : Day) (rows : List SpecimenCollection.Assessment) :
    ChargeList (day.withCollectionAssessments rows).collection
      (rows.filterMap fun a => (a.toCollection 0).map (·.scheduledPoints)) := by
  induction rows with
  | nil => exact .nil
  | cons a rest ih =>
    cases h : a.toCollection 0 with
    | none => simpa [Day.withCollectionAssessments, h] using ih
    | some charge =>
      simpa [Day.withCollectionAssessments, h, fixedCharge] using
        (ChargeList.cons (charge := fixedCharge charge.scheduledPoints) rfl ih)

theorem without_additions_sound (c : Input) (selected : Option (List Nat))
    (r : Breakdown) (h : c.withoutAdditions selected = some r)
    (eligible : ∀ prep execution, c.prepare selected = some (prep, execution) →
      prep.judgment.Eligible) :
    c.Permits selected r := by
  unfold Input.withoutAdditions at h
  cases hp : c.prepare selected with
  | none => simp [hp] at h
  | some pair =>
    obtain ⟨prep, execution⟩ := pair
    by_cases ha : prep.additions.selection = .none
    · cases hj : prep.judgment.points with
      | none => simp [hp, ha, hj] at h
      | some judgment =>
        cases hc : SpecimenCollection.assessDay c.dayCollections with
        | none => simp [hp, hc] at h
        | some assessments =>
          simp [hp, ha, hj, hc] at h
          subst r
          refine ⟨prep, execution, prep.withCollectionAssessments assessments, hp, ?_, ?_⟩
          · simp [Day.withCollectionContexts, hc]
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · change ChargeList prep.execution execution
              rw [prepare_execution hp]
              exact fixed_charges execution
            · exact collection_charges prep assessments
            · exact (SpecimenJudgment.outpatient_day_iff _ (eligible _ _ hp) _).2 hj
            · simp [Day.withCollectionAssessments, SpecimenOutpatientDay.additionRules,
                satisfies_cons, satisfies_nil, SpecimenOutpatientDay.emergencyPrimary,
                SpecimenOutpatientDay.rapidPrimary, SpecimenOutpatientDay.emergencyOnce,
                SpecimenOutpatientDay.emergencyNightExclusion, SpecimenOutpatientDay.rapidBundle,
                SpecimenOutpatientDay.rapidDailyLimit, SpecimenOutpatientDay.rapidConsultationBundle, ha]
            · exact (SpecimenOutpatientDay.satisfies_iff ..).2 rfl
    · simp [hp, ha] at h

-- 複数区分の合成例はカーネルで簡約して検査する。
section
set_option maxRecDepth 4096
private def site : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def base : Input where
  judgment := ⟨⟨site, [], false, ⟨⟨site.monthScope, []⟩, by simp⟩, ⟨site.monthScope, []⟩⟩,
    true, .outpatient, none, none, none⟩
  additions := ⟨site, .none, [], [], some false, some [], false⟩
  rows := []
  collections := []
  collectionHistoryConfirmed := true
  eligible := fun _ => some true
  chemistryFacts := fun _ =>
    { performed := [], albuminByModifiedBCP := some true, creatinineByJaffe := some false }
  coverage := fun test => ⟨test, false, false, none, none⟩
  excludedJudgmentCandidate := some false
  emergency := fun _ => none
  rapid := fun _ => none

private def urineDaySite : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def urineDayBase : Input :=
  { base with
    judgment := { base.judgment with day := ⟨urineDaySite, [], false,
      ⟨⟨urineDaySite.monthScope, []⟩, by simp⟩, ⟨urineDaySite.monthScope, []⟩⟩ }
    additions := { base.additions with site := urineDaySite } }

private def urineProtein : Performance UrineFecalTests.UrineSpecial :=
  { id := 1, site := urineDaySite, item := .protein, specimen := some 1 }

private theorem urineProteinEligible : D001.Eligible { performance := urineProtein } := by
  simp [D001.Eligible, Satisfies, D001.conditions, D001.screeningRule, D001.porphyriaRule,
    D001.renalRule, D001.trypsinogenRule, D001.pancreaticRule, D001.myoinositolRule,
    D001.pgeRule, D001.colitisRule, D001.oxalateRule, D001.lfabpRule, D001.ngalRule,
    D001.lfabpNgalRule, D001.stripRatioRule, D001.trypsinogenParagraph, D001.pgeParagraph,
    D001.ngalParagraph, D001.ReferenceResolved, D001.RenalItem, urineProtein]
  repeat' first | apply And.intro | exact True.intro | rfl | (intro h; contradiction)

private def stool : Performance UrineFecalTests.Fecal :=
  { id := 2, site := urineDaySite, item := .lipids, specimen := some 2 }

private theorem stoolEligible : D003.Eligible
    { performance := stool, d017BacteriaOrProtozoa := some false } := by
  simp [D003.Eligible, Satisfies, D003.conditions, D003.d017Rule, D003.qualitativeRule,
    D003.quantitativeRule, D003.purposeRule, D003.diagnosisRule, D003.monitoringRule,
    D003.colonoscopyRule, D003.urinaryPgeSelectionRule, D003.HemoglobinItem, stool]
  repeat' first | apply And.intro | exact True.intro | rfl | (intro h; contradiction)

private def urineAndStool : Input :=
  { urineDayBase with
    rows := [{ urineProtein with item := .specialUrine .protein }, { stool with item := .fecal .lipids }]
    specialUrineFacts := fun p => if h : urineProtein = p then
      some ⟨{ performance := urineProtein }, h, urineProteinEligible⟩ else none
    fecalFacts := fun p => if h : stool = p then
      some ⟨{ performance := stool, d017BacteriaOrProtozoa := some false }, h, stoolEligible⟩ else none }

example : (urineAndStool.withoutAdditions none).map (fun r => (r.execution, r.judgment)) =
    some ([7, 25], 34) := by decide

example : ({ urineAndStool with specialUrineFacts := fun _ => none }.withoutAdditions none) =
    none := by decide

private def microscopyRow : Performance UrineSediment.Method :=
  { id := 3, site := urineDaySite, item := .microscopy, specimen := some 3 }

private def microscopyContext : UrineSediment.Context :=
  { sedimentContext microscopyRow with
    indication := some .medicallyNecessaryOnExamination
    location := some .directInHouse
    d017 := some .noCombinedPerformance
    otherSedimentPerformed := some false
    stained := some true }

private def punctureRow : Performance D004.Item :=
  { id := 4, site := urineDaySite, item := .huhner, specimen := some 4 }

private def microscopyAndPuncture : Input :=
  { urineAndStool with
    rows := urineAndStool.rows ++
      [{ microscopyRow with item := .sediment .microscopy },
       { punctureRow with item := .punctureFluid .huhner }]
    sedimentFacts := fun p paired =>
      if hp : microscopyRow = p then
        if hb : paired = false then
          some ⟨microscopyContext, hp, rfl, congrArg some hb.symm, by
            subst p
            exact ⟨rfl, trivial, .inl rfl, .inl rfl, .inl rfl, rfl⟩⟩
        else none
      else none
    punctureFluidFacts := fun p =>
      if h : p.item = .huhner then
        some (⟨{ item := .huhner }, h.symm, D004.huhner_eligible⟩, .urineFecal)
      else none }

example : (microscopyAndPuncture.withoutAdditions none).map Breakdown.execution =
    some [7, 36, 25, 20] := by decide

private def flowRow : Performance UrineSediment.Method :=
  { id := 5, site := urineDaySite, item := .flow, specimen := some 3, simultaneous := some 2 }

private def flowMeasurements : List (Performance UrineSediment.FlowComponent) :=
  [UrineSediment.FlowComponent.redCells, .whiteCells, .epithelialCells, .casts, .bacteria].map
    (fun component => { flowRow with item := component })

private def flowContext (paired : Bool) : UrineSediment.Context :=
  { sedimentContext flowRow with
    indication := some .medicallyNecessaryOnExamination
    location := some .directInHouse
    d017 := some .noCombinedPerformance
    otherSedimentPerformed := some paired
    chosenSedimentMethod := some .flow
    flowMeasurements }

private theorem flowInScope (paired : Bool) : UrineSediment.InScope .flow (flowContext paired) := by
  refine ⟨rfl, trivial, .inl rfl, ?_, .inl rfl, ?_⟩
  · cases paired
    · exact .inl rfl
    · exact .inr ⟨rfl, rfl⟩
  · intro component
    refine ⟨{ flowRow with item := component }, ?_, rfl, rfl⟩
    cases component <;> simp [flowContext, flowMeasurements]

private def pairedSediment : Input :=
  { microscopyAndPuncture with
    rows := microscopyAndPuncture.rows ++ [{ flowRow with item := .sediment .flow }]
    sedimentFacts := fun p paired =>
      if hp : flowRow = p then
        some ⟨flowContext paired, hp, rfl, rfl, hp ▸ flowInScope paired⟩
      else microscopyAndPuncture.sedimentFacts p paired }

example :
    let paired := { pairedSediment with sedimentPaired := some true }
    pairedSediment.groups = none ∧
      paired.groups.map (List.map ChoiceGroup.members) = some [[3, 5]] ∧
      (paired.prepare none).isNone ∧
      (paired.withoutAdditions (some [5])).map Breakdown.execution = some [7, 24, 25, 20] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site := urineDaySite, item := .specialUrine .transferrin, simultaneous := some 1 },
       { id := 2, site := urineDaySite, item := .specialUrine .albuminQuantitative, simultaneous := some 1 }]
    let c := { urineDayBase with rows }
    c.groups.map (List.map ChoiceGroup.members) = some [[1, 2]] ∧
      ({ c with rows := rows.map fun r => { r with simultaneous := none } } : Input).groups.isNone := by decide

private def sensitivityRow : Performance D004Tumor.Item :=
  { id := 6, site := urineDaySite, item := .sensitivity, specimen := some 5 }

private def sensitivityContext : D004Tumor.Classified :=
  { test := { performance := sensitivityRow
              cancer := .breast
              purpose := .solidCancerDrugSelection
              method := some .hdra
              surgicalTissue := some true
              cytotoxicDrug := some true
              priorClaims := some { coverage := ⟨1, none, Period.through urineDaySite.date⟩
                                    entries := [], distinctIds := by simp } }
    branch := none }

private theorem sensitivityEligible : D004Tumor.Eligible sensitivityContext := by
  simp [D004Tumor.Eligible, D004Tumor.eligibilityRules, satisfies_cons, satisfies_nil,
    D004Tumor.geneRule, D004Tumor.hematologicRule, D004Tumor.egfrRule, D004Tumor.alkRule,
    D004Tumor.her2Rule, D004Tumor.brcaRule, D004Tumor.sensitivityRule, D004Tumor.cytotoxicRule,
    D004Tumor.lynchMsiRule, D004Tumor.drugAidRule, D004Tumor.otherSimpleRule,
    D004Tumor.complexRule, D004Tumor.branchRule]
  repeat' first | apply And.intro | exact True.intro | rfl | (intro h; contradiction)
  all_goals intro h
  · rcases h.1 with a | a | a <;> contradiction
  · exact ⟨by decide, rfl, ⟨.hdra, by simp, rfl⟩, rfl, rfl⟩
  · rfl
  · intro impossible
    cases impossible

example :
    let c : Input := { urineAndStool with
      rows := urineAndStool.rows ++ [{ sensitivityRow with item := .tumorTissue .sensitivity }]
      tumorSensitivityFacts := fun p =>
        if h : sensitivityRow = p then some (⟨sensitivityContext, h, sensitivityEligible⟩, .biochemicalII)
        else none }
    (c.withoutAdditions none).map Breakdown.execution = some [7, 25, 2500] := by decide

private def chemistryRows (items : List BloodChemistry.Item) : List (Performance Item) :=
  items.zipIdx.map fun (i, j) =>
    { id := j + 10, site, item := .chemistry i, draw := some 1, simultaneous := some 1 }

private def morphologyRow (id : Nat) (item : BloodMorphology.Item) : Performance Item :=
  { id, site, specimen := some 2, draw := some 1, item := .morphology {
      item
      counts := some [.redCells, .whiteCells, .hemoglobin, .hematocrit, .platelets]
      cellClasses := some [.lymphocyte, .monocyte, .neutrophil, .eosinophil, .basophil] } }

private def raw429 : Input :=
  { base with rows := morphologyRow 1 .completeBloodCount ::
      chemistryRows [.bun, .creatinine, .ast, .alt, .totalProtein, .albumin, .gammaGT, .uricAcid]
              collections := [{ item := .venousBlood, ageYears := 40 }] }

private def rawDifferential : Input :=
  let urine : D000.Context :=
    ⟨⟨3, site, (), none, none, none, none⟩, some site.institution, some .strip, [.ph], some .direct⟩
  { base with rows := [morphologyRow 1 .eosinophilCount, morphologyRow 2 .automatedDifferential,
    { id := 3, site, item := .urine urine }] ++ chemistryRows [.bun, .uricAcid, .glucose, .ast, .alt] }

private def total (c : Input) (selected : Option (List Nat)) : Option Nat :=
  (c.withoutAdditions selected).map (·.total.specimenWithCollection)

example : total raw429 none = some 429 := by decide
example : total rawDifferential (some [1]) = some 405 := by decide
example : total rawDifferential (some [2]) = some 403 := by decide
example : total rawDifferential none = none := by decide

example : total { raw429 with rows := raw429.rows.map fun p => { p with draw := none } } none =
    none := by decide

example : total { raw429 with judgment := { raw429.judgment with day :=
    { raw429.judgment.day with performances := ⟨{ site.monthScope with patient := 4 }, []⟩ } } }
    none = none := by decide

/-- 二つの選択群と採血包括、D026、D400を同じ原実施日から評価する。 -/
private def twoGroups : Input :=
  let rows : List (Performance Item) :=
    [{ id := 20, site, item := .chemistry .calcium, draw := some 1, simultaneous := some 1 },
     { id := 21, site, item := .chemistry .ionizedCalcium, draw := some 1, simultaneous := some 1 }]
  { rawDifferential with
    rows := rawDifferential.rows ++ rows
    collections := raw429.collections }

example : (twoGroups.groups.map List.length, total twoGroups (some [1, 20])) =
    (some 2, some 445) := by decide

private def multiDivision : Input :=
  let coagulation := [D006.Item.antithrombinActivity, .pic, .dDimer, .tat, .prothrombinFragment]
  let hepatitis := [D013.Item.hbeAntigen, .hbeAntibody, .hcvAntibody]
  { twoGroups with rows := twoGroups.rows ++
      (coagulation.zipIdx.map fun (i, j) =>
        { id := j + 30, site, item := .coagulation i, draw := some 1, simultaneous := some 2 }) ++
      (hepatitis.zipIdx.map fun (i, j) =>
        { id := j + 40, site, item := .hepatitis i, draw := some 1 }) }

example :
    (multiDivision.groups.map List.length,
      (multiDivision.withoutAdditions (some [1, 20, 33])).map Breakdown.judgment,
      total multiDivision (some [1, 20, 33])) =
    (some 3, some 413, some 1479) := by decide

private def mixedRawDay : Input :=
  { urineAndStool with
    rows := urineAndStool.rows ++
      (multiDivision.rows.filter (fun p => p.id != 1 && p.id != 2)).map
        (fun p => { p with site := urineDaySite }) ++
      [{ id := 70, site := urineDaySite, item := .alpPag, draw := some 1 },
       { id := 71, site := urineDaySite, item := .endocrine .bap, draw := some 1 }]
    alpPaired := some true
    collections := raw429.collections }

example :
    (mixedRawDay.withoutAdditions (some [20, 33, 70])).map
      (fun r => (r.execution, r.judgment, r.collection, r.total.specimenWithCollection)) =
    some ([93, 26, 7, 25, 600, 290, 180], 447, [40], 1708) := by decide

private def leukemiaExample : Individual := by
  let c : D006Leukemia.D006_3.Context :=
    ⟨.minor, some .treatmentMonitoring, some .philadelphiaPositiveAll, some true⟩
  exact Individual.d006_3 c { id := 80, site := urineDaySite, item := .minor, draw := some 1 } .hematological
    (by simp [c, D006Leukemia.D006_3.Eligible, D006Leukemia.D006_3.majorInternationalRule,
      D006Leukemia.D006_3.majorQuantitativeRule, D006Leukemia.D006_3.minorRule]) rfl

private def cultureExample : Individual := by
  let p : Performance D018.Item :=
    { id := 82, site := urineDaySite, item := .bloodOrPuncture, specimen := some 82 }
  let c : D018.Context :=
    { performance := p, material := .cerebrospinal, method := .plannedIdentification
      targetExcludesMycobacteria := some true, generalCulture := true, anaerobicCulture := true
      fungalCulture := false, searchSelection := some ⟨[(p, .cerebrospinal)], none⟩ }
  refine Individual.d018 c ?_
  change Satisfies D018.eligibilityRules c ()
  simp only [D018.eligibilityRules, satisfies_cons, satisfies_nil]
  refine ⟨⟨rfl, Or.inl ⟨rfl, by decide⟩, ⟨rfl, fun h => by contradiction⟩, ?_⟩, fun _ => rfl,
    ⟨fun impossible => by contradiction, fun impossible => by contradiction⟩, trivial⟩
  exact ⟨⟨[(p, .cerebrospinal)], none⟩, rfl, by simp [c], Or.inl rfl⟩

private def sevenCategoryDay : Input :=
  let individuals := [leukemiaExample, cultureExample]
  { mixedRawDay with
    rows := mixedRawDay.rows ++
      [{ id := 81, site := urineDaySite, item := .endocrine .fsh, draw := some 1 }] ++ individuals.map (fun i =>
      { i.performance with item := .individual i.performance.item })
    individualFacts := fun id => individuals.find? (fun i => i.performance.id == id)
    individualStandalone := fun _ => some true
    collectionFactsConfirmed := fun id => if id == 83 then some true else none
    collectionRows := [({ id := 83, site := urineDaySite, specimen := some 82,
                          item := { item := .lumbarPuncture } }, 82)] }

example :
    (sevenCategoryDay.prepare (some [20, 33, 70])).map (fun (day, _) =>
      SpecimenJudgment.allCategories.filter day.judgment.day.hasTest) =
    some SpecimenJudgment.allCategories := by decide

example :
    (sevenCategoryDay.withoutAdditions (some [20, 33, 70])).map
      (fun r => (r.execution, r.judgment, r.collection, r.total.specimenWithCollection)) =
    some ([93, 26, 7, 25, 600, 290, 105, 180, 2520, 377], 841, [40, 312], 5416) := by decide

example : (sevenCategoryDay.withoutAdditions none).isNone := by decide

example : ({ sevenCategoryDay with individualStandalone := fun _ => none }.withoutAdditions
    (some [20, 33, 70])).isNone := by decide

example :
    let rows := sevenCategoryDay.collectionRows.map (fun pair => (pair.1, 999))
    ({ sevenCategoryDay with collectionRows := rows }.withoutAdditions (some [20, 33, 70])).isNone :=
  by decide

example :
    let panel : D006Targeted.LungPanel.Context :=
      { performance := { id := 1, site, item := () } }
    let counterpart : Performance D006Targeted.LungPanel.Counterpart :=
      { id := 2, site, item := .tissue .drugAid .egfr .realTimePCR }
    let day := { base with
      rows := [{ panel.performance with item := .individual lungPanelTest },
        { counterpart with item := .tumorTissue .drugAid }]
      lungPanelTogether := [(panel, [counterpart])] }
    (day.groups.map (List.map ChoiceGroup.members),
      (day.prepare none).isNone) = (some [[1, 2]], true) := by decide

private def rapidOnMixedDay : Input :=
  let designated := [30, 31, 32]
  { sevenCategoryDay with
    additions := { sevenCategoryDay.additions with selection := .rapid }
    rapidDesignation := fun id => some (if designated.contains id then some id else none)
    rapid := fun id => if designated.contains id then some ⟨id, true, true, true, true, true⟩
      else none }

example :
    (rapidOnMixedDay.prepare (some [20, 33, 70])).map
      (fun (day, _) => 10 * (day.additions.rapidCandidates []).length) = some 30 := by decide

example : ({ rapidOnMixedDay with rapidDesignation := fun _ => none }.prepare
    (some [20, 33, 70])).isNone := by decide

private def emergencyOnMixedDay : Input :=
  { sevenCategoryDay with
    additions := { sevenCategoryDay.additions with selection := .emergency }
    emergency := fun id => if id == 31 || id == 82 then some ⟨true, true, true, true, true, true⟩
      else none }

example :
    (emergencyOnMixedDay.prepare (some [20, 33, 70])).map
      (fun (day, _) => day.additions.emergencyTests.length) = some 2 := by decide

example : (mixedRawDay.withoutAdditions none).isNone := by decide

example : ({ mixedRawDay with collections :=
      [{ item := .venousBlood }, { item := .otherBlood }] }.withoutAdditions (some [20, 33, 70])).isNone :=
  by decide

example :
    let inpatient := { urineAndStool with judgment := { urineAndStool.judgment with status := .inpatient } }
    (inpatient.withoutAdditions none).isNone := by decide

example :
    (multiDivision.prepare (some [1, 20, 33])).map (fun (day, _) =>
      SpecimenJudgment.allCategories.filter day.judgment.day.hasTest) =
    some [.hematological, .biochemicalI, .immunological] := by decide

example : total { multiDivision with judgment := { multiDivision.judgment with day :=
    { multiDivision.judgment.day with performances := ⟨{ site.monthScope with patient := 4 }, []⟩ } } }
    (some [1, 20, 33]) = none := by decide

example : total { multiDivision with judgment := { multiDivision.judgment with day :=
    { multiDivision.judgment.day with claims := ⟨⟨{ site.monthScope with patient := 4 }, []⟩, by simp⟩ } } }
    (some [1, 20, 33]) = none := by decide

example : total { multiDivision with rows := multiDivision.rows.map fun p =>
    if p.id == 30 then { p with draw := none } else p } (some [1, 20, 33]) = none := by decide

example : total multiDivision none = none := by decide

example : total { multiDivision with rows := multiDivision.rows ++
    [{ id := 99, site, item := .other ("D015", "specificIge") }] } (some [1, 20, 33]) =
    none := by decide

example :
    let rows : List (Performance Item) := (List.range 14).map fun i =>
      { id := i, site, item := .specificIge (some i), draw := some 1 }
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [1430] := by decide

example :
    let row : Performance Item := { id := 1, site, item := .specificIge none, draw := some 1 }
    total { base with rows := [row] } none = none := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .endocrine .fsh, draw := some 1 },
       { id := 2, site, item := .endocrine .lh, draw := some 1 },
       { id := 3, site, item := .endocrine .cortisol, draw := some 1 },
       { id := 4, site, item := .tumorMarker ⟨3, 0⟩, draw := some 1 },
       { id := 5, site, item := .tumorMarker ⟨4, 0⟩, draw := some 1 }]
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [410, 230] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .viralTiter .rubella, specimen := some 1 },
       { id := 2, site, item := .viralTiter .rubella, specimen := some 1 },
       { id := 3, site, item := .viralTiter .measles, specimen := some 1 }]
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [158] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .classTiter .rubella .igm, specimen := some 1 },
       { id := 2, site, item := .classTiter .measles .igg, specimen := some 1 },
       { id := 3, site, item := .classTiter .mumps .igg, specimen := some 1 }]
    (({ base with rows } : Input).withoutAdditions none).map Breakdown.execution =
      some [400] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .autoantibody .rnpQuant },
       { id := 2, site, item := .autoantibody .smQuant },
       { id := 3, site, item := .autoantibody .ssbQuant }]
    (({ base with rows, autoantibodyDayConfirmed := true } : Input).withoutAdditions none).map
      Breakdown.execution = some [490] ∧
    total { base with rows } none = none := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .alpPag, draw := some 1 },
       { id := 2, site, item := .endocrine .bap, draw := some 1 }]
    let c := { base with rows, alpPaired := some true }
    c.groups.map (List.map ChoiceGroup.members) = some [[1, 2]] ∧
      (c.withoutAdditions (some [1])).map Breakdown.execution = some [180] ∧
      (c.withoutAdditions (some [2])).map Breakdown.execution = some [D008.Item.bap.points] ∧
      total { c with alpPaired := none } (some [1]) = none := by decide

example : raw429.Scope none := by
  refine ⟨?_, _, _, _, rfl, rfl, ?_⟩
  · exact fun _ membership => List.all_eq_true.mp (by decide :
      raw429.rows.all (fun p => p.item.supported) = true) _ membership
  · refine ⟨rfl, ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · unfold SpecimenJudgment.DailyJudgment.Known
      decide
    · intro f h
      cases h
    · intro e h
      cases h
    · intro e h
      cases h
    · intro h
      cases h
    · intro h
      cases h

end

end Sanri.MedicalFee.SpecimenRawDay
