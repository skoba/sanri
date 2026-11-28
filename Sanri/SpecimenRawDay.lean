import Sanri.SpecimenSelectionGeneration
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
  | ketone (item : BloodChemistryFurther.Item)
  | coagulation (item : D006.Item)
  | endocrine (item : D008.Item)
  | geneticDisease (disease : Nat)
  | alpPag
  | tumorMarker (item : D009.Item)
  /-- D011の項3に該当すると確認したRh因子。 -/
  | rhFactor (factor : Nat)
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
      .uibcColorimetric, .tibcColorimetric, .hdlCholesterol, .ldlCholesterol,
      .totalCholesterol, .proteinFractionation].contains i
  | .ketone i => [.ketoneBodies, .ketoneFractions].contains i
  | .coagulation i => [D006.Item.antithrombinActivity, .pic, .dDimer,
      .tat, .prothrombinFragment].contains i
  | .endocrine i => [D008.Item.fsh, .lh, .cortisol, .bap].contains i
  | .alpPag | .geneticDisease _ => true
  | .tumorMarker i => [4, 5, 13].contains i.number && i.variant == 0
  | .rhFactor _ => true
  | .hepatitis i => [D013.Item.hbeAntigen, .hbeAntibody, .hcvAntibody,
      .hbcAntibody, .hbcIgM, .haAntibody, .haIgM].contains i
  | .specificIge _ => true
  | .viralTiter t => [D012.Target.rubella, .measles, .mumps, .cytomegalovirus].contains t
  | .classTiter t a =>
    [D012.Target.rubella, .measles, .mumps, .cytomegalovirus].contains t &&
      [D012.AntibodyClass.igg, .igm].contains a
  | .autoantibody i => [D014.Item.rnpQuant, .smQuant, .ssbQuant].contains i
  | .individual _ => true
  | .other _ => false

/-- D007の併測について試す単位。条項ごとに指定する。 -/
inductive CotestReading where
  | simultaneous | specimen | day
  deriving DecidableEq

def CotestReading.matches (reading : CotestReading) (a b : Performance α) : Option Bool :=
  match reading with
  | .simultaneous => a.simultaneousWith b
  | .specimen => a.sameSpecimen b
  | .day => some (a.site == b.site)

theorem cotest_reading_agrees (a b : Performance α)
    (simultaneous : a.simultaneousWith b = some true)
    (specimen : a.sameSpecimen b = some true) (day : (a.site == b.site) = true)
    (reading : CotestReading) : reading.matches a b = some true := by
  cases reading <;> simp [CotestReading.matches, simultaneous, specimen, day]

theorem cotest_reading_members (anchor : Performance α) (rows : List (Performance α))
    (simultaneous : ∀ row ∈ rows, anchor.simultaneousWith row = some true)
    (specimen : ∀ row ∈ rows, anchor.sameSpecimen row = some true)
    (day : ∀ row ∈ rows, (anchor.site == row.site) = true) (reading : CotestReading) :
    rows.filterM (reading.matches anchor) = some rows := by
  have all : ∀ row ∈ rows, reading.matches anchor row = some true :=
    fun row member => cotest_reading_agrees anchor row
      (simultaneous row member) (specimen row member) (day row member) reading
  have loop (xs acc : List (Performance α))
      (matched : ∀ row ∈ xs, reading.matches anchor row = some true) :
      List.filterAuxM (reading.matches anchor) xs acc = some (xs.reverse ++ acc) := by
    induction xs generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      have hx := matched x (by simp)
      have step := ih (x :: acc) (fun y hy => matched y (by simp [hy]))
      simp [List.filterAuxM, hx, step, List.reverse_cons, List.append_assoc]
  simp [List.filterM, loop rows [] all]

inductive HepatitisCountReading where
  | performed | retained

/-- 方法をまとめる一連の条項。同じ一連でもD016は項ごとに別とする。 -/
private def seriesRule (test : SpecimenJudgment.Test) : Option (BundleRoute × SourceRef) :=
  if test.major == 16 && test.suffix == 0 && [2, 4, 5].contains test.number then
    some (⟨16, test.number, .series⟩, D016.seriesRule.source)
  else if test.major == 17 && test.suffix == 0 then
    some (⟨17, 0, .series⟩, D017.oneExamination.source)
  else if test == D021.judgmentTest then
    some (⟨21, 0, .series⟩, D021.indication.source)
  else none

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
  cholesterolReading : Option CotestReading := none
  proteinReading : Option CotestReading := none
  ketoneReading : Option CotestReading := none
  /-- D013注の項目数と単価合計に、併施選択で除外した実施を含めるか。 -/
  hepatitisCountReading : Option HepatitisCountReading := none
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
  /-- 疾患分類と検査法を原実施に対応付け、採取単位の主検査を指定する。 -/
  geneticExamination : (p : Performance Nat) →
    Option { e : D006Genetic.Examination // e.performance = p } := fun _ => none
  geneticPrincipal : Nat → Option Nat := fun _ => none
  geneticContext : Nat → Option D006Genetic.Context := fun _ => none
  geneticEligible : (ctx : D006Genetic.Context) →
    Option (PLift (D006Genetic.Eligible ctx)) := fun _ => none
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
  /-- 対象外群の確認。空リストは非発動。発動した各群には当日実施の範囲と採用IDを渡す。 -/
  outsideSelection : String → Option (List (List Nat × List Nat)) := fun _ => none
  /-- 照合済みの当月・当日以前の実施。日次の点数には加えない。 -/
  outsideMonthRows : List SpecimenSelectionGeneration.Row := []
  /-- 単位が未確定の併施群の読み。条項が同時・同一検体を指定する場合はその指定を使う。 -/
  selectionReading : String → Option CotestReading := fun _ => none
  /-- 医学的条件の確認。実施IDを昇順に揃えた群ごとに与える。 -/
  selectionCondition : String → List Nat → Option Bool := fun _ _ => none
  /-- 追加登録した群の共通採否。適用群の実施では未確認を許さない。 -/
  selectionKeep : Nat → Option Bool := fun _ => none
  /-- 一連の院内履歴を確認し、原実施群から今回算定候補を選べることを確認する。 -/
  seriesConfirmed : BundleKey → Bool := fun _ => false
  /-- D019項1〜3の一検査で感受性を調べた菌種の確認済み識別子。 -/
  susceptibilitySpecies : Nat → Option (List Nat) := fun _ => none
  /-- D020の当日の採取群ID。読みは採取群ごとに指定する。 -/
  mycobacterialGroup : Nat → Option Nat := fun _ => none
  mycobacterialReading : Nat → Option D020.CollectionReading := fun _ => none
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
private def CotestReading.generationReading : CotestReading → SpecimenSelectionGeneration.Reading
  | .simultaneous => .simultaneous
  | .specimen => .specimen
  | .day => .day

private def generateGroups (clause : String) (rows : List (Performance α)) (key : α → String)
    (division : String) (reading : Option CotestReading := none) :
    Option (List SpecimenSelectionGeneration.Instance) := do
  let entry ← SpecimenSelectionInventory.inventory.find? (·.id == clause)
  let indexed := rows.map fun row => { row with item := (division, key row.item) }
  (SpecimenSelectionGeneration.generate entry indexed
    (fun _ => reading.map CotestReading.generationReading)).toOption

private def groupProjection (generated : SpecimenSelectionGeneration.Instance)
    (existing : ChoiceGroup) : Option ChoiceGroup :=
  let ids := generated.members.map Performance.id
  if generated.limit == existing.count && ids.isPerm existing.members then
    some { existing with members := ids }
  else none

private theorem group_projection_spec
    {generated : SpecimenSelectionGeneration.Instance} {existing projected : ChoiceGroup}
    (h : groupProjection generated existing = some projected) :
    projected.source = existing.source ∧ projected.count = generated.limit ∧
      projected.members = generated.members.map Performance.id ∧
      projected.members.Perm existing.members := by
  unfold groupProjection at h
  dsimp only at h
  split at h
  · rename_i agreed
    simp only [Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] at agreed
    obtain rfl := Option.some.inj h.symm
    exact ⟨rfl, agreed.1.symm, rfl, agreed.2⟩
  · contradiction

def renalKey : UrineFecalTests.UrineSpecial → String
  | .albuminQuantitative => "albuminQuantitative"
  | .transferrin => "transferrin"
  | .typeIVCollagen => "typeIVCollagen"
  | _ => ""

private def Input.renalGroups (c : Input) : Option (List ChoiceGroup) := do
  let rows := c.specialUrine.filter (D001.renalItem ∘ Performance.item)
  if rows.length < 2 then return []
  let groups ← generateGroups D001.renalRule.id rows renalKey "D001"
  groups.mapM fun group => do
    let typed ← group.members.mapM fun p => rows.find? (·.id == p.id)
    let anchor :: _ := typed | none
    if (typed.map Performance.item).eraseDups.length != typed.length then none else
      let [existing] ← renalSimultaneousGroup { performance := anchor } typed | none
      groupProjection group existing

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

def chemistryKey : BloodChemistry.Item → String
  | .calcium => "calcium"
  | .ionizedCalcium => "ionizedCalcium"
  | .uibcColorimetric => "uibcColorimetric"
  | .tibcColorimetric => "tibcColorimetric"
  | .hdlCholesterol => "hdlCholesterol"
  | .ldlCholesterol => "ldlCholesterol"
  | .totalCholesterol => "totalCholesterol"
  | .proteinFractionation => "proteinFractionation"
  | .totalProtein => "totalProtein"
  | .albumin => "albumin"
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

private def Input.chemistryGroups (c : Input) (reading : Option CotestReading)
    (kind : ChemistryCombination) (clause : String) (keys : List BloodChemistry.Item) :
    Option (List ChoiceGroup) := do
  let rows := c.chemistry.filter (fun p => keys.contains p.item)
  if !keys.all (fun item => rows.any (·.item == item)) then return []
  let generated ← generateGroups clause rows chemistryKey "D007" reading
  generated.mapM fun group => do
    let typed ← group.members.mapM fun p => rows.find? (·.id == p.id)
    let existing ← match kind with
      | .calcium | .ironBinding => chemistryCombinationGroup kind typed
      | .cholesterol | .protein => chemistryCombinationProjection kind typed
    groupProjection group existing

def hepatitisKey : D013.Item → String
  | .hbcAntibody => "hbcAntibody"
  | .hbcIgM => "hbcIgM"
  | .haAntibody => "haAntibody"
  | .haIgM => "haIgM"
  | .hbeAntigen => "hbeAntigen"
  | .hbcrAntigen => "hbcrAntigen"
  | _ => ""

private def Input.hepatitisGroups (c : Input) (kind : HepatitisCombination)
    (clause : String) (first second : D013.Item) : Option (List ChoiceGroup) := do
  let rows : List (Performance D013.Item) := c.rows.filterMap fun p =>
    match p.item with
    | .hepatitis i => if i == first || i == second then some { p with item := i } else none
    | _ => none
  if !([first, second].all fun i => rows.any (·.item == i)) then return []
  let generated ← generateGroups clause rows hepatitisKey "D013"
  generated.mapM fun group => do
    let typed ← group.members.mapM fun p => rows.find? (·.id == p.id)
    let anchor :: _ := typed | none
    -- 採血による包括の射影は同じ採血内に限定する。
    if !typed.all (fun row => anchor.sameDraw row == some true) then none else
      let existing ← hepatitisGroup kind anchor typed
      groupProjection group existing

def coagulationKey : D006.Item → String
  | .fibrinMonomer => "fibrinMonomer"
  | .prothrombinFragment => "prothrombinFragment"
  | .tat => "tat"
  | _ => ""

private def Input.coagulationGroups (c : Input) : Option (List ChoiceGroup) := do
  let rows := c.coagulation.filter (fun row => D006.competingMarkers.contains row.item)
  if !((rows.map Performance.item).eraseDups.length == rows.length) then none else
  if rows.length < 2 then return []
  let generated ← generateGroups D006.markerCombinationRule.id rows coagulationKey "D006"
  generated.mapM fun group => do
    let typed ← group.members.mapM fun p => rows.find? (·.id == p.id)
    let existing ← coagulationMarkerGroup typed
    groupProjection group existing

private def Input.seriesGroups (c : Input) : Option (List ChoiceGroup) := do
  let keyed ← (c.rows.filterMap fun row => match row.item with
    | .individual test => (seriesRule test).map fun (route, source) => (row, route, source)
    | _ => none).mapM fun (row, route, source) => do
      let key ← bundleKey route row
      return (key, source, row.id)
  let keys := (keyed.map Prod.fst).eraseDups
  let groups ← keys.mapM fun key => do
    if !c.seriesConfirmed key then none else
      let rows := keyed.filter (·.1 == key)
      let (_, source, _) :: _ := rows | none
      let ids := rows.map (·.2.2)
      if ids.length < 2 then return []
      return [⟨source, ids, 1⟩]
  return groups.flatten

private def mycobacterialTest (test : SpecimenJudgment.Test) : Bool :=
  test.major == 20 && test.suffix == 0

private def Input.mycobacterialGroups (c : Input) : Option (List ChoiceGroup) := do
  let rows := c.rows.filter fun row => match row.item with
    | .individual test => mycobacterialTest test
    | _ => false
  let keys ← rows.mapM (c.mycobacterialGroup ∘ Performance.id)
  return keys.eraseDups.filterMap fun key =>
    let ids := ((rows.zip keys).filter fun (_, k) => k == key).map (·.1.id)
    if ids.length < 2 then none else some ⟨D020.collectionLimit.source, ids, 1⟩

def Input.groups (c : Input) : Option (List ChoiceGroup) := do
  let morphology ← (pairs c.morphology).mapM fun (left, right) => do
    let a : Performance BloodMorphology.Item := { left with item := left.item.item }
    let b : Performance BloodMorphology.Item := { right with item := right.item.item }
    let existing ← morphologyGroups a b false
    existing.mapM (indexedPair BloodMorphology.eosinophilRule.id a b morphologyKey "D005")
  if !(overlappingGroups morphology.flatten).isEmpty then none else
    let calcium ← c.chemistryGroups none .calcium
      BloodChemistry.calciumRule.id BloodChemistry.calciumGroup
    let iron ← c.chemistryGroups none .ironBinding
      BloodChemistry.ironBindingRule.id BloodChemistry.ironBindingGroup
    let coagulation ← c.coagulationGroups
    let alp ← c.alpGroups
    let sediment ← c.sedimentGroups
    let renal ← c.renalGroups
    let lungPanel ← c.lungPanelGroups
    let cholesterol ← c.chemistryGroups c.cholesterolReading .cholesterol
      BloodChemistry.cholesterolRule.id BloodChemistry.cholesterolGroup
    let protein ← c.chemistryGroups c.proteinReading .protein
      BloodChemistry.proteinRule.id BloodChemistry.proteinGroup
    let hbCore ← c.hepatitisGroups .hbCore D013.hbCoreChoice.id .hbcAntibody .hbcIgM
    let ha ← c.hepatitisGroups .ha D013.haChoice.id .haAntibody .haIgM
    let series ← c.seriesGroups
    let mycobacterial ← c.mycobacterialGroups
    return morphology.flatten ++ calcium ++ iron ++ coagulation ++ alp ++ sediment ++ renal ++
      lungPanel ++ cholesterol ++ protein ++ hbCore ++ ha ++ series ++ mycobacterial

/-- 指定した採否が全群に共通し、各群の必要件数を満たす場合にだけ射影する。 -/
def resolveChoices (groups : List ChoiceGroup) (selected : Option (List Nat)) :
    Option (List GroupChoice) := do
  if groups.isEmpty then
    if selected.getD [] == [] then some [] else none
  else
    let ids ← selected
    let memberIds := (groups.flatMap ChoiceGroup.members).eraseDups
    if !((memberIds.filter ids.contains).isPerm ids) ||
        !groups.all (fun g => g.members.eraseDups == g.members &&
          (g.members.filter ids.contains).length == g.count) then none else
      return groups.map fun g => ⟨g, g.members.filter ids.contains⟩

private theorem resolveChoices_perm (groups : List ChoiceGroup) {ids other : List Nat}
    (perm : ids.Perm other) :
    resolveChoices groups (some ids) = resolveChoices groups (some other) := by
  have contains (id : Nat) : ids.contains id = other.contains id := by
    apply Bool.eq_iff_iff.mpr
    simpa only [List.contains_iff_mem] using perm.mem_iff (a := id)
  have test (xs : List Nat) : xs.isPerm ids = xs.isPerm other := by
    apply Bool.eq_iff_iff.mpr
    rw [List.isPerm_iff, List.isPerm_iff]
    exact ⟨(·.trans perm), (·.trans perm.symm)⟩
  have empty : (ids == []) = (other == []) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor <;> intro h
    · subst ids
      exact perm.nil_eq.symm
    · subst other
      exact perm.symm.nil_eq.symm
  have filters : ids.contains = other.contains := funext contains
  simp only [resolveChoices, Option.getD_some, bind, Option.bind, test, empty, filters]

private theorem resolveChoices_canonical (groups : List ChoiceGroup) (selected : Option (List Nat))
    {choices : List GroupChoice} (ok : resolveChoices groups selected = some choices) :
    ∃ candidate ∈ (none :: (consistentSelections groups [] []).map some),
      resolveChoices groups candidate = some choices := by
  unfold resolveChoices at ok
  split at ok
  · split at ok
    · refine ⟨none, by simp, ?_⟩
      simpa [resolveChoices, ‹groups.isEmpty = true›] using ok
    · simp at ok
  · cases selected with
    | none => simp at ok
    | some ids =>
      simp only [bind, Option.bind] at ok
      split at ok
      · simp at ok
      · rename_i valid
        have conditions := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr valid)
        have unneg (b : Bool) : (!b) = false → b = true := by cases b <;> simp
        have perm := List.isPerm_iff.mp (unneg _ conditions.1)
        have counts := unneg _ conditions.2
        let canon := (groups.flatMap ChoiceGroup.members).eraseDups.filter ids.contains
        have mem : canon ∈ consistentSelections groups [] [] := by
          simpa [canon] using consistentSelections_contains groups [] [] ids.contains rfl rfl counts
        have old : resolveChoices groups (some ids) = some choices := by
          simp only [resolveChoices, ‹¬groups.isEmpty = true›, bind, Option.bind, valid]
          exact ok
        exact ⟨some canon, by simp [mem], (resolveChoices_perm groups perm).trans old⟩

theorem resolveChoices_agree (groups : List ChoiceGroup) (selected : Option (List Nat))
    (choices : List GroupChoice) (resolved : resolveChoices groups selected = some choices) :
    Agree choices := by
  unfold resolveChoices at resolved
  split at resolved
  · split at resolved
    · have eq : choices = [] := by simpa [eq_comm] using resolved
      simp [eq, Agree]
    · simp at resolved
  · cases selected with
    | none => simp at resolved
    | some ids =>
      simp only [bind, Option.bind] at resolved
      split at resolved
      · simp at resolved
      · have eq := Option.some.inj resolved
        subst choices
        intro a ha b hb id ia ib
        obtain ⟨ga, _, rfl⟩ := List.mem_map.mp ha
        obtain ⟨gb, _, rfl⟩ := List.mem_map.mp hb
        simp [ia, ib]

theorem resolveChoices_realizes (groups : List ChoiceGroup) (selected : Option (List Nat))
    (choices : List GroupChoice) (resolved : resolveChoices groups selected = some choices) :
    Realizes choices (fun id => retained choices id = true) :=
  retained_iff _ (resolveChoices_agree groups selected choices resolved)

private def Input.ketones (c : Input) : List (Performance BloodChemistryFurther.Item) :=
  c.rows.filterMap fun p => match p.item with
    | .ketone item => some { p with item := item }
    | _ => none

def ketoneKey : BloodChemistryFurther.Item → String
  | .ketoneBodies => "ketoneBodies"
  | .ketoneFractions => "ketoneFractions"
  | .bicarbonate => "bicarbonate"
  | .bloodGas => "bloodGas"
  | .bileAcids => "bileAcids"
  | .urinarySulfatedBileAcids => "urinarySulfatedBileAcids"
  | _ => ""

/-- 型付き項目の集合を、登録索引と照合するための射影。 -/
def checkedSelectionKeys : List (String × List SpecimenSelectionInventory.ItemKey) :=
  let keyed {α : Type} (division : String) (key : α → String) (items : List α) :=
    items.map fun i => (division, key i)
  let chemistry := keyed "D007" chemistryKey
  let further := keyed "D007" ketoneKey
  let hepatitis := keyed "D013" hepatitisKey
  [(D001.renalRule.id, keyed "D001" renalKey
      [.albuminQuantitative, .transferrin, .typeIVCollagen]),
   (D006.markerCombinationRule.id, keyed "D006" coagulationKey D006.competingMarkers),
   (BloodChemistry.calciumRule.id, chemistry BloodChemistry.calciumGroup),
   (BloodChemistry.ironBindingRule.id, chemistry BloodChemistry.ironBindingGroup),
   (BloodChemistry.cholesterolRule.id, chemistry BloodChemistry.cholesterolGroup),
   (BloodChemistry.proteinRule.id, chemistry BloodChemistry.proteinGroup),
   ((BloodChemistryFurther.Pair.ketones.rule).id, further [.ketoneBodies, .ketoneFractions]),
   ((BloodChemistryFurther.Pair.bicarbonateAndBloodGas.rule).id, further [.bicarbonate, .bloodGas]),
   ((BloodChemistryFurther.Pair.bileAcids.rule).id, further [.bileAcids, .urinarySulfatedBileAcids]),
   (D013.hbCoreChoice.id, hepatitis [.hbcAntibody, .hbcIgM]),
   (D013.haChoice.id, hepatitis [.haAntibody, .haIgM])]

/-- 新規の日次群の構成を、区分別の項目型から照合する。 -/
def registeredSelectionKeys : List (String × List SpecimenSelectionInventory.ItemKey) :=
  let urine (items : List UrineFecalTests.UrineSpecial) :=
    items.filterMap fun i => (Individual.urineSelectionKey i).map ("D001", ·)
  let infection (items : List D012.Item) :=
    items.filterMap fun i => (Individual.infectionKey i).map ("D012", ·)
  let antibody (items : List D014.Item) :=
    items.filterMap fun i => (Individual.autoantibodySelectionKey i).map ("D014", ·)
  let puncture (items : List D004.Item) :=
    items.filterMap fun i => (Individual.punctureSelectionKey i).map ("D004", ·)
  let endocrine (items : List D008.Item) :=
    items.filterMap fun i => (Individual.endocrineSelectionKey i).map ("D008", ·)
  let marker (items : List D009.Item) :=
    items.filterMap fun i => (Individual.markerSelectionKey i).map ("D009", ·)
  [("notice/D001/paragraph/9/i", urine [.lFabp, .ngal]),
   ("notice/D012/paragraph/2",
     infection [.mycoplasmaQual, .mycoplasmaSemi, .mycoplasmaChromatography, .mycoplasmaFluorescence]),
   ("notice/D012/paragraph/31/i", infection [.pneumococcusCapsule, .pneumococcusWall]),
   ("notice/D012/paragraph/48/e", infection [.dengueAntigen, .dengueCombo]),
   ("notice/D014/paragraph/3", antibody [.microsomal, .tpo]),
   ("notice/D014/paragraph/8", antibody [.trab, .tsab]),
   ("notice/D014/paragraph/16/i", antibody [.dsg1, .dsg3]),
   ("notice/D014/paragraph/19/i", antibody [.dsg1, .dsg3]),
   ("notice/D014/paragraph/24/i", antibody [.achr, .musk]),
   ("notice/D014/paragraph/27/i", antibody [.achr, .musk]),
   ("notice/D004/paragraph/13/i", puncture [.amyloidRatio, .phosphoTau, .phosphoTauAmyloidRatio]),
   ("notice/D008/paragraph/3", endocrine [.reninActivity, .reninQuantitative]),
   ("notice/D008/paragraph/25", endocrine [.metanephrine, .normetanephrine]),
   ("notice/D008/paragraph/26/i", endocrine [.igfbp3, .somatomedinC]),
   ("notice/D008/paragraph/27/i", endocrine [.freeMetanephrineFractions, .metanephrine, .metanephrineFractions, .normetanephrine]),
   ("notice/D009/paragraph/3", marker [⟨2, 0⟩, ⟨6, 0⟩]),
   ("notice/D009/paragraph/5", marker [⟨10, 0⟩, ⟨27, 0⟩]),
   ("notice/D009/paragraph/8", marker [⟨11, 0⟩, ⟨20, 0⟩]),
   ("notice/D009/paragraph/10/i", marker [⟨17, 0⟩, ⟨5, 1⟩]),
   ("notice/D009/paragraph/15", marker [⟨13, 0⟩, ⟨23, 0⟩]),
   ("notice/D009/paragraph/20/u", marker [⟨30, 0⟩, ⟨8, 0⟩, ⟨16, 1⟩, ⟨31, 0⟩]),
   ("notice/D009/paragraph/21/e", marker [⟨16, 1⟩, ⟨31, 0⟩]),
   ("notice/D009/paragraph/21/u", marker [⟨8, 0⟩, ⟨31, 0⟩]),
   ("notice/D009/paragraph/24/i", marker [⟨14, 0⟩, ⟨2, 0⟩, ⟨6, 0⟩, ⟨34, 0⟩]),
   ("notice/D013/paragraph/8", [("D013", (Individual.hepatitisSelectionKey .hbcrAntigen).getD ""),
     ("D023", Individual.hbvQuantitySelectionKey)]),
   ("notice/D015/paragraph/4/i",
     ([.wholeAntiserum, .specificAntiserum, .drugImmunofixation] : List D015.Item).filterMap
       fun i => (Individual.proteinSelectionKey i).map ("D015", ·))]

private def namedKey (division item : String) : Option SpecimenSelectionInventory.ItemKey :=
  if item == "" then none else some (division, item)

/-- 区分別評価の識別を使い、明示した項目だけを照合索引へ射影する。 -/
def Input.selectionRows (c : Input) : List SpecimenSelectionGeneration.Row :=
  c.rows.filterMap fun row => do
    let key ← match row.item with
      | .specialUrine i => namedKey "D001" (renalKey i)
      | .sediment .microscopy => some ("D002", "microscopy")
      | .sediment .flow => some ("D002-2", "flow")
      | .punctureFluid .jointFluid => some ("D004", "jointFluid")
      | .punctureFluid i => (Individual.punctureSelectionKey i).map ("D004", ·)
      | .morphology ctx => namedKey "D005" (morphologyKey ctx.item)
      | .coagulation i => namedKey "D006" (coagulationKey i)
      | .chemistry i => namedKey "D007" (chemistryKey i)
      | .ketone i => namedKey "D007" (ketoneKey i)
      | .endocrine i => (Individual.endocrineSelectionKey i).map ("D008", ·)
      | .tumorMarker i => (Individual.markerSelectionKey i).map ("D009", ·)
      | .hepatitis i => namedKey "D013" (hepatitisKey i)
      | .autoantibody i => (Individual.autoantibodySelectionKey i).map ("D014", ·)
      | .individual test => do
        let assessed ← c.individualFacts row.id
        if assessed.performance == { row with item := test } then assessed.selectionKey else none
      | .other key => some key
      | _ => none
    return { row with item := key }

private def overlapClauses : List String :=
  ["notice/D004/paragraph/1", "primary/D017/note/unnumbered/1",
   "notice/D007/paragraph/47", "notice/D007/paragraph/48/i", "notice/D012/paragraph/12",
   "notice/D012/paragraph/28", "notice/D012/paragraph/30", "notice/D012/paragraph/32",
   "notice/D018/paragraph/1/e", "notice/D018/paragraph/1/u",
   "notice/D023/paragraph/1/a", "notice/D023/paragraph/2/a", "notice/D023/paragraph/3",
   "notice/D023/paragraph/5/a"]

/-- 既知の構成項目から三つの重複成分の確認候補を拾う。
日次評価での確認と保留は `requiredOutside` と `outsideChoices` が担う。 -/
def Input.pendingOverlap (c : Input) : List String :=
  let rows := c.selectionRows.filter fun row =>
    ["D002", "D002-2", "D004", "D012", "D017", "D018", "D023"].contains row.item.1 ||
      (row.item.1 == "D007" &&
        ["procalcitoninQuantitative", "procalcitoninSemiquantitative", "presepsin"].contains row.item.2)
  if rows.length < 2 then [] else
  (SpecimenSelectionInventory.inventory.filter fun entry =>
    overlapClauses.contains entry.id &&
      let matched := SpecimenSelectionGeneration.members entry rows
      if entry.id == "primary/D017/note/unnumbered/1" then
        matched.any (fun row => row.item.1 == "D017") &&
          matched.any (fun row => row.item.1 == "D002" || row.item.1 == "D002-2")
      else if entry.id == "notice/D018/paragraph/1/e" then matched.length ≥ 2
      else (matched.map Performance.item).eraseDups.length ≥ 2).map (·.id)

private def divisionName (major suffix : Nat) : String :=
  let lead := if major < 10 then "D00" else if major < 100 then "D0" else "D"
  lead ++ toString major ++ (if suffix == 0 then "" else "-" ++ toString suffix)

private def Item.division : Item → String
  | .urine _ => "D000"
  | .specialUrine _ => "D001"
  | .sediment .microscopy => "D002"
  | .sediment .flow => "D002-2"
  | .fecal _ => "D003"
  | .punctureFluid _ => "D004"
  | .tumorTissue _ => "D004-2"
  | .morphology _ => "D005"
  | .coagulation _ => "D006"
  | .geneticDisease _ => "D006-4"
  | .chemistry _ | .ketone _ | .alpPag => "D007"
  | .endocrine _ => "D008"
  | .tumorMarker _ => "D009"
  | .rhFactor _ => "D011"
  | .viralTiter _ | .classTiter _ _ => "D012"
  | .hepatitis _ => "D013"
  | .autoantibody _ => "D014"
  | .specificIge _ => "D015"
  | .individual test => divisionName test.major test.suffix
  | .other key => key.1

private def Item.outsideKey : Item → Option String
  | .specialUrine .protein => some "protein"
  | .specialUrine .trypsinogen2 => some "trypsinogen2"
  | .specialUrine .prostaglandinEMajorMetabolite => some "prostaglandinEMajorMetabolite"
  | .fecal .calprotectin => some "calprotectin"
  | .fecal .hemoglobin => some "hemoglobin"
  | .fecal .lipids => some "lipids"
  | .morphology c => match c.item with
    | .completeBloodCount => some "completeBloodCount"
    | _ => none
  | .chemistry i => match i with
    | .bun => some "bun"
    | .uricAcid => some "uricAcid"
    | .glucose => some "glucose"
    | .ast => some "ast"
    | .alt => some "alt"
    | .creatinine => some "creatinine"
    | .gammaGT => some "gammaGT"
    | _ => none
  | .endocrine i => match i with
    | .bap => some "bap"
    | .fsh => some "fsh"
    | .lh => some "lh"
    | .cortisol => some "cortisol"
    | _ => Individual.endocrineSelectionKey i
  | .punctureFluid .huhner => some "huhner"
  | .alpPag => some "alpIsoenzymesPag"
  | .tumorMarker i => Individual.markerSelectionKey i
  | .rhFactor _ => some "otherRh"
  | .specificIge _ => some "specificIge"
  | .viralTiter _ => some "viralTiter"
  | .classTiter _ _ => some "classSpecificTiter"
  | .autoantibody i => match i with
    | .rnpQuant => some "rnpQuant"
    | .smQuant => some "smQuant"
    | .ssbQuant => some "ssbQuant"
    | _ => Individual.autoantibodySelectionKey i
  | _ => none

private def collectionSelectionDivision : SpecimenCollection.Item → Option String
  | .ventricularPuncture => some "D401"
  | .suboccipitalPuncture => some "D402"
  | .lumbarPuncture | .thoracicPuncture | .cervicalPuncture => some "D403"
  | .sternalMarrowPuncture | .otherMarrowPuncture => some "D404"
  | .jointPuncture => some "D405"
  | .maxillarySinusPuncture => some "D406"
  | .peritonsillarTrialPuncture => some "D406-2"
  | .renalCystHydronephrosisPuncture => some "D407"
  | .douglasPuncture => some "D408"
  | .lymphNodeNeedleBiopsy => some "D409"
  | .breastBiopsyNeedle | .breastOther => some "D410"
  | .thyroidNeedleBiopsy => some "D411"
  | .gastricDuodenalFluid => some "D419"
  | _ => none

/-- 空の項目キーは区分だけ判明した実施として照合する。 -/
def Input.outsideRows (c : Input) : List SpecimenSelectionGeneration.Row :=
  let indexed := c.selectionRows
  (c.rows.map fun row =>
    (indexed.find? (·.id == row.id)).getD
      { row with item := (row.item.division, row.item.outsideKey.getD "") }) ++
  c.collectionRows.filterMap fun (row, _) =>
    (collectionSelectionDivision row.item.item).map fun division => { row with item := (division, "") }

private def outsideDivisions (g : SpecimenSelectionInventory.Entry) : List String :=
  if g.members.isEmpty then
    match g.id with
    | "notice/D003/paragraph/4/u" => ["D003", "D313"]
    | "notice/D004-2/paragraph/10" => ["D004-2", "N005"]
    | "primary/D006-4/note/2" => ["D006-4"]
    | "notice/D007/paragraph/38" => ["D007"]
    | "notice/D008/paragraph/4" => ["D008"]
    | "notice/D012/paragraph/38/i" => ["D012"]
    | "notice/D023/paragraph/16/u" => ["D023", "D419"]
    | "notice/D023/paragraph/39/i" => ["D023"]
    | "notice/D023-2/paragraph/1/i" => ["D023-2", "D023"]
    | "notice/ch2-part3-section4/general/3" =>
      ["D401", "D402", "D403", "D404", "D405", "D406", "D406-2", "D407", "D408",
       "D409", "D410", "D411"]
    | _ => []
  else g.members.map Prod.fst

example : (SpecimenSelectionInventory.inventory.filter (·.outsideReason.isSome)).all
    (fun g => !(outsideDivisions g).isEmpty) = true := by decide

private def outsideMatches (g : SpecimenSelectionInventory.Entry) (broad : Bool)
    (divisions : List String) (row : SpecimenSelectionGeneration.Row) : Bool :=
  if g.id == "notice/D007/paragraph/38" then
    row.item.1 == "D007" && (row.item.2 == "" || row.item.2 == "cardiacMyosinLightChainI")
  else if broad || row.item.2 == "" then divisions.contains row.item.1
  else g.members.contains row.item

private def possibleOutside (g : SpecimenSelectionInventory.Entry)
    (reason : SpecimenSelectionInventory.OutsideReason) (divisions : List String)
    (today prior : List SpecimenSelectionGeneration.Row) : List Nat :=
  let broad := g.members.isEmpty || reason == .key
  let matchesEntry := outsideMatches g broad divisions
  let today := today.filter matchesEntry
  let prior := prior.filter matchesEntry
  if g.id == "notice/D007/paragraph/38" then
    (today.filter fun row => row.item.2 == "" ||
      (today.filter (·.item == row.item)).length ≥ 2).map Performance.id
  else
    -- 日をまたぐ相手や検体検査外の相手は、当日の候補が一件でも確認を要する。
    let crossesDay := [SpecimenSelectionInventory.UnitKind.month, .series, .week].contains g.unit
    let minimum := if broad || reason == .shape || reason == .external || crossesDay ||
        (today ++ prior).any (·.item.2 == "") then 1
      else (g.cardinality.map Prod.fst).getD 1
    if today.length + prior.length ≥ minimum then today.map Performance.id else []

def Input.requiredOutside (c : Input) : List (SpecimenSelectionInventory.Entry × List Nat) :=
  let today := c.outsideRows
  let divisions := (today.map (·.item.1)).eraseDups
  let prior := (c.outsideMonthRows.filter fun row =>
    row.site.patient == c.site.patient && row.site.date.month == c.site.date.month &&
      decide (row.site.date.key < c.site.date.key)).eraseDups
  SpecimenSelectionInventory.inventory.filterMap fun g => do
    let relevant := outsideDivisions g
    if !divisions.any relevant.contains then none else
      let reason ← g.outsideReason
      let ids := possibleOutside g reason relevant today prior
      if ids.isEmpty then none else some (g, ids)

private def Input.outsideGroupChoices (c : Input)
    (requirement : SpecimenSelectionInventory.Entry × List Nat) : Option (List GroupChoice) := do
  let (g, candidates) := requirement
  let decisions ← c.outsideSelection g.id
  decisions.mapM fun (members, selected) =>
    if !members.isEmpty && members.eraseDups == members &&
        members.all candidates.contains && selected.eraseDups == selected &&
        selected.all members.contains then
      some ⟨⟨g.source, members, selected.length⟩, selected⟩
    else none

def Input.outsideChoices (c : Input) : Option (List GroupChoice) :=
  (c.requiredOutside.mapM c.outsideGroupChoices).map List.flatten

def Input.dayCollections (c : Input) : List SpecimenCollection.Context :=
  c.collections ++ (c.collectionRows.filter fun (p, _) =>
    retained (c.outsideChoices.getD []) p.id).map (·.1.item)

private theorem some_of_mem_mapM {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨first, hf, tail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hr, he⟩ := Option.bind_eq_some_iff.mp tail
    have eq : first :: rest = ys := Option.some.inj he
    subst ys
    rcases List.mem_cons.mp hx with eq | member
    · subst x
      exact ⟨first, by simp, hf⟩
    · obtain ⟨y, hy, hfy⟩ := ih hr member
      exact ⟨y, by simp [hy], hfy⟩

theorem outside_confirmed (c : Input) {choices : List GroupChoice}
    (checked : c.outsideChoices = some choices)
    {g : SpecimenSelectionInventory.Entry} {ids : List Nat}
    (required : (g, ids) ∈ c.requiredOutside) :
    ∃ decisions, c.outsideSelection g.id = some decisions := by
  obtain ⟨groups, hg, _⟩ := Option.map_eq_some_iff.mp checked
  obtain ⟨accepted, _, ok⟩ := some_of_mem_mapM hg required
  exact (Option.bind_eq_some_iff.mp ok).imp fun _ eq => eq.1

theorem outside_choice_included (c : Input) {choices : List GroupChoice}
    (checked : c.outsideChoices = some choices)
    {g : SpecimenSelectionInventory.Entry} {ids members selected : List Nat}
    (required : (g, ids) ∈ c.requiredOutside)
    {decisions : List (List Nat × List Nat)}
    (confirmed : c.outsideSelection g.id = some decisions)
    (active : (members, selected) ∈ decisions) :
    (⟨⟨g.source, members, selected.length⟩, selected⟩ : GroupChoice) ∈ choices := by
  obtain ⟨groups, hg, eq⟩ := Option.map_eq_some_iff.mp checked
  obtain ⟨accepted, inside, ok⟩ := some_of_mem_mapM hg required
  simp only [Input.outsideGroupChoices, confirmed] at ok
  obtain ⟨choice, included, projected⟩ := some_of_mem_mapM ok active
  split at projected
  · cases projected
    rw [← eq]
    exact List.mem_flatten.mpr ⟨accepted, inside, included⟩
  · contradiction

/-- 同じ実施についての二つの確認が食い違う日は保留する。 -/
private def agreeChoices (choices : List GroupChoice) : Option (List GroupChoice) :=
  if choices.all (fun g =>
      decide g.group.members.Nodup && decide g.selected.Nodup &&
        g.selected.length == g.group.count && g.selected.all g.group.members.contains &&
        g.group.members.all (fun id => retained choices id == g.selected.contains id))
  then some choices else none

private theorem agree_choices_spec {choices accepted : List GroupChoice}
    (h : agreeChoices choices = some accepted) :
    accepted = choices ∧
      Satisfies (accepted.map GroupChoice.rule) () (fun id => retained accepted id = true) := by
  unfold agreeChoices at h
  split at h
  · rename_i ok
    obtain rfl := Option.some.inj h
    refine ⟨rfl, ?_⟩
    intro rule member
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp member
    have checked := List.all_eq_true.mp ok g hg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at checked
    refine ⟨⟨checked.1.1.1.1,
      checked.1.1.1.2, checked.1.1.2,
      fun id hi => List.contains_iff_mem.mp (checked.1.2 id hi)⟩, ?_⟩
    intro id hi
    change retained choices id = true ↔ id ∈ g.selected
    rw [checked.2 id hi, List.contains_iff_mem]
  · contradiction

private def checkedRegisteredChoice (c : Input) (source : SourceRef)
    (group : SpecimenSelectionGeneration.Instance) : Option GroupChoice :=
  if group.checkSelection c.selectionKeep then
    let ids := group.members.map Performance.id
    let keep := ids.filter fun id => c.selectionKeep id == some true
    some ⟨⟨source, ids, keep.length⟩, keep⟩
  else none

private theorem registered_choice_sound (c : Input) (source : SourceRef)
    (group : SpecimenSelectionGeneration.Instance) (choice : GroupChoice)
    (checked : checkedRegisteredChoice c source group = some choice)
    (keep : Nat → Bool) (realizes : ∀ id ∈ choice.group.members, keep id = true ↔ id ∈ choice.selected) :
    group.Permits keep := by
  unfold checkedRegisteredChoice at checked
  split at checked
  · rename_i ok
    obtain rfl := Option.some.inj checked.symm
    have checkedKeep := SpecimenSelectionGeneration.checkSelection_sound group c.selectionKeep ok
    have agrees (row : SpecimenSelectionGeneration.Row) (member : row ∈ group.members) :
        keep row.id = (c.selectionKeep row.id == some true) := by
      have idMember : row.id ∈ group.members.map Performance.id :=
        List.mem_map.mpr ⟨row, member, rfl⟩
      have agrees := realizes row.id idMember
      simp only [List.mem_filter, idMember, true_and] at agrees
      exact Bool.eq_iff_iff.mpr agrees
    have filtered :
        group.members.filter (fun row => keep row.id) =
          group.members.filter (fun row => c.selectionKeep row.id == some true) :=
      List.filter_congr agrees
    cases h : group.direction with
    | principal =>
      simpa only [SpecimenSelectionGeneration.Instance.Permits, h, filtered] using checkedKeep
    | retain item =>
      simp only [SpecimenSelectionGeneration.Instance.Permits, h] at checkedKeep ⊢
      exact ⟨by rw [filtered]; exact checkedKeep.1,
        fun row member => (agrees row member).trans (checkedKeep.2 row member)⟩
  · contradiction

def Input.registrationRows (c : Input) : List SpecimenSelectionGeneration.Row :=
  let keys := registeredSelectionKeys.flatMap Prod.snd
  c.selectionRows.filter fun row => keys.contains row.item

def Input.generateRegistered (c : Input) (entry : SpecimenSelectionInventory.Entry) :=
  (SpecimenSelectionGeneration.generateRegistered entry c.registrationRows
    (fun id => (c.selectionReading id).map CotestReading.generationReading)
    c.selectionCondition).toOption

/-- 構成を照合した群を日次に渡す。適用条件と採否は未確認なら保留する。 -/
def Input.registeredChoices (c : Input) : Option (List GroupChoice) := do
  if (c.registrationRows.map Performance.item).eraseDups.length < 2 then return []
  let entries := SpecimenSelectionInventory.inventory.filter (·.dayRegistration.isSome)
  let groups ← entries.mapM fun entry => do
    let groups ← c.generateRegistered entry
    groups.mapM (checkedRegisteredChoice c entry.source)
  return groups.flatten

private theorem registered_choice_included (c : Input) {choices : List GroupChoice}
    (checked : c.registeredChoices = some choices)
    (enough : ¬ (c.registrationRows.map Performance.item).eraseDups.length < 2)
    {entry : SpecimenSelectionInventory.Entry}
    (registered : entry ∈ SpecimenSelectionInventory.inventory.filter (·.dayRegistration.isSome))
    {groups : List SpecimenSelectionGeneration.Instance}
    (generated : c.generateRegistered entry = some groups)
    {group : SpecimenSelectionGeneration.Instance} (member : group ∈ groups) :
    ∃ choice ∈ choices, checkedRegisteredChoice c entry.source group = some choice := by
  simp only [Input.registeredChoices, enough, ite_false] at checked
  obtain ⟨accepted, bound, eq⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨localChoices, inside, confirmed⟩ := some_of_mem_mapM bound registered
  simp only [generated] at confirmed
  obtain ⟨choice, included, projected⟩ := some_of_mem_mapM confirmed member
  rw [← Option.some.inj eq]
  exact ⟨choice, List.mem_flatten.mpr ⟨localChoices, inside, included⟩, projected⟩

private def Input.ketoneChoices (c : Input) : Option (List GroupChoice) := do
  let rows := c.ketones
  if ![.ketoneBodies, .ketoneFractions].all (fun item => rows.any (·.item == item)) then
    return []
  let groups ← generateGroups "notice/D007/paragraph/9" rows ketoneKey "D007" c.ketoneReading
  groups.mapM fun group => do
    let .retain retainedKey := group.direction | none
    let [first, second] := group.members | none
    let other ← rows.find? fun row =>
      (row.id == first.id || row.id == second.id) && ("D007", ketoneKey row.item) != retainedKey
    let retained ← rows.find? fun row =>
      (row.id == first.id || row.id == second.id) && ("D007", ketoneKey row.item) == retainedKey
    let existing ← chemistryPriorityGroup other retained
    let projected ← groupProjection group existing.group
    return ⟨projected, [retained.id]⟩

/-- 照合済みの共通採否とD007(9)が指定する採否を、既存の日次の選択に合流させる。 -/
def Input.directedChoices (c : Input) : Option (List GroupChoice) := do
  let registered ← c.registeredChoices
  let ketones ← c.ketoneChoices
  return registered ++ ketones

theorem ketone_priority_iff (choice : BloodChemistryFurther.Choice) :
    BloodChemistryFurther.Pair.ketones.rule.holds true choice ↔ choice = .second := by
  simp [BloodChemistryFurther.Pair.rule, BloodChemistryFurther.Pair.permits]

def Input.resolveDayChoices (c : Input) (selected : Option (List Nat)) :
    Option (List GroupChoice) := do
  let openGroups ← c.groups
  let directed ← c.directedChoices
  let free ← resolveChoices openGroups selected
  let outside ← c.outsideChoices
  agreeChoices (free ++ directed ++ outside)

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
    ironBinding := { together := some false }
    cholesterol := { together := some false }
    protein := { together := some false } }

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
    c.test p.id (D003.judgmentTest { performance := p, d017BacteriaOrProtozoa := none })
      (if retained choices p.id then some true else c.excludedJudgmentCandidate)) ++
  (c.punctureFluid.filterMap fun p =>
    (c.punctureFluidFacts p).map fun (_, category) =>
      c.test p.id (D004.judgmentTest p.item category)
        (if retained choices p.id then some true else c.excludedJudgmentCandidate)) ++
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
      | .ketone i => some (D007.Item.judgmentTest ⟨.further, i⟩)
      | .coagulation i => some (D006.judgmentTest i)
      | .endocrine i => some (D008.judgmentTest i)
      | .alpPag => some (D007.Item.judgmentTest ⟨.late, .alpIsoenzymesPag⟩)
      | .tumorMarker i => some (D009.judgmentTest i)
      | .rhFactor _ => some (D011.judgmentTest .otherRh)
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
  | .geneticDisease _ => bundleKey ⟨6, 4, .draw⟩ p
  | .chemistry _ => bundleKey ⟨7, 0, .draw⟩ p
  | .coagulation _ => bundleKey ⟨6, 0, .draw⟩ p
  | .endocrine _ => bundleKey ⟨8, 0, .draw⟩ p
  | .tumorMarker _ => bundleKey ⟨9, 0, .draw⟩ p
  | .rhFactor _ => bundleKey ⟨11, 3, .specimen⟩ p
  | .hepatitis _ => bundleKey ⟨13, 0, .draw⟩ p
  | .specificIge _ => bundleKey ⟨15, 13, .draw⟩ p
  | .viralTiter _ => bundleKey ⟨12, 11, .specimen⟩ p
  | .classTiter _ _ => bundleKey ⟨12, 46, .specimen⟩ p
  | .autoantibody _ => bundleKey ⟨14, 0, .day⟩ p
  | .individual test => (seriesRule test).bind fun (route, _) => bundleKey route p
  | _ => none

theorem assignment_disjoint (c : Input) {row : Performance Item} {a b : BundleKey}
    (ha : row ∈ assignedMembers Input.assignment c.rows a)
    (hb : row ∈ assignedMembers Input.assignment c.rows b) : a = b :=
  assigned_members_disjoint _ _ ha hb

private def susceptibilityTest (test : SpecimenJudgment.Test) : Bool :=
  test.major == 19 && test.suffix == 0 && [1, 2, 3].contains test.number

/-- D006-27の二系列も、個別評価証拠を原実施に照合してから同じ割当てに渡す。 -/
def Input.bundleAssignment (c : Input) (row : Performance Item) : Option BundleKey := do
  match row.item with
  | .individual test =>
    if susceptibilityTest test then do
      let species ← c.susceptibilitySpecies row.id
      let count := species.eraseDups.length
      if count == 0 || min 3 count != test.number then none else
        some ⟨⟨19, 0, .examination⟩, row.site, row.id⟩
    else if mycobacterialTest test then do
      let group ← c.mycobacterialGroup row.id
      let _ ← c.mycobacterialReading group
      return ⟨⟨20, 0, .collection⟩, row.site, group⟩
    else if (seriesRule test).isSome then Input.assignment row else
      let individual ← c.individualFacts row.id
      if individual.performance != { row with item := test } then none else
        let item ← individual.plasmaPanelItem
        plasmaPanelBundleKey { row with item := item }
  | _ => Input.assignment row

theorem bundle_assignment_disjoint (c : Input) {row : Performance Item} {a b : BundleKey}
    (ha : row ∈ assignedMembers c.bundleAssignment c.rows a)
    (hb : row ∈ assignedMembers c.bundleAssignment c.rows b) : a = b :=
  assigned_members_disjoint _ _ ha hb

theorem d019_bundle_assignment (c : Input) (p : Performance D019.Item) (species : List Nat)
    (confirmed : c.susceptibilitySpecies p.id = some species)
    (item : p.item.number ∈ [1, 2, 3])
    (nonempty : species.eraseDups.length ≠ 0)
    (count : min 3 species.eraseDups.length = p.item.number) :
    c.bundleAssignment { p with item := .individual (D019.judgmentTest p.item) } =
      some ⟨⟨19, 0, .examination⟩, p.site, p.id⟩ := by
  have present : species.eraseDups ≠ [] := fun h => nonempty (by simp [h])
  simp [Input.bundleAssignment, susceptibilityTest, D019.judgmentTest,
    confirmed, item, present, count]

theorem d020_bundle_assignment (c : Input) (p : Performance D020.Item)
    (group : Nat) (reading : D020.CollectionReading)
    (confirmed : c.mycobacterialGroup p.id = some group)
    (read : c.mycobacterialReading group = some reading) :
    c.bundleAssignment { p with item := .individual (D020.judgmentTest p.item) } =
      some ⟨⟨20, 0, .collection⟩, p.site, group⟩ := by
  simp [Input.bundleAssignment, susceptibilityTest, mycobacterialTest, D020.judgmentTest,
    confirmed, read]

/-- 同時又は一連の採取を、指定した読みと当日の採否で確認する。 -/
private def Input.checkMycobacterialGroups (c : Input) (choices : List GroupChoice) : Option Unit := do
  let rows := c.rows.filter fun row => match row.item with
    | .individual test => mycobacterialTest test
    | _ => false
  let keys ← rows.mapM c.bundleAssignment
  if (pairs (rows.zip keys)).any (fun ((a, ka), (b, kb)) =>
      ka != kb && (a.simultaneousWith b == some true || a.sameSeries b == some true)) then none else
  for key in keys.eraseDups do
    let members ← (assignedMembers c.bundleAssignment rows key).mapM fun row => do
      let .individual test := row.item | none
      let item ← match test.number with
        | 1 => some D020.Item.liquid
        | 2 => some D020.Item.other
        | _ => none
      return ({ row with item := item } : Performance D020.Item)
    let [anchor] := members.filter (fun row => retained choices row.id) | none
    let _ ← D020.collectionFromReading { performance := anchor } members
      (c.mycobacterialReading key.identity)
  return ()

def Input.needsBundle (row : Performance Item) : Bool :=
  match row.item with
  | .tumorTissue i => i != .sensitivity
  | .geneticDisease _ | .chemistry _ | .coagulation _ | .endocrine _ | .tumorMarker _
  | .rhFactor _ | .hepatitis _ | .specificIge _ | .viralTiter _ | .classTiter _ _
  | .autoantibody _ => true
  | .individual test => (seriesRule test).isSome || susceptibilityTest test ||
      mycobacterialTest test || (test.major == 6 && [12, 27].contains test.suffix)
  | _ => false

def Input.bundleCoverage (c : Input) : Bool :=
  c.rows.all fun row => !Input.needsBundle row || (c.bundleAssignment row).isSome

theorem bundle_coverage (c : Input) (checked : c.bundleCoverage = true)
    {row : Performance Item} (member : row ∈ c.rows) (required : Input.needsBundle row = true) :
    ∃ key, row ∈ assignedMembers c.bundleAssignment c.rows key := by
  have h := List.all_eq_true.mp checked row member
  simp only [required, Bool.not_true, Bool.false_or] at h
  cases assigned : c.bundleAssignment row with
  | none => simp [assigned] at h
  | some key => exact ⟨key, by simp [assignedMembers, member, assigned]⟩

/-- 採取IDで原実施を集め、指定された主検査と各実施の疾患分類からD006-4を組み立てる。 -/
def Input.geneticAssessments (c : Input) : Option (List Individual) := do
  let rows := c.rows.filter fun row => match row.item with
    | .geneticDisease _ => true
    | _ => false
  let keys ← rows.mapM c.bundleAssignment
  keys.eraseDups.mapM fun key => do
    let members ← (assignedMembers c.bundleAssignment rows key).mapM fun row => do
      let .geneticDisease disease := row.item | none
      let exam ← c.geneticExamination { row with item := disease }
      return exam.val
    let anchor :: _ := members | none
    let template ← c.geneticContext key.identity
    let ids := members.map (·.performance.id)
    let context ← match members with
      | [single] => do
        let grade ← single.group
        some { template with principal := single, item := grade.grade, application := .single }
      | _ => do
        let principal ← c.geneticPrincipal key.identity
        geneticDiseaseDraw anchor.performance members
          ⟨⟨D006Genetic.bundleRule.source, ids, 1⟩, [principal]⟩ template
    let proof ← c.geneticEligible context
    return Individual.d006_4 context proof.down

private def Item.extraBundle : Item → Bool
  | .tumorTissue i => decide (i ≠ .sensitivity)
  | .coagulation _ | .endocrine _ | .tumorMarker _ | .hepatitis _ | .specificIge _ | .rhFactor _
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
      | .rhFactor _ =>
        let factors := members.filterMap fun p => match p.item with
          | .rhFactor factor => some ({ p with item := factor } : Performance Nat)
          | _ => none
        let context : D011.Context := { performance := { anchor with item := .otherRh } }
        let group ← rhSpecimenInput context factors
        return [group.performance.item.points]
      | .hepatitis item =>
        let performed := assignedMembers Input.assignment rows key
        let count ← if performed.length == members.length then some members.length
          else c.hepatitisCountReading.map fun reading => match reading with
            | .performed => performed.length
            | .retained => members.length
        let typed := members.filterMap fun p => match p.item with
          | .hepatitis i => some ({ p with item := i } : Performance D013.Item)
          | _ => none
        if !distinctItems typed then none else
          let rows := typed.map fun p => ({ performance := p } : D013.Context)
          let draw ← hepatitisDraw { anchor with item := item } rows
          let performedItems := performed.filterMap fun p => match p.item with
            | .hepatitis i => some i
            | _ => none
          if count != draw.count && performedItems.eraseDups != performedItems then none
          else some [SpecimenTests.groupedBase .hepatitis count draw.standardSum]
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

def Input.individualRows (c : Input) (choices : List GroupChoice) :
    List (Performance SpecimenJudgment.Test) :=
  (c.rows.filterMap fun row => match row.item with
    | .individual test => if retained choices row.id then some { row with item := test } else none
    | _ => none)

private def Input.individuals (c : Input) (choices : List GroupChoice) : Option (List Individual) :=
  (c.individualRows choices).mapM fun row => do
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

theorem individual_candidates_exclude (c : Input) (choices : List GroupChoice)
    (row : Performance SpecimenJudgment.Test) (excluded : retained choices row.id = false) :
    row ∉ c.individualRows choices := by
  intro member
  obtain ⟨p, _, projected⟩ := List.mem_filterMap.mp member
  cases h : p.item <;> simp [h] at projected
  obtain ⟨kept, rfl⟩ := projected
  simp [excluded] at kept

private def Input.validCollectionRows (c : Input) : Bool :=
  let ids := c.collectionRows.map (·.1.id)
  ids.eraseDups == ids && c.collectionRows.all fun (p, testId) =>
    p.site == c.site && !p.item.inpatient && c.collectionFactsConfirmed p.id == some true &&
    !c.rows.any (·.id == p.id) &&
    (!SpecimenCollection.isSeries p.item.item || p.series == some p.item.seriesId) &&
    c.rows.any (fun row => row.id == testId &&
      (!p.specimen.isSome || row.specimen == p.specimen))

/-- D006-12・D006-27を当日確認済みの採血IDごとに集約する。 -/
private def Input.individualPoints (c : Input) (rows : List Individual) : Option (List Nat) := do
  let panel ← (rows.filter (·.plasmaPanelItem.isSome)).mapM fun i => do
    let item ← i.plasmaPanelItem
    let key ← c.bundleAssignment { i.performance with item := .individual i.performance.item }
    let assessed : D006PlasmaPanel.Assessed :=
      { performance := { i.performance with item := item }, points := i.points }
    return ((key.site, key.identity), assessed)
  let draws := (panel.map Prod.fst).eraseDups
  let grouped ← draws.mapM fun draw => do
    let members := (panel.filter fun p => p.1 == draw).map Prod.snd
    let items := members.map (·.performance.item)
    if items.eraseDups != items then none else some (D006PlasmaPanel.bundlePoints members).total
  -- D019とD020では、一検査・一採取の割当てを確認した後に区分別の一群分の点数を使う。
  return (rows.filter fun i => i.plasmaPanelItem.isNone).map Individual.points ++ grouped

theorem rh_rate_projection (g : D011.Context) (p : Nat) :
    Satisfies D011.rules g p ↔ p = g.performance.item.points :=
  D011.rate_iff g p

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
  | .tumorTissue _ | .rhFactor _ | .hepatitis _ | .specificIge _ | .viralTiter _
  | .classTiter _ _ | .autoantibody _ =>
    some (.other (c.rapidOtherBasis id))
  | .geneticDisease _ => some (.other (c.rapidOtherBasis id))
  | .individual test =>
    if (seriesRule test).isSome || (test.major == 6 && [4, 12, 27].contains test.suffix) then
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
private def Input.prepareFacts (c : Input) (choices : List GroupChoice) :
    Option (Day × List Nat) := do
  let ids := c.rows.map Performance.id
  if decide (c.judgment.status ≠ .outpatient) ||
      !c.collectionHistoryConfirmed || !c.validCollectionRows || c.collections.length > 1 ||
      !c.collections.all (fun p => SpecimenCollection.isD400 p.item && !p.inpatient) ||
      !c.rows.all (fun p => p.item.supported && p.site == c.site &&
      c.eligible p.id == some true) || ids.eraseDups != ids || c.additions.site != c.site then none
  else
    let _ ← c.checkMycobacterialGroups choices
    if c.morphology.length != (c.morphology.map (·.item.item)).eraseDups.length ||
        c.urine.length > 1 then none else
      let urine ← (c.urine.filter fun p => retained choices p.performance.id).mapM fun p =>
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
      let fecal ← (c.fecal.filter fun p => retained choices p.id).mapM fun p => do
        let confirmed ← c.fecalFacts p
        return UrineFecalTests.fecalPoints confirmed.val.performance.item
      let punctureFluid ← (c.punctureFluid.filter fun p => retained choices p.id).mapM fun p => do
        let (confirmed, _) ← c.punctureFluidFacts p
        D004.scheduled confirmed.val
      let sensitivity ← (c.rows.filterMap fun p => match p.item with
        | .tumorTissue .sensitivity =>
          if retained choices p.id then some ({ p with item := .sensitivity } : Performance D004Tumor.Item) else none
        | _ => none).mapM fun p => do
          let _ ← c.tumorSensitivityFacts p
          return D004Tumor.Item.sensitivity.points
      let morphology ← c.morphologyPoints choices
      let draws ← c.chemistryDraws choices
      let extra ← c.extraBundlePoints choices
      let ketones ← (c.ketones.filter fun p => retained choices p.id).mapM
        (fun p => p.item.scheduledPoints)
      let pag := c.rows.filterMap fun p => match p.item with
        | .alpPag =>
          if retained choices p.id then some (BloodChemistryLate.Item.points .alpIsoenzymesPag) else none
        | _ => none
      let individuals ← c.individuals choices
      let directPoints ← c.individualPoints individuals
      let genetic ← ({ c with rows := c.rows.filter (fun row => retained choices row.id) }).geneticAssessments
      if individuals.any (fun i => i.performance.item.major == 6 && i.performance.item.suffix == 4 &&
          genetic.any (fun g => g.performance.draw == i.performance.draw)) then none else
      let geneticTests ← (c.rows.filterMap fun row => match row.item with
        | .geneticDisease disease => some ({ row with item := disease } : Performance Nat)
        | _ => none).mapM fun row => do
          let main := genetic.find? (fun main => main.performance.draw == row.draw)
          if retained choices row.id then
            let chosen ← main
            return c.test row.id chosen.performance.item
              (if chosen.performance.id == row.id then some true else c.excludedJudgmentCandidate)
          else
            let test := main.map (·.performance.item)
            let test ← test.orElse (fun _ => (c.individualFacts row.id).map (·.performance.item))
            return c.test row.id test c.excludedJudgmentCandidate
      let execution := (draws.map fun (_, items) => BloodChemistry.pointsForItems items) ++
        morphology ++ urine ++ specialUrine ++ sediment ++ fecal ++ punctureFluid ++ sensitivity ++ extra ++ pag ++
        ketones ++ directPoints ++ genetic.map Individual.points
      let tests := c.tests choices ++ geneticTests
      let day ← Day.withTests ⟨[], [], c.judgment, c.additions⟩ tests
      let day ← c.checkedRapid choices day tests
      let _ ← day.judgment.points
      return (day, execution)

private def Input.confirmDay (c : Input) (selected : Option (List Nat)) :
    Option (Day × List Nat) := do
  if !c.bundleCoverage then none else
    let choices ← c.resolveDayChoices selected
    c.prepareFacts choices

def Input.prepare (c : Input) (selected : Option (List Nat)) : Option (Day × List Nat) :=
  (c.confirmDay selected).map fun (day, execution) =>
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

theorem bundle_coverage_of_scope (c : Input) (selected : Option (List Nat))
    (scope : c.Scope selected) {row : Performance Item} (member : row ∈ c.rows)
    (required : Input.needsBundle row = true) :
    ∃ key, row ∈ assignedMembers c.bundleAssignment c.rows key := by
  apply bundle_coverage c _ member required
  obtain ⟨_, prep, execution, _, prepared, _, _⟩ := scope
  cases h : c.bundleCoverage with
  | true => rfl
  | false =>
    simp [Input.prepare, Input.confirmDay, h] at prepared

theorem missing_bundle_holds_day (c : Input) (selected : Option (List Nat))
    {row : Performance Item} (member : row ∈ c.rows)
    (required : Input.needsBundle row = true)
    (unassigned : c.bundleAssignment row = none) : c.prepare selected = none := by
  have unchecked : c.bundleCoverage = false := by
    cases h : c.bundleCoverage with
    | false => rfl
    | true =>
      have accepted := List.all_eq_true.mp h row member
      simp [required, unassigned] at accepted
  simp [Input.prepare, Input.confirmDay, unchecked]

theorem unique_bundle_of_scope (c : Input) (selected : Option (List Nat))
    (scope : c.Scope selected) {row : Performance Item} (member : row ∈ c.rows)
    (required : Input.needsBundle row = true) :
    ∃ key, row ∈ assignedMembers c.bundleAssignment c.rows key ∧
      ∀ other, row ∈ assignedMembers c.bundleAssignment c.rows other → other = key := by
  obtain ⟨key, assigned⟩ := bundle_coverage_of_scope c selected scope member required
  exact ⟨key, assigned, fun _ other => bundle_assignment_disjoint c other assigned⟩

theorem scope_realizes_choices (c : Input) (selected : Option (List Nat))
    (scope : c.Scope selected) :
    ∃ groups free directed outside choices,
      c.groups = some groups ∧ resolveChoices groups selected = some free ∧
      c.directedChoices = some directed ∧ c.outsideChoices = some outside ∧
      c.resolveDayChoices selected = some choices ∧ choices = free ++ directed ++ outside ∧
      Satisfies (choices.map GroupChoice.rule) () (fun id => retained choices id = true) := by
  obtain ⟨_, prep, execution, _, prepared, _, _⟩ := scope
  have resolved : ∃ choices, c.resolveDayChoices selected = some choices := by
    cases h : c.resolveDayChoices selected with
    | none => simp [Input.prepare, Input.confirmDay, h] at prepared
    | some choices => exact ⟨choices, rfl⟩
  obtain ⟨choices, resolved⟩ := resolved
  cases hg : c.groups with
  | none => simp [Input.resolveDayChoices, hg] at resolved
  | some groups =>
    cases hd : c.directedChoices with
    | none => simp [Input.resolveDayChoices, hg, hd] at resolved
    | some directed =>
      cases hf : resolveChoices groups selected with
      | none => simp [Input.resolveDayChoices, hg, hd, hf] at resolved
      | some free =>
        cases ho : c.outsideChoices with
        | none => simp [Input.resolveDayChoices, hg, hd, ho] at resolved
        | some outside =>
          have h : agreeChoices (free ++ directed ++ outside) = some choices := by
            simpa [Input.resolveDayChoices, hg, hd, hf, ho] using resolved
          have sound := agree_choices_spec h
          exact ⟨groups, free, directed, outside, choices, rfl, hf, rfl, rfl,
            resolved, sound.1, sound.2⟩

theorem retained_of_unrelated (choices : List GroupChoice) (id : Nat)
    (unrelated : ∀ choice ∈ choices, id ∉ choice.group.members) :
    retained choices id = true := by
  simp only [retained, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, List.contains_iff_mem]
  exact fun g hg => Or.inl (fun present => unrelated g hg (List.contains_iff_mem.mp present))

theorem missing_outside_confirmation_holds_day (c : Input) (selected : Option (List Nat))
    {g : SpecimenSelectionInventory.Entry} {ids : List Nat}
    (required : (g, ids) ∈ c.requiredOutside)
    (missing : c.outsideSelection g.id = none) : c.prepare selected = none := by
  have unresolved : c.outsideChoices = none := by
    cases h : c.outsideChoices with
    | none => rfl
    | some choices =>
      obtain ⟨decisions, confirmed⟩ := outside_confirmed c h required
      simp [missing] at confirmed
  simp [Input.prepare, Input.confirmDay, Input.resolveDayChoices, unresolved]

theorem scope_applies_outside_choice (c : Input) (selected : Option (List Nat))
    (scope : c.Scope selected)
    {g : SpecimenSelectionInventory.Entry} {ids members kept : List Nat}
    (required : (g, ids) ∈ c.requiredOutside)
    {decisions : List (List Nat × List Nat)}
    (confirmed : c.outsideSelection g.id = some decisions)
    (active : (members, kept) ∈ decisions) :
    ∃ choices, c.resolveDayChoices selected = some choices ∧
      ∀ id ∈ members, retained choices id = true ↔ id ∈ kept := by
  obtain ⟨_, free, directed, outside, choices, _, _, _, checked, resolved, eq, satisfies⟩ :=
    scope_realizes_choices c selected scope
  have included := outside_choice_included c checked required confirmed active
  let choice : GroupChoice := ⟨⟨g.source, members, kept.length⟩, kept⟩
  have member : choice ∈ choices := by rw [eq]; simp [choice, included]
  exact ⟨choices, resolved, (satisfies choice.rule (List.mem_map.mpr ⟨choice, member, rfl⟩)).2⟩

theorem scope_satisfies_registered (c : Input) (selected : Option (List Nat))
    (scope : c.Scope selected)
    (enough : ¬ (c.registrationRows.map Performance.item).eraseDups.length < 2)
    {entry : SpecimenSelectionInventory.Entry}
    (registered : entry ∈ SpecimenSelectionInventory.inventory.filter (·.dayRegistration.isSome))
    {groups : List SpecimenSelectionGeneration.Instance}
    (generated : c.generateRegistered entry = some groups)
    {group : SpecimenSelectionGeneration.Instance} (member : group ∈ groups) :
    ∃ choices, c.resolveDayChoices selected = some choices ∧
      group.Permits (retained choices) := by
  obtain ⟨_, free, directed, outside, choices, _, _, hd, _, resolved, eq, satisfies⟩ :=
    scope_realizes_choices c selected scope
  unfold Input.directedChoices at hd
  obtain ⟨registeredChoices, checked, rest⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨choice, included, projected⟩ :=
    registered_choice_included c checked enough registered generated member
  obtain ⟨ketones, _, appended⟩ := Option.bind_eq_some_iff.mp rest
  have inDirected : choice ∈ directed := by
    rw [← Option.some.inj appended]
    exact List.mem_append.mpr (Or.inl included)
  have inChoices : choice ∈ choices := by rw [eq]; simp [inDirected]
  exact ⟨choices, resolved, registered_choice_sound c entry.source group choice projected _
    (satisfies choice.rule (List.mem_map.mpr ⟨choice, inChoices, rfl⟩)).2⟩

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

/-- 読みを固定した日について、自由選択による内訳は有限なリストに全て含まれる。 -/
theorem allowed_finite (c : Input) :
    ∃ results : List Breakdown, ∀ r, c.Allowed r → r ∈ results := by
  classical
  -- 群の生成に失敗した場合は、定義域に入る選択がない。
  let candidates : List (Option (List Nat)) := none ::
    (consistentSelections (c.groups.getD []) [] []).map some
  let result (choice : Option (List Nat)) : Option Breakdown :=
    if h : ∃ r, c.Scope choice ∧ c.Permits choice r then some (Classical.choose h) else none
  refine ⟨candidates.filterMap result, ?_⟩
  rintro r ⟨selected, scope, allowed⟩
  obtain ⟨supported, prep, execution, day, prepared, collected, confirmed⟩ := scope
  have resolved : ∃ choices, c.resolveDayChoices selected = some choices := by
    cases h : c.resolveDayChoices selected with
    | none =>
      simp [Input.prepare, Input.confirmDay, h] at prepared
    | some choices => exact ⟨choices, rfl⟩
  obtain ⟨choices, resolved⟩ := resolved
  cases hg : c.groups with
  | none => simp [Input.resolveDayChoices, hg] at resolved
  | some groups =>
    cases hf : resolveChoices groups selected with
    | none =>
      cases hd : c.directedChoices with
      | none => simp [Input.resolveDayChoices, hg, hd] at resolved
      | some directed =>
        simp [Input.resolveDayChoices, hg, hd, hf] at resolved
    | some free =>
      obtain ⟨candidate, member, same⟩ := resolveChoices_canonical groups selected hf
      have eq : c.resolveDayChoices candidate = c.resolveDayChoices selected := by
        cases hd : c.directedChoices <;> simp [Input.resolveDayChoices, hg, hd, hf, same]
      have prepareEq : c.prepare candidate = c.prepare selected := by
        simp only [Input.prepare, Input.confirmDay, eq]
      have scope' : c.Scope candidate :=
        ⟨supported, prep, execution, day, prepareEq.trans prepared, collected, confirmed⟩
      have allowed' : c.Permits candidate r := by
        simpa [Input.Permits, prepareEq] using allowed
      have existsResult : ∃ b, c.Scope candidate ∧ c.Permits candidate b :=
        ⟨r, scope', allowed'⟩
      have unique := (determines c candidate scope').choose_spec.2
      have eqResult : Classical.choose existsResult = r :=
        (unique _ (Classical.choose_spec existsResult).2).trans (unique _ allowed').symm
      exact List.mem_filterMap.mpr
        ⟨candidate, by simpa [candidates, hg] using member,
          by unfold result; rw [dite_eq_left existsResult, eqResult]⟩

/-- この日次経路で実装した読みの組合せ。基礎となる適格性と履歴は固定する。 -/
def Input.readingAlternatives (c : Input) : List Input := Id.run do
  let units := [none, some CotestReading.simultaneous, some .specimen, some .day]
  let counts := [none, some HepatitisCountReading.performed, some .retained]
  let mut alternatives := []
  for cholesterol in units do
    for protein in units do
      for ketone in units do
        for hepatitis in counts do
          alternatives := { c with
            cholesterolReading := cholesterol
            proteinReading := protein
            ketoneReading := ketone
            hepatitisCountReading := hepatitis } :: alternatives
  return alternatives

def Input.AllowedReadings (c : Input) (r : Breakdown) : Prop :=
  ∃ candidate ∈ c.readingAlternatives, candidate.Allowed r

theorem allowed_readings_finite (c : Input) :
    ∃ results : List Breakdown, ∀ r, c.AllowedReadings r → r ∈ results := by
  have cover (inputs : List Input) :
      ∃ results : List Breakdown, ∀ r, (∃ input ∈ inputs, input.Allowed r) →
        r ∈ results := by
    induction inputs with
    | nil => exact ⟨[], by simp⟩
    | cons input rest ih =>
      obtain ⟨head, hhead⟩ := allowed_finite input
      obtain ⟨tail, htail⟩ := ih
      refine ⟨head ++ tail, ?_⟩
      rintro r ⟨candidate, h, allowed⟩
      rcases List.mem_cons.mp h with rfl | member
      · exact List.mem_append.mpr (Or.inl (hhead r allowed))
      · exact List.mem_append.mpr (Or.inr (htail r ⟨candidate, member, allowed⟩))
  exact cover c.readingAlternatives

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

example : Date.ofParts 2026 10 22 = some site.date := by decide

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

private def confirmOutside (c : Input) (id : String)
    (decision : List (List Nat × List Nat)) : Input :=
  { c with outsideSelection := fun clause =>
      if clause == id then some decision else c.outsideSelection clause }

private def confirmInactive (c : Input) (ids : List String) : Input :=
  ids.foldl (fun day id => confirmOutside day id []) c

private def urineDaySite : Site := site

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
  { (confirmInactive urineDayBase ["notice/D003/paragraph/4/u"]) with
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

private def flowDay : Input :=
  { (confirmOutside
    (confirmInactive pairedSediment ["primary/D017/note/unnumbered/1"])
    "notice/D002/paragraph/5" [([3, 5], [5])]) with sedimentPaired := some true }

example :
    pairedSediment.groups = none ∧
      flowDay.groups.map (List.map ChoiceGroup.members) = some [[3, 5]] ∧
      (flowDay.prepare none).isNone ∧
      (flowDay.withoutAdditions (some [5])).map Breakdown.execution = some [7, 24, 25, 20] := by decide

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

private def sensitivityDay : Input :=
  let checked := confirmInactive urineAndStool
    ["notice/D004-2/paragraph/7", "notice/D004-2/paragraph/8", "notice/D004-2/paragraph/9",
     "notice/D004-2/paragraph/10", "notice/D004-2/paragraph/11",
     "notice/D006-22/paragraph/3", "notice/D006-24/paragraph/2"]
  { checked with
    rows := urineAndStool.rows ++ [{ sensitivityRow with item := .tumorTissue .sensitivity }]
    tumorSensitivityFacts := fun p =>
      if h : sensitivityRow = p then some (⟨sensitivityContext, h, sensitivityEligible⟩, .biochemicalII)
      else none }

example : (sensitivityDay.withoutAdditions none).map Breakdown.execution =
    some [7, 25, 2500] := by decide

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

private def rawDifferential (principal : Nat := 1) : Input :=
  let urine : D000.Context :=
    ⟨⟨3, site, (), none, none, none, none⟩, some site.institution, some .strip, [.ph], some .direct⟩
  { (confirmOutside base "notice/D005/paragraph/3" [([1, 2], [principal])]) with
    rows := [morphologyRow 1 .eosinophilCount, morphologyRow 2 .automatedDifferential,
    { id := 3, site, item := .urine urine }] ++ chemistryRows [.bun, .uricAcid, .glucose, .ast, .alt] }

private def total (c : Input) (selected : Option (List Nat)) : Option Nat :=
  (c.withoutAdditions selected).map (·.total.specimenWithCollection)

example : total raw429 none = some 429 := by decide
example : total (rawDifferential 1) (some [1]) = some 405 := by decide
example : total (rawDifferential 2) (some [2]) = some 403 := by decide
example : total (rawDifferential 1) none = none := by decide

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
  { (rawDifferential 1) with
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
  { (confirmOutside (confirmInactive urineAndStool ["notice/D008/paragraph/4"])
      "notice/D008/paragraph/16" [([70, 71], [70])]) with
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
  { (confirmInactive mixedRawDay
      ["notice/D012/paragraph/12", "notice/D012/paragraph/30", "notice/D012/paragraph/32",
       "notice/D018/paragraph/1/e", "notice/D018/paragraph/1/u",
       "notice/ch2-part3-section4/general/3"]) with
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

private theorem seven_category_scope : sevenCategoryDay.Scope (some [20, 33, 70]) := by
  refine ⟨?_, _, _, _, rfl, rfl, ?_⟩
  · exact fun _ membership => List.all_eq_true.mp (by decide :
      sevenCategoryDay.rows.all (fun p => p.item.supported) = true) _ membership
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

theorem seven_category_day_determines :
    ∃ r, sevenCategoryDay.Permits (some [20, 33, 70]) r ∧
      ∀ other, sevenCategoryDay.Permits (some [20, 33, 70]) other → other = r :=
  determines sevenCategoryDay (some [20, 33, 70]) seven_category_scope

private def generatedGroupsDay : Input :=
  let newRows : List (Performance Item) :=
    [{ id := 90, site := urineDaySite, item := .chemistry .hdlCholesterol, draw := some 2,
       simultaneous := some 3 },
     { id := 91, site := urineDaySite, item := .chemistry .totalCholesterol, draw := some 2,
       simultaneous := some 3 },
     { id := 92, site := urineDaySite, item := .chemistry .ldlCholesterol, draw := some 2,
       simultaneous := some 4 },
     { id := 93, site := urineDaySite, item := .hepatitis .hbcAntibody, draw := some 3,
       simultaneous := some 5 },
     { id := 94, site := urineDaySite, item := .hepatitis .hbcIgM, draw := some 3,
       simultaneous := some 5 },
     { id := 95, site := urineDaySite, item := .hepatitis .hbeAntigen, draw := some 3 },
     { id := 96, site := urineDaySite, item := .ketone .ketoneBodies },
     { id := 97, site := urineDaySite, item := .ketone .ketoneFractions }]
  { sevenCategoryDay with
    rows := sevenCategoryDay.rows ++ newRows
    cholesterolReading := some .day
    ketoneReading := some .day
    hepatitisCountReading := some .retained }

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .rhFactor 1, specimen := some 1 },
       { id := 2, site, item := .rhFactor 2, specimen := some 1 },
       { id := 3, site, item := .rhFactor 1, specimen := some 2 }]
    (({ base with rows := rows }).withoutAdditions none).map Breakdown.execution =
      some [163, 163] := by decide

example :
    let row : Performance Item := { id := 1, site, item := .rhFactor 1 }
    (({ base with rows := [row] }).prepare none).isNone := by decide

example : total generatedGroupsDay (some [20, 33, 70, 90, 91, 93]) = some 5737 := by decide
example : total generatedGroupsDay (some [20, 33, 70, 91, 92, 94]) = some 5754 := by decide
example :
    total { generatedGroupsDay with cholesterolReading := some .simultaneous }
      (some [20, 33, 70, 93]) = some 5755 := by decide
example :
    total { generatedGroupsDay with hepatitisCountReading := some .performed }
      (some [20, 33, 70, 90, 91, 93]) = some 5799 := by decide
example :
    total { generatedGroupsDay with cholesterolReading := none }
      (some [20, 33, 70, 90, 91, 93]) = none := by decide
example :
    total { generatedGroupsDay with hepatitisCountReading := none }
      (some [20, 33, 70, 90, 91, 93]) = none := by decide

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

private def coreAntigenExample : Individual := by
  let p : Performance D013.Item :=
    { id := 98, site := urineDaySite, item := .hbcrAntigen, simultaneous := some 6 }
  let history : ClaimHistory D013.Item :=
    ⟨⟨{ p.site.monthScope with institution := none }, []⟩, by simp⟩
  let c : D013.Context :=
    { performance := p, specimen := some .serum, priorClaims := some history
      diagnosisOrResponsePurpose := some true, simultaneousHbvDna := some true
      mainWhenHbvDnaMeasured := some true }
  refine Individual.d013 c ?_
  simp [D013.Eligible, D013.eligibilityRules, satisfies_cons, satisfies_nil,
    D013.antigenMethod, D013.antibodyMethod, D013.reactivationScreen, D013.coreMethod,
    D013.hbCoreChoice, D013.haChoice, D013.serotype, D013.coreRelatedAntigen,
    D013.genotype, D013.Context.item, D013.SingleChoice, c, p]
  refine ⟨by decide, history, rfl, by decide⟩

private def coreDnaExample : Individual := by
  let p : Performance Unit :=
    { id := 99, site := urineDaySite, item := (), simultaneous := some 6 }
  let c : D023.OutpatientInput :=
    ⟨.hbv { performance := p, method := .pcr, considersReactivation := some false },
      true, .outpatient, none, none, none⟩
  refine Individual.d023 c { p with item := c.test } rfl ?_ ?_
  · simp [D023.OutpatientEligible, D023.OutpatientTest.Eligible, D023.OutpatientTest.tier,
      D023.OutpatientTest.rapidTarget, c]
    exact ⟨by simp, Or.inl rfl⟩
  · intro anchor h
    exact Option.some.inj h.symm

private def registeredGroupsDay (principal : Nat) : Input :=
  let added := [coreAntigenExample, coreDnaExample]
  let previous := confirmInactive generatedGroupsDay
    ["notice/D023/paragraph/2/a", "notice/D023/paragraph/5/a",
     "notice/D023/paragraph/16/u", "notice/D023/paragraph/39/i", "notice/D023-2/paragraph/1/i"]
  { previous with
    rows := previous.rows ++ added.map (fun i => { i.performance with item := .individual i.performance.item })
    individualFacts := fun id => (added.find? (·.performance.id == id)).orElse (fun _ =>
      previous.individualFacts id)
    selectionKeep := fun id => some (id == principal) }

example :
    (registeredGroupsDay 98).registeredChoices.map (List.map (·.selected)) = some [[98]] :=
  by decide

example :
    total (registeredGroupsDay 98) (some [20, 33, 70, 90, 91, 93]) = some 5983 := by decide

example :
    total (registeredGroupsDay 99) (some [20, 33, 70, 90, 91, 93]) = some 5993 := by decide

example :
    let c := registeredGroupsDay 98
    ({ c with selectionKeep := fun _ => none : Input }.registeredChoices).isNone = true := by decide

private def seriesExample (id : Nat) (series : Nat) : Individual := by
  let p : Performance Unit := { id, site, item := (), series := some series }
  let ctx : D021.Context := ⟨p, some [p]⟩
  have valid : D021.InScope ctx := by
    simp [D021.InScope, D021.indication, D021.OneInSeries, ctx, p, Performance.sameSeries,
      Performance.sameGroup]
  exact Individual.d021 ctx valid (by simpa [D021.rates, satisfies_cons, satisfies_nil,
    D021.rate, D021.InScope, D021.indication] using valid)

example :
    let assessed := seriesExample 2 3
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .individual D021.judgmentTest, series := some 3 },
       { id := 2, site, item := .individual D021.judgmentTest, series := some 3 }]
    let c := { base with
      rows := rows
      seriesConfirmed := fun key => key.identity == 3
      individualFacts := fun id => if id == 2 then some assessed else none
      individualStandalone := fun _ => some true }
    (c.groups.map (List.map ChoiceGroup.members),
      (c.withoutAdditions (some [2])).map Breakdown.execution,
      ({ c with seriesConfirmed := fun _ => false }.prepare (some [2])).isNone) =
      (some [[1, 2]], some [376], true) := by decide

example :
    let c := { base with rows :=
      [{ id := 1, site, item := .other ("D007", "procalcitoninQuantitative") },
       { id := 2, site, item := .other ("D007", "presepsin") }] }
    c.pendingOverlap = ["notice/D007/paragraph/48/i"] := by decide

example :
    let c := { base with rows :=
      [{ id := 1, site, item := .hepatitis .hbcAntibody, draw := some 1 },
       { id := 2, site, item := .hepatitis .hbcIgM, draw := some 1, simultaneous := some 3 }] }
    c.groups.isNone := by decide

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

private def markerDay : Input :=
  let checked := confirmInactive base ["notice/D001/paragraph/4/i", "notice/D008/paragraph/4"]
  { checked with rows :=
    [{ id := 1, site, item := .endocrine .fsh, draw := some 1 },
     { id := 2, site, item := .endocrine .lh, draw := some 1 },
     { id := 3, site, item := .endocrine .cortisol, draw := some 1 },
     { id := 4, site, item := .tumorMarker ⟨3, 0⟩, draw := some 1 },
     { id := 5, site, item := .tumorMarker ⟨4, 0⟩, draw := some 1 }] }

example : (markerDay.withoutAdditions none).map Breakdown.execution = some [410, 230] := by decide

example : total markerDay none = some 784 := by decide

private def viralTiterDay (rows : List (Performance Item)) : Input :=
  { (confirmInactive base ["notice/D012/paragraph/38/i", "notice/D012/paragraph/38/u",
      "notice/D023/paragraph/2/a", "notice/D023/paragraph/5/a"]) with rows }

private def immunologyDay : Input :=
  let rows : List (Performance Item) :=
    [{ id := 1, site, item := .rhFactor 1, specimen := some 1 },
     { id := 2, site, item := .viralTiter .rubella, specimen := some 2 },
     { id := 3, site, item := .autoantibody .rnpQuant },
     { id := 4, site, item := .specificIge (some 1), draw := some 3 }]
  { (confirmInactive (viralTiterDay rows) ["notice/D014/paragraph/1", "notice/D014/paragraph/7/i"]) with
    autoantibodyDayConfirmed := true }

example : total immunologyDay none = some 640 := by decide

private theorem immunology_day_scope : immunologyDay.Scope none := by
  refine ⟨?_, _, _, _, rfl, rfl, ?_⟩
  · exact fun _ membership => List.all_eq_true.mp (by decide :
      immunologyDay.rows.all (fun p => p.item.supported) = true) _ membership
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

theorem immunology_day_determines :
    ∃ r, immunologyDay.Permits none r ∧ ∀ other, immunologyDay.Permits none other → other = r :=
  determines immunologyDay none immunology_day_scope

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .viralTiter .rubella, specimen := some 1 },
       { id := 2, site, item := .viralTiter .rubella, specimen := some 1 },
       { id := 3, site, item := .viralTiter .measles, specimen := some 1 }]
    ((viralTiterDay rows).withoutAdditions none).map Breakdown.execution =
      some [158] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .classTiter .rubella .igm, specimen := some 1 },
       { id := 2, site, item := .classTiter .measles .igg, specimen := some 1 },
       { id := 3, site, item := .classTiter .mumps .igg, specimen := some 1 }]
    ((viralTiterDay rows).withoutAdditions none).map Breakdown.execution =
      some [400] := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .autoantibody .rnpQuant },
       { id := 2, site, item := .autoantibody .smQuant },
       { id := 3, site, item := .autoantibody .ssbQuant }]
    (({ (confirmInactive base ["notice/D014/paragraph/1", "notice/D014/paragraph/7/i"]) with
      rows, autoantibodyDayConfirmed := true } : Input).withoutAdditions none).map
      Breakdown.execution = some [490] ∧
    total { base with rows } none = none := by decide

example :
    let rows : List (Performance Item) :=
      [{ id := 1, site, item := .alpPag, draw := some 1 },
       { id := 2, site, item := .endocrine .bap, draw := some 1 }]
    let c := { (confirmOutside (confirmInactive base ["notice/D008/paragraph/4"])
      "notice/D008/paragraph/16" [([1, 2], [1])]) with rows, alpPaired := some true }
    let bap := confirmOutside c "notice/D008/paragraph/16" [([1, 2], [2])]
    c.groups.map (List.map ChoiceGroup.members) = some [[1, 2]] ∧
      (c.withoutAdditions (some [1])).map Breakdown.execution = some [180] ∧
      (bap.withoutAdditions (some [2])).map Breakdown.execution = some [D008.Item.bap.points] ∧
      total { c with alpPaired := none } (some [1]) = none := by decide

private theorem raw429_scope : raw429.Scope none := by
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

theorem raw429_determines :
    ∃ r, raw429.Permits none r ∧ ∀ other, raw429.Permits none other → other = r :=
  determines raw429 none raw429_scope

private def susceptibilityExample : Individual := by
  let row : Performance D019.Item := { id := 1, site, item := .two }
  let c : D019.Context := {
    performance := row, speciesCount := 2,
    routineAntimicrobialNonSusceptibility := some true,
    needsRepeatForMultidrugResistantTreatment := some true,
    testPerformedOnDetectedOrganism := some true }
  apply Individual.d019 c
  refine ⟨rfl, ?_⟩
  simp only [D019.eligibilityRules, satisfies_cons, satisfies_nil]
  refine ⟨Or.inr ⟨rfl, rfl⟩, rfl, ?_, ?_, trivial⟩
  · change D019.Item.two = .resistance → _
    intro h
    cases h
  · change D019.Item.two = .combination → _
    intro h
    cases h

private def mycobacterialExample : Individual := by
  let row : Performance D020.Item := { id := 2, site, item := .liquid, simultaneous := some 3 }
  let c : D020.Context := {
    performance := row, liquidMedium := some true,
    detection := some .redoxDye, collection := some [row], selected := some [row] }
  refine Individual.d020 c ?_ ((D020.legacy_iff _ _).mpr rfl)
  have collection : D020.collectionLimit.holds c () :=
    D020.collectionFromReading_sound (c := c) (rows := [row]) (reading := some .pairwise) rfl
  simp only [D020.InScope, satisfies_cons, satisfies_nil]
  refine ⟨collection, ?_, ?_, trivial⟩
  · change _ → D020.Liquid c
    exact fun _ => ⟨rfl, by simp [c]⟩
  · change D020.Item.liquid = .other → D020.Other c
    intro h
    cases h

private def yeastExample : Individual := by
  let c : D019Yeast.Context :=
    { performance := { id := 4, site, item := () }
      deepMycosis := some true, isolatedCausativeOrganism := some .candida }
  apply Individual.d019_2 c <;>
    simp [D019Yeast.InScope, D019Yeast.indication, D019Yeast.rates, D019Yeast.rate,
      satisfies_cons, satisfies_nil, c]

private def mixedDrugExample : Individual := by
  let c : D022.Context :=
    { performance := { id := 5, site, item := () }
      method := .mixedDrugResistance, agents := [1, 2, 3, 4] }
  apply Individual.d022 c
  · have enough : 4 ≤ c.quantity := by decide
    simp only [D022.InScope, satisfies_cons, satisfies_nil]
    exact ⟨enough, enough, fun _ => enough, trivial⟩
  · simp only [D022.rates, satisfies_cons, satisfies_nil]
    exact ⟨rfl, trivial⟩

private def breathExample : Individual := by
  let c : D023Other.Context :=
    { performance := { id := 6, site, item := .breath }, pyloriNotificationSatisfied := some true }
  apply Individual.d023_2 c
  simp only [D023Other.InScope, D023Other.eligibilityRules, satisfies_cons, satisfies_nil]
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, trivial⟩ <;>
    (intro h; first | rfl | cases h)

private def lymphocyteExample : Individual := by
  let c : D016.Context :=
    { performance := { id := 7, site, item := .tSubset, series := some 7 }
      investigatesImmunodeficiency := some true, otherSelected := some [] }
  apply Individual.d016 c
  simp [D016.Eligible, D016.eligibilityRules, satisfies_cons, satisfies_nil, D016.seriesRule,
    D016.SeriesUnit, D016.surfaceRule, D016.lstBranches, D016.lstMethod, D016.gpiRule,
    D016.Context.item, D016.Item.number, c]

private def microscopySeriesExample : Individual := by
  let row : Performance D017.Item :=
    { id := 8, site, item := .specializedMicroscopy, specimen := some 8, series := some 8 }
  let c : D017.Context :=
    { performance := row, material := some .sputum,
      examinesBacteriaOrProtozoaOrSimilar := some true, concentrationSmear := some true,
      sediment := some .noCombinedPerformance, selectedInExamination := some [row],
      sameCauseSuspectedAcrossSites := some false }
  have scope : D017.InScope c := by
    simp [D017.InScope, D017.eligibilityRules, satisfies_cons, satisfies_nil, D017.materialRule,
      D017.oneExamination, D017.causativeSite, D017.Context.suppressed, D017.SmearKnown,
      D017.Context.item, c, row]
  exact Individual.d017 c 65 35 scope ((D017.legacy_iff _ _ scope false rfl).mpr rfl)

private def organismDay : Input :=
  let checked := [susceptibilityExample, mycobacterialExample, seriesExample 3 5,
    yeastExample, mixedDrugExample, breathExample, lymphocyteExample, microscopySeriesExample]
  let day := confirmInactive base
    ["notice/D023-2/paragraph/1/i", "notice/D023-2/paragraph/4/i", "notice/D017/paragraph/2", "notice/D017/paragraph/4"]
  { day with
    rows := checked.map fun i => { i.performance with item := .individual i.performance.item }
    individualFacts := fun id => checked.find? (·.performance.id == id)
    individualStandalone := fun id => some ((checked.map (·.performance.id)).contains id)
    susceptibilitySpecies := fun id => if id == 1 then some [10, 20, 20] else none
    mycobacterialGroup := fun id => if id == 2 then some 3 else none
    mycobacterialReading := fun group => if group == 3 then some .pairwise else none
    seriesConfirmed := fun k => [5, 7, 8].contains k.identity }

example :
    (organismDay.withoutAdditions none).map Breakdown.execution =
      some [240, 315, 376, 165, 415, 70, 185, 100] ∧
      ({ organismDay with mycobacterialReading := fun _ => none }.prepare none).isNone ∧
      ({ organismDay with susceptibilitySpecies := fun _ => none }.prepare none).isNone := by decide

example : total organismDay none = some 2160 := by decide

example : (total microscopyAndPuncture none, total flowDay (some [5]), total sensitivityDay none) =
    (some 122, some 110, some 2710) := by decide

private theorem early_division_scopes :
    microscopyAndPuncture.Scope none ∧ flowDay.Scope (some [5]) ∧ sensitivityDay.Scope none := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    refine ⟨?_, _, _, _, rfl, rfl, ?_⟩
    · intro row member
      exact (List.all_eq_true (p := fun p : Performance Item => p.item.supported)).mp
        (by decide) row member
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

theorem microscopy_day_determines :
    ∃ r, microscopyAndPuncture.Permits none r ∧
      ∀ other, microscopyAndPuncture.Permits none other → other = r :=
  determines microscopyAndPuncture none early_division_scopes.1

theorem flow_day_determines :
    ∃ r, flowDay.Permits (some [5]) r ∧ ∀ other, flowDay.Permits (some [5]) other → other = r :=
  determines flowDay (some [5]) early_division_scopes.2.1

theorem sensitivity_day_determines :
    ∃ r, sensitivityDay.Permits none r ∧ ∀ other, sensitivityDay.Permits none other → other = r :=
  determines sensitivityDay none early_division_scopes.2.2

private theorem additional_division_scopes :
    markerDay.Scope none ∧ (registeredGroupsDay 99).Scope (some [20, 33, 70, 90, 91, 93]) := by
  constructor
  all_goals
    refine ⟨?_, _, _, _, rfl, rfl, ?_⟩
    · intro row member
      exact (List.all_eq_true (p := fun p : Performance Item => p.item.supported)).mp
        (by decide) row member
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

theorem marker_day_determines :
    ∃ r, markerDay.Permits none r ∧ ∀ other, markerDay.Permits none other → other = r :=
  determines markerDay none additional_division_scopes.1

theorem registered_day_determines :
    let day := registeredGroupsDay 99
    let selected := some [20, 33, 70, 90, 91, 93]
    ∃ r, day.Permits selected r ∧ ∀ other, day.Permits selected other → other = r :=
  determines (registeredGroupsDay 99) _ additional_division_scopes.2

private theorem organism_day_scope : organismDay.Scope none := by
  refine ⟨?_, _, _, _, rfl, rfl, ?_⟩
  · exact fun _ membership => List.all_eq_true.mp (by decide :
      organismDay.rows.all (fun p => p.item.supported) = true) _ membership
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

theorem organism_day_determines :
    ∃ r, organismDay.Permits none r ∧ ∀ other, organismDay.Permits none other → other = r :=
  determines organismDay none organism_day_scope

example :
    let c := rawDifferential 1
    (({ c with outsideSelection := fun _ => none }.prepare (some [1])).isNone,
      (c.prepare (some [2])).isNone,
      total c (some [1])) = (true, true, some 405) := by decide


end

end Sanri.MedicalFee.SpecimenRawDay
