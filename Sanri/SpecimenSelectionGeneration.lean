import Sanri.SpecimenSelectionInventory

namespace Sanri.MedicalFee.SpecimenSelectionGeneration

open Sanri.History Sanri.Logic SpecimenSelectionInventory

/-- 未確定の適用単位について、比較する読みを明示する。 -/
inductive Reading where
  | simultaneous | specimen | draw | day
  deriving DecidableEq

def Reading.unit : Reading → UnitKind
  | .simultaneous => .simultaneous
  | .specimen => .specimen
  | .draw => .draw
  | .day => .day

inductive Pending where
  | emptyMembers | externalMember | additionalConditions
  | unknownCardinality | unknownDirection | unsupportedUnit
  | missingReading | missingHistory | missingIdentity
  | excludedFromRegistration | missingCondition | repeatedGroupMember
  deriving DecidableEq, Repr

inductive Direction where
  | principal
  | retain (key : ItemKey)
  deriving DecidableEq

/-- 算定側は構成項目の並びと独立に指定する。 -/
def direction (g : Entry) : Option Direction :=
  match g.directed with
  | some false => some .principal
  | some true =>
    match g.id with
    | "notice/D007/paragraph/9" => some (.retain ("D007", "ketoneFractions"))
    | "notice/D007/paragraph/12" => some (.retain ("D007", "bloodGas"))
    | _ => none
  | none => none

/-- 項目対の索引だけで発動を決められると確認した部分を選ぶ。
それ以外の群は区分別の追加条件・射影の確認を要する。 -/
def mode (g : Entry) : Except Pending (Nat × Nat × Direction) := do
  if g.members.isEmpty then throw .emptyMembers
  if g.members.any (fun key => ["N002", "N004", "N005", "N005-2", "D313", "D419"].contains key.1) then throw .externalMember
  if g.outsideReason.isSome then throw .excludedFromRegistration
  let some (minimum, limit) := g.cardinality | throw .unknownCardinality
  let some ruleDirection := direction g | throw .unknownDirection
  return (minimum, limit, ruleDirection)

abbrev Row := Performance ItemKey

def members (g : Entry) (rows : List Row) : List Row :=
  rows.filter fun row => g.members.contains row.item

/-- キーの先頭は患者と医療機関。暦月と暦日は別の単位として扱う。 -/
def unitKey (unit : UnitKind) (row : Row) : Option (List Nat) :=
  let date := row.site.date
  let localKey := match unit with
    | .simultaneous => row.simultaneous.map (· :: [])
    | .specimen => row.specimen.map (· :: [])
    | .draw => row.draw.map (· :: [])
    | .series => row.series.map (· :: [])
    | .day => some [date.month.year, date.month.index.val, date.day.val]
    | .month => some [date.month.year, date.month.index.val]
    | _ => none
  localKey.map fun xs => row.site.patient :: row.site.institution :: xs

def resolveUnit (g : Entry) (read : String → Option Reading)
    (history : String → UnitKind → Bool) : Except Pending UnitKind := do
  match g.unit with
  | .unresolved =>
    let some reading := read g.id | throw .missingReading
    return reading.unit
  | .month | .series =>
    if history g.id g.unit then return g.unit else throw .missingHistory
  | .simultaneous | .specimen | .draw | .day => return g.unit
  | _ => throw .unsupportedUnit

def bucket (unit : UnitKind) (rows : List Row) (key : List Nat) : List Row :=
  rows.filter fun row => unitKey unit row == some key

structure Instance where
  members : List Row
  limit : Nat
  direction : Direction
  deriving DecidableEq

def Instance.Permits (g : Instance) (keep : Nat → Bool) : Prop :=
  (g.members.filter fun row => keep row.id).length ≤ g.limit ∧
    match g.direction with
    | .principal => True
    | .retain item => ∀ row ∈ g.members, keep row.id = (row.item == item)

def active (unit : UnitKind) (rows : List Row) (minimum : Nat) (key : List Nat) : Bool :=
  let group := bucket unit rows key
  !group.isEmpty && minimum ≤ group.length

def instances (unit : UnitKind) (rows : List Row) (minimum limit : Nat)
    (ruleDirection : Direction) : List Instance :=
  let keys := (rows.filterMap (unitKey unit)).eraseDups
  (keys.filter (active unit rows minimum)).map fun key =>
    ⟨bucket unit rows key, limit, ruleDirection⟩

def prepare (g : Entry) (rows : List Row) (read : String → Option Reading)
    (history : String → UnitKind → Bool) : Except Pending (Option (UnitKind × Nat × Nat × Direction)) := do
  let relevant := members g rows
  if relevant.isEmpty && !g.members.isEmpty then return none
  let (minimum, limit, ruleDirection) ← mode g
  let unit ← resolveUnit g read history
  if !relevant.all (fun row => (unitKey unit row).isSome) then throw .missingIdentity
  return some (unit, minimum, limit, ruleDirection)

/-- 月・一連では呼出し側が対象の全実施を渡し、その確認範囲を指定する。 -/
def generate (g : Entry) (rows : List Row) (read : String → Option Reading)
    (history : String → UnitKind → Bool := fun _ _ => false) : Except Pending (List Instance) := do
  match ← prepare g rows read history with
  | none => return []
  | some (unit, minimum, limit, ruleDirection) =>
    return instances unit (members g rows) minimum limit ruleDirection

/-- 異なる二種類以上と、条項が指定する起点がそろう場合だけ候補を作る。医学的適用条件は条項と実施IDの組に対して確認する。 -/
def generateRegistered (g : Entry) (rows : List Row) (read : String → Option Reading)
    (condition : String → List Nat → Option Bool) : Except Pending (List Instance) := do
  if g.dayRegistration.isNone then throw .excludedFromRegistration
  let relevant := members g rows
  let keys := (relevant.map Performance.item).eraseDups
  if keys.length < 2 || !(g.dayAnchor.all keys.contains) then return []
  let candidates ← generate g relevant read
  let groups ← candidates.filterM fun group => do
    let keys := group.members.map Performance.item
    if keys.eraseDups.length < 2 || !(g.dayAnchor.all keys.contains) then return false
    if g.dayRegistration == some .conditional then
      let some confirmed := condition g.id ((group.members.map Performance.id).mergeSort)
        | throw .missingCondition
      return confirmed
    else return true
  if !groups.all (fun group =>
      let keys := group.members.map Performance.item
      keys.eraseDups.length == keys.length) then throw .repeatedGroupMember
  return groups

/-- 確認済みの採否を上限制約と方向に照合する。 -/
def Instance.checkSelection (g : Instance) (keep : Nat → Option Bool) : Bool :=
  g.members.all (fun row => (keep row.id).isSome) &&
    (g.members.filter fun row => keep row.id == some true).length ≤ g.limit &&
    match g.direction with
    | .principal => true
    | .retain item => g.members.all fun row => keep row.id == some (row.item == item)

theorem checkSelection_sound (g : Instance) (keep : Nat → Option Bool)
    (checked : g.checkSelection keep = true) :
    g.Permits (fun id => keep id == some true) := by
  rcases g with ⟨rows, limit, direction⟩
  cases direction with
  | principal =>
    simp [Instance.checkSelection, Instance.Permits, Bool.and_eq_true] at checked ⊢
    exact checked.2
  | retain item =>
    simp only [Instance.checkSelection, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq] at checked
    refine ⟨checked.1.2, ?_⟩
    intro row member
    change (keep row.id == some true) = (row.item == item)
    rw [checked.2 row member]
    cases (row.item == item) <;> rfl

theorem prepare_perm (g : Entry) {rows other : List Row} (h : rows.Perm other) (read history) :
    prepare g rows read history = prepare g other read history := by
  have hp : (members g rows).Perm (members g other) := h.filter _
  rw [prepare, prepare, hp.isEmpty_eq]
  have all (unit : UnitKind) : (members g rows).all (fun row => (unitKey unit row).isSome) =
      (members g other).all (fun row => (unitKey unit row).isSome) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, hp.mem_iff]
  simp only [all]

/-- 群全体の上限と方向を、実施IDによる採否に適用する。 -/
def Permits (groups : List Instance) (keep : Nat → Bool) : Prop :=
  ∀ group ∈ groups, group.Permits keep

theorem instance_mem {unit rows minimum limit ruleDirection group} :
    group ∈ instances unit rows minimum limit ruleDirection ↔
      ∃ key, key ∈ rows.filterMap (unitKey unit) ∧ active unit rows minimum key = true ∧
        group = ⟨bucket unit rows key, limit, ruleDirection⟩ := by
  simp only [instances, List.mem_map, List.mem_filter, List.mem_eraseDups]
  constructor
  · rintro ⟨key, ⟨member, triggered⟩, rfl⟩
    exact ⟨key, member, triggered, rfl⟩
  · rintro ⟨key, member, triggered, rfl⟩
    exact ⟨key, ⟨member, triggered⟩, rfl⟩

theorem permits_iff {unit rows minimum limit ruleDirection} (keep : Nat → Bool) :
    Permits (instances unit rows minimum limit ruleDirection) keep ↔
      ∀ key ∈ rows.filterMap (unitKey unit), minimum ≤ (bucket unit rows key).length →
        (Instance.mk (bucket unit rows key) limit ruleDirection).Permits keep := by
  have present (key) (h : key ∈ rows.filterMap (unitKey unit)) :
      (bucket unit rows key).isEmpty = false := by
    obtain ⟨row, hr, hk⟩ := List.mem_filterMap.mp h
    have member : row ∈ bucket unit rows key := List.mem_filter.mpr ⟨hr, by simp [hk]⟩
    cases he : bucket unit rows key with
    | nil => simp [he] at member
    | cons => rfl
  simp only [Permits, instance_mem, active, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq]
  constructor
  · intro h key hk count
    exact h _ ⟨key, hk, ⟨present key hk, count⟩, rfl⟩
  · rintro h _ ⟨key, hk, ⟨_, count⟩, rfl⟩
    exact h key hk count

theorem principal_iff (rows : List Row) (limit : Nat) (keep : Nat → Bool) :
    (Instance.mk rows limit .principal).Permits keep ↔
      (rows.filter fun row => keep row.id).length ≤ limit := by
  simp [Instance.Permits]

theorem principal_exact_iff (rows : List Row) (limit : Nat) (keep : Nat → Bool) :
    (Instance.mk rows limit .principal).Permits keep ∧
      limit ≤ (rows.filter fun row => keep row.id).length ↔
    (rows.filter fun row => keep row.id).length = limit := by
  rw [principal_iff]
  omega

theorem principal_pairs_iff (rows : List Row) (keep : Nat → Bool) :
    (Instance.mk rows 1 .principal).Permits keep ↔
      (rows.map Performance.id).Pairwise (fun a b => keep a = true → keep b = false) := by
  rw [principal_iff, ← atMostOne_iff_pairwise, List.filter_map, List.length_map]
  rfl

theorem two_members_iff (left right : Row) (keep : Nat → Bool) :
    (Instance.mk [left, right] 1 .principal).Permits keep ↔
      (keep left.id = true → keep right.id = false) := by
  rw [principal_pairs_iff]
  simp

/-- 上限制約だけの重複では、どの成分でも空の採否が解になる。 -/
theorem principal_overlap_has_solution (groups : List Instance)
    (principal : ∀ group ∈ groups, group.direction = .principal) :
    Permits groups (fun _ => false) := by
  intro group member
  have empty : group.members.filter (fun _ => false) = [] := by
    exact List.filter_eq_nil_iff.mpr (by simp)
  simp [Instance.Permits, principal group member, empty]

theorem direction_iff (rows : List Row) (limit : Nat) (key : ItemKey) (keep : Nat → Bool)
    (bound : (rows.filter fun row => row.item == key).length ≤ limit) :
    (Instance.mk rows limit (.retain key)).Permits keep ↔
      ∀ row ∈ rows, keep row.id = (row.item == key) := by
  constructor
  · exact And.right
  · intro h
    have same : rows.filter (fun row => keep row.id) = rows.filter (fun row => row.item == key) :=
      List.filter_congr h
    exact ⟨same ▸ bound, h⟩

theorem instance_permits_perm {rows other : List Row} (h : rows.Perm other)
    (limit : Nat) (dir : Direction) (keep : Nat → Bool) :
    (Instance.mk rows limit dir).Permits keep ↔ (Instance.mk other limit dir).Permits keep := by
  unfold Instance.Permits
  rw [(h.filter _).length_eq]
  cases dir <;> simp only [h.mem_iff]

theorem instance_perm {unit rows other minimum limit dir group} (h : rows.Perm other)
    (member : group ∈ instances unit rows minimum limit dir) :
    ∃ found ∈ instances unit other minimum limit dir,
      group.members.Perm found.members ∧ group.limit = found.limit ∧ group.direction = found.direction := by
  obtain ⟨key, hk, ha, rfl⟩ := instance_mem.mp member
  have hp : (bucket unit rows key).Perm (bucket unit other key) := h.filter _
  have empty : (bucket unit rows key).isEmpty = (bucket unit other key).isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff]
    exact ⟨fun h => (h ▸ hp).nil_eq.symm, fun h => (h ▸ hp.symm).nil_eq.symm⟩
  exact ⟨_, instance_mem.mpr ⟨key, (h.filterMap _).mem_iff.mp hk,
    by simpa [active, ← empty, ← hp.length_eq] using ha, rfl⟩, hp, rfl, rfl⟩

theorem permits_perm {unit rows other minimum limit dir} (h : rows.Perm other) (keep) :
    Permits (instances unit rows minimum limit dir) keep ↔
      Permits (instances unit other minimum limit dir) keep := by
  have transfer {xs ys} (p : List.Perm xs ys)
      (valid : Permits (instances unit xs minimum limit dir) keep) :
      Permits (instances unit ys minimum limit dir) keep := by
    intro group hg
    obtain ⟨found, hf, hm, hl, hd⟩ := instance_perm p.symm hg
    obtain ⟨_, _, _⟩ := group
    obtain ⟨_, _, _⟩ := found
    cases hl
    cases hd
    exact (instance_permits_perm hm _ _ _).mpr (valid _ hf)
  exact ⟨transfer h, transfer h.symm⟩

theorem generate_perm (g : Entry) {rows other : List Row} (h : rows.Perm other)
    (read history) (keep : Nat → Bool) :
    match generate g rows read history, generate g other read history with
    | .error a, .error b => a = b
    | .ok a, .ok b => Permits a keep ↔ Permits b keep
    | _, _ => False := by
  unfold generate
  rw [prepare_perm g h]
  cases prepare g other read history with
  | error => rfl
  | ok result =>
    cases result with
    | none => exact Iff.rfl
    | some config =>
      obtain ⟨unit, minimum, limit, dir⟩ := config
      exact permits_perm (h.filter _) keep

theorem instances_of_shared_key (unit rows minimum limit dir key)
    (shared : ∀ row ∈ rows, unitKey unit row = some key) :
    instances unit rows minimum limit dir =
      if !rows.isEmpty && minimum ≤ rows.length then [⟨rows, limit, dir⟩] else [] := by
  have bucket_eq : bucket unit rows key = rows :=
    List.filter_eq_self.mpr fun row hm => by simp [shared row hm]
  have keys_eq : rows.filterMap (unitKey unit) = rows.map (fun _ => key) := by
    clear bucket_eq
    induction rows with
    | nil => rfl
    | cons row rest ih =>
      simp [shared row (by simp), ih (fun row hm => shared row (by simp [hm]))]
  cases rows with
  | nil => simp [instances]
  | cons row rest =>
    have keys : ((row :: rest).filterMap (unitKey unit)).eraseDups = [key] := by
      rw [keys_eq]
      simp only [List.map_cons, List.eraseDups_cons]
      have removed : (rest.map (fun _ => key)).filter (fun b => !b == key) = [] := by
        apply List.filter_eq_nil_iff.mpr
        simp
      rw [removed]
      rfl
    simp only [instances, keys, List.filter_cons, List.filter_nil, active, bucket_eq]
    split <;> simp [bucket_eq]

theorem readings_agree (rows : List Row) (minimum limit : Nat) (dir : Direction)
    (shared : ∀ r : Reading, ∃ key, ∀ row ∈ rows, unitKey r.unit row = some key)
    (a b : Reading) :
    instances a.unit rows minimum limit dir = instances b.unit rows minimum limit dir := by
  obtain ⟨ka, ha⟩ := shared a
  obtain ⟨kb, hb⟩ := shared b
  rw [instances_of_shared_key _ _ _ _ _ _ ha, instances_of_shared_key _ _ _ _ _ _ hb]

/-- 条項が起動し、課した上限と同じ件数の算定を要求する場合のD007算定条件。 -/
theorem chemistry_rules_iff (kind : SpecimenCrossDivision.ChemistryCombination)
    (rows : List (Performance BloodChemistry.Item)) (keep : Nat → Bool)
    (keys : BloodChemistry.Item → ItemKey)
    (activated : (match kind with
      | .calcium => BloodChemistry.calciumGroup
      | .ironBinding => BloodChemistry.ironBindingGroup
      | .cholesterol => BloodChemistry.cholesterolGroup
      | .protein => BloodChemistry.proteinGroup).all (rows.map Performance.item).contains = true)
    (onlyMembers : ∀ row ∈ rows, row.item ∈ (match kind with
      | .calcium => BloodChemistry.calciumGroup
      | .ironBinding => BloodChemistry.ironBindingGroup
      | .cholesterol => BloodChemistry.cholesterolGroup
      | .protein => BloodChemistry.proteinGroup)) :
    let (rule, limit) := match kind with
      | .calcium => (BloodChemistry.calciumRule, 1)
      | .ironBinding => (BloodChemistry.ironBindingRule, 1)
      | .cholesterol => (BloodChemistry.cholesterolRule, 2)
      | .protein => (BloodChemistry.proteinRule, 2)
    let charged := rows.filter (fun row => keep row.id)
    let indexed := rows.map fun row => ({ row with item := keys row.item } : Row)
    rule.holds (rows.map Performance.item) (charged.map Performance.item) ↔
      (Instance.mk indexed limit .principal).Permits keep ∧ limit ≤ charged.length := by
  have filtered {items : List BloodChemistry.Item}
      (only : ∀ row ∈ rows, row.item ∈ items) :
      ((rows.filter (fun row => keep row.id)).map Performance.item).filter items.contains =
        (rows.filter (fun row => keep row.id)).map Performance.item := by
    apply List.filter_eq_self.mpr
    intro item hi
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hi
    exact List.contains_iff_mem.mpr (only row (List.mem_filter.mp hr).1)
  cases kind <;>
    change (_ = true → (_ : List BloodChemistry.Item).length = _) ↔ _ <;>
    simp only [activated, true_implies, filtered onlyMembers, List.length_map,
      principal_iff, List.filter_map, Function.comp_def] <;> omega

end Sanri.MedicalFee.SpecimenSelectionGeneration
