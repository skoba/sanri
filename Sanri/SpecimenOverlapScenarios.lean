import Sanri.SpecimenSelectionInventory

namespace Sanri.MedicalFee.SpecimenSelectionInventory

open Sanri.Logic SpecimenCrossDivision

set_option maxRecDepth 4096

private def scenarioSource : SourceRef :=
  ⟨.manualInterpretation, "工程3a-4jの合成入力", "2026-10-22", "仮定した発動範囲", .unchecked, none⟩

private def oneEach (members : List (List Nat)) (required excluded : List Nat := []) :
    List (List Nat) :=
  (consistentSelections (members.map (fun ids => ⟨scenarioSource, ids, 1⟩))
    required excluded).map fun chosen =>
    (List.range (chosen.foldl max 0 + 1)).filter chosen.contains

/-- 群を一つずつ外した後の解数。変更対象は入力と同じ順に並ぶ。 -/
private def deletionCounts (members : List (List Nat)) (excluded : List Nat := []) : List Nat :=
  (List.range members.length).map fun i => (oneEach (members.eraseIdx i) [] excluded).length

/-- 1,2は尿沈渣2方式、3,4はD017の候補、5は関節液。
二件群をすべて一件必須と読む場合と、尿沈渣とD017をまとめて読む場合。 -/
theorem sediment_joint_component :
    let triangle := [[1, 2], [1, 3], [2, 3]]
    let other := [[3, 4], [4, 5]]
    oneEach (triangle ++ other) = [] ∧
    deletionCounts (triangle ++ other) = [2, 2, 2, 0, 0] ∧
    (oneEach ([[1, 2, 3]] ++ other)).isPerm [[1, 4], [2, 4], [3, 5]] ∧
    (oneEach ([[1, 2]] ++ other)).isPerm [[1, 4], [2, 4], [1, 3, 5], [2, 3, 5]] :=
  by decide

/-- EGFRの同月群と、同じ候補に実際に発動する併施群を独立に固定する。
別の目的のRAS・BRCA経路は別の合成入力で確認する。 -/
theorem tumor_gene_component :
    -- 1＝D004-2、2＝D006-12、3＝D006-24
    (oneEach [[1, 2, 3], [1, 3]]).isPerm [[1], [3]] ∧
    (oneEach [[1, 2, 3], [1, 2], [1, 3]]).isPerm [[1]] ∧
    -- 1＝D004-2、4＝D006-22、5＝D006-27のRAS
    (oneEach [[1, 4], [4, 5]]).isPerm [[4], [1, 5]] ∧
    -- 1＝D004-2、2,3＝同月の造血器側、4＝BRCA腫瘍細胞、5＝MSI
    (oneEach [[1, 2, 3], [1, 4], [4, 5]]).isPerm [[1, 5], [2, 4], [3, 4]] ∧
    -- D006-27のNTRKとMSIが共通のBRCA候補を持つ場合
    (oneEach [[1, 2], [2, 3]]).isPerm [[2], [1, 3]] :=
  by decide

/-- D007(30)(40)イ(41)イ(42)イ(43)ウを一件ずつと読む。
実施ID 1〜8はIV型、7S、P-III-P、ヒアルロン酸、Mac-2、オートタキシン、CK-18F、ELF。
ELFの構成費用を別に立てない(43)イを加えた場合も調べる。 -/
theorem liver_fibrosis_component :
    let core := [[1, 2, 3, 5], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7]]
    let groups := core ++ [[1, 2, 5, 6, 7, 8]]
    (oneEach groups).isPerm [[1], [2], [5], [3, 8]] ∧
    (oneEach groups [] [3, 4]).isPerm [[1], [2], [5]] ∧
    (oneEach core [8]).isPerm [[1, 8], [2, 8], [3, 8], [5, 8]] :=
  by decide

/-- 1,2はPCT定量・半定量、3はエンドトキシン、4はプレセプシン。
(47)(48)イを各条項で一群とする読みと、二件群に展開する読みを比較する。 -/
theorem sepsis_component :
    let triples := [[1, 3], [1, 4], [3, 4]]
    let bothMethods := [[1, 3], [2, 3], [1, 4], [2, 4], [3, 4]]
    (oneEach [[1, 3], [1, 3, 4]]).isPerm [[1], [3]] ∧
    (oneEach [[1, 2, 3], [1, 2, 3, 4]]).isPerm [[1], [2], [3]] ∧
    oneEach triples = [] ∧ deletionCounts triples = [2, 2, 2] ∧
    oneEach bothMethods = [] ∧ deletionCounts bothMethods = [0, 0, 0, 0, 2] :=
  by decide

/-- 1,2,3は同一目的の核酸・抗原・通常培養、4は別部位の通常培養、
5は同一起因菌の別の部位、6は通常培養と同じ検体の簡易培養。
方向付きの簡易培養除外と、各群の「主たるもの」の必要件数を区別する。 -/
theorem culture_component :
    let pairs := [[1, 2], [2, 3], [1, 3], [1, 5]]
    (oneEach [[1, 2], [1, 3, 4], [1, 5]] [] [6]).isPerm [[1], [2, 3, 5], [2, 4, 5]] ∧
    (oneEach [[1, 2], [2, 3], [1, 5]] [] [6]).isPerm [[1, 3], [2, 5]] ∧
    oneEach pairs [] [6] = [] ∧ deletionCounts pairs [6] = [2, 2, 2, 0] :=
  by decide

private def respiratoryClauses : List String :=
  ["notice/D012/paragraph/2", "notice/D012/paragraph/23", "notice/D012/paragraph/31/i",
   "notice/D012/paragraph/43/i", "notice/D012/paragraph/47/i", "notice/D012/paragraph/53/i",
   "notice/D012/paragraph/54/i", "notice/D023/paragraph/36/i", "notice/D023/paragraph/37/e",
   "notice/D023/paragraph/37/e/u", "notice/D023/paragraph/37/u", "notice/D023/paragraph/37/u/ko"]

def respiratoryInventory : List Entry :=
  inventory.filter fun g => respiratoryClauses.contains g.id

theorem respiratory_component_size : respiratoryInventory.length = 12 := by decide

/-- 12群から、発動・対象を確認して上限一件を課す群だけを射影する。
相手側の非別算定だけを求める条項には、必要なら別の方向付き条件を課す。 -/
def respiratoryUpperGroups (active : String → Bool) (inScope : String → ItemKey → Bool) :
    List (List Nat) :=
  (respiratoryInventory.filter (active ∘ Entry.id)).map fun entry =>
    (List.range indexedItems.length).filter fun i =>
      (indexedItems[i]?).any fun item => entry.members.contains item && inScope entry.id item

private theorem respiratory_distinct (active : String → Bool) (inScope : String → ItemKey → Bool)
    (group : List Nat) (member : group ∈ respiratoryUpperGroups active inScope) : group.Nodup := by
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  exact (List.nodup_range).filter _

/-- 上限・主検査の存在・方向付き非別算定が指定された読みの解集合。 -/
theorem respiratory_component (active : String → Bool) (inScope : String → ItemKey → Bool)
    (keep : Nat → Bool) (required : List (List Nat)) (excluded : List (Nat × Nat)) :
    let groups := respiratoryUpperGroups active inScope
    let nonempty := ∀ g ∈ required, ∃ a ∈ g, keep a = true
    let directed := ∀ pair ∈ excluded, keep pair.1 = true → keep pair.2 = false
    ((∀ group ∈ groups, (group.filter keep).length ≤ 1) ∧ nonempty ∧ directed) ↔
      (∀ a b, coMembers groups a b → keep a = true → keep b = false) ∧ nonempty ∧ directed := by
  dsimp only
  rw [atMostOne_groups_iff_independent _ _ (respiratory_distinct active inScope)]

end Sanri.MedicalFee.SpecimenSelectionInventory
