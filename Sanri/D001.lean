import Sanri.D008
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D001

open Sanri.Logic Sanri.History UrineFecalTests

inductive Screening where
  | ferricChloride | mucopolysaccharides | sulfhydrylCompounds | histidine
  | methylmalonicAcid | millon | isatin | benedict
  deriving DecidableEq

inductive PorphyriaReaction where
  | watsonSchwartz | rimington | deanBarnes
  deriving DecidableEq

inductive KidneyStage where
  | first | second | other
  deriving DecidableEq

inductive AkiPhase where
  | diagnosis | treatment
  deriving DecidableEq

structure Context where
  performance : Performance UrineSpecial
  /-- 医学的所見と測定法には確認した事実を渡す。 -/
  screening : Option Screening := none
  porphyriaReaction : Option PorphyriaReaction := none
  diabetesOrEarlyNephropathy : Prop := False
  suspectedMicroalbuminuria : Prop := False
  stage : Option KidneyStage := none
  trypsinogenImmunochromatography : Prop := False
  /-- mg/dLで表す。 -/
  fastingGlucose : Option Rat := none
  glucoseToleranceDiagnosticAid : Prop := False
  diabetesDiagnosisExcluded : Prop := False
  ulcerativeColitisMonitoringUrineCleia : Prop := False
  recurrentStonesCapillaryElectrophoresis : Prop := False
  medicallyNecessaryMonthlyPge : Prop := False
  justifiedOxalateException : Prop := False
  medicallyNecessaryExtraLfabp : Prop := False
  akiPhase : Option AkiPhase := none
  ngalUrineClia : Prop := False
  medicallyNecessaryExtraNgal : Prop := False
  /-- 各枠の起算と履歴の帰属を確認し、現候補を除く。 -/
  threeMonthWindow : Option Period := none
  annualWindow : Option Period := none
  akiWindow : Option Period := none
  history : Option (ClaimHistory (UrineSpecial × Option AkiPhase)) := none
  /-- 指定された相手との群が確認済みで、候補を排除する主検査がない。 -/
  renalSimultaneousSelection : Prop := False
  pancreaticSelection : Prop := False
  colitisMonthlySelection : Prop := False
  lfabpNgalSelection : Prop := False
  reference : Option ReferenceResolution := none
  /-- 尿蛋白・クレアチニン比を試験紙で測る実施であることの確認。 -/
  stripProteinCreatinineRatio : Prop := False
  referenceChemistryItem : Option BloodChemistry.Item := none

def ItemNumber : UrineSpecial → Nat
  | .protein => 1
  | .vmaQualitative | .glucose => 2
  | .urobilinogen | .congenitalMetabolicScreening | .osmolality => 3
  | .porphyriaScreening => 4
  | .nag => 5
  | .albuminQualitative => 6
  | .lhQualitative => 7
  | .fdp => 8
  | .transferrin => 9
  | .albuminQuantitative => 10
  | .uroporphyrin | .trypsinogen2 => 11
  | .deltaAla => 12
  | .polyamines => 13
  | .myoinositol => 14
  | .coproporphyrin => 15
  | .typeIVCollagen => 16
  | .totalIodine | .porphobilinogen => 17
  | .prostaglandinEMajorMetabolite => 18
  | .oxalate => 19
  | .lFabp | .ngal => 20
  | .proteinImmunology => 21
  | .other _ => 22

private def primary (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    loc, .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def fixedItem (n points : Nat) : Rule Context Nat :=
  ⟨"primary/D001/item/" ++ toString n,
    primary ((if n ≤ 3 then "PDF173頁" else "PDF174頁") ++ " D001 " ++ toString n),
    fun c p => ItemNumber c.performance.item = n → p = points⟩

def proteinReference : Rule Context Nat :=
  ⟨"primary/D001/item/21", primary "PDF174頁 D001 21", fun c p =>
    c.performance.item = .proteinImmunology →
      ∃ r, c.reference = some r ∧ r.target = .d015 ∧ p = r.points⟩

def otherReference : Rule Context Nat :=
  ⟨"primary/D001/item/22", primary "PDF174頁 D001 22", fun c p =>
    ∀ target, c.performance.item = .other target →
      ∃ r, c.reference = some r ∧ r.target = .other target ∧ p = r.points⟩

def otherReferenceNote : Rule Context Nat :=
  ⟨"primary/D001/item/22/note", primary "PDF174頁 D001 22 注", fun c _ =>
    ∀ target, c.performance.item = .other target →
      ∃ r, c.reference = some r ∧ r.sectionNotesAppliedAndSatisfied = true⟩

def primaryRules : List (Rule Context Nat) :=
  [fixedItem 1 7, fixedItem 2 9, fixedItem 3 16, fixedItem 4 17, fixedItem 5 41,
   fixedItem 6 49, fixedItem 7 72, fixedItem 8 77, fixedItem 9 98, fixedItem 10 99,
   fixedItem 11 105, fixedItem 12 106, fixedItem 13 115, fixedItem 14 120, fixedItem 15 131,
   fixedItem 16 179, fixedItem 17 186, fixedItem 18 187, fixedItem 19 200, fixedItem 20 210,
   proteinReference, otherReference, otherReferenceNote]

private def WithinClaims (c : Context) (window : Option Period)
    (accepts : UrineSpecial × Option AkiPhase → Bool)
    (maximumPrior : Nat) : Prop :=
  ∃ h p, c.history = some h ∧ window = some p ∧ p.Contains c.performance.site.date ∧
    withinLimit h ⟨c.performance.site.patient, none, p⟩ accepts maximumPrior = some true

def Within (c : Context) (window : Option Period) (accepts : UrineSpecial → Bool)
    (maximumPrior : Nat) : Prop :=
  WithinClaims c window (fun claim => accepts claim.1) maximumPrior

def RenalItem (t : UrineSpecial) : Prop :=
  t = .transferrin ∨ t = .albuminQuantitative ∨ t = .typeIVCollagen

def renalItem (t : UrineSpecial) : Bool :=
  t == .transferrin || t == .albuminQuantitative || t == .typeIVCollagen

private def condition (id loc : String) (holds : Context → Prop) : Rule Context Nat :=
  ⟨"notice/D001/paragraph/" ++ id, notice loc, fun c _ => holds c⟩

def screeningRule : Rule Context Nat :=
  condition "1" "PDF331頁 D001(1)" fun c =>
    c.performance.item = .congenitalMetabolicScreening → c.screening.isSome = true

def screeningBranch (s : Screening) : Rule Context Nat :=
  let (id, label) := match s with
    | .ferricChloride => ("a", "ア")
    | .mucopolysaccharides => ("i", "イ")
    | .sulfhydrylCompounds => ("u", "ウ")
    | .histidine => ("e", "エ")
    | .methylmalonicAcid => ("o", "オ")
    | .millon => ("ka", "カ")
    | .isatin => ("ki", "キ")
    | .benedict => ("ku", "ク")
  ⟨"notice/D001/paragraph/1/" ++ id, notice ("PDF331頁 D001(1)" ++ label), fun c p =>
    c.performance.item = .congenitalMetabolicScreening → c.screening = some s → p = 16⟩

def porphyriaRule : Rule Context Nat :=
  condition "2" "PDF331頁 D001(2)" fun c =>
    c.performance.item = .porphyriaScreening → c.porphyriaReaction.isSome = true

def renalRule : Rule Context Nat :=
  condition "3" "PDF331頁 D001(3)" fun c =>
    RenalItem c.performance.item →
      c.diabetesOrEarlyNephropathy ∧ c.suspectedMicroalbuminuria ∧
      (c.stage = some .first ∨ c.stage = some .second) ∧
      Within c c.threeMonthWindow renalItem 0 ∧ c.renalSimultaneousSelection

def trypsinogenRule : Rule Context Nat :=
  condition "4/a" "PDF331–332頁 D001(4)ア" fun c =>
    c.performance.item = .trypsinogen2 → c.trypsinogenImmunochromatography

def pancreaticRule : Rule Context Nat :=
  condition "4/i" "PDF332頁 D001(4)イ" fun c =>
    c.performance.item = .trypsinogen2 → c.pancreaticSelection

def myoinositolRule : Rule Context Nat :=
  condition "5" "PDF332頁 D001(5)" fun c =>
    c.performance.item = .myoinositol →
      (∃ glucose, c.fastingGlucose = some glucose ∧ 110 ≤ glucose ∧ glucose < 126) ∧
      c.glucoseToleranceDiagnosticAid ∧ c.diabetesDiagnosisExcluded ∧
      Within c c.annualWindow (· == .myoinositol) 0

def monthlyPge (c : Context) : Prop :=
  c.medicallyNecessaryMonthlyPge ∧
    Within c (some (Period.month c.performance.site.date.month)) (· == .prostaglandinEMajorMetabolite) 0

def pgeRule : Rule Context Nat :=
  condition "6/a" "PDF332頁 D001(6)ア" fun c =>
    c.performance.item = .prostaglandinEMajorMetabolite →
      c.ulcerativeColitisMonitoringUrineCleia ∧
      (Within c c.threeMonthWindow (· == .prostaglandinEMajorMetabolite) 0 ∨ monthlyPge c)

def colitisRule : Rule Context Nat :=
  condition "6/i" "PDF332頁 D001(6)イ" fun c =>
    c.performance.item = .prostaglandinEMajorMetabolite → c.colitisMonthlySelection

def oxalateRule : Rule Context Nat :=
  condition "7" "PDF332頁 D001(7)" fun c =>
    c.performance.item = .oxalate → c.recurrentStonesCapillaryElectrophoresis ∧
      (Within c c.annualWindow (· == .oxalate) 0 ∨ c.justifiedOxalateException)

def lfabpRule : Rule Context Nat :=
  condition "8" "PDF332頁 D001(8)" fun c =>
    c.performance.item = .lFabp →
      (Within c c.threeMonthWindow (· == .lFabp) 0 ∨ c.medicallyNecessaryExtraLfabp)

private def AkiHistoryClassified (c : Context) : Prop :=
  ∃ history, c.history = some history ∧
    ∀ entry ∈ history.entries, entry.item.1 = .ngal → entry.item.2.isSome = true

def ngalNormalFrequency (c : Context) : Prop :=
  AkiHistoryClassified c ∧
    ((c.akiPhase = some .diagnosis ∧ WithinClaims c c.akiWindow (· == (.ngal, some .diagnosis)) 0) ∨
      (c.akiPhase = some .treatment ∧ WithinClaims c c.akiWindow (· == (.ngal, some .treatment)) 2))

def ngalRule : Rule Context Nat :=
  condition "9/a" "PDF332頁 D001(9)ア" fun c =>
    c.performance.item = .ngal → c.ngalUrineClia ∧ c.akiPhase.isSome = true ∧
      (ngalNormalFrequency c ∨ c.medicallyNecessaryExtraNgal)

def lfabpNgalRule : Rule Context Nat :=
  condition "9/i" "PDF332頁 D001(9)イ" fun c =>
    (c.performance.item = .lFabp ∨ c.performance.item = .ngal) → c.lfabpNgalSelection

def stripRatioRule : Rule Context Nat :=
  condition "11" "PDF332–333頁 D001(11)" fun c =>
    c.stripProteinCreatinineRatio →
      c.performance.item = .other .d007 ∧ c.referenceChemistryItem = some .creatinine

def judgmentTest (c : Context) : SpecimenJudgment.Test :=
  { major := 1, number := ItemNumber c.performance.item, ordinaryCategory := .urineFecal }

/-- 個別点数とは別に、確認済み同日群への配分を制約する。 -/
def sameDayBundleRule (Test : Type) : Rule (D004.SameDayBundle Test) (List (List Test)) :=
  ⟨"notice/D001/paragraph/10", notice "PDF332頁 D001(10)", fun c groups =>
    groups = (c.urine ++ c.puncture ++ c.firstBloodDraw) :: c.laterBloodDraws⟩

/-- D007とD008で共用する同日群の分割を、各区分の包括評価へ渡す。 -/
theorem sameDay_groups (d : D004.SameDayBundle Test) (groups : List (List Test)) :
    (sameDayBundleRule Test).holds d groups ↔ (D004.sameDayBundleRule Test).holds d groups :=
  Iff.rfl

def chemistryBundlePoints (d : D004.SameDayBundle BloodChemistry.Item) (points : List Nat) : Prop :=
  ∃ groups, (sameDayBundleRule BloodChemistry.Item).holds d groups ∧
    points = groups.map BloodChemistry.pointsForItems

theorem chemistry_bundle_iff (d : D004.SameDayBundle BloodChemistry.Item) (points : List Nat) :
    chemistryBundlePoints d points ↔ D004.d007BundlePoints d points := Iff.rfl

def endocrineBundlePoints (d : D008.SameDay) (points : List Nat) : Prop :=
  ∃ groups, (sameDayBundleRule D008.BundleItem).holds d groups ∧
    points = groups.map D008.bundlePoints

theorem endocrine_bundle_iff (d : D008.SameDay) (points : List Nat) :
    endocrineBundlePoints d points ↔ D008.sameDayPoints d points := by
  rw [D008.sameDay_iff]
  constructor
  · rintro ⟨groups, h, rfl⟩
    cases h
    rfl
  · intro h
    exact ⟨_, rfl, h⟩

structure Documentation where
  pancreaticGroundsInClaim : Prop
  pgeReasonAndResultInChartAndClaim : Prop
  lfabpReasonInClaim : Prop
  ngalReasonInClaim : Prop

def documentationMet (c : Context) (d : Documentation) : Prop :=
  (c.performance.item = .trypsinogen2 → d.pancreaticGroundsInClaim) ∧
  (c.performance.item = .prostaglandinEMajorMetabolite →
    ¬ Within c c.threeMonthWindow (· == .prostaglandinEMajorMetabolite) 0 →
      d.pgeReasonAndResultInChartAndClaim) ∧
  (c.performance.item = .lFabp → ¬ Within c c.threeMonthWindow (· == .lFabp) 0 → d.lfabpReasonInClaim) ∧
  (c.performance.item = .ngal → ¬ ngalNormalFrequency c → d.ngalReasonInClaim)

/-- 通知の見出し段落が束ねる枝。枝自体にもそれぞれの出典位置を付ける。 -/
def trypsinogenParagraph : Rule Context Nat :=
  condition "4" "PDF331–332頁 D001(4)" fun c =>
    trypsinogenRule.holds c 0 ∧ pancreaticRule.holds c 0

def pgeParagraph : Rule Context Nat :=
  condition "6" "PDF332頁 D001(6)" fun c => pgeRule.holds c 0 ∧ colitisRule.holds c 0

def ngalParagraph : Rule Context Nat :=
  condition "9" "PDF332頁 D001(9)" fun c => ngalRule.holds c 0 ∧ lfabpNgalRule.holds c 0

def conditions :=
  [screeningRule, porphyriaRule, renalRule, trypsinogenRule, pancreaticRule, myoinositolRule,
   pgeRule, colitisRule, oxalateRule, lfabpRule, ngalRule, lfabpNgalRule, stripRatioRule,
   trypsinogenParagraph, pgeParagraph, ngalParagraph]

def screeningBranches :=
  [screeningBranch .ferricChloride, screeningBranch .mucopolysaccharides,
   screeningBranch .sulfhydrylCompounds, screeningBranch .histidine,
   screeningBranch .methylmalonicAcid, screeningBranch .millon,
   screeningBranch .isatin, screeningBranch .benedict]

def rules := primaryRules ++ conditions ++ screeningBranches

def legacyInput (c : Context) : UrineFecalTests.Context :=
  { item := .specialUrine c.performance.item, referenceResolution := c.reference }

/-- D007への準用に属する尿の実施を確認済みの同日群に結び付ける。 -/
def ChemistryBundleReference (c : Context) (d : D004.SameDayBundle BloodChemistry.Item) : Prop :=
  c.performance.item = .other .d007 ∧ c.performance.site = d.site ∧
    ∃ item ∈ d.urine, c.referenceChemistryItem = some item

/-- D008の具体的な準用先と尿の実施は呼出側で同定する。 -/
def EndocrineBundleReference (c : Context) (test : D008.Context) (d : D008.SameDay) : Prop :=
  c.performance.site = test.performance.site ∧
    D008.D001Reference (legacyInput { c with reference := none }) test d

set_option maxHeartbeats 1200000 in
theorem primary_iff (c : Context) (p : Nat) :
    Satisfies primaryRules c p ↔ assess (legacyInput c) = some (.charged ⟨p, 0⟩) := by
  cases h : c.performance.item with
  | proteinImmunology =>
    cases hr : c.reference with
    | none => simp [Satisfies, primaryRules, fixedItem, proteinReference, otherReference,
        otherReferenceNote, ItemNumber, h, hr, legacyInput, assess, requiresInHouse, isSediment, pointRule, urineSpecialPointRule]
    | some r =>
      simp [Satisfies, primaryRules, fixedItem, proteinReference, otherReference,
        otherReferenceNote, ItemNumber, h, hr, legacyInput, assess, requiresInHouse, isSediment, pointRule, urineSpecialPointRule,
        and_comm] <;> omega
  | other target =>
    cases hr : c.reference with
    | none => simp [Satisfies, primaryRules, fixedItem, proteinReference, otherReference,
        otherReferenceNote, ItemNumber, h, hr, legacyInput, assess, requiresInHouse, isSediment, pointRule, urineSpecialPointRule]
    | some r =>
      by_cases ht : r.target = .other target <;> cases hn : r.sectionNotesAppliedAndSatisfied <;>
        simp [Satisfies, primaryRules, fixedItem, proteinReference, otherReference,
          otherReferenceNote, ItemNumber, h, hr, ht, hn, legacyInput, assess, requiresInHouse, isSediment, pointRule, urineSpecialPointRule] <;> omega
  | _ =>
    simp [Satisfies, primaryRules, fixedItem, proteinReference, otherReference, otherReferenceNote,
      ItemNumber, h, legacyInput, assess, requiresInHouse, isSediment, pointRule, urineSpecialPointRule] <;> omega

def ReferenceResolved (c : Context) : Prop :=
  match c.performance.item with
  | .proteinImmunology => ∃ r, c.reference = some r ∧ r.target = .d015
  | .other target => ∃ r, c.reference = some r ∧ r.target = .other target ∧
      r.sectionNotesAppliedAndSatisfied = true
  | _ => True

def Eligible (c : Context) : Prop :=
  Satisfies conditions c 0 ∧ ReferenceResolved c

private theorem resolved_has_points (c : Context) (h : ReferenceResolved c) :
    ∃ p, assess (legacyInput c) = some (.charged ⟨p, 0⟩) := by
  cases hi : c.performance.item with
  | proteinImmunology =>
    obtain ⟨r, hr, ht⟩ := show ∃ r, c.reference = some r ∧ r.target = .d015 from
      by simpa [ReferenceResolved, hi] using h
    exact ⟨r.points, by simp [legacyInput, assess, hi, hr, ht, requiresInHouse, isSediment,
      pointRule, urineSpecialPointRule]⟩
  | other target =>
    obtain ⟨r, hr, ht, hn⟩ := show ∃ r, c.reference = some r ∧ r.target = .other target ∧
        r.sectionNotesAppliedAndSatisfied = true from by simpa [ReferenceResolved, hi] using h
    exact ⟨r.points, by simp [legacyInput, assess, hi, hr, ht, hn, requiresInHouse, isSediment,
      pointRule, urineSpecialPointRule]⟩
  | _ => exact ⟨_, by simp [legacyInput, assess, hi, requiresInHouse, isSediment, pointRule,
      urineSpecialPointRule] <;> rfl⟩

theorem satisfies_iff (c : Context) (p : Nat) :
    Satisfies rules c p ↔ Satisfies conditions c 0 ∧
      assess (legacyInput c) = some (.charged ⟨p, 0⟩) := by
  have independent : Satisfies conditions c p ↔ Satisfies conditions c 0 := by
    simp [Satisfies, conditions, screeningRule, porphyriaRule, renalRule, trypsinogenRule,
      pancreaticRule, myoinositolRule, pgeRule, colitisRule, oxalateRule, lfabpRule,
      ngalRule, lfabpNgalRule, stripRatioRule, trypsinogenParagraph, pgeParagraph, ngalParagraph, condition]
  constructor
  · intro h
    exact ⟨independent.mp (fun r hr => h r (by simp [rules, hr])),
      (primary_iff c p).mp (fun r hr => h r (by simp [rules, hr]))⟩
  · rintro ⟨hc, hp⟩ r hr
    have hprimary := (primary_iff c p).mpr hp
    simp only [rules, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hprimary r hr
    · exact independent.mpr hc r hr
    · have hscreen : c.performance.item = .congenitalMetabolicScreening → p = 16 :=
        hprimary (fixedItem 3 16) (by simp [primaryRules]) ∘
          (fun eq => by simp [ItemNumber, eq])
      simp only [screeningBranches, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact fun hi _ => hscreen hi

theorem determines : DeterminesOn Eligible rules := by
  rintro c ⟨hc, resolved⟩
  obtain ⟨p, hp⟩ := resolved_has_points c resolved
  refine ⟨⟨p, (satisfies_iff ..).mpr ⟨hc, hp⟩⟩, ?_⟩
  intro a b ha hb
  have eq := ((satisfies_iff c a).mp ha).2.symm.trans ((satisfies_iff c b).mp hb).2
  simpa using eq

def toSpecimenItem (kind points : Nat) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := points }

private def sample : Context :=
  { performance := ⟨1, ⟨2, 3, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩, .protein, none, some 4, none, none⟩ }

example : Satisfies rules sample 7 := by
  apply (satisfies_iff ..).mpr
  constructor
  · simp [Satisfies, conditions, screeningRule, porphyriaRule, renalRule, trypsinogenRule,
      pancreaticRule, myoinositolRule, pgeRule, colitisRule, oxalateRule, lfabpRule,
      ngalRule, lfabpNgalRule, stripRatioRule, trypsinogenParagraph, pgeParagraph, ngalParagraph,
      condition, RenalItem, sample]
  · rfl

example : ¬ SatisfiableAt rules { sample with
    performance := { sample.performance with
    item := .myoinositol }, fastingGlucose := some 126 } := by
  rintro ⟨p, hp⟩
  have h := hp myoinositolRule (by simp [rules, conditions]) rfl
  obtain ⟨⟨g, hg, _, limit⟩, _⟩ := h
  simp at hg
  subst g
  exact (by decide : ¬ (126 : Rat) < 126) limit

end Sanri.MedicalFee.D001
