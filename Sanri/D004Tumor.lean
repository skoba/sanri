import Sanri.History
import Sanri.Logic
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D004Tumor

open Sanri.Logic Sanri.History

inductive Item where
  | drugAid | otherSimple | complex | sensitivity
  deriving DecidableEq, Repr

def Item.number : Item → Nat
  | .sensitivity => 2
  | _ => 1

def Item.points : Item → Nat
  | .drugAid | .sensitivity => 2500
  | .otherSimple => 2100
  | .complex => 5000

def ledgerItems : List Item := [.drugAid, .otherSimple, .complex, .sensitivity]

example : (ledgerItems.map Item.number).eraseDups = [1, 2] := by decide

inductive Assay where
  | egfr | ros1Fusion | alkFusion | braf | metEx14 | krasG12c | ras | her2 | msi
  | ezh2 | fgfr3 | kras | ewsFli1 | tlsChop | sytSsx | cKit | sentinelNode
  | retFusion | ntrkFusion | mutationBurden | fgfr2Fusion | idh1 | retMutation
  | akt1 | pik3ca | pten
  deriving DecidableEq, Repr

inductive Cancer where
  | lung | colorectal | breast | follicularLymphoma | urothelial | pancreas
  | boneSoftTissue | gist | melanoma | biliary | thyroid | medullaryThyroid
  | otherLymphoma | ovarianClearCell | otherOvarian | prostate | digestive
  | headNeck | pleuralOrPeritonealCarcinomatosis | cervix | uterineBody | otherSolid
  deriving DecidableEq, Repr

def Cancer.solid : Cancer → Bool
  | .follicularLymphoma | .otherLymphoma => false
  | _ => true

inductive Method where
  | realTimePCR | pcrRssO | multiplexFragmentPCR | ngs | pcr | sscp | rflp
  | otherSimpleConfirmed | otherComplexConfirmed | hdra | cdDst | other
  deriving DecidableEq, Repr

inductive Purpose where
  | tumorDiagnosisAndTreatmentSelection | lynchDiagnosticAid | solidCancerDrugSelection
  | earlyColorectalLynchExclusion | other
  deriving DecidableEq, Repr

structure ClaimKind where
  assay : Option Assay
  purpose : Purpose
  deriving DecidableEq, Repr

/-- 各段落の指定する範囲で関係検査を照会し、適用外または主たる検査であったかを確定する。 -/
inductive Combination where
  | alk | her2 | brca
  deriving DecidableEq, Repr

inductive OtherTest where
  | d004_2_1 | d006_2 | d006_6 | d006_12 | d006_14 | d006_16 | d006_18_1 | d006_24
  | n002_6 | n005 | n005_2
  deriving DecidableEq, Repr

structure Selection where
  other : OtherTest
  principalIsThisTest : Option Bool := none

/-- 同月内の実施を確認してから、関係する相手との主従を検査する。
医療機関をまたぐ照会範囲は上位の解釈で確定して渡す。 -/
structure MonthlySelection where
  survey : Snapshot (Performance OtherTest)
  scopeInstitution : Option Nat
  principal : OtherTest → Nat → Option Bool

def MonthlySelection.Allows (s : MonthlySelection) (site : Site)
    (counterparts : List OtherTest) : Prop :=
  ∃ performed, s.survey.select Performance.site
    ⟨site.patient, s.scopeInstitution, Period.month site.date.month⟩
    (fun p => counterparts.contains p.item) = some performed ∧
    (s.scopeInstitution = none ∨ s.scopeInstitution = some site.institution) ∧
    ∀ p ∈ performed, s.principal p.item p.id = some true

structure Context where
  performance : Performance Item
  cancer : Cancer
  assay : Option Assay := none
  method : Option Method := none
  purpose : Purpose := .other
  patientIsSubject : Option Bool := none
  tumorCells : Option Bool := none
  approvedReagent : Option Bool := none
  approvedDevice : Option Bool := none
  surgicalTissue : Option Bool := none
  cytotoxicDrug : Option Bool := none
  egfrSecondaryMutationSuspectedAfterProgression : Option Bool := none
  egfrTreatmentReselectionNeeded : Option Bool := none
  priorClaims : Option (ClaimHistory ClaimKind) := none
  lynchBrafWithKrasOrRas : Option Bool := none
  monthlySelection : Option MonthlySelection := none
  combinations : Combination → Option (List Selection) := fun _ => none

def Context.item (c : Context) : Item := c.performance.item

private def primary (locator : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF175頁 D004-2 " ++ locator, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (locator : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    "PDF335〜337頁 D004-2 " ++ locator, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

private def april (locator : String) : SourceRef :=
  ⟨.notification, "保医発0430第4号・別添2（05-18差替）", "2026-06-01適用",
    "PDF10頁 D004-2 " ++ locator, .checkedAgainstSource,
    some "https://kouseikyoku.mhlw.go.jp/kantoshinetsu/080525_016.pdf"⟩

private def may : SourceRef :=
  ⟨.notification, "保医発0529第2号・別添1", "2026-06-01適用",
    "PDF3頁 指示3 D004-2(4)エ", .checkedAgainstSource,
    some "https://kouseikyoku.mhlw.go.jp/kantoshinetsu/080608_009.pdf"⟩

private def condition (id : String) (applies : Context → Prop)
    (required : Context → Prop) : Rule Context Unit :=
  ⟨"notice/D004-2/paragraph/" ++ id, notice id, fun c _ => applies c → required c⟩

/-- 実施が該当する通知枝を列挙する。親段落で適用枝の存在を要求し、
枝の規則は選択された枝に固有の検査・がん種・測定法を要求する。 -/
inductive Branch where
  | drugLung | drugColorectal | drugBreast | drugMsi | drugLymphoma | drugUrothelial | drugNonLungAlk
  | simpleLung | simplePancreas | simpleSarcoma | simpleGist | simpleMelanoma | simpleColorectal | simpleLynch
  | complexLung | complexMelanoma | complexSolid | complexBiliary | complexThyroid
  | complexMedullary | complexSolidBraf | complexLymphoma | complexBreast | complexOvary
  deriving DecidableEq, Repr

structure Classified where
  test : Context
  branch : Option Branch

def Branch.item : Branch → Item
  | .drugLung | .drugColorectal | .drugBreast | .drugMsi | .drugLymphoma | .drugUrothelial
  | .drugNonLungAlk => .drugAid
  | .simpleLung | .simplePancreas | .simpleSarcoma | .simpleGist | .simpleMelanoma
  | .simpleColorectal | .simpleLynch => .otherSimple
  | _ => .complex

private def Context.measures (c : Context) (assays : List Assay) : Prop :=
  ∃ assay ∈ assays, c.assay = some assay

private def Context.uses (c : Context) (methods : List Method) : Prop :=
  ∃ method ∈ methods, c.method = some method

def Branch.conditions : Branch → Context → Prop
  | .drugLung => fun c => c.cancer = .lung ∧
      (c.measures [.egfr, .ros1Fusion, .alkFusion, .krasG12c] ∨
        (c.measures [.braf, .metEx14] ∧ c.uses [.realTimePCR, .pcrRssO, .multiplexFragmentPCR]))
  | .drugColorectal => fun c => c.cancer = .colorectal ∧ c.measures [.ras, .braf]
  | .drugBreast => fun c => c.cancer = .breast ∧ c.assay = some .her2
  | .drugMsi => fun c => c.cancer.solid = true ∧ c.assay = some .msi
  | .drugLymphoma => fun c => c.cancer = .follicularLymphoma ∧ c.assay = some .ezh2
  | .drugUrothelial => fun c => c.cancer = .urothelial ∧ c.assay = some .fgfr3
  | .drugNonLungAlk => fun c => c.cancer.solid = true ∧ c.cancer ≠ .lung ∧ c.assay = some .alkFusion
  | .simpleLung => fun c => c.cancer = .lung ∧ c.assay = some .kras
  | .simplePancreas => fun c => c.cancer = .pancreas ∧ c.assay = some .kras
  | .simpleSarcoma => fun c => c.cancer = .boneSoftTissue ∧ c.measures [.ewsFli1, .tlsChop, .sytSsx]
  | .simpleGist => fun c => c.cancer = .gist ∧ c.assay = some .cKit
  | .simpleMelanoma => fun c => c.cancer = .melanoma ∧ c.assay = some .sentinelNode
  | .simpleColorectal => fun c => c.cancer = .colorectal ∧ c.measures [.egfr, .kras]
  | .simpleLynch => fun c => c.purpose = .lynchDiagnosticAid ∧ c.assay = some .msi ∧
      c.approvedReagent = some false
  | .complexLung => fun c => c.cancer = .lung ∧
      (c.assay = some .retFusion ∨ (c.measures [.braf, .metEx14, .her2] ∧ c.method = some .ngs))
  | .complexMelanoma => fun c => c.cancer = .melanoma ∧ c.assay = some .braf ∧
      c.uses [.realTimePCR, .pcrRssO]
  | .complexSolid => fun c => c.cancer.solid = true ∧ c.measures [.ntrkFusion, .mutationBurden, .retFusion]
  | .complexBiliary => fun c => c.cancer = .biliary ∧ c.measures [.fgfr2Fusion, .idh1]
  | .complexThyroid => fun c => c.cancer = .thyroid ∧ c.measures [.retFusion, .braf]
  | .complexMedullary => fun c => c.cancer = .medullaryThyroid ∧ c.assay = some .retMutation
  | .complexSolidBraf => fun c => c.cancer.solid = true ∧ c.cancer ≠ .lung ∧ c.cancer ≠ .colorectal ∧
      c.assay = some .braf ∧ c.method = some .pcrRssO
  | .complexLymphoma => fun c => c.cancer.solid = false ∧ c.assay = some .braf ∧ c.method = some .pcrRssO
  | .complexBreast => fun c => c.cancer = .breast ∧ c.measures [.akt1, .pik3ca, .pten]
  | .complexOvary => fun c => c.cancer = .ovarianClearCell ∧ c.assay = some .pik3ca ∧ c.method = some .realTimePCR

def Branch.locator : Branch → String
  | .drugLung => "2/a" | .drugColorectal => "2/i" | .drugBreast => "2/u"
  | .drugMsi => "2/e" | .drugLymphoma => "2/o" | .drugUrothelial => "2/ka" | .drugNonLungAlk => "2/ki"
  | .simpleLung => "3/a" | .simplePancreas => "3/i" | .simpleSarcoma => "3/u"
  | .simpleGist => "3/e" | .simpleMelanoma => "3/o" | .simpleColorectal => "3/ka" | .simpleLynch => "3/ki"
  | .complexLung => "4/a" | .complexMelanoma => "4/i" | .complexSolid => "4/u"
  | .complexBiliary => "4/e" | .complexThyroid => "4/o" | .complexMedullary => "4/ka"
  | .complexSolidBraf => "4/ki" | .complexLymphoma => "4/ku" | .complexBreast => "4/ke"
  | .complexOvary => "4/ko"

def branchRule (b : Branch) : Rule Classified Unit :=
  ⟨"notice/D004-2/paragraph/" ++ b.locator,
    match b with
    | .drugNonLungAlk | .complexOvary => april b.locator
    | .complexBiliary => may
    | _ => notice b.locator,
    fun c _ => c.branch = some b → b.conditions c.test⟩

private def approval (c : Context) : Prop :=
  c.approvedReagent = some true ∨ c.approvedDevice = some true

def drugAidRule : Rule Classified Unit :=
  ⟨"notice/D004-2/paragraph/2", notice "(2)", fun c _ =>
    c.test.item = .drugAid →
      (∃ b, c.branch = some b ∧ b.item = .drugAid) ∧ approval c.test ∧
      c.test.uses [.realTimePCR, .pcrRssO, .multiplexFragmentPCR, .ngs]⟩

def otherSimpleRule : Rule Classified Unit :=
  ⟨"notice/D004-2/paragraph/3", notice "(3)", fun c _ =>
    c.test.item = .otherSimple →
      (∃ b, c.branch = some b ∧ b.item = .otherSimple) ∧
      c.test.uses [.pcr, .realTimePCR, .sscp, .rflp, .otherSimpleConfirmed]⟩

def complexRule : Rule Classified Unit :=
  ⟨"notice/D004-2/paragraph/4", notice "(4)", fun c _ =>
    c.test.item = .complex →
      (∃ b, c.branch = some b ∧ b.item = .complex) ∧ approval c.test ∧
      (c.test.uses [.ngs, .otherComplexConfirmed] ∨
        (c.branch = some .complexMelanoma ∧ c.test.uses [.realTimePCR, .pcrRssO]) ∨
        ((c.branch = some .complexSolidBraf ∨ c.branch = some .complexLymphoma) ∧
          c.test.method = some .pcrRssO) ∨
        (c.branch = some .complexOvary ∧ c.test.method = some .realTimePCR))⟩

def priorCount (c : Context) (accepts : ClaimKind → Bool) : Option Nat :=
  c.priorClaims.bind fun h =>
    count h ⟨c.performance.site.patient, none, Period.through c.performance.site.date⟩ accepts

private def msiPurpose (p : Purpose) : Bool :=
  p == .lynchDiagnosticAid || p == .solidCancerDrugSelection

def GeneFrequency (c : Context) : Prop :=
  c.assay.isSome = true ∧
  (priorCount c (fun row => row.assay == c.assay) = some 0 ∨
    (c.cancer = .lung ∧ c.assay = some .egfr ∧
      c.egfrSecondaryMutationSuspectedAfterProgression = some true ∧
      c.egfrTreatmentReselectionNeeded = some true ∧
      ∃ n, 0 < n ∧ priorCount c (fun row => row.assay == some .egfr) = some n) ∨
    (c.assay = some .msi ∧ msiPurpose c.purpose = true ∧
      priorCount c (fun row => row.assay == some .msi) = some 1 ∧
      priorCount c (fun row => row.assay == some .msi && msiPurpose row.purpose &&
        row.purpose != c.purpose) = some 1))

def geneRule : Rule Context Unit :=
  condition "1" (fun c => c.item.number = 1) fun c =>
    c.patientIsSubject = some true ∧ c.tumorCells = some true ∧
    c.purpose ≠ .other ∧ GeneFrequency c ∧
    ((c.cancer = .colorectal ∧ c.assay = some .braf ∧ c.purpose = .earlyColorectalLynchExclusion) →
      c.lynchBrafWithKrasOrRas = some false)

private def SelectionSatisfied (c : Context) (kind : Combination) (counterparts : List OtherTest) : Prop :=
  ∃ confirmed, c.combinations kind = some confirmed ∧
    ∀ s ∈ confirmed, s.other ∈ counterparts → s.principalIsThisTest = some true

def hematologicRule : Rule Context Unit :=
  condition "7" (fun c => c.item.number = 1) fun c =>
    ∃ s, c.monthlySelection = some s ∧
      s.Allows c.performance.site [.d006_2, .d006_6, .d006_14, .d006_16]

def egfrRule : Rule Context Unit :=
  condition "8" (fun c => c.item = .drugAid ∧ c.cancer = .lung ∧ c.assay = some .egfr) fun c =>
    ∃ s, c.monthlySelection = some s ∧ s.Allows c.performance.site [.d006_12, .d006_24]

def alkRule : Rule Context Unit :=
  condition "9" (fun c => c.item = .drugAid ∧ c.cancer = .lung ∧ c.assay = some .alkFusion) fun c =>
    SelectionSatisfied c .alk [.d006_24, .n002_6, .n005_2]

def her2Rule : Rule Context Unit :=
  condition "10" (fun c => c.item = .drugAid ∧ c.cancer = .breast ∧ c.assay = some .her2) fun c =>
    SelectionSatisfied c .her2 [.n005]

def brcaRule : Rule Context Unit :=
  condition "11" (fun c =>
    c.cancer ∈ [.ovarianClearCell, .otherOvarian, .prostate] ∧
      ((c.item = .drugAid ∧ c.assay = some .msi) ∨
        (c.item = .complex ∧ c.measures [.ntrkFusion, .mutationBurden]))) fun c =>
    SelectionSatisfied c .brca [.d006_18_1]

def sensitivityRule : Rule Context Unit :=
  condition "13" (fun c => c.item = .sensitivity) fun c =>
    c.cancer ∈ [.colorectal, .pancreas, .biliary, .digestive, .headNeck, .breast, .lung,
      .pleuralOrPeritonealCarcinomatosis, .cervix, .uterineBody, .ovarianClearCell, .otherOvarian] ∧
    c.surgicalTissue = some true ∧ c.uses [.hdra, .cdDst] ∧
    c.purpose = .solidCancerDrugSelection ∧ priorCount c (fun row => row.assay.isNone) = some 0

structure DrugCosts where
  separateCharge : Bool

def cytotoxicRule : Rule Context Unit :=
  condition "14" (fun c => c.item = .sensitivity) (fun c => c.cytotoxicDrug = some true)

def drugCostRule : Rule Context DrugCosts :=
  ⟨"notice/D004-2/paragraph/14", notice "(14)", fun c costs =>
    c.item = .sensitivity → costs.separateCharge = false⟩

def lynchMsiRule : Rule Context Unit :=
  condition "15" (fun c => c.assay = some .msi ∧ c.purpose = .lynchDiagnosticAid ∧
    c.approvedReagent = some true) (fun c => c.item = .drugAid)

def eligibilityRules : List (Rule Context Unit) :=
  [geneRule, hematologicRule, egfrRule, alkRule, her2Rule, brcaRule,
    sensitivityRule, cytotoxicRule, lynchMsiRule]

def Eligible (c : Classified) : Prop :=
  Satisfies eligibilityRules c.test () ∧ drugAidRule.holds c () ∧
  otherSimpleRule.holds c () ∧ complexRule.holds c () ∧
  (∀ b, (branchRule b).holds c ())

structure Documentation where
  assaysInRemarks : List Assay
  msiOrMismatchRepairDateInRemarks : Option Date

def assayDocumentationRule : Rule Context Documentation :=
  ⟨"notice/D004-2/paragraph/6", notice "(6)", fun c d =>
    c.item.number = 1 → ∃ a ∈ d.assaysInRemarks, c.assay = some a⟩

def lynchDocumentationRule : Rule Context Documentation :=
  ⟨"notice/D004-2/paragraph/1", notice "(1)", fun c d =>
    c.item.number = 1 → c.cancer = .colorectal → c.assay = some .braf →
    c.purpose = .earlyColorectalLynchExclusion → d.msiOrMismatchRepairDateInRemarks.isSome = true⟩

structure Disclosure where
  comprehensiveProfileObtained : Bool
  onlyTargetResultsProvided : Bool
  otherResultsUsedForClinicalDecisions : Bool

def disclosureRule : Rule Context Disclosure :=
  ⟨"notice/D004-2/paragraph/12", notice "(12)", fun c d =>
    c.item.number = 1 → c.method = some .ngs → c.purpose = .solidCancerDrugSelection →
    d.comprehensiveProfileObtained = true →
    d.onlyTargetResultsProvided = true ∧ d.otherResultsUsedForClinicalDecisions = false⟩

/-- 同じ患者の同じ採取・がん種について、個別の算定候補を束ねる。項目の重複かどうかは確認済みの識別子で区別する。 -/
structure Group where
  anchor : Performance Item
  cancer : Cancer
  tests : List Classified

def Group.Valid (g : Group) : Prop :=
  g.tests ≠ [] ∧ (g.tests.map fun c => c.test.performance.id).Nodup ∧
  (g.tests.map fun c => c.test.assay).Nodup ∧
  ∀ c ∈ g.tests, Eligible c ∧ c.test.item.number = 1 ∧ c.test.cancer = g.cancer ∧
    g.anchor.sameDraw c.test.performance = some true

def Group.simple (g : Group) : List Classified :=
  g.tests.filter fun c => c.test.item == .drugAid || c.test.item == .otherSimple

def Group.complex (g : Group) : List Classified :=
  g.tests.filter fun c => c.test.item == .complex

def simpleBundlePoints : Nat → Option Nat
  | 0 | 1 => none
  | 2 => some 4000
  | 3 => some 6000
  | _ => some 8000

def complexBundlePoints : Nat → Option Nat
  | 0 | 1 => none
  | 2 => some 8000
  | _ => some 12000

structure GroupResult where
  simple : Nat
  complex : Nat
  total : Nat
  deriving DecidableEq, Repr

private def sumBase (tests : List Classified) : Nat :=
  (tests.map fun c => c.test.item.points).sum

def geneBaseRule : Rule Group GroupResult :=
  ⟨"primary/D004-2/item/1", primary "項1", fun g p =>
    (g.simple.length < 2 → p.simple = sumBase g.simple) ∧
    (g.complex.length < 2 → p.complex = sumBase g.complex)⟩

def simpleNoteRule : Rule Group GroupResult :=
  ⟨"primary/D004-2/item/1/note/1", primary "注1", fun g p =>
    ∀ n, simpleBundlePoints g.simple.length = some n → p.simple = n⟩

def complexNoteRule : Rule Group GroupResult :=
  ⟨"primary/D004-2/item/1/note/2", primary "注2", fun g p =>
    ∀ n, complexBundlePoints g.complex.length = some n → p.complex = n⟩

def totalRule : Rule Group GroupResult :=
  ⟨"notice/D004-2/paragraph/5", notice "(5)", fun g p =>
    g.Valid ∧ p.total = p.simple + p.complex⟩

def groupRules : List (Rule Group GroupResult) :=
  [geneBaseRule, simpleNoteRule, complexNoteRule, totalRule]

def groupPoints (g : Group) : GroupResult :=
  let simple := (simpleBundlePoints g.simple.length).getD (sumBase g.simple)
  let complex := (complexBundlePoints g.complex.length).getD (sumBase g.complex)
  ⟨simple, complex, simple + complex⟩

private theorem simple_iff (n base p : Nat) :
    ((n < 2 → p = base) ∧ (∀ v, simpleBundlePoints n = some v → p = v)) ↔
      p = (simpleBundlePoints n).getD base := by
  rcases n with _ | ⟨_ | ⟨_ | ⟨_ | n⟩⟩⟩ <;> simp [simpleBundlePoints] <;> omega

private theorem complex_iff (n base p : Nat) :
    ((n < 2 → p = base) ∧ (∀ v, complexBundlePoints n = some v → p = v)) ↔
      p = (complexBundlePoints n).getD base := by
  rcases n with _ | ⟨_ | ⟨_ | n⟩⟩ <;> simp [complexBundlePoints] <;> omega

theorem group_satisfies_iff (g : Group) (p : GroupResult) :
    Satisfies groupRules g p ↔ g.Valid ∧ p = groupPoints g := by
  simp only [groupRules, satisfies_cons, satisfies_nil, and_true, geneBaseRule,
    simpleNoteRule, complexNoteRule, totalRule]
  constructor
  · rintro ⟨⟨s, c⟩, sn, cn, valid, total⟩
    have hs := (simple_iff _ _ _).mp ⟨s, sn⟩
    have hc := (complex_iff _ _ _).mp ⟨c, cn⟩
    refine ⟨valid, ?_⟩
    cases p
    simp_all [groupPoints]
  · rintro ⟨valid, rfl⟩
    have hs := (simple_iff g.simple.length (sumBase g.simple) _).mpr rfl
    have hc := (complex_iff g.complex.length (sumBase g.complex) _).mpr rfl
    exact ⟨⟨hs.1, hc.1⟩, hs.2, hc.2, valid, rfl⟩

theorem group_determines : DeterminesOn Group.Valid groupRules := by
  intro g valid
  exact ⟨⟨_, (group_satisfies_iff _ _).mpr ⟨valid, rfl⟩⟩,
    fun a b ha hb => ((group_satisfies_iff _ _).mp ha).2.trans ((group_satisfies_iff _ _).mp hb).2.symm⟩

def sensitivityPointsRule : Rule Classified Nat :=
  ⟨"primary/D004-2/item/2", primary "項2",
    fun c p => c.test.item = .sensitivity ∧ p = Item.sensitivity.points⟩

def sensitivityEligibilityRule : Rule Classified Nat :=
  ⟨"notice/D004-2/paragraph/13", notice "(13)・(14)",
    fun c _ => Eligible c⟩

def sensitivityRules : List (Rule Classified Nat) :=
  [sensitivityPointsRule, sensitivityEligibilityRule]

theorem sensitivity_satisfies_iff (c : Classified) (p : Nat) :
    Satisfies sensitivityRules c p ↔
      (c.test.item = .sensitivity ∧ p = Item.sensitivity.points) ∧ Eligible c := by
  simp [sensitivityRules, satisfies_cons, satisfies_nil, sensitivityPointsRule,
    sensitivityEligibilityRule]

theorem sensitivity_determines :
    DeterminesOn (fun c => c.test.item = .sensitivity ∧ Eligible c) sensitivityRules := by
  rintro c ⟨item, eligible⟩
  exact ⟨⟨_, (sensitivity_satisfies_iff _ _).mpr ⟨⟨item, rfl⟩, eligible⟩⟩,
    fun a b ha hb => ((sensitivity_satisfies_iff _ _).mp ha).1.2.trans
      ((sensitivity_satisfies_iff _ _).mp hb).1.2.symm⟩

def judgmentTest (item : Item) (ordinary : SpecimenJudgment.Category) : SpecimenJudgment.Test :=
  { major := 4, suffix := 2, number := item.number, ordinaryCategory := ordinary }

theorem judgment_gene (item : Item) (ordinary : SpecimenJudgment.Category) (h : item.number = 1) :
    SpecimenJudgment.categoryFor (judgmentTest item ordinary) = some .geneticChromosomal := by
  cases item <;> first | rfl | contradiction

theorem judgment_sensitivity (ordinary : SpecimenJudgment.Category) :
    SpecimenJudgment.categoryFor (judgmentTest .sensitivity ordinary) = some ordinary := rfl

private def exampleSite : Site :=
  ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def emptyHistory : ClaimHistory ClaimKind :=
  { coverage := ⟨1, none, Period.through exampleSite.date⟩
    entries := []
    distinctIds := List.nodup_nil }

private def sensitivityExample : Classified :=
  { test := { performance := ⟨1, exampleSite, .sensitivity, some 1, none, none, none⟩
              cancer := .breast
              purpose := .solidCancerDrugSelection
              method := some .hdra
              surgicalTissue := some true
              cytotoxicDrug := some true
              priorClaims := some emptyHistory }
    branch := none }

private theorem sensitivity_example_eligible : Eligible sensitivityExample := by
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, sensitivityExample, geneRule,
    hematologicRule, egfrRule, alkRule, her2Rule, brcaRule, sensitivityRule, cytotoxicRule,
    lynchMsiRule, condition, Context.item, Item.number, Context.uses, drugAidRule, otherSimpleRule,
    complexRule, branchRule]
  rfl

example : Satisfies sensitivityRules sensitivityExample 2500 :=
  (sensitivity_satisfies_iff _ _).mpr ⟨⟨rfl, rfl⟩, sensitivity_example_eligible⟩

example (confirmed : Option (ClaimHistory ClaimKind)) (h : confirmed = none) :
    ¬ SatisfiableAt sensitivityRules
      { sensitivityExample with test := { sensitivityExample.test with priorClaims := confirmed } } := by
  subst confirmed
  rintro ⟨p, hp⟩
  have h := ((sensitivity_satisfies_iff _ p).mp hp).2.1 sensitivityRule (by simp [eligibilityRules])
  simp [sensitivityRule, condition, sensitivityExample, Context.item, Context.uses, priorCount] at h

example : ¬ SatisfiableAt sensitivityRules
    { sensitivityExample with test := { sensitivityExample.test with cytotoxicDrug := some false } } := by
  rintro ⟨p, hp⟩
  have h := ((sensitivity_satisfies_iff _ p).mp hp).2.1 cytotoxicRule (by simp [eligibilityRules])
  simp [cytotoxicRule, condition, sensitivityExample, Context.item] at h

private def geneExample : Classified :=
  { branch := some .drugColorectal
    test := { performance := { id := 8, site := exampleSite, item := .drugAid, draw := some 5 }
              cancer := .colorectal
              assay := some .ras
              method := some .realTimePCR
              purpose := .tumorDiagnosisAndTreatmentSelection
              patientIsSubject := some true
              tumorCells := some true
              approvedReagent := some true
              priorClaims := some emptyHistory
              monthlySelection := some {
                survey := ⟨exampleSite.monthScope, []⟩
                scopeInstitution := some exampleSite.institution
                principal := fun _ _ => none } } }

private theorem gene_example_eligible : Eligible geneExample := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [eligibilityRules, satisfies_cons, satisfies_nil, geneRule, hematologicRule, egfrRule,
      alkRule, her2Rule, brcaRule, sensitivityRule, cytotoxicRule, lynchMsiRule, condition,
      geneExample, Context.item, Item.number, GeneFrequency, priorCount]
    exact ⟨rfl, [], rfl, .inr rfl, by simp⟩
  · exact fun _ => ⟨⟨.drugColorectal, rfl, rfl⟩, .inl rfl, ⟨.realTimePCR, by simp, rfl⟩⟩
  · intro h
    contradiction
  · intro h
    contradiction
  · intro b hb
    have eq : b = .drugColorectal := (Option.some.inj hb).symm
    subst b
    exact ⟨rfl, .ras, by simp, rfl⟩

private def geneGroupExample : Group :=
  ⟨geneExample.test.performance, .colorectal, [geneExample]⟩

example : Satisfies groupRules geneGroupExample ⟨2500, 0, 2500⟩ := by
  refine (group_satisfies_iff _ _).mpr ⟨⟨by simp [geneGroupExample], by decide, by decide, ?_⟩, rfl⟩
  intro c hc
  have hc' : c = geneExample := List.mem_singleton.mp hc
  subst c
  exact ⟨gene_example_eligible, rfl, rfl, rfl⟩

end Sanri.MedicalFee.D004Tumor
