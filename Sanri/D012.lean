import Sanri.History
import Sanri.SpecimenRules
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D012

open Sanri.Logic Sanri.History

/-- 基準診療日2026-10-22の外来。第1〜21項と第62項の検査種類。 -/
inductive Item where
  | stsQual | asoQual | asoSemi | asoQuant
  | toxoplasmaQual | toxoplasmaSemi
  | askQual | askSemi
  | treponemaQual | mycoplasmaQual | mycoplasmaSemi
  | stsSemi | stsQuant
  | treponemaSemi | treponemaQuant
  | stoolAdenovirus | urease
  | stoolRotavirusQual | stoolRotavirusQuant
  | pyloriQualSemi | pneumoniaeIgG
  | pneumoniaeIgA
  | viralTiter
  | pyloriAntibody | pertussisQual | pertussisSemi
  | htlvQual | htlvSemi | toxoplasmaAntibody | toxoplasmaIgM | difficileAntigen
  | hiv12Qual | hiv12Semi | hiv12ComboQual
  | hiv1Antibody
  | rapidGroupAStrep
  | hiv12Quant
  | hibAntigen
  | hiv12ComboQuant
  | aspergillusIgG
  deriving DecidableEq

def Item.number : Item → Nat
  | .stsQual | .asoQual | .asoSemi | .asoQuant => 1
  | .toxoplasmaQual | .toxoplasmaSemi => 2
  | .askQual | .askSemi => 3
  | .treponemaQual | .mycoplasmaQual | .mycoplasmaSemi => 4
  | .stsSemi | .stsQuant => 5
  | .treponemaSemi | .treponemaQuant => 6
  | .stoolAdenovirus | .urease => 7
  | .stoolRotavirusQual | .stoolRotavirusQuant => 8
  | .pyloriQualSemi | .pneumoniaeIgG => 9
  | .pneumoniaeIgA => 10
  | .viralTiter => 11
  | .pyloriAntibody | .pertussisQual | .pertussisSemi => 12
  | .htlvQual | .htlvSemi => 13
  | .toxoplasmaAntibody => 14
  | .toxoplasmaIgM | .difficileAntigen => 15
  | .hiv12Qual | .hiv12Semi | .hiv12ComboQual => 16
  | .hiv1Antibody => 17
  | .rapidGroupAStrep => 18
  | .hiv12Quant => 19
  | .hibAntigen => 20
  | .hiv12ComboQuant => 21
  | .aspergillusIgG => 62

def Item.points : Item → Nat
  | .stsQual | .asoQual | .asoSemi | .asoQuant => 15
  | .toxoplasmaQual | .toxoplasmaSemi => 26
  | .askQual | .askSemi => 29
  | .treponemaQual | .mycoplasmaQual | .mycoplasmaSemi => 32
  | .stsSemi | .stsQuant => 34
  | .treponemaSemi | .treponemaQuant => 53
  | .stoolAdenovirus | .urease => 60
  | .stoolRotavirusQual | .stoolRotavirusQuant => 65
  | .pyloriQualSemi | .pneumoniaeIgG => 70
  | .pneumoniaeIgA => 75
  | .viralTiter => 79
  | .pyloriAntibody | .pertussisQual | .pertussisSemi => 80
  | .htlvQual | .htlvSemi => 85
  | .toxoplasmaAntibody => 93
  | .toxoplasmaIgM | .difficileAntigen => 95
  | .hiv12Qual | .hiv12Semi | .hiv12ComboQual => 109
  | .hiv1Antibody => 113
  | .rapidGroupAStrep => 121
  | .hiv12Quant => 124
  | .hibAntigen => 126
  | .hiv12ComboQuant => 127
  | .aspergillusIgG => 390

def Item.variant : Item → Nat
  | .hiv12Semi => 1
  | .hiv12ComboQual => 2
  | .asoQual | .toxoplasmaSemi | .askSemi | .mycoplasmaQual | .stsQuant | .treponemaQuant | .urease | .stoolRotavirusQuant | .pneumoniaeIgG | .pertussisQual | .htlvSemi | .difficileAntigen => 1
  | .asoSemi | .mycoplasmaSemi | .pertussisSemi => 2
  | .asoQuant => 3
  | _ => 0

def ledgerItems : List Item :=
  [.stsQual, .asoQual, .asoSemi, .asoQuant,
    .toxoplasmaQual, .toxoplasmaSemi,
    .askQual, .askSemi,
    .treponemaQual, .mycoplasmaQual, .mycoplasmaSemi,
    .stsSemi, .stsQuant,
    .treponemaSemi, .treponemaQuant,
    .stoolAdenovirus, .urease,
    .stoolRotavirusQual, .stoolRotavirusQuant,
    .pyloriQualSemi, .pneumoniaeIgG,
    .pneumoniaeIgA,
    .viralTiter,
    .pyloriAntibody, .pertussisQual, .pertussisSemi, .htlvQual, .htlvSemi,
    .toxoplasmaAntibody, .toxoplasmaIgM, .difficileAntigen,
    .hiv12Qual, .hiv12Semi, .hiv12ComboQual, .hiv1Antibody, .rapidGroupAStrep,
    .hiv12Quant, .hibAntigen, .hiv12ComboQuant, .aspergillusIgG]

private def primary (page : Nat) (loc : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度・2026-06-01適用",
    s!"PDF{page}頁 D012 {loc}", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (pages loc : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    s!"PDF{pages}頁 D012({loc})", .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

def itemRule (i : Item) : Rule Item Nat :=
  let n := toString i.number
  let page := if i.number ≤ 18 then 184 else if i.number ≤ 21 then 185 else 186
  ⟨"primary/D012/item/" ++ n, primary page n,
    fun candidate p => candidate = i → p = i.points⟩

def rules : List (Rule Item Nat) := ledgerItems.map itemRule

theorem rate_iff (i : Item) (p : Nat) :
    Satisfies rules i p ↔ p = i.points := by
  constructor
  · intro h
    exact h _ (List.mem_map.mpr ⟨i, by cases i <;> simp [ledgerItems], rfl⟩) rfl
  · intro h _ hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    intro hi
    simpa [hi] using h

inductive Target where
  | adenovirus | coxsackie | cytomegalovirus | eb | echo | herpes
  | influenzaA | influenzaB | mumps | parainfluenzaI | parainfluenzaII | parainfluenzaIII
  | polioI | polioII | polioIII | rs | rubella | measles | japaneseEncephalitis
  | psittacosis | varicellaZoster
  deriving DecidableEq

inductive RelatedTest where
  | local (item : Item)
  | bacterialCultureD018
  | mycoplasma27 | mycoplasma38 | pneumoniaeIgM30
  | influenzaAntigen22 | metapneumovirus25 | rsAntigen24 | classSpecific46 | toxoplasmaAvidity64
  deriving DecidableEq

inductive PyloriMethod where
  | la | immunochromatography | goldColloid | simpleEia
  deriving DecidableEq

structure Combined where
  /-- 当該通知の「併せて」に該当することを確認した実施群。 -/
  members : List (Performance RelatedTest)
  /-- 医学的判断又は選択で確定した算定対象の実施ID。 -/
  selected : Option (List Nat) := none
  viralTarget : Nat → Option Target := fun _ => none

inductive HivMethod where
  | la | eia | pa | immunochromatography | other
  deriving DecidableEq

inductive HistoricalBleeding where
  | neonatalOrSimilar | severeLiverDisease | digestiveDisease | surgeryOrDelivery
  deriving DecidableEq

inductive HivIndication where
  | documentedUnheatedFactor
  | undocumentedFactor (inpatientYear : Nat) (bleeding : HistoricalBleeding)
  | suspectedWithDifferentialDisease
  | suspectedWithAssociatedSexuallyTransmittedInfection
  deriving DecidableEq

inductive TransfusionKind where
  | k920NonAutologous | plasmaProduct
  deriving DecidableEq

/-- 他機関の一連も識別する。算定履歴のキーには実施元機関も含める。 -/
structure TransfusionSeries where
  patient : Nat
  provider : Nat
  seriesId : Nat
  finalDay : Date
  kind : TransfusionKind

structure HivFollowUp where
  series : TransfusionSeries
  /-- 最終日から概ね2か月後に該当することを確認した外部判断。 -/
  approximatelyTwoMonths : Bool
  /-- 候補を除き、同じ一連に対する既算定を全機関について確認する。 -/
  history : ClaimHistory (Nat × Nat)

inductive HivRoute where
  | clinical (indication : HivIndication)
  | transfusion (followUp : HivFollowUp)

structure Context where
  performance : Performance RelatedTest
  /-- 確認済みの併施なしは候補実施だけの群とする。同時実施には別途同時IDを使う。 -/
  combined : Option Combined := none
  target : Option Target := none
  conventionalStsMethod : Option Bool := none
  /-- 同じSTS定性・半定量・定量区分で、確認された沈降反応の方法数。 -/
  stsMethodCount : Option Nat := none
  pyloriMethod : Option PyloriMethod := none
  pyloriNoticeSatisfied : Option Bool := none
  treatmentNecessity : Option Bool := none
  particleAgglutination : Option Bool := none
  hivRoute : Option HivRoute := none
  /-- 当該機関での採血を保健所に委託した検査に該当するか。 -/
  hivHealthCenterOutsourcing : Option Bool := none
  hivMethod : Option HivMethod := none
  aspergillus : Option SpecimenTests.AspergillusAssessment := none

private def condition (id pages paragraph : String) (holds : Context → Prop) :
    Rule Context Unit :=
  ⟨"notice/D012/paragraph/" ++ id, notice pages paragraph, fun c _ => holds c⟩

/-- 確認された併施群の局所IDを、患者・機関をまたいで再利用しない。 -/
def Combined.Valid (g : Combined) (p : Performance RelatedTest) : Prop :=
  p ∈ g.members ∧ (g.members.map (·.id)).Nodup ∧
    ∀ q ∈ g.members, q.site.patient = p.site.patient ∧ q.site.institution = p.site.institution

private def selectedFrom (g : Combined) (members : List (Performance RelatedTest))
    (p : Performance RelatedTest) (limit : Nat) : Prop :=
  ∃ ids, g.selected = some ids ∧
    let chosen := ids.filter fun id => members.any fun q => q.id == id
    chosen.Nodup ∧ chosen.length = limit ∧ p.id ∈ chosen

def stsRule : Rule Context Unit :=
  condition "1" "370" "1" fun c =>
    ∀ i ∈ [Item.stsQual, .stsSemi, .stsQuant], c.performance.item = .local i →
      c.conventionalStsMethod = some true ∧ ∃ n, c.stsMethodCount = some n ∧ 0 < n ∧
        (2 ≤ n → ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
          selectedFrom g (g.members.filter fun q => q.item == .local i) c.performance 1)

private def isMycoplasma (i : RelatedTest) : Bool :=
  decide (i ∈ [RelatedTest.local .mycoplasmaQual, .local .mycoplasmaSemi,
    .mycoplasma27, .mycoplasma38])

private def mycoplasmaSelection (c : Context) : Prop :=
  isMycoplasma c.performance.item = true → ∃ g, c.combined = some g ∧
    g.Valid c.performance ∧
    let members := g.members.filter (isMycoplasma ∘ Performance.item)
    (2 ≤ members.length → selectedFrom g members c.performance 1)

def mycoplasmaAntibodyRule : Rule Context Unit :=
  condition "2" "370" "2" mycoplasmaSelection

def mycoplasmaChromatographyRule : Rule Context Unit :=
  condition "18" "373" "18" mycoplasmaSelection

def mycoplasmaFluorescenceRule : Rule Context Unit :=
  condition "29" "374" "29" mycoplasmaSelection

def ureaseRule : Rule Context Unit :=
  condition "3" "370" "3" fun c =>
    c.performance.item = .local .urease → c.pyloriNoticeSatisfied = some true

private def isRotavirus (i : RelatedTest) : Bool :=
  decide (i ∈ [RelatedTest.local .stoolRotavirusQual, .local .stoolRotavirusQuant])

def stoolAntigenRule : Rule Context Unit :=
  condition "4" "370" "4" fun c =>
    let p := c.performance
    (p.item = .local .stoolAdenovirus ∨ isRotavirus p.item = true) →
      ∃ g, c.combined = some g ∧ g.Valid p ∧
        let stool := g.members.filter fun q =>
          q.item == .local .stoolAdenovirus || isRotavirus q.item
        (∀ q ∈ stool, q.id ≠ p.id → (p.simultaneousWith q).isSome = true) ∧
        let simultaneous := stool.filter fun q => q.id == p.id || p.simultaneousWith q == some true
        (simultaneous.any (fun q => q.item == .local .stoolAdenovirus) = true →
          simultaneous.any (fun q => isRotavirus q.item) = true →
          selectedFrom g simultaneous p 1)

def pyloriMethodRule : Rule Context Unit :=
  condition "5/a" "370" "5 ア" fun c =>
    c.performance.item = .local .pyloriQualSemi → c.pyloriMethod.isSome = true

def pyloriReferenceRule : Rule Context Unit :=
  condition "5/i" "370" "5 イ" fun c =>
    c.performance.item = .local .pyloriQualSemi → c.pyloriNoticeSatisfied = some true

def pyloriRule : Rule Context Unit :=
  condition "5" "370" "5" fun c => pyloriMethodRule.holds c () ∧ pyloriReferenceRule.holds c ()

def viralIndication : Rule Context Unit :=
  condition "6/a" "370–371" "6 ア" fun c =>
    c.performance.item = .local .viralTiter → c.treatmentNecessity = some true ∧ c.target.isSome = true

def viralParagraph : Rule Context Unit :=
  condition "6" "370–371" "6" fun c => viralIndication.holds c ()

def pyloriAntibodyRule : Rule Context Unit :=
  condition "7" "371" "7" fun c =>
    c.performance.item = .local .pyloriAntibody → c.pyloriNoticeSatisfied = some true

def htlvRule : Rule Context Unit :=
  condition "8" "371" "8" fun c =>
    c.performance.item ∈ [RelatedTest.local .htlvQual, .local .htlvSemi] →
      c.particleAgglutination = some true

def pneumoniaeChoice : Rule Context Unit :=
  condition "23" "373" "23" fun c =>
    let antibodies := [RelatedTest.local .pneumoniaeIgG, .local .pneumoniaeIgA, .pneumoniaeIgM30]
    c.performance.item ∈ antibodies → ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
      let members := g.members.filter fun q => decide (q.item ∈ antibodies)
      (members.any (fun q => q.item == .pneumoniaeIgM30) = true →
        members.any (fun q => q.item == .local .pneumoniaeIgG ||
          q.item == .local .pneumoniaeIgA) = true →
        selectedFrom g members c.performance 1)

private def isFluTarget (t : Option Target) : Bool :=
  decide (t ∈ [some .influenzaA, some .influenzaB])

private def confirmedTargets (g : Combined) (c : Context) : Prop :=
  (∀ q ∈ g.members, q.item = .local .viralTiter → (g.viralTarget q.id).isSome = true) ∧
    (c.performance.item = .local .viralTiter → g.viralTarget c.performance.id = c.target)

private def isFluAntibody (g : Combined) (q : Performance RelatedTest) : Bool :=
  q.item == .local .viralTiter && isFluTarget (g.viralTarget q.id)

def influenzaChoice : Rule Context Unit :=
  condition "13/i" "372" "13 イ" fun c =>
    (c.performance.item = .local .viralTiter ∧ isFluTarget c.target = true) →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧ confirmedTargets g c ∧
        (g.members.any (fun q => q.item == .influenzaAntigen22) = true →
          selectedFrom g (g.members.filter fun q =>
            q.item == .influenzaAntigen22 || isFluAntibody g q) c.performance 1)

private inductive RespiratoryGroup where
  | influenza | metapneumovirus | rs
  deriving DecidableEq

private def respiratoryGroup (g : Combined) (q : Performance RelatedTest) :
    Option RespiratoryGroup :=
  match q.item with
  | .influenzaAntigen22 => some .influenza
  | .metapneumovirus25 => some .metapneumovirus
  | .rsAntigen24 => some .rs
  | .local .viralTiter => if isFluAntibody g q then some .influenza else none
  | _ => none

def metapneumovirusChoice : Rule Context Unit :=
  condition "17/a" "372–373" "17 ア" fun c =>
    (c.performance.item = .local .viralTiter ∧ isFluTarget c.target = true) →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧ confirmedTargets g c ∧
        ((g.members.filterMap (respiratoryGroup g)).eraseDups.length = 3 →
          ∃ ids, g.selected = some ids ∧ c.performance.id ∈ ids ∧
            ((g.members.filter fun q => decide (q.id ∈ ids)).filterMap
              (respiratoryGroup g)).eraseDups.length = 2)

def viralClassChoice : Rule Context Unit :=
  condition "38/u" "375" "38 ウ" fun c =>
    c.performance.item = .local .viralTiter →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        let other := g.members.filter fun q => q.item == .classSpecific46
        (other ≠ [] → ∃ ids, g.selected = some ids ∧ c.performance.id ∈ ids ∧
          ∀ q ∈ other, q.id ∉ ids)

def aspergillusRule : Rule Context Unit :=
  { id := "notice/D012/paragraph/52"
    source := { SpecimenTests.d012AspergillusSource with
      url := some "https://www.mhlw.go.jp/content/12400000/001700249.pdf" }
    holds := fun c _ => c.performance.item = .local .aspergillusIgG →
      ∃ a, c.aspergillus = some a ∧ a.elisa = true ∧ a.guidelineFollowed = true ∧
        (a.suspectedChronicProgressivePulmonaryDisease = true ∨
          a.suspectedAllergicBronchopulmonaryDisease = true) }

/-- (56)のうち第14項との併施に関する制約。第64項の適格性は別途扱う。 -/
def toxoplasmaChoice : Rule Context Unit :=
  condition "56" "378" "56" fun c =>
    c.performance.item = .local .toxoplasmaAntibody →
      ∃ g, c.combined = some g ∧ g.Valid c.performance ∧
        let other := g.members.filter fun q => q.item == .toxoplasmaAvidity64
        (other ≠ [] → selectedFrom g
          (g.members.filter fun q =>
            q.item == .local .toxoplasmaAntibody || q.item == .toxoplasmaAvidity64)
          c.performance 1)

def isHivScreening : RelatedTest → Bool
  | .local .hiv12Qual | .local .hiv12Semi | .local .hiv12ComboQual
  | .local .hiv1Antibody | .local .hiv12Quant | .local .hiv12ComboQuant => true
  | _ => false

private def HivFollowUp.Valid (f : HivFollowUp) (site : Site) : Prop :=
  f.series.patient = site.patient ∧
    ∃ period : Period, period.first = f.series.finalDay ∧ period.last = site.date ∧
      f.approximatelyTwoMonths = true ∧
      withinLimit f.history ⟨site.patient, none, period⟩
        (· == (f.series.provider, f.series.seriesId)) 0 = some true

def hivClinicalRule : Rule Context Unit :=
  condition "9" "371" "9" fun c =>
    isHivScreening c.performance.item = true →
      c.hivRoute.isSome = true ∧
      ∀ indication, c.hivRoute = some (.clinical indication) →
        c.hivHealthCenterOutsourcing = some false

private def historicalBranch (id label : String) (b : HistoricalBleeding) : Rule Context Unit :=
  condition id "371" label fun c =>
    ∀ year, isHivScreening c.performance.item = true →
      c.hivRoute = some (.clinical (.undocumentedFactor year b)) →
      1978 ≤ year ∧ year ≤ 1988

def hivNeonatalRule := historicalBranch "9/a" "9 ア" .neonatalOrSimilar
def hivLiverRule := historicalBranch "9/i" "9 イ" .severeLiverDisease
def hivDigestiveRule := historicalBranch "9/u" "9 ウ" .digestiveDisease
def hivSurgeryRule := historicalBranch "9/e" "9 エ" .surgeryOrDelivery

def hivFollowUpRule : Rule Context Unit :=
  condition "10/a" "371–372" "10 ア" fun c =>
    isHivScreening c.performance.item = true →
    ∀ f, c.hivRoute = some (.transfusion f) → f.series.provider = c.performance.site.institution →
      f.Valid c.performance.site

def hivOtherInstitutionRule : Rule Context Unit :=
  condition "10/i" "372" "10 イ" fun c =>
    isHivScreening c.performance.item = true →
    ∀ f, c.hivRoute = some (.transfusion f) → f.series.provider ≠ c.performance.site.institution →
      f.Valid c.performance.site

def hivTransfusionRule : Rule Context Unit :=
  condition "10" "371–372" "10" fun c =>
    hivFollowUpRule.holds c () ∧ hivOtherInstitutionRule.holds c ()

def hivFinalDayEntry : Rule Context (Option Date) :=
  ⟨"notice/D012/paragraph/10/u", notice "372" "10 ウ", fun c entry =>
    isHivScreening c.performance.item = true →
    ∀ f, c.hivRoute = some (.transfusion f) → entry = some f.series.finalDay⟩

def hivMethodRule : Rule Context Unit :=
  condition "11" "372" "11" fun c =>
    c.performance.item ∈ [RelatedTest.local .hiv12Qual, .local .hiv12Semi, .local .hiv12Quant] →
      c.hivMethod ∈ [some .la, some .eia, some .pa, some .immunochromatography]

/-- D018側との照合入力。陰性を受けた後続検査かどうかは実施記録で確認する。 -/
structure StrepCulture where
  rapid : Performance RelatedTest
  culture : Performance RelatedTest
  followedNegativeRapid : Option Bool

def strepCultureRule : Rule StrepCulture Bool :=
  ⟨"notice/D012/paragraph/12", notice "372" "12", fun c separate =>
    c.rapid.item = .local .rapidGroupAStrep → c.culture.item = .bacterialCultureD018 →
    c.rapid.site.patient = c.culture.site.patient →
    c.rapid.site.institution = c.culture.site.institution → separate = true →
      c.rapid.simultaneousWith c.culture = some false ∧ c.followedNegativeRapid = some false⟩

def eligibilityRules :=
  [stsRule, mycoplasmaAntibodyRule, ureaseRule, stoolAntigenRule, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule, htlvRule,
    influenzaChoice, metapneumovirusChoice, mycoplasmaChromatographyRule, pneumoniaeChoice,
    hivClinicalRule, hivNeonatalRule, hivLiverRule, hivDigestiveRule, hivSurgeryRule,
    hivTransfusionRule, hivFollowUpRule, hivOtherInstitutionRule, hivMethodRule,
    mycoplasmaFluorescenceRule, viralClassChoice, aspergillusRule, toxoplasmaChoice]

def Eligible (c : Context) : Prop := Satisfies eligibilityRules c ()

def PermitsRate (i : Item) (c : Context) (p : Nat) : Prop :=
  c.performance.item = .local i ∧ Eligible c ∧ Satisfies rules i p

def legacyRequest (i : Item) (a : Option SpecimenTests.AspergillusAssessment) :
    SpecimenTests.Request :=
  { code := .d012, number := i.number, variant := i.variant, conditions := { aspergillus := a } }

theorem legacy_rate (i : Item) (a : Option SpecimenTests.AspergillusAssessment)
    (h : i = .aspergillusIgG → a.any (fun x => x.elisa && x.guidelineFollowed &&
      (x.suspectedChronicProgressivePulmonaryDisease ||
        x.suspectedAllergicBronchopulmonaryDisease)) = true) :
    SpecimenTests.assessOne (legacyRequest i a) = some (.charged i.points 0) := by
  cases i <;> try rfl
  change (if !(a.any fun x => x.elisa && x.guidelineFollowed &&
      (x.suspectedChronicProgressivePulmonaryDisease ||
        x.suspectedAllergicBronchopulmonaryDisease)) then none else some (SpecimenTests.ItemResult.charged 390 0)) =
    some (SpecimenTests.ItemResult.charged 390 0)
  simp [h rfl]

theorem legacy_iff (c : Context) (i : Item) (p : Nat)
    (hi : c.performance.item = .local i) (he : Eligible c) :
    Satisfies rules i p ↔
      SpecimenTests.assessOne (legacyRequest i c.aspergillus) = some (.charged p 0) := by
  have h := he aspergillusRule (by simp [eligibilityRules])
  rw [rate_iff, legacy_rate]
  · simp [eq_comm]
  · intro h62
    subst i
    obtain ⟨a, ha, helisa, hguide, hsuspect⟩ := h hi
    rcases hsuspect with hc | ha'
    · simp [ha, helisa, hguide, hc]
    · simp [ha, helisa, hguide, ha']

theorem determines (c : Context) (i : Item)
    (hi : c.performance.item = .local i) (he : Eligible c) :
    (∃ p, PermitsRate i c p) ∧
      ∀ a b, PermitsRate i c a → PermitsRate i c b → a = b := by
  exact ⟨⟨i.points, hi, he, (rate_iff ..).mpr rfl⟩,
    fun a b ha hb => ((rate_iff i a).mp ha.2.2).trans ((rate_iff i b).mp hb.2.2).symm⟩

/-- 検体単位の照合済み抗体価測定。異なる方法による同じ対象も保持する。 -/
structure ViralGroup where
  anchor : Performance RelatedTest
  measurements : List (Context × Target)

def ViralGroup.Assessed (g : ViralGroup) : Prop :=
  g.measurements ≠ [] ∧ (g.measurements.map (·.1.performance.id)).Nodup ∧
    ∀ (pair : Context × Target), pair ∈ g.measurements →
      pair.1.performance.item = .local .viralTiter ∧ pair.1.target = some pair.2 ∧
      g.anchor.sameSpecimen pair.1.performance = some true ∧ Eligible pair.1

def ViralGroup.targetCount (g : ViralGroup) : Nat :=
  (g.measurements.map Prod.snd).eraseDups.length

def viralMethods : Rule ViralGroup Nat :=
  ⟨"notice/D012/paragraph/6/i", notice "371" "6 イ", fun g p =>
    g.targetCount ≤ 8 → p = 79 * g.targetCount⟩

def viralCapPoints : Nat := 79 * 8

def viralCap : Rule ViralGroup Nat :=
  ⟨"primary/D012/item/11/note", primary 184 "11 注", fun g p =>
    8 ≤ g.targetCount → p = viralCapPoints⟩

def viralRules := [viralMethods, viralCap]

theorem viral_legacy_iff (g : ViralGroup) (p : Nat) :
    Satisfies viralRules g p ↔
      p = SpecimenTests.groupedBase .viralAntibodies g.targetCount 79 := by
  by_cases hn : g.targetCount ≤ 8
  · simp only [viralRules, satisfies_cons, satisfies_nil, viralMethods, viralCap, viralCapPoints,
      and_true, SpecimenTests.groupedBase, Nat.min_eq_right hn]
    constructor
    · exact fun h => h.1 hn
    · intro h
      exact ⟨fun _ => h, fun h8 => by have eq := Nat.le_antisymm hn h8; simpa [eq] using h⟩
  · have h8 : 8 ≤ g.targetCount := by omega
    simp [viralRules, satisfies_cons, satisfies_nil, viralMethods, viralCap, viralCapPoints, hn, h8,
      SpecimenTests.groupedBase, Nat.min_eq_left h8]

theorem viral_determines : DeterminesOn ViralGroup.Assessed viralRules := by
  intro g _
  exact ⟨⟨_, (viral_legacy_iff ..).mpr rfl⟩,
    fun a b ha hb => ((viral_legacy_iff g a).mp ha).trans ((viral_legacy_iff g b).mp hb).symm⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 12, number := i.number, variant := i.variant, ordinaryCategory := .immunological }

private def executionItem (kind points : Nat) : Examinations.SpecimenItem :=
  { kind := kind, executionPoints := points }

def individualExecution (kind : Nat) (i : Item) (c : Context) (p : Nat)
    (_ : i ≠ .viralTiter) (_ : PermitsRate i c p) : Examinations.SpecimenItem :=
  executionItem kind p

def viralExecution (kind : Nat) (g : ViralGroup) (p : Nat)
    (_ : g.Assessed) (_ : Satisfies viralRules g p) : Examinations.SpecimenItem :=
  executionItem kind p

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .immunological := rfl

private def sample (item : Item) : Context :=
  { performance := ⟨1, ⟨2, 3, ⟨⟨2026, 9⟩, ⟨22, by decide⟩⟩⟩, .local item,
    none, some 1, none, none⟩ }

private def aspergillusSample : Context :=
  { sample .aspergillusIgG with aspergillus := some ⟨true, false, true, true⟩ }

example : PermitsRate .aspergillusIgG aspergillusSample 390 := by
  refine ⟨rfl, ?_, (rate_iff ..).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, condition, stsRule,
    mycoplasmaAntibodyRule, mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule,
    mycoplasmaSelection, isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule, htlvRule, influenzaChoice,
    pneumoniaeChoice, metapneumovirusChoice, viralClassChoice, aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule, hivDigestiveRule,
    hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule, hivOtherInstitutionRule,
    hivMethodRule, isHivScreening, aspergillusSample, sample]

example : ¬ Eligible (sample .aspergillusIgG) := by
  intro h
  obtain ⟨a, ha, _⟩ := h aspergillusRule (by simp [eligibilityRules]) rfl
  cases ha

private def hivSample : Context :=
  { sample .hiv12Qual with
    hivRoute := some (.clinical (.undocumentedFactor 1978 .neonatalOrSimilar))
    hivHealthCenterOutsourcing := some false
    hivMethod := some .pa }

example : PermitsRate .hiv12Qual hivSample 109 := by
  refine ⟨rfl, ?_, (rate_iff ..).mpr rfl⟩
  simp [Eligible, eligibilityRules, satisfies_cons, satisfies_nil, condition, stsRule,
    mycoplasmaAntibodyRule, mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule,
    mycoplasmaSelection, isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule,
    pyloriMethodRule, pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule,
    htlvRule, influenzaChoice, pneumoniaeChoice, metapneumovirusChoice, viralClassChoice,
    aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule,
    hivDigestiveRule, hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule,
    hivOtherInstitutionRule, hivMethodRule, isHivScreening, hivSample, sample]

example : ¬ Eligible
    { hivSample with hivRoute := some (.clinical (.undocumentedFactor 1977 .neonatalOrSimilar)) } := by
  intro h
  have year := h hivNeonatalRule (by simp [eligibilityRules]) 1977 rfl rfl
  omega

private def followUpPeriod : Period :=
  ⟨⟨⟨2026, 7⟩, ⟨22, by decide⟩⟩, hivSample.performance.site.date, by decide⟩

private def followUpSample : HivFollowUp :=
  { series := ⟨2, 4, 1, followUpPeriod.first, .plasmaProduct⟩
    approximatelyTwoMonths := true
    history := ⟨⟨⟨2, none, followUpPeriod⟩, []⟩, by simp⟩ }

private def transfusionSample : Context :=
  { hivSample with hivRoute := some (.transfusion followUpSample) }

example : hivOtherInstitutionRule.holds transfusionSample () := by
  intro _ f hf _
  have eq : followUpSample = f := by
    simpa [transfusionSample] using hf
  subst f
  exact ⟨rfl, followUpPeriod, rfl, rfl, rfl, by decide⟩

example : hivFinalDayEntry.holds transfusionSample (some followUpPeriod.first) := by
  intro _ f hf
  have eq : followUpSample = f := by
    simpa [transfusionSample] using hf
  subst f
  rfl

private def strepCultureSample : StrepCulture :=
  let rapid := { (sample .rapidGroupAStrep).performance with simultaneous := some 1 }
  ⟨rapid, { rapid with id := 2, item := .bacterialCultureD018 }, some false⟩

example : ¬ strepCultureRule.holds strepCultureSample true := by
  intro h
  have bad := (h rfl rfl rfl rfl rfl).1
  contradiction

private def titer (id : Nat) (target : Target) : Context × Target :=
  let p := { (sample .viralTiter).performance with id := id }
  ({ performance := p, target := some target, treatmentNecessity := some true
     combined := some { members := [p] } }, target)

private def nineTargets : List (Context × Target) :=
  [titer 1 .adenovirus, titer 2 .coxsackie, titer 3 .cytomegalovirus,
    titer 4 .eb, titer 5 .echo, titer 6 .herpes, titer 7 .mumps,
    titer 8 .parainfluenzaI, titer 9 .parainfluenzaII]

private def nineTargetGroup : ViralGroup :=
  ⟨(sample .viralTiter).performance, nineTargets⟩

example : nineTargetGroup.Assessed := by
  refine ⟨by simp [nineTargetGroup, nineTargets], by decide, ?_⟩
  simp [nineTargetGroup, nineTargets, titer, sample, Eligible, eligibilityRules,
    satisfies_cons, satisfies_nil, stsRule, condition, mycoplasmaAntibodyRule,
    mycoplasmaChromatographyRule, mycoplasmaFluorescenceRule, mycoplasmaSelection,
    isMycoplasma, ureaseRule, stoolAntigenRule, isRotavirus, pyloriRule, pyloriMethodRule,
    pyloriReferenceRule, viralParagraph, viralIndication, pyloriAntibodyRule, htlvRule,
    influenzaChoice, metapneumovirusChoice, isFluTarget, pneumoniaeChoice, viralClassChoice,
    aspergillusRule, toxoplasmaChoice, hivClinicalRule, hivNeonatalRule, hivLiverRule, hivDigestiveRule,
    hivSurgeryRule, historicalBranch, hivTransfusionRule, hivFollowUpRule, hivOtherInstitutionRule,
    hivMethodRule, isHivScreening, Combined.Valid, Performance.sameSpecimen, Performance.sameGroup]

example : Satisfies viralRules nineTargetGroup 632 :=
  (viral_legacy_iff ..).mpr rfl

example : Satisfies viralRules
    { nineTargetGroup with measurements := nineTargets.take 8 } 632 :=
  (viral_legacy_iff ..).mpr rfl

example : Satisfies viralRules
    { nineTargetGroup with measurements := [titer 1 .adenovirus, titer 2 .adenovirus] } 79 :=
  (viral_legacy_iff ..).mpr rfl

end Sanri.MedicalFee.D012
