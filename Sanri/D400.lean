import Sanri.SpecimenCollection
import Sanri.History
import Sanri.Logic

namespace Sanri.MedicalFee.D400

open Sanri.Logic Sanri.History

inductive Method where
  | venous | other
  deriving DecidableEq, Repr

def Method.item : Method → SpecimenCollection.Item
  | .venous => .venousBlood
  | .other => .otherBlood

structure Context where
  performance : Performance Method
  ageYears : Nat
  outpatient : Bool
  duringSurgery : Bool
  commonProcedureSameDay : Bool
  bloodCircuit : Bool
  history : ClaimHistory Method

def Context.withinDailyLimit (c : Context) : Option Bool :=
  let site := c.performance.site
  withinLimit c.history ⟨site.patient, some site.institution, Period.day site.date⟩
    (· == c.performance.item) 0

def Context.separate (c : Context) : Prop :=
  c.outpatient = true ∧ c.duringSurgery = false ∧ c.commonProcedureSameDay = false ∧
    c.bloodCircuit = false ∧ c.withinDailyLimit = some true

instance (c : Context) : Decidable c.separate := by unfold Context.separate; infer_instance

structure Result where
  base : Nat
  infant : Nat
  deriving DecidableEq, Repr

def Result.total (r : Result) : Nat := r.base + r.infant

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF210頁 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

def venousRule : Rule Context Result :=
  ⟨"primary/D400/item/1", primary "D400の1",
    fun c r => c.separate → c.performance.item = .venous → r.base = 40⟩

def otherRule : Rule Context Result :=
  ⟨"primary/D400/item/2", primary "D400の2",
    fun c r => c.separate → c.performance.item = .other → r.base = 6⟩

def dailyRule : Rule Context Result :=
  ⟨"primary/D400/heading", primary "D400見出し",
    fun c r => c.withinDailyLimit = some false → r = ⟨0, 0⟩⟩

def outpatientRule : Rule Context Result :=
  ⟨"primary/D400/note/1", primary "D400注1", fun c r => c.outpatient = false → r = ⟨0, 0⟩⟩

def infantRule : Rule Context Result :=
  ⟨"primary/D400/note/2", primary "D400注2",
    fun c r => c.separate → r.infant = (if c.ageYears < 6 then 35 else 0)⟩

def circuitRule : Rule Context Result :=
  ⟨"primary/D400/note/3", primary "D400注3", fun c r => c.bloodCircuit = true → r = ⟨0, 0⟩⟩

def surgeryRule : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/1", primary "第4節通則1",
    fun c r => c.duringSurgery = true → r = ⟨0, 0⟩⟩

def commonProcedureRule : Rule Context Result :=
  ⟨"primary/ch2-part3-section4/general/2", primary "第4節通則2",
    fun c r => c.commonProcedureSameDay = true → r = ⟨0, 0⟩⟩

/-- 加算を各採血方法に帰属させ、もう一方の方法での算定を日次枠へ混ぜない。 -/
def methodInfantRule : Rule Context Result :=
  ⟨"notice/D400/paragraph/unnumbered",
    ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後", "PDF446頁 D400",
      .checkedAgainstSource, some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩,
    fun c r => ∀ method, c.performance.item = method → c.ageYears < 6 →
      r.infant > 0 → withinLimit c.history
        ⟨c.performance.site.patient, some c.performance.site.institution,
          Period.day c.performance.site.date⟩ (· == method) 0 ≠ some false⟩

def rules : List (Rule Context Result) :=
  [venousRule, otherRule, dailyRule, outpatientRule, infantRule, circuitRule, surgeryRule,
    commonProcedureRule, methodInfantRule]

/-- 既存の単回評価に方法別の日次履歴を渡す。履歴の確認が取れなければ点数は未確定。 -/
def assess (c : Context) : Option Result := do
  let available ← c.withinDailyLimit
  let a ← SpecimenCollection.assess {
    item := c.performance.item.item
    ageYears := c.ageYears
    inpatient := !c.outpatient
    duringSurgery := c.duringSurgery
    commonProcedureClaimedSameDay := c.commonProcedureSameDay
    bloodCircuitSampling := c.bloodCircuit
    dailyAlreadyClaimed := !available }
  return ⟨a.base, a.infant⟩

theorem satisfies_iff (c : Context) (r : Result) (available : Bool)
    (known : c.withinDailyLimit = some available) :
    Satisfies rules c r ↔ assess c = some r := by
  simp only [rules, satisfies_cons, satisfies_nil, and_true, venousRule, otherRule, dailyRule,
    outpatientRule, infantRule, circuitRule, surgeryRule, commonProcedureRule, methodInfantRule]
  cases ho : c.outpatient <;> cases hs : c.duringSurgery <;>
    cases hp : c.commonProcedureSameDay <;> cases hb : c.bloodCircuit <;>
    cases available <;> cases hm : c.performance.item <;>
    simp [Context.separate, known, ho, hs, hp, hb, hm, assess, Method.item,
      SpecimenCollection.assess, SpecimenCollection.notSeparateReason, SpecimenCollection.isD400,
      SpecimenCollection.isDaily, SpecimenCollection.isUnilateral, SpecimenCollection.eligible,
      SpecimenCollection.basePoints, SpecimenCollection.infantPoints,
      eq_comm (a := r)] <;>
    (cases r; simp_all [Context.withinDailyLimit])
  all_goals
    by_cases age : c.ageYears < 6 <;>
      simp [age, show 6 ≤ c.ageYears ↔ ¬ c.ageYears < 6 from Nat.not_lt.symm, eq_comm]

theorem determines (c : Context) (available : Bool)
    (known : c.withinDailyLimit = some available) : DeterminesAt rules c := by
  have calculated : ∃ r, assess c = some r := by
    cases ho : c.outpatient <;> cases hs : c.duringSurgery <;>
      cases hp : c.commonProcedureSameDay <;> cases hb : c.bloodCircuit <;>
      cases available <;> cases hm : c.performance.item <;>
      simp [assess, known, Method.item, ho, hs, hp, hb, hm, SpecimenCollection.assess,
        SpecimenCollection.notSeparateReason, SpecimenCollection.isD400,
        SpecimenCollection.isDaily, SpecimenCollection.eligible]
  obtain ⟨r, hr⟩ := calculated
  refine ⟨⟨r, (satisfies_iff c r available known).2 hr⟩, ?_⟩
  intro a b ha hb
  exact Option.some.inj (((satisfies_iff c a available known).1 ha).symm.trans
    ((satisfies_iff c b available known).1 hb))

private def sampleSite : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def sample : Context :=
  { performance := ⟨1, sampleSite, .venous, none, none, none, none⟩
    ageYears := 5
    outpatient := true
    duringSurgery := false
    commonProcedureSameDay := false
    bloodCircuit := false
    history := ⟨⟨⟨1, some 2, Period.day sampleSite.date⟩, []⟩, by simp⟩ }

example : assess sample = some ⟨40, 35⟩ := by decide
example : assess { sample with ageYears := 6 } = some ⟨40, 0⟩ := by decide
example : assess { sample with bloodCircuit := true } = some ⟨0, 0⟩ := by decide
example : assess { sample with history := ⟨⟨⟨2, some 2, Period.day sampleSite.date⟩, []⟩,
    by simp⟩ } = none := by decide

/-- 告示PDF210頁の見出しと通知PDF446頁の乳幼児加算から、異方式併施時の
本体点数を一意に決める読みはここでは確定しない。同日の二実施で両モデルを比較する。 -/
private def mixedSite : Site := ⟨1, 2, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def mixedMethod (method prior : Method) : Context :=
  { sample with
    performance := ⟨2, mixedSite, method, none, none, none, none⟩
    ageYears := 40
    history := ⟨⟨⟨mixedSite.patient, some mixedSite.institution, .day mixedSite.date⟩,
      [⟨1, mixedSite, prior, some 1⟩]⟩, by simp⟩ }

private def adultCollection (method : Method) : SpecimenCollection.Context :=
  { item := method.item, ageYears := 40 }

private def sharedTotal (methods : List Method) : Option Nat :=
  (SpecimenCollection.assessDay (methods.map adultCollection)).map
    (fun charges => (charges.map SpecimenCollection.Assessment.total).sum)

/-- 方式別では先に異方式を算定しても、後の実施に当日の方式枠が残る。 -/
theorem mixed_method_history :
    (assess (mixedMethod .other .venous)).map Result.total = some 6 ∧
      (assess (mixedMethod .venous .other)).map Result.total = some 40 := by decide

/-- 共有枠は順序により40点又は6点となる。各方式単独の日は点数が一致する。 -/
theorem mixed_shared_frame :
    sharedTotal [.venous, .other] = some 40 ∧ sharedTotal [.other, .venous] = some 6 ∧
      sharedTotal [.venous] = some 40 ∧ sharedTotal [.other] = some 6 := by decide

/-- 同じ二実施の方式別合計は各順序で46点。前の算定を後の履歴に入れても変わらない。 -/
theorem mixed_method_total :
    let first (method : Method) := { (mixedMethod method method) with
      performance := ⟨1, mixedSite, method, none, none, none, none⟩
      history := ⟨⟨⟨mixedSite.patient, some mixedSite.institution, .day mixedSite.date⟩, []⟩,
        by simp⟩ }
    let total (a b : Method) := do
      let x ← assess (first a)
      let y ← assess (mixedMethod b a)
      return x.total + y.total
    total .venous .other = some 46 ∧ total .other .venous = some 46 := by decide

end Sanri.MedicalFee.D400
