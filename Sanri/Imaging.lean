import Sanri.InitialConsultation

namespace Sanri.MedicalFee.Imaging

/-! 第４部 画像診断 通則１〜８。個別区分、第４節・第５節の要件と点数、
施設基準の詳細は入力する。日次・月次履歴は同一患者・算定医療機関について管理する。
遠隔読影はオンライン診療とは別の概念として表現する。 -/

inductive Code where
  | e001 | e004 | e102 | e203 | other
  deriving DecidableEq, Repr

inductive Group where
  | e001OrE004 | e102 | e203
  deriving DecidableEq, Repr

def groupOf : Code → Option Group
  | .e001 | .e004 => some .e001OrE004
  | .e102 => some .e102
  | .e203 => some .e203
  | .other => none

inductive Management where
  | one | two | partialTwo | three | four
  deriving DecidableEq, Repr

def managementPoints : Management → Nat
  | .one => 70
  | .two => 175
  | .partialTwo => 166
  | .three => 235
  | .four => 340

/-- 各フラグは当該基準への適合と届出の両方を意味する。 -/
structure Standards where
  one : Bool := false
  two : Bool := false
  three : Bool := false
  four : Bool := false
  deriving DecidableEq, Repr

def higherNotified (s : Standards) : Bool := s.two || s.three || s.four

def notified (s : Standards) : Management → Bool
  | .one => s.one
  | .two | .partialTwo => s.two
  | .three => s.three
  | .four => s.four

inductive Section where
  | section1 | section2 | section3
  deriving DecidableEq, Repr

structure Entry where
  code : Code
  feeSection : Section
  scheduledPoints : Nat
  /-- 加算を請求しない場合は none。partialTwo は遠隔条件から決定する。 -/
  management : Option Management := none
  deriving DecidableEq, Repr

structure ManagementHistory where
  group : Group
  kind : Management
  deriving DecidableEq, Repr

structure Remote where
  /-- 通則６本文：所定の基準に適合・届出済みの医療機関間の遠隔画像診断。 -/
  betweenNotifiedInstitutions : Bool := false
  receiverStandards : Standards := {}
  /-- 受信側の専任・常勤医師が読影し、送信側へ文書等で報告した。 -/
  receiverDedicatedFullTimeDoctorReportedToSender : Bool := false
  deriving DecidableEq, Repr

structure Context where
  insuranceMedicalInstitution : Bool := true
  imagingPerformed : Bool := true
  entries : List Entry
  /-- 第４節の要件を満たした算定点数。使わなければ空。 -/
  section4Points : List Nat := []
  /-- 実際に使用した大臣指定の特定保険医療材料の第５節の点数。 -/
  section5MaterialPoints : List Nat := []
  inpatient : Bool := false
  urgent : Bool := false
  photographyInsideInstitution : Bool := false
  diagnosisInsideInstitution : Bool := false
  time : InitialConsultation.Time := {}
  emergencyAdditionClaimedToday : Bool := false
  localStandards : Standards := {}
  /-- 算定側（遠隔の場合は送信側）の専任・常勤医師による読影と文書報告。 -/
  localDedicatedFullTimeDoctorWrittenReport : Bool := false
  remoteDiagnosis : Bool := false
  remote : Remote := {}
  managementHistoryThisMonth : List ManagementHistory := []
  deriving DecidableEq, Repr

/-- 要件不備は none。通則７該当時は２〜４の選択を166点へ置換し、
通則８による高位加算や送信側の175点を重ねない。 -/
def resolveManagement (c : Context) (e : Entry) : Option (Option Management) := do
  match e.management with
  | none => some none
  | some requested =>
    let group ← groupOf e.code
    if requested = .partialTwo then none
    else if !c.remoteDiagnosis then
      if c.localDedicatedFullTimeDoctorWrittenReport && notified c.localStandards requested &&
          (decide (requested = .one) || decide (group ≠ .e001OrE004)) then some (some requested)
      else none
    else
      let r := c.remote
      let partialApplies := c.localStandards.two && higherNotified r.receiverStandards
      let receiverReport := r.receiverDedicatedFullTimeDoctorReportedToSender
      if !r.betweenNotifiedInstitutions then none
      else if requested = .one then
        if receiverReport && r.receiverStandards.one then some (some .one) else none
      else if group = .e001OrE004 then none
      else if partialApplies then
        if receiverReport || c.localDedicatedFullTimeDoctorWrittenReport then some (some .partialTwo) else none
      else if receiverReport && notified r.receiverStandards requested then some (some requested)
      else none

structure ManagementCharge where
  group : Group
  kind : Management
  points : Nat
  deriving DecidableEq, Repr

structure Assessment where
  section1To3 : Nat
  section4 : Nat
  section5Materials : Nat
  emergency : Nat
  management : List ManagementCharge
  deriving DecidableEq, Repr

def Assessment.total (a : Assessment) : Nat :=
  a.section1To3 + a.section4 + a.section5Materials + a.emergency +
  (a.management.map ManagementCharge.points).sum

/-- 月次の単位はＥ００１・Ｅ００４共通、Ｅ１０２、Ｅ２０３の３群。
同月に高位管理加算を算定する場合は、群をまたいでも管理加算１を加えない。 -/
def assess (c : Context) : Option Assessment := do
  if !c.insuranceMedicalInstitution || !c.imagingPerformed || c.entries.isEmpty ||
      (c.remoteDiagnosis && (!c.remote.betweenNotifiedInstitutions ||
        c.entries.any (fun e => (groupOf e.code).isNone))) then none
  else
    let resolved ← c.entries.mapM (fun e => do
      let kind ← resolveManagement c e
      match kind with
      | none => some none
      | some kind => do
        let group ← groupOf e.code
        some (some (group, kind)))
    let requested := resolved.filterMap id
    let high := requested.any (fun (_, k) => decide (k ≠ .one)) ||
      c.managementHistoryThisMonth.any (fun h => decide (h.kind ≠ .one))
    -- 既算定の管理加算１を残したまま高位加算へ変更することは認めない。
    if high && c.managementHistoryThisMonth.any (fun h => decide (h.kind = .one)) then none else
    let current := requested.filter (fun (g, k) =>
      !(high && decide (k = .one)) &&
      !c.managementHistoryThisMonth.any (fun h => decide (h.group = g)))
    let unique := current.eraseDups
    -- 同じ群で複数種類を同時に請求する入力は認めない。
    if (unique.map Prod.fst).eraseDups.length != unique.length then none else
      let emergency := !c.inpatient && c.urgent && c.photographyInsideInstitution &&
        c.diagnosisInsideInstitution && !c.emergencyAdditionClaimedToday &&
        (!c.time.withinDisplayedHours || c.time.holiday || InitialConsultation.deepNight c.time)
      some {
        section1To3 := (c.entries.map Entry.scheduledPoints).sum
        section4 := c.section4Points.sum
        section5Materials := c.section5MaterialPoints.sum
        emergency := if emergency then 110 else 0
        management := unique.map (fun (group, kind) => ⟨group, kind, managementPoints kind⟩) }

def points (c : Context) : Option Nat := (assess c).map Assessment.total

/-! 各区分の100点は合算を確認する仮の入力であり、実際のＥ区分の点数ではない。 -/
private def entry (code : Code) (kind : Option Management := none) : Entry :=
  ⟨code, .section1, 100, kind⟩
private def localContext : Context :=
  { entries := [entry .e102 (some .two)]
    localStandards := { one := true, two := true, three := true, four := true }
    localDedicatedFullTimeDoctorWrittenReport := true }
private def remoteContext : Context :=
  { localContext with
    remoteDiagnosis := true
    localStandards := {}
    remote := {
      betweenNotifiedInstitutions := true
      receiverStandards := { one := true, two := true, three := true, four := true }
      receiverDedicatedFullTimeDoctorReportedToSender := true } }

example : points { entries := [entry .other], section4Points := [12, 23], section5MaterialPoints := [7] } = some 142 := by decide
example : points { entries := [entry .other], urgent := true, photographyInsideInstitution := true, diagnosisInsideInstitution := true, time := { holiday := true } } = some 210 := by decide
example : points { entries := [entry .other], urgent := true, photographyInsideInstitution := true, diagnosisInsideInstitution := true, time := { holiday := true }, inpatient := true } = some 100 := by decide
example : points { entries := [entry .other], urgent := true, photographyInsideInstitution := true, diagnosisInsideInstitution := true, time := { holiday := true }, emergencyAdditionClaimedToday := true } =
    some 100 := by decide
example : points { entries := [entry .other], urgent := true, photographyInsideInstitution := true, time := { holiday := true } } = some 100 := by decide
example : points { entries := [entry .other], urgent := true, photographyInsideInstitution := true, diagnosisInsideInstitution := true } = some 100 := by decide
example : points { entries := [entry .other], urgent := true, photographyInsideInstitution := true, diagnosisInsideInstitution := true, time := { minute := 1320 } } = some 210 := by decide
example : points localContext = some 275 := by decide
example : points { localContext with localDedicatedFullTimeDoctorWrittenReport := false } = none := by decide
example : points { localContext with localStandards := {} } = none := by decide
example : points { localContext with entries := [entry .e001 (some .two)] } = none := by decide
example : points { localContext with entries := [entry .e001 (some .one), entry .e004 (some .one)] } =
    some 270 := by decide
example : points { localContext with entries := [entry .e102 (some .one), entry .e203 (some .one)] } =
    some 340 := by decide
example : points { localContext with entries := [entry .e102 (some .two), entry .e203 (some .two)] } =
    some 550 := by decide
example : points { localContext with entries := [entry .e203 (some .three)] } = some 335 := by decide
example : points { localContext with entries := [entry .e203 (some .four)] } = some 440 := by decide
example : points { localContext with managementHistoryThisMonth := [⟨.e102, .two⟩] } = some 100 := by decide
example : points { localContext with entries := [entry .e001 (some .one)], managementHistoryThisMonth := [⟨.e102, .two⟩] } = some 100 := by decide
example : points { localContext with entries := [entry .e001 (some .one), entry .e102 (some .two)] } =
    some 375 := by decide
example : points { localContext with entries := [entry .e102 (some .two), entry .e102 (some .three)] } =
    none := by decide
example : points { localContext with entries := [entry .other (some .one)] } = none := by decide
example : points { remoteContext with remote := {} } = none := by decide
example : points { remoteContext with entries := [entry .other] } = none := by decide
example : points { remoteContext with entries := [entry .e001 (some .one)] } = some 170 := by decide
example : points remoteContext = some 275 := by decide
example : points { remoteContext with entries := [entry .e203 (some .four)] } = some 440 := by decide
example : points { remoteContext with localStandards := { two := true } } = some 266 := by decide
example : points { remoteContext with localStandards := { two := true }, entries := [entry .e203 (some .four)] } = some 266 := by decide
-- 通則７の最後の文：送信側で読影・文書報告しても175点に戻らない。
example : points { remoteContext with localStandards := { two := true }, remote := { betweenNotifiedInstitutions := true, receiverStandards := { three := true } } } =
    some 266 := by decide
example : points { remoteContext with localStandards := { two := true }, localDedicatedFullTimeDoctorWrittenReport := false, remote := { betweenNotifiedInstitutions := true, receiverStandards := { three := true } } } = none := by decide
example : points { remoteContext with localStandards := { two := true }, managementHistoryThisMonth := [⟨.e102, .partialTwo⟩] } = some 100 := by decide
example : points { entries := [] } = none := by decide

example : points { localContext with managementHistoryThisMonth := [⟨.e001OrE004, .one⟩] } = none := by decide

end Sanri.MedicalFee.Imaging
