import Sanri.SpecimenJudgmentRouting
import Sanri.D023References
import Sanri.SpecimenSelectionInventory

namespace Sanri.MedicalFee.SpecimenRawDay

open Sanri.History Sanri.Logic

/-- 区分別評価を通過した個別実施。包括・併施の適用範囲は日次側で確認する。 -/
structure Individual where
  private mk ::
  performance : Performance SpecimenJudgment.Test
  points : Nat
  plasmaPanelItem : Option D006PlasmaPanel.DrawItem := none
  selectionKey : Option SpecimenSelectionInventory.ItemKey := none

namespace Individual

private def fromRule {Context Result Item : Type} (row : Performance Item)
    (test : SpecimenJudgment.Test) (ctx : Context) (rules : List (Rule Context Result))
    (result : Result) (project : Result → Nat) (_ : Satisfies rules ctx result) : Individual :=
  ⟨{ row with item := test }, project result, none, none⟩

def d006_2 (c : D006Leukemia.D006_2.Context) (row : Performance Unit) (ordinary : SpecimenJudgment.Category)
    (eligible : D006Leukemia.D006_2.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Leukemia.D006_2.judgmentTest ordinary) c
    D006Leukemia.D006_2.rules D006Leukemia.D006_2.points id
    ((D006Leukemia.D006_2.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_3 (c : D006Leukemia.D006_3.Context) (row : Performance D006Leukemia.D006_3.Item) (ordinary : SpecimenJudgment.Category)
    (eligible : D006Leukemia.D006_3.Eligible c) (_item : row.item = c.item) : Individual :=
  fromRule row (D006Leukemia.D006_3.judgmentTest c.item ordinary) c
    D006Leukemia.D006_3.rules D006Leukemia.D006_3.points id
    ((D006Leukemia.D006_3.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_4 (c : D006Genetic.Context)
    (eligible : D006Genetic.Eligible c) : Individual :=
  fromRule c.principal.performance (D006Genetic.judgmentTest c.item) c
    D006Genetic.rules (D006Genetic.scheduled c) (·.total)
    ((D006Genetic.satisfies_iff _ _).mpr ⟨eligible, rfl⟩)

def d006_5 (c : D006Chromosome.Context) (row : Performance D006Chromosome.Item)
    (eligible : D006Chromosome.Eligible c) (_site : row.site = c.site) (_item : row.item = c.item) : Individual :=
  fromRule row (D006Chromosome.judgmentTest c.item) c
    D006Chromosome.rules (D006Chromosome.scheduled c) (·.total)
    ((D006Chromosome.satisfies_iff _ _).mpr ⟨eligible, rfl⟩)

def d006_6 (c : D006GeneTests.Immune.Context) (row : Performance Unit)
    (eligible : D006GeneTests.Immune.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006GeneTests.judgmentTest .immuneRearrangement) c
    D006GeneTests.Immune.rules D006GeneTests.Item.immuneRearrangement.points id
    ((D006GeneTests.Immune.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_7 (c : D006GeneTests.Ugt.Context) (row : Performance Unit)
    (eligible : D006GeneTests.Ugt.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006GeneTests.judgmentTest .ugtPolymorphism) c
    D006GeneTests.Ugt.rules D006GeneTests.Item.ugtPolymorphism.points id
    ((D006GeneTests.Ugt.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_8 (c : D006GeneTests.Krt19.Context)
    (eligible : D006GeneTests.Krt19.Eligible c) : Individual :=
  fromRule c.performance (D006GeneTests.judgmentTest .krt19) c
    D006GeneTests.Krt19.rules D006GeneTests.Item.krt19.points id
    ((D006GeneTests.Krt19.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_9 (c : D006GeneTests.Wt1.Context) (row : Performance Unit)
    (eligible : D006GeneTests.Wt1.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006GeneTests.judgmentTest .wt1) c D006GeneTests.Wt1.rules D006GeneTests.Item.wt1.points id
    ((D006GeneTests.Wt1.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_10 (c : D006GeneTests.Ccr4.Context) (row : Performance Unit)
    (eligible : D006GeneTests.Ccr4.Eligible c) : Individual :=
  fromRule row (D006GeneTests.Ccr4.judgmentTest) c D006GeneTests.Ccr4.rules D006GeneTests.Ccr4.points id
    ((D006GeneTests.Ccr4.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_11 (c : D006GeneTests.Fusion.Context) (row : Performance Unit)
    (eligible : D006GeneTests.Fusion.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006GeneTests.Fusion.judgmentTest) c D006GeneTests.Fusion.rules D006GeneTests.Fusion.points id
    ((D006GeneTests.Fusion.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_12 (c : D006GeneTests.Egfr.Context) (r : D006GeneTests.Egfr.Result)
    (eligible : D006GeneTests.Egfr.Eligible c) (scheduled : D006GeneTests.Egfr.scheduled c = some r) : Individual :=
  { fromRule c.performance D006GeneTests.Egfr.judgmentTest c D006GeneTests.Egfr.rules r (·.total)
      ((D006GeneTests.Egfr.satisfies_iff _ _).mpr ⟨eligible, scheduled⟩) with
    plasmaPanelItem := some .egfr }

def d006_13 (c : D006GeneTests.ResidualDisease.Context)
    (eligible : D006GeneTests.ResidualDisease.Eligible c) : Individual :=
  fromRule c.performance (D006GeneTests.ResidualDisease.judgmentTest c.performance.item) c
    D006GeneTests.ResidualDisease.rules c.performance.item.points id
    ((D006GeneTests.ResidualDisease.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_14 (c : D006Oncology.Flt3.Context) (row : Performance Unit)
    (eligible : D006Oncology.Flt3.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Oncology.judgmentTest .flt3) c D006Oncology.Flt3.rules D006Oncology.Item.flt3.points id
    ((D006Oncology.Flt3.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_15 (c : D006Oncology.Bladder.Context)
    (eligible : D006Oncology.Bladder.Eligible c) : Individual :=
  fromRule c.performance (D006Oncology.judgmentTest .bladder) c
    D006Oncology.Bladder.rules D006Oncology.Item.bladder.points id
    ((D006Oncology.Bladder.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_16 (c : D006Oncology.Jak2.Context) (row : Performance Unit)
    (eligible : D006Oncology.Jak2.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Oncology.judgmentTest .jak2) c D006Oncology.Jak2.rules D006Oncology.Item.jak2.points id
    ((D006Oncology.Jak2.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_17 (c : D006Oncology.Pharmacogenetics.Context) (row : Performance D006Oncology.Pharmacogenetics.Item)
    (eligible : D006Oncology.Pharmacogenetics.Eligible c) (_site : row.site = c.site) (_item : row.item = c.item) : Individual :=
  fromRule row (D006Oncology.Pharmacogenetics.judgmentTest c.item) c
    D006Oncology.Pharmacogenetics.rules D006Oncology.Pharmacogenetics.points id
    ((D006Oncology.Pharmacogenetics.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_18 (c : D006Oncology.Brca.Context) (row : Performance D006Oncology.Brca.Item)
    (eligible : D006Oncology.Brca.Eligible c) (_item : row.item = c.item) : Individual :=
  fromRule row (D006Oncology.Brca.judgmentTest c.item) c D006Oncology.Brca.rules D006Oncology.Brca.points id
    ((D006Oncology.Brca.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_19 (c : D006Profiling.Context) (row : Performance D006Profiling.Item) (p : Nat)
    (_eligible : D006Profiling.Eligible c) (_site : row.site = c.site) (_item : row.item = c.item) (rate : Satisfies D006Profiling.rules c p) : Individual :=
  fromRule row (D006Profiling.judgmentTest c.item) c D006Profiling.rules p id
    rate

def d006_20 (c : D006Targeted.Corneal.Context) (row : Performance Unit)
    (eligible : D006Targeted.Corneal.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Targeted.judgmentTest .cornealDystrophy) c
    D006Targeted.Corneal.rules D006Targeted.Item.cornealDystrophy.points id
    ((D006Targeted.Corneal.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_21 (c : D006Targeted.Viscoelastic.Context)
    (eligible : D006Targeted.Viscoelastic.Eligible c) : Individual :=
  fromRule c.performance (D006Targeted.judgmentTest .viscoelastic) c
    D006Targeted.Viscoelastic.rules D006Targeted.Item.viscoelastic.points id
    ((D006Targeted.Viscoelastic.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_22 (c : D006Targeted.PlasmaRas.Context) (row : Performance Unit)
    (eligible : D006Targeted.PlasmaRas.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Targeted.judgmentTest .plasmaRas) c
    D006Targeted.PlasmaRas.rules D006Targeted.Item.plasmaRas.points id
    ((D006Targeted.PlasmaRas.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_23 (c : D006Targeted.HomologousRecombination.Context) (row : Performance Unit)
    (eligible : D006Targeted.HomologousRecombination.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Targeted.judgmentTest .homologousRecombination) c
    D006Targeted.HomologousRecombination.rules D006Targeted.Item.homologousRecombination.points id
    ((D006Targeted.HomologousRecombination.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_24 (c : D006Targeted.LungPanel.Context)
    (eligible : D006Targeted.LungPanel.Eligible c) : Individual :=
  fromRule c.performance (D006Targeted.judgmentTest .lungPanel) c
    D006Targeted.LungPanel.rules D006Targeted.Item.lungPanel.points id
    ((D006Targeted.LungPanel.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_25 (c : D006Targeted.Cyp2c9.Context) (row : Performance Unit)
    (eligible : D006Targeted.Cyp2c9.Indication c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Targeted.judgmentTest .cyp2c9) c
    D006Targeted.Cyp2c9.rules D006Targeted.Item.cyp2c9.points id
    ((D006Targeted.Cyp2c9.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_26 (c : D006Targeted.StructuralVariation.Context) (row : Performance Unit)
    (eligible : D006Targeted.StructuralVariation.Eligible c) (_site : row.site = c.site) : Individual :=
  fromRule row (D006Targeted.judgmentTest .structuralVariation) c
    D006Targeted.StructuralVariation.rules D006Targeted.Item.structuralVariation.points id
    ((D006Targeted.StructuralVariation.satisfies_iff _ _).mpr ⟨rfl, eligible⟩)

def d006_27 (c : D006PlasmaPanel.Context) (_eligible : D006PlasmaPanel.Eligible c) : Individual :=
  { fromRule c.performance (D006PlasmaPanel.judgmentTest c.performance.item)
      c.performance.item D006PlasmaPanel.individualRules c.performance.item.points id
      ((D006PlasmaPanel.individual_iff _ _).mpr rfl) with
    plasmaPanelItem := some (.panel c.performance.item) }

def d006_28_to_31 (c : D006Late.Context)
    (eligible : D006Late.Eligible c) : Individual :=
  fromRule c.performance (D006Late.judgmentTest c.performance.item) c
    D006Late.rules c.performance.item.points id
    ((D006Late.permits_iff _ _).mpr ⟨eligible, rfl⟩).2

def d010 (c : D010.Context) (p : Nat)
    (_eligible : D010.Eligible c) (rate : Satisfies D010.rules c p) : Individual :=
  fromRule c.performance (D010.judgmentTest c.performance.item) c D010.rules p id
    rate

def d011 (c : D011.Context)
    (_eligible : D011.Eligible c) : Individual :=
  fromRule c.performance (D011.judgmentTest c.performance.item) c D011.rules c.performance.item.points id
    ((D011.rate_iff _ _).mpr rfl)

def d016 (c : D016.Context)
    (_eligible : D016.Eligible c) : Individual :=
  fromRule c.performance (D016.judgmentTest c.performance.item) c.performance.item
    D016.rates c.performance.item.points id
    ((D016.rate_iff _ _).mpr rfl)

def microscopyKey : D017.Item → String
  | .specializedMicroscopy => "specializedMicroscopy"
  | .heatedAmoeba => "heatedAmoeba"
  | .otherMicroscopy => "otherMicroscopy"

def cultureKey : D018.Item → String
  | .respiratory => "respiratory"
  | .gastrointestinal => "gastrointestinal"
  | .bloodOrPuncture => "bloodOrPuncture"
  | .genitourinary => "genitourinary"
  | .other => "other"
  | .simple => "simple"

def infectionKey : D012.Item → Option String
  | .endotoxin => some "endotoxin"
  | .rapidGroupAStrep => some "rapidGroupAStrep"
  | .ecoliO157Antibody => some "ecoliO157Antibody"
  | .ecoliO157Antigen => some "ecoliO157Antigen"
  | .ecoliSerotype => some "ecoliSerotype"
  | .gonococcusAntigen => some "gonococcusAntigen"
  | _ => none

def d017 (c : D017.Context) (base extra : Nat)
    (_eligible : D017.InScope c) (rate : Satisfies D017.resultRules c (some (base, extra))) : Individual :=
  { fromRule c.performance (D017.judgmentTest c.performance.item) c
      D017.resultRules (some (base, extra)) (fun _ => base + extra) rate with
    selectionKey := some ("D017", microscopyKey c.performance.item) }

def d018 (c : D018.Context)
    (_eligible : D018.InScope c) : Individual :=
  { fromRule c.performance (D018.judgmentTest c.performance.item) c
      D018.resultRules (D018.assessedResult c) (·.total)
      ((D018.result_iff _ _).mpr rfl) with
    selectionKey := some ("D018", cultureKey c.performance.item) }

def d019 (c : D019.Context)
    (eligible : D019.InScope c) : Individual :=
  fromRule c.performance (D019.judgmentTest c.performance.item) c D019.rates c.performance.item.points id
    ((D019.rates_iff _ _).mpr ⟨eligible.1, rfl⟩)

def d019_2 (c : D019Yeast.Context)
    (_eligible : D019Yeast.InScope c) (rate : Satisfies D019Yeast.rates c D019Yeast.points) : Individual :=
  fromRule c.performance (D019Yeast.judgmentTest) c D019Yeast.rates D019Yeast.points id
    rate

def d020 (c : D020.Context)
    (_eligible : D020.InScope c) (rate : Satisfies D020.rates c c.performance.item.points) : Individual :=
  fromRule c.performance (D020.judgmentTest c.performance.item) c D020.rates c.performance.item.points id
    rate

def d021 (c : D021.Context)
    (_eligible : D021.InScope c) (rate : Satisfies D021.rates c D021.points) : Individual :=
  fromRule c.performance (D021.judgmentTest) c D021.rates D021.points id
    rate

def d022 (c : D022.Context)
    (_eligible : D022.InScope c) (rate : Satisfies D022.rates c D022.points) : Individual :=
  fromRule c.performance (D022.judgmentTest) c D022.rates D022.points id
    rate

def d023_2 (c : D023Other.Context)
    (_eligible : D023Other.InScope c) : Individual :=
  fromRule c.performance (D023Other.judgmentTest c.performance.item) c
    D023Other.rates c.performance.item.points id
    ((D023Other.rates_iff _ _).mpr rfl)

/-- 保持されている履歴上の実施を日次入力と照合する。 -/
def d023Anchor : D023.OutpatientTest → Option (Performance Unit)
  | .genitourinary e => some { e.performance with item := () }
  | .groupStrep e => some { e.performance with item := () }
  | .hbv e => some { e.performance with item := () }
  | .ebv e => some { e.performance with item := () }
  | .hcv e => some { e.performance with item := () }
  | .hpv e => some { e.performance with item := () }
  | .pertussis e => some { e.performance with item := () }
  | .pneumoniae e => some { e.performance with item := () }
  | .pylori e => some { e.performance with item := () }
  | .mac e => some { e.performance with item := () }
  | .hbvVariant e => some { e.performance with item := () }
  | .methicillin e => some { e.performance with item := () }
  | .sars e => some { e.performance with item := () }
  | .htlv e => some { e.performance with item := () }
  | .herpes e => some { e.performance with item := () }
  | .hivQuantity e => some { e.performance with item := () }
  | .covid e => some { e.performance with item := () }
  | .mpox e => some { e.performance with item := () }
  | .cmvDetection e => some { e.performance with item := () }
  | .tbSingle e => some { e.2.performance with item := () }
  | .tbDual e => some { e.performance with item := () }
  | .pneumoniaPanel e => some { e.performance with item := () }
  | .panel e => some { e.panel.performance with item := () }
  | .csf e => some { e.performance with item := () }
  | .sepsis e => some { e.1.performance with item := () }
  | .hpvGenotype e => some { e.performance with item := () }
  | .hivGenotype e => some { e.performance with item := () }
  | _ => none

def d023 (c : D023.OutpatientInput) (row : Performance D023.OutpatientTest)
    (_test : row.item = c.test) (_eligible : D023.OutpatientEligible c)
    (_anchor : ∀ p, d023Anchor c.test = some p → p = { row with item := () }) : Individual :=
  let key := match row.item with
    | .groupStrep _ => some ("D023", "groupAStrep")
    | _ => none
  ⟨{ row with item := c.test.judgmentTest }, c.points, none, key⟩

def d023Reference (a : D023References.Assessment) (row : Performance Unit) (p : Nat)
    (_valid : a.Valid) (_id : a.legacy.1 = row.id)
    (_anchor : ∀ c, a = .mycobacteria c → c.performance = row)
    (_rate : a.legacy.2.points = some p) : Individual :=
  ⟨{ row with item := a.legacy.2.judgmentTest }, p, none, none⟩

def d001 (c : D001.Context) (p : Nat) (_eligible : D001.Eligible c)
    (rate : Satisfies D001.rules c p) : Individual :=
  fromRule c.performance (D001.judgmentTest c) c D001.rules p id rate

def d003 (c : D003.Context) (p : Nat) (rate : Satisfies D003.rules c p) : Individual :=
  fromRule c.performance (D003.judgmentTest c) c D003.rules p id rate

def d004 (c : D004.Context) (row : Performance D004.Item)
    (_item : row.item = c.item) (category : SpecimenJudgment.Category) (p : Nat)
    (rate : Satisfies D004.rules c p) : Individual :=
  { fromRule row (D004.judgmentTest c.item category) c D004.rules p id rate with
    selectionKey := if row.item == .jointFluid then some ("D004", "jointFluid") else none }

def d004_3 (c : D004Methylation.Context) (row : Performance Unit)
    (_site : row.site = c.site) (category : SpecimenJudgment.Category) (p : Nat)
    (rate : Satisfies D004Methylation.rules c p) : Individual :=
  fromRule row (D004Methylation.judgmentTest category) c D004Methylation.rules p id rate

def d006 (c : D006.Context) (_eligible : D006.Eligible c)
    (addition : Nat) (rate : Satisfies D006.addOnRules c addition) : Individual :=
  fromRule c.performance (D006.judgmentTest c.item) c D006.addOnRules
    addition (c.item.points + ·) rate

def d008 (c : D008.Context) (_eligible : D008.Eligible c) : Individual :=
  fromRule c.performance (D008.judgmentTest c.performance.item) c.performance.item
    D008.individualRules c.performance.item.points id ((D008.individual_iff _ _).mpr rfl)

def d009 (c : D009.Context) (_eligible : D009.Eligible c) (p : Nat)
    (rate : Satisfies D009.itemRules c.performance.item p) : Individual :=
  fromRule c.performance (D009.judgmentTest c.performance.item) c.performance.item D009.itemRules
    p id rate

def d012 (c : D012.Context) (i : D012.Item) (_item : c.performance.item = .local i)
    (_eligible : D012.Eligible c) : Individual :=
  { fromRule c.performance (D012.judgmentTest i) i D012.rules i.points id
      ((D012.rate_iff _ _).mpr rfl) with
    selectionKey := (infectionKey i).map ("D012", ·) }

def d013 (c : D013.Context) (_eligible : D013.Eligible c) : Individual :=
  fromRule c.performance (D013.judgmentTest c.item) c.item D013.rates c.item.points id
    ((D013.rate_iff _ _).mpr rfl)

def d014 (c : D014.Context) (_eligible : D014.Eligible c) : Individual :=
  fromRule c.performance (D014.judgmentTest c.item) c.item D014.rates c.item.points id
    ((D014.rate_iff _ _).mpr rfl)

def d015 (c : D015.Context) (_eligible : D015.Eligible c)
    (specialistWrittenReport : Bool) : Individual :=
  fromRule c.performance (D015.judgmentTest c.item specialistWrittenReport)
    c.item D015.rates c.item.points id ((D015.rate_iff _ _).mpr rfl)

end Individual
end Sanri.MedicalFee.SpecimenRawDay
