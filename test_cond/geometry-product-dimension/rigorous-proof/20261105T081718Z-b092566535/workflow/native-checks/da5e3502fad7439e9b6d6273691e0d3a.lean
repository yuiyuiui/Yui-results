import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T016
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T013 : ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0) (h_T015 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → (ENNReal.ofReal δ) ^ (s - 1) ≤ YuiContent s δ YuiI) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → YuiMeasure s YuiI = ⊤" := by
  intro s hs hs1
  have h0 : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have ht : Filter.Tendsto (fun δ : ℝ => (ENNReal.ofReal δ) ^ (s - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((0 : ℝ≥0∞) ^ (s - 1))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h0
  rw [ENNReal.zero_rpow_of_neg (sub_neg.mpr hs1)] at ht
  apply top_unique
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (h_T015 s δ hs hs1 hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))

end Local_T016
open Local_T016 in
theorem T016 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T013 : ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0) (h_T015 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → (ENNReal.ofReal δ) ^ (s - 1) ≤ YuiContent s δ YuiI) :
    dimH YuiI = 1 := by
  apply le_antisymm
  · by_contra h
    have hd : (1 : ℝ≥0∞) < dimH YuiI := lt_of_not_ge h
    obtain ⟨a, ha1, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hd
    have ha : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
    have ha0 : 0 < (a : ℝ) := lt_trans zero_lt_one ha
    have hm : MeasureTheory.Measure.hausdorffMeasure (a : ℝ) YuiI = 0 :=
      (h_T001 ℝ YuiI (a : ℝ) ha0).symm.trans (h_T013 (a : ℝ) ha)
    have hb : dimH YuiI ≤ (a : ℝ≥0∞) :=
      dimH_le_of_hausdorffMeasure_ne_top (d := a) (by rw [hm]; exact zero_ne_top)
    exact had.not_ge hb
  · refine ENNReal.le_of_forall_pos_nnreal_lt fun s hs hs1 => ?_
    have hs0 : 0 < (s : ℝ) := by exact_mod_cast hs
    have hsreal1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    have hm : MeasureTheory.Measure.hausdorffMeasure (s : ℝ) YuiI = ⊤ :=
      (h_T001 ℝ YuiI (s : ℝ) hs0).symm.trans
        (@yui_aux_0001 n E h_T001 h_T002 h_T013 h_T015 (s : ℝ) hs0 hsreal1)
    exact le_dimH_of_hausdorffMeasure_eq_top (d := s) hm

#check @T016
#print axioms T016

end Translation
