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

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)" := by
  intro k A a ha
  let d : ℝ≥0 := ⟨a, ha.le⟩
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal a := by
    exact (ENNReal.ofReal_coe_nnreal (p := d)).symm
  have hn := h_T001 (YuiEucl k) A a ha
  have hz : dimH A < ENNReal.ofReal a → YuiMeasure a A = 0 := by
    intro h
    rw [hn]
    exact hausdorffMeasure_of_dimH_lt (d := d) (by simpa only [hd] using h)
  have ht : ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤ := by
    intro h
    rw [hn]
    exact hausdorffMeasure_of_lt_dimH (d := d) (by simpa only [hd] using h)
  refine ⟨hn, hz, ht, ?_, ?_⟩
  · intro h
    apply le_of_not_gt
    intro hlt
    have hc := ht hlt
    rw [h] at hc
    exact ENNReal.zero_ne_top hc
  · intro h
    apply le_of_not_gt
    intro hlt
    have hc := hz hlt
    rw [h] at hc
    exact ENNReal.top_ne_zero hc
#check @checked
#print axioms checked
end YuiAuxiliary
