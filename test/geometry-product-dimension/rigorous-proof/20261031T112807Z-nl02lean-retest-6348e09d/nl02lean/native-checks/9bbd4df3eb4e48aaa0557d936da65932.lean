import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) : yui_aux_type% "∃ b : ℝ, 0 < b ∧ E ⊆ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm '' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-b) b)) ∧ MeasureTheory.Measure.hausdorffMeasure (n : ℝ) E < ⊤" := by
  classical
  let e : YEuclid n ≃L[ℝ] (Fin n → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  obtain ⟨b, hb, hbound⟩ := h_H003.isBounded.exists_pos_norm_le
  let B : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-b) b)
  have hsub : E ⊆ e.symm '' B := by
    intro x hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    change ∀ i ∈ Set.univ, e x i ∈ Set.Icc (-b) b
    intro i _
    have hi : |x i| ≤ b := by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans (hbound x hx)
    exact abs_le.mp hi
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hm : MeasureTheory.Measure.hausdorffMeasure (n : ℝ) B < ⊤ := by
    have heq : (MeasureTheory.Measure.hausdorffMeasure (n : ℝ) : Measure (Fin n → ℝ)) = volume := by
      simpa only [Fintype.card_fin] using (MeasureTheory.hausdorffMeasure_pi_real (ι := Fin n))
    rw [heq]
    exact hB.measure_lt_top
  have himg : MeasureTheory.Measure.hausdorffMeasure (n : ℝ) (e.symm '' B) < ⊤ := by
    apply lt_of_le_of_lt (e.symm.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg n) B)
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top) hm
  exact ⟨b, hb, hsub, (measure_mono hsub).trans_lt himg⟩
#check @checked
#print axioms checked
end YuiAuxiliary
