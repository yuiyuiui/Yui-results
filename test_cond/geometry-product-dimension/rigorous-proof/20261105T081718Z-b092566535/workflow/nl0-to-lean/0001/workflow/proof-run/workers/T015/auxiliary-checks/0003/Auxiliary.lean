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
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T014 : ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)) : yui_aux_type% "∀ (a b : ℝ≥0∞), a ≤ b → b⁻¹ ≤ a⁻¹" := by
  intro a b h
  exact ENNReal.inv_le_inv' h

theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_T014 : ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)) : yui_aux_type% "∀ (s δ : ℝ) (ρ : ℝ≥0∞), 0 < s → s < 1 → 0 < δ → ρ ≤ ENNReal.ofReal δ → (ENNReal.ofReal δ) ^ (s - 1) * ρ ≤ ρ ^ s" := by
  intro s δ ρ hs hs1 hδ hρ
  by_cases hzero : ρ = 0
  · simp [hzero, ENNReal.zero_rpow_of_pos hs]
  have hfinite : ρ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hρ
  have hneg : (ENNReal.ofReal δ) ^ (s - 1) ≤ ρ ^ (s - 1) := by
    have hp : ρ ^ (1 - s) ≤ (ENNReal.ofReal δ) ^ (1 - s) :=
      ENNReal.rpow_le_rpow hρ (by linarith)
    have hi := (@yui_aux_0001 n E h_T014) _ _ hp
    simpa only [← ENNReal.rpow_neg, neg_sub] using hi
  calc
    (ENNReal.ofReal δ) ^ (s - 1) * ρ ≤ ρ ^ (s - 1) * ρ := mul_le_mul_right' hneg ρ
    _ = ρ ^ s := by
      have heq : s - 1 + 1 = s := by ring
      simpa only [ENNReal.rpow_one, heq] using (ENNReal.rpow_add (s - 1) 1 hzero hfinite).symm
#check @checked
#print axioms checked
end YuiAuxiliary
