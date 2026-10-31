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
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T003 : dimH yI ≤ 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0)) (h_T004 : ∀ (δ : ℝ), 0 < δ → ∀ V : ℕ → Set ℝ, yCover δ yI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)) : yui_aux_type% "∀ (s : ℝ), s < 1 → ∀ r : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ (r : ℝ≥0∞) ≤ (ENNReal.ofReal δ) ^ (s - 1)" := by
  intro s hs r
  have he : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), (r : ℝ) ≤ δ ^ (s-1) :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : s-1 < 0)).eventually
      (Filter.eventually_ge_atTop (r : ℝ))
  obtain ⟨δ, hb, hδ⟩ := (he.and self_mem_nhdsWithin).exists
  refine ⟨δ, hδ, ?_⟩
  rw [ENNReal.ofReal_rpow_of_pos hδ]
  have hconv : ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞) := by simp
  rw [← hconv]
  exact ENNReal.ofReal_le_ofReal hb
#check @checked
#print axioms checked
end YuiAuxiliary
