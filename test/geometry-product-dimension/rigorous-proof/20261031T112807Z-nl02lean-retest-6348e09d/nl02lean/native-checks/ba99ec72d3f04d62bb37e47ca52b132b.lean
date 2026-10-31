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
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) : yui_aux_type% "∀ a δ η : ℝ, 1 < a → 0 < δ → 0 < η → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ δ ∧ (N : ℝ) ^ (1 - a) < η" := by
  intro a δ η ha hδ hη
  have hlim : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) Filter.atTop (nhds 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < a - 1)).comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)
  have hinv : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop))
  obtain ⟨N, hN, hδN, hηN⟩ := (Filter.eventually_gt_atTop 0 |>.and
    ((hinv.eventually (gt_mem_nhds hδ)).and (hlim.eventually (gt_mem_nhds hη)))).exists
  exact ⟨N, hN, hδN.le, hηN⟩
#check @checked
#print axioms checked
end YuiAuxiliary
