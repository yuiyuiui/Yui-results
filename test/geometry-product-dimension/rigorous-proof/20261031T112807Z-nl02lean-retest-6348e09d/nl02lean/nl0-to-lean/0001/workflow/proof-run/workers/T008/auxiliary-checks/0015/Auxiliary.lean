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
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T007 : 1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (U : Set (YEuclid n)) (J : Set ℝ) (a : ℝ), 0 ≤ a → Metric.ediam U ≤ ENNReal.ofReal a → (∀ s ∈ J, ∀ t ∈ J, dist s t ≤ a) → Metric.ediam {z : YEuclid (n+1) | yHoriz z ∈ U ∧ yVert z ∈ J} ≤ ENNReal.ofReal (Real.sqrt 2 * a)" := by
  intro U J a ha hd hJ
  apply Metric.ediam_le_of_forall_dist_le
  intro z hz w hw
  have hh : dist (yHoriz z) (yHoriz w) ≤ a := by
    exact (edist_le_ofReal ha).mp ((Metric.edist_le_ediam_of_mem hz.1 hw.1).trans hd)
  have hv : dist (yVert z) (yVert w) ≤ a := hJ _ hz.2 _ hw.2
  have heq : dist z w ^ 2 = dist (yHoriz z) (yHoriz w) ^ 2 + dist (yVert z) (yVert w) ^ 2 := by
    rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_castSucc, PiLp.dist_sq_eq_of_L2]
    rfl
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hh0 : 0 ≤ dist (yHoriz z) (yHoriz w) := dist_nonneg
  have hv0 : 0 ≤ dist (yVert z) (yVert w) := dist_nonneg
  have hd0 : 0 ≤ dist z w := dist_nonneg
  apply (sq_le_sq₀ hd0 (mul_nonneg hsq0 ha)).mp
  rw [mul_pow, hsq, heq]
  nlinarith [mul_self_le_mul_self hh0 hh, mul_self_le_mul_self hv0 hv]
#check @checked
#print axioms checked
end YuiAuxiliary
