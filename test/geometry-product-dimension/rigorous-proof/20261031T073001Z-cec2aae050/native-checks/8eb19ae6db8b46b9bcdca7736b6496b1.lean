import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "LipschitzWith 1 (@GP.horizontal n) ∧ LipschitzWith 1 (@GP.vertical n)" := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    have hsum : dist x y ^ 2 =
        dist (GP.horizontal x) (GP.horizontal y) ^ 2 +
          dist (GP.vertical x) (GP.vertical y) ^ 2 := by
      simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc,
        GP.horizontal, GP.vertical, WithLp.toLp_apply]
    nlinarith [sq_nonneg (dist (GP.vertical x) (GP.vertical y)),
      dist_nonneg (x := GP.horizontal x) (y := GP.horizontal y),
      dist_nonneg (x := x) (y := y)]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    have hsum : dist x y ^ 2 =
        dist (GP.horizontal x) (GP.horizontal y) ^ 2 +
          dist (GP.vertical x) (GP.vertical y) ^ 2 := by
      simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc,
        GP.horizontal, GP.vertical, WithLp.toLp_apply]
    nlinarith [sq_nonneg (dist (GP.horizontal x) (GP.horizontal y)),
      dist_nonneg (x := GP.vertical x) (y := GP.vertical y),
      dist_nonneg (x := x) (y := y)]
#check @checked
#print axioms checked
end YuiAuxiliary
