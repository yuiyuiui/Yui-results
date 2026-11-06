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

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (k : ℕ) (z w : YuiEucl (k + 1)), dist z w ^ 2 = dist (YuiHead z) (YuiHead w) ^ 2 + |YuiLast z - YuiLast w| ^ 2" := by
  intro k z w
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
  rfl

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k)) := by
  intro k
  have hinv : ∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t := by
    intro x t
    constructor
    · ext i
      simp [YuiHead, YuiSnoc]
    · simp [YuiLast, YuiSnoc]
  have hrec : ∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z := by
    intro z
    ext i
    cases i using Fin.lastCases <;> simp [YuiHead, YuiLast, YuiSnoc]
  refine ⟨hinv, hrec, ?_, ?_, ?_⟩
  · intro x y t u
    have hs := yui_aux_0001 n E k (YuiSnoc x t) (YuiSnoc y u)
    rw [(hinv x t).1, (hinv y u).1, (hinv x t).2, (hinv y u).2] at hs
    rw [← hs, Real.sqrt_sq (dist_nonneg)]
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    have hs := yui_aux_0001 n E k z w
    have ha := sq_nonneg (YuiLast z - YuiLast w)
    have hz : 0 ≤ dist z w := dist_nonneg
    have hh : 0 ≤ dist (YuiHead z) (YuiHead w) := dist_nonneg
    norm_num only [NNReal.coe_one, one_mul]
    nlinarith [sq_abs (YuiLast z - YuiLast w)]
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    have hs := yui_aux_0001 n E k z w
    have hh := sq_nonneg (dist (YuiHead z) (YuiHead w))
    have hz : 0 ≤ dist z w := dist_nonneg
    have ha := abs_nonneg (YuiLast z - YuiLast w)
    norm_num only [NNReal.coe_one, one_mul]
    rw [Real.dist_eq]
    nlinarith

#check @T003
#print axioms T003

end Translation
