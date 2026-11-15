import Mathlib
open Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section

abbrev YuiRn (n : ℕ) := EuclideanSpace ℝ (Fin n)

def YuiContent {X : Type*} [EMetricSpace X] (a : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
    ∑' i, (Metric.ediam (U i)) ^ a

def YuiJoinEquiv (n : ℕ) : (YuiRn n × ℝ) ≃L[ℝ] YuiRn (n + 1) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans
    (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm)

def YuiI : Set ℝ := Set.Icc 0 1

def YuiFmax (n : ℕ) (A : Set (YuiRn n)) : Set (YuiRn n × ℝ) :=
  A ×ˢ YuiI

def YuiFeuc (n : ℕ) (A : Set (YuiRn n)) : Set (YuiRn (n + 1)) :=
  YuiJoinEquiv n '' YuiFmax n A

def YuiLast (n : ℕ) (z : YuiRn (n + 1)) : YuiRn (n + 1) :=
  WithLp.toLp 2 (fun j => z (finRotate (n + 1) j))

def YuiFeucLast (n : ℕ) (A : Set (YuiRn n)) : Set (YuiRn (n + 1)) :=
  YuiLast n '' YuiFeuc n A

namespace YuiClosed
set_option autoImplicit false
theorem P : ∀ (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E), dimH (YuiFeucLast n E) = dimH E + 1 := by sorry
end YuiClosed
