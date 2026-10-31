import Mathlib
open scoped ENNReal NNReal
noncomputable section
abbrev YEucl (m : ℕ) := EuclideanSpace ℝ (Fin m)
def YI : Set ℝ := Set.Icc 0 1
def YJoin {m : ℕ} (x : YEucl m) (t : ℝ) : YEucl (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YBase {m : ℕ} (z : YEucl (m + 1)) : YEucl m :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def YLast {m : ℕ} (z : YEucl (m + 1)) : ℝ := z (Fin.last m)
def YF {m : ℕ} (A : Set (YEucl m)) : Set (YEucl (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ YI, z = YJoin x t}
def YLine (t : ℝ) : YEucl 1 := WithLp.toLp 2 (fun _ => t)
def YCover {X : Type*} [PseudoEMetricSpace X]
    (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def YCost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s
def YContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YCover δ A U), YCost s U
def YHaus {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A
def YCritical {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) : Prop :=
  0 ≤ dimH A ∧ ∀ s : ℝ, 0 < s →
    YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → YHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → YHaus s A = ⊤) ∧
    (YHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (YHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEucl n))  : yui_aux_type% "∀ a : ℝ, 0 < a → ∀ k : ℕ, 0 < k → YCost a (fun j : ℕ => if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) = ENNReal.ofReal ((k : ℝ) ^ (1 - a))" := by
  intro a ha k hk
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hd : ∀ j : ℕ, Metric.ediam (Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k)) = ENNReal.ofReal (1 / (k : ℝ)) := by
    intro j
    rw [Real.ediam_Icc]
    congr 1
    ring
  unfold YCost
  rw [tsum_eq_sum (s := Finset.range k)]
  · calc
      (∑ j ∈ Finset.range k, Metric.ediam (if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) ^ a)
          = (k : ℝ≥0∞) * (ENNReal.ofReal (1 / (k : ℝ))) ^ a := by
            simp [Finset.sum_congr rfl (fun j hj => by rw [if_pos (Finset.mem_range.mp hj), hd]), nsmul_eq_mul]
      _ = ENNReal.ofReal ((k : ℝ) * (1 / (k : ℝ)) ^ a) := by
            rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((k : ℝ) ^ (1 - a)) := by
            congr 1
            rw [sub_eq_add_neg, Real.rpow_add hkR, Real.rpow_one,
              Real.rpow_neg_eq_inv_rpow, one_div]
  · intro j hj
    have hj' : ¬ j < k := by simpa using hj
    simp [hj', ENNReal.zero_rpow_of_pos ha]
#check @checked
#print axioms checked
end YuiAuxiliary
