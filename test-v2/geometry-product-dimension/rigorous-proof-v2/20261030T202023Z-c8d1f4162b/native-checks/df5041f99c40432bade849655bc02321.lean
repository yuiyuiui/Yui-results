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

namespace Translation
set_option autoImplicit false

theorem T003 (n : ℕ) (E : Set (YEucl n))  :
    (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine := by
  have hsq : ∀ (m : ℕ) (z w : YEucl (m+1)),
      dist z w ^ 2 = dist (YBase z) (YBase w) ^ 2 + |YLast z-YLast w| ^ 2 := by
    intro m z w
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc, EuclideanSpace.dist_sq_eq]
    simp [YBase, YLast, Real.dist_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m x y t u
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_castSucc, EuclideanSpace.dist_sq_eq]
    simp [YJoin, Real.dist_eq]
  · intro m z
    ext i
    cases i using Fin.lastCases <;> simp [YJoin, YBase, YLast]
  · intro m x t
    constructor
    · ext i
      simp [YBase, YJoin]
    · simp [YLast, YJoin]
  · intro m
    constructor
    · apply LipschitzWith.mk_one
      intro z w
      have h := hsq m z w
      have hz : 0 ≤ dist z w := dist_nonneg
      have hb : 0 ≤ dist (YBase z) (YBase w) := dist_nonneg
      nlinarith [sq_nonneg (YLast z-YLast w)]
    · apply LipschitzWith.mk_one
      intro z w
      rw [Real.dist_eq]
      have h := hsq m z w
      have hz : 0 ≤ dist z w := dist_nonneg
      have hl : 0 ≤ |YLast z-YLast w| := abs_nonneg _
      nlinarith [sq_nonneg (dist (YBase z) (YBase w))]
  · apply Isometry.of_dist_eq
    intro t u
    simpa [EuclideanSpace.dist_eq, YLine, Real.dist_eq] using
      (Real.sqrt_sq_eq_abs (t-u))
  · intro z
    refine ⟨z 0, ?_⟩
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [YLine, hi]

#check @T003
#print axioms T003

end Translation
