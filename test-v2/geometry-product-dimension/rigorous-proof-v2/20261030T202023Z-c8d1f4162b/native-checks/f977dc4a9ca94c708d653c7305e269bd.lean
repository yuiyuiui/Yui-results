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

theorem T002 (n : ℕ) (E : Set (YEucl n)) (h_T001 : ∀ (m : ℕ) (A : Set (YEucl m)) (s : ℝ), 0 < s → YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A) :
    ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A := by
  intro m A
  refine ⟨bot_le, ?_⟩
  intro s hs
  have hr : (Real.toNNReal s : ℝ) = s := Real.coe_toNNReal s hs.le
  have he : (Real.toNNReal s : ℝ≥0∞) = ENNReal.ofReal s :=
    ENNReal.ofNNReal_toNNReal s
  refine ⟨h_T001 m A s hs, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h_T001 m A s hs]
    have h' : dimH A < (Real.toNNReal s : ℝ≥0∞) := by
      simpa only [he] using h
    simpa only [hr] using
      (hausdorffMeasure_of_dimH_lt (s := A) (d := Real.toNNReal s) h')
  · intro h
    rw [h_T001 m A s hs]
    have h' : (Real.toNNReal s : ℝ≥0∞) < dimH A := by
      simpa only [he] using h
    simpa only [hr] using
      (hausdorffMeasure_of_lt_dimH (s := A) (d := Real.toNNReal s) h')
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (Real.toNNReal s : ℝ) A ≠ ⊤ := by
      rw [hr, ← h_T001 m A s hs, h]
      exact ENNReal.zero_ne_top
    simpa only [he] using
      (dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := Real.toNNReal s) hm)
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (Real.toNNReal s : ℝ) A = ⊤ := by
      rw [hr, ← h_T001 m A s hs]
      exact h
    simpa only [he] using
      (le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := Real.toNNReal s) hm)

#check @T002
#print axioms T002

end Translation
