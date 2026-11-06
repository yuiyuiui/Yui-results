import Mathlib
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
namespace YuiBasis
noncomputable def Content {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ δ),
    ∑' i, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ s
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
noncomputable def appendCoord (n : ℕ) (p : Ambient n × ℝ) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
end YuiBasis

open YuiBasis
namespace YuiPlan
noncomputable def H {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  hausdorffMeasure s A
noncomputable def C {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  YuiBasis.Content s (ENNReal.ofReal δ) A
end YuiPlan
open YuiPlan
namespace YuiPortTypes
abbrev T011.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤
abbrev T013 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S
end YuiPortTypes

namespace Translation
set_option autoImplicit false

theorem T014 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : @YuiPortTypes.T013 n E) :
    dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  have hprod : dimH (E ×ˢ YuiBasis.unitInterval) = dimH E + 1 ∧
      dimH (E ×ˢ YuiBasis.unitInterval) ≠ ⊤ :=
    h_T011 (YuiBasis.Ambient n) E h_H001 h_T001.2
  have himage : dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) =
      dimH (E ×ˢ YuiBasis.unitInterval) :=
    h_T013.2.2.2.2 (E ×ˢ YuiBasis.unitInterval)
  refine ⟨himage.trans hprod.1, h_T001.2, ?_⟩
  rw [himage]
  exact hprod.2

#check @T014
#print axioms T014

end Translation
