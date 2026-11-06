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

namespace Translation
set_option autoImplicit false

theorem T013 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T012 : Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n)) :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S := by
  rcases h_T012 with ⟨hbij, hdist, hlip, hanti⟩
  refine ⟨hbij, hdist, hlip, hanti, ?_⟩
  intro S
  exact le_antisymm (hlip.dimH_image_le S) (hanti.le_dimH_image S)

#check @T013
#print axioms T013

end Translation
