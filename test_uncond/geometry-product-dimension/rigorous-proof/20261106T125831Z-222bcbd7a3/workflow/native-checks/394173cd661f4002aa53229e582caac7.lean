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

section
universe u
theorem T009 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T002 : dimH YuiBasis.unitInterval = 1) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  intro X _ A hA
  rcases hA with ⟨x₀, hx₀⟩
  let f : ℝ → X × ℝ := fun t => (x₀, t)
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    simp [f, Prod.dist_eq, dist_nonneg]
  have hdim : dimH (f '' YuiBasis.unitInterval) = dimH YuiBasis.unitInterval :=
    le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)
  have hsub : f '' YuiBasis.unitInterval ⊆ A ×ˢ YuiBasis.unitInterval := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hx₀, ht⟩
  calc
    1 = dimH (f '' YuiBasis.unitInterval) := (hdim.trans h_T002).symm
    _ ≤ dimH (A ×ˢ YuiBasis.unitInterval) := dimH_mono hsub

end
#check @T009
#print axioms T009

end Translation
