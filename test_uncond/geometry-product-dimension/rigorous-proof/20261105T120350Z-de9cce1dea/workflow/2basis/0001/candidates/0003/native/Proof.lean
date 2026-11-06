import Mathlib
open scoped ENNReal NNReal Topology
open Set MeasureTheory
namespace BasisObjects
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def content {X : Type*} [EMetricSpace X]
    (s : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def euclideanLift (n : ℕ) : Rn n × ℝ → WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2
end BasisObjects

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r), BasisObjects.content a r A := by
  intro X _ _ _ a A
  exact MeasureTheory.Measure.hausdorffMeasure_apply a A
set_option Elab.async false in
theorem B002 : ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
  (((d : ℝ≥0∞) < dimH A) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
  ((dimH A < (d : ℝ≥0∞)) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
  ((MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤) → dimH A ≤ (d : ℝ≥0∞)) ∧
  ((MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) → (d : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A d
  exact ⟨hausdorffMeasure_of_lt_dimH,
    hausdorffMeasure_of_dimH_lt,
    dimH_le_of_hausdorffMeasure_ne_top,
    le_dimH_of_hausdorffMeasure_eq_top⟩
set_option Elab.async false in
theorem B003 : ∀ (X : Type) [EMetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B := by
  intro X _ A B h
  exact dimH_mono h
set_option Elab.async false in
theorem B004 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
  dimH (Set.univ : Set X) = (Module.finrank ℝ X : ℝ≥0∞) := by
  intro X _ _ _
  exact Real.dimH_univ_eq_finrank X
set_option Elab.async false in
theorem B005 : ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃L[ℝ] Y) (A : Set X),
  dimH (e '' A) = dimH A := by
  intro X Y _ _ _ _ e A
  exact e.dimH_image A
set_option Elab.async false in
theorem B006 : ∀ (X Y : Type) [EMetricSpace X] [EMetricSpace Y] (f : X → Y),
  Isometry f → ∀ A : Set X, dimH (f '' A) = dimH A := by
  intro X Y _ _ f hf A
  exact hf.dimH_image A
set_option Elab.async false in
theorem B007 : ∀ a b : ℝ, MeasureTheory.volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  intro a b
  exact Real.volume_Icc
set_option Elab.async false in
theorem B008 : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞),
  (∀ i, AEMeasurable (f i) μ) →
  (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := by
  intro X _ μ f hf
  exact MeasureTheory.lintegral_tsum hf
set_option Elab.async false in
theorem B009 : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞),
  (∀ x, f x ≤ g x) → (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := by
  intro X _ μ f g h
  exact MeasureTheory.lintegral_mono h
set_option Elab.async false in
theorem B010 : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (S : Set X) (c : ℝ≥0∞),
  MeasurableSet S → (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S := by
  intro X _ μ S c hS
  exact MeasureTheory.lintegral_indicator_const hS c
set_option Elab.async false in
theorem B011 : ∀ (n : ℕ) (S : Set (BasisObjects.Rn n × ℝ)),
  dimH (BasisObjects.euclideanLift n '' S) = dimH S := by
  intro n S
  exact YuiBasis.B005 (BasisObjects.Rn n × ℝ) (WithLp 2 (BasisObjects.Rn n × ℝ))
    (WithLp.prodContinuousLinearEquiv 2 ℝ (BasisObjects.Rn n) ℝ).symm S
set_option Elab.async false in
theorem B012 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  (A : Set X), (interior A).Nonempty → dimH A = (Module.finrank ℝ X : ℝ≥0∞) := by
  intro X _ _ _ A h
  exact Real.dimH_of_nonempty_interior h
set_option Elab.async false in
theorem B013 : ∀ (n : ℕ) (p : WithLp 2 (BasisObjects.Rn n × ℝ)),
  ‖p‖ ^ 2 = ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 := by
  intro n p
  exact WithLp.prod_norm_sq_eq_of_L2 p

end YuiBasis
