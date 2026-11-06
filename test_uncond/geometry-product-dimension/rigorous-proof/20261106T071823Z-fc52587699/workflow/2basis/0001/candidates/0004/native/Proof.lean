import Mathlib
open scoped ENNReal NNReal MeasureTheory
open MeasureTheory Set

noncomputable def YuiContent {X : Type} [MetricSpace X] (p : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
    ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ p

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (p : ℝ) (A : Set X), MeasureTheory.Measure.hausdorffMeasure p A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), YuiContent p r A := by
  intro X _ _ _ p A
  simpa only [YuiContent] using MeasureTheory.Measure.hausdorffMeasure_apply p A
set_option Elab.async false in
theorem B002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0), (((a : ℝ≥0∞) < dimH A) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ⊤) ∧ ((dimH A < (a : ℝ≥0∞)) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧ ((MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A ≠ ⊤) → dimH A ≤ (a : ℝ≥0∞)) ∧ ((MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ⊤) → (a : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A a
  exact ⟨hausdorffMeasure_of_lt_dimH, hausdorffMeasure_of_dimH_lt, dimH_le_of_hausdorffMeasure_ne_top, le_dimH_of_hausdorffMeasure_eq_top⟩
set_option Elab.async false in
theorem B003 : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y], (∀ (A B : Set X), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (K : ℝ≥0) (f : X → Y) (A : Set X), LipschitzWith K f → dimH (f '' A) ≤ dimH A) ∧ (∀ (f : X → Y) (A : Set X), Isometry f → dimH (f '' A) = dimH A) := by
  intro X Y _ _
  exact ⟨fun A B h => dimH_mono h, fun K f A h => h.dimH_image_le A, fun f A h => h.dimH_image A⟩
set_option Elab.async false in
theorem B004 : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (A : Set V), dimH A ≤ (Module.finrank ℝ V : ℝ≥0∞) := by
  intro V _ _ _ A
  exact (dimH_mono (Set.subset_univ A)).trans_eq (Real.dimH_univ_eq_finrank V)
set_option Elab.async false in
theorem B005 : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  have h : (interior (Set.Icc (0 : ℝ) 1)).Nonempty := by
    rw [interior_Icc]
    exact ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  simpa using Real.dimH_of_nonempty_interior h
set_option Elab.async false in
theorem B006 : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X), (∀ (f : ℕ → X → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) → (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ) ∧ (∀ (S : Set X) (c : ℝ≥0∞), MeasurableSet S → (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S) ∧ (∀ (f g : X → ℝ≥0∞), (∀ x, f x ≤ g x) → (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧ (∀ (S : Set X) (c : ℝ≥0∞), (∫⁻ x in S, c ∂μ) = c * μ S) := by
  intro X _ μ
  exact ⟨fun f h => MeasureTheory.lintegral_tsum h, fun S c h => MeasureTheory.lintegral_indicator_const h c, fun f g h => MeasureTheory.lintegral_mono h, fun S c => MeasureTheory.setLIntegral_const S c⟩
set_option Elab.async false in
theorem B007 : ∀ (a b : ℝ), MeasureTheory.volume (Set.Icc a b) = ENNReal.ofReal (b - a) ∧ MeasureTheory.volume (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
  intro a b
  exact ⟨Real.volume_Icc, Real.volume_Ioo⟩
set_option Elab.async false in
theorem B008 : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (e : V ≃ₗ[ℝ] W) (A : Set V), dimH (e '' A) = dimH A := by
  intro V W _ _ _ _ _ _ e A
  exact e.toContinuousLinearEquiv.dimH_image A
set_option Elab.async false in
theorem B009 : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] (K : ℝ≥0) (f : X → Y) (A : Set X), LipschitzWith K f → Metric.ediam (f '' A) ≤ (K : ℝ≥0∞) * Metric.ediam A := by
  intro X Y _ _ K f A h
  exact h.ediam_image_le A

end YuiBasis
