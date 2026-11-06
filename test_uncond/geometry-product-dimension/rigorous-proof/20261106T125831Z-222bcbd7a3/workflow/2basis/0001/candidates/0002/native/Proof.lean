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

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (s : ℝ) (A : Set X),
  hausdorffMeasure s A = ⨆ (δ : ℝ≥0∞) (_ : 0 < δ), YuiBasis.Content s δ A := by
  intro X _ _ _ s A
  exact hausdorffMeasure_apply s A
set_option Elab.async false in
theorem B002 : ∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
  ((d : ℝ≥0∞) < dimH A → hausdorffMeasure (d : ℝ) A = ⊤) ∧
  (dimH A < (d : ℝ≥0∞) → hausdorffMeasure (d : ℝ) A = 0) ∧
  (hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
  (hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A d
  exact ⟨hausdorffMeasure_of_lt_dimH, hausdorffMeasure_of_dimH_lt,
    dimH_le_of_hausdorffMeasure_ne_top, le_dimH_of_hausdorffMeasure_eq_top⟩
set_option Elab.async false in
theorem B003 : ∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K L : ℝ≥0) (f : X → Y)
  (hf : LipschitzWith K f) (hg : AntilipschitzWith L f) (A : Set X),
  (dimH (f '' A) ≤ dimH A ∧ dimH A ≤ dimH (f '' A)) ∧
  (∀ B : Set X, A ⊆ B → dimH A ≤ dimH B) := by
  intro X Y _ _ K L f hf hg A
  exact ⟨⟨hf.dimH_image_le A, hg.le_dimH_image A⟩, fun B h => dimH_mono h⟩
set_option Elab.async false in
theorem B004 : ∀ (n : ℕ) (A : Set (YuiBasis.Ambient n)), dimH A ≤ (n : ℝ≥0∞) ∧ dimH A ≠ ⊤ := by
  intro n A
  constructor
  · calc
      dimH A ≤ dimH (Set.univ : Set (YuiBasis.Ambient n)) := dimH_mono (Set.subset_univ A)
      _ = (n : ℝ≥0∞) := by rw [Real.dimH_univ_eq_finrank]; simp [YuiBasis.Ambient]
  · exact Real.dimH_ne_top A
set_option Elab.async false in
theorem B005 : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  simpa only [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)] using
    (Real.dimH_segment (by norm_num : (0 : ℝ) ≠ 1))
set_option Elab.async false in
theorem B006 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞),
  (∀ i, AEMeasurable (f i) μ) →
  (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := by
  intro X _ μ f hf
  exact lintegral_tsum hf
set_option Elab.async false in
theorem B007 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (S : Set X),
  MeasurableSet S → ∀ c : ℝ≥0∞,
  (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S := by
  intro X _ μ S hS c
  exact lintegral_indicator_const hS c
set_option Elab.async false in
theorem B008 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X),
  (∀ f g : X → ℝ≥0∞, (∀ x, f x ≤ g x) →
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧
  (∀ c : ℝ≥0∞, (∫⁻ _x : X, c ∂μ) = c * μ Set.univ) := by
  intro X _ μ
  exact ⟨fun f g h => lintegral_mono h, fun c => lintegral_const c⟩
set_option Elab.async false in
theorem B009 : (∀ B : Set ℝ, Bornology.IsBounded B →
  B ⊆ Set.Icc (sInf B) (sSup B) ∧
  volume (Set.Icc (sInf B) (sSup B)) = Metric.ediam B) ∧
  (∀ a b : ℝ, volume (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
  volume (Set.Icc (0 : ℝ) 1) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    exact ⟨hB.subset_Icc_sInf_sSup, Real.volume_Icc.trans (Real.ediam_eq hB).symm⟩
  · intro a b
    exact Real.volume_Icc
  · simp
set_option Elab.async false in
theorem B010 : ∀ q : ℝ, 0 ≤ q → Continuous (fun x : ℝ => x ^ q) := by
  intro q hq
  exact Real.continuous_rpow_const hq
set_option Elab.async false in
theorem B011 : ∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K : ℝ≥0) (f : X → Y),
  LipschitzWith K f → ∀ A : Set X,
  Metric.ediam (f '' A) ≤ (K : ℝ≥0∞) * Metric.ediam A := by
  intro X Y _ _ K f hf A
  exact hf.ediam_image_le A

end YuiBasis
