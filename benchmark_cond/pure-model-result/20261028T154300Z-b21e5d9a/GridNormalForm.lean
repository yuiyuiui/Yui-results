import GridPathTools
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The proved normal form across grid points, where the derivative may jump.
The functions themselves are continuous and every open step has an explicitly
proved derivative. No differentiability at grid points is required. -/
theorem variable_normal_form_grid (τ : ℝ) (hτ : 0 < τ) (k : ℕ)
    (f g : ℝ → Sobolev 1) (df dg : ℕ → ℝ → Sobolev 1)
    (hf : Continuous f) (hg : Continuous g) (hdf : ∀ j, Continuous (df j)) (hdg : ∀ j, Continuous (dg j))
    (hfd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun r : ℝ => (f r).val m) ((df j t).val m) t)
    (hgd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun r : ℝ => (g r).val m) ((dg j t).val m) t)
    (hfm : ∀ t, MeanZero (f t).val) (hgm : ∀ t, MeanZero (g t).val)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (m : ℤ) :
    (∫ t : ℝ in a..b, B t (f t).val (g t).val m) =
      (1 / 3 : ℂ) * (J b (f b).val (g b).val m - J a (f a).val (g a).val m) -
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b,
        (J t (concatenate τ df k t).val (g t).val m + J t (f t).val (concatenate τ dg k t).val m) := by
  have hcB : Continuous (fun t : ℝ => B t (f t).val (g t).val m) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using
      (coefficientMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hf hg)
  have hcJ : Continuous (fun t : ℝ => J t (f t).val (g t).val m) := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hf)
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hg))
    simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
    exact h
  have hcD (j : ℕ) : Continuous (fun t : ℝ => J t (df j t).val (g t).val m) := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
        ((inclusionMap 0 1 (by norm_num)).continuous.comp (hdf j))
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hg))
    simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
    exact h
  have hcE (j : ℕ) : Continuous (fun t : ℝ => J t (f t).val (dg j t).val m) := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hf)
        ((inclusionMap 0 1 (by norm_num)).continuous.comp (hdg j)))
    simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
    exact h
  have hiD : IntervalIntegrable (fun t : ℝ => J t (concatenate τ df k t).val (g t).val m) volume a b := by
    have hi := intervalIntegrable_concatenate τ (fun j t => J t (df j t).val (g t).val m)
      (fun j => (hcD j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => J t (df j t).val (g t).val m) k =
        (fun t => J t (concatenate τ df k t).val (g t).val m) := by
      funext t
      exact concatenate_map τ df (fun r v => J r v.val (g r).val m) k t
    rwa [hmap] at hi
  have hiE : IntervalIntegrable (fun t : ℝ => J t (f t).val (concatenate τ dg k t).val m) volume a b := by
    have hi := intervalIntegrable_concatenate τ (fun j t => J t (f t).val (dg j t).val m)
      (fun j => (hcE j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => J t (f t).val (dg j t).val m) k =
        (fun t => J t (f t).val (concatenate τ dg k t).val m) := by
      funext t
      exact concatenate_map τ dg (fun r v => J r (f r).val v.val m) k t
    rwa [hmap] at hi
  have hiB : IntervalIntegrable (fun t : ℝ => B t (f t).val (g t).val m) volume a b :=
    hcB.intervalIntegrable a b
  have hi3B := hiB.const_mul (3 : ℂ)
  have hD : ∀ t ∈ Set.Ioo a b \ Set.range (fun j : ℕ => (j : ℝ) * τ),
      HasDerivAt (fun r : ℝ => J r (f r).val (g r).val m)
        (3 * B t (f t).val (g t).val m + J t (concatenate τ df k t).val (g t).val m +
          J t (f t).val (concatenate τ dg k t).val m) t := by
    intro t ht
    have hnot : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => ht.2 ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k
      (lt_of_le_of_lt ha ht.1.1) (lt_of_lt_of_le ht.1.2 hb) hnot
    have hfreg := regularFourierPath_of_bundled hf (hdf j) (hfd j hj)
    have hgreg := regularFourierPath_of_bundled hg (hdg j) (hgd j hj)
    rw [concatenate_on_open_step hτ.le df hj hstep, concatenate_on_open_step hτ.le dg hj hstep]
    exact variable_J_hasDerivAt hfreg hgreg (fun t _ => hfm t) (fun t _ => hgm t) hstep m
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ => J t (f t).val (g t).val m)
    (fun t : ℝ => 3 * B t (f t).val (g t).val m + J t (concatenate τ df k t).val (g t).val m +
      J t (f t).val (concatenate τ dg k t).val m) hab
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)) hcJ.continuousOn hD ((hi3B.add hiD).add hiE)
  rw [intervalIntegral.integral_add (hi3B.add hiD) hiE,
    intervalIntegral.integral_add hi3B hiD, intervalIntegral.integral_const_mul] at hFTC
  rw [intervalIntegral.integral_add hiD hiE]
  linear_combination (1 / 3 : ℂ) * hFTC

end KdV
