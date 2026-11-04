import GlobalRegularity
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The perturbation identity on any restarted interval. The finite grid is
handled by Mathlib's fundamental theorem off a countable exceptional set;
continuity at every grid point was proved by exact endpoint matching. -/
theorem global_perturbation_integral_identity (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    (globalInterpolation externalStep τ hτ f hfr hfm k b).val -
      (globalInterpolation externalStep τ hτ f hfr hfm k a).val =
        (1 / 2 : ℂ) • (fun m => ∫ t : ℝ in a..b,
          B t (globalInterpolation externalStep τ hτ f hfr hfm k t).val
            (globalInterpolation externalStep τ hτ f hfr hfm k t).val m) +
        ((globalResidual externalStep τ hτ f hfr hfm k b).val -
          (globalResidual externalStep τ hτ f hfr hfm k a).val) := by
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let R := globalResidual externalStep τ hτ f hfr hfm k
  have hVC := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  have hRC := continuous_globalResidual externalStep τ hτ f hfr hfm k
  have hBC := continuous_BOneBundled continuous_id hVC hVC
  funext m
  have hB : Continuous (fun t : ℝ => B t (V t).val (V t).val m) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using
      (coefficientMap 0 m).continuous.comp hBC
  have hC : Continuous (fun t : ℝ => (V t).val m - (R t).val m) := by
    simpa only [Function.comp_def, coefficientMap_apply, Pi.sub_apply, V, R] using!
      ((coefficientMap 1 m).continuous.comp hVC).sub ((coefficientMap 0 m).continuous.comp hRC)
  have hD : ∀ t ∈ Set.Ioo a b \ Set.range (fun j : ℕ => (j : ℝ) * τ),
      HasDerivAt (fun r : ℝ => (V r).val m - (R r).val m)
        ((1 / 2 : ℂ) * B t (V t).val (V t).val m) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1.1
    have htT : t < ((k + 1 : ℕ) : ℝ) * τ := lt_of_lt_of_le ht.1.2 hb
    have hnot : ∀ j : ℕ, t ≠ (j : ℝ) * τ := by
      intro j heq
      exact ht.2 ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k ht0 htT hnot
    exact global_perturbation_hasDerivAt_on_step externalStep τ hτ f hfr hfm hj hstep m
  have hi : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℂ) * B t (V t).val (V t).val m) volume a b :=
    (continuous_const.mul hB).intervalIntegrable a b
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ => (V t).val m - (R t).val m)
    (fun t : ℝ => (1 / 2 : ℂ) * B t (V t).val (V t).val m) hab
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)) hC.continuousOn hD hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  change (V b).val m - (V a).val m =
    (1 / 2 : ℂ) * (∫ t : ℝ in a..b, B t (V t).val (V t).val m) + ((R b).val m - (R a).val m)
  linear_combination -hFTC

theorem globalInterpolation_zero (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) :
    (globalInterpolation externalStep τ hτ f hfr hfm k 0).val = f.val := by
  have h := globalInterpolation_grid externalStep τ hτ f hfr hfm (j := 0) (Nat.zero_le (k + 1))
  simpa only [Nat.cast_zero, zero_mul, twistedNumericalBundled_val, neg_zero, airy_zero, numerical_zero] using h

theorem globalInterpolation_integral_identity (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 (((k + 1 : ℕ) : ℝ) * τ)) :
    (globalInterpolation externalStep τ hτ f hfr hfm k t).val = f.val +
      (1 / 2 : ℂ) • (fun m => ∫ s : ℝ in (0 : ℝ)..t,
        B s (globalInterpolation externalStep τ hτ f hfr hfm k s).val
          (globalInterpolation externalStep τ hτ f hfr hfm k s).val m) +
      (globalResidual externalStep τ hτ f hfr hfm k t).val := by
  have h := global_perturbation_integral_identity externalStep τ hτ f hfr hfm k le_rfl ht.1 ht.2
  rw [globalInterpolation_zero, globalResidual_zero] at h
  change (globalInterpolation externalStep τ hτ f hfr hfm k t).val - f.val = _ at h
  have hz : (0 : Sobolev 0).val = (0 : Fourier) := rfl
  rw [hz, sub_zero] at h
  linear_combination h

end KdV
