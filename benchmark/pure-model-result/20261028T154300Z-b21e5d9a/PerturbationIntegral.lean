import ResidualIdentity
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Equation (25) on one step, proved from the actual interpolation and its
residual. It is not a replacement definition of the numerical method. -/
theorem localInterpolation_integral_identity (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) :
    localInterpolation τ ((n : ℝ) * τ) t f.val = f.val +
      (1 / 2 : ℂ) • (fun k => ∫ s : ℝ in (n : ℝ) * τ..t,
        B s (localInterpolation τ ((n : ℝ) * τ) s f.val)
          (localInterpolation τ ((n : ℝ) * τ) s f.val) k) +
      localResidual τ ((n : ℝ) * τ) t f.val := by
  let a : ℝ := (n : ℝ) * τ
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hVC := continuous_localInterpolationBundled externalStep τ hτ n f hfr hfm
  have hBC := continuous_BOneBundled continuous_id hVC hVC
  funext k
  have hB : Continuous (fun s : ℝ => B s (localInterpolation τ a s f.val)
      (localInterpolation τ a s f.val) k) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val,
      localInterpolationBundled_val, id_eq, a] using (coefficientMap 0 k).continuous.comp hBC
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ =>
      localInterpolation τ a s f.val k - localResidual τ a s f.val k)
      ((1 / 2 : ℂ) * B r (localInterpolation τ a r f.val) (localInterpolation τ a r f.val) k) r := by
    have hY : InSobolev 0 (interpolationRemainder τ a r f.val) := by
      rw [← defectBundled_val externalStep τ hτ n r f hfr hfm]
      exact (defectBundled externalStep τ hτ n r f hfr hfm).property.of_le (by norm_num)
    have hp := congrFun (localInterpolation_perturbation_identity hf0 hY) k
    have h := (localInterpolation_hasDerivAt (τ := τ) (a := a) (t := r) f hfm k).sub
      (localResidual_hasDerivAt externalStep τ hτ n f hfr hfm r k)
    apply h.congr_deriv
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right] using
      congrArg (fun z : ℂ => z - localResidualDerivative τ a r f.val k) hp
  have hi : IntervalIntegrable (fun r : ℝ => (1 / 2 : ℂ) * B r
      (localInterpolation τ a r f.val) (localInterpolation τ a r f.val) k) volume a t :=
    (continuous_const.mul hB).intervalIntegrable a t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hv0 : localInterpolation τ a a f.val k = f.val k := congrFun (localInterpolation_left f.val) k
  have hr0 : localResidual τ a a f.val k = 0 := congrFun (localResidual_left τ a f.val) k
  rw [hv0, hr0, sub_zero] at hFTC
  change localInterpolation τ a t f.val k = f.val k + (1 / 2 : ℂ) *
    (∫ s : ℝ in a..t, B s (localInterpolation τ a s f.val) (localInterpolation τ a s f.val) k) +
      localResidual τ a t f.val k
  linear_combination -hFTC

end KdV
