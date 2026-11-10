import DefectPartialTime
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem J_neg_left (t : ℝ) (f g : Fourier) : J t (-f) g = -J t f g := by
  simpa only [neg_one_smul] using J_smul_left t (-1 : ℂ) f g

theorem residual_forcing_integrand_identity {τ t : ℝ} (Y Z V : Sobolev 1) (W : Sobolev 0) :
    J t (- B t Y.val Z.val - (1 / 2 : ℂ) • B t Y.val Y.val - ((τ⁻¹ : ℝ) : ℂ) • W.val) V.val =
      - CIntegrand t Y.val Z.val V.val - (1 / 2 : ℂ) • CIntegrand t Y.val Y.val V.val -
        ((τ⁻¹ : ℝ) : ℂ) • J t W.val V.val := by
  have hB := (B_h1_bound Y.property Z.property t).1
  have hB2 := (B_h1_bound Y.property Y.property t).1
  have hV := V.property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  rw [J_sub_left ((hB.neg).sub (hB2.smul (1 / 2 : ℂ))) (W.property.smul _) hV,
    J_sub_left hB.neg (hB2.smul (1 / 2 : ℂ)) hV, J_neg_left, J_smul_left, J_smul_left,
    J_B, J_B]
  rfl

/-- Integrating the actual residual derivative yields two explicit cubic
 integrals and the constant endpoint correction. -/
theorem residual_forcing_integral_identity (externalStep : LiWuStepIdentity)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val)
    (V : ℝ → Sobolev 1) (hV : Continuous V) (b : ℝ) :
    (fun m => ∫ t : ℝ in (n : ℝ) * τ..b,
      J t (localResidualDerivative τ ((n : ℝ) * τ) t f.val) (V t).val m) =
      - CIntegral ((n : ℝ) * τ) b
        (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val)
        (fun t => frozenZ ((n : ℝ) * τ) t f.val) (fun t => (V t).val) -
      (1 / 2 : ℂ) • CIntegral ((n : ℝ) * τ) b
        (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val)
        (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val) (fun t => (V t).val) -
      ((τ⁻¹ : ℝ) : ℂ) • (fun m => ∫ t : ℝ in (n : ℝ) * τ..b,
        J t (endpointCorrection τ ((n : ℝ) * τ) f.val) (V t).val m) := by
  let a : ℝ := (n : ℝ) * τ
  let Y := fun t => defectBundled externalStep τ hτ n t f hfr hfm
  let Z := fun t => frozenZBundled a t f
  let W := inclusionMap 0 1 (by norm_num) (endpointCorrectionBundled externalStep τ hτ n f hfr hfm)
  have hYC : Continuous Y := continuous_defectBundled externalStep τ hτ n f hfr hfm
  have hZC : Continuous Z := continuous_frozenZBundled a f
  funext m
  have hpoint (t : ℝ) : J t (localResidualDerivative τ a t f.val) (V t).val m =
      - CIntegrand t (Y t).val (Z t).val (V t).val m -
      (1 / 2 : ℂ) * CIntegrand t (Y t).val (Y t).val (V t).val m -
      ((τ⁻¹ : ℝ) : ℂ) * J t W.val (V t).val m := by
    have h := congrFun (residual_forcing_integrand_identity (τ := τ) (t := t) (Y t) (Z t) (V t) W) m
    simpa only [Y, Z, W, localResidualDerivative, defectBundled_val, frozenZBundled_val,
      inclusionMap_val, endpointCorrectionBundled, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using h
  have hi1 : IntervalIntegrable (fun t => CIntegrand t (Y t).val (Z t).val (V t).val m) volume a b :=
    (continuous_CIntegrand_paths hYC hZC hV m).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t => CIntegrand t (Y t).val (Y t).val (V t).val m) volume a b :=
    (continuous_CIntegrand_paths hYC hYC hV m).intervalIntegrable a b
  have hi3 : IntervalIntegrable (fun t => J t W.val (V t).val m) volume a b := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
      (continuous_const (y := W)) ((inclusionMap 0 1 (by norm_num)).continuous.comp hV))
    exact h.intervalIntegrable a b
  have hiN : IntervalIntegrable (fun t => - CIntegrand t (Y t).val (Z t).val (V t).val m) volume a b := hi1.neg
  have hint := intervalIntegral.integral_congr (μ := volume) (a := a) (b := b) (fun t _ => hpoint t)
  rw [intervalIntegral.integral_sub (hiN.sub (hi2.const_mul (1 / 2 : ℂ))) (hi3.const_mul (((τ⁻¹ : ℝ) : ℂ))),
    intervalIntegral.integral_sub hiN (hi2.const_mul (1 / 2 : ℂ)), intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  simpa only [CIntegral, CIntegrand, Y, Z, W, a, defectBundled_val, frozenZBundled_val, inclusionMap_val,
    endpointCorrectionBundled, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using hint

end KdV
