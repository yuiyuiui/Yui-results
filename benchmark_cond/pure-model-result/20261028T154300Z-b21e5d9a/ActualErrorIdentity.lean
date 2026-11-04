import ActualErrorNormalForm
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem extendedTwistedPath_integral_difference {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (extendedTwistedPath hT hu b).val - (extendedTwistedPath hT hu a).val =
      (1 / 2 : ℂ) • (fun k => ∫ t : ℝ in a..b,
        B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) := by
  have hC := continuous_extendedTwistedPath hT hu
  funext k
  have hc : Continuous (fun t : ℝ => B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) := by
    have hh := (coefficientMap 1 k).continuous.comp (continuous_BTwoBundled continuous_id hC hC)
    simpa only [Function.comp_def, coefficientMap_apply, BTwoBundled_val, id_eq] using hh
  have hder : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun r : ℝ => (extendedTwistedPath hT hu r).val k)
      ((1 / 2 : ℂ) * B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) t := by
    intro t ht
    exact extendedTwistedPath_hasDerivAt hT hu ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩ k
  have hi : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℂ) *
      B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) volume a b :=
    (continuous_const.mul hc).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (((coefficientMap 2 k).continuous.comp hC).continuousOn) hder hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  exact hFTC.symm

/-- The exact restarted error identity (29), with the residual increment
already proved to belong to the specified numerical interpolation. -/
theorem actual_error_integral_identity (externalStep : LiWuStepIdentity)
    {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
    let V := globalInterpolation externalStep τ hτ f hfr hfm k
    let R := globalResidual externalStep τ hτ f hfr hfm k
    let e : ℝ → Sobolev 1 := fun t => v t - V t
    let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
    (e b).val = (e a).val + (fun m => ∫ t : ℝ in a..b, B t (e t).val (g t).val m) -
      ((R b).val - (R a).val) := by
  dsimp only
  let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let R := globalResidual externalStep τ hτ f hfr hfm k
  let e : ℝ → Sobolev 1 := fun t => v t - V t
  let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
  have hdiffv := extendedTwistedPath_integral_difference hT hu ha hab (hb.trans hTotal)
  have hdiffV := global_perturbation_integral_identity externalStep τ hτ f hfr hfm k ha hab hb
  have hvC : Continuous v := (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
  have hVC := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  funext m
  have hi1 : IntervalIntegrable (fun t : ℝ => B t (v t).val (v t).val m) volume a b := by
    have hc := (coefficientMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hvC hvC)
    have hcc : Continuous (fun t : ℝ => B t (v t).val (v t).val m) := by
      simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using hc
    exact hcc.intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t : ℝ => B t (V t).val (V t).val m) volume a b := by
    have hc := (coefficientMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hVC hVC)
    have hcc : Continuous (fun t : ℝ => B t (V t).val (V t).val m) := by
      simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using hc
    exact hcc.intervalIntegrable a b
  have hFI : (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
      (1 / 2 : ℂ) * ((∫ t : ℝ in a..b, B t (v t).val (v t).val m) -
        (∫ t : ℝ in a..b, B t (V t).val (V t).val m)) := by
    have heq : (fun t : ℝ => B t (e t).val (g t).val m) =
        (fun t : ℝ => (1 / 2 : ℂ) * (B t (v t).val (v t).val m - B t (V t).val (V t).val m)) := by
      funext t
      exact congrFun (B_error_polarization ((v t).property.of_le (by norm_num)) ((V t).property.of_le (by norm_num)) t) m
    rw [heq, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2]
  have hv := congrFun hdiffv m
  have hV := congrFun hdiffV m
  change (v b).val m - (v a).val m = (1 / 2 : ℂ) * (∫ t : ℝ in a..b, B t (v t).val (v t).val m) at hv
  change (V b).val m - (V a).val m = (1 / 2 : ℂ) * (∫ t : ℝ in a..b, B t (V t).val (V t).val m) +
    ((R b).val m - (R a).val m) at hV
  change (v b).val m - (V b).val m = (v a).val m - (V a).val m +
    (∫ t : ℝ in a..b, B t (e t).val (g t).val m) - ((R b).val m - (R a).val m)
  linear_combination hv - hV - hFI

theorem actual_error_grid_norm (externalStep : LiWuStepIdentity)
    {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) {j : ℕ} (hj : j ≤ k + 1) :
    hNorm 0 ((inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu ((j : ℝ) * τ)) -
      globalInterpolation externalStep τ hτ f hfr hfm k ((j : ℝ) * τ)).val) =
      hNorm 0 (u ((j : ℝ) * τ) - numerical τ f.val j) := by
  have ht : (j : ℝ) * τ ∈ Set.Icc 0 T := ⟨mul_nonneg (Nat.cast_nonneg j) hτ.le,
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hj : (j : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) hτ.le).trans hTotal⟩
  rw [sobolev_val_sub, inclusionMap_val, extendedTwistedPath_val_on hT hu ht,
    globalInterpolation_grid externalStep τ hτ f hfr hfm hj, twistedNumericalBundled_val,
    ← airy_sub, airy_hNorm]

end KdV
