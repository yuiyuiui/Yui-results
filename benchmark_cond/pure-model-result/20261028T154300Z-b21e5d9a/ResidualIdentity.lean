import PathIntervalTools
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem coefficientMap_apply (s : ℝ) (k : ℤ) (f : Sobolev s) :
    coefficientMap s k f = f.val k := rfl

def frozenZ (a t : ℝ) (f : Fourier) : Fourier := f + bilinearStage a t f f

def localResidualDerivative (τ a t : ℝ) (f : Fourier) : Fourier :=
  - B t (interpolationRemainder τ a t f) (frozenZ a t f) -
    (1 / 2 : ℂ) • B t (interpolationRemainder τ a t f) (interpolationRemainder τ a t f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f

def localResidual (τ a t : ℝ) (f : Fourier) : Fourier := fun k =>
  -(∫ s : ℝ in a..t, B s (interpolationRemainder τ a s f) (frozenZ a s f) k) -
    (1 / 2 : ℂ) * (∫ s : ℝ in a..t,
      B s (interpolationRemainder τ a s f) (interpolationRemainder τ a s f) k) -
    (((t - a) / τ : ℝ) : ℂ) * endpointCorrection τ a f k

@[simp] theorem localResidual_left (τ a : ℝ) (f : Fourier) : localResidual τ a a f = 0 := by
  funext k
  simp [localResidual]

/-- The differential perturbation identity for the actual interpolation. -/
theorem localInterpolation_perturbation_identity {τ a t : ℝ} {f : Fourier}
    (hf : InSobolev 0 f) (hY : InSobolev 0 (interpolationRemainder τ a t f)) :
    localInterpolationDerivative τ a t f =
      (1 / 2 : ℂ) • B t (localInterpolation τ a t f) (localInterpolation τ a t f) +
        localResidualDerivative τ a t f := by
  have hF := (bilinearStage_h1_bound hf hf a t).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hZ : InSobolev 0 (frozenZ a t f) := hf.add hF
  have heq : localInterpolation τ a t f = frozenZ a t f + interpolationRemainder τ a t f := by
    unfold frozenZ interpolationRemainder
    abel
  rw [heq, B_diagonal_add hZ hY]
  rw [B_comm t (frozenZ a t f) (interpolationRemainder τ a t f)]
  change localInterpolationDerivative τ a t f =
    (1 / 2 : ℂ) • (B t (f + bilinearStage a t f f) (f + bilinearStage a t f f) +
      (2 : ℂ) • B t (interpolationRemainder τ a t f) (frozenZ a t f) +
      B t (interpolationRemainder τ a t f) (interpolationRemainder τ a t f)) + _
  rw [B_diagonal_add hf hF]
  unfold localInterpolationDerivative localResidualDerivative
  module

def derivativeOneLinear : Sobolev 1 →ₗ[ℂ] Sobolev 0 where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := 0) (by norm_num; exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeOneMap : Sobolev 1 →L[ℂ] Sobolev 0 :=
  derivativeOneLinear.mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm 0 (derivative f.val) ≤ hNorm 1 f.val
    have h := derivative_hNorm (s := 0) (by norm_num; exact f.property)
    norm_num at h
    exact h)

def BOneBundled (t : ℝ) (f g : Sobolev 1) : Sobolev 0 :=
  airyMap 0 (-t) (derivativeOneMap (productMap (airyMap 1 t f) (airyMap 1 t g)))

theorem BOneBundled_val (t : ℝ) (f g : Sobolev 1) :
    (BOneBundled t f g).val = B t f.val g.val := rfl

theorem continuous_BOneBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g : X → Sobolev 1} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => BOneBundled (t x) (f x) (g x)) := by
  unfold BOneBundled
  have hf' := continuous_airy_apply 1 ht hf
  have hg' := continuous_airy_apply 1 ht hg
  apply continuous_airy_apply 0 ht.neg
  fun_prop

def frozenZBundled (a t : ℝ) (f : Sobolev 2) : Sobolev 1 :=
  inclusionMap 1 2 (by norm_num) (f + stageTwoBundled a t f f)

theorem frozenZBundled_val (a t : ℝ) (f : Sobolev 2) :
    (frozenZBundled a t f).val = frozenZ a t f.val := rfl

theorem continuous_frozenZBundled (a : ℝ) (f : Sobolev 2) :
    Continuous (fun t : ℝ => frozenZBundled a t f) := by
  unfold frozenZBundled
  fun_prop

theorem continuous_residual_integrands (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => BOneBundled t (defectBundled externalStep τ hτ n t f hfr hfm)
      (frozenZBundled ((n : ℝ) * τ) t f)) ∧
    Continuous (fun t : ℝ => BOneBundled t (defectBundled externalStep τ hτ n t f hfr hfm)
      (defectBundled externalStep τ hτ n t f hfr hfm)) := by
  have hY := continuous_defectBundled externalStep τ hτ n f hfr hfm
  exact ⟨continuous_BOneBundled continuous_id hY (continuous_frozenZBundled _ f),
    continuous_BOneBundled continuous_id hY hY⟩

theorem localResidual_hasDerivAt (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun r : ℝ => localResidual τ ((n : ℝ) * τ) r f.val k)
      (localResidualDerivative τ ((n : ℝ) * τ) t f.val k) t := by
  let a : ℝ := (n : ℝ) * τ
  obtain ⟨hC, hQ⟩ := continuous_residual_integrands externalStep τ hτ n f hfr hfm
  have hc : Continuous (fun s : ℝ => B s (interpolationRemainder τ a s f.val) (frozenZ a s f.val) k) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, defectBundled_val, frozenZBundled_val] using
      (coefficientMap 0 k).continuous.comp hC
  have hq : Continuous (fun s : ℝ => B s (interpolationRemainder τ a s f.val)
      (interpolationRemainder τ a s f.val) k) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, defectBundled_val] using (coefficientMap 0 k).continuous.comp hQ
  have hci := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hqi := intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a t)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hlin : HasDerivAt (fun r : ℝ => (((r - a) / τ : ℝ) : ℂ)) ((τ⁻¹ : ℝ) : ℂ) t := by
    simpa only [one_div, id_eq] using! (((hasDerivAt_id t).sub_const a).div_const τ).ofReal_comp
  have h := (hci.neg.sub (hqi.const_mul (1 / 2 : ℂ))).sub
    (hlin.mul_const (endpointCorrection τ a f.val k))
  simpa only [localResidual, localResidualDerivative, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul] using! h

end KdV
