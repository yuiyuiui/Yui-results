import InverseDefectEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def interpolationRemainderDerivative (τ a t : ℝ) (f : Fourier) : Fourier :=
  B t f (bilinearStage a t f f) +
    (1 / 2 : ℂ) • B t (bilinearStage a t f f) (bilinearStage a t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f

theorem interpolationRemainderDerivative_meanZero (τ a t : ℝ) (f : Fourier) :
    MeanZero (interpolationRemainderDerivative τ a t f) :=
  ((B_meanZero t _ _).add ((B_meanZero t _ _).smul _)).sub ((endpointCorrection_meanZero τ a f).smul _)

theorem interpolationRemainder_hasDerivAt {τ a t : ℝ} (f : Sobolev 2)
    (hfm : MeanZero f.val) (k : ℤ) :
    HasDerivAt (fun r : ℝ => interpolationRemainder τ a r f.val k)
      (interpolationRemainderDerivative τ a t f.val k) t := by
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hv := localInterpolation_hasDerivAt (τ := τ) (a := a) (t := t) f hfm k
  have hz := (hasDerivAt_const t (f.val k)).add (stage_hasDerivAt hf0 hf0 hfm hfm a t k)
  have h := hv.sub hz
  have hd : localInterpolationDerivative τ a t f.val k -
      (0 + (1 / 2 : ℂ) * B t f.val f.val k) = interpolationRemainderDerivative τ a t f.val k := by
    change (1 / 2 : ℂ) * B t f.val f.val k + _ + _ - _ -
      (0 + (1 / 2 : ℂ) * B t f.val f.val k) = _
    simp only [interpolationRemainderDerivative, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [interpolationRemainder, Pi.add_apply, Pi.sub_apply, hd] using! h

def defectBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  frozenCrossBundled ((n : ℝ) * τ) t f + frozenSquareBundled ((n : ℝ) * τ) t f -
    ((((t - (n : ℝ) * τ) / τ) : ℝ) : ℂ) •
      endpointCorrectionBundled externalStep τ hτ n f hfr hfm

def defectDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  BTwoBundled t f (stageTwoBundled ((n : ℝ) * τ) t f f) +
    (1 / 2 : ℂ) • BTwoBundled t (stageTwoBundled ((n : ℝ) * τ) t f f)
      (stageTwoBundled ((n : ℝ) * τ) t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrectionBundled externalStep τ hτ n f hfr hfm

theorem defectBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (defectBundled externalStep τ hτ n t f hfr hfm).val =
      interpolationRemainder τ ((n : ℝ) * τ) t f.val := by
  change (frozenCrossBundled _ t f).val + (frozenSquareBundled _ t f).val - _ = _
  rw [frozenCrossBundled_val, frozenSquareBundled_val, interpolationRemainder_eq]
  rfl

theorem defectDerivativeBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (defectDerivativeBundled externalStep τ hτ n t f hfr hfm).val =
      interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val := rfl

theorem continuous_defectBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => defectBundled externalStep τ hτ n t f hfr hfm) := by
  unfold defectBundled
  have hC := continuous_frozenCrossBundled ((n : ℝ) * τ) f
  have hQ := continuous_frozenSquareBundled ((n : ℝ) * τ) f
  fun_prop

theorem continuous_defectDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => defectDerivativeBundled externalStep τ hτ n t f hfr hfm) := by
  unfold defectDerivativeBundled
  have hC := continuous_cross_integrand ((n : ℝ) * τ) f
  have hQ := continuous_square_integrand ((n : ℝ) * τ) f
  fun_prop

theorem interpolationRemainder_regular (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    RegularFourierPath ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)
      (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val)
      (fun t => interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val) := by
  have h := regularFourierPath_of_bundled
    (a := (n : ℝ) * τ) (b := ((n + 1 : ℕ) : ℝ) * τ)
    (continuous_defectBundled externalStep τ hτ n f hfr hfm)
    (continuous_defectDerivativeBundled externalStep τ hτ n f hfr hfm)
    (fun t _ k => by
      simp_rw [defectBundled_val, defectDerivativeBundled_val]
      exact interpolationRemainder_hasDerivAt f hfm k)
  simpa only [defectBundled_val, defectDerivativeBundled_val] using h

end KdV
