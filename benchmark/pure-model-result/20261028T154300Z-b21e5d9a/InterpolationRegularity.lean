import StepInterpolation
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem coefficient_integral_bound {s A a b : ℝ} {f : ℝ → Sobolev s}
    (hf : Continuous f) (hab : a ≤ b) (hb : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ A) :
    InSobolev s (fun k => ∫ t : ℝ in a..b, (f t).val k) ∧
      hNorm s (fun k => ∫ t : ℝ in a..b, (f t).val k) ≤ A * (b - a) := by
  have heq := sobolev_integral_val (hf.intervalIntegrable a b)
  rw [← heq]
  refine ⟨(∫ t : ℝ in a..b, f t).property, ?_⟩
  rw [← sobolev_norm]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (f := f)
    (fun t ht => hb t (by rw [Set.uIoc_of_le hab] at ht; exact ⟨ht.1.le, ht.2⟩))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hn

/-- Compactness supplies coefficient envelopes used solely to justify the
normal-form identities, without asserting uniformity in these higher norms. -/
theorem regularFourierPath_of_bundled {a b : ℝ} {f df : ℝ → Sobolev 1}
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (f r).val k) ((df t).val k) t) :
    RegularFourierPath a b (fun t => (f t).val) (fun t => (df t).val) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image (hf.norm)).bddAbove
  obtain ⟨Md, hMd⟩ := (isCompact_Icc.image (hdf.norm)).bddAbove
  apply regularFourierPath_of_h1_bounds (M := |M|) (Md := |Md|) (abs_nonneg _) (abs_nonneg _)
  · intro k
    exact ((coefficientMap 1 k).continuous.comp hf).continuousOn
  · intro k
    exact ((coefficientMap 1 k).continuous.comp hdf).continuousOn
  · exact hd
  · intro t ht
    exact ⟨(f t).property, (by rw [← sobolev_norm]; exact (hM ⟨t, ht, rfl⟩).trans (le_abs_self _))⟩
  · intro t ht
    exact ⟨(df t).property, (by rw [← sobolev_norm]; exact (hMd ⟨t, ht, rfl⟩).trans (le_abs_self _))⟩

def localInterpolationDerivative (τ a t : ℝ) (f : Fourier) : Fourier :=
  (1 / 2 : ℂ) • B t f f + B t f (bilinearStage a t f f) +
    (1 / 2 : ℂ) • B t (bilinearStage a t f f) (bilinearStage a t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f

theorem localInterpolation_hasDerivAt {τ a t : ℝ} (f : Sobolev 2)
    (hfm : MeanZero f.val) (k : ℤ) :
    HasDerivAt (fun r : ℝ => localInterpolation τ a r f.val k)
      (localInterpolationDerivative τ a t f.val k) t := by
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hF := stage_hasDerivAt hf0 hf0 hfm hfm a t k
  have hC := frozenCross_hasDerivAt a t f k
  have hQ := frozenSquare_hasDerivAt a t f k
  have hlin : HasDerivAt (fun r : ℝ => (((r - a) / τ : ℝ) : ℂ))
      ((τ⁻¹ : ℝ) : ℂ) t := by
    simpa only [one_div, id_eq] using! (((hasDerivAt_id t).sub_const a).div_const τ).ofReal_comp
  have hc := hlin.mul_const (endpointCorrection τ a f.val k)
  simpa only [localInterpolation, localInterpolationDerivative, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, zero_add] using!
      (((hasDerivAt_const t (f.val k)).add hF).add hC |>.add hQ).sub hc

def localDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  (1 / 2 : ℂ) • BTwoBundled t f f + BTwoBundled t f (stageTwoBundled ((n : ℝ) * τ) t f f) +
    (1 / 2 : ℂ) • BTwoBundled t (stageTwoBundled ((n : ℝ) * τ) t f f)
      (stageTwoBundled ((n : ℝ) * τ) t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrectionBundled externalStep τ hτ n f hfr hfm

theorem localDerivativeBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (localDerivativeBundled externalStep τ hτ n t f hfr hfm).val =
      localInterpolationDerivative τ ((n : ℝ) * τ) t f.val := rfl

theorem continuous_localDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => localDerivativeBundled externalStep τ hτ n t f hfr hfm) := by
  unfold localDerivativeBundled
  have hf := continuous_BTwoBundled continuous_id (continuous_const (y := f)) (continuous_const (y := f))
  have hC := continuous_cross_integrand ((n : ℝ) * τ) f
  have hQ := continuous_square_integrand ((n : ℝ) * τ) f
  fun_prop

/-- The actual interpolation satisfies all regularity hypotheses of the
internally proved time-dependent normal form. -/
theorem localInterpolation_regular (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    RegularFourierPath ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)
      (fun t => localInterpolation τ ((n : ℝ) * τ) t f.val)
      (fun t => localInterpolationDerivative τ ((n : ℝ) * τ) t f.val) := by
  have h := regularFourierPath_of_bundled
    (a := (n : ℝ) * τ) (b := ((n + 1 : ℕ) : ℝ) * τ)
    (continuous_localInterpolationBundled externalStep τ hτ n f hfr hfm)
    (continuous_localDerivativeBundled externalStep τ hτ n f hfr hfm)
    (fun t _ k => by
      simp_rw [localInterpolationBundled_val, localDerivativeBundled_val]
      exact localInterpolation_hasDerivAt f hfm k)
  simpa only [localInterpolationBundled_val, localDerivativeBundled_val] using h

end KdV
