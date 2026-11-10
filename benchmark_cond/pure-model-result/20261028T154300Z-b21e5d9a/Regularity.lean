import VariableSeries
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem weighted_coeff_bound {s : ℝ} {f : Fourier} (hf : InSobolev s f) (k : ℤ) :
    ‖weighted s f k‖ ≤ hNorm s f := by
  rw [hNorm_eq_lpNorm hf]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ⟨weighted s f, hf⟩ k

theorem weight_neg (s : ℝ) (k : ℤ) : weight (-s) k = (weight s k)⁻¹ := by
  unfold weight
  rw [neg_div, Real.rpow_neg (by positivity)]

def sobolevEnvelope (M : ℝ) : Fourier := fun k => (M : ℂ) * (weight (-1) k : ℂ)

theorem sobolevEnvelope_inSobolev (M : ℝ) : InSobolev 0 (sobolevEnvelope M) := by
  rw [inSobolev_zero_iff]
  exact (negativeWeightLp 1 (by norm_num)).property.const_smul (M : ℂ)

theorem h1_coeff_envelope {f : Fourier} (hf : InSobolev 1 f) {M : ℝ}
    (hM : 0 ≤ M) (hfM : hNorm 1 f ≤ M) (k : ℤ) : ‖f k‖ ≤ ‖sobolevEnvelope M k‖ := by
  have hw := (weighted_coeff_bound hf k).trans hfM
  rw [norm_weighted] at hw
  change ‖f k‖ ≤ ‖(M : ℂ) * (weight (-1) k : ℂ)‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hM,
    Complex.norm_real, Real.norm_of_nonneg (weight_pos (-1) k).le, weight_neg]
  have heq : ‖f k‖ = (weight 1 k)⁻¹ * (weight 1 k * ‖f k‖) := by
    rw [← mul_assoc, inv_mul_cancel₀ (weight_pos 1 k).ne', one_mul]
  rw [heq]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr (weight_pos 1 k).le)

/-- The envelope hypothesis in the internally proved normal form follows from
ordinary uniform `H¹` bounds; no uniform higher norm is needed in its conclusion. -/
theorem regularFourierPath_of_h1_bounds {a b M Md : ℝ} (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    {f df : ℝ → Fourier}
    (hc : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b))
    (hdc : ∀ k, ContinuousOn (fun t : ℝ => df t k) (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k, HasDerivAt (fun r : ℝ => f r k) (df t k) t)
    (hb : ∀ t ∈ Set.Icc a b, InSobolev 1 (f t) ∧ hNorm 1 (f t) ≤ M)
    (hdb : ∀ t ∈ Set.Icc a b, InSobolev 1 (df t) ∧ hNorm 1 (df t) ≤ Md) :
    RegularFourierPath a b f df where
  continuous := hc
  derivative_continuous := hdc
  hasDerivAt := hd
  envelope := by
    refine ⟨sobolevEnvelope M, sobolevEnvelope Md, sobolevEnvelope_inSobolev M,
      sobolevEnvelope_inSobolev Md, ?_⟩
    intro t ht k
    exact ⟨h1_coeff_envelope (hb t ht).1 hM (hb t ht).2 k,
      h1_coeff_envelope (hdb t ht).1 hMd (hdb t ht).2 k⟩

set_option maxHeartbeats 800000 in
/-- Smooth inputs supply the regularity of their twisted vector field needed
only to justify normal-form identities. Final estimates use the negative norm. -/
theorem B_h1_of_h2 {f g : Fourier} (hf : InSobolev 2 f) (hg : InSobolev 2 g) (t : ℝ) :
    InSobolev 1 (B t f g) ∧
      hNorm 1 (B t f g) ≤ 4 * h1EmbeddingConstant * hNorm 2 f * hNorm 2 g := by
  have hf1 := (airy_inSobolev hf t).of_le (by norm_num : (1 : ℝ) ≤ 2)
  have hg1 := (airy_inSobolev hg t).of_le (by norm_num : (1 : ℝ) ≤ 2)
  have hfp : InSobolev ((1 : ℝ) + 1) (airy t f) := by
    norm_num
    exact airy_inSobolev hf t
  have hgp : InSobolev ((1 : ℝ) + 1) (airy t g) := by
    norm_num
    exact airy_inSobolev hg t
  have hdf : InSobolev 1 (derivative (airy t f)) := derivative_inSobolev hfp
  have hdg : InSobolev 1 (derivative (airy t g)) := derivative_inSobolev hgp
  have hprod1 := h1_product_bound hdf hg1
  have hprod2 := h1_product_bound hf1 hdg
  have heq := derivative_product hf1 hg1
  have hdprod : InSobolev 1 (derivative (product (airy t f) (airy t g))) := by
    rw [heq]
    exact hprod1.1.add hprod2.1
  refine ⟨airy_inSobolev hdprod (-t), ?_⟩
  rw [B, airy_hNorm, heq]
  calc
    _ ≤ hNorm 1 (product (derivative (airy t f)) (airy t g)) +
        hNorm 1 (product (airy t f) (derivative (airy t g))) := hNorm_add_le hprod1.1 hprod2.1
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 (derivative (airy t f)) * hNorm 1 (airy t g) +
        (2 * h1EmbeddingConstant) * hNorm 1 (airy t f) * hNorm 1 (derivative (airy t g)) :=
      add_le_add hprod1.2 hprod2.2
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g +
        (2 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g := by
      have hC : 0 ≤ 2 * h1EmbeddingConstant := by linarith [h1EmbeddingConstant_ge_one]
      have hfD : hNorm 1 (derivative (airy t f)) ≤ hNorm 2 f := by
        have h := derivative_hNorm hfp
        norm_num at h
        simpa only [airy_hNorm] using h
      have hgD : hNorm 1 (derivative (airy t g)) ≤ hNorm 2 g := by
        have h := derivative_hNorm hgp
        norm_num at h
        simpa only [airy_hNorm] using h
      have hfL : hNorm 1 (airy t f) ≤ hNorm 2 f := by
        simpa only [airy_hNorm] using hNorm_mono (airy_inSobolev hf t) (by norm_num : (1 : ℝ) ≤ 2)
      have hgL : hNorm 1 (airy t g) ≤ hNorm 2 g := by
        simpa only [airy_hNorm] using hNorm_mono (airy_inSobolev hg t) (by norm_num : (1 : ℝ) ≤ 2)
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hfD hC) hgL (hNorm_nonneg _ _)
          (mul_nonneg hC (hNorm_nonneg _ _)))
        (mul_le_mul (mul_le_mul_of_nonneg_left hfL hC) hgD (hNorm_nonneg _ _)
          (mul_nonneg hC (hNorm_nonneg _ _)))
    _ = _ := by ring

end KdV
