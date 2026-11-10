import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem removeMean_coeff_norm_le (f : Fourier) (k : ℤ) : ‖removeMean f k‖ ≤ ‖f k‖ := by
  by_cases hk : k = 0
  · simp [removeMean, hk]
  · simp [removeMean, hk]

/-- Absolute convergence of a bounded coefficient sequence convolved with an
`H¹` input. This is used for the actual nested trilinear operator. -/
theorem bounded_h1_convolution {f g : Fourier} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k, ‖f k‖ ≤ A) (hg : InSobolev 1 g) (k : ℤ) :
    Summable (fun a : ℤ => f a * g (k - a)) ∧
      ‖product f g k‖ ≤ A * h1EmbeddingConstant * hNorm 1 g := by
  obtain ⟨hgs, hgb⟩ := h1_absolute_coefficients hg
  have hgr : Summable (fun a : ℤ => ‖g (k - a)‖) := (reflectAt k).summable_iff.mpr hgs
  have hen : Summable (fun a : ℤ => A * ‖g (k - a)‖) := hgr.mul_left A
  have hs : Summable (fun a : ℤ => ‖f a * g (k - a)‖) := by
    apply hen.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)
  refine ⟨hs.of_norm, ?_⟩
  calc
    _ ≤ ∑' a : ℤ, ‖f a * g (k - a)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' a : ℤ, A * ‖g (k - a)‖ := by
      apply hs.tsum_le_tsum _ hen
      intro a
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)
    _ = A * ∑' a : ℤ, ‖g (k - a)‖ := tsum_mul_left
    _ = A * ∑' a : ℤ, ‖g a‖ := by
      congr 1
      exact (reflectAt k).tsum_eq (fun a => ‖g a‖)
    _ ≤ A * (h1EmbeddingConstant * hNorm 1 g) := mul_le_mul_of_nonneg_left hgb hA
    _ = _ := by ring

def CIntegrand (t : ℝ) (f g h : Fourier) : Fourier :=
  airy (-t) (removeMean (product (removeMean (product (airy t f) (airy t g)))
    (airy t (inverseDerivative h))))

/-- The nested convolution in (3.13) is absolutely convergent even though its
inner `L² × L²` product need not itself have square-summable coefficients. -/
theorem CIntegrand_summable_bound {f g h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (t : ℝ) (k : ℤ) :
    Summable (fun a : ℤ => removeMean (product (airy t f) (airy t g)) a *
      airy t (inverseDerivative h) (k - a)) ∧
    ‖CIntegrand t f g h k‖ ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * hNorm 0 f * hNorm 0 g * hNorm 0 h := by
  have hb (a : ℤ) : ‖removeMean (product (airy t f) (airy t g)) a‖ ≤ hNorm 0 f * hNorm 0 g := by
    exact (removeMean_coeff_norm_le _ a).trans (by
      simpa only [airy_hNorm] using product_coeff_bound (airy_inSobolev hf t) (airy_inSobolev hg t) a)
  obtain ⟨hs, hn⟩ := bounded_h1_convolution (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g)) hb
    (airy_inSobolev (inverseDerivative_inSobolev_one hh) t) k
  refine ⟨hs, ?_⟩
  have hC : 0 ≤ h1EmbeddingConstant := le_trans zero_le_one h1EmbeddingConstant_ge_one
  have hnon : 0 ≤ (hNorm 0 f * hNorm 0 g) * h1EmbeddingConstant := by
    exact mul_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g)) hC
  calc
    _ = ‖removeMean (product (removeMean (product (airy t f) (airy t g)))
        (airy t (inverseDerivative h))) k‖ := by
      simp only [CIntegrand, airy, norm_mul, airy_multiplier_norm, one_mul]
    _ ≤ ‖product (removeMean (product (airy t f) (airy t g))) (airy t (inverseDerivative h)) k‖ :=
      removeMean_coeff_norm_le _ k
    _ ≤ (hNorm 0 f * hNorm 0 g) * h1EmbeddingConstant * hNorm 1 (inverseDerivative h) := by
      simpa only [airy_hNorm] using hn
    _ ≤ (hNorm 0 f * hNorm 0 g) * h1EmbeddingConstant * (Real.sqrt 2 * hNorm 0 h) :=
      mul_le_mul_of_nonneg_left (inverseDerivative_hNorm_one hh) hnon
    _ = _ := by ring

theorem CIntegral_eq_integrand (a b : ℝ) (f g h : ℝ → Fourier) (k : ℤ) :
    CIntegral a b f g h k = ∫ t : ℝ in a..b, CIntegrand t (f t) (g t) (h t) k := rfl

@[simp] theorem CIntegrand_meanZero (t : ℝ) (f g h : Fourier) : MeanZero (CIntegrand t f g h) := by
  simp [CIntegrand, MeanZero]

theorem CIntegral_meanZero (a b : ℝ) (f g h : ℝ → Fourier) : MeanZero (CIntegral a b f g h) := by
  change (∫ t : ℝ in a..b, CIntegrand t (f t) (g t) (h t) 0) = 0
  simp [CIntegrand, airy, removeMean]

end KdV
