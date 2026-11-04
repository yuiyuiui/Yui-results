import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem airy_inverse_neg (t : ℝ) (f : Fourier) : airy t (airy (-t) f) = f := by
  rw [← airy_add_time, add_neg_cancel, airy_zero]

theorem inverseDerivative_airy (t : ℝ) (f : Fourier) :
    inverseDerivative (airy t f) = airy t (inverseDerivative f) := by
  funext k
  by_cases hk : k = 0
  · simp [inverseDerivative, airy, hk]
  · simp only [inverseDerivative, if_neg hk, airy]
    ring

theorem removeMean_airy (t : ℝ) (f : Fourier) : removeMean (airy t f) = airy t (removeMean f) := by
  funext k
  by_cases hk : k = 0 <;> simp [removeMean, airy, hk]

theorem derivative_airy (t : ℝ) (f : Fourier) : derivative (airy t f) = airy t (derivative f) := by
  funext k
  simp only [derivative, airy]
  ring

theorem inverseDerivative_derivative (f : Fourier) : inverseDerivative (derivative f) = removeMean f := by
  funext k
  by_cases hk : k = 0
  · simp [inverseDerivative, removeMean, hk]
  · simp only [inverseDerivative, removeMean, if_neg hk, derivative]
    rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk : (k : ℂ) ≠ 0)), one_mul]

theorem derivative_inverseDerivative (f : Fourier) : derivative (inverseDerivative f) = removeMean f := by
  funext k
  by_cases hk : k = 0
  · simp [derivative, inverseDerivative, removeMean, hk]
  · simp only [derivative, inverseDerivative, removeMean, if_neg hk]
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk : (k : ℂ) ≠ 0)), one_mul]

/-- The substitution in (14), with no commutation through a product. -/
theorem J_B (t : ℝ) (f g h : Fourier) :
    J t (B t f g) h = airy (-t) (removeMean
      (product (removeMean (product (airy t f) (airy t g))) (airy t (inverseDerivative h)))) := by
  unfold J B
  rw [inverseDerivative_airy, inverseDerivative_derivative, airy_inverse_neg]

theorem J_B_integral (a b : ℝ) (f g h : ℝ → Fourier) (k : ℤ) :
    (∫ t : ℝ in a..b, J t (B t (f t) (g t)) (h t) k) = CIntegral a b f g h k := by
  unfold CIntegral
  apply intervalIntegral.integral_congr
  intro t _
  exact congrFun (J_B t (f t) (g t) (h t)) k

@[simp] theorem hNorm_neg (s : ℝ) (f : Fourier) : hNorm s (-f) = hNorm s f := by
  unfold hNorm
  congr 1
  apply tsum_congr
  intro k
  simp [weighted]

theorem hNorm_sub_le {s : ℝ} {f g : Fourier} (hf : InSobolev s f) (hg : InSobolev s g) :
    hNorm s (f - g) ≤ hNorm s f + hNorm s g := by
  let F : Sobolev s := ⟨f, hf⟩
  let G : Sobolev s := ⟨g, hg⟩
  have h := norm_sub_le F G
  simp only [sobolev_norm] at h
  change hNorm s (f - g) ≤ hNorm s f + hNorm s g at h
  exact h

theorem bilinearStage_h1_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (a t : ℝ) : InSobolev 1 (bilinearStage a t f g) ∧
      hNorm 1 (bilinearStage a t f g) ≤
        (4 / 3 : ℝ) * h1EmbeddingConstant * hNorm 0 f * hNorm 0 g := by
  obtain ⟨hm₁, hn₁⟩ := J_h1_bound hf hg t
  obtain ⟨hm₂, hn₂⟩ := J_h1_bound hf hg a
  refine ⟨(hm₁.sub hm₂).smul _, ?_⟩
  rw [bilinearStage, hNorm_smul (hm₁.sub hm₂)]
  have hn : ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) := by norm_num
  rw [hn]
  have hs := hNorm_sub_le hm₁ hm₂
  nlinarith

end KdV
