import AnalysisOps
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The fixed negative Sobolev exponent in the continuous estimates. -/
def pStar : ℝ := 23 / 14

/-- The twisted KdV bilinear vector field, retaining every Fourier mode. -/
def B (t : ℝ) (f g : Fourier) : Fourier :=
  airy (-t) (derivative (product (airy t f) (airy t g)))

/-- The symmetric quadratic normal-form boundary operator. -/
def J (t : ℝ) (f g : Fourier) : Fourier :=
  airy (-t) (removeMean
    (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))))

/-- The trilinear time integral appearing in the cited Proposition 3.4.
Its coefficients are integrals; membership and bounds require proved hypotheses. -/
def CIntegral (a b : ℝ) (f g h : ℝ → Fourier) : Fourier := fun k =>
  ∫ t : ℝ in a..b,
    airy (-t) (removeMean (product (removeMean (product (airy t (f t)) (airy t (g t))))
      (airy t (inverseDerivative (h t))))) k

/-- The bilinear stage in its exact endpoint form. -/
def bilinearStage (a t : ℝ) (f g : Fourier) : Fourier :=
  (1 / 6 : ℂ) • (J t f g - J a f g)

theorem B_meanZero (t : ℝ) (f g : Fourier) : MeanZero (B t f g) := by
  simp [MeanZero, B, derivative]

theorem J_meanZero (t : ℝ) (f g : Fourier) : MeanZero (J t f g) := by
  simp [MeanZero, J]

theorem B_comm (t : ℝ) (f g : Fourier) : B t f g = B t g f := by
  rw [B, product_comm]
  rfl

theorem J_comm (t : ℝ) (f g : Fourier) : J t f g = J t g f := by
  rw [J, product_comm]
  rfl

theorem B_negative_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : InSobolev (-pStar) (B t f g) ∧
      hNorm (-pStar) (B t f g) ≤
        negativeProductConstant (9 / 14) (by norm_num) * hNorm 0 f * hNorm 0 g := by
  have hp := negative_product_bound (q := 9 / 14) (by norm_num) (airy_inSobolev hf t)
    (airy_inSobolev hg t)
  have hd : InSobolev (-pStar + 1) (product (airy t f) (airy t g)) := by
    convert hp.1 using 1; norm_num [pStar]
  refine ⟨airy_inSobolev (derivative_inSobolev hd) (-t), ?_⟩
  rw [B, airy_hNorm]
  calc
    _ ≤ hNorm (-pStar + 1) (product (airy t f) (airy t g)) := derivative_hNorm hd
    _ = hNorm (-(9 / 14)) (product (airy t f) (airy t g)) := by norm_num [pStar]
    _ ≤ _ := by simpa only [airy_hNorm] using hp.2

theorem J_h1_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : InSobolev 1 (J t f g) ∧
      hNorm 1 (J t f g) ≤ 4 * h1EmbeddingConstant * hNorm 0 f * hNorm 0 g := by
  have hp := h1_product_bound (airy_inSobolev (inverseDerivative_inSobolev_one hf) t)
    (airy_inSobolev (inverseDerivative_inSobolev_one hg) t)
  refine ⟨airy_inSobolev (removeMean_inSobolev hp.1) (-t), ?_⟩
  rw [J, airy_hNorm]
  calc
    _ ≤ hNorm 1 (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))) :=
      removeMean_hNorm_le hp.1
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 (inverseDerivative f) * hNorm 1 (inverseDerivative g) := by
      simpa only [airy_hNorm] using hp.2
    _ ≤ (2 * h1EmbeddingConstant) * (Real.sqrt 2 * hNorm 0 f) * (Real.sqrt 2 * hNorm 0 g) := by
      have hC : 0 ≤ h1EmbeddingConstant := le_trans zero_le_one h1EmbeddingConstant_ge_one
      have hF := hNorm_nonneg 0 f
      have hG := hNorm_nonneg 0 g
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (inverseDerivative_hNorm_one hf) (by positivity))
        (inverseDerivative_hNorm_one hg) (hNorm_nonneg 1 _) (by positivity)
    _ = (2 * h1EmbeddingConstant) * (Real.sqrt 2) ^ 2 * hNorm 0 f * hNorm 0 g := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

theorem l2_h1_product_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 1 g) :
    InSobolev 0 (product f g) ∧
      hNorm 0 (product f g) ≤ h1EmbeddingConstant * hNorm 0 f * hNorm 1 g := by
  let F : L2Seq := ⟨f, (inSobolev_zero_iff f).mp hf⟩
  have hc := h1_absolute_coefficients hg
  have heq : (convolutionLp g F).val = product f g := by
    funext k
    rw [product_comm f g]
    exact convolutionLp_coeff g F hc.1 k
  have hm : InSobolev 0 (product f g) := by
    apply (inSobolev_zero_iff _).mpr
    rw [← heq]
    exact (convolutionLp g F).property
  refine ⟨hm, ?_⟩
  have hn : hNorm 0 (product f g) = ‖convolutionLp g F‖ := by
    rw [hNorm_eq_lpNorm hm]
    congr 1
    apply Subtype.ext
    simpa only [weighted_zero] using heq.symm
  rw [hn]
  calc
    _ ≤ (∑' k : ℤ, ‖g k‖) * ‖F‖ := convolutionLp_norm g F hc.1
    _ ≤ (h1EmbeddingConstant * hNorm 1 g) * ‖F‖ :=
      mul_le_mul_of_nonneg_right hc.2 (norm_nonneg F)
    _ = _ := by
      have hF : ‖F‖ = hNorm 0 f := by
        rw [hNorm_eq_lpNorm hf]
        congr 1
        apply Subtype.ext
        exact (weighted_zero f).symm
      rw [hF]
      ring

/-- The sharper `J` estimate used when its first input has a small inverse derivative. -/
theorem J_inverse_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : hNorm 0 (J t f g) ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * hNorm 0 (inverseDerivative f) * hNorm 0 g := by
  have hfi := (inverseDerivative_inSobolev_one hf).of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hp := l2_h1_product_bound (airy_inSobolev hfi t)
    (airy_inSobolev (inverseDerivative_inSobolev_one hg) t)
  rw [J, airy_hNorm]
  calc
    _ ≤ hNorm 0 (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))) :=
      removeMean_hNorm_le hp.1
    _ ≤ h1EmbeddingConstant * hNorm 0 (inverseDerivative f) * hNorm 1 (inverseDerivative g) := by
      simpa only [airy_hNorm] using hp.2
    _ ≤ h1EmbeddingConstant * hNorm 0 (inverseDerivative f) * (Real.sqrt 2 * hNorm 0 g) := by
      apply mul_le_mul_of_nonneg_left (inverseDerivative_hNorm_one hg)
      exact mul_nonneg (le_trans zero_le_one h1EmbeddingConstant_ge_one) (hNorm_nonneg 0 _)
    _ = _ := by ring

end KdV
