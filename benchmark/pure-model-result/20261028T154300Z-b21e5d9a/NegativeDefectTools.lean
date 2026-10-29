import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem MeanZero.add {f g : Fourier} (hf : MeanZero f) (hg : MeanZero g) : MeanZero (f + g) := by
  change f 0 + g 0 = 0
  rw [hf, hg, add_zero]

theorem MeanZero.sub {f g : Fourier} (hf : MeanZero f) (hg : MeanZero g) : MeanZero (f - g) := by
  change f 0 - g 0 = 0
  rw [hf, hg, sub_zero]

theorem MeanZero.smul {f : Fourier} (hf : MeanZero f) (z : ℂ) : MeanZero (z • f) := by
  change z * f 0 = 0
  rw [hf, mul_zero]

theorem endpointCorrection_meanZero (τ a : ℝ) (f : Fourier) : MeanZero (endpointCorrection τ a f) :=
  (frozenSquare_meanZero a (a + τ) f).add (remainder_meanZero τ a f f f)

theorem localInterpolation_meanZero (τ a t : ℝ) {f : Fourier} (hf : MeanZero f) :
    MeanZero (localInterpolation τ a t f) :=
  (((hf.add (stage_meanZero a t f f)).add (frozenCross_meanZero a t f)).add
    (frozenSquare_meanZero a t f)).sub ((endpointCorrection_meanZero τ a f).smul _)

theorem interpolationRemainder_meanZero (τ a t : ℝ) {f : Fourier} (hf : MeanZero f) :
    MeanZero (interpolationRemainder τ a t f) :=
  (localInterpolation_meanZero τ a t hf).sub (hf.add (stage_meanZero a t f f))

/-- Mean-zero negative norms of order at least one are controlled by the
inverse derivative, exactly as used in the small-norm part of (24). -/
theorem negative_hNorm_le_inverse {p : ℝ} (hp : 1 ≤ p) {f : Fourier}
    (hf : InSobolev 0 f) (hfm : MeanZero f) :
    hNorm (-p) f ≤ hNorm 0 (inverseDerivative f) := by
  have hi := inverseDerivative_inSobolev_same hf
  have hb (k : ℤ) : ‖weighted (-p) f k‖ ≤ 1 * ‖weighted 0 (inverseDerivative f) k‖ := by
    by_cases hk : k = 0
    · subst k
      have hz : f 0 = 0 := hfm
      simp [weighted, hz, inverseDerivative]
    · have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (intCast_ne_zero hk)
      have hw : weight (-p) k ≤ |(k : ℝ)|⁻¹ := by
        calc
          _ ≤ weight (-1) k := weight_mono (by linarith : -p ≤ -1) k
          _ = (weight 1 k)⁻¹ := by simpa using weight_neg 1 k
          _ ≤ _ := inv_anti₀ hkpos (weight_one_ge_abs k)
      rw [norm_weighted, weighted_zero]
      simp only [one_mul, inverseDerivative, if_neg hk, norm_mul, norm_inv,
        Complex.norm_I, Complex.norm_intCast]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (f k))
  simpa only [one_mul] using hNorm_le_of_weighted_bound hi (by norm_num : (0 : ℝ) ≤ 1) hb

end KdV
