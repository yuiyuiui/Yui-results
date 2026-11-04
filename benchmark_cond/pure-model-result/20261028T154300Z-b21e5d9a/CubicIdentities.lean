import InterpolationRegularity
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem J_smul_left (t : ℝ) (z : ℂ) (f g : Fourier) : J t (z • f) g = z • J t f g := by
  unfold J
  rw [inverseDerivative_smul, airy_smul, product_smul_left, removeMean_smul, airy_smul]

theorem J_smul_right (t : ℝ) (z : ℂ) (f g : Fourier) : J t f (z • g) = z • J t f g := by
  rw [J_comm t f (z • g), J_smul_left, J_comm t g f]

@[simp] theorem J_zero_left (t : ℝ) (g : Fourier) : J t 0 g = 0 := by
  simpa only [zero_smul] using J_smul_left t 0 g g

@[simp] theorem J_zero_right (t : ℝ) (f : Fourier) : J t f 0 = 0 := by
  rw [J_comm, J_zero_left]

@[simp] theorem bilinearStage_self (a : ℝ) (f g : Fourier) : bilinearStage a a f g = 0 := by
  simp [bilinearStage]

theorem stage_regular {a b : ℝ} (f : Sobolev 2) (hfm : MeanZero f.val) :
    RegularFourierPath a b (fun t => bilinearStage a t f.val f.val)
      (fun t => (1 / 2 : ℂ) • B t f.val f.val) := by
  have hc : Continuous (fun t : ℝ => inclusionMap 1 2 (by norm_num) (stageTwoBundled a t f f)) :=
    (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_stageTwoBundled a f f)
  have hdc : Continuous (fun t : ℝ => (1 / 2 : ℂ) • BTwoBundled t f f) :=
    (continuous_const (y := (1 / 2 : ℂ))).smul
      (continuous_BTwoBundled continuous_id continuous_const continuous_const)
  exact regularFourierPath_of_bundled hc hdc (by
    intro t _ k
    exact stage_hasDerivAt (f.property.of_le (by norm_num))
      (f.property.of_le (by norm_num)) hfm hfm a t k)

theorem constant_regular (a b : ℝ) (f : Sobolev 1) :
    RegularFourierPath a b (fun _ => f.val) (fun _ => 0) := by
  exact regularFourierPath_of_bundled (continuous_const (y := f))
    (continuous_const (y := (0 : Sobolev 1))) (fun t _ k => hasDerivAt_const t _)

/-- Identity (23), derived from the proved variable-input normal form. The
initial boundary vanishes because the actual stage is zero there. -/
theorem frozenCross_normal_form {a b : ℝ} (hab : a ≤ b) (f : Sobolev 2)
    (hfm : MeanZero f.val) :
    frozenCross a b f.val = (1 / 3 : ℂ) • J b f.val (bilinearStage a b f.val f.val) -
      (1 / 6 : ℂ) • CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun _ => f.val) := by
  have hreg := constant_regular a b (inclusionMap 1 2 (by norm_num) f)
  have hFreg := stage_regular (a := a) (b := b) f hfm
  funext k
  have hnf := variable_normal_form hab hreg hFreg (fun _ _ => hfm)
    (fun t _ => stage_meanZero a t f.val f.val) k
  have hInt : (fun t : ℝ => J t 0 (bilinearStage a t f.val f.val) k +
      J t f.val ((1 / 2 : ℂ) • B t f.val f.val) k) =
      (fun t : ℝ => (1 / 2 : ℂ) * J t (B t f.val f.val) f.val k) := by
    funext t
    rw [J_zero_left, J_smul_right, J_comm t f.val (B t f.val f.val)]
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul]
  change (∫ t : ℝ in a..b, B t f.val (bilinearStage a t f.val f.val) k) =
    (1 / 3 : ℂ) * (J b f.val (bilinearStage a b f.val f.val) k -
      J a f.val (bilinearStage a a f.val f.val) k) -
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b,
        (J t 0 (bilinearStage a t f.val f.val) k + J t f.val ((1 / 2 : ℂ) • B t f.val f.val) k) at hnf
  rw [hInt, intervalIntegral.integral_const_mul, J_B_integral,
    bilinearStage_self, J_zero_right] at hnf
  simp only [Pi.zero_apply, sub_zero] at hnf
  change frozenCross a b f.val k = (1 / 3 : ℂ) * J b f.val (bilinearStage a b f.val f.val) k -
    (1 / 6 : ℂ) * CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun _ => f.val) k
  dsimp only [frozenCross]
  linear_combination hnf

theorem continuous_airy_coefficient (f : Fourier) (k : ℤ) :
    Continuous (fun t : ℝ => airy t f k) := by
  unfold airy
  fun_prop

theorem norm_airy_coefficient (f : Fourier) (t : ℝ) (k : ℤ) : ‖airy t f k‖ = ‖f k‖ := by
  simp only [airy, norm_mul, airy_multiplier_norm, one_mul]

theorem continuous_airy_product_coefficient {f g : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (k : ℤ) :
    Continuous (fun t : ℝ => product (airy t f) (airy t g) k) := by
  apply continuous_tsum
  · intro a
    exact (continuous_airy_coefficient f a).mul (continuous_airy_coefficient g (k - a))
  · exact absolute_convolution_summable hf hg k
  · intro a t
    rw [norm_mul, norm_airy_coefficient, norm_airy_coefficient]

theorem continuous_CIntegrand_fixed {f g h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (k : ℤ) :
    Continuous (fun t : ℝ => CIntegrand t f g h k) := by
  by_cases hk : k = 0
  · subst k
    simpa [CIntegrand, airy, removeMean] using (continuous_const (y := (0 : ℂ)))
  · have hinv := inverseDerivative_inSobolev_one hh
    have hs := (reflectAt k).summable_iff.mpr (h1_absolute_coefficients hinv).1
    have hu : Summable (fun a : ℤ => (hNorm 0 f * hNorm 0 g) * ‖inverseDerivative h (k - a)‖) :=
      hs.mul_left _
    have hinner (a : ℤ) : Continuous (fun t : ℝ =>
        removeMean (product (airy t f) (airy t g)) a * airy t (inverseDerivative h) (k - a)) := by
      by_cases ha : a = 0
      · subst a
        simpa using (continuous_const (y := (0 : ℂ)))
      · have hca : Continuous (fun t : ℝ => removeMean (product (airy t f) (airy t g)) a) := by
          simpa only [removeMean, if_neg ha] using continuous_airy_product_coefficient hf hg a
        exact hca.mul (continuous_airy_coefficient _ _)
    have hb (a : ℤ) (t : ℝ) :
        ‖removeMean (product (airy t f) (airy t g)) a * airy t (inverseDerivative h) (k - a)‖ ≤
          (hNorm 0 f * hNorm 0 g) * ‖inverseDerivative h (k - a)‖ := by
      rw [norm_mul, norm_airy_coefficient]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (removeMean_coeff_norm_le _ a).trans (by
        simpa only [airy_hNorm] using product_coeff_bound (airy_inSobolev hf t) (airy_inSobolev hg t) a)
    have hc := continuous_tsum hinner hu hb
    change Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3) *
      removeMean (product (removeMean (product (airy t f) (airy t g)))
        (airy t (inverseDerivative h))) k)
    simp only [removeMean, if_neg hk]
    have he : Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3)) := by fun_prop
    exact he.mul hc

end KdV
