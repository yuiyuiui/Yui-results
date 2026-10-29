import Reflection
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

/-- Homogeneous weights used by Babin–Ilyin–Titi, with zero mean required
separately so that the zero frequency contributes nothing. -/
def homogeneousWeight (s : ℝ) (k : ℤ) : ℝ := |(k : ℝ)| ^ s

def homogeneousWeighted (s : ℝ) (f : Fourier) : Fourier := fun k => (homogeneousWeight s k : ℂ) * f k

def InHomSobolev (s : ℝ) (f : Fourier) : Prop :=
  MeanZero f ∧ Memℓp (homogeneousWeighted s f) 2

def homogeneousNorm (s : ℝ) (f : Fourier) : ℝ :=
  Real.sqrt (∑' k : ℤ, ‖homogeneousWeighted s f k‖ ^ 2)

theorem homogeneousNorm_nonneg (s : ℝ) (f : Fourier) : 0 ≤ homogeneousNorm s f := Real.sqrt_nonneg _

theorem norm_homogeneousWeighted (s : ℝ) (f : Fourier) (k : ℤ) :
    ‖homogeneousWeighted s f k‖ = homogeneousWeight s k * ‖f k‖ := by
  simp only [homogeneousWeighted, homogeneousWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (k : ℝ)) s)]

theorem homogeneousNorm_eq_lpNorm {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) :
    homogeneousNorm s f = ‖(⟨homogeneousWeighted s f, hf.2⟩ : L2Seq)‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp [homogeneousNorm, Real.sqrt_eq_rpow]

@[simp] theorem homogeneousWeighted_zero (f : Fourier) : homogeneousWeighted 0 f = f := by
  funext k
  simp [homogeneousWeighted, homogeneousWeight]

@[simp] theorem homogeneousNorm_zero (f : Fourier) : homogeneousNorm 0 f = hNorm 0 f := by
  simp only [homogeneousNorm, homogeneousWeighted_zero, hNorm, weighted_zero]

theorem weight_eq_weightOne_rpow (s : ℝ) (k : ℤ) : weight s k = (weight 1 k) ^ s := by
  unfold weight
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + (k : ℝ) ^ 2)]
  congr 1
  ring

/-- An explicit comparison constant is sufficient for transferring the source
norms; it depends only on the fixed regularity. -/
theorem weight_le_homogeneous {s : ℝ} (hs : 0 ≤ s) {k : ℤ} (hk : k ≠ 0) :
    weight s k ≤ (2 : ℝ) ^ s * homogeneousWeight s k := by
  have hkone : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hw : weight 1 k ≤ 2 * |(k : ℝ)| := (weight_one_le_one_add_abs k).trans (by linarith)
  rw [weight_eq_weightOne_rpow]
  calc
    _ ≤ (2 * |(k : ℝ)|) ^ s := Real.rpow_le_rpow (weight_pos 1 k).le hw hs
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (k : ℝ))]; rfl

theorem InSobolev.to_homogeneous {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InSobolev s f) (hfm : MeanZero f) : InHomSobolev s f := by
  refine ⟨hfm, ?_⟩
  apply Memℓp.mono' hf
  intro k
  rw [norm_homogeneousWeighted, norm_weighted]
  exact mul_le_mul_of_nonneg_right (abs_rpow_le_weight hs k) (norm_nonneg _)

theorem homogeneousNorm_le_hNorm {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InSobolev s f) (hfm : MeanZero f) : homogeneousNorm s f ≤ hNorm s f := by
  rw [homogeneousNorm_eq_lpNorm (hf.to_homogeneous hs hfm), hNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s f k‖ ≤ ‖weighted s f k‖
  rw [norm_homogeneousWeighted, norm_weighted]
  exact mul_le_mul_of_nonneg_right (abs_rpow_le_weight hs k) (norm_nonneg _)

theorem homogeneous_weighted_comparison {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hfm : MeanZero f) (k : ℤ) :
    ‖weighted s f k‖ ≤ (2 : ℝ) ^ s * ‖homogeneousWeighted s f k‖ := by
  by_cases hk : k = 0
  · subst k
    change f 0 = 0 at hfm
    simp [weighted, homogeneousWeighted, hfm]
  · rw [norm_weighted, norm_homogeneousWeighted]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (weight_le_homogeneous hs hk) (norm_nonneg (f k))

theorem InHomSobolev.to_inhomogeneous {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InHomSobolev s f) : InSobolev s f := by
  apply Memℓp.mono' (hf.2.const_smul (((2 : ℝ) ^ s : ℝ) : ℂ))
  intro k
  have hb := homogeneous_weighted_comparison hs hf.1 k
  simpa only [Pi.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)] using hb

theorem hNorm_le_homogeneousNorm {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InHomSobolev s f) : hNorm s f ≤ (2 : ℝ) ^ s * homogeneousNorm s f := by
  have hi := hf.to_inhomogeneous hs
  rw [hNorm_eq_lpNorm hi, homogeneousNorm_eq_lpNorm hf]
  calc
    _ ≤ ‖(((2 : ℝ) ^ s : ℝ) : ℂ) • (⟨homogeneousWeighted s f, hf.2⟩ : L2Seq)‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro k
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)]
        using homogeneous_weighted_comparison hs hf.1 k
    _ = _ := by
      rw [norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)]

theorem homogeneous_reflectSign {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) :
    InHomSobolev s (reflectSign f) := by
  refine ⟨reflectSign_meanZero hf.1, ?_⟩
  apply memℓp_gen
  have h := (Equiv.neg ℤ).summable_iff.mpr (hf.2.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
  simpa only [Function.comp_def, Equiv.neg_apply, norm_homogeneousWeighted,
    homogeneousWeight, reflectSign, Int.cast_neg, abs_neg, norm_neg] using h

theorem homogeneousNorm_reflectSign (s : ℝ) (f : Fourier) :
    homogeneousNorm s (reflectSign f) = homogeneousNorm s f := by
  unfold homogeneousNorm
  congr 1
  calc
    _ = ∑' k : ℤ, ‖homogeneousWeighted s f (-k)‖ ^ 2 := by
      apply tsum_congr
      intro k
      simp [norm_homogeneousWeighted, homogeneousWeight, reflectSign]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ‖homogeneousWeighted s f k‖ ^ 2)

end KdV
