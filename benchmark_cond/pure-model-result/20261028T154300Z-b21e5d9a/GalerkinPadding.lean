import HomogeneousAlgebra
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

def symmetricSpike (p : ℤ) (a : ℝ) : L2Seq :=
  lp.single 2 p (a : ℂ) + lp.single 2 (-p) (a : ℂ)

theorem symmetricSpike_zero {p : ℤ} (hp : p ≠ 0) (a : ℝ) : symmetricSpike p a 0 = 0 := by
  simp [symmetricSpike, lp.single_apply, hp, eq_comm]

theorem symmetricSpike_real (p : ℤ) (a : ℝ) : RealValued (symmetricSpike p a).val := by
  intro k
  simp only [symmetricSpike, lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply]
  have h₁ : (-k = p) ↔ (k = -p) := by omega
  have h₂ : (-k = -p) ↔ (k = p) := by omega
  simp only [h₁, h₂, map_add]
  split_ifs <;> simp

theorem symmetricSpike_norm_sq {p : ℤ} (hp : p ≠ 0) (a : ℝ) :
    ‖symmetricSpike p a‖ ^ 2 = 2 * a ^ 2 := by
  have hpneg : p ≠ -p := by omega
  have horth : inner ℂ (lp.single 2 p (a : ℂ) : L2Seq) (lp.single 2 (-p) (a : ℂ) : L2Seq) = 0 := by
    rw [lp.inner_single_left]
    simp [lp.single_apply, hpneg]
  have hsq : ‖symmetricSpike p a‖ ^ 2 = ‖(lp.single 2 p (a : ℂ) : L2Seq)‖ ^ 2 +
      ‖(lp.single 2 (-p) (a : ℂ) : L2Seq)‖ ^ 2 := by
    simpa only [symmetricSpike, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [hsq, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_add_symmetricSpike_sq {p : ℤ} (hp : p ≠ 0) (a : ℝ)
    (F : L2Seq) (hFp : F p = 0) (hFm : F (-p) = 0) :
    ‖F + symmetricSpike p a‖ ^ 2 = ‖F‖ ^ 2 + 2 * a ^ 2 := by
  have horth : inner ℂ F (symmetricSpike p a) = 0 := by
    rw [symmetricSpike, inner_add_right, lp.inner_single_right, lp.inner_single_right, hFp, hFm]
    simp
  have hsq : ‖F + symmetricSpike p a‖ ^ 2 = ‖F‖ ^ 2 + ‖symmetricSpike p a‖ ^ 2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [hsq, symmetricSpike_norm_sq hp]

/-- A datum in a homogeneous norm ball can be padded outside any given source
Galerkin projection to lie on the exact norm sphere. The low modes are unchanged,
and reality, zero mean and the `L²` bound are retained. This is solely an exact-
flow argument; no projection or padding is made in the numerical method. -/
theorem homogeneous_sphere_padding {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    {f : Fourier} (hf : InHomSobolev s f) (hfr : RealValued f) (hfR : homogeneousNorm s f ≤ R)
    (m : ℕ) : ∃ g : Fourier,
      RealValued g ∧ InHomSobolev s g ∧ homogeneousNorm s g = R ∧
      homogeneousNorm 0 g ≤ R ∧ cutoff m g = cutoff m f := by
  let p : ℤ := (m : ℤ) + 1
  have hp : p ≠ 0 := by dsimp [p]; omega
  have hpo : p ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by simp [p]
  have hmo : -p ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by simp [p]
  let C : L2Seq := homogeneousLp s (cutoff m f) (hf.cutoff m)
  have hCp : C p = 0 := by
    change homogeneousWeighted s (cutoff m f) p = 0
    rw [homogeneousWeighted_cutoff]
    simp [cutoff, hpo]
  have hCm : C (-p) = 0 := by
    change homogeneousWeighted s (cutoff m f) (-p) = 0
    rw [homogeneousWeighted_cutoff]
    simp [cutoff, hmo]
  have hC0 : C 0 = 0 := by
    change (homogeneousWeight s 0 : ℂ) * cutoff m f 0 = 0
    rw [cutoff_meanZero hf.1 m, mul_zero]
  have hCR : ‖C‖ ≤ R := by
    rw [homogeneousLp_norm]
    exact (homogeneousNorm_cutoff_le hf m).trans hfR
  let a : ℝ := Real.sqrt ((R ^ 2 - ‖C‖ ^ 2) / 2)
  have hRad : 0 ≤ (R ^ 2 - ‖C‖ ^ 2) / 2 := by nlinarith [norm_nonneg C]
  have haSq : a ^ 2 = (R ^ 2 - ‖C‖ ^ 2) / 2 := Real.sq_sqrt hRad
  let Q : L2Seq := C + symmetricSpike p a
  have hQ0 : Q 0 = 0 := by
    change C 0 + symmetricSpike p a 0 = 0
    rw [hC0, symmetricSpike_zero hp, zero_add]
  have hQr : RealValued Q.val :=
    (homogeneousWeighted_real s (cutoff_real hfr m)).add (symmetricSpike_real p a)
  have hQs : ‖Q‖ ^ 2 = R ^ 2 := by
    have h := norm_add_symmetricSpike_sq hp a C hCp hCm
    change ‖Q‖ ^ 2 = ‖C‖ ^ 2 + 2 * a ^ 2 at h
    nlinarith only [h, haSq]
  have hQN : ‖Q‖ = R := by nlinarith [norm_nonneg Q]
  let g : Fourier := homogeneousReconstruct s Q
  have hg := homogeneousReconstruct_inHomSobolev s Q hQ0
  have hgn : homogeneousNorm s g = R := by
    rw [homogeneousReconstruct_norm s Q hQ0, hQN]
  refine ⟨g, homogeneousReconstruct_real s Q hQr, hg, hgn, ?_, ?_⟩
  · exact (homogeneousNorm_mono hg hs).trans_eq hgn
  · funext k
    by_cases hki : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · simp only [cutoff, if_pos hki]
      by_cases hk : k = 0
      · subst k
        have hf0 : f 0 = 0 := hf.1
        simp [g, homogeneousReconstruct, hf0]
      · have hpk : p ≠ k := by intro he; subst k; exact hpo hki
        have hmk : -p ≠ k := by intro he; subst k; exact hmo hki
        have hsk : symmetricSpike p a k = 0 := by simp [symmetricSpike, lp.single_apply, hpk, hmk]
        have hQk : Q k = (homogeneousWeight s k : ℂ) * f k := by
          change C k + symmetricSpike p a k = _
          rw [hsk, add_zero]
          change (homogeneousWeight s k : ℂ) * cutoff m f k = _
          simp [cutoff, hki]
        change (if k = 0 then 0 else (homogeneousWeight s k : ℂ)⁻¹ * Q k) = f k
        rw [if_neg hk, hQk, ← mul_assoc,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (homogeneousWeight_pos_of_ne_zero s hk).ne'), one_mul]
    · simp [cutoff, hki]

end KdV
