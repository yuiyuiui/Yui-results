import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

@[simp] theorem homogeneousWeighted_add (s : ℝ) (f g : Fourier) :
    homogeneousWeighted s (f + g) = homogeneousWeighted s f + homogeneousWeighted s g := by
  funext k
  simp [homogeneousWeighted, mul_add]

@[simp] theorem homogeneousWeighted_smul (s : ℝ) (z : ℂ) (f : Fourier) :
    homogeneousWeighted s (z • f) = z • homogeneousWeighted s f := by
  funext k
  simp [homogeneousWeighted, mul_left_comm]

theorem homogeneousWeighted_cutoff (s : ℝ) (m : ℕ) (f : Fourier) :
    homogeneousWeighted s (cutoff m f) = cutoff m (homogeneousWeighted s f) := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [homogeneousWeighted, cutoff, hk]

theorem homogeneousWeighted_real (s : ℝ) {f : Fourier} (hf : RealValued f) :
    RealValued (homogeneousWeighted s f) := by
  intro k
  simp [homogeneousWeighted, homogeneousWeight, hf k]

theorem homogeneousWeight_pos_of_ne_zero (s : ℝ) {k : ℤ} (hk : k ≠ 0) :
    0 < homogeneousWeight s k :=
  Real.rpow_pos_of_pos (abs_pos.mpr (intCast_ne_zero hk)) s

theorem InHomSobolev.of_le {s r : ℝ} {f : Fourier} (hf : InHomSobolev r f) (hsr : s ≤ r) :
    InHomSobolev s f := by
  refine ⟨hf.1, ?_⟩
  apply Memℓp.mono' hf.2
  intro k
  by_cases hk : k = 0
  · subst k
    have hf0 : f 0 = 0 := hf.1
    simp [homogeneousWeighted, hf0]
  · rw [norm_homogeneousWeighted, norm_homogeneousWeighted]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Int.one_le_abs hk) hsr

theorem homogeneousNorm_mono {s r : ℝ} {f : Fourier} (hf : InHomSobolev r f) (hsr : s ≤ r) :
    homogeneousNorm s f ≤ homogeneousNorm r f := by
  rw [homogeneousNorm_eq_lpNorm (hf.of_le hsr), homogeneousNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s f k‖ ≤ ‖homogeneousWeighted r f k‖
  by_cases hk : k = 0
  · subst k
    have hf0 : f 0 = 0 := hf.1
    simp [homogeneousWeighted, hf0]
  · rw [norm_homogeneousWeighted, norm_homogeneousWeighted]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Int.one_le_abs hk) hsr) (norm_nonneg _)

theorem InHomSobolev.cutoff {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) (m : ℕ) :
    InHomSobolev s (KdV.cutoff m f) := by
  refine ⟨cutoff_meanZero hf.1 m, ?_⟩
  apply Memℓp.mono' hf.2
  intro k
  rw [homogeneousWeighted_cutoff]
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp [KdV.cutoff, hk]
  · simp [KdV.cutoff, hk]

theorem homogeneousNorm_cutoff_le {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) (m : ℕ) :
    homogeneousNorm s (cutoff m f) ≤ homogeneousNorm s f := by
  rw [homogeneousNorm_eq_lpNorm (hf.cutoff m), homogeneousNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s (cutoff m f) k‖ ≤ ‖homogeneousWeighted s f k‖
  rw [homogeneousWeighted_cutoff]
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

def homogeneousLp (s : ℝ) (f : Fourier) (hf : InHomSobolev s f) : L2Seq :=
  ⟨homogeneousWeighted s f, hf.2⟩

theorem homogeneousLp_norm (s : ℝ) (f : Fourier) (hf : InHomSobolev s f) :
    ‖homogeneousLp s f hf‖ = homogeneousNorm s f := (homogeneousNorm_eq_lpNorm hf).symm

def homogeneousReconstruct (s : ℝ) (F : L2Seq) : Fourier := fun k =>
  if k = 0 then 0 else (homogeneousWeight s k : ℂ)⁻¹ * F k

theorem homogeneousReconstruct_weighted (s : ℝ) (F : L2Seq) (hF0 : F 0 = 0) :
    homogeneousWeighted s (homogeneousReconstruct s F) = F := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [homogeneousWeighted, homogeneousReconstruct, hF0]
  · simp [homogeneousWeighted, homogeneousReconstruct, hk,
      Complex.ofReal_ne_zero.mpr (homogeneousWeight_pos_of_ne_zero s hk).ne']

theorem homogeneousReconstruct_inHomSobolev (s : ℝ) (F : L2Seq) (hF0 : F 0 = 0) :
    InHomSobolev s (homogeneousReconstruct s F) := by
  refine ⟨by simp [MeanZero, homogeneousReconstruct], ?_⟩
  rw [homogeneousReconstruct_weighted s F hF0]
  exact F.property

theorem homogeneousReconstruct_norm (s : ℝ) (F : L2Seq) (hF0 : F 0 = 0) :
    homogeneousNorm s (homogeneousReconstruct s F) = ‖F‖ := by
  rw [homogeneousNorm_eq_lpNorm (homogeneousReconstruct_inHomSobolev s F hF0)]
  congr 1
  apply Subtype.ext
  exact homogeneousReconstruct_weighted s F hF0

theorem homogeneousReconstruct_real (s : ℝ) (F : L2Seq) (hF : RealValued F.val) :
    RealValued (homogeneousReconstruct s F) := by
  intro k
  by_cases hk : k = 0 <;> simp [homogeneousReconstruct, homogeneousWeight, hk, hF k]

end KdV
