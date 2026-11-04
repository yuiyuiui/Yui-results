import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem highCutoff_smul (m : ℕ) (z : ℂ) (f : Fourier) : highCutoff m (z • f) = z • highCutoff m f := by
  unfold highCutoff
  rw [cutoff_smul]
  module

theorem hNorm_normal_form_sum {s : ℝ} {A B C D : Fourier}
    (hA : InSobolev s A) (hB : InSobolev s B) (hC : InSobolev s C) (hD : InSobolev s D) :
    InSobolev s ((1 / 3 : ℂ) • A - (1 / 3 : ℂ) • B - (1 / 6 : ℂ) • C + (1 / 3 : ℂ) • D) ∧
    hNorm s ((1 / 3 : ℂ) • A - (1 / 3 : ℂ) • B - (1 / 6 : ℂ) • C + (1 / 3 : ℂ) • D) ≤
      hNorm s A + hNorm s B + hNorm s C + hNorm s D := by
  have hAB := (hA.smul (1 / 3 : ℂ)).sub (hB.smul (1 / 3 : ℂ))
  have hABC := hAB.sub (hC.smul (1 / 6 : ℂ))
  refine ⟨hABC.add (hD.smul _), ?_⟩
  have h1 := hNorm_sub_le (hA.smul (1 / 3 : ℂ)) (hB.smul (1 / 3 : ℂ))
  have h2 := hNorm_sub_le hAB (hC.smul (1 / 6 : ℂ))
  have h3 := hNorm_add_le hABC (hD.smul (1 / 3 : ℂ))
  rw [hNorm_smul hA, hNorm_smul hB] at h1
  rw [hNorm_smul hC] at h2
  rw [hNorm_smul hD] at h3
  norm_num only [norm_div, norm_one, Complex.norm_ofNat] at h1 h2 h3
  linarith [hNorm_nonneg s A, hNorm_nonneg s B, hNorm_nonneg s C, hNorm_nonneg s D]

/-- High-output consequence of the retained-endpoint normal form. Only the
 explicit cubic terms and residual forcing remain to be estimated. -/
theorem normal_form_high_bound {F Jb Ja C₁ C₂ I : Fourier} (m : ℕ)
    (hJb : InSobolev 1 Jb) (hJa : InSobolev 1 Ja)
    (hC₁ : InSobolev 0 (highCutoff m C₁)) (hC₂ : InSobolev 0 (highCutoff m C₂)) (hI : InSobolev 0 I)
    (hNF : F = (1 / 3 : ℂ) • (Jb - Ja) - (1 / 3 : ℂ) • C₁ - (1 / 6 : ℂ) • C₂ + (1 / 3 : ℂ) • I) :
    InSobolev 0 (highCutoff m F) ∧
    hNorm 0 (highCutoff m F) ≤ weight (-1) (m : ℤ) * (hNorm 1 Jb + hNorm 1 Ja) +
      hNorm 0 (highCutoff m C₁) + hNorm 0 (highCutoff m C₂) + hNorm 0 I := by
  have hDiff := hJb.sub hJa
  obtain ⟨hA, hAn⟩ := high_cutoff_bound (s := 0) (by norm_num : (0 : ℝ) ≤ 1) hDiff m
  have hD : InSobolev 0 (highCutoff m I) := hI.sub (cutoff_inSobolev hI m)
  have hlin := hNorm_normal_form_sum hA hC₁ hC₂ hD
  have heq : highCutoff m F = (1 / 3 : ℂ) • highCutoff m (Jb - Ja) -
      (1 / 3 : ℂ) • highCutoff m C₁ - (1 / 6 : ℂ) • highCutoff m C₂ + (1 / 3 : ℂ) • highCutoff m I := by
    rw [hNF, highCutoff_add, highCutoff_sub, highCutoff_sub, highCutoff_smul, highCutoff_smul,
      highCutoff_smul, highCutoff_smul]
  rw [heq]
  refine ⟨hlin.1, hlin.2.trans ?_⟩
  have hAb : hNorm 0 (highCutoff m (Jb - Ja)) ≤ weight (-1) (m : ℤ) * (hNorm 1 Jb + hNorm 1 Ja) := by
    calc
      _ ≤ weight (0 - 1) (m : ℤ) * hNorm 1 (Jb - Ja) := hAn
      _ ≤ _ := by norm_num only [zero_sub]; exact mul_le_mul_of_nonneg_left (hNorm_sub_le hJb hJa) (weight_pos _ _).le
  exact add_le_add (add_le_add (add_le_add hAb le_rfl) le_rfl) (highCutoff_hNorm_le hI m)

end KdV
