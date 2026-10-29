import AnalysisOps
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

/-- Complementary projection, used only in the stability proof. -/
def highCutoff (m : ℕ) (f : Fourier) : Fourier := f - cutoff m f

theorem cutoff_frequency_bound {m : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)) : (k : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
  have h := (Finset.mem_Icc.mp hk)
  have hlo : -(m : ℝ) ≤ (k : ℝ) := by exact_mod_cast h.1
  have hhi : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.2
  nlinarith

theorem high_frequency_bound {m : ℕ} {k : ℤ}
    (hk : k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ)) : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hlo | hhi
  · have h : (k : ℝ) < -(m : ℝ) := by exact_mod_cast hlo
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  · have h : (m : ℝ) < (k : ℝ) := by exact_mod_cast hhi
    nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Bernstein bound for the proof projection; it does not change the method. -/
theorem cutoff_gain_bound {s q : ℝ} (hq : 0 ≤ q) {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    InSobolev (s + q) (cutoff m f) ∧
      hNorm (s + q) (cutoff m f) ≤ weight q (m : ℤ) * hNorm s f := by
  have hb (k : ℤ) : ‖weighted (s + q) (cutoff m f) k‖ ≤
      weight q (m : ℤ) * ‖weighted s f k‖ := by
    by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · rw [norm_weighted, norm_weighted]
      simp only [cutoff, if_pos hk]
      have hw : weight q k ≤ weight q (m : ℤ) := by
        unfold weight
        apply Real.rpow_le_rpow (by positivity)
          (by simpa using add_le_add_left (cutoff_frequency_bound hk) 1) (by positivity)
      rw [weight_add]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hw (mul_nonneg (weight_pos s k).le (norm_nonneg (f k)))
    · simp only [weighted, cutoff, if_neg hk, mul_zero, norm_zero]
      exact mul_nonneg (weight_pos q (m : ℤ)).le (norm_nonneg _)
  exact ⟨InSobolev.of_weighted_bound hf (weight_pos q (m : ℤ)).le hb,
    hNorm_le_of_weighted_bound hf (weight_pos q (m : ℤ)).le hb⟩

/-- Negative-order smallness of a high-frequency input, with the exact Japanese weight. -/
theorem high_cutoff_bound {s r : ℝ} (hsr : s ≤ r) {f : Fourier} (hf : InSobolev r f) (m : ℕ) :
    InSobolev s (highCutoff m f) ∧
      hNorm s (highCutoff m f) ≤ weight (s - r) (m : ℤ) * hNorm r f := by
  have hb (k : ℤ) : ‖weighted s (highCutoff m f) k‖ ≤
      weight (s - r) (m : ℤ) * ‖weighted r f k‖ := by
    by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · simp only [highCutoff, weighted, Pi.sub_apply, cutoff, if_pos hk, sub_self, mul_zero, norm_zero]
      exact mul_nonneg (weight_pos (s - r) (m : ℤ)).le (norm_nonneg _)
    · rw [norm_weighted, norm_weighted]
      simp only [highCutoff, Pi.sub_apply, cutoff, if_neg hk, sub_zero]
      have hw : weight (s - r) k ≤ weight (s - r) (m : ℤ) := by
        unfold weight
        apply Real.rpow_le_rpow_of_nonpos (by positivity)
          (by simpa using add_le_add_left (high_frequency_bound hk) 1) (by linarith)
      have hweight : weight s k = weight (s - r) k * weight r k := by
        simpa only [sub_add_cancel] using weight_add (s - r) r k
      rw [hweight]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hw (mul_nonneg (weight_pos r k).le (norm_nonneg (f k)))
  exact ⟨InSobolev.of_weighted_bound hf (weight_pos (s - r) (m : ℤ)).le hb,
    hNorm_le_of_weighted_bound hf (weight_pos (s - r) (m : ℤ)).le hb⟩

theorem cutoff_airy (m : ℕ) (t : ℝ) (f : Fourier) : cutoff m (airy t f) = airy t (cutoff m f) := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, airy, hk]

theorem cutoff_derivative (m : ℕ) (f : Fourier) :
    cutoff m (derivative f) = derivative (cutoff m f) := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, derivative, hk]

end KdV
