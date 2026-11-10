import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

theorem weight_one_le_one_add_abs (k : ℤ) : weight 1 k ≤ 1 + |(k : ℝ)| := by
  have h := weight_sq 1 k
  rw [Real.rpow_one] at h
  nlinarith [weight_pos 1 k, abs_nonneg (k : ℝ), sq_abs (k : ℝ)]

/-- A derivative characterization in the actual complete weighted sequence spaces. -/
theorem sobolev_succ_bound {s : ℝ} {f : Fourier} (hf : InSobolev s f)
    (hdf : InSobolev s (derivative f)) :
    InSobolev (s + 1) f ∧ hNorm (s + 1) f ≤ hNorm s f + hNorm s (derivative f) := by
  let F := normWeightedLp s f hf
  let D := normWeightedLp s (derivative f) hdf
  have hb (k : ℤ) : ‖weighted (s + 1) f k‖ ≤ (F + D) k := by
    change ‖weighted (s + 1) f k‖ ≤ ‖weighted s f k‖ + ‖weighted s (derivative f) k‖
    rw [norm_weighted, norm_weighted, norm_weighted, weight_add]
    simp only [derivative, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]
    have h := mul_le_mul_of_nonneg_left (weight_one_le_one_add_abs k)
      (mul_nonneg (weight_pos s k).le (norm_nonneg (f k)))
    simpa only [mul_add, add_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using h
  obtain ⟨hm, hn⟩ := hNorm_le_lp_envelope (F + D) hb
  refine ⟨hm, hn.trans ?_⟩
  calc
    _ ≤ ‖F‖ + ‖D‖ := norm_add_le F D
    _ = _ := by rw [norm_normWeightedLp, norm_normWeightedLp]

theorem inSobolev_succ_iff {s : ℝ} {f : Fourier} :
    InSobolev (s + 1) f ↔ InSobolev s f ∧ InSobolev s (derivative f) := by
  constructor
  · intro hf
    exact ⟨hf.of_le (by linarith), derivative_inSobolev hf⟩
  · rintro ⟨hf, hdf⟩
    exact (sobolev_succ_bound hf hdf).1

theorem inverseDerivative_inSobolev_same {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    InSobolev s (inverseDerivative f) := by
  apply Memℓp.mono' hf
  intro k
  rw [norm_weighted, norm_weighted]
  exact mul_le_mul_of_nonneg_left (inverseDerivative_coeff_norm_le f k) (weight_pos s k).le

theorem inverseDerivative_hNorm_same {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    hNorm s (inverseDerivative f) ≤ hNorm s f := by
  simpa only [one_mul] using hNorm_le_of_weighted_bound hf (by norm_num : (0 : ℝ) ≤ 1)
    (fun k => by
      rw [norm_weighted, norm_weighted, one_mul]
      exact mul_le_mul_of_nonneg_left (inverseDerivative_coeff_norm_le f k) (weight_pos s k).le)

/-- All positive integer Sobolev orders are convolution algebras; no Fourier
support restriction is used in this induction. -/
theorem integer_product_inSobolev (n : ℕ) {f g : Fourier}
    (hf : InSobolev ((n + 1 : ℕ) : ℝ) f) (hg : InSobolev ((n + 1 : ℕ) : ℝ) g) :
    InSobolev ((n + 1 : ℕ) : ℝ) (product f g) := by
  induction n generalizing f g with
  | zero =>
    norm_num at hf hg ⊢
    exact (h1_product_bound hf hg).1
  | succ n ih =>
    have hfp : InSobolev (((n + 1 : ℕ) : ℝ) + 1) f := by
      simpa only [Nat.cast_add, Nat.cast_one] using hf
    have hgp : InSobolev (((n + 1 : ℕ) : ℝ) + 1) g := by
      simpa only [Nat.cast_add, Nat.cast_one] using hg
    obtain ⟨hfl, hfd⟩ := inSobolev_succ_iff.mp hfp
    obtain ⟨hgl, hgd⟩ := inSobolev_succ_iff.mp hgp
    have hf1 : InSobolev 1 f := hfl.of_le (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
    have hg1 : InSobolev 1 g := hgl.of_le (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
    have hder : InSobolev ((n + 1 : ℕ) : ℝ) (derivative (product f g)) := by
      rw [derivative_product hf1 hg1]
      exact (ih hfd hgl).add (ih hfl hgd)
    have hp := (inSobolev_succ_iff).mpr ⟨ih hfl hgl, hder⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hp

/-- An explicit bound supplies continuity of multiplication at order two. -/
theorem h2_product_bound {f g : Fourier} (hf : InSobolev 2 f) (hg : InSobolev 2 g) :
    InSobolev 2 (product f g) ∧
      hNorm 2 (product f g) ≤ 6 * h1EmbeddingConstant * hNorm 2 f * hNorm 2 g := by
  have hf1 := hf.of_le (by norm_num : (1 : ℝ) ≤ 2)
  have hg1 := hg.of_le (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨hp, hpb⟩ := h1_product_bound hf1 hg1
  obtain ⟨hdp, hdpb⟩ := B_h1_of_h2 hf hg 0
  have heq : B 0 f g = derivative (product f g) := by simp [B]
  rw [heq] at hdp hdpb
  have hb := sobolev_succ_bound hp hdp
  norm_num at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 f * hNorm 1 g +
        (4 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g := add_le_add hpb hdpb
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g +
        (4 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g := by
      have hC : 0 ≤ 2 * h1EmbeddingConstant := by linarith [h1EmbeddingConstant_ge_one]
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left (hNorm_mono hf (by norm_num : (1 : ℝ) ≤ 2)) hC)
          (hNorm_mono hg (by norm_num : (1 : ℝ) ≤ 2)) (hNorm_nonneg 1 _)
          (mul_nonneg hC (hNorm_nonneg 2 _))) le_rfl
    _ = _ := by ring

end KdV
