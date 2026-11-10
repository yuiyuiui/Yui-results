import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

theorem integer_product_bound (n : ℕ) {f g : Fourier}
    (hf : InSobolev ((n + 1 : ℕ) : ℝ) f) (hg : InSobolev ((n + 1 : ℕ) : ℝ) g) :
    hNorm ((n + 1 : ℕ) : ℝ) (product f g) ≤
      ((3 : ℝ) ^ n * (2 * h1EmbeddingConstant)) * hNorm ((n + 1 : ℕ) : ℝ) f * hNorm ((n + 1 : ℕ) : ℝ) g := by
  induction n generalizing f g with
  | zero => simpa using (h1_product_bound (by simpa using hf) (by simpa using hg)).2
  | succ n ih =>
    let s : ℝ := ((n + 1 : ℕ) : ℝ)
    let K : ℝ := (3 : ℝ) ^ n * (2 * h1EmbeddingConstant)
    have hK : 0 ≤ K := by dsimp [K]; have hh := h1EmbeddingConstant_ge_one; positivity
    have hs1 : 1 ≤ s := by dsimp [s]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hfp : InSobolev (s + 1) f := by simpa only [s, Nat.cast_add, Nat.cast_one] using hf
    have hgp : InSobolev (s + 1) g := by simpa only [s, Nat.cast_add, Nat.cast_one] using hg
    obtain ⟨hfl, hfd⟩ := inSobolev_succ_iff.mp hfp
    obtain ⟨hgl, hgd⟩ := inSobolev_succ_iff.mp hgp
    have hf1 := hfl.of_le hs1
    have hg1 := hgl.of_le hs1
    have hp := integer_product_inSobolev n hfl hgl
    have hd1 := integer_product_inSobolev n hfd hgl
    have hd2 := integer_product_inSobolev n hfl hgd
    have hdp : InSobolev s (derivative (product f g)) := by
      rw [derivative_product hf1 hg1]
      exact hd1.add hd2
    have hl := ih hfl hgl
    have hd1n := ih hfd hgl
    have hd2n := ih hfl hgd
    have hfpn := derivative_hNorm hfp
    have hgpn := derivative_hNorm hgp
    have hfln := hNorm_mono hfp (by linarith : s ≤ s + 1)
    have hgln := hNorm_mono hgp (by linarith : s ≤ s + 1)
    have hfnon := hNorm_nonneg (s + 1) f
    have hgnon := hNorm_nonneg (s + 1) g
    have hln : hNorm s (product f g) ≤ K * hNorm (s + 1) f * hNorm (s + 1) g := hl.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hfln hK) hgln (hNorm_nonneg _ _) (mul_nonneg hK hfnon))
    have hd1n' : hNorm s (product (derivative f) g) ≤ K * hNorm (s + 1) f * hNorm (s + 1) g := hd1n.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hfpn hK) hgln (hNorm_nonneg _ _) (mul_nonneg hK hfnon))
    have hd2n' : hNorm s (product f (derivative g)) ≤ K * hNorm (s + 1) f * hNorm (s + 1) g := hd2n.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hfln hK) hgpn (hNorm_nonneg _ _) (mul_nonneg hK hfnon))
    have hd : hNorm s (derivative (product f g)) ≤ 2 * K * hNorm (s + 1) f * hNorm (s + 1) g := by
      rw [derivative_product hf1 hg1]
      exact (hNorm_add_le hd1 hd2).trans (by linarith)
    have hn := (sobolev_succ_bound hp hdp).2
    have hsBound : hNorm (s + 1) (product f g) ≤ 3 * K * hNorm (s + 1) f * hNorm (s + 1) g := by linarith
    simpa only [s, K, Nat.cast_add, Nat.cast_one, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hsBound

end KdV
