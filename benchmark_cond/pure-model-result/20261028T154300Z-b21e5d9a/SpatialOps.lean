import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

theorem derivative_product {f g : Fourier} (hf : InSobolev 1 f) (hg : InSobolev 1 g) :
    derivative (product f g) = product (derivative f) g + product f (derivative g) := by
  have hf0 := hf.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hg0 := hg.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hdf : InSobolev 0 (derivative f) := derivative_inSobolev (s := 0) (by simpa using hf)
  have hdg : InSobolev 0 (derivative g) := derivative_inSobolev (s := 0) (by simpa using hg)
  funext k
  change Complex.I * (k : ℂ) * (∑' a : ℤ, f a * g (k - a)) =
    (∑' a : ℤ, (Complex.I * (a : ℂ) * f a) * g (k - a)) +
    ∑' a : ℤ, f a * (Complex.I * ((k - a : ℤ) : ℂ) * g (k - a))
  have hs := (product_summable hdf hg0 k).tsum_add (product_summable hf0 hdg k)
  simp only [derivative] at hs
  rw [← hs, ← tsum_mul_left]
  apply tsum_congr
  intro a
  push_cast
  ring

theorem derivative_square {f : Fourier} (hf : InSobolev 1 f) :
    derivative (product f f) = (2 : ℂ) • product (derivative f) f := by
  rw [derivative_product hf hf, product_comm f (derivative f)]
  module

/-- The product input (17) gives the exact-data square estimate needed in (21). -/
theorem derivative_square_bound (externalProduct : LiWuProductEstimate)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fourier,
      InSobolev (1 + γ) f → InSobolev (aGamma γ) f →
        InSobolev 0 (derivative (product f f)) ∧
        hNorm 0 (derivative (product f f)) ≤ C * hNorm (1 + γ) f * hNorm (aGamma γ) f := by
  obtain ⟨Cp, hCp, hprod⟩ := normalized_product_estimate externalProduct hγ.le hγ1
    (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨2 * Cp, by positivity, ?_⟩
  intro f hf hfa
  have hf1 := hf.of_le (by linarith : (1 : ℝ) ≤ 1 + γ)
  have hfplus : InSobolev (γ + 1) f := by simpa [add_comm] using hf
  have hdf := derivative_inSobolev hfplus
  obtain ⟨hm, hn⟩ := hprod (derivative f) f hdf hfa
  change hNorm 0 (product (derivative f) f) ≤ Cp * hNorm γ (derivative f) * hNorm (aGamma γ) f at hn
  rw [derivative_square hf1]
  refine ⟨hm.smul _, ?_⟩
  rw [hNorm_smul hm]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  calc
    _ ≤ 2 * (Cp * hNorm γ (derivative f) * hNorm (aGamma γ) f) := by linarith
    _ ≤ 2 * (Cp * hNorm (1 + γ) f * hNorm (aGamma γ) f) := by
      have hd : hNorm γ (derivative f) ≤ hNorm (1 + γ) f := by
        simpa only [add_comm] using derivative_hNorm hfplus
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hCp.le) (hNorm_nonneg _ _))
        (by norm_num)
    _ = _ := by ring

theorem B_h1_bound {f g : Fourier} (hf : InSobolev 1 f) (hg : InSobolev 1 g) (t : ℝ) :
    InSobolev 0 (B t f g) ∧
      hNorm 0 (B t f g) ≤ 2 * h1EmbeddingConstant * hNorm 1 f * hNorm 1 g := by
  obtain ⟨hp, hn⟩ := h1_product_bound (airy_inSobolev hf t) (airy_inSobolev hg t)
  have hd : InSobolev 0 (derivative (product (airy t f) (airy t g))) :=
    derivative_inSobolev (s := 0) (by simpa using hp)
  refine ⟨airy_inSobolev hd (-t), ?_⟩
  rw [B, airy_hNorm]
  calc
    _ ≤ hNorm 1 (product (airy t f) (airy t g)) := by
      simpa using derivative_hNorm (s := 0) (by simpa using hp)
    _ ≤ _ := by simpa only [airy_hNorm] using hn

theorem product_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) : product (f - g) h = product f h - product g h := by
  funext k
  unfold product
  simp only [Pi.sub_apply, sub_mul]
  exact (product_summable hf hh k).tsum_sub (product_summable hg hh k)

theorem product_difference_squares {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g) :
    product f f - product g g = product (f - g) (f + g) := by
  rw [product_add_right (hf.sub hg) hf hg, product_sub_left hf hg hf,
    product_sub_left hf hg hg, product_comm g f]
  abel

/-- The low-output estimate needed for (30), without any cutoff in the scheme. -/
theorem B_low_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) (m : ℕ) : hNorm 0 (cutoff m (B t f g)) ≤
      (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * hNorm 0 f * hNorm 0 g := by
  obtain ⟨hp, hn⟩ := negative_product_bound (q := 1) (by norm_num)
    (airy_inSobolev hf t) (airy_inSobolev hg t)
  have hgain := cutoff_gain_bound (s := -1) (q := 2) (by norm_num) hp m
  have hcut : InSobolev (0 + 1) (cutoff m (product (airy t f) (airy t g))) := by
    convert hgain.1 using 1; norm_num
  rw [B, cutoff_airy, cutoff_derivative, airy_hNorm]
  calc
    _ ≤ hNorm 1 (cutoff m (product (airy t f) (airy t g))) := by
      simpa using derivative_hNorm hcut
    _ ≤ weight 2 (m : ℤ) * hNorm (-1) (product (airy t f) (airy t g)) := by
      convert hgain.2 using 1; norm_num
    _ ≤ weight 2 (m : ℤ) * (negativeProductConstant 1 (by norm_num) * hNorm 0 f * hNorm 0 g) := by
      apply mul_le_mul_of_nonneg_left _ (weight_pos 2 (m : ℤ)).le
      simpa only [airy_hNorm] using hn
    _ = _ := by simp [weight, mul_assoc]

end KdV
