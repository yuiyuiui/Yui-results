import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem cutoff_coefficient_integral (m : ℕ) (f : ℝ → Fourier) (a b : ℝ) :
    cutoff m (fun k => ∫ t : ℝ in a..b, f t k) =
      (fun k => ∫ t : ℝ in a..b, cutoff m (f t) k) := by
  funext k
  unfold cutoff
  split_ifs <;> simp

theorem integrated_B_low_bound {a b E G : ℝ} (hab : a ≤ b) (hE : 0 ≤ E) (_hG : 0 ≤ G)
    (f g : ℝ → Sobolev 1) (hf : Continuous f) (hg : Continuous g)
    (hfn : ∀ t ∈ Set.Icc a b, hNorm 0 (f t).val ≤ E)
    (hgn : ∀ t ∈ Set.Icc a b, hNorm 0 (g t).val ≤ G) (m : ℕ) :
    InSobolev 0 (cutoff m (fun k => ∫ t : ℝ in a..b, B t (f t).val (g t).val k)) ∧
    hNorm 0 (cutoff m (fun k => ∫ t : ℝ in a..b, B t (f t).val (g t).val k)) ≤
      (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * E * G * (b - a) := by
  let F := fun t => cutoffMap 0 m (BOneBundled t (f t) (g t))
  have hC : Continuous F := (cutoffMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hf hg)
  have hK : 0 ≤ negativeProductConstant 1 (by norm_num) := norm_nonneg _
  have hbound : ∀ t ∈ Set.Icc a b, ‖F t‖ ≤ (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * E * G := by
    intro t ht
    rw [sobolev_norm]
    change hNorm 0 (cutoff m (B t (f t).val (g t).val)) ≤ _
    calc
      _ ≤ (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * hNorm 0 (f t).val * hNorm 0 (g t).val :=
        B_low_bound ((f t).property.of_le (by norm_num)) ((g t).property.of_le (by norm_num)) t m
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hfn t ht) (by positivity)) (hgn t ht)
        (hNorm_nonneg _ _) (by positivity)
  have hb := coefficient_integral_bound hC hab hbound
  rwa [cutoff_coefficient_integral]

theorem hNorm_low_high_le {s : ℝ} {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    hNorm s f ≤ hNorm s (cutoff m f) + hNorm s (highCutoff m f) := by
  have hh := hNorm_add_le (cutoff_inSobolev hf m) (hf.sub (cutoff_inSobolev hf m))
  have heq : cutoff m f + (f - cutoff m f) = f := by abel
  rw [heq] at hh
  exact hh

theorem high_J_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g) (t : ℝ) (m : ℕ) :
    InSobolev 0 (highCutoff m (J t f g)) ∧
    hNorm 0 (highCutoff m (J t f g)) ≤ weight (-1) (m : ℤ) * (4 * h1EmbeddingConstant * hNorm 0 f * hNorm 0 g) := by
  obtain ⟨hJ, hJn⟩ := J_h1_bound hf hg t
  obtain ⟨hm, hmn⟩ := high_cutoff_bound (s := 0) (by norm_num : (0 : ℝ) ≤ 1) hJ m
  refine ⟨hm, ?_⟩
  calc
    _ ≤ weight (0 - 1) (m : ℤ) * hNorm 1 (J t f g) := hmn
    _ ≤ _ := by norm_num only [zero_sub]; exact mul_le_mul_of_nonneg_left hJn (weight_pos _ _).le

end KdV
