import PathIntervalTools
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- An internal normal-form estimate retaining the endpoint and integrating
the actual differentiated path. Its hypotheses will be supplied by (22)-(24). -/
theorem integral_B_self_bound {a b A Ad M : ℝ} (hab : a ≤ b)
    (hA : 0 ≤ A) (hAd : 0 ≤ Ad) (_hM : 0 ≤ M)
    (Y dY : ℝ → Sobolev 1) (hYC : Continuous Y) (hdYC : Continuous dY)
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (Y r).val k) ((dY t).val k) t)
    (hm : ∀ t ∈ Set.Icc a b, MeanZero (Y t).val) (hleft : (Y a).val = 0)
    (hY : ∀ t ∈ Set.Icc a b, hNorm 0 (Y t).val ≤ M)
    (hIb : hNorm 0 (inverseDerivative (Y b).val) ≤ A)
    (hId : ∀ t ∈ Set.Icc a b, hNorm 0 (inverseDerivative (dY t).val) ≤ Ad) :
    InSobolev 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) ∧
    hNorm 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * A * M / 3 +
        (2 / 3 : ℝ) * (Real.sqrt 2 * h1EmbeddingConstant) * Ad * M * (b - a) := by
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one h1EmbeddingConstant_ge_one)
  let g : ℝ → Sobolev 0 := fun t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t (inclusionMap 0 1 (by norm_num) (dY t)) (inclusionMap 0 1 (by norm_num) (Y t)))
  have hg : Continuous g := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id ((inclusionMap 0 1 (by norm_num)).continuous.comp hdYC)
      ((inclusionMap 0 1 (by norm_num)).continuous.comp hYC))
  have hgb : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ K * Ad * M := by
    intro t ht
    rw [sobolev_norm]
    change hNorm 0 (J t (dY t).val (Y t).val) ≤ _
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (dY t).val) * hNorm 0 (Y t).val :=
        J_inverse_bound ((dY t).property.of_le (by norm_num)) ((Y t).property.of_le (by norm_num)) t
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hId t ht) hK) (hY t ht)
        (hNorm_nonneg _ _) (mul_nonneg hK hAd)
  obtain ⟨hI, hIn⟩ := coefficient_integral_bound hg hab hgb
  have hJ : InSobolev 0 (J b (Y b).val (Y b).val) :=
    (J_h1_bound ((Y b).property.of_le (by norm_num)) ((Y b).property.of_le (by norm_num)) b).1.of_le (by norm_num)
  have hJn : hNorm 0 (J b (Y b).val (Y b).val) ≤ K * A * M := by
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (Y b).val) * hNorm 0 (Y b).val :=
        J_inverse_bound ((Y b).property.of_le (by norm_num)) ((Y b).property.of_le (by norm_num)) b
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hIb hK) (hY b ⟨hab, le_rfl⟩)
        (hNorm_nonneg _ _) (mul_nonneg hK hA)
  have hreg := regularFourierPath_of_bundled hYC hdYC hd
  have heq : (fun k => ∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) =
      (1 / 3 : ℂ) • J b (Y b).val (Y b).val -
        (2 / 3 : ℂ) • (fun k => ∫ t : ℝ in a..b, (g t).val k) := by
    funext k
    have hn := variable_normal_form hab hreg hreg hm hm k
    have hfun : (fun t : ℝ => J t (dY t).val (Y t).val k + J t (Y t).val (dY t).val k) =
        (fun t : ℝ => (2 : ℂ) * J t (dY t).val (Y t).val k) := by
      funext t
      rw [J_comm t (Y t).val (dY t).val]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hleft, J_zero_left] at hn
    simp only [Pi.zero_apply, sub_zero] at hn
    change (∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) =
      (1 / 3 : ℂ) * J b (Y b).val (Y b).val k -
        (2 / 3 : ℂ) * (∫ t : ℝ in a..b, J t (dY t).val (Y t).val k)
    linear_combination hn
  rw [heq]
  refine ⟨(hJ.smul _).sub (hI.smul _), ?_⟩
  have hs := hNorm_sub_le (hJ.smul (1 / 3 : ℂ)) (hI.smul (2 / 3 : ℂ))
  rw [hNorm_smul hJ, hNorm_smul hI] at hs
  have hn3 : ‖(1 / 3 : ℂ)‖ = (1 / 3 : ℝ) := by norm_num
  have hn23 : ‖(2 / 3 : ℂ)‖ = (2 / 3 : ℝ) := by norm_num
  rw [hn3, hn23] at hs
  change hNorm 0 _ ≤ K * A * M / 3 + (2 / 3 : ℝ) * K * Ad * M * (b - a)
  linarith

end KdV
