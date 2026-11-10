import EndpointEstimates
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem inverseDerivative_B (t : ℝ) (f g : Fourier) :
    inverseDerivative (B t f g) =
      airy (-t) (removeMean (product (airy t f) (airy t g))) := by
  rw [B, inverseDerivative_airy, inverseDerivative_derivative]

/-- The asymmetric product decomposition used in (22). -/
theorem numerical_cross_inverse_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        InSobolev 0 (inverseDerivative (B t f (bilinearStage ((n : ℝ) * τ) t f f))) ∧
        hNorm 0 (inverseDerivative (B t f (bilinearStage ((n : ℝ) * τ) t f f))) ≤
          C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cn, hCn, hnum⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cp, hCp, hprod⟩ := normalized_product_estimate externalProduct hγ.le hγ1
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hC1 : 0 < h1EmbeddingConstant := lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one
  let C : ℝ := 1 + Cp * M * Cn + h1EmbeddingConstant * Cn
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  let F : Fourier := bilinearStage ((n : ℝ) * τ) t f f
  let q : ℝ := τ ^ γ + hNorm 0 (f - w)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hδq : hNorm 0 (f - w) ≤ q := le_add_of_nonneg_left (Real.rpow_nonneg hτ.le γ)
  have hw0 := hw.of_le hγ.le
  have hF1 := (bilinearStage_h1_bound hf hf ((n : ℝ) * τ) t).1
  have hF0 := hF1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have ha1 := (aGamma_parameters hγ hγ1).2.1
  have hFa := hF1.of_le ha1.le
  obtain ⟨hFbound, hDiff, hFaB, hF0B⟩ := hnum τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  obtain ⟨hPw, hPwb⟩ := hprod (airy t w) (airy t F) (airy_inSobolev hw t) (airy_inSobolev hFa t)
  obtain ⟨hPd, hPdb⟩ := l2_h1_product_bound (airy_inSobolev (hf.sub hw0) t) (airy_inSobolev hF1 t)
  have heq : product (airy t f) (airy t F) = product (airy t w) (airy t F) +
      product (airy t (f - w)) (airy t F) := by
    rw [airy_sub, product_sub_left (airy_inSobolev hf t) (airy_inSobolev hw0 t) (airy_inSobolev hF0 t)]
    abel
  have hP : InSobolev 0 (product (airy t f) (airy t F)) := by rw [heq]; exact hPw.add hPd
  rw [inverseDerivative_B]
  refine ⟨airy_inSobolev (removeMean_inSobolev hP) (-t), ?_⟩
  rw [airy_hNorm]
  calc
    _ ≤ hNorm 0 (product (airy t f) (airy t F)) := removeMean_hNorm_le hP
    _ ≤ hNorm 0 (product (airy t w) (airy t F)) + hNorm 0 (product (airy t (f - w)) (airy t F)) := by
      rw [heq]
      exact hNorm_add_le hPw hPd
    _ ≤ Cp * hNorm γ w * hNorm (aGamma γ) F +
        h1EmbeddingConstant * hNorm 0 (f - w) * hNorm 1 F := by
      simpa only [airy_hNorm, aGamma, F] using add_le_add hPwb hPdb
    _ ≤ Cp * M * (Cn * q) + h1EmbeddingConstant * q * Cn :=
      add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hwM hCp.le) hFaB
          (hNorm_nonneg _ _) (mul_nonneg hCp.le hM))
        (mul_le_mul (mul_le_mul_of_nonneg_left hδq hC1.le) hFbound
          (hNorm_nonneg _ _) (mul_nonneg hC1.le hq))
    _ ≤ C * q := by dsimp [C]; nlinarith

theorem inverseDerivative_integral (a b : ℝ) (f : ℝ → Fourier) :
    inverseDerivative (fun k => ∫ t : ℝ in a..b, f t k) =
      (fun k => ∫ t : ℝ in a..b, inverseDerivative (f t) k) := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [inverseDerivative]
  · simp only [inverseDerivative, if_neg hk, intervalIntegral.integral_const_mul]

end KdV
