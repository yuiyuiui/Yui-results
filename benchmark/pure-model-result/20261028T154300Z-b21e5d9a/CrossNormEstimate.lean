import StaticCubicEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The `L²` cross-integral bound obtained from identity (23), using the
mixed static trilinear estimate and the sharper boundary estimate. -/
theorem numerical_cross_bound (externalStage : LiWuStageEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (frozenCross ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (frozenCross ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cn, hCn, hnum⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cc, hCc, hcubic⟩ := numerical_static_cubic_bound externalTrilinear hγ hγ1 hM
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 < K := mul_pos (by positivity)
    (lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one)
  let C : ℝ := 1 + K * Cn * (M + 1) / 3 + Cc / 6
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let F : Fourier := bilinearStage a t f.val f.val
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hw0 := hw.of_le hγ.le
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hb := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hb
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hF1 := (bilinearStage_h1_bound hf0 hf0 a t).1
  have hF0 := hF1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hF0b := (hnum τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ).2.2.2
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg n) hτ.le
  have hlength : t - a ≤ τ := by
    have hEnd : ((n + 1 : ℕ) : ℝ) * τ = a + τ := by dsimp [a]; push_cast; ring
    linarith [ht.2]
  obtain ⟨hCI, hCIb⟩ := hcubic τ hτ hτ1 a t ha ht.1 hlength f.val w hf0 hw hwM hδ
  have hJ : InSobolev 0 (J t f.val F) := (J_h1_bound hf0 hF0 t).1.of_le (by norm_num)
  have hJb : hNorm 0 (J t f.val F) ≤ K * Cn * (M + 1) * q := by
    rw [J_comm]
    calc
      _ ≤ K * hNorm 0 (inverseDerivative F) * hNorm 0 f.val := J_inverse_bound hF0 hf0 t
      _ ≤ K * (Cn * q) * (M + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ((inverseDerivative_hNorm_same hF0).trans hF0b) hK.le)
          hfM (hNorm_nonneg _ _) (mul_nonneg hK.le (mul_nonneg hCn.le hq))
      _ = _ := by ring
  rw [frozenCross_normal_form ht.1 f hfm]
  refine ⟨(hJ.smul _).sub (hCI.smul _), ?_⟩
  have hs := hNorm_sub_le (hJ.smul (1 / 3 : ℂ)) (hCI.smul (1 / 6 : ℂ))
  rw [hNorm_smul hJ, hNorm_smul hCI] at hs
  have hn3 : ‖(1 / 3 : ℂ)‖ = (1 / 3 : ℝ) := by norm_num
  have hn6 : ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) := by norm_num
  rw [hn3, hn6] at hs
  change hNorm 0 _ ≤ C * q
  dsimp [C]
  nlinarith

end KdV
