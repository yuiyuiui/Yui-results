import ResidualIdentity
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem InSobolev.neg {s : ℝ} {f : Fourier} (hf : InSobolev s f) : InSobolev s (-f) := by
  simpa only [neg_one_smul] using hf.smul (-1 : ℂ)

set_option maxHeartbeats 800000 in
/-- The negative Sobolev bound for the actual residual derivative in (26). -/
theorem numerical_residual_derivative_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate) (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ∧
          hNorm (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cn, hCn, hstage⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cy, hCy, hdefect⟩ := numerical_defect_l2_bound externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  let Z : ℝ := M + 1 + 2 * Cn
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C : ℝ := 1 + K * Cy * Z + K * Cy * Cy + Cw
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let Y := interpolationRemainder τ a t f.val
  let z := frozenZ a t f.val
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq0 : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hq2 : q ≤ 2 := by dsimp [q]; linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hw0 := hw.of_le hγ.le
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hF0 := (bilinearStage_h1_bound hf0 hf0 a t).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hFb := (hstage τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ).2.2.2
  have hFb' : hNorm 0 (bilinearStage a t f.val f.val) ≤ 2 * Cn :=
    hFb.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq2 hCn.le)
  have hz0 : InSobolev 0 z := hf0.add hF0
  have hzb : hNorm 0 z ≤ Z := by
    have hh := hNorm_add_le hf0 hF0
    change hNorm 0 z ≤ _ at hh
    dsimp [Z]
    linarith only [hh, hfM, hFb']
  obtain ⟨hY0, hYb⟩ := hdefect τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  have hYb' : hNorm 0 Y ≤ 2 * Cy :=
    hYb.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq2 hCy.le)
  obtain ⟨hB1, hB1b⟩ := B_negative_bound hY0 hz0 t
  obtain ⟨hB2, hB2b⟩ := B_negative_bound hY0 hY0 t
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have hp : -pStar ≤ (0 : ℝ) := by norm_num [pStar]
  have hWneg := hW0.of_le hp
  have hSW : hNorm (-pStar) (((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) ≤ Cw * q := by
    rw [hNorm_smul hWneg, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hτ.le)]
    calc
      _ ≤ τ⁻¹ * (Cw * τ * q) := mul_le_mul_of_nonneg_left
        ((hNorm_mono hW0 hp).trans hWb) (inv_nonneg.mpr hτ.le)
      _ = _ := by field_simp [hτ.ne']
  have hB1b' : hNorm (-pStar) (B t Y z) ≤ K * Cy * Z * q := by
    calc
      _ ≤ K * hNorm 0 Y * hNorm 0 z := hB1b
      _ ≤ K * (Cy * q) * Z := mul_le_mul (mul_le_mul_of_nonneg_left hYb hK) hzb
        (hNorm_nonneg _ _) (mul_nonneg hK (mul_nonneg hCy.le hq0))
      _ = _ := by ring
  have hB2b' : hNorm (-pStar) (B t Y Y) ≤ 2 * K * Cy * Cy * q := by
    calc
      _ ≤ K * hNorm 0 Y * hNorm 0 Y := hB2b
      _ ≤ K * (Cy * q) * (2 * Cy) := mul_le_mul (mul_le_mul_of_nonneg_left hYb hK) hYb'
        (hNorm_nonneg _ _) (mul_nonneg hK (mul_nonneg hCy.le hq0))
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · change InSobolev (-pStar) (-B t Y z - (1 / 2 : ℂ) • B t Y Y -
      ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val)
    exact ((hB1.neg).sub (hB2.smul (1 / 2 : ℂ))).sub (hWneg.smul ((τ⁻¹ : ℝ) : ℂ))
  have hh := hNorm_sub_le ((hB1.neg).sub (hB2.smul (1 / 2 : ℂ))) (hWneg.smul ((τ⁻¹ : ℝ) : ℂ))
  have hh' := hNorm_sub_le (hB1.neg) (hB2.smul (1 / 2 : ℂ))
  rw [hNorm_neg, hNorm_smul hB2] at hh'
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf] at hh'
  change hNorm (-pStar) (-B t Y z - (1 / 2 : ℂ) • B t Y Y -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) ≤ C * q
  calc
    _ ≤ hNorm (-pStar) (-B t Y z - (1 / 2 : ℂ) • B t Y Y) +
        hNorm (-pStar) (((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) := hh
    _ ≤ (hNorm (-pStar) (B t Y z) + (1 / 2 : ℝ) * hNorm (-pStar) (B t Y Y)) +
        hNorm (-pStar) (((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) := add_le_add hh' le_rfl
    _ ≤ (K * Cy * Z * q + (1 / 2 : ℝ) * (2 * K * Cy * Cy * q)) + Cw * q :=
      add_le_add (add_le_add hB1b' (mul_le_mul_of_nonneg_left hB2b' (by norm_num))) hSW
    _ ≤ C * q := by dsimp [C]; nlinarith only [hq0]

end KdV
