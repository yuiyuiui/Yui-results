import SmallFirstTrilinear
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

/-- The forcing term on a whole or partial step. All hypotheses concerning
 the moving third input are explicit internal analytic hypotheses. -/
theorem local_residual_forcing_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      ∀ hτ : 0 < τ, τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ b ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
        ∀ V : ℝ → Sobolev 1, Continuous V → ∀ dV : ℝ → Sobolev (-pStar), ∀ B : ℝ, 1 ≤ B →
        let a := (n : ℝ) * τ
        let V0 := fun t => inclusionMap 0 1 (by norm_num) (V t)
        MemLp V0 ∞ (volume.restrict (Set.Icc a b)) →
        MemLp dV ∞ (volume.restrict (Set.Icc a b)) →
        WeakTimeDerivative a b (fun t => (V0 t).val) (fun t => (dV t).val) →
        timeXNorm a b V0 dV ≤ B →
        (∀ t ∈ Set.Icc a b, hNorm 0 (V t).val ≤ B) →
        InSobolev 0 (fun m => ∫ t : ℝ in a..b, J t (localResidualDerivative τ a t f.val) (V t).val m) ∧
        hNorm 0 (fun m => ∫ t : ℝ in a..b, J t (localResidualDerivative τ a t f.val) (V t).val m) ≤
          C * τ * (τ ^ γ + hNorm 0 (f.val - w)) * B ^ 2 := by
  obtain ⟨Cy, hCy, hy⟩ := numerical_defect_partial_time_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cz, hCz, hz⟩ := numerical_frozen_time_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cp, hCp, hp⟩ := dynamic_small_first_bound externalTrilinear
  obtain ⟨Cw, hCw, hw⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  let N := 1 + Cz + 2 * Cy
  let K := 4 * h1EmbeddingConstant
  have hK : 0 ≤ K := by dsimp [K]; have h := h1EmbeddingConstant_ge_one; positivity
  have hN : 1 ≤ N := by dsimp [N]; linarith
  let D := Cp * Cy * N ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + 2 * D + K * Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hwγ hwm hwM hδ b hb V hVC dV B hB
  dsimp only
  intro hV hdV hwV hXV hVB
  let a : ℝ := (n : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let Y := defectL2Path externalStep τ hτ n f hfr hfm
  let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
  let Z := frozenL2Path a f
  let dZ := frozenNegativeDerivative f
  let V0 := fun t => inclusionMap 0 1 (by norm_num) (V t)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hq2 : q ≤ 2 := by dsimp [q]; linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  have hB0 : 0 ≤ B := by linarith
  have hNB : B ≤ N * B := by nlinarith
  have hNleNB : N ≤ N * B := by nlinarith
  obtain ⟨hY, hdY, hwY, hXY, hNY⟩ := hy τ n hτ hτ1 hnT f hfr hfm w hwγ hwm hwM hδ b hb
  obtain ⟨hZ, hdZ, hwZ, hXZ⟩ := hz τ n hτ hτ1 hnT f hfm w hwγ hwm hwM hδ b hb
  have hNY' : timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤ τ * (Cy * q) := by
    calc
      _ ≤ Cy * τ * q := hNY
      _ = _ := by ring
  have hXZ' : timeXNorm a b Z dZ ≤ N * B := hXZ.trans (by dsimp [N] at *; linarith)
  have hXY' : timeXNorm a b Y dY ≤ N * B := hXY.trans (calc
    _ ≤ 2 * Cy := by nlinarith
    _ ≤ N := by dsimp [N]; linarith
    _ ≤ _ := hNleNB)
  have hXV' : timeXNorm a b V0 dV ≤ N * B := hXV.trans hNB
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
  have hlen : b - a ≤ τ := grid_interval_length n hb
  obtain ⟨hCI, hCIn⟩ := hp a b τ (Cy * q) (N * B) ha hb.1 hlen hτ1 hτ.le (by positivity) (by positivity)
    Y Z V0 dY dZ dV hY hZ hV hdY hdZ hdV hwY hwZ hwV hXY hXZ' hXV' hNY'
  obtain ⟨hCI2, hCI2n⟩ := hp a b τ (Cy * q) (N * B) ha hb.1 hlen hτ1 hτ.le (by positivity) (by positivity)
    Y Y V0 dY dY dV hY hY hV hdY hdY hdV hwY hwY hwV hXY hXY' hXV' hNY'
  have hCIn' : hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) ≤ D * τ * q * B ^ 2 :=
    hCIn.trans_eq (by dsimp [D]; ring)
  have hCI2n' : hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Y t).val) (fun t => (V t).val)) ≤ D * τ * q * B ^ 2 :=
    hCI2n.trans_eq (by dsimp [D]; ring)
  obtain ⟨hW, hWn⟩ := hw τ n hτ hτ1 hnT f hfm w hwγ hwm hwM hδ
  let W : Sobolev 0 := ⟨endpointCorrection τ a f.val, hW⟩
  let JW := fun t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t W (inclusionMap 0 1 (by norm_num) (V t)))
  have hJWC : Continuous JW := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id (continuous_const (y := W))
      ((inclusionMap 0 1 (by norm_num)).continuous.comp hVC))
  have hJWb : ∀ t ∈ Set.Icc a b, ‖JW t‖ ≤ K * (Cw * τ * q) * B := by
    intro t ht
    have hv0 := (V t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    obtain ⟨hj, hjn⟩ := J_h1_bound W.property hv0 t
    rw [sobolev_norm]
    change hNorm 0 (J t W.val (V t).val) ≤ _
    calc
      _ ≤ hNorm 1 (J t W.val (V t).val) := hNorm_mono hj (by norm_num)
      _ ≤ K * hNorm 0 W.val * hNorm 0 (V t).val := hjn
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hWn hK) (hVB t ht)
        (hNorm_nonneg _ _) (by positivity)
  obtain ⟨hI, hIn⟩ := coefficient_integral_bound hJWC hb.1 hJWb
  change InSobolev 0 (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m) at hI
  change hNorm 0 (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m) ≤ K * (Cw * τ * q) * B * (b - a) at hIn
  have hIs : hNorm 0 (((τ⁻¹ : ℝ) : ℂ) • (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m)) ≤
      K * Cw * τ * q * B := by
    rw [hNorm_smul hI, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hτ]
    calc
      _ ≤ τ⁻¹ * (K * (Cw * τ * q) * B * (b - a)) := mul_le_mul_of_nonneg_left hIn (inv_nonneg.mpr hτ.le)
      _ ≤ τ⁻¹ * (K * (Cw * τ * q) * B * τ) := by gcongr
      _ = _ := by field_simp <;> ring
  have hId := residual_forcing_integral_identity externalStep hτ n f hfr hfm V hVC b
  have hvY : (fun t => (Y t).val) = (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val) :=
    funext (fun t => defectBundled_val externalStep τ hτ n t f hfr hfm)
  have hvZ : (fun t => (Z t).val) = (fun t => frozenZ ((n : ℝ) * τ) t f.val) := rfl
  rw [← hvY, ← hvZ] at hId
  rw [hId]
  refine ⟨(hCI.neg.sub (hCI2.smul (1 / 2 : ℂ))).sub (hI.smul _), ?_⟩
  have htriangle := hNorm_sub_le (hCI.neg.sub (hCI2.smul (1 / 2 : ℂ))) (hI.smul (((τ⁻¹ : ℝ) : ℂ)))
  have htriangle2 := hNorm_sub_le hCI.neg (hCI2.smul (1 / 2 : ℂ))
  rw [hNorm_neg, hNorm_smul hCI2, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at htriangle2
  have hBsq : B ≤ B ^ 2 := by nlinarith
  calc
    _ ≤ hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) +
        (1 / 2 : ℝ) * hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Y t).val) (fun t => (V t).val)) +
        hNorm 0 (((τ⁻¹ : ℝ) : ℂ) • (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m)) :=
      htriangle.trans (add_le_add htriangle2 le_rfl)
    _ ≤ D * τ * q * B ^ 2 + (1 / 2 : ℝ) * (D * τ * q * B ^ 2) + K * Cw * τ * q * B :=
      add_le_add (add_le_add hCIn' (mul_le_mul_of_nonneg_left hCI2n' (by norm_num))) hIs
    _ ≤ (1 + 2 * D + K * Cw) * τ * q * B ^ 2 := by
      have hBterm := mul_le_mul_of_nonneg_left hBsq (show 0 ≤ K * Cw * τ * q by positivity)
      have hbase : 0 ≤ τ * q * B ^ 2 := by positivity
      nlinarith

end KdV
