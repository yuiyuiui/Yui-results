import CrossNormEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem interpolationRemainder_eq (τ a t : ℝ) (f : Fourier) :
    interpolationRemainder τ a t f = frozenCross a t f + frozenSquare a t f -
      (((t - a) / τ : ℝ) : ℂ) • endpointCorrection τ a f := by
  unfold interpolationRemainder localInterpolation
  abel

theorem grid_interval_length {τ : ℝ} (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)) :
    t - (n : ℝ) * τ ≤ τ := by
  have hEnd : ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ := by push_cast; ring
  linarith [ht.2]

theorem grid_interval_fraction {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)) :
    0 ≤ (t - (n : ℝ) * τ) / τ ∧ (t - (n : ℝ) * τ) / τ ≤ 1 :=
  ⟨div_nonneg (sub_nonneg.mpr ht.1) hτ.le, (div_le_one hτ).mpr (grid_interval_length n ht)⟩

/-- The strong defect norm (23), with constants before the numerical input. -/
theorem numerical_defect_l2_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate) (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cc, hCc, hcross⟩ := numerical_cross_bound externalStage externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cq, hCq, hsquare⟩ := numerical_square_integral_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Cc + Cq + Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  obtain ⟨hC, hCb⟩ := hcross τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  obtain ⟨hQ, hQb⟩ := hsquare τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let rfrac : ℝ := (t - (n : ℝ) * τ) / τ
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hrfrac := grid_interval_fraction hτ n ht
  have hscaled : hNorm 0 ((rfrac : ℂ) • endpointCorrection τ ((n : ℝ) * τ) f.val) ≤ Cw * τ * q := by
    rw [hNorm_smul hW0, Complex.norm_real, Real.norm_of_nonneg hrfrac.1]
    exact (mul_le_mul_of_nonneg_right hrfrac.2 (hNorm_nonneg _ _)).trans (by simpa only [one_mul] using hWb)
  rw [interpolationRemainder_eq]
  refine ⟨(hC.add hQ).sub (hW0.smul _), ?_⟩
  have hb := hNorm_sub_le (hC.add hQ) (hW0.smul (rfrac : ℂ))
  have hb' := hNorm_add_le hC hQ
  change hNorm 0 _ ≤ (Cc + Cq + Cw) * q
  have hQb' : hNorm 0 (frozenSquare ((n : ℝ) * τ) t f.val) ≤ Cq * q :=
    hQb.trans (by nlinarith [mul_nonneg hCq.le hq])
  have hscaled' : hNorm 0 ((rfrac : ℂ) • endpointCorrection τ ((n : ℝ) * τ) f.val) ≤ Cw * q :=
    hscaled.trans (by nlinarith [mul_nonneg hCw.le hq])
  linarith

/-- The inverse-derivative cross-integral bound in (22), proved by commuting
the coefficient multiplier with the Bochner integral. -/
theorem numerical_cross_inverse_integral_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (inverseDerivative (frozenCross ((n : ℝ) * τ) t f.val)) ∧
          hNorm 0 (inverseDerivative (frozenCross ((n : ℝ) * τ) t f.val)) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨C, hC, hb⟩ := numerical_cross_inverse_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨C, hC, ?_⟩
  intro τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let g : ℝ → Sobolev 0 := fun s => inverseDerivativeSameMap 0
    (inclusionMap 0 1 (by norm_num) (BTwoBundled s f (stageTwoBundled a s f f)))
  have hg : Continuous g := (inverseDerivativeSameMap 0).continuous.comp
    ((inclusionMap 0 1 (by norm_num)).continuous.comp (continuous_cross_integrand a f))
  have hB : ∀ s ∈ Set.Icc a t, ‖g s‖ ≤ C * q := by
    intro s hs
    rw [sobolev_norm]
    exact (hb τ n s hτ hτ1 hnT ⟨hs.1, hs.2.trans ht.2⟩ f.val w
      (f.property.of_le (by norm_num)) hw hwm hwM hδ).2
  obtain ⟨hI, hIb⟩ := coefficient_integral_bound hg ht.1 hB
  have heq : inverseDerivative (frozenCross a t f.val) =
      fun k => ∫ s : ℝ in a..t, (g s).val k :=
    inverseDerivative_integral a t (fun s => B s f.val (bilinearStage a s f.val f.val))
  rw [heq]
  refine ⟨hI, hIb.trans ?_⟩
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  calc
    C * q * (t - a) ≤ C * q * τ := mul_le_mul_of_nonneg_left (grid_interval_length n ht) (mul_nonneg hC.le hq)
    _ = _ := by ring

end KdV
