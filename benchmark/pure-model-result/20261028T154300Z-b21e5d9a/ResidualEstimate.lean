import ResidualBilinearEstimates
import ResidualNegativeEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Both estimates (26), for the residual of the specified full unfiltered
update. Constants precede every state, step count, and grid point. -/
theorem numerical_residual_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (localResidual τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (localResidual τ ((n : ℝ) * τ) t f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          InSobolev (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ∧
          hNorm (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cb, hCb, hbil⟩ := numerical_residual_bilinear_bounds externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hder⟩ := numerical_residual_derivative_bound externalStage externalProduct externalTrilinear
    hT hγ hγ1 hM
  let C : ℝ := 2 * Cb + Cw + Cd
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let IC : Fourier := fun k => ∫ s : ℝ in a..t,
    B s (interpolationRemainder τ a s f.val) (frozenZ a s f.val) k
  let IQ : Fourier := fun k => ∫ s : ℝ in a..t,
    B s (interpolationRemainder τ a s f.val) (interpolationRemainder τ a s f.val) k
  let rfrac : ℝ := (t - a) / τ
  obtain ⟨hIC, hICb, hIQ, hIQb⟩ := hbil τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  obtain ⟨hD, hDb⟩ := hder τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  have hfrac := grid_interval_fraction hτ n ht
  have hq0 : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hScaled : hNorm 0 ((rfrac : ℂ) • endpointCorrection τ a f.val) ≤ Cw * τ * q := by
    rw [hNorm_smul hW0, Complex.norm_real, Real.norm_of_nonneg hfrac.1]
    exact (mul_le_mul_of_nonneg_right hfrac.2 (hNorm_nonneg _ _)).trans
      (by simpa only [one_mul] using hWb)
  have hR : InSobolev 0 (localResidual τ a t f.val) := by
    change InSobolev 0 (-IC - (1 / 2 : ℂ) • IQ - (rfrac : ℂ) • endpointCorrection τ a f.val)
    exact ((hIC.neg).sub (hIQ.smul (1 / 2 : ℂ))).sub (hW0.smul (rfrac : ℂ))
  refine ⟨hR, ?_, hD, hDb.trans ?_⟩
  · have hh := hNorm_sub_le ((hIC.neg).sub (hIQ.smul (1 / 2 : ℂ))) (hW0.smul (rfrac : ℂ))
    have hh' := hNorm_sub_le (hIC.neg) (hIQ.smul (1 / 2 : ℂ))
    rw [hNorm_neg, hNorm_smul hIQ] at hh'
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf] at hh'
    change hNorm 0 (-IC - (1 / 2 : ℂ) • IQ - (rfrac : ℂ) • endpointCorrection τ a f.val) ≤ C * τ * q
    have hpos := mul_nonneg hCb.le (mul_nonneg hτ.le hq0)
    have hposd := mul_nonneg hCd.le (mul_nonneg hτ.le hq0)
    calc
      _ ≤ hNorm 0 (-IC - (1 / 2 : ℂ) • IQ) +
          hNorm 0 ((rfrac : ℂ) • endpointCorrection τ a f.val) := hh
      _ ≤ (hNorm 0 IC + (1 / 2 : ℝ) * hNorm 0 IQ) +
          hNorm 0 ((rfrac : ℂ) • endpointCorrection τ a f.val) := add_le_add hh' le_rfl
      _ ≤ (Cb * τ * q + (1 / 2 : ℝ) * (Cb * τ * q)) + Cw * τ * q :=
        add_le_add (add_le_add hICb (mul_le_mul_of_nonneg_left hIQb (by norm_num))) hScaled
      _ ≤ C * τ * q := by dsimp [C]; nlinarith only [hpos, hposd]
  · have hCdC : Cd ≤ C := by dsimp [C]; linarith
    exact mul_le_mul_of_nonneg_right hCdC hq0

end KdV
