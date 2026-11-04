import DefectNormEstimate
import NegativeDefectTools
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem interpolationRemainder_inverse_estimate {τ a t A B D : ℝ} {f : Fourier}
    (hc : InSobolev 0 (frozenCross a t f)) (hq : InSobolev 0 (frozenSquare a t f))
    (hw : InSobolev 0 (endpointCorrection τ a f))
    (hfrac : 0 ≤ (t - a) / τ ∧ (t - a) / τ ≤ 1)
    (hC : hNorm 0 (inverseDerivative (frozenCross a t f)) ≤ A)
    (hQ : hNorm 0 (frozenSquare a t f) ≤ B)
    (hW : hNorm 0 (endpointCorrection τ a f) ≤ D) :
    hNorm 0 (inverseDerivative (interpolationRemainder τ a t f)) ≤ A + B + D := by
  have hci := inverseDerivative_inSobolev_same hc
  have hqi := inverseDerivative_inSobolev_same hq
  have hwi := inverseDerivative_inSobolev_same hw
  rw [interpolationRemainder_eq, inverseDerivative_sub, inverseDerivative_add, inverseDerivative_smul]
  have hs := hNorm_sub_le (hci.add hqi) (hwi.smul ((((t - a) / τ) : ℝ) : ℂ))
  have hs' := hNorm_add_le hci hqi
  have hQ' := (inverseDerivative_hNorm_same hq).trans hQ
  have hW' : hNorm 0 (((((t - a) / τ) : ℝ) : ℂ) • inverseDerivative (endpointCorrection τ a f)) ≤ D := by
    rw [hNorm_smul hwi, Complex.norm_real, Real.norm_of_nonneg hfrac.1]
    exact (mul_le_mul_of_nonneg_right hfrac.2 (hNorm_nonneg _ _)).trans
      (by simpa only [one_mul] using (inverseDerivative_hNorm_same hw).trans hW)
  linarith

/-- The small inverse-derivative and negative-norm bounds in (22),(24),
with constants independent of all higher numerical Sobolev norms. -/
theorem numerical_defect_negative_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (inverseDerivative (interpolationRemainder τ ((n : ℝ) * τ) t f.val)) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          hNorm (-pStar) (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cc, hCc, hcross⟩ := numerical_cross_inverse_integral_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cq, hCq, hsquare⟩ := numerical_square_integral_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Cc + Cq + Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  obtain ⟨hIC, hICb⟩ := hcross τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  obtain ⟨hQ, hQb⟩ := hsquare τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have hC : InSobolev 0 (frozenCross ((n : ℝ) * τ) t f.val) := by
    rw [← frozenCrossBundled_val _ _ f]
    exact (frozenCrossBundled _ _ f).property.of_le (by norm_num)
  have hY : InSobolev 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) := by
    rw [interpolationRemainder_eq]
    exact (hC.add hQ).sub (hW0.smul _)
  have hInv := interpolationRemainder_inverse_estimate hC hQ hW0
    (grid_interval_fraction hτ n ht) hICb hQb hWb
  have hInv' : hNorm 0 (inverseDerivative (interpolationRemainder τ ((n : ℝ) * τ) t f.val)) ≤
      (Cc + Cq + Cw) * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
    calc
      _ ≤ _ := hInv
      _ = _ := by ring
  exact ⟨hY, hInv', (negative_hNorm_le_inverse (by norm_num [pStar]) hY
    (interpolationRemainder_meanZero τ _ t hfm)).trans hInv'⟩

end KdV
