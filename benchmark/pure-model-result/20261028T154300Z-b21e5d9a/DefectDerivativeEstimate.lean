import DefectDerivative
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The derivative bound in (22), hence the negative derivative norm needed
for (24). Every estimate is derived from the actual interpolation formula. -/
theorem numerical_defect_derivative_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (inverseDerivative (interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val)) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          hNorm (-pStar) (interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Ci, hCi, hcross⟩ := numerical_cross_inverse_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cb, hCb, hquad⟩ := numerical_stage_square_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Ci + Cb / 2 + Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let F : Fourier := bilinearStage a t f.val f.val
  let W : Fourier := endpointCorrection τ a f.val
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  obtain ⟨hIC, hICb⟩ := hcross τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ
  obtain ⟨hB, hBb⟩ := hquad τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have hC0 : InSobolev 0 (B t f.val F) :=
    (B_h1_of_h2 f.property (stageTwoBundled a t f f).property t).1.of_le (by norm_num)
  have hY : InSobolev 0 (interpolationRemainderDerivative τ a t f.val) :=
    (hC0.add (hB.smul (1 / 2 : ℂ))).sub (hW0.smul _)
  have hIB := inverseDerivative_inSobolev_same hB
  have hIW := inverseDerivative_inSobolev_same hW0
  have hSW : hNorm 0 (((τ⁻¹ : ℝ) : ℂ) • inverseDerivative W) ≤ Cw * q := by
    rw [hNorm_smul hIW, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hτ.le)]
    calc
      _ ≤ τ⁻¹ * (Cw * τ * q) :=
        mul_le_mul_of_nonneg_left ((inverseDerivative_hNorm_same hW0).trans hWb) (inv_nonneg.mpr hτ.le)
      _ = _ := by field_simp [hτ.ne']
  have hSB : hNorm 0 ((1 / 2 : ℂ) • inverseDerivative (B t F F)) ≤ (Cb / 2) * q := by
    rw [hNorm_smul hIB]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    have hh := (inverseDerivative_hNorm_same hB).trans hBb
    linarith
  have hInv : hNorm 0 (inverseDerivative (interpolationRemainderDerivative τ a t f.val)) ≤
      (Ci + Cb / 2 + Cw) * q := by
    rw [interpolationRemainderDerivative, inverseDerivative_sub, inverseDerivative_add,
      inverseDerivative_smul, inverseDerivative_smul]
    have hnorm := hNorm_sub_le (hIC.add (hIB.smul (1 / 2 : ℂ))) (hIW.smul ((τ⁻¹ : ℝ) : ℂ))
    have hnorm' := hNorm_add_le hIC (hIB.smul (1 / 2 : ℂ))
    linarith
  exact ⟨hY, hInv, (negative_hNorm_le_inverse (by norm_num [pStar]) hY
    (interpolationRemainderDerivative_meanZero τ a t f.val)).trans hInv⟩

end KdV
