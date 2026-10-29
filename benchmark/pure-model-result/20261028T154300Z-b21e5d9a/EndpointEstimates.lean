import InterpolationRegularity
import StageSquareEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Integrating the stage square bound gives the full quadratic correction
bound in (21), with no higher norm in its constant. -/
theorem numerical_square_integral_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (frozenSquare ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (frozenSquare ((n : ℝ) * τ) t f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cs, hCs, hb⟩ := numerical_stage_square_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Cs / 2, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let g : ℝ → Sobolev 0 := fun s => inclusionMap 0 1 (by norm_num)
    (BTwoBundled s (stageTwoBundled a s f f) (stageTwoBundled a s f f))
  have hg : Continuous g := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_square_integrand a f)
  have hB : ∀ s ∈ Set.Icc a t, ‖g s‖ ≤ Cs * q := by
    intro s hs
    have hs' : s ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) :=
      ⟨hs.1, hs.2.trans ht.2⟩
    rw [sobolev_norm]
    change hNorm 0 (B s (bilinearStage a s f.val f.val) (bilinearStage a s f.val f.val)) ≤ Cs * q
    exact (hb τ n s hτ hτ1 hnT hs' f.val w
      (f.property.of_le (by norm_num)) hw hwm hwM hδ).2
  obtain ⟨hI, hIb⟩ := coefficient_integral_bound hg ht.1 hB
  have hQ : InSobolev 0 (frozenSquare a t f.val) := hI.smul (1 / 2 : ℂ)
  refine ⟨hQ, ?_⟩
  have heq : frozenSquare a t f.val = (1 / 2 : ℂ) •
      (fun k => ∫ s : ℝ in a..t, (g s).val k) := rfl
  change hNorm 0 (frozenSquare a t f.val) ≤ (Cs / 2) * τ * q
  rw [heq, hNorm_smul hI]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  have hlength : t - a ≤ τ := by
    have heq : b = a + τ := by dsimp [a, b]; push_cast; ring
    have htb : t ≤ b := ht.2
    linarith
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  calc
    _ ≤ (1 / 2 : ℝ) * (Cs * q * (t - a)) := mul_le_mul_of_nonneg_left hIb (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (Cs * q * τ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlength (mul_nonneg hCs.le hq)) (by norm_num)
    _ = _ := by ring

/-- The complete endpoint correction is small even for a merely `L²`-close
numerical state. The source identity is not an estimate premise here. -/
theorem numerical_endpoint_correction_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
          InSobolev 0 (endpointCorrection τ ((n : ℝ) * τ) f.val) ∧
          hNorm 0 (endpointCorrection τ ((n : ℝ) * τ) f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cq, hCq, hb⟩ := numerical_square_integral_bound externalStage externalProduct hT hγ hγ1 hM
  let Cr := numericalRemainderConstant γ M
  have hCr : 0 < Cr := numericalRemainderConstant_pos γ hM
  refine ⟨Cq + Cr, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have heq : ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ := by push_cast; ring
  have ht : ((n + 1 : ℕ) : ℝ) * τ ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) := by
    rw [heq]
    exact ⟨le_add_of_nonneg_right hτ.le, le_rfl⟩
  obtain ⟨hQ, hQb⟩ := hb τ n hτ hτ1 hnT f w hw hwm hwM hδ _ ht
  rw [heq] at hQ hQb
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hR : InSobolev 0 (remainder τ ((n : ℝ) * τ) f.val f.val f.val) := by
    rw [remainder_eq_interactionRemainder τ _ hfm hfm hfm]
    exact (interactionRemainder_endpoint hτ _ hf0 hf0 hf0).1
  have hRb := numerical_state_estimate hτ hγ.le hγ1 ((n : ℝ) * τ)
    hf0 hw hfm hwm hwM hδ
  refine ⟨hQ.add hR, ?_⟩
  calc
    _ ≤ hNorm 0 (frozenSquare ((n : ℝ) * τ) ((n : ℝ) * τ + τ) f.val) +
        hNorm 0 (remainder τ ((n : ℝ) * τ) f.val f.val f.val) := hNorm_add_le hQ hR
    _ ≤ Cq * τ * (τ ^ γ + hNorm 0 (f.val - w)) + Cr * τ * (τ ^ γ + hNorm 0 (f.val - w)) :=
      add_le_add hQb hRb
    _ = _ := by ring

end KdV
