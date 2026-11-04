import DynamicTrilinear
import DefectDerivativeEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem continuousOn_memLp_top_Icc {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → E} (hf : ContinuousOn f (Set.Icc a b)) :
    MemLp f ∞ (volume.restrict (Set.Icc a b)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hf.norm).bddAbove
  exact MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) B (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hB ⟨t, ht, rfl⟩)

theorem timeLInfinity_le_of_bound {s A a b : ℝ} (hA : 0 ≤ A)
    (f : ℝ → Sobolev s) (hf : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ A) :
    timeLInfinity a b f ≤ A := by
  have hs := sourceLInfinity_le_of_bound hA a b f (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hf t ht)
  change sourceNormalization * timeLInfinity a b f ≤ sourceNormalization * A at hs
  exact (mul_le_mul_iff_right₀ sourceNormalization_pos).mp hs

def defectL2Path (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) : Sobolev 0 :=
  inclusionMap 0 1 (by norm_num) (defectBundled externalStep τ hτ n t f hfr hfm)

def defectNegativeDerivativePath (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) : Sobolev (-pStar) :=
  inclusionMap (-pStar) 1 (by norm_num [pStar]) (defectDerivativeBundled externalStep τ hτ n t f hfr hfm)

/-- All hypotheses and both time-norm bounds in (24) for the actual defect
path. The weak derivative is proved, and the essential time norms are genuine
`eLpNorm` values on the closed step interval. -/
theorem numerical_defect_time_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      ∀ hτ : 0 < τ, τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        let a := (n : ℝ) * τ
        let b := ((n + 1 : ℕ) : ℝ) * τ
        let Y := defectL2Path externalStep τ hτ n f hfr hfm
        let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
        MemLp Y ∞ (volume.restrict (Set.Icc a b)) ∧
        MemLp dY ∞ (volume.restrict (Set.Icc a b)) ∧
        WeakTimeDerivative a b (fun t => (Y t).val) (fun t => (dY t).val) ∧
        timeXNorm a b Y dY ≤ C * (τ ^ γ + hNorm 0 (f.val - w)) ∧
        timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤
          C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨C0, hC0, hL2⟩ := numerical_defect_l2_bound externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hd⟩ := numerical_defect_derivative_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cn, hCn, hn⟩ := numerical_defect_negative_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨C0 + Cd + Cn, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ
  dsimp only
  let a : ℝ := (n : ℝ) * τ
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  let Y := defectL2Path externalStep τ hτ n f hfr hfm
  let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hYC : Continuous Y := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_defectBundled externalStep τ hτ n f hfr hfm)
  have hdYC : Continuous dY := (inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp
    (continuous_defectDerivativeBundled externalStep τ hτ n f hfr hfm)
  refine ⟨continuousOn_memLp_top_Icc hYC.continuousOn,
    continuousOn_memLp_top_Icc hdYC.continuousOn, ?_, ?_, ?_⟩
  · have hab : a ≤ b := by
      dsimp [a, b]
      push_cast
      nlinarith
    have hw' := (interpolationRemainder_regular externalStep τ hτ n f hfr hfm).weakTimeDerivative hab
    simpa only [Y, dY, defectL2Path, defectNegativeDerivativePath,
      show ∀ s r h (f : Sobolev r), (inclusionMap s r h f).val = f.val from fun _ _ _ _ => rfl,
      defectBundled_val, defectDerivativeBundled_val] using hw'
  · have hYb : timeLInfinity a b Y ≤ C0 * q := timeLInfinity_le_of_bound (mul_nonneg hC0.le hq) Y (by
      intro t ht
      rw [sobolev_norm]
      change hNorm 0 (defectBundled externalStep τ hτ n t f hfr hfm).val ≤ C0 * q
      rw [defectBundled_val]
      exact (hL2 τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2)
    have hdYb : timeLInfinity a b dY ≤ Cd * q := timeLInfinity_le_of_bound (mul_nonneg hCd.le hq) dY (by
      intro t ht
      rw [sobolev_norm]
      change hNorm (-pStar) (defectDerivativeBundled externalStep τ hτ n t f hfr hfm).val ≤ Cd * q
      rw [defectDerivativeBundled_val]
      exact (hd τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2.2)
    change timeLInfinity a b Y + timeLInfinity a b dY ≤ _
    nlinarith
  · have hnb : timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤
        Cn * τ * q := timeLInfinity_le_of_bound (mul_nonneg (mul_nonneg hCn.le hτ.le) hq) _ (by
      intro t ht
      rw [sobolev_norm]
      change hNorm (-pStar) (defectBundled externalStep τ hτ n t f hfr hfm).val ≤ Cn * τ * q
      rw [defectBundled_val]
      exact (hn τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2.2)
    exact hnb.trans (by nlinarith [mul_nonneg hC0.le (mul_nonneg hτ.le hq), mul_nonneg hCd.le (mul_nonneg hτ.le hq)])

end KdV
