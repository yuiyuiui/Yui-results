import GlobalInterpolation
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def localResidualBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 0 :=
  -(∫ s : ℝ in (n : ℝ) * τ..t,
      BOneBundled s (defectBundled externalStep τ hτ n s f hfr hfm) (frozenZBundled ((n : ℝ) * τ) s f)) -
    (1 / 2 : ℂ) • (∫ s : ℝ in (n : ℝ) * τ..t,
      BOneBundled s (defectBundled externalStep τ hτ n s f hfr hfm)
        (defectBundled externalStep τ hτ n s f hfr hfm)) -
    ((((t - (n : ℝ) * τ) / τ) : ℝ) : ℂ) •
      inclusionMap 0 1 (by norm_num) (endpointCorrectionBundled externalStep τ hτ n f hfr hfm)

theorem localResidualBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (localResidualBundled externalStep τ hτ n t f hfr hfm).val =
      localResidual τ ((n : ℝ) * τ) t f.val := by
  obtain ⟨hC, hQ⟩ := continuous_residual_integrands externalStep τ hτ n f hfr hfm
  unfold localResidualBundled
  change -(∫ s : ℝ in (n : ℝ) * τ..t, BOneBundled s _ _).val -
    (1 / 2 : ℂ) • (∫ s : ℝ in (n : ℝ) * τ..t, BOneBundled s _ _).val - _ = _
  rw [sobolev_integral_val (hC.intervalIntegrable _ _), sobolev_integral_val (hQ.intervalIntegrable _ _)]
  simp only [BOneBundled_val, defectBundled_val, frozenZBundled_val]
  rfl

theorem continuous_localResidualBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => localResidualBundled externalStep τ hτ n t f hfr hfm) := by
  obtain ⟨hC, hQ⟩ := continuous_residual_integrands externalStep τ hτ n f hfr hfm
  have hCI := (intervalIntegral.differentiable_integral_of_continuous (a := (n : ℝ) * τ) hC).continuous
  have hQI := (intervalIntegral.differentiable_integral_of_continuous (a := (n : ℝ) * τ) hQ).continuous
  unfold localResidualBundled
  fun_prop

theorem localResidualBundled_left (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    localResidualBundled externalStep τ hτ n ((n : ℝ) * τ) f hfr hfm = 0 := by
  apply Sobolev.ext
  rw [localResidualBundled_val, localResidual_left]
  rfl

def residualPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) : Sobolev 0 :=
  localResidualBundled externalStep τ hτ n t (twistedNumericalBundled τ f n)
    (twistedNumericalBundled_real τ hfr n) (twistedNumericalBundled_meanZero τ hfm n)

theorem residualPiece_val (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) :
    (residualPiece externalStep τ hτ f hfr hfm n t).val =
      localResidual τ ((n : ℝ) * τ) t (twistedNumericalBundled τ f n).val :=
  localResidualBundled_val externalStep τ hτ n t _ _ _

theorem residualPiece_left (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    residualPiece externalStep τ hτ f hfr hfm n ((n : ℝ) * τ) = 0 :=
  localResidualBundled_left externalStep τ hτ n _ _ _

theorem continuous_residualPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    Continuous (residualPiece externalStep τ hτ f hfr hfm n) :=
  continuous_localResidualBundled externalStep τ hτ n _ _ _

def cumulativeResidualPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) : Sobolev 0 :=
  (∑ j ∈ Finset.range n, residualPiece externalStep τ hτ f hfr hfm j (((j + 1 : ℕ) : ℝ) * τ)) +
    residualPiece externalStep τ hτ f hfr hfm n t

theorem cumulativeResidualPiece_glue (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    cumulativeResidualPiece externalStep τ hτ f hfr hfm n (((n + 1 : ℕ) : ℝ) * τ) =
      cumulativeResidualPiece externalStep τ hτ f hfr hfm (n + 1) (((n + 1 : ℕ) : ℝ) * τ) := by
  simp only [cumulativeResidualPiece, residualPiece_left, add_zero, Finset.sum_range_succ]

def globalResidual (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) : ℝ → Sobolev 0 :=
  concatenate τ (cumulativeResidualPiece externalStep τ hτ f hfr hfm) k

theorem continuous_globalResidual (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) :
    Continuous (globalResidual externalStep τ hτ f hfr hfm k) := by
  apply continuous_concatenate hτ.le
  · intro j
    exact continuous_const.add (continuous_residualPiece externalStep τ hτ f hfr hfm j)
  · exact cumulativeResidualPiece_glue externalStep τ hτ f hfr hfm

theorem globalResidual_on_step (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    globalResidual externalStep τ hτ f hfr hfm k t =
      cumulativeResidualPiece externalStep τ hτ f hfr hfm j t :=
  concatenate_on_step hτ.le _ (cumulativeResidualPiece_glue externalStep τ hτ f hfr hfm) hjk ht

theorem globalResidual_step_increment (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    globalResidual externalStep τ hτ f hfr hfm k t -
      globalResidual externalStep τ hτ f hfr hfm k ((j : ℝ) * τ) =
        residualPiece externalStep τ hτ f hfr hfm j t := by
  rw [globalResidual_on_step externalStep τ hτ f hfr hfm hjk ht,
    globalResidual_on_step externalStep τ hτ f hfr hfm hjk
      (by constructor; rfl; push_cast; nlinarith)]
  simp only [cumulativeResidualPiece, residualPiece_left, add_zero, add_sub_cancel_left]

theorem globalResidual_zero (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) :
    globalResidual externalStep τ hτ f hfr hfm k 0 = 0 := by
  have ht : (0 : ℝ) ∈ Set.Icc ((0 : ℕ) : ℝ) (((0 + 1 : ℕ) : ℝ) * τ) := by simp [hτ.le]
  have hh := globalResidual_on_step externalStep τ hτ f hfr hfm (j := 0) (Nat.zero_le k)
    (t := 0) (by simpa using ht)
  rw [hh]
  simp only [cumulativeResidualPiece, Finset.range_zero, Finset.sum_empty, zero_add]
  simpa using residualPiece_left externalStep τ hτ f hfr hfm 0

end KdV
