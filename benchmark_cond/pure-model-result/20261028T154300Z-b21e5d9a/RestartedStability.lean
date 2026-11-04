import ErrorInequality
import AbsorptionParameters
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

theorem exists_hNorm_maximum {a b : ℝ} (hab : a ≤ b) (f : ℝ → Sobolev 1) (hf : Continuous f) :
    ∃ E : ℝ, 0 ≤ E ∧ (∀ t ∈ Set.Icc a b, hNorm 0 (f t).val ≤ E) ∧
      ∃ t ∈ Set.Icc a b, hNorm 0 (f t).val = E := by
  have hc : Continuous (fun t => ‖inclusionMap 0 1 (by norm_num) (f t)‖) :=
    ((inclusionMap 0 1 (by norm_num)).continuous.comp hf).norm
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab⟩ hc.continuousOn
  refine ⟨hNorm 0 (f t).val, hNorm_nonneg _ _, ?_, t, ht, rfl⟩
  intro r hr
  have hh := hmax hr
  change ‖inclusionMap 0 1 (by norm_num) (f r)‖ ≤ ‖inclusionMap 0 1 (by norm_num) (f t)‖ at hh
  simpa only [sobolev_norm, inclusionMap_val] using hh

/-- The restarted stability estimate (35), after an internal maximum and
 absorption argument. The remaining unit bootstrap is explicit and will be
 discharged by continuity in the global estimate. -/
theorem restarted_stability_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧
      ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ δ → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          b - (j0 : ℝ) * τ ≤ δ →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ 1) →
          ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤
              2 * hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k ((j0 : ℝ) * τ)).val + K * τ ^ γ := by
  obtain ⟨C, hC, hEst⟩ := restarted_error_inequality externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨m, _, δ, hδ, hδ1, hAbs⟩ := absorption_parameters hC
  refine ⟨δ, 4 * C * δ, hδ, hδ1, by positivity, ?_⟩
  intro τ hτ hτδ k hTotal f hfr hfm u hu huM j0 hj0 b hab hb hlen hUnit t ht
  let a : ℝ := (j0 : ℝ) * τ
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  obtain ⟨E, hE, hEbound, s, hs, hsE⟩ := exists_hNorm_maximum hab e
    (continuous_errorPath externalStep hT.le hτ f hfr hfm hu k)
  have hE1 : E ≤ 1 := hsE ▸ hUnit s hs
  have hSub : Set.Icc a s ⊆ Set.Icc a b := fun r hr => ⟨hr.1, hr.2.trans hs.2⟩
  have hslen : s - a ≤ δ := by linarith [hs.2]
  have hI := hEst τ hτ (hτδ.trans hδ1) k hTotal f hfr hfm u hu huM j0 hj0 s E hs.1
    (hs.2.trans hb) (hslen.trans hδ1) hE hE1 (fun r hr => hEbound r (hSub hr)) m
  change hNorm 0 (e s).val ≤ hNorm 0 (e a).val + _ at hI
  rw [hsE] at hI
  have hCoeff := hAbs (s - a) τ (sub_nonneg.mpr hs.1) hslen hτ.le hτδ
  have hStep : s - a + τ ≤ 2 * δ := by linarith
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hTime := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hStep hτγ) hC.le
  have hCoefE := mul_le_mul_of_nonneg_right hCoeff hE
  have hA : 0 ≤ hNorm 0 (e a).val := hNorm_nonneg _ _
  have hEB : E ≤ 2 * hNorm 0 (e a).val + (4 * C * δ) * τ ^ γ := by nlinarith
  exact (hEbound t ht).trans hEB

end KdV
