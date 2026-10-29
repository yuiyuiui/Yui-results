import ErrorPaths
import ResidualIntervalBound
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem concatenate_ae_bound_on_steps {s τ b A : ℝ} (hτ : 0 < τ) (F : ℕ → ℝ → Sobolev s)
    {j0 k : ℕ} (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ)
    (hLocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b → ‖F j t‖ ≤ A) :
    ∀ᵐ t ∂volume.restrict (Set.Icc ((j0 : ℝ) * τ) b), ‖concatenate τ F k t‖ ≤ A := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)).ae_notMem
      (volume.restrict (Set.Icc ((j0 : ℝ) * τ) b))] with t ht hnot
  have hneq : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => hnot ⟨j, heq.symm⟩
  have hat : (j0 : ℝ) * τ < t := lt_of_le_of_ne ht.1 (Ne.symm (hneq j0))
  have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg j0) hτ.le) hat
  have htT : t < ((k + 1 : ℕ) : ℝ) * τ := lt_of_le_of_ne (ht.2.trans hb) (hneq (k + 1))
  obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k ht0 htT hneq
  have hj0 : j0 ≤ j := by
    by_contra hn
    have hn' : j + 1 ≤ j0 := by omega
    have hbound : ((j + 1 : ℕ) : ℝ) * τ ≤ (j0 : ℝ) * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn') hτ.le
    linarith [hstep.2]
  rw [concatenate_on_open_step hτ.le F hj hstep]
  exact hLocal j hj0 hj t ⟨hstep.1.le, hstep.2.le⟩ ht.2

theorem frozen_comparison_bound (externalStep : LiWuStepIdentity) {T τ γ M E b : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k j0 : ℕ) (_hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (_hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (hγ2 : γ ≤ 2)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    (huM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M)
    (he : ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
      hNorm 0 (errorPath externalStep hT hτ f hfr hfm hu k t).val ≤ E)
    {j : ℕ} (hj0 : j0 ≤ j) (hjk : j ≤ k) (hjb : (j : ℝ) * τ ≤ b) :
    let w := (extendedTwistedPath hT hu ((j : ℝ) * τ)).val
    InSobolev γ w ∧ MeanZero w ∧ hNorm γ w ≤ M ∧
      hNorm 0 ((twistedNumericalBundled τ f j).val - w) ≤ E := by
  dsimp only
  have hgrid : (j : ℝ) * τ ∈ Set.Icc ((j0 : ℝ) * τ) b :=
    ⟨mul_le_mul_of_nonneg_right (by exact_mod_cast hj0) hτ.le, hjb⟩
  refine ⟨(extendedTwistedPath hT hu _).property.of_le hγ2,
    extendedTwistedPath_meanZero hT hu _, extendedTwistedPath_bound hT hu huM _, ?_⟩
  have hh := he _ hgrid
  change hNorm 0 ((inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu ((j : ℝ) * τ)) -
    globalInterpolation externalStep τ hτ f hfr hfm k ((j : ℝ) * τ)).val) ≤ E at hh
  rw [sobolev_val_sub, inclusionMap_val,
    globalInterpolation_grid externalStep τ hτ f hfr hfm (hjk.trans (Nat.le_succ _))] at hh
  rw [hNorm_sub_symm]
  exact hh

/-- The global residual derivative estimate needed for (28), in its genuine
essential time norm. The possible previous-step value at the restart point is
handled as a null singleton, rather than assigned an unsupported pointwise bound. -/
theorem restarted_residual_derivative_time_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          timeLInfinity ((j0 : ℝ) * τ) b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar])
            (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t)) ≤
              C * (τ ^ γ + E) := by
  obtain ⟨C, hC, hb⟩ := numerical_residual_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  let F : ℕ → ℝ → Sobolev (-pStar) := fun j t => inclusionMap (-pStar) 0 (by norm_num [pStar])
    (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t)
  have hmap : concatenate τ F k = (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar])
      (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t)) := by
    funext t
    exact concatenate_map τ _ (fun _ v => inclusionMap (-pStar) 0 (by norm_num [pStar]) v) k t
  rw [← hmap]
  apply timeLInfinity_le_of_ae_bound (mul_nonneg hC.le (add_nonneg (Real.rpow_nonneg hτ.le γ) hE))
  apply concatenate_ae_bound_on_steps hτ F hbT
  intro j hj0j hjk t ht htb
  obtain ⟨hw, hwm, hwM, hδ⟩ := frozen_comparison_bound externalStep hT.le hτ k j0 hTotal hbT
    (by linarith : γ ≤ 2) f hfr hfm hu huM he hj0j hjk (ht.1.trans htb)
  have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal
  have hR := (hb τ j hτ hτ1 hEnd (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)
    _ hw hwm hwM (hδ.trans hE1) t ht).2.2.2
  rw [sobolev_norm]
  change hNorm (-pStar) (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t).val ≤ _
  rw [numericalResidualDerivativeFamily_val]
  exact hR.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) hC.le)

end KdV
