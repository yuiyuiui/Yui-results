import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

theorem numericalL2_eq_affine (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) :
    (fun t => inclusionMap 0 1 (by norm_num) (globalInterpolation externalStep τ hτ f hfr hfm k t)) =
      (fun t => exactL2Path hT hu t - (1 : ℂ) • errorL2Path externalStep hT hτ f hfr hfm hu k t) := by
  funext t
  apply Sobolev.ext
  simp only [sobolev_val_sub, one_smul, errorL2Path, inclusionMap_val, exactL2Path,
    errorPath, sobolev_val_sub, exactTwistedOne]
  module

/-- The restarted forcing estimate in (33), applied to the actual full
 unfiltered interpolation and its actual residual derivative. -/
theorem restarted_forcing_bound (externalStep : LiWuStepIdentity)
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
          let R' := concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k
          let V := globalInterpolation externalStep τ hτ f hfr hfm k
          InSobolev 0 (fun m => ∫ t : ℝ in (j0 : ℝ) * τ..b, J t (R' t).val (V t).val m) ∧
          hNorm 0 (fun m => ∫ t : ℝ in (j0 : ℝ) * τ..b, J t (R' t).val (V t).val m) ≤
            C * (b - (j0 : ℝ) * τ + τ) * (τ ^ γ + E) := by
  obtain ⟨Ca, hCa, hAffine⟩ := restarted_affine_error_time_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cl, hCl, hLocal⟩ := local_residual_forcing_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  let B : ℝ := 1 + Ca + M
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by linarith
  refine ⟨Cl * B ^ 2, mul_pos hCl (sq_pos_of_pos (by linarith)), ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let V0 := fun t => inclusionMap 0 1 (by norm_num) (V t)
  let dV := fun t => exactNegativeDerivative hT.le hu t - (1 : ℂ) • errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k t
  let rn := numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm
  let F : ℕ → ℝ → Sobolev 0 := fun j t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t (rn j t) (V0 t))
  have hVC : Continuous V := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  have hFC (j : ℕ) : Continuous (F j) := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id (continuous_numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j)
      ((inclusionMap 0 1 (by norm_num)).continuous.comp hVC))
  have hEqV := numericalL2_eq_affine externalStep hT.le hτ f hfr hfm hu k
  have hEqRaw : (fun t => (V0 t).val) =
      (fun t => (exactL2Path hT.le hu t - (1 : ℂ) • errorL2Path externalStep hT.le hτ f hfr hfm hu k t).val) :=
    congrArg (fun p : ℝ → Sobolev 0 => fun t => (p t).val) hEqV
  obtain ⟨hV, hdV, _⟩ := affine_error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu 1
    (mul_nonneg (Nat.cast_nonneg j0) hτ.le) hab hbT
  rw [← hEqV] at hV
  have hVX : timeXNorm a b V0 dV ≤ Ca := by
    have h := hAffine τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he 1 (by norm_num)
    rwa [← hEqV] at h
  have hVB : ∀ t ∈ Set.Icc a b, hNorm 0 (V t).val ≤ B := by
    intro t ht
    have he0 := (errorPath externalStep hT.le hτ f hfr hfm hu k t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hv0 := (exactTwistedOne hT.le hu t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hvM : hNorm 0 (exactTwistedOne hT.le hu t).val ≤ M := by
      simpa only [sobolev_norm, exactL2Path, exactTwistedOne, inclusionMap_val] using
        exactL2Path_bound hT.le hγ.le (by linarith : γ ≤ 2) hu huM t
    have hn := hNorm_sub_le hv0 he0
    have heq : (exactTwistedOne hT.le hu t).val - (errorPath externalStep hT.le hτ f hfr hfm hu k t).val = (V t).val := by
      simp only [errorPath, sobolev_val_sub]; exact sub_sub_cancel _ _
    rw [heq] at hn
    have heb := he t ht
    dsimp [B]
    linarith
  have hlocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b →
      ‖∫ r : ℝ in (j : ℝ) * τ..t, F j r‖ ≤ (Cl * B ^ 2) * τ * (τ ^ γ + E) := by
    intro j hj0j hjk t ht htb
    have hSub : Set.Icc ((j : ℝ) * τ) t ⊆ Set.Icc a b := fun r hr =>
      ⟨(mul_le_mul_of_nonneg_right (by exact_mod_cast hj0j) hτ.le).trans hr.1, hr.2.trans htb⟩
    have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal
    have htTotal : t ≤ ((k + 1 : ℕ) : ℝ) * τ := htb.trans hbT
    obtain ⟨_, _, hW⟩ := affine_error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu 1
      (mul_nonneg (Nat.cast_nonneg j) hτ.le) ht.1 htTotal
    rw [← hEqRaw] at hW
    have hXs : timeXNorm ((j : ℝ) * τ) t V0 dV ≤ B := by
      exact ((add_le_add (timeLInfinity_mono_interval hV hSub)
        (timeLInfinity_mono_interval hdV hSub)).trans hVX).trans (by dsimp [B]; linarith)
    obtain ⟨hw, hwm, hwM, hδ⟩ := frozen_comparison_bound externalStep hT.le hτ k j0 hTotal hbT
      (by linarith : γ ≤ 2) f hfr hfm hu huM he hj0j hjk (ht.1.trans htb)
    obtain ⟨hI, hIn⟩ := hLocal τ j hτ hτ1 hEnd (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)
      _ hw hwm hwM (hδ.trans hE1) t ht V hVC dV B hB
      (memLp_mono_interval hV hSub) (memLp_mono_interval hdV hSub) hW hXs
      (fun r hr => hVB r (hSub hr))
    have hval : (∫ r : ℝ in (j : ℝ) * τ..t, F j r).val =
        (fun m => ∫ r : ℝ in (j : ℝ) * τ..t,
          J r (localResidualDerivative τ ((j : ℝ) * τ) r (twistedNumericalBundled τ f j).val) (V r).val m) := by
      rw [sobolev_integral_val ((hFC j).intervalIntegrable _ _)]
      funext m
      apply intervalIntegral.integral_congr
      intro r _
      change J r (rn j r).val (V r).val m = _
      rw [numericalResidualDerivativeFamily_val]
    rw [sobolev_norm, hval]
    calc
      _ ≤ Cl * τ * (τ ^ γ + hNorm 0 ((twistedNumericalBundled τ f j).val - (extendedTwistedPath hT.le hu ((j : ℝ) * τ)).val)) * B ^ 2 := hIn
      _ ≤ Cl * τ * (τ ^ γ + E) * B ^ 2 := by gcongr
      _ = _ := by ring
  have hbnd := grid_integral_bound hτ F hFC hj0 hab hbT (mul_nonneg hCl.le (sq_nonneg B))
    (add_nonneg (Real.rpow_nonneg hτ.le γ) hE) hlocal
  have hi : IntervalIntegrable (concatenate τ F k) volume a b :=
    intervalIntegrable_concatenate τ F (fun j => (hFC j).intervalIntegrable a b) k
  have hval : (∫ t : ℝ in a..b, concatenate τ F k t).val =
      (fun m => ∫ t : ℝ in a..b, J t (concatenate τ rn k t).val (V t).val m) := by
    rw [sobolev_integral_val hi]
    funext m
    apply intervalIntegral.integral_congr
    intro t _
    have hmap : concatenate τ F k t = inclusionMap 0 1 (by norm_num)
        (JZeroBundled t (concatenate τ rn k t) (V0 t)) :=
      concatenate_map τ rn (fun r w => inclusionMap 0 1 (by norm_num) (JZeroBundled r w (V0 r))) k t
    dsimp only
    rw [hmap]
    rfl
  rw [← hval]
  exact ⟨(∫ t : ℝ in a..b, concatenate τ F k t).property, by rwa [← sobolev_norm]⟩

end KdV
