import GridBlockBootstrap
import GlobalParameters
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

/-- Uniform convergence for auxiliary `H²` flows. Its constants use only the
 common `H^γ` bound; the `H²` norm is absent. This is the input to density. -/
theorem uniform_h2_convergence (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ u : ℝ → Fourier, KdVSolution 2 T f.val u →
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ L : ℕ, 0 < L → T / (L : ℝ) ≤ τ0 →
          maximumError T L f.val u ≤ C * (T / (L : ℝ)) ^ γ := by
  obtain ⟨δ, K, hδ, _, hK, hStab⟩ := restarted_stability_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨B, _, hBlocks⟩ := uniform_grid_blocks hT hδ
  let C : ℝ := 1 + K * (2 : ℝ) ^ B
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨τ0, hτ0, hτ0δ, hSmall⟩ := small_rpow_threshold hγ hC (half_pos hδ)
  refine ⟨C, hC, τ0, hτ0, ?_⟩
  intro f hfr hfm u hu huM L hL hτsmall
  let τ : ℝ := T / (L : ℝ)
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hτ : 0 < τ := div_pos hT hLR
  have hτδ2 : τ ≤ δ / 2 := hτsmall.trans hτ0δ
  have hτδ : τ ≤ δ := hτδ2.trans (by linarith)
  have hLT : (L : ℝ) * τ = T := by dsimp [τ]; field_simp
  let k := L - 1
  have hKL : k + 1 = L := by dsimp [k]; omega
  have hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T := by rw [hKL, hLT]
  let J := L / B + 1
  obtain ⟨hCover, hStep⟩ := hBlocks L hL τ rfl hτδ2
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let q : ℝ → ℝ := fun t => hNorm 0 (e t).val
  have hqC : Continuous q := by
    have h := (((inclusionMap 0 1 (by norm_num)).continuous.comp
      (continuous_errorPath externalStep hT.le hτ f hfr hfm hu k)).norm)
    simpa only [sobolev_norm, inclusionMap_val, Function.comp_def] using h
  have hq0 : q 0 = 0 := by
    simp only [q, e, errorPath, sobolev_val_sub, exactTwistedOne, inclusionMap_val,
      extendedTwistedPath_zero, globalInterpolation_zero, sub_self, hNorm_zero]
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hCoeff : K * ((2 : ℝ) ^ B - 1) ≤ C := by dsimp [C]; nlinarith
  have hSmall' : K * ((2 : ℝ) ^ B - 1) * τ ^ γ < 1 := by
    calc
      _ ≤ C * τ ^ γ := mul_le_mul_of_nonneg_right hCoeff hτγ
      _ ≤ 1 / 2 := hSmall τ hτ hτsmall
      _ < _ := by norm_num
  have hLocal : ∀ j : ℕ, j < L → ∀ c : ℝ,
      (j : ℝ) * τ ≤ c → c ≤ (L : ℝ) * τ → c - (j : ℝ) * τ ≤ δ →
      (∀ r ∈ Set.Icc ((j : ℝ) * τ) c, q r ≤ 1) → q c ≤ 2 * q ((j : ℝ) * τ) + K * τ ^ γ := by
    intro j hj c hac hc hlen hUnit
    have hjk : j ≤ k := by dsimp [k]; omega
    have hcT : c ≤ ((k + 1 : ℕ) : ℝ) * τ := by rwa [hKL]
    exact hStab τ hτ hτδ k hTotal f hfr hfm u hu huM j hjk c hac hcT hlen hUnit c ⟨hac, le_rfl⟩
  have hGlobal := grid_block_bootstrap (N := L) (B := B) (J := J) hτ hStep hK.le hτγ hCover hSmall' q hqC hq0 hLocal
  unfold maximumError
  apply Finset.sup'_le
  intro j hj
  have hjL : j ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have ht : (j : ℝ) * τ ∈ Set.Icc 0 ((L : ℝ) * τ) :=
    ⟨mul_nonneg (Nat.cast_nonneg _) hτ.le, mul_le_mul_of_nonneg_right (by exact_mod_cast hjL) hτ.le⟩
  have hjk : j ≤ k + 1 := by rwa [hKL]
  have hGrid := actual_error_grid_norm externalStep hT.le hτ k hTotal f hfr hfm hu hjk
  change hNorm 0 (e ((j : ℝ) * τ)).val = _ at hGrid
  rw [← hGrid]
  exact (hGlobal _ ht).trans (mul_le_mul_of_nonneg_right hCoeff hτγ)

end KdV
