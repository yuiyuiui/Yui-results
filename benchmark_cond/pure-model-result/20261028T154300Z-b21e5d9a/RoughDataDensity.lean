import Proof
import PositiveFlowExistence
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 1000000

theorem numerical_cutoff_converges {f : Fourier} (hf : InSobolev 0 f) (τ : ℝ) (n : ℕ) :
    Filter.Tendsto (fun m : ℕ => hNorm 0 (numerical τ (cutoff m f) n - numerical τ f n))
      Filter.atTop (nhds 0) := by
  let F : Sobolev 0 := ⟨f, hf⟩
  have h := ((continuous_numericalBundled τ n).continuousAt.tendsto.comp (approximation_converges F))
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [sobolev_norm, sobolev_val_sub, numericalBundled_val, approximation, Function.comp_def] using h

/-- Density is performed at each fixed positive timestep, using the proved
 full-method `L²` continuity and the source flow's uniform `L²` dependence.
 The constants are selected before the rough datum and the number of steps. -/
theorem uniform_rough_convergence (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    (externalGalerkin : BITGalerkinEstimate) (externalLimit : BITExistenceLimit)
    (externalHigh : BITHigherRegularity) (externalLow : BITLowRegularity)
    (externalLipschitz : BITWeakerLipschitz)
    {T γ R : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ f : Fourier, InSobolev γ f → RealValued f → MeanZero f → hNorm γ f ≤ R →
      ∀ u : ℝ → Fourier, KdVSolution γ T f u →
        ∀ L : ℕ, 0 < L → T / (L : ℝ) ≤ τ0 →
          maximumError T L f u ≤ C * (T / (L : ℝ)) ^ γ := by
  obtain ⟨M, hM, hFlow⟩ := uniform_kdv_flow_bound externalGalerkin externalLimit externalHigh externalLow hγ hT hR
  obtain ⟨C, hC, τ0, hτ0, hConv⟩ := uniform_h2_convergence externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM.le
  obtain ⟨Cd, hCd, hDep⟩ := kdv_flow_l2_lipschitz externalLipschitz (show 0 ≤ 2 * R by positivity) hT
  refine ⟨C, hC, τ0, hτ0, ?_⟩
  intro f hf hfr hfm hfR u hu L hL hτ0bound
  let τ : ℝ := T / (L : ℝ)
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hτ : 0 < τ := div_pos hT hLR
  have hLT : (L : ℝ) * τ = T := by dsimp [τ]; field_simp
  have hf0 := hf.of_le hγ.le
  have hf0R : hNorm 0 f ≤ R := (hNorm_mono hf hγ.le).trans hfR
  let fm : ℕ → Sobolev 2 := fun m => ⟨cutoff m f, cutoff_inSobolev_all 2 m f⟩
  have hfmR (m : ℕ) : RealValued (fm m).val := cutoff_real hfr m
  have hfmM (m : ℕ) : MeanZero (fm m).val := cutoff_meanZero hfm m
  have hfmγ (m : ℕ) : InSobolev γ (fm m).val := cutoff_inSobolev hf m
  have hfmBound (m : ℕ) : hNorm γ (fm m).val ≤ R := (cutoff_hNorm_le hf m).trans hfR
  have hex (m : ℕ) : ∃ v : ℝ → Fourier, KdVSolution 2 T (fm m).val v :=
    positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow (by norm_num) hT
      (fm m).property (hfmR m) (hfmM m)
  choose vm hvm using hex
  have hvmγ (m : ℕ) : KdVSolution γ T (fm m).val (vm m) :=
    ⟨(hvm m).1.of_le (by linarith : γ ≤ 2), (hvm m).2⟩
  have hvmBound (m : ℕ) : ∀ t ∈ Set.Icc 0 T, hNorm γ (vm m t) ≤ M :=
    hFlow (fm m).val (hfmR m) (hfmM m) (hfmγ m) (hfmBound m) (vm m) (hvmγ m)
  have hConvM (m : ℕ) := hConv (fm m) (hfmR m) (hfmM m) (vm m) (hvm m) (hvmBound m) L hL hτ0bound
  have hData := cutoff_converges hf0
  unfold maximumError
  apply Finset.sup'_le
  intro n hn
  have hnL : n ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have ht : (n : ℝ) * τ ∈ Set.Icc 0 T := ⟨mul_nonneg (Nat.cast_nonneg _) hτ.le,
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hnL) hτ.le).trans_eq hLT⟩
  have hNum := numerical_cutoff_converges hf0 τ n
  have hLimit : Filter.Tendsto (fun m : ℕ => Cd * hNorm 0 (cutoff m f - f) + C * τ ^ γ +
      hNorm 0 (numerical τ (cutoff m f) n - numerical τ f n)) Filter.atTop (nhds (C * τ ^ γ)) := by
    have h := (((tendsto_const_nhds (x := Cd)).mul hData).add_const (C * τ ^ γ)).add hNum
    simpa only [mul_zero, zero_add, add_zero] using h
  apply ge_of_tendsto hLimit
  apply Filter.Eventually.of_forall
  intro m
  have hL2 : hNorm 0 (fm m).val + hNorm 0 f ≤ 2 * R := by
    have hb := (cutoff_hNorm_le hf0 m).trans hf0R
    change hNorm 0 (cutoff m f) + hNorm 0 f ≤ _
    linarith
  have hExact := hDep 2 γ (by norm_num) hγ.le (fm m).val f (hfmR m) (hfmM m) (fm m).property
    hfr hfm hf hL2 (vm m) u (hvm m) hu _ ht
  have hErr : hNorm 0 (vm m ((n : ℝ) * τ) - numerical τ (fm m).val n) ≤ C * τ ^ γ := by
    have h := Finset.le_sup' (fun j : ℕ => hNorm 0 (vm m ((j : ℝ) * τ) - numerical τ (fm m).val j)) hn
    exact h.trans (hConvM m)
  have hu0 := (hu.1.1 _ ht).of_le hγ.le
  have hm0 := ((hvm m).1.1 _ ht).of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hn0 := numerical_inSobolev (γ := 0) le_rfl (by norm_num) τ ((fm m).property.of_le (by norm_num)) n
  have hnf0 := numerical_inSobolev (γ := 0) le_rfl (by norm_num) τ hf0 n
  have hSplit : u ((n : ℝ) * τ) - numerical τ f n =
      (u ((n : ℝ) * τ) - vm m ((n : ℝ) * τ)) +
      (vm m ((n : ℝ) * τ) - numerical τ (fm m).val n) +
      (numerical τ (fm m).val n - numerical τ f n) := by abel
  have hSymm : hNorm 0 (u ((n : ℝ) * τ) - vm m ((n : ℝ) * τ)) ≤ Cd * hNorm 0 (cutoff m f - f) := by
    rw [hNorm_sub_symm]
    exact hExact
  rw [hSplit]
  exact (hNorm_add_le ((hu0.sub hm0).add (hm0.sub hn0)) (hn0.sub hnf0)).trans
    ((add_le_add (hNorm_add_le (hu0.sub hm0) (hm0.sub hn0)) le_rfl).trans
      (add_le_add (add_le_add hSymm hErr) le_rfl))

end KdV
