import CubicConstantPair
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The moving-defect trilinear bound needed for (26), on every subinterval
of the actual step. Every weak derivative and time-norm hypothesis is proved. -/
theorem numerical_cubic_defect_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (CIntegral ((n : ℝ) * τ) t (fun _ => f.val) (fun _ => f.val)
            (fun s => interpolationRemainder τ ((n : ℝ) * τ) s f.val)) ∧
          hNorm 0 (CIntegral ((n : ℝ) * τ) t (fun _ => f.val) (fun _ => f.val)
            (fun s => interpolationRemainder τ ((n : ℝ) * τ) s f.val)) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cp, hCp, hpair⟩ := dynamic_constant_pair_bound externalTrilinear (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Cy, hCy, htime⟩ := numerical_defect_time_bounds externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  refine ⟨2 * Cp * Cy * (M + 1) ^ 2, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let Y := defectL2Path externalStep τ hτ n f hfr hfm
  let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
  let NY := fun s => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y s)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  obtain ⟨hY, hdY, hWeak, hX, hN⟩ := htime τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ
  have hSub : Set.Icc a t ⊆ Set.Icc a b := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hYs := memLp_mono_interval hY hSub
  have hdYs := memLp_mono_interval hdY hSub
  have hYC : Continuous Y := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_defectBundled externalStep τ hτ n f hfr hfm)
  have hNY : MemLp NY ∞ (volume.restrict (Set.Icc a b)) := continuousOn_memLp_top_Icc
    (((inclusionMap (-pStar) 0 (by norm_num [pStar])).continuous.comp hYC).continuousOn)
  have hNX : timeLInfinity a t NY ≤ Cy * τ * q :=
    (timeLInfinity_mono_interval hNY hSub).trans hN
  have hXs : timeXNorm a t Y dY ≤ Cy * q := by
    exact (add_le_add (timeLInfinity_mono_interval hY hSub)
      (timeLInfinity_mono_interval hdY hSub)).trans hX
  have hWs : WeakTimeDerivative a t (fun s => (Y s).val) (fun s => (dY s).val) := by
    have hh := ((interpolationRemainder_regular externalStep τ hτ n f hfr hfm).restrict
      le_rfl ht.2).weakTimeDerivative ht.1
    simpa only [Y, dY, defectL2Path, defectNegativeDerivativePath,
      show ∀ s r h (f : Sobolev r), (inclusionMap s r h f).val = f.val from fun _ _ _ _ => rfl,
      defectBundled_val, defectDerivativeBundled_val] using hh
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
    have hw0 := hw.of_le hγ.le
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  obtain ⟨hCI, hCIb⟩ := hpair a t (mul_nonneg (Nat.cast_nonneg n) hτ.le) ht.1
    ((grid_interval_length n ht).trans hτ1) (inclusionMap 1 2 (by norm_num) f) Y dY hYs hdYs hWs
    (M + 1) (Cy * q) (Cy * τ * q) (by linarith) (mul_nonneg hCy.le hq)
    (mul_nonneg (mul_nonneg hCy.le hτ.le) hq) hfM hXs hNX
  have hbound : hNorm 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) ≤
      (2 * Cp * Cy * (M + 1) ^ 2) * τ * q := by
    calc
      _ ≤ Cp * (t - a) * (M + 1) ^ 2 * (Cy * q) + Cp * (Cy * τ * q) * (M + 1) ^ 2 := hCIb
      _ ≤ Cp * τ * (M + 1) ^ 2 * (Cy * q) + Cp * (Cy * τ * q) * (M + 1) ^ 2 := by
        gcongr
        exact grid_interval_length n ht
      _ = _ := by ring
  have hval (s : ℝ) : (Y s).val = interpolationRemainder τ a s f.val :=
    defectBundled_val externalStep τ hτ n s f hfr hfm
  change InSobolev 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) at hCI
  simpa only [hval, a, q] using And.intro hCI hbound

end KdV
