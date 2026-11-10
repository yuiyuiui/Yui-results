import TimeNormLinear
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem errorDerivative_ae_equation (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t).val =
        B t (errorPath externalStep hT hτ f hfr hfm hu k t).val
          (errorMidpoint externalStep hT hτ f hfr hfm hu k t).val -
        (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t).val := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)).ae_notMem (volume.restrict (Set.Icc a b))] with t ht hnot
  have hneq : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => hnot ⟨j, heq.symm⟩
  have htz : t ≠ 0 := by simpa only [Nat.cast_zero, zero_mul] using hneq 0
  have ht0 : 0 < t := lt_of_le_of_ne (ha.trans ht.1) (Ne.symm htz)
  have htT : t < ((k + 1 : ℕ) : ℝ) * τ := lt_of_le_of_ne (ht.2.trans hb) (hneq (k + 1))
  obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k ht0 htT hneq
  simp only [errorNegativeDerivative, inclusionMap_val]
  rw [concatenate_on_open_step hτ.le _ hj hstep, concatenate_on_open_step hτ.le _ hj hstep]
  exact errorDerivativeFamily_equation externalStep hT hτ f hfr hfm hu hj ⟨hstep.1.le, hstep.2.le⟩

/-- The small error `X` norm in (28), with actual weak derivatives and time
memberships. This follows from the proved restarted residual derivative bound. -/
theorem restarted_error_time_bound (externalStep : LiWuStepIdentity)
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
          timeXNorm ((j0 : ℝ) * τ) b (errorL2Path externalStep hT.le hτ f hfr hfm hu k)
            (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k) ≤ C * (τ ^ γ + E) := by
  obtain ⟨Cr, hCr, hR⟩ := restarted_residual_derivative_time_bound externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  let D : ℝ := K * (M + 1) + Cr
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + D, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  let a : ℝ := (j0 : ℝ) * τ
  let q : ℝ := τ ^ γ + E
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  let de := errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k
  let rn := numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm
  let Rn : ℝ → Sobolev (-pStar) := fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (concatenate τ rn k t)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) hE
  have hEq : E ≤ q := le_add_of_nonneg_left (Real.rpow_nonneg hτ.le γ)
  have hRN := hR τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  have hMemR : MemLp (concatenate τ rn k) ∞ (volume.restrict (Set.Icc a b)) :=
    memLp_concatenate τ rn (fun j => continuousOn_memLp_top_Icc
      (continuous_numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j).continuousOn) k
  have hMemRn : MemLp Rn ∞ (volume.restrict (Set.Icc a b)) :=
    hMemR.continuousLinearMap_comp (inclusionMap (-pStar) 0 (by norm_num [pStar]))
  have hRae : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖Rn t‖ ≤ Cr * q :=
    (timeLInfinity_ae_bound hMemRn).mono (fun _ ht => ht.trans hRN)
  have hdeEq := errorDerivative_ae_equation externalStep hT.le hτ k hTotal f hfr hfm hu
    (mul_nonneg (Nat.cast_nonneg j0) hτ.le) hbT
  have hdeb : timeLInfinity a b de ≤ D * q := by
    apply timeLInfinity_le_of_ae_bound (mul_nonneg hD hq)
    filter_upwards [hdeEq, hRae, ae_restrict_mem measurableSet_Icc] with t hdt hrt ht
    have he0 := (e t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hg0 := (g t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have heb : hNorm 0 (e t).val ≤ E := he t ht
    have hv0 : hNorm 0 (exactTwistedOne hT.le hu t).val ≤ M := by
      simpa only [sobolev_norm, exactL2Path, exactTwistedOne, inclusionMap_val] using
        exactL2Path_bound hT.le hγ.le (by linarith : γ ≤ 2) hu huM t
    have hgb : hNorm 0 (g t).val ≤ M + 1 := by
      have hG := hNorm_sub_le ((exactTwistedOne hT.le hu t).property.of_le (by norm_num)) (he0.smul (1 / 2 : ℂ))
      rw [hNorm_smul he0] at hG
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf] at hG
      change hNorm 0 (g t).val ≤ _ at hG
      linarith
    obtain ⟨hB, hBn⟩ := B_negative_bound he0 hg0 t
    have hBbound : hNorm (-pStar) (B t (e t).val (g t).val) ≤ K * (M + 1) * q := by
      calc
        _ ≤ K * hNorm 0 (e t).val * hNorm 0 (g t).val := hBn
        _ ≤ K * q * (M + 1) := mul_le_mul (mul_le_mul_of_nonneg_left (heb.trans hEq) hK) hgb
          (hNorm_nonneg _ _) (mul_nonneg hK hq)
        _ = _ := by ring
    rw [sobolev_norm]
    change hNorm (-pStar) (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k t).val ≤ D * q
    rw [hdt]
    have hrt' : hNorm (-pStar) (concatenate τ rn k t).val ≤ Cr * q := by
      simpa only [sobolev_norm, Rn, inclusionMap_val] using hrt
    calc
      _ ≤ hNorm (-pStar) (B t (e t).val (g t).val) + hNorm (-pStar) (concatenate τ rn k t).val :=
        hNorm_sub_le hB (Rn t).property
      _ ≤ K * (M + 1) * q + Cr * q := add_le_add hBbound hrt'
      _ = _ := by dsimp [D]; ring
  have heb : timeLInfinity a b (errorL2Path externalStep hT.le hτ f hfr hfm hu k) ≤ E :=
    timeLInfinity_le_of_bound hE _ (fun t ht => by rw [sobolev_norm]; exact he t ht)
  change timeLInfinity a b (errorL2Path externalStep hT.le hτ f hfr hfm hu k) + timeLInfinity a b de ≤ _
  calc
    _ ≤ E + D * q := add_le_add heb hdeb
    _ ≤ (1 + D) * q := by linarith

end KdV
