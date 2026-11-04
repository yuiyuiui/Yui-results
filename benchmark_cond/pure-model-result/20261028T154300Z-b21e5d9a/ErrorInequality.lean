import ErrorIntegralEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

/-- The pointwise restarted inequality before choosing proof parameters or
 discharging the temporary bootstrap hypothesis. -/
theorem restarted_error_inequality (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          b - (j0 : ℝ) * τ ≤ 1 → 0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          ∀ m : ℕ,
          let e := errorPath externalStep hT.le hτ f hfr hfm hu k
          hNorm 0 (e b).val ≤ hNorm 0 (e ((j0 : ℝ) * τ)).val +
            C * ((b - (j0 : ℝ) * τ + τ) * τ ^ γ +
            ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - (j0 : ℝ) * τ) + τ +
              weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E) := by
  obtain ⟨Ci, hCi, hInt⟩ := restarted_error_integral_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cr, hCr, hRes⟩ := restarted_residual_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  refine ⟨Ci + Cr, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  let R := globalResidual externalStep τ hτ f hfr hfm k
  let FI := fun l => ∫ t : ℝ in a..b, B t (e t).val (g t).val l
  let Z : ℝ := (b - a + τ) * τ ^ γ +
    ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - a) + τ + weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E
  obtain ⟨hFI, hFIn⟩ := hInt τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m
  have hRn := hRes τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he b ⟨hab, le_rfl⟩
  have hRI : InSobolev 0 ((R b).val - (R a).val) := (R b).property.sub (R a).property
  have hRnorm : hNorm 0 ((R b).val - (R a).val) ≤ Cr * (b - a + τ) * (τ ^ γ + E) := by
    simpa only [sobolev_norm, sobolev_val_sub] using hRn
  have hCoeff : b - a + τ ≤ (1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - a) + τ +
      weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ) := by
    have hh : 0 ≤ b - a := sub_nonneg.mpr hab
    have h1 := (weight_pos (-1) (3 * m : ℤ)).le
    have h2 := (weight_pos (-pStar) (m : ℤ)).le
    nlinarith [mul_nonneg (sq_nonneg (((3 * m : ℕ) : ℝ))) hh]
  have hRZ : hNorm 0 ((R b).val - (R a).val) ≤ Cr * Z := hRnorm.trans (calc
    _ = Cr * ((b - a + τ) * τ ^ γ + (b - a + τ) * E) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCoeff hE)) hCr.le)
  have hEq : (e b).val = (e a).val + FI - ((R b).val - (R a).val) :=
    actual_error_integral_identity externalStep hT.le hτ k hTotal f hfr hfm hu
      (mul_nonneg (Nat.cast_nonneg _) hτ.le) hab hb
  rw [hEq]
  have hea := (e a).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ hNorm 0 ((e a).val + FI) + hNorm 0 ((R b).val - (R a).val) := hNorm_sub_le (hea.add hFI) hRI
    _ ≤ (hNorm 0 (e a).val + hNorm 0 FI) + hNorm 0 ((R b).val - (R a).val) :=
      add_le_add (hNorm_add_le hea hFI) le_rfl
    _ ≤ (hNorm 0 (e a).val + Ci * Z) + Cr * Z := add_le_add (add_le_add le_rfl hFIn) hRZ
    _ = _ := by dsimp [Z]; ring

end KdV
