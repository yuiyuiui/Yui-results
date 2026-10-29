import RestartedCubicBound
import NormalFormHighBound
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

theorem affine_error_pointwise_bound (externalStep : LiWuStepIdentity) {T τ γ M E : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (_hE : 0 ≤ E)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    (huM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) (k : ℕ) (t : ℝ)
    (he : hNorm 0 (errorPath externalStep hT hτ f hfr hfm hu k t).val ≤ E)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    hNorm 0 (affineErrorPath externalStep hT hτ f hfr hfm hu k z t).val ≤ M + E := by
  have hv := (exactTwistedOne hT hu t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have he0 := (errorPath externalStep hT hτ f hfr hfm hu k t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hvM : hNorm 0 (exactTwistedOne hT hu t).val ≤ M := by
    simpa only [sobolev_norm, exactL2Path, exactTwistedOne, inclusionMap_val] using
      exactL2Path_bound hT hγ hγ2 hu huM t
  have hn := hNorm_sub_le hv (he0.smul z)
  rw [hNorm_smul he0] at hn
  exact hn.trans (add_le_add hvM (calc
    _ ≤ 1 * E := mul_le_mul hz he (hNorm_nonneg _ _) (by norm_num)
    _ = _ := one_mul _))

theorem pathCubic_error_first (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (a b : ℝ) :
    pathCubic a b (errorCubicInputs externalStep hT hτ f hfr hfm hu k 0 ![0,1/2,1]) =
      CIntegral a b (fun t => (errorPath externalStep hT hτ f hfr hfm hu k t).val)
        (fun t => (errorMidpoint externalStep hT hτ f hfr hfm hu k t).val)
        (fun t => (globalInterpolation externalStep τ hτ f hfr hfm k t).val) := by
  simp only [pathCubic, errorCubicInputs]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [ite_true, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, ite_false]
  simp only [affineErrorPath_half, affineErrorPath_one]

theorem pathCubic_error_last (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (a b : ℝ) :
    pathCubic a b (errorCubicInputs externalStep hT hτ f hfr hfm hu k 2 (fun _ => 0)) =
      CIntegral a b (fun t => (exactTwistedOne hT hu t).val) (fun t => (exactTwistedOne hT hu t).val)
        (fun t => (errorPath externalStep hT hτ f hfr hfm hu k t).val) := by
  simp only [pathCubic, errorCubicInputs]
  simp [affineErrorPath]

theorem combine_stability_scalar {h τ x E N l j c r wt wp : ℝ}
    (hh : 0 ≤ h) (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hE : 0 ≤ E) (hN : 1 ≤ N)
    (hl : 0 ≤ l) (hj : 0 ≤ j) (hc : 0 ≤ c) (hr : 0 ≤ r) (hwt : 0 ≤ wt) (hwp : 0 ≤ wp) :
    N * l * E * h + wt * (2 * j * E) + 2 * c * (h * x + (h + wp) * E) + r * (h + τ) * (x + E) ≤
      (1 + l + 2 * j + 2 * c + r) * ((h + τ) * x + (N * h + τ + wt + wp) * E) := by
  apply sub_nonneg.mp
  have hNm : 0 ≤ N - 1 := sub_nonneg.mpr hN
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  calc
    _ = (1 + l + 2 * j) * h * x + (1 + l + 2 * j + 2 * c) * τ * x +
        (N * (1 + 2 * j) + (N - 1) * (2 * c + r)) * h * E +
        (1 + l + 2 * j + 2 * c) * τ * E +
        (1 + l + 2 * c + r) * wt * E + (1 + l + 2 * j + r) * wp * E := by ring
    _ ≥ 0 := by positivity

/-- Bound on the nonlinear integral in the actual error equation, before
 choosing the proof frequency threshold and the restarted interval length. -/
theorem restarted_error_integral_bound (externalStep : LiWuStepIdentity)
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
          let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
          let I := fun l => ∫ t : ℝ in (j0 : ℝ) * τ..b, B t (e t).val (g t).val l
          InSobolev 0 I ∧ hNorm 0 I ≤ C * ((b - (j0 : ℝ) * τ + τ) * τ ^ γ +
            ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - (j0 : ℝ) * τ) + τ +
              weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E) := by
  obtain ⟨Cc, hCc, hCubic⟩ := restarted_cubic_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cf, hCf, hForcing⟩ := restarted_forcing_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  let Kl := negativeProductConstant 1 (by norm_num)
  let Kj := 4 * h1EmbeddingConstant
  have hKl : 0 ≤ Kl := norm_nonneg _
  have hKj : 0 ≤ Kj := by dsimp [Kj]; have h := h1EmbeddingConstant_ge_one; positivity
  let G := M + 1
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let C := 1 + Kl * G + 2 * Kj * G + 2 * Cc + Cf
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  let v := exactTwistedOne hT.le hu
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let FI := fun l => ∫ t : ℝ in a..b, B t (e t).val (g t).val l
  let C₁ := CIntegral a b (fun t => (e t).val) (fun t => (g t).val) (fun t => (V t).val)
  let C₂ := CIntegral a b (fun t => (v t).val) (fun t => (v t).val) (fun t => (e t).val)
  let RI := fun l => ∫ t : ℝ in a..b,
    J t (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t).val (V t).val l
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
  have heC : Continuous e := continuous_errorPath externalStep hT.le hτ f hfr hfm hu k
  have hgC : Continuous g := continuous_errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  have hgB : ∀ t ∈ Set.Icc a b, hNorm 0 (g t).val ≤ G := by
    intro t ht
    exact (affine_error_pointwise_bound externalStep hT.le hτ hγ.le (by linarith : γ ≤ 2) hE f hfr hfm hu huM k t (he t ht)
      (1 / 2) (by norm_num)).trans (by dsimp [G]; linarith)
  have hFI : InSobolev 0 FI := by
    have hi : IntervalIntegrable (fun t => BOneBundled t (e t) (g t)) volume a b :=
      (continuous_BOneBundled continuous_id heC hgC).intervalIntegrable a b
    rw [show FI = (∫ t : ℝ in a..b, BOneBundled t (e t) (g t)).val from (sobolev_integral_val hi).symm]
    exact (∫ t : ℝ in a..b, BOneBundled t (e t) (g t)).property
  have hLow := (integrated_B_low_bound hab hE hG e g heC hgC he hgB (3 * m)).2
  obtain ⟨hC₁, hC₁n⟩ := hCubic τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m 0 ![0,1/2,1]
    (by intro j; fin_cases j <;> norm_num)
  rw [pathCubic_error_first] at hC₁ hC₁n
  obtain ⟨hC₂, hC₂n⟩ := hCubic τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m 2 (fun _ => 0)
    (by intro j; norm_num)
  rw [pathCubic_error_last] at hC₂ hC₂n
  obtain ⟨hRI, hRIn⟩ := hForcing τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he
  have hNF : FI = (1 / 3 : ℂ) • (J b (e b).val (g b).val - J a (e a).val (g a).val) -
      (1 / 3 : ℂ) • C₁ - (1 / 6 : ℂ) • C₂ + (1 / 3 : ℂ) • RI := by
    funext l
    exact actual_error_normal_form externalStep hT.le hτ k hTotal f hfr hfm hu ha hab hb l
  obtain ⟨hJb, hJbn⟩ := J_h1_bound ((e b).property.of_le (by norm_num)) ((g b).property.of_le (by norm_num)) b
  obtain ⟨hJa, hJan⟩ := J_h1_bound ((e a).property.of_le (by norm_num)) ((g a).property.of_le (by norm_num)) a
  have hEnd : hNorm 1 (J b (e b).val (g b).val) + hNorm 1 (J a (e a).val (g a).val) ≤ 2 * Kj * E * G := by
    have hbE := he b ⟨hab, le_rfl⟩
    have haE := he a ⟨le_rfl, hab⟩
    have hbG := hgB b ⟨hab, le_rfl⟩
    have haG := hgB a ⟨le_rfl, hab⟩
    have hbj : hNorm 1 (J b (e b).val (g b).val) ≤ Kj * E * G := hJbn.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hbE hKj) hbG (hNorm_nonneg _ _) (mul_nonneg hKj hE))
    have haj : hNorm 1 (J a (e a).val (g a).val) ≤ Kj * E * G := hJan.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left haE hKj) haG (hNorm_nonneg _ _) (mul_nonneg hKj hE))
    linarith
  have hHigh := (normal_form_high_bound (3 * m) hJb hJa hC₁ hC₂ hRI hNF).2
  refine ⟨hFI, (hNorm_low_high_le hFI (3 * m)).trans ?_⟩
  have hwt : 0 ≤ weight (-1) (3 * m : ℤ) := (weight_pos _ _).le
  have hwp : 0 ≤ weight (-pStar) (m : ℤ) := (weight_pos _ _).le
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hHigh' : hNorm 0 (highCutoff (3 * m) FI) ≤ weight (-1) (3 * m : ℤ) * (2 * Kj * E * G) +
      2 * Cc * ((b - a) * τ ^ γ + (b - a + weight (-pStar) (m : ℤ)) * E) +
      Cf * (b - a + τ) * (τ ^ γ + E) := by
    have hh := hHigh.trans (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hEnd (weight_pos _ _).le) hC₁n) hC₂n) hRIn)
    convert! hh using 1 <;> (try simp only [Nat.cast_mul, Nat.cast_ofNat]) <;> (try dsimp only [a]) <;> ring
  calc
    _ ≤ (1 + ((3 * m : ℕ) : ℝ) ^ 2) * Kl * E * G * (b - a) +
      (weight (-1) (3 * m : ℤ) * (2 * Kj * E * G) +
      2 * Cc * ((b - a) * τ ^ γ + (b - a + weight (-pStar) (m : ℤ)) * E) +
      Cf * (b - a + τ) * (τ ^ γ + E)) := add_le_add hLow hHigh'
    _ ≤ C * ((b - a + τ) * τ ^ γ +
      ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - a) + τ + weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E) := by
      have hs := combine_stability_scalar (h := b - a) (τ := τ) (x := τ ^ γ) (E := E)
        (N := 1 + ((3 * m : ℕ) : ℝ) ^ 2) (l := Kl * G) (j := Kj * G) (c := Cc) (r := Cf)
        (wt := weight (-1) (3 * m : ℤ)) (wp := weight (-pStar) (m : ℤ))
        hlen0 hτ.le hτγ hE (by nlinarith [sq_nonneg (((3 * m : ℕ) : ℝ))])
        (mul_nonneg hKl hG) (mul_nonneg hKj hG) hCc.le hCf.le hwt hwp
      dsimp only [C]
      convert! hs using 1 <;> ring


end KdV
