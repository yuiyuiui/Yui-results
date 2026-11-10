import SmoothOperators
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The first estimate in (21). The numerical input only has an `L²` bound
relative to the exact `H^γ` state; its higher Sobolev norm is not used. -/
theorem numerical_stage_square_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        InSobolev 0 (B t (bilinearStage ((n : ℝ) * τ) t f f)
          (bilinearStage ((n : ℝ) * τ) t f f)) ∧
        hNorm 0 (B t (bilinearStage ((n : ℝ) * τ) t f f)
          (bilinearStage ((n : ℝ) * τ) t f f)) ≤ C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cs, hCs, hstage⟩ := paper_stage_bounds externalStage hT hγ hγ1
  obtain ⟨Cn, hCn, hnum⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hsquare⟩ := derivative_square_bound externalProduct hγ hγ1
  let K : ℝ := Cs * M ^ 2
  let E : ℝ := Cd * K * K
  let D : ℝ := 4 * h1EmbeddingConstant * Cn * Cn
  have hK : 0 ≤ K := mul_nonneg hCs.le (sq_nonneg _)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg hCd.le hK) hK
  have hC1 : 0 < h1EmbeddingConstant := lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + E + D, by linarith, ?_⟩
  intro τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  have hδ0 := hNorm_nonneg 0 (f - w)
  let a : ℝ := (n : ℝ) * τ
  let F : Fourier := bilinearStage a t f f
  let A : Fourier := bilinearStage a t w w
  have hw0 := hw.of_le hγ.le
  obtain ⟨hAα, hAh, hAαb, hAhb⟩ := hstage τ n t hτ hτ1 hnT ht w w hw hw hwm hwm
  have hAhb' : hNorm (1 + γ) A ≤ K := by
    calc
      _ ≤ Cs * hNorm γ w * hNorm γ w := hAhb
      _ ≤ K := by
        have hb : hNorm γ w * hNorm γ w ≤ M ^ 2 := by nlinarith [hNorm_nonneg γ w]
        simpa only [K, mul_assoc] using mul_le_mul_of_nonneg_left hb hCs.le
  have hAαb' : hNorm (aGamma γ) A ≤ K * τ ^ γ := by
    calc
      _ ≤ Cs * τ ^ γ * hNorm γ w * hNorm γ w := hAαb
      _ ≤ K * τ ^ γ := by
        have hb : hNorm γ w * hNorm γ w ≤ M ^ 2 := by nlinarith [hNorm_nonneg γ w]
        have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hCs.le (Real.rpow_nonneg hτ.le γ))
        dsimp [K]
        nlinarith only [hh]
  have hF1 := (bilinearStage_h1_bound hf hf a t).1
  have hA1 := (bilinearStage_h1_bound hw0 hw0 a t).1
  have hFA := hF1.sub hA1
  obtain ⟨hFbound, hDiff, hFa, hF0⟩ := hnum τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  have hAw : hNorm 1 A ≤ Cn :=
    (hnum τ n t hτ hτ1 hnT ht w w hw0 hw hwm hwM (by simp)).1
  obtain ⟨hBAraw, hBAb⟩ := hsquare (airy t A) (airy_inSobolev hAh t) (airy_inSobolev hAα t)
  have hBA : InSobolev 0 (B t A A) := airy_inSobolev hBAraw (-t)
  have hBA_bound : hNorm 0 (B t A A) ≤ E * τ ^ γ := by
    change hNorm 0 (airy (-t) (derivative (product (airy t A) (airy t A)))) ≤ _
    rw [airy_hNorm]
    simp only [airy_hNorm] at hBAb
    calc
      _ ≤ Cd * hNorm (1 + γ) A * hNorm (aGamma γ) A := hBAb
      _ ≤ Cd * K * (K * τ ^ γ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAhb' hCd.le) hAαb'
          (hNorm_nonneg _ _) (mul_nonneg hCd.le hK)
      _ = E * τ ^ γ := by dsimp [E]; ring
  obtain ⟨hBDF, hBDFb⟩ := B_h1_bound hFA hF1 t
  obtain ⟨hBAD, hBADb⟩ := B_h1_bound hA1 hFA t
  have heq : B t F F = B t A A + (B t (F - A) F + B t A (F - A)) := by
    have hh := B_diagonal_sub (hF1.of_le (by norm_num)) (hA1.of_le (by norm_num)) t
    linear_combination hh
  rw [heq]
  refine ⟨hBA.add (hBDF.add hBAD), ?_⟩
  have hCalg : 0 ≤ 2 * h1EmbeddingConstant := by linarith [h1EmbeddingConstant_ge_one]
  have hBDbound : hNorm 0 (B t (F - A) F) + hNorm 0 (B t A (F - A)) ≤
      D * hNorm 0 (f - w) := by
    calc
      _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 (F - A) * hNorm 1 F +
          (2 * h1EmbeddingConstant) * hNorm 1 A * hNorm 1 (F - A) := add_le_add hBDFb hBADb
      _ ≤ (2 * h1EmbeddingConstant) * (Cn * hNorm 0 (f - w)) * Cn +
          (2 * h1EmbeddingConstant) * Cn * (Cn * hNorm 0 (f - w)) :=
        add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hDiff hCalg) hFbound
            (hNorm_nonneg _ _) (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left hAw hCalg) hDiff
            (hNorm_nonneg _ _) (by positivity))
      _ = _ := by dsimp [D]; ring
  calc
    _ ≤ hNorm 0 (B t A A) + hNorm 0 (B t (F - A) F + B t A (F - A)) :=
      hNorm_add_le hBA (hBDF.add hBAD)
    _ ≤ hNorm 0 (B t A A) + (hNorm 0 (B t (F - A) F) + hNorm 0 (B t A (F - A))) :=
      add_le_add le_rfl (hNorm_add_le hBDF hBAD)
    _ ≤ E * τ ^ γ + D * hNorm 0 (f - w) := add_le_add hBA_bound hBDbound
    _ ≤ (1 + E + D) * (τ ^ γ + hNorm 0 (f - w)) := by
      have ht0 := Real.rpow_nonneg hτ.le γ
      have hd0 := hNorm_nonneg 0 (f - w)
      nlinarith

end KdV
