import BilinearOps
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

/-- The stage estimates used in (20), uniform over numerical `L²` inputs close
to an exact `H^γ` state. No numerical higher Sobolev bound is assumed. -/
theorem numerical_stage_bounds (externalStage : LiWuStageEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f) ≤ C ∧
        hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) ≤
          C * hNorm 0 (f - w) ∧
        hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f f) ≤ C * (τ ^ γ + hNorm 0 (f - w)) ∧
        hNorm 0 (bilinearStage ((n : ℝ) * τ) t f f) ≤ C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cs, hCs, hstage⟩ := paper_stage_bounds externalStage hT hγ hγ1
  obtain ⟨ha0, ha1, hrest⟩ := aGamma_parameters hγ hγ1
  let K : ℝ := (4 / 3 : ℝ) * h1EmbeddingConstant
  have hK : 0 < K := mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one)
  let A : ℝ := K * (M + 1) ^ 2
  let D : ℝ := K * (2 * M + 1)
  let E : ℝ := Cs * M ^ 2
  have hA : 0 ≤ A := mul_nonneg hK.le (sq_nonneg _)
  have hD : 0 ≤ D := mul_nonneg hK.le (by linarith)
  have hE : 0 ≤ E := mul_nonneg hCs.le (sq_nonneg _)
  let C : ℝ := 1 + A + D + E
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  have hw0 := hw.of_le hγ.le
  have hwM0 : hNorm 0 w ≤ M := (hNorm_mono hw hγ.le).trans hwM
  have hfM : hNorm 0 f ≤ M + 1 := by
    have hs := hNorm_add_le (hf.sub hw0) hw0
    rw [sub_add_cancel] at hs
    linarith
  obtain ⟨hf1, hfb⟩ := bilinearStage_h1_bound hf hf ((n : ℝ) * τ) t
  obtain ⟨hw1, hwb⟩ := bilinearStage_h1_bound hw0 hw0 ((n : ℝ) * τ) t
  have hdiff := bilinearStage_diagonal_lipschitz hf hw0 ((n : ℝ) * τ) t
  have hDb : hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) ≤
      D * hNorm 0 (f - w) := by
    calc
      _ ≤ K * (hNorm 0 f + hNorm 0 w) * hNorm 0 (f - w) := hdiff
      _ ≤ K * ((M + 1) + M) * hNorm 0 (f - w) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hfM hwM0) hK.le) (hNorm_nonneg 0 _)
      _ = _ := by dsimp [D]; ring
  have hAb : hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f) ≤ A := by
    calc
      _ ≤ K * hNorm 0 f * hNorm 0 f := hfb
      _ ≤ A := by
        dsimp [A]
        have hs : hNorm 0 f * hNorm 0 f ≤ (M + 1) ^ 2 := by nlinarith [hNorm_nonneg 0 f]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hK.le
  obtain ⟨hwA, hwHigh, hwAB, hwHighB⟩ := hstage τ n t hτ hτ1 hnT ht w w hw hw hwm hwm
  have hEb : hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t w w) ≤ E * τ ^ γ := by
    calc
      _ ≤ Cs * τ ^ γ * hNorm γ w * hNorm γ w := hwAB
      _ ≤ E * τ ^ γ := by
        have hs : hNorm γ w * hNorm γ w ≤ M ^ 2 := by nlinarith [hNorm_nonneg γ w]
        have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hCs.le (Real.rpow_nonneg hτ.le γ))
        dsimp [E]
        nlinarith only [hm]
  have hsum : hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f f) ≤
      E * τ ^ γ + D * hNorm 0 (f - w) := by
    have hdA : InSobolev (aGamma γ)
        (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) :=
      (hf1.sub hw1).of_le ha1.le
    have hs := hNorm_add_le hwA hdA
    rw [show bilinearStage ((n : ℝ) * τ) t w w +
      (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) =
      bilinearStage ((n : ℝ) * τ) t f f by abel] at hs
    exact hs.trans (add_le_add hEb ((hNorm_mono (hf1.sub hw1) ha1.le).trans hDb))
  have hbound : hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f f) ≤
      C * (τ ^ γ + hNorm 0 (f - w)) := by
    calc
      _ ≤ E * τ ^ γ + D * hNorm 0 (f - w) := hsum
      _ ≤ C * τ ^ γ + C * hNorm 0 (f - w) :=
        add_le_add (mul_le_mul_of_nonneg_right hEC (Real.rpow_nonneg hτ.le _))
          (mul_le_mul_of_nonneg_right hDC (hNorm_nonneg 0 _))
      _ = _ := by ring
  exact ⟨hAb.trans hAC, hDb.trans (mul_le_mul_of_nonneg_right hDC (hNorm_nonneg 0 _)),
    hbound, (hNorm_mono (hf1.of_le ha1.le) ha0).trans hbound⟩

end KdV
