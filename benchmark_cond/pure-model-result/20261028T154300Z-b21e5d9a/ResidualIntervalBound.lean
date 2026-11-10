import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem exists_closed_grid_step {τ : ℝ} (_hτ : 0 < τ) (k : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    ∃ j : ℕ, j ≤ k ∧ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simpa using And.intro ht0 htT⟩
  | succ k ih =>
    by_cases hlast : t ≤ ((k + 1 : ℕ) : ℝ) * τ
    · obtain ⟨j, hj, hjt⟩ := ih hlast
      exact ⟨j, hj.trans (Nat.le_succ _), hjt⟩
    · exact ⟨k + 1, le_rfl, (le_of_not_ge hlast), htT⟩

/-- The number of residual increments is controlled by interval length plus
one step. This is a proved finite-sum estimate for the actual concatenation. -/
theorem globalResidual_interval_bound (externalStep : LiWuStepIdentity)
    {τ : ℝ} (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {j0 k : ℕ} (hj0 : j0 ≤ k) {b A q : ℝ} (hab : (j0 : ℝ) * τ ≤ b)
    (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hLocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b →
        ‖residualPiece externalStep τ hτ f hfr hfm j t‖ ≤ A * τ * q) :
    ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
      ‖globalResidual externalStep τ hτ f hfr hfm k t -
        globalResidual externalStep τ hτ f hfr hfm k ((j0 : ℝ) * τ)‖ ≤
          A * (b - (j0 : ℝ) * τ + τ) * q := by
  intro t ht
  by_cases hta : t = (j0 : ℝ) * τ
  · subst t
    rw [sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg hA (by linarith)) hq
  · have hat : (j0 : ℝ) * τ < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
    obtain ⟨n, hn, hnt⟩ := exists_closed_grid_step hτ k
      ((mul_nonneg (Nat.cast_nonneg j0) hτ.le).trans ht.1) (ht.2.trans hb)
    have hjn : j0 ≤ n := by
      by_contra h
      have hh : n + 1 ≤ j0 := by omega
      have hc : ((n + 1 : ℕ) : ℝ) * τ ≤ (j0 : ℝ) * τ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hτ.le
      linarith [hnt.2]
    let F : ℕ → Sobolev 0 := fun j => residualPiece externalStep τ hτ f hfr hfm j (((j + 1 : ℕ) : ℝ) * τ)
    have hstart : (j0 : ℝ) * τ ∈ Set.Icc ((j0 : ℝ) * τ) (((j0 + 1 : ℕ) : ℝ) * τ) := by
      constructor
      · rfl
      · push_cast
        nlinarith
    rw [globalResidual_on_step externalStep τ hτ f hfr hfm hn hnt,
      globalResidual_on_step externalStep τ hτ f hfr hfm hj0 hstart]
    change ‖((∑ j ∈ Finset.range n, F j) + residualPiece externalStep τ hτ f hfr hfm n t) -
      ((∑ j ∈ Finset.range j0, F j) + residualPiece externalStep τ hτ f hfr hfm j0 ((j0 : ℝ) * τ))‖ ≤ _
    rw [residualPiece_left, add_zero]
    have heq : ((∑ j ∈ Finset.range n, F j) + residualPiece externalStep τ hτ f hfr hfm n t) -
        (∑ j ∈ Finset.range j0, F j) =
        ((∑ j ∈ Finset.range n, F j) - ∑ j ∈ Finset.range j0, F j) + residualPiece externalStep τ hτ f hfr hfm n t := by
      abel
    rw [heq, ← Finset.sum_Ico_eq_sub F hjn]
    have hFn : ‖residualPiece externalStep τ hτ f hfr hfm n t‖ ≤ A * τ * q := hLocal n hjn hn t hnt ht.2
    have hsum : ‖∑ j ∈ Finset.Ico j0 n, F j‖ ≤ (n - j0 : ℕ) * (A * τ * q) := by
      calc
        _ ≤ ∑ j ∈ Finset.Ico j0 n, ‖F j‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.Ico j0 n, A * τ * q := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Finset.mem_Ico.mp hj
          have hjk : j ≤ k := hj'.2.le.trans hn
          have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ b :=
            ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj'.2) hτ.le).trans hnt.1).trans ht.2
          exact hLocal j hj'.1 hjk _
            ⟨by push_cast; nlinarith, le_rfl⟩ hEnd
        _ = _ := by simp
    have hlength : ((n - j0 + 1 : ℕ) : ℝ) * τ ≤ b - (j0 : ℝ) * τ + τ := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn]
      linarith [hnt.1, ht.2]
    calc
      _ ≤ ‖∑ j ∈ Finset.Ico j0 n, F j‖ + ‖residualPiece externalStep τ hτ f hfr hfm n t‖ := norm_add_le _ _
      _ ≤ (n - j0 : ℕ) * (A * τ * q) + A * τ * q := add_le_add hsum hFn
      _ = A * (((n - j0 + 1 : ℕ) : ℝ) * τ) * q := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength hA) hq

theorem hNorm_sub_symm (s : ℝ) (f g : Fourier) : hNorm s (f - g) = hNorm s (g - f) := by
  rw [← neg_sub g f, hNorm_neg]

/-- Restarted residual estimate (27), derived from (26) and the actual grid
error bound. The exact Sobolev bound is explicit and will be supplied by the
previously proved initial-ball flow theorem. -/
theorem restarted_residual_bound (externalStep : LiWuStepIdentity)
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
            hNorm 0 ((inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT.le hu t) -
              globalInterpolation externalStep τ hτ f hfr hfm k t).val) ≤ E) →
          ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            ‖globalResidual externalStep τ hτ f hfr hfm k t -
              globalResidual externalStep τ hτ f hfr hfm k ((j0 : ℝ) * τ)‖ ≤
              C * (b - (j0 : ℝ) * τ + τ) * (τ ^ γ + E) := by
  obtain ⟨C, hC, hb⟩ := numerical_residual_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  apply globalResidual_interval_bound externalStep hτ f hfr hfm hj0 hab hbT hC.le
    (add_nonneg (Real.rpow_nonneg hτ.le γ) hE)
  intro j hj0j hjk s hs hsb
  have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal
  have hgridI : (j : ℝ) * τ ∈ Set.Icc ((j0 : ℝ) * τ) b :=
    ⟨mul_le_mul_of_nonneg_right (by exact_mod_cast hj0j) hτ.le, hs.1.trans hsb⟩
  have hgridT : (j : ℝ) * τ ∈ Set.Icc 0 T :=
    ⟨mul_nonneg (Nat.cast_nonneg j) hτ.le, hgridI.2.trans (hbT.trans hTotal)⟩
  let fj := twistedNumericalBundled τ f j
  let w := (extendedTwistedPath hT.le hu ((j : ℝ) * τ)).val
  have hw : InSobolev γ w := (extendedTwistedPath hT.le hu ((j : ℝ) * τ)).property.of_le (by linarith : γ ≤ 2)
  have hwm : MeanZero w := extendedTwistedPath_meanZero hT.le hu _
  have hwM : hNorm γ w ≤ M := by
    dsimp [w]
    rw [extendedTwistedPath_val_on hT.le hu hgridT, airy_hNorm]
    exact huM _ hgridT
  have hδ : hNorm 0 (fj.val - w) ≤ E := by
    have hh := he _ hgridI
    rw [sobolev_val_sub, inclusionMap_val, globalInterpolation_grid externalStep τ hτ f hfr hfm (hjk.trans (Nat.le_succ _))] at hh
    rw [hNorm_sub_symm]
    exact hh
  have hrho := (hb τ j hτ hτ1 hEnd fj (twistedNumericalBundled_real τ hfr j)
    (twistedNumericalBundled_meanZero τ hfm j) w hw hwm hwM (hδ.trans hE1) s hs).2.1
  rw [sobolev_norm, residualPiece_val]
  exact hrho.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) (mul_nonneg hC.le hτ.le))

end KdV
