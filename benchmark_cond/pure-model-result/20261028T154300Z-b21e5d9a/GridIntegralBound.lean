import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem integral_concatenate_on_step {s τ : ℝ} (hτ : 0 < τ) (F : ℕ → ℝ → Sobolev s)
    {j k : ℕ} (hjk : j ≤ k) {b : ℝ}
    (hb : b ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    (∫ t : ℝ in (j : ℝ) * τ..b, concatenate τ F k t) =
      ∫ t : ℝ in (j : ℝ) * τ..b, F j t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (((j + 1 : ℕ) : ℝ) * τ)] with t hne
  intro ht
  rw [Set.uIoc_of_le hb.1] at ht
  exact concatenate_on_open_step hτ.le F hjk ⟨ht.1, lt_of_le_of_ne (ht.2.trans hb.2) hne⟩

/-- Finite-step accumulation for genuine Bochner integrals. It includes the
 possible partial final step and requires no agreement of derivative pieces. -/
theorem grid_integral_bound {s τ b A q : ℝ} (hτ : 0 < τ) (F : ℕ → ℝ → Sobolev s)
    (hF : ∀ j, Continuous (F j)) {j0 k : ℕ} (hj0 : j0 ≤ k)
    (hab : (j0 : ℝ) * τ ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ)
    (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hLocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b →
        ‖∫ r : ℝ in (j : ℝ) * τ..t, F j r‖ ≤ A * τ * q) :
    ‖∫ t : ℝ in (j0 : ℝ) * τ..b, concatenate τ F k t‖ ≤
      A * (b - (j0 : ℝ) * τ + τ) * q := by
  by_cases hba : b = (j0 : ℝ) * τ
  · subst b
    simp only [intervalIntegral.integral_same, norm_zero, sub_self, zero_add]
    positivity
  have hab' : (j0 : ℝ) * τ < b := lt_of_le_of_ne hab (Ne.symm hba)
  obtain ⟨n, hn, hnt⟩ := exists_closed_grid_step hτ k
    ((mul_nonneg (Nat.cast_nonneg j0) hτ.le).trans hab) hb
  have hjn : j0 ≤ n := by
    by_contra h
    have hh : n + 1 ≤ j0 := by omega
    have hc : ((n + 1 : ℕ) : ℝ) * τ ≤ (j0 : ℝ) * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hτ.le
    linarith [hnt.2]
  have hi (a c : ℝ) : IntervalIntegrable (concatenate τ F k) volume a c :=
    intervalIntegrable_concatenate τ F (fun j => (hF j).intervalIntegrable a c) k
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun j : ℕ => (j : ℝ) * τ)
    (f := concatenate τ F k) (μ := volume) hjn (fun j _ => hi _ _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi ((j0 : ℝ) * τ) ((n : ℝ) * τ))
    (hi ((n : ℝ) * τ) b)
  rw [← hsplit, ← hsum]
  have hEach (j : ℕ) (hj : j ∈ Finset.Ico j0 n) :
      (∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, concatenate τ F k t) =
        ∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t :=
    integral_concatenate_on_step hτ F ((Finset.mem_Ico.mp hj).2.le.trans hn)
      ⟨by push_cast; nlinarith, le_rfl⟩
  rw [Finset.sum_congr rfl hEach, integral_concatenate_on_step hτ F hn hnt]
  have hsumBound : ‖∑ j ∈ Finset.Ico j0 n, ∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t‖ ≤
      (n - j0 : ℕ) * (A * τ * q) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico j0 n, ‖∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.Ico j0 n, A * τ * q := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        apply hLocal j hj'.1 (hj'.2.le.trans hn) _ ⟨by push_cast; nlinarith, le_rfl⟩
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj'.2) hτ.le).trans hnt.1
      _ = _ := by simp
  have hlength : ((n - j0 + 1 : ℕ) : ℝ) * τ ≤ b - (j0 : ℝ) * τ + τ := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn]
    linarith [hnt.1]
  calc
    _ ≤ ‖∑ j ∈ Finset.Ico j0 n, ∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t‖ +
      ‖∫ t : ℝ in (n : ℝ) * τ..b, F n t‖ := norm_add_le _ _
    _ ≤ (n - j0 : ℕ) * (A * τ * q) + A * τ * q :=
      add_le_add hsumBound (hLocal n hjn hn b hnt le_rfl)
    _ = A * (((n - j0 + 1 : ℕ) : ℝ) * τ) * q := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength hA) hq

end KdV
