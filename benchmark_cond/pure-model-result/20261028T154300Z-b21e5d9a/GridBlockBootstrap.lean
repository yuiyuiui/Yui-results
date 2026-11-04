import ContinuityBootstrap
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Quantitative induction on a fixed number of blocks. The local hypothesis
 is an internal scalar interface, instantiated later by restarted stability. -/
theorem grid_block_bootstrap {τ δ K x : ℝ} {N B J : ℕ}
    (hτ : 0 < τ) (hStep : (J : ℝ) * τ ≤ δ) (hK : 0 ≤ K) (hx : 0 ≤ x)
    (hCover : N ≤ B * J) (hSmall : K * ((2 : ℝ) ^ B - 1) * x < 1)
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hLocal : ∀ j : ℕ, j < N → ∀ c : ℝ,
      (j : ℝ) * τ ≤ c → c ≤ (N : ℝ) * τ → c - (j : ℝ) * τ ≤ δ →
      (∀ r ∈ Set.Icc ((j : ℝ) * τ) c, q r ≤ 1) →
        q c ≤ 2 * q ((j : ℝ) * τ) + K * x) :
    ∀ t ∈ Set.Icc 0 ((N : ℝ) * τ), q t ≤ K * ((2 : ℝ) ^ B - 1) * x := by
  let D : ℕ → ℝ := fun n => K * ((2 : ℝ) ^ n - 1) * x
  have hD0 (n : ℕ) : 0 ≤ D n := by
    have hp : 0 ≤ (2 : ℝ) ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact mul_nonneg (mul_nonneg hK hp) hx
  have hDmono : Monotone D := by
    intro n m hnm
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnm) 1) hK) hx
  have hDsucc (n : ℕ) : D (n + 1) = 2 * D n + K * x := by dsimp [D]; rw [pow_succ]; ring
  have hAll : ∀ n : ℕ, n ≤ B → ∀ t ∈ Set.Icc 0 (((min (n * J) N : ℕ) : ℝ) * τ), q t ≤ D n := by
    intro n
    induction n with
    | zero =>
      intro _ t ht
      simp only [Nat.zero_min, Nat.cast_zero, zero_mul] at ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simpa only [hq0, D, pow_zero, sub_self, mul_zero, zero_mul] using (le_refl (0 : ℝ))
    | succ n ih =>
      intro hn t ht
      have hnB : n ≤ B := (Nat.le_succ n).trans hn
      have hdn : D n ≤ D (n + 1) := hDmono (Nat.le_succ _)
      by_cases hdone : N ≤ n * J
      · have hdone' : N ≤ (n + 1) * J := hdone.trans (Nat.mul_le_mul_right J (Nat.le_succ n))
        rw [Nat.min_eq_right hdone'] at ht
        exact (ih hnB t (by rwa [Nat.min_eq_right hdone])).trans hdn
      · have hj : n * J < N := lt_of_not_ge hdone
        let a : ℝ := ((n * J : ℕ) : ℝ) * τ
        let b : ℝ := ((min ((n + 1) * J) N : ℕ) : ℝ) * τ
        have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
        have hab : a ≤ b := mul_le_mul_of_nonneg_right (by
          exact_mod_cast (le_min (Nat.mul_le_mul_right J (Nat.le_succ n)) hj.le)) hτ.le
        have hbN : b ≤ (N : ℝ) * τ := mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right ((n + 1) * J) N) hτ.le
        have hbStep : b - a ≤ δ := by
          have hbJ : b ≤ (((n + 1) * J : ℕ) : ℝ) * τ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left ((n + 1) * J) N) hτ.le
          have heq : (((n + 1) * J : ℕ) : ℝ) * τ = a + (J : ℝ) * τ := by dsimp [a]; push_cast; ring
          rw [heq] at hbJ
          linarith
        have hStart : q a ≤ D n := ih hnB a (by rw [Nat.min_eq_left hj.le]; exact ⟨ha0, le_rfl⟩)
        have hqa : q a < 1 := hStart.trans_lt ((hDmono hnB).trans_lt hSmall)
        have hNext : D (n + 1) < 1 := (hDmono hn).trans_lt hSmall
        have hBlock : ∀ r ∈ Set.Icc a b, q r ≤ D (n + 1) := by
          apply continuity_unit_bootstrap hab q hq hqa hNext
          intro c hc hUnit
          have hcStep : c - a ≤ δ := by linarith [hc.2]
          have h := hLocal (n * J) hj c hc.1 (hc.2.trans hbN) hcStep hUnit
          rw [hDsucc]
          linarith
        by_cases hta : t ≤ a
        · exact (ih hnB t (by rw [Nat.min_eq_left hj.le]; exact ⟨ht.1, hta⟩)).trans hdn
        · exact hBlock t ⟨le_of_not_ge hta, ht.2⟩
  have hFinal := hAll B le_rfl
  rw [Nat.min_eq_right hCover] at hFinal
  exact hFinal

end KdV
