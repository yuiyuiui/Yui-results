import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Concatenate the first `k+1` full step functions at their grid endpoints.
Each function is defined for every real time; only its own step is used inside
the integration interval. -/
def concatenate {E : Type*} (τ : ℝ) (F : ℕ → ℝ → E) : ℕ → ℝ → E
  | 0 => F 0
  | k + 1 => fun t => if t ≤ ((k + 1 : ℕ) : ℝ) * τ then concatenate τ F k t else F (k + 1) t

theorem concatenate_tail {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    (k : ℕ) {t : ℝ} (ht : (k : ℝ) * τ ≤ t) : concatenate τ F k t = F k t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [concatenate]
    dsimp only
    split_ifs with h
    · have heq : t = ((k + 1 : ℕ) : ℝ) * τ := le_antisymm h ht
      subst t
      rw [ih (by push_cast; nlinarith), hglue k]
    · rfl

theorem concatenate_eq_earlier {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ)
    (F : ℕ → ℝ → E) {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ≤ ((j + 1 : ℕ) : ℝ) * τ) : concatenate τ F k t = concatenate τ F j t := by
  induction k with
  | zero =>
    have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
    subst j
    rfl
  | succ k ih =>
    by_cases hj : j = k + 1
    · subst j
      rfl
    · have hj' : j ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne hjk hj)
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj'
      have hbound := ht.trans (mul_le_mul_of_nonneg_right hcast hτ)
      rw [concatenate]
      dsimp only
      rw [if_pos hbound]
      exact ih hj'

theorem concatenate_on_step {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    concatenate τ F k t = F j t := by
  rw [concatenate_eq_earlier hτ F hjk ht.2]
  exact concatenate_tail hτ F hglue j ht.1

theorem continuous_concatenate {E : Type*} [TopologicalSpace E] {τ : ℝ} (hτ : 0 ≤ τ)
    (F : ℕ → ℝ → E) (hF : ∀ j, Continuous (F j))
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    (k : ℕ) : Continuous (concatenate τ F k) := by
  induction k with
  | zero => exact hF 0
  | succ k ih =>
    apply ih.if_le (hF (k + 1)) continuous_id continuous_const
    intro t ht
    change t = ((k + 1 : ℕ) : ℝ) * τ at ht
    rw [ht, concatenate_tail hτ F hglue k (by push_cast; nlinarith), hglue k]

theorem concatenate_eventuallyEq {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    concatenate τ F k =ᶠ[nhds t] F j := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
  exact concatenate_on_step hτ F hglue hjk ⟨hr.1.le, hr.2.le⟩

end KdV
