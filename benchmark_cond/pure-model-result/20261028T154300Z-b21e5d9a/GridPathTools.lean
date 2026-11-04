import GlobalPerturbation
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem concatenate_tail_strict {E : Type*} (τ : ℝ) (F : ℕ → ℝ → E) (j : ℕ) {t : ℝ}
    (ht : (j : ℝ) * τ < t) : concatenate τ F j t = F j t := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [concatenate]
    dsimp only
    exact if_neg (not_le.mpr ht)

/-- Derivative pieces need not match at the grid: on an open step the correct
piece is selected without any endpoint-gluing hypothesis. -/
theorem concatenate_on_open_step {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    concatenate τ F k t = F j t := by
  rw [concatenate_eq_earlier hτ F hjk ht.2.le]
  exact concatenate_tail_strict τ F j ht.1

theorem concatenate_map {E F : Type*} (τ : ℝ) (u : ℕ → ℝ → E) (G : ℝ → E → F)
    (k : ℕ) (t : ℝ) :
    concatenate τ (fun j r => G r (u j r)) k t = G t (concatenate τ u k t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [concatenate, concatenate]
    dsimp only
    split_ifs <;> first | exact ih | rfl

theorem intervalIntegrable_concatenate {E : Type*} [NormedAddCommGroup E]
    (τ : ℝ) (F : ℕ → ℝ → E) {a b : ℝ}
    (hF : ∀ j, IntervalIntegrable (F j) volume a b) (k : ℕ) :
    IntervalIntegrable (concatenate τ F k) volume a b := by
  induction k with
  | zero => exact hF 0
  | succ k ih =>
    constructor
    · change Integrable ((Set.Iic (((k + 1 : ℕ) : ℝ) * τ)).piecewise
        (concatenate τ F k) (F (k + 1))) (volume.restrict (Set.Ioc a b))
      exact Integrable.piecewise measurableSet_Iic ih.1.integrableOn (hF (k + 1)).1.integrableOn
    · change Integrable ((Set.Iic (((k + 1 : ℕ) : ℝ) * τ)).piecewise
        (concatenate τ F k) (F (k + 1))) (volume.restrict (Set.Ioc b a))
      exact Integrable.piecewise measurableSet_Iic ih.2.integrableOn (hF (k + 1)).2.integrableOn

theorem memLp_concatenate {E : Type*} [NormedAddCommGroup E]
    (τ : ℝ) (F : ℕ → ℝ → E) {μ : Measure ℝ} {p : ℝ≥0∞}
    (hF : ∀ j, MemLp (F j) p μ) (k : ℕ) : MemLp (concatenate τ F k) p μ := by
  induction k with
  | zero => exact hF 0
  | succ k ih =>
    change MemLp ((Set.Iic (((k + 1 : ℕ) : ℝ) * τ)).piecewise
      (concatenate τ F k) (F (k + 1))) p μ
    exact MemLp.piecewise measurableSet_Iic (ih.restrict _) ((hF (k + 1)).restrict _)

end KdV
