import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem weight_negative_le_inverse_index {p : ℝ} (hp : 1 ≤ p) {m : ℕ} (hm : 0 < m) :
    weight (-p) (m : ℤ) ≤ (m : ℝ)⁻¹ := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    _ ≤ weight (-1) (m : ℤ) := weight_mono (by linarith) _
    _ = (weight 1 (m : ℤ))⁻¹ := weight_neg 1 _
    _ ≤ _ := inv_anti₀ hmR (by simpa only [Int.cast_natCast, abs_of_pos hmR] using weight_one_ge_abs (m : ℤ))

/-- The proof frequency threshold and restarted interval length are chosen
 before the numerical data, grid and bootstrap interval. -/
theorem absorption_parameters {C : ℝ} (hC : 0 < C) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ h τ : ℝ, 0 ≤ h → h ≤ δ → 0 ≤ τ → τ ≤ δ →
        C * ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * h + τ +
          weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) ≤ 1 / 4 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 : ℝ) (16 * C))
  have hm1 : 1 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmC : 16 * C < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hmR : 0 < (m : ℝ) := by positivity
  let N : ℝ := 1 + ((3 * m : ℕ) : ℝ) ^ 2
  have hN : 1 ≤ N := by dsimp [N]; nlinarith [sq_nonneg (((3 * m : ℕ) : ℝ))]
  have hN0 : 0 ≤ N := by linarith
  let δ : ℝ := min 1 (1 / (8 * C * (N + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδn : δ ≤ 1 / (8 * C * (N + 1)) := min_le_right _ _
  have hw1 : weight (-1) (3 * m : ℤ) ≤ (m : ℝ)⁻¹ := by
    have hwm := weight_negative_le_inverse_index (p := 1) le_rfl (m := 3 * m) (by omega)
    have hc : (3 * m : ℤ) = ((3 * m : ℕ) : ℤ) := by push_cast; rfl
    rw [hc]
    exact hwm.trans (inv_anti₀ hmR (by push_cast; nlinarith))
  have hwp : weight (-pStar) (m : ℤ) ≤ (m : ℝ)⁻¹ := weight_negative_le_inverse_index (by norm_num [pStar]) hm0
  have hwC : C * (weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) ≤ 1 / 8 := by
    calc
      _ ≤ C * (2 * (m : ℝ)⁻¹) := mul_le_mul_of_nonneg_left (by linarith) hC.le
      _ = (2 * C) / (m : ℝ) := by ring
      _ ≤ 1 / 8 := (div_le_iff₀ hmR).mpr (by nlinarith)
  refine ⟨m, hm0, δ, hδ, hδ1, ?_⟩
  intro h τ hh hhδ hτ hτδ
  have hδC : C * (N + 1) * δ ≤ 1 / 8 := by
    have hd : 0 < 8 * C * (N + 1) := by positivity
    have hx := (le_div_iff₀ hd).mp hδn
    nlinarith
  have hhτ : C * (N * h + τ) ≤ 1 / 8 := by
    calc
      _ ≤ C * ((N + 1) * δ) := mul_le_mul_of_nonneg_left (by nlinarith) hC.le
      _ = C * (N + 1) * δ := by ring
      _ ≤ _ := hδC
  change C * (N * h + τ + weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) ≤ _
  linarith

end KdV
