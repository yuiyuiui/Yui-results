import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem small_rpow_threshold {γ C A : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hA : 0 < A) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ τ0 ≤ A ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → C * τ ^ γ ≤ 1 / 2 := by
  let r : ℝ := (1 / (2 * C)) ^ γ⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min A r, lt_min hA hr, min_le_left _ _, ?_⟩
  intro τ hτ hτ0
  have hτr : τ ≤ r := hτ0.trans (min_le_right _ _)
  have hp : τ ^ γ ≤ 1 / (2 * C) := by
    have h := Real.rpow_le_rpow hτ.le hτr hγ.le
    rwa [Real.rpow_inv_rpow (by positivity : 0 ≤ 1 / (2 * C)) hγ.ne'] at h
  calc
    _ ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hp hC.le
    _ = _ := by field_simp

/-- A fixed number of blocks covers every grid. Integer division chooses
 only the block length; no cutoff or modification of the method is involved. -/
theorem uniform_grid_blocks {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ L : ℕ, 0 < L → ∀ τ : ℝ, τ = T / (L : ℝ) → τ ≤ δ / 2 →
      L ≤ B * (L / B + 1) ∧ ((L / B + 1 : ℕ) : ℝ) * τ ≤ δ := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (1 : ℝ) (2 * T / δ))
  have hB1 : 1 < (B : ℝ) := (le_max_left _ _).trans_lt hB
  have hBR : 0 < (B : ℝ) := by linarith
  have hBN : 0 < B := by exact_mod_cast hBR
  have hBT : 2 * T / δ < (B : ℝ) := (le_max_right _ _).trans_lt hB
  have hTdivB : T / (B : ℝ) ≤ δ / 2 := by
    apply (div_le_iff₀ hBR).mpr
    have h := (div_lt_iff₀ hδ).mp hBT
    nlinarith
  refine ⟨B, hBN, ?_⟩
  intro L hL τ hτ hτδ
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hτpos : 0 < τ := hτ ▸ div_pos hT hLR
  have hCover : L ≤ B * (L / B + 1) := by
    have hrem := Nat.mod_lt L hBN
    have heq := Nat.div_add_mod L B
    nlinarith
  have hfloor : ((L / B : ℕ) : ℝ) ≤ (L : ℝ) / (B : ℝ) := by
    apply (le_div_iff₀ hBR).mpr
    exact_mod_cast Nat.div_mul_le_self L B
  refine ⟨hCover, ?_⟩
  calc
    _ = ((L / B : ℕ) : ℝ) * τ + τ := by push_cast; ring
    _ ≤ ((L : ℝ) / (B : ℝ)) * τ + τ := add_le_add (mul_le_mul_of_nonneg_right hfloor hτpos.le) le_rfl
    _ = T / (B : ℝ) + τ := by rw [hτ]; field_simp
    _ ≤ δ := by linarith

end KdV
