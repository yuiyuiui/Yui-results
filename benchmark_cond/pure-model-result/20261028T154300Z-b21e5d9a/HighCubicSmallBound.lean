import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem fin_three_prod_bound {x : Fin 3 → ℝ} {A B : ℝ} (i : Fin 3)
    (hx : ∀ j, 0 ≤ x j) (hi : x i ≤ A) (hothers : ∀ j, j ≠ i → x j ≤ B) :
    (∏ j : Fin 3, x j) ≤ A * B ^ 2 := by
  have hp : (∏ j : Fin 3, x j) ≤ ∏ j : Fin 3, if j = i then A else B := by
    apply Finset.prod_le_prod (fun j _ => hx j)
    intro j _
    split_ifs with h
    · subst j; exact hi
    · exact hothers j h
  have heq : (∏ j : Fin 3, if j = i then A else B) = A * B ^ 2 := by
    fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
  rwa [heq] at hp

/-- A specialization of (32) which preserves separate small error and error
 derivative norms. It leaves both terms needed for absorption explicit. -/
theorem high_output_small_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 1 →
      ∀ f : Fin 3 → ℝ → Sobolev 1, (∀ j, Continuous (f j)) →
      ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
        ∀ m : ℕ, ∀ i : Fin 3, ∀ A E B : ℝ,
        timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (f i t)) (df i) ≤ A →
        timeLInfinity a b (fun t => inclusionMap 0 1 (by norm_num) (f i t)) ≤ E →
        (∀ j, j ≠ i → timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (f j t)) (df j) ≤ B) →
        InSobolev 0 (highCutoff (3 * m) (pathCubic a b f)) ∧
        hNorm 0 (highCutoff (3 * m) (pathCubic a b f)) ≤
          C * (b - a) * A * B ^ 2 + C * weight (-pStar) (m : ℤ) * E * B ^ 2 := by
  obtain ⟨C, hC, hd⟩ := high_output_trilinear_bound externalTrilinear
  refine ⟨C, hC, ?_⟩
  intro a b ha hab hlen f hf df hdf hw m i A E B hXi hLi hX
  obtain ⟨hmem, hbound⟩ := hd a b ha hab hlen f hf df hdf hw m
  have hprodX := fin_three_prod_bound (x := fun j => timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (f j t)) (df j)) i (fun j => timeXNorm_nonneg a b _ _) hXi hX
  have hprodL := fin_three_prod_bound (x := fun j => timeLInfinity a b (fun t => inclusionMap 0 1 (by norm_num) (f j t))) i (fun j => timeLInfinity_nonneg a b _) hLi (fun j hj =>
    (le_add_of_nonneg_right (timeLInfinity_nonneg a b (df j))).trans (hX j hj))
  refine ⟨hmem, hbound.trans ?_⟩
  calc
    _ ≤ C * (b - a) * (A * B ^ 2) + C * weight (-pStar) (m : ℤ) * (E * B ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hprodX (mul_nonneg hC.le (sub_nonneg.mpr hab)))
        (mul_le_mul_of_nonneg_left hprodL (mul_nonneg hC.le (weight_pos _ _).le))
    _ = _ := by ring

end KdV
