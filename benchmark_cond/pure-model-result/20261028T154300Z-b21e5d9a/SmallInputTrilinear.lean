import RestartedAllTimeBounds
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem timeLInfinity_le_timeXNorm (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) :
    timeLInfinity a b f ≤ timeXNorm a b f df :=
  le_add_of_nonneg_right (timeLInfinity_nonneg _ _ _)

/-- A moving small input, in any position allowed by the primary trilinear
 estimate, gives one full time-step gain. The operator slots stay fixed. -/
theorem dynamic_small_input_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b τ A B : ℝ, 0 ≤ a → a ≤ b → b - a ≤ τ → τ ≤ 1 →
      0 ≤ τ → 0 ≤ A → 0 ≤ B →
      ∀ f : Fin 3 → ℝ → Sobolev 0, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
      (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
      (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
      (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
      ∀ i : Fin 3,
        timeXNorm a b (f i) (df i) ≤ A →
        (∀ j, j ≠ i → timeXNorm a b (f j) (df j) ≤ B) →
        timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (f i t)) ≤ τ * A →
        InSobolev 0 (CIntegral a b (fun t => (f 0 t).val) (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ∧
        hNorm 0 (CIntegral a b (fun t => (f 0 t).val) (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ≤
          C * τ * A * B ^ 2 := by
  obtain ⟨C, hC, hd⟩ := normalized_dynamic_trilinear externalTrilinear (H := 1) (by norm_num) le_rfl
  refine ⟨2 * C, by positivity, ?_⟩
  intro a b τ A B ha hab hlen hτ1 hτ hA hB f df hf hdf hw i hXi hX hNi
  obtain ⟨hmem, hbound⟩ := hd a b ha hab (hlen.trans hτ1) f df hf hdf hw
  have hprod : (∏ j : Fin 3, timeXNorm a b (f j) (df j)) ≤ A * B ^ 2 := by
    fin_cases i <;> simp only [Fin.prod_univ_three]
    · change timeXNorm a b (f 0) (df 0) ≤ A at hXi
      have hX1 := hX 1 (by decide); have hX2 := hX 2 (by decide)
      simpa only [pow_two, mul_assoc] using mul_le_mul
        (mul_le_mul hXi hX1 (timeXNorm_nonneg _ _ _ _) hA) hX2
        (timeXNorm_nonneg _ _ _ _) (mul_nonneg hA hB)
    · change timeXNorm a b (f 1) (df 1) ≤ A at hXi
      have hX0 := hX 0 (by decide); have hX2 := hX 2 (by decide)
      have h012 := mul_le_mul (mul_le_mul hX0 hXi (timeXNorm_nonneg _ _ _ _) hB) hX2
        (timeXNorm_nonneg _ _ _ _) (mul_nonneg hB hA)
      calc
        _ ≤ B * A * B := h012
        _ = _ := by ring
    · change timeXNorm a b (f 2) (df 2) ≤ A at hXi
      have hX0 := hX 0 (by decide); have hX1 := hX 1 (by decide)
      have h012 := mul_le_mul (mul_le_mul hX0 hX1 (timeXNorm_nonneg _ _ _ _) hB) hXi
        (timeXNorm_nonneg _ _ _ _) (mul_nonneg hB hB)
      calc
        _ ≤ B * B * A := h012
        _ = _ := by ring
  have hothers : (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) ≤ B ^ 2 := by
    have hL (j : Fin 3) (hji : j ≠ i) : timeLInfinity a b (f j) ≤ B :=
      (timeLInfinity_le_timeXNorm a b _ _).trans (hX j hji)
    fin_cases i <;> simp [Fin.prod_univ_three]
    · simpa only [pow_two] using mul_le_mul (hL 1 (by decide)) (hL 2 (by decide))
        (timeLInfinity_nonneg _ _ _) hB
    · simpa only [pow_two] using mul_le_mul (hL 0 (by decide)) (hL 2 (by decide))
        (timeLInfinity_nonneg _ _ _) hB
    · simpa only [pow_two] using mul_le_mul (hL 0 (by decide)) (hL 1 (by decide))
        (timeLInfinity_nonneg _ _ _) hB
  refine ⟨hmem, (hbound i).trans ?_⟩
  have hp0 : 0 ≤ ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j) :=
    Finset.prod_nonneg (fun j _ => by split_ifs; exact zero_le_one; exact timeLInfinity_nonneg _ _ _)
  calc
    _ ≤ C * τ * (A * B ^ 2) + C * (τ * A) * B ^ 2 :=
      add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hlen hC.le) hprod
        (Finset.prod_nonneg (fun j _ => timeXNorm_nonneg _ _ _ _)) (mul_nonneg hC.le hτ))
        (mul_le_mul (mul_le_mul_of_nonneg_left hNi hC.le) hothers hp0 (by positivity))
    _ = _ := by ring

end KdV
