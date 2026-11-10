import ProjectionTimeNorm
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The three terms of the proof's trilinear telescoping: slots before `i`
are low, slot `i` is high, and subsequent slots are unchanged. -/
def inputProjection (s : ℝ) (m : ℕ) (i j : Fin 3) : Sobolev s →L[ℂ] Sobolev s :=
  if j < i then cutoffMap s m else if j = i then highCutoffMap s m else ContinuousLinearMap.id ℂ _

theorem inputProjection_norm_le (s : ℝ) (m : ℕ) (i j : Fin 3) (f : Sobolev s) :
    ‖inputProjection s m i j f‖ ≤ ‖f‖ := by
  unfold inputProjection
  split_ifs
  · exact cutoffMap_norm_le s m f
  · exact highCutoffMap_norm_le s m f
  · exact le_rfl

theorem inputProjection_inclusion_val (s r : ℝ) (hsr : s ≤ r) (m : ℕ) (i j : Fin 3) (f : Sobolev r) :
    (inputProjection s m i j (inclusionMap s r hsr f)).val = (inputProjection r m i j f).val := by
  unfold inputProjection
  split_ifs <;> simp only [cutoffMap_val, highCutoffMap_val, inclusionMap_val, ContinuousLinearMap.id_apply]

theorem inputProjection_memLp {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i j : Fin 3) :
    MemLp (fun t => inputProjection s m i j (f t)) ∞ (volume.restrict (Set.Icc a b)) :=
  hf.continuousLinearMap_comp (inputProjection s m i j)

theorem inputProjection_time_norm_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i j : Fin 3) :
    timeLInfinity a b (fun t => inputProjection s m i j (f t)) ≤ timeLInfinity a b f := by
  simpa only [one_mul] using timeLInfinity_map_bound (by norm_num : (0 : ℝ) ≤ 1)
    (inputProjection s m i j) (fun v => by simpa only [one_mul] using inputProjection_norm_le s m i j v) hf

theorem inputProjection_timeX_le {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i j : Fin 3) :
    timeXNorm a b (fun t => inputProjection 0 m i j (f t)) (fun t => inputProjection (-pStar) m i j (df t)) ≤
      timeXNorm a b f df :=
  add_le_add (inputProjection_time_norm_le hf m i j) (inputProjection_time_norm_le hdf m i j)

theorem inputProjection_weak {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : WeakTimeDerivative a b (fun t => (f t).val) (fun t => (df t).val)) (m : ℕ) (i j : Fin 3) :
    WeakTimeDerivative a b (fun t => (inputProjection 0 m i j (f t)).val)
      (fun t => (inputProjection (-pStar) m i j (df t)).val) := by
  unfold inputProjection
  split_ifs
  · simpa only [cutoffMap_val] using hf.cutoff m
  · simpa only [highCutoffMap_val] using hf.highCutoff m
  · exact hf

theorem inputProjection_high_negative {a b : ℝ} {f : ℝ → Sobolev 0}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i : Fin 3) :
    timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (inputProjection 0 m i i (f t))) ≤
      weight (-pStar) (m : ℤ) * timeLInfinity a b f := by
  simp only [inputProjection, lt_irrefl, if_false, if_true]
  exact time_highCutoff_negative_bound hf m

theorem fin_three_selected_mul_others (x : Fin 3 → ℝ) (i : Fin 3) :
    x i * (∏ j : Fin 3, if j = i then 1 else x j) = ∏ j : Fin 3, x j := by
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

/-- The cited dynamic estimate applied to one of the three internally
specified high-input terms. The high-frequency gain is proved from projection
norms and every time-derivative hypothesis is preserved. -/
theorem one_high_cubic_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 1 →
      ∀ f : Fin 3 → ℝ → Sobolev 0, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
        ∀ m : ℕ, ∀ i : Fin 3,
          InSobolev 0 (CIntegral a b (fun t => (inputProjection 0 m i 0 (f 0 t)).val)
            (fun t => (inputProjection 0 m i 1 (f 1 t)).val) (fun t => (inputProjection 0 m i 2 (f 2 t)).val)) ∧
          hNorm 0 (CIntegral a b (fun t => (inputProjection 0 m i 0 (f 0 t)).val)
            (fun t => (inputProjection 0 m i 1 (f 1 t)).val) (fun t => (inputProjection 0 m i 2 (f 2 t)).val)) ≤
            C * (b - a) * (∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
              C * weight (-pStar) (m : ℤ) * (∏ j : Fin 3, timeLInfinity a b (f j)) := by
  obtain ⟨C, hC, hb⟩ := normalized_dynamic_trilinear externalTrilinear (by norm_num : (0 : ℝ) < 1) le_rfl
  refine ⟨C, hC, ?_⟩
  intro a b ha hab hlen f df hf hdf hd m i
  let F : Fin 3 → ℝ → Sobolev 0 := fun j t => inputProjection 0 m i j (f j t)
  let D : Fin 3 → ℝ → Sobolev (-pStar) := fun j t => inputProjection (-pStar) m i j (df j t)
  obtain ⟨hmem, hn⟩ := hb a b ha hab hlen F D
    (fun j => inputProjection_memLp (hf j) m i j)
    (fun j => inputProjection_memLp (hdf j) m i j)
    (fun j => inputProjection_weak (hd j) m i j)
  have hPX : (∏ j : Fin 3, timeXNorm a b (F j) (D j)) ≤ ∏ j : Fin 3, timeXNorm a b (f j) (df j) := by
    apply Finset.prod_le_prod
    · intro j _
      exact timeXNorm_nonneg _ _ _ _
    · intro j _
      exact inputProjection_timeX_le (hf j) (hdf j) m i j
  have hPO : (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (F j)) ≤
      ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j) := by
    apply Finset.prod_le_prod
    · intro j _
      split_ifs
      · norm_num
      · exact timeLInfinity_nonneg _ _ _
    · intro j _
      split_ifs
      · exact le_rfl
      · exact inputProjection_time_norm_le (hf j) m i j
  have hNi := inputProjection_high_negative (hf i) m i
  have hPO0 : 0 ≤ ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (F j) := by
    apply Finset.prod_nonneg
    intro j _
    split_ifs
    · norm_num
    · exact timeLInfinity_nonneg _ _ _
  refine ⟨hmem, (hn i).trans ?_⟩
  calc
    _ ≤ C * (b - a) * (∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
        C * (weight (-pStar) (m : ℤ) * timeLInfinity a b (f i)) *
          (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) :=
      add_le_add (mul_le_mul_of_nonneg_left hPX (mul_nonneg hC.le (sub_nonneg.mpr hab)))
        (mul_le_mul (mul_le_mul_of_nonneg_left hNi hC.le) hPO hPO0
          (mul_nonneg hC.le (mul_nonneg (weight_pos _ _).le (timeLInfinity_nonneg _ _ _))))
    _ = _ := by
      rw [← mul_assoc C (weight (-pStar) (m : ℤ)) (timeLInfinity a b (f i)),
        mul_assoc (C * weight (-pStar) (m : ℤ)),
        fin_three_selected_mul_others (fun j => timeLInfinity a b (f j)) i]

end KdV
