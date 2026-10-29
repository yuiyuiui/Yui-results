import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def timeLInfinity {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) : ℝ :=
  (eLpNorm f ∞ (volume.restrict (Set.Icc a b))).toReal

def timeXNorm (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) : ℝ :=
  timeLInfinity a b f + timeLInfinity a b df

theorem inclusionMap_self_apply (s : ℝ) (h : s ≤ s) (f : Sobolev s) :
    inclusionMap s s h f = f := by apply Sobolev.ext; rfl

theorem source_zero_time_norm (a b : ℝ) (f : ℝ → Sobolev 0) :
    sourceLInfinityZero le_rfl a b f = sourceNormalization * timeLInfinity a b f := by
  unfold sourceLInfinityZero sourceLInfinity timeLInfinity
  simp only [inclusionMap_self_apply]

theorem source_x_time_norm (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) :
    sourceXNorm le_rfl a b f df = sourceNormalization * timeXNorm a b f df := by
  rw [sourceXNorm, source_zero_time_norm]
  simp only [sourceLInfinity, timeLInfinity, timeXNorm]
  ring

theorem fin_three_product_scalar (κ : ℝ) (x : Fin 3 → ℝ) :
    (∏ j : Fin 3, κ * x j) = κ ^ 3 * ∏ j : Fin 3, x j := by
  simp only [Fin.prod_univ_three]
  ring

theorem fin_three_product_except_scalar (κ : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    (∏ j : Fin 3, if j = i then 1 else κ * x j) =
      κ ^ 2 * ∏ j : Fin 3, if j = i then 1 else x j := by
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

/-- The dynamic source trilinear estimate, normalized on the paper's torus.
Every time norm and weak derivative is retained. Only the fixed spatial measure
factor changes the constant; no interpolation or stability estimate is imported. -/
theorem normalized_dynamic_trilinear (externalTrilinear : LiWuTrilinearEstimate)
    {H : ℝ} (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f : Fin 3 → ℝ → Sobolev 0, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
          InSobolev 0 (CIntegral a b (fun t => (f 0 t).val)
            (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ∧
          ∀ i : Fin 3,
            hNorm 0 (CIntegral a b (fun t => (f 0 t).val)
              (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ≤
              C * (b - a) * (∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
              C * timeLInfinity a b (fun t => inclusionMap (-pStar) 0
                (by dsimp [pStar]; norm_num) (f i t)) *
                (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) := by
  obtain ⟨C, hC, hb⟩ := externalTrilinear.dynamic H hH 0 le_rfl (by norm_num)
  refine ⟨C * sourceNormalization ^ 2, mul_pos hC (sq_pos_of_pos sourceNormalization_pos), ?_⟩
  intro a b ha hab hlength f df hf hdf hd
  obtain ⟨hmem, hbound⟩ := hb a b ha hab hlength f df hf hdf hd
  refine ⟨hmem, ?_⟩
  intro i
  have h := hbound i
  simp_rw [source_x_time_norm, source_zero_time_norm, fin_three_product_scalar,
    fin_three_product_except_scalar] at h
  change sourceNormalization * hNorm 0 _ ≤ C * (b - a) *
    (sourceNormalization ^ 3 * ∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
    C * (sourceNormalization * timeLInfinity a b (fun t => inclusionMap (-pStar) 0
      (by dsimp [pStar]; norm_num) (f i t))) *
    (sourceNormalization ^ 2 * ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) at h
  apply (mul_le_mul_iff_right₀ sourceNormalization_pos).mp
  calc
    _ ≤ _ := h
    _ = _ := by ring

end KdV
