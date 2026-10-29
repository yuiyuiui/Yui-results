import PathIntervalTools
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- A useful specialization of the dynamic trilinear estimate: two frozen
inputs and a moving defect, with the small negative norm on the moving slot. -/
theorem dynamic_constant_pair_bound (externalTrilinear : LiWuTrilinearEstimate)
    {H : ℝ} (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f : Sobolev 1, ∀ Y : ℝ → Sobolev 0, ∀ dY : ℝ → Sobolev (-pStar),
        MemLp Y ∞ (volume.restrict (Set.Icc a b)) →
        MemLp dY ∞ (volume.restrict (Set.Icc a b)) →
        WeakTimeDerivative a b (fun t => (Y t).val) (fun t => (dY t).val) →
        ∀ M A B : ℝ, 0 ≤ M → 0 ≤ A → 0 ≤ B → hNorm 0 f.val ≤ M →
          timeXNorm a b Y dY ≤ A →
          timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤ B →
          InSobolev 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)) ∧
          hNorm 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)) ≤
            C * (b - a) * M ^ 2 * A + C * B * M ^ 2 := by
  obtain ⟨C, hC, hb⟩ := normalized_dynamic_trilinear externalTrilinear hH
  refine ⟨C, hC, ?_⟩
  intro a b ha hab hlen f Y dY hY hdY hweak M A B hM hA hB hfM hXA hNB
  let F : ℝ → Sobolev 0 := fun _ => inclusionMap 0 1 (by norm_num) f
  let Z : ℝ → Sobolev (-pStar) := fun _ => 0
  have hF : MemLp F ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc continuousOn_const
  have hZ : MemLp Z ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc continuousOn_const
  have hW : WeakTimeDerivative a b (fun t => (F t).val) (fun t => (Z t).val) :=
    (constant_regular a b f).weakTimeDerivative hab
  let fs : Fin 3 → ℝ → Sobolev 0 := ![F, F, Y]
  let ds : Fin 3 → ℝ → Sobolev (-pStar) := ![Z, Z, dY]
  obtain ⟨hmem, hbound⟩ := hb a b ha hab hlen fs ds
    (by intro j; fin_cases j <;> first | exact hF | exact hY)
    (by intro j; fin_cases j <;> first | exact hZ | exact hdY)
    (by intro j; fin_cases j <;> first | exact hW | exact hweak)
  have hconst : timeLInfinity a b F ≤ M := timeLInfinity_le_of_bound hM F (by
    intro t _
    rw [sobolev_norm]
    exact hfM)
  have hzero : timeLInfinity a b Z = 0 := by
    change (eLpNorm (0 : ℝ → Sobolev (-pStar)) ∞ (volume.restrict (Set.Icc a b))).toReal = 0
    rw [eLpNorm_zero, ENNReal.toReal_zero]
  have hconstX : timeXNorm a b F Z ≤ M := by simpa only [timeXNorm, hzero, add_zero] using hconst
  have hprod := hbound 2
  simp [fs, ds, Fin.prod_univ_three] at hprod
  refine ⟨hmem, hprod.trans ?_⟩
  have hF0 := timeLInfinity_nonneg a b F
  have hFX0 := timeXNorm_nonneg a b F Z
  have hYX0 := timeXNorm_nonneg a b Y dY
  have hYN0 := timeLInfinity_nonneg a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t))
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  calc
    _ ≤ C * (b - a) * (M * M * A) + C * B * (M * M) := by gcongr
    _ = _ := by ring

end KdV
