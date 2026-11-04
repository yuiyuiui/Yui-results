import SmoothPhysicalEquation
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

theorem spatial_hasDerivWithinAt {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (spatialPath hT hAll n)
      (physicalVectorField n (spatialPath hT hAll (n + 3) t)) (Set.Icc 0 T) t := by
  let F := fun r => physicalVectorField n (spatialPath hT hAll (n + 3) r)
  have hc : Continuous F := (continuous_physicalVectorField n).comp (continuous_spatialPath hT hAll (n + 3))
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hG := (hasDerivAt_const t (spatialPath hT hAll n 0)).add hd
  simp only [zero_add] at hG
  exact hG.hasDerivWithinAt.congr_of_mem (fun r hr => spatial_physical_integral hT hu hAll n hr) ht

/-- Infinite spatial Sobolev regularity and the actual autonomous KdV equation
 imply all time derivatives, including one-sided boundary regularity. -/
theorem all_regular_coefficient_contDiffOn {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 < T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) :
    ∀ k : ℤ, ∀ m : ℕ, ContDiffOn ℝ m (fun t => u t k) (Set.Icc 0 T) := by
  have hD (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) := spatial_hasDerivWithinAt hT.le hu hAll n ht
  have hSmooth : ∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ m (spatialPath hT.le hAll n) (Set.Icc 0 T) := by
    intro m
    induction m with
    | zero =>
      intro n
      exact contDiffOn_zero.mpr (continuous_spatialPath hT.le hAll n).continuousOn
    | succ m ih =>
      intro n
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
      refine ⟨fun t ht => (hD n t ht).differentiableWithinAt, by simp, ?_⟩
      have hF := (contDiff_physicalVectorField n m).comp_contDiffOn (ih (n + 3))
      apply hF.congr
      intro t ht
      exact (hD n t ht).derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
  intro k m
  have h := ((coefficientMap (((0 + 1 : ℕ) : ℝ)) k).restrictScalars ℝ).contDiff.comp_contDiffOn (hSmooth m 0)
  apply h.congr
  intro t ht
  change u t k = (spatialPath hT.le hAll 0 t).val k
  rw [spatialPath_val_on hT.le hAll 0 ht]

theorem all_regular_is_smooth {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 < T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) :
    SmoothSolution T f u :=
  ⟨hu.2.1, hAll, all_regular_coefficient_contDiffOn hT hu hAll, hu.2.2⟩

end KdV
