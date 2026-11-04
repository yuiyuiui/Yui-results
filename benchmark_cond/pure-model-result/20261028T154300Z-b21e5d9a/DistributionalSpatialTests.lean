import SobolevDistributionalEquation
import SobolevDistributionPair
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The H^-3-valued distribution identity can be tested against every H³
 spatial test function, in particular every smooth periodic test function. -/
theorem kdv_solution_distributional_spatial_tests {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) :
    ∃ U : ℝ → Sobolev 0, ∃ F : ℝ → Sobolev (-3), Continuous U ∧ Continuous F ∧
      (∀ t ∈ Set.Icc 0 T, (U t).val = u t ∧ (F t).val = physicalRHS (u t)) ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
        Function.support φ ⊆ Set.Ioo 0 T → ∀ ψ : Sobolev 3,
        (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) *
          distributionTest 3 ψ (inclusionMap (-3) 0 (by norm_num) (U t))) =
          -(∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * distributionTest 3 ψ (F t)) := by
  obtain ⟨U, F, hUC, hFC, hval, hWeak⟩ := kdv_solution_sobolev_distributional hT hγ hu
  refine ⟨U, F, hUC, hFC, hval, ?_⟩
  intro φ hφ hsupp hsupport ψ
  let L := distributionTest 3 ψ
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hi1 : IntervalIntegrable (fun t => ((deriv φ t : ℝ) : ℂ) • inclusionMap (-3) 0 (by norm_num) (U t)) volume 0 T :=
    (hcDφ.smul ((inclusionMap (-3) 0 (by norm_num)).continuous.comp hUC)).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t => (φ t : ℂ) • F t) volume 0 T := (hcφ.smul hFC).intervalIntegrable 0 T
  have h := congrArg L (hWeak φ hφ hsupp hsupport)
  rw [L.map_neg, ← L.intervalIntegral_comp_comm hi1, ← L.intervalIntegral_comp_comm hi2] at h
  simpa only [map_smul, smul_eq_mul] using h

end KdV
