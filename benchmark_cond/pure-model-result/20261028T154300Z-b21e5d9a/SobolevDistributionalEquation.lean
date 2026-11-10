import DistributionalEquation
import DistributionalSobolevField
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem sobolev_val_neg {s : ℝ} (f : Sobolev s) : (-f).val = -f.val := rfl

/-- The equation as a time distribution with values in H^-3(T), not merely
 a list of assigned derivative values. All terms use the full Fourier product. -/
def SobolevDistributionalKdV (T : ℝ) (u : ℝ → Fourier) : Prop :=
  ∃ U : ℝ → Sobolev 0, ∃ F : ℝ → Sobolev (-3), Continuous U ∧ Continuous F ∧
    (∀ t ∈ Set.Icc 0 T, (U t).val = u t ∧ (F t).val = physicalRHS (u t)) ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
      Function.support φ ⊆ Set.Ioo 0 T →
        (∫ t : ℝ in (0 : ℝ)..T, (((deriv φ t : ℝ) : ℂ)) • inclusionMap (-3) 0 (by norm_num) (U t)) =
          -(∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) • F t)

theorem kdv_solution_sobolev_distributional {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : SobolevDistributionalKdV T u := by
  let U := sobolevExtension hT u (hu.1.of_le hγ)
  let F := fun t => physicalRoughField (U t)
  have hUC : Continuous U := continuous_sobolevExtension hT _
  have hFC : Continuous F := continuous_physicalRoughField.comp hUC
  have hUv (t : ℝ) (ht : t ∈ Set.Icc 0 T) : (U t).val = u t := sobolevExtension_val_on hT _ ht
  have hFv (t : ℝ) (ht : t ∈ Set.Icc 0 T) : (F t).val = physicalRHS (u t) := by
    rw [physicalRoughField_val, hUv t ht]
  refine ⟨U, F, hUC, hFC, fun t ht => ⟨hUv t ht, hFv t ht⟩, ?_⟩
  intro φ hφ hsupp hsupport
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hi1 : IntervalIntegrable (fun t => ((deriv φ t : ℝ) : ℂ) • inclusionMap (-3) 0 (by norm_num) (U t)) volume 0 T :=
    (hcDφ.smul ((inclusionMap (-3) 0 (by norm_num)).continuous.comp hUC)).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t => (φ t : ℂ) • F t) volume 0 T :=
    (hcφ.smul hFC).intervalIntegrable 0 T
  apply Sobolev.ext
  rw [sobolev_integral_val hi1, sobolev_val_neg, sobolev_integral_val hi2]
  funext k
  change (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * (U t).val k) =
    -(∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * (F t).val k)
  have hI1 : (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * (U t).val k) =
      ∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * u t k := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [hUv t ht]
  have hI2 : (∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * (F t).val k) =
      ∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * physicalRHS (u t) k := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [hFv t ht]
  rw [hI1, hI2]
  exact kdv_solution_distributional hT hγ hu k φ hφ hsupp hsupport

end KdV
