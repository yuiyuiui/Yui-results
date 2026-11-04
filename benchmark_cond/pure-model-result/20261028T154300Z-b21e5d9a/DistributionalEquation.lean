import RoughCoefficientDerivative
import SmoothPhysicalEquation
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The time-distributional identity for every integer spatial Fourier mode.
 The negative Sobolev realization below supplies its vector-valued form. -/
def DistributionalKdV (T : ℝ) (u : ℝ → Fourier) : Prop :=
  WeakTimeDerivative 0 T u (fun t => physicalRHS (u t))

theorem weakTimeDerivative_of_coefficient_calculus {a b : ℝ} (hab : a ≤ b)
    {f df : ℝ → Fourier}
    (hc : ∀ k : ℤ, ContinuousOn (fun t => f t k) (Set.Icc a b))
    (hdc : ∀ k : ℤ, ContinuousOn (fun t => df t k) (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ, HasDerivAt (fun r => f r k) (df t k) t) :
    WeakTimeDerivative a b f df := by
  intro k φ hφ _ hsupp
  have ha : φ a = 0 := by
    by_contra h
    exact (lt_irrefl a) (hsupp h).1
  have hb : φ b = 0 := by
    by_contra h
    exact (lt_irrefl b) (hsupp h).2
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hφdiff := hφ.differentiable (by simp)
  have hprod := hcφ.continuousOn.mul (hc k)
  have hi1 : IntervalIntegrable (fun t => ((deriv φ t : ℝ) : ℂ) * f t k) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hcDφ.continuousOn.mul (hc k))
  have hi2 : IntervalIntegrable (fun t => (φ t : ℂ) * df t k) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hcφ.continuousOn.mul (hdc k))
  have hder (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun r => (φ r : ℂ) * f r k)
        (((deriv φ t : ℝ) : ℂ) * f t k + (φ t : ℂ) * df t k) t :=
    ((hφdiff t).hasDerivAt.ofReal_comp).mul (hd t ht k)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hprod hder (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  change (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) * f t k) +
    (∫ t : ℝ in a..b, (φ t : ℂ) * df t k) = (φ b : ℂ) * f b k - (φ a : ℂ) * f a k at hFTC
  simp only [ha, hb, Complex.ofReal_zero, zero_mul, sub_self] at hFTC
  linear_combination hFTC

theorem kdv_solution_distributional {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : DistributionalKdV T u := by
  let U := sobolevExtension hT u (hu.1.of_le hγ)
  have hUC : Continuous U := continuous_sobolevExtension hT _
  have hUv (t : ℝ) (ht : t ∈ Set.Icc 0 T) : (U t).val = u t := sobolevExtension_val_on hT _ ht
  apply weakTimeDerivative_of_coefficient_calculus hT
  · intro k
    have h := (coefficientMap 0 k).continuous.comp hUC
    apply h.continuousOn.congr
    intro t ht
    change u t k = (U t).val k
    rw [hUv t ht]
  · intro k
    have hP := continuous_productCoefficientMap k hUC hUC
    have hC := ((continuous_const (y := Complex.I * (k : ℂ) ^ 3)).mul ((coefficientMap 0 k).continuous.comp hUC)).add
      ((continuous_const (y := (1 / 2 : ℂ) * (Complex.I * (k : ℂ)))).mul hP)
    have hR : Continuous (fun t : ℝ => physicalRHS (U t).val k) := by
      simp only [physicalRHS_coefficient]
      exact hC
    apply hR.continuousOn.congr
    intro t ht
    dsimp only
    rw [hUv t ht]
  · intro t ht k
    rw [physicalRHS_coefficient]
    exact rough_physical_coefficient_hasDerivAt hT hγ hu ht k

end KdV
