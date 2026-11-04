import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The internal normal-form regularity condition implies the actual weak time
derivative required by the cited trilinear estimate. -/
theorem RegularFourierPath.weakTimeDerivative {a b : ℝ} (hab : a ≤ b)
    {f df : ℝ → Fourier} (hf : RegularFourierPath a b f df) : WeakTimeDerivative a b f df := by
  intro k φ hφ _ hsupp
  have ha : φ a = 0 := by
    by_contra ha
    have hm : a ∈ Function.support φ := ha
    exact (lt_irrefl a) (hsupp hm).1
  have hb : φ b = 0 := by
    by_contra hb
    have hm : b ∈ Function.support φ := hb
    exact (lt_irrefl b) (hsupp hm).2
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcprod : ContinuousOn (fun t : ℝ => (φ t : ℂ) * f t k) (Set.Icc a b) :=
    hcφ.continuousOn.mul (hf.continuous k)
  have hc1 : ContinuousOn (fun t : ℝ => ((deriv φ t : ℝ) : ℂ) * f t k) (Set.Icc a b) :=
    hcDφ.continuousOn.mul (hf.continuous k)
  have hc2 : ContinuousOn (fun t : ℝ => (φ t : ℂ) * df t k) (Set.Icc a b) :=
    hcφ.continuousOn.mul (hf.derivative_continuous k)
  have hi1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hc1
  have hi2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hc2
  have hd (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun r : ℝ => (φ r : ℂ) * f r k)
        (((deriv φ t : ℝ) : ℂ) * f t k + (φ t : ℂ) * df t k) t :=
    ((hφdiff t).hasDerivAt.ofReal_comp).mul (hf.hasDerivAt t ht k)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcprod hd (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  simp only [ha, hb, Complex.ofReal_zero, zero_mul, sub_self] at hFTC
  linear_combination hFTC

/-- Pointwise bounds on a Sobolev-valued path imply the corresponding source
essential bound. No continuity or value-at-endpoints convention is hidden here. -/
theorem sourceLInfinity_le_of_bound {s A : ℝ} (hA : 0 ≤ A) (a b : ℝ)
    (f : ℝ → Sobolev s) (hf : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖f t‖ ≤ A) :
    sourceLInfinity a b f ≤ sourceNormalization * A := by
  have he : eLpNorm f ∞ (volume.restrict (Set.Icc a b)) ≤ ENNReal.ofReal A := by
    simpa only [eLpNorm_exponent_top] using eLpNormEssSup_le_of_ae_bound hf
  unfold sourceLInfinity
  apply mul_le_mul_of_nonneg_left _ sourceNormalization_pos.le
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ENNReal.toReal_ofReal hA] using ht

end KdV
