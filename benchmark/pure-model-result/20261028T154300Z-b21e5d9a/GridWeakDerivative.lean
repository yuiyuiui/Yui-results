import GridPathTools
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Continuous paths with stepwise classical derivatives have the actual
distributional derivative given by the concatenated pieces, even when those
pieces jump at grid points. -/
theorem grid_weakTimeDerivative (τ : ℝ) (hτ : 0 < τ) (k : ℕ)
    (f : ℝ → Sobolev 1) (df : ℕ → ℝ → Sobolev 1)
    (hf : Continuous f) (hdf : ∀ j, Continuous (df j))
    (hfd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun r : ℝ => (f r).val m) ((df j t).val m) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    WeakTimeDerivative a b (fun t => (f t).val) (fun t => (concatenate τ df k t).val) := by
  intro m φ hφ _ hsupp
  have hφa : φ a = 0 := by
    by_contra ha'
    exact (lt_irrefl a) (hsupp (show a ∈ Function.support φ from ha')).1
  have hφb : φ b = 0 := by
    by_contra hb'
    exact (lt_irrefl b) (hsupp (show b ∈ Function.support φ from hb')).2
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hfc : Continuous (fun t : ℝ => (f t).val m) :=
    (coefficientMap 1 m).continuous.comp hf
  have hcprod : Continuous (fun t : ℝ => (φ t : ℂ) * (f t).val m) := hcφ.mul hfc
  have hi1 : IntervalIntegrable (fun t : ℝ => ((deriv φ t : ℝ) : ℂ) * (f t).val m) volume a b :=
    (hcDφ.mul hfc).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t : ℝ => (φ t : ℂ) * (concatenate τ df k t).val m) volume a b := by
    have hc (j : ℕ) : Continuous (fun t : ℝ => (φ t : ℂ) * (df j t).val m) :=
      hcφ.mul ((coefficientMap 1 m).continuous.comp (hdf j))
    have hi := intervalIntegrable_concatenate τ (fun j t => (φ t : ℂ) * (df j t).val m)
      (fun j => (hc j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => (φ t : ℂ) * (df j t).val m) k =
        (fun t => (φ t : ℂ) * (concatenate τ df k t).val m) := by
      funext t
      exact concatenate_map τ df (fun r v => (φ r : ℂ) * v.val m) k t
    rwa [hmap] at hi
  have hd : ∀ t ∈ Set.Ioo a b \ Set.range (fun j : ℕ => (j : ℝ) * τ),
      HasDerivAt (fun r : ℝ => (φ r : ℂ) * (f r).val m)
        (((deriv φ t : ℝ) : ℂ) * (f t).val m + (φ t : ℂ) * (concatenate τ df k t).val m) t := by
    intro t ht
    have hnot : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => ht.2 ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k
      (lt_of_le_of_lt ha ht.1.1) (lt_of_lt_of_le ht.1.2 hb) hnot
    rw [concatenate_on_open_step hτ.le df hj hstep]
    exact ((hφdiff t).hasDerivAt.ofReal_comp).mul (hfd j hj t hstep m)
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ => (φ t : ℂ) * (f t).val m)
    (fun t : ℝ => ((deriv φ t : ℝ) : ℂ) * (f t).val m + (φ t : ℂ) * (concatenate τ df k t).val m)
    hab (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)) hcprod.continuousOn hd (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  simp only [hφa, hφb, Complex.ofReal_zero, zero_mul, sub_self] at hFTC
  linear_combination hFTC

end KdV
