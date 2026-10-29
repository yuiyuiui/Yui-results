import KdVBridge
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

/-- The cited source's Galerkin equation (4.1), with its original phase sign.
The projection belongs to the source's exact-flow construction, not the numerical
method. Classical differentiation is required on the interval interior, with
continuity on the closed interval supplied in the a priori theorem's hypotheses. -/
def SourceGalerkinODE (m : ℕ) (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Ioo 0 T, ∀ k : ℤ,
    HasDerivAt (fun r : ℝ => v r k)
      ((1 / 2 : ℂ) * cutoff m (B (-t) (cutoff m (v t)) (cutoff m (v t))) k) t

/-- Explicit external premise: the a priori estimate clause (4.13) of
Babin–Ilyin–Titi Theorem 4.2, arXiv:0910.1389v2. The dependence on the *actual*
initial homogeneous norm is represented by equality to `r`, with the constant
chosen before the datum and the Galerkin index. This does not assume a bound
uniform over all data of norm at most `r`; that implication remains internal work.
The theorem's unused second-normal-form identity (4.10) is not asserted here. -/
def BITGalerkinEstimate : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ M₀ : ℝ, 0 ≤ M₀ → ∀ T : ℝ, 0 < T → ∀ r : ℝ, 0 ≤ r →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∀ f : Fourier, ∀ v : ℝ → Fourier,
      RealValued f → InHomSobolev s f → homogeneousNorm s f = r → homogeneousNorm 0 f ≤ M₀ →
      HomSobolevContinuousOn s T v → (∀ t ∈ Set.Icc 0 T, RealValued (v t)) →
      SourceGalerkinODE m T f v → ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A

end KdV
