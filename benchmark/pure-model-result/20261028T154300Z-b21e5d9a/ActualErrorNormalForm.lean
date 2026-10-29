import ErrorNormalForm
import ExactPathRegularity
import NumericalDerivativeFamilies
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Equation (31) for the actual exact Duhamel solution and the actual
numerical interpolation. All derivative and equation callbacks of the internal
grid normal form are discharged, rather than imposed as new source premises. -/
theorem actual_error_normal_form (externalStep : LiWuStepIdentity)
    {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (m : ℤ) :
    let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
    let V := globalInterpolation externalStep τ hτ f hfr hfm k
    let e : ℝ → Sobolev 1 := fun t => v t - V t
    let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
    (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
      (1 / 3 : ℂ) * (J b (e b).val (g b).val m - J a (e a).val (g a).val m) -
      (1 / 3 : ℂ) * CIntegral a b (fun t => (e t).val) (fun t => (g t).val) (fun t => (V t).val) m -
      (1 / 6 : ℂ) * CIntegral a b (fun t => (v t).val) (fun t => (v t).val) (fun t => (e t).val) m +
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b,
        J t (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t).val (V t).val m := by
  dsimp only
  let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let dv : ℕ → ℝ → Sobolev 1 := fun _ t => exactTwistedDerivative hT hu t
  let dV := numericalDerivativeFamily externalStep τ hτ f hfr hfm
  let r := numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm
  have hvC : Continuous v := (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
  have hVC : Continuous V := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  have hdvC (j : ℕ) : Continuous (dv j) := continuous_exactTwistedDerivative hT hu
  have hdVC (j : ℕ) : Continuous (dV j) := continuous_numericalDerivativeFamily externalStep τ hτ f hfr hfm j
  have hrC (j : ℕ) : Continuous (r j) := continuous_numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j
  have hvd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (v s).val l) ((dv j t).val l) t := by
    intro j hj t ht l
    have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg j) hτ.le) ht.1
    have hbound : ((j + 1 : ℕ) : ℝ) * τ ≤ ((k + 1 : ℕ) : ℝ) * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hj) hτ.le
    have htT : t < T := lt_of_lt_of_le ht.2 (hbound.trans hTotal)
    exact extendedTwistedPath_hasDerivAt hT hu ⟨ht0, htT⟩ l
  have hVd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (V s).val l) ((dV j t).val l) t := by
    intro j hj t ht l
    exact numerical_derivative_family_correct externalStep τ hτ f hfr hfm hj ht l
  have hvEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dv j t).val = (1 / 2 : ℂ) • B t (v t).val (v t).val := by
    intro j _ t _
    exact exactTwistedDerivative_equation hT hu t
  have hVEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dV j t).val = (1 / 2 : ℂ) • B t (V t).val (V t).val + (r j t).val := by
    intro j hj t ht
    exact numerical_derivative_family_equation externalStep τ hτ f hfr hfm hj ht
  have hvm (t : ℝ) : MeanZero (v t).val := extendedTwistedPath_meanZero hT hu t
  have hVm (t : ℝ) : MeanZero (V t).val := globalInterpolation_meanZero externalStep τ hτ f hfr hfm k t
  exact error_normal_form_grid τ hτ k v V dv dV r hvC hVC hdvC hdVC hrC hvd hVd hvEq hVEq hvm hVm ha hab hb m

end KdV
