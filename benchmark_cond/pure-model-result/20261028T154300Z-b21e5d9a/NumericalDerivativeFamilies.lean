import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def numericalDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) : Sobolev 1 :=
  localDerivativeBundled externalStep τ hτ j t (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)

theorem numericalDerivativeFamily_val (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) :
    (numericalDerivativeFamily externalStep τ hτ f hfr hfm j t).val =
      localInterpolationDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val := rfl

theorem continuous_numericalDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) :
    Continuous (numericalDerivativeFamily externalStep τ hτ f hfr hfm j) :=
  continuous_localDerivativeBundled externalStep τ hτ j _ _ _

def numericalResidualDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) : Sobolev 0 :=
  let fj := twistedNumericalBundled τ f j
  let hjr := twistedNumericalBundled_real τ hfr j
  let hjm := twistedNumericalBundled_meanZero τ hfm j;
  -BOneBundled t (defectBundled externalStep τ hτ j t fj hjr hjm) (frozenZBundled ((j : ℝ) * τ) t fj) -
    (1 / 2 : ℂ) • BOneBundled t (defectBundled externalStep τ hτ j t fj hjr hjm)
      (defectBundled externalStep τ hτ j t fj hjr hjm) -
    ((τ⁻¹ : ℝ) : ℂ) • inclusionMap 0 1 (by norm_num)
      (endpointCorrectionBundled externalStep τ hτ j fj hjr hjm)

theorem numericalResidualDerivativeFamily_val (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) :
    (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t).val =
      localResidualDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val := by
  unfold numericalResidualDerivativeFamily
  dsimp only
  change -B t (defectBundled externalStep τ hτ j t _ _ _).val (frozenZBundled _ t _).val -
    (1 / 2 : ℂ) • B t (defectBundled externalStep τ hτ j t _ _ _).val
      (defectBundled externalStep τ hτ j t _ _ _).val - _ = _
  rw [defectBundled_val, frozenZBundled_val]
  rfl

theorem continuous_numericalResidualDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) :
    Continuous (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j) := by
  have hC := (continuous_residual_integrands externalStep τ hτ j (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)).1
  have hQ := (continuous_residual_integrands externalStep τ hτ j (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)).2
  unfold numericalResidualDerivativeFamily
  dsimp only
  fun_prop

/-- The derivative callback used by the global error normal form is verified
for the actual concatenated numerical interpolation. -/
theorem numerical_derivative_family_correct (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (globalInterpolation externalStep τ hτ f hfr hfm k r).val m)
      ((numericalDerivativeFamily externalStep τ hτ f hfr hfm j t).val m) t := by
  rw [numericalDerivativeFamily_val]
  exact globalInterpolation_hasDerivAt_on_step externalStep τ hτ f hfr hfm hjk ht m

/-- The perturbed equation callback is also proved, including at both step
endpoints. It is not an assumed numerical differential equation. -/
theorem numerical_derivative_family_equation (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    (numericalDerivativeFamily externalStep τ hτ f hfr hfm j t).val =
      (1 / 2 : ℂ) • B t (globalInterpolation externalStep τ hτ f hfr hfm k t).val
        (globalInterpolation externalStep τ hτ f hfr hfm k t).val +
      (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t).val := by
  have hv : (globalInterpolation externalStep τ hτ f hfr hfm k t).val =
      localInterpolation τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val :=
    (congrArg Sobolev.val (globalInterpolation_on_step externalStep τ hτ f hfr hfm hjk ht)).trans
      (interpolationPiece_val externalStep τ hτ f hfr hfm j t)
  rw [numericalDerivativeFamily_val, numericalResidualDerivativeFamily_val, hv]
  have hY : InSobolev 0 (interpolationRemainder τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val) := by
    rw [← defectBundled_val externalStep τ hτ j t (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)]
    exact (defectBundled externalStep τ hτ j t (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)).property.of_le (by norm_num)
  exact localInterpolation_perturbation_identity ((twistedNumericalBundled τ f j).property.of_le (by norm_num)) hY

end KdV
