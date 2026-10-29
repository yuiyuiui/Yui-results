import HigherSobolev
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

/-- An algebra property, instantiated below by an internal proof. -/
def SobolevAlgebra (s : ℝ) : Prop :=
  ∀ f g : Fourier, InSobolev s f → InSobolev s g → InSobolev s (product f g)

theorem integer_sobolev_algebra (n : ℕ) : SobolevAlgebra ((n + 1 : ℕ) : ℝ) :=
  fun _ _ hf hg => integer_product_inSobolev n hf hg

theorem quadratic_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (quadratic τ f) := by
  have hd := inverseDerivative_inSobolev_same hf
  have ha := airy_inSobolev hd τ
  exact ((removeMean_inSobolev (hAlg _ _ ha ha)).smul (1 / 6 : ℂ)).sub
    ((airy_inSobolev (removeMean_inSobolev (hAlg _ _ hd hd)) τ).smul (1 / 6 : ℂ))

theorem cubicBoundary_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ r : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (cubicBoundary τ r f) := by
  have ha := airy_inSobolev (inverseDerivative_inSobolev_same hf) r
  exact airy_inSobolev (inverseDerivative_inSobolev_same (hAlg _ _ (hAlg _ _ ha ha) ha)) (τ - r)

theorem lastBoundary_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ r : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (lastBoundary τ r f) := by
  have hF := quadratic_in_algebra hAlg τ hf
  have ha := airy_inSobolev (inverseDerivative_inSobolev_same
    (inverseDerivative_inSobolev_same hF)) (r - τ)
  have hb := airy_inSobolev (inverseDerivative_inSobolev_same hf) r
  exact airy_inSobolev (inverseDerivative_inSobolev_same
    (inverseDerivative_inSobolev_same (hAlg _ _ ha hb))) (τ - r)

theorem cubicCorrection_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (cubicCorrection τ f) := by
  have hF := quadratic_in_algebra hAlg τ hf
  have hfirst := (removeMean_inSobolev (hAlg _ _
    (airy_inSobolev (inverseDerivative_inSobolev_same hf) τ)
    (inverseDerivative_inSobolev_same hF))).smul (1 / 3 : ℂ)
  have hsecond := (airy_inSobolev (inverseDerivative_inSobolev_same hf) τ).smul
    ((τ : ℂ) / 9 * mean (product f f))
  have hthird := ((cubicBoundary_in_algebra hAlg τ τ hf).sub
    (cubicBoundary_in_algebra hAlg τ 0 hf)).smul (1 / 54 : ℂ)
  have hfourth := ((lastBoundary_in_algebra hAlg τ τ hf).sub
    (lastBoundary_in_algebra hAlg τ 0 hf)).smul (1 / (27 * (τ : ℂ)))
  exact ((hfirst.add hsecond).sub hthird).sub hfourth

theorem step_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (step τ f) :=
  ((airy_inSobolev hf τ).add (quadratic_in_algebra hAlg τ hf)).add
    (cubicCorrection_in_algebra hAlg τ hf)

/-- Spatial smoothness of finite iterates is proved for the specified update,
only for the smooth-data part of the proof, with no alteration of the method. -/
theorem numerical_in_integer_sobolev (n : ℕ) (τ : ℝ) {f : Fourier}
    (hf : InSobolev ((n + 1 : ℕ) : ℝ) f) (j : ℕ) :
    InSobolev ((n + 1 : ℕ) : ℝ) (numerical τ f j) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact step_in_algebra (integer_sobolev_algebra n) τ ih

end KdV
