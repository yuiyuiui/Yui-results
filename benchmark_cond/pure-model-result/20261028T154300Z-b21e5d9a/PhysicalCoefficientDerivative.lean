import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Actual differentiation of the physical (untwisted) equation, derived
 from Duhamel rather than assumed as regularity of the exact solution. -/
theorem physical_coefficient_hasDerivAt {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T f u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => u r k)
      (Complex.I * (k : ℂ) ^ 3 * u t k + (1 / 2 : ℂ) * (Complex.I * (k : ℂ)) * product (u t) (u t) k) t := by
  let v := extendedTwistedPath hT hu
  let E := fun r : ℝ => Complex.exp (Complex.I * (r : ℂ) * (k : ℂ) ^ 3)
  have hdv := extendedTwistedPath_hasDerivAt hT hu ht k
  have hdE : HasDerivAt E ((Complex.I * (k : ℂ) ^ 3) * E t) t := by
    have h := ((((hasDerivAt_id t).ofReal_comp).const_mul Complex.I).mul_const ((k : ℂ) ^ 3)).cexp
    simpa only [E, id_eq, Complex.ofReal_one, mul_one, mul_comm] using h
  have hd := hdE.mul hdv
  have hEq : (fun r : ℝ => E r * (v r).val k) =ᶠ[nhds t] (fun r : ℝ => u r k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    change airy r (v r).val k = u r k
    rw [extendedTwistedPath_val_on hT hu hr, airy_inverse_neg]
  have hB : E t * B t (v t).val (v t).val k = (Complex.I * (k : ℂ)) * product (u t) (u t) k := by
    change airy t (B t (v t).val (v t).val) k = _
    rw [B, airy_inverse_neg, extendedTwistedPath_val_on hT hu ⟨ht.1.le, ht.2.le⟩, airy_inverse_neg]
    rfl
  have hU : E t * (v t).val k = u t k := hEq.self_of_nhds
  have hD : (exactTwistedDerivative hT hu t).val k = (1 / 2 : ℂ) * B t (v t).val (v t).val k := by
    rw [exactTwistedDerivative_equation]
    rfl
  apply (hd.congr_of_eventuallyEq hEq.symm).congr_deriv
  rw [hD]
  linear_combination (Complex.I * (k : ℂ) ^ 3) * hU + (1 / 2 : ℂ) * hB

end KdV
