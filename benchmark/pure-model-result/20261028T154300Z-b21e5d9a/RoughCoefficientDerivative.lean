import ProductCoefficientMap
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def roughTwistedPath {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : ℝ → Sobolev 0 :=
  sobolevExtension hT (fun t => airy (-t) (u t))
    ((hu.1.of_le hγ).airy_path (fun t : ℝ => -t) continuous_neg)

theorem roughTwistedPath_val_on {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (roughTwistedPath hT hγ hu t).val = airy (-t) (u t) := sobolevExtension_val_on hT _ ht

theorem continuous_roughTwistedPath {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : Continuous (roughTwistedPath hT hγ hu) :=
  continuous_sobolevExtension hT _

theorem roughTwistedPath_equation {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (k : ℤ) :
    (roughTwistedPath hT hγ hu t).val k = f k + (1 / 2 : ℂ) *
      ∫ r : ℝ in (0 : ℝ)..t, B r (roughTwistedPath hT hγ hu r).val (roughTwistedPath hT hγ hu r).val k := by
  have h := (twist_Duhamel hu.2.1).2 t ht k
  rw [roughTwistedPath_val_on hT hγ hu ht]
  convert h using 1
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le ht.1] at hr
  dsimp only
  rw [roughTwistedPath_val_on hT hγ hu ⟨hr.1, hr.2.trans ht.2⟩]

theorem roughTwistedPath_hasDerivAt {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => (roughTwistedPath hT hγ hu r).val k)
      ((1 / 2 : ℂ) * B t (roughTwistedPath hT hγ hu t).val (roughTwistedPath hT hγ hu t).val k) t := by
  let v := roughTwistedPath hT hγ hu
  have hc := continuous_BCoefficient (continuous_roughTwistedPath hT hγ hu) (continuous_roughTwistedPath hT hγ hu) k
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := (hasDerivAt_const t (f k)).add (hi.const_mul (1 / 2 : ℂ))
  have hEq : (fun r : ℝ => (v r).val k) =ᶠ[nhds t]
      (fun r : ℝ => f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..r, B s (v s).val (v s).val k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    exact roughTwistedPath_equation hT hγ hu hr k
  simpa only [zero_add] using! hd.congr_of_eventuallyEq hEq

theorem rough_physical_coefficient_hasDerivAt {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => u r k)
      (Complex.I * (k : ℂ) ^ 3 * u t k + (1 / 2 : ℂ) * (Complex.I * (k : ℂ)) * product (u t) (u t) k) t := by
  let v := roughTwistedPath hT hγ hu
  let E := fun r : ℝ => Complex.exp (Complex.I * (r : ℂ) * (k : ℂ) ^ 3)
  have hdv := roughTwistedPath_hasDerivAt hT hγ hu ht k
  have hdE : HasDerivAt E ((Complex.I * (k : ℂ) ^ 3) * E t) t := by
    have h := ((((hasDerivAt_id t).ofReal_comp).const_mul Complex.I).mul_const ((k : ℂ) ^ 3)).cexp
    simpa only [E, id_eq, Complex.ofReal_one, mul_one, mul_comm] using h
  have hd := hdE.mul hdv
  have hEq : (fun r : ℝ => E r * (v r).val k) =ᶠ[nhds t] (fun r : ℝ => u r k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    change airy r (v r).val k = u r k
    rw [roughTwistedPath_val_on hT hγ hu hr, airy_inverse_neg]
  have hB : E t * B t (v t).val (v t).val k = (Complex.I * (k : ℂ)) * product (u t) (u t) k := by
    change airy t (B t (v t).val (v t).val) k = _
    rw [B, airy_inverse_neg, roughTwistedPath_val_on hT hγ hu ⟨ht.1.le, ht.2.le⟩, airy_inverse_neg]
    rfl
  have hU : E t * (v t).val k = u t k := hEq.self_of_nhds
  apply (hd.congr_of_eventuallyEq hEq.symm).congr_deriv
  linear_combination (Complex.I * (k : ℂ) ^ 3) * hU + (1 / 2 : ℂ) * hB

end KdV
