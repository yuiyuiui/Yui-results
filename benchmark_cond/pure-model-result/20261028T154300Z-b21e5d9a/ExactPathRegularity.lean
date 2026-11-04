import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- A continuous Sobolev path extended constantly past both endpoints. Only
this auxiliary extension is used outside the physical time interval. -/
def sobolevExtension {s T : ℝ} (hT : 0 ≤ T) (u : ℝ → Fourier)
    (hu : SobolevContinuousOn s T u) : ℝ → Sobolev s :=
  fun t => sobolevRestriction s T u hu.1 (Set.projIcc 0 T hT t)

theorem continuous_sobolevExtension {s T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) : Continuous (sobolevExtension hT u hu) :=
  hu.continuous_restriction.comp continuous_projIcc

theorem sobolevExtension_val_on {s T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (sobolevExtension hT u hu t).val = u t := by
  unfold sobolevExtension
  rw [Set.projIcc_of_mem hT ht]
  rfl

def extendedTwistedPath {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : ℝ → Sobolev 2 :=
  sobolevExtension hT (fun t => airy (-t) (u t)) (hu.1.airy_path (fun t => -t) continuous_neg)

theorem continuous_extendedTwistedPath {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : Continuous (extendedTwistedPath hT hu) :=
  continuous_sobolevExtension hT _

theorem extendedTwistedPath_val_on {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (extendedTwistedPath hT hu t).val = airy (-t) (u t) :=
  sobolevExtension_val_on hT _ ht

theorem extendedTwistedPath_meanZero {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : MeanZero (extendedTwistedPath hT hu t).val := by
  let p := Set.projIcc 0 T hT t
  change airy (-p.val) (u p.val) 0 = 0
  rw [airy_mean]
  exact (hu.2.2 p.val p.property).2

theorem extendedTwistedPath_zero {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : (extendedTwistedPath hT hu 0).val = u0 := by
  rw [extendedTwistedPath_val_on hT hu ⟨le_rfl, hT⟩, neg_zero, airy_zero]
  exact hu.2.1.1

theorem extendedTwistedPath_equation {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (k : ℤ) :
    (extendedTwistedPath hT hu t).val k = u0 k + (1 / 2 : ℂ) *
      ∫ s : ℝ in (0 : ℝ)..t, B s (extendedTwistedPath hT hu s).val (extendedTwistedPath hT hu s).val k := by
  have hv := twist_Duhamel hu.2.1
  have hInt : (∫ s : ℝ in (0 : ℝ)..t, B s (extendedTwistedPath hT hu s).val (extendedTwistedPath hT hu s).val k) =
      (∫ s : ℝ in (0 : ℝ)..t, B s (airy (-s) (u s)) (airy (-s) (u s)) k) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    dsimp only
    rw [extendedTwistedPath_val_on hT hu ⟨hs.1, hs.2.trans ht.2⟩]
  rw [hInt, extendedTwistedPath_val_on hT hu ht]
  exact hv.2 t ht k

def exactTwistedDerivative {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : Sobolev 1 :=
  (1 / 2 : ℂ) • BTwoBundled t (extendedTwistedPath hT hu t) (extendedTwistedPath hT hu t)

theorem continuous_exactTwistedDerivative {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : Continuous (exactTwistedDerivative hT hu) := by
  exact (continuous_const (y := (1 / 2 : ℂ))).smul (continuous_BTwoBundled continuous_id
    (continuous_extendedTwistedPath hT hu) (continuous_extendedTwistedPath hT hu))

/-- Actual coefficient differentiation of the source-prescribed Duhamel
solution. No exact-trajectory derivative premise is introduced. -/
theorem extendedTwistedPath_hasDerivAt {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => (extendedTwistedPath hT hu r).val k)
      ((exactTwistedDerivative hT hu t).val k) t := by
  have hV := continuous_extendedTwistedPath hT hu
  have hc : Continuous (fun r : ℝ => B r (extendedTwistedPath hT hu r).val (extendedTwistedPath hT hu r).val k) := by
    have h := (coefficientMap 1 k).continuous.comp (continuous_BTwoBundled continuous_id hV hV)
    simpa only [Function.comp_def, coefficientMap_apply, BTwoBundled_val, id_eq] using h
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hDF := (hasDerivAt_const t (u0 k)).add (hi.const_mul (1 / 2 : ℂ))
  have hE : (fun r : ℝ => (extendedTwistedPath hT hu r).val k) =ᶠ[nhds t]
      (fun r : ℝ => u0 k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..r,
        B s (extendedTwistedPath hT hu s).val (extendedTwistedPath hT hu s).val k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    exact extendedTwistedPath_equation hT hu hr k
  simpa only [zero_add] using! hDF.congr_of_eventuallyEq hE

theorem exactTwistedDerivative_equation {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) :
    (exactTwistedDerivative hT hu t).val =
      (1 / 2 : ℂ) • B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val := rfl

end KdV
