import DuhamelBridge
import SobolevPaths
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

/-- Source regularity and its original coefficient equation give exactly the
paper's Sobolev Duhamel solution after the proved reflection and Airy changes. -/
theorem source_solution_to_kdv {s T : ℝ} (hs : 0 ≤ s) {f : Fourier} {v : ℝ → Fourier}
    (hf : InHomSobolev s f) (hEq : SourceNonzeroEquation T f v)
    (hc : HomSobolevContinuousOn s T v) (hr : ∀ t ∈ Set.Icc 0 T, RealValued (v t)) :
    KdVSolution s T (reflectSign f) (fun t => airy t (reflectSign (v t))) := by
  have hm : ∀ t ∈ Set.Icc 0 T, MeanZero (v t) := fun t ht => (hc.1 t ht).1
  have htarget := sourceTwisted_to_target (hEq.all_modes hf.1 hm)
  have hcont := homogeneous_continuity_to_inhomogeneous hs hc.reflectSign
  refine ⟨hcont.airy_path id continuous_id, untwist_Duhamel htarget, ?_⟩
  intro t ht
  refine ⟨(reflectSign_real (hr t ht)).airy t, ?_⟩
  change airy t (reflectSign (v t)) 0 = 0
  rw [airy_mean]
  exact reflectSign_meanZero (hm t ht)

/-- Conversely every target Sobolev solution has the source coefficient
representation. This is needed when applying source uniqueness and dependence
results to the solution quantified in Theorem 1. -/
theorem kdv_solution_to_source {s T : ℝ} (hs : 0 ≤ s) {f : Fourier} {u : ℝ → Fourier}
    (hu : KdVSolution s T f u) :
    SourceNonzeroEquation T (reflectSign f) (fun t => reflectSign (airy (-t) (u t))) ∧
    HomSobolevContinuousOn s T (fun t => reflectSign (airy (-t) (u t))) ∧
    ∀ t ∈ Set.Icc 0 T, RealValued (reflectSign (airy (-t) (u t))) := by
  have hEq := targetTwisted_to_source (twist_Duhamel hu.2.1)
  have hc := hu.1.airy_path (fun t : ℝ => -t) continuous_neg
  have hm : ∀ t ∈ Set.Icc 0 T, MeanZero (airy (-t) (u t)) := by
    intro t ht
    change airy (-t) (u t) 0 = 0
    rw [airy_mean]
    exact (hu.2.2 t ht).2
  refine ⟨⟨hEq.1, fun t ht k _ => hEq.2 t ht k⟩,
    (inhomogeneous_continuity_to_homogeneous hs hc hm).reflectSign, ?_⟩
  intro t ht
  exact reflectSign_real ((hu.2.2 t ht).1.airy (-t))

def sourceFrame (t : ℝ) (f : Fourier) : Fourier := reflectSign (airy (-t) f)

/-- Exact normalization of the source `L²` distance under the change of frame. -/
theorem sourceFrame_difference_norm (t : ℝ) (f g : Fourier) :
    homogeneousNorm 0 (sourceFrame t f - sourceFrame t g) = hNorm 0 (f - g) := by
  rw [homogeneousNorm_zero]
  change hNorm 0 (reflectSign (airy (-t) f) - reflectSign (airy (-t) g)) = _
  rw [← reflectSign_sub, reflectSign_hNorm, ← airy_sub, airy_hNorm]

end KdV
