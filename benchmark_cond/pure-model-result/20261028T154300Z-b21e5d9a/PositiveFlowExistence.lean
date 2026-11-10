import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem positive_kdv_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    {f : Fourier} (hf : InSobolev s f) (hfr : RealValued f) (hfm : MeanZero f) :
    ∃ u : ℝ → Fourier, KdVSolution s T f u := by
  obtain ⟨A, _, hExists⟩ := uniform_source_flow_exists externalGalerkin externalLimit externalHigh externalLow
    hs hT (show 0 < hNorm s f + 1 by linarith [hNorm_nonneg s f])
  have hfh := homogeneous_reflectSign (hf.to_homogeneous hs.le hfm)
  have hfn : homogeneousNorm s (reflectSign f) ≤ hNorm s f + 1 := by
    rw [homogeneousNorm_reflectSign]
    exact (homogeneousNorm_le_hNorm hs.le hf hfm).trans (by linarith)
  obtain ⟨v, _, hw, hc, _⟩ := hExists (reflectSign f) (reflectSign_real hfr) hfh hfn
  have hu := source_solution_to_kdv hs.le hfh hw.1 hc (fun t ht => (hw.2.1 t ht).1)
  rw [reflectSign_involutive] at hu
  exact ⟨_, hu⟩

end KdV
