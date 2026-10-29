import PhysicalVectorField
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem contDiff_physicalVectorField (n m : ℕ) : ContDiff ℝ m (physicalVectorField n) := by
  let A := inclusionMap ((n + 2 : ℕ) : ℝ) ((n + 4 : ℕ) : ℝ) (by push_cast; linarith)
  have hA : ContDiff ℝ m A := (A.restrictScalars ℝ).contDiff
  have hP : ContDiff ℝ m (fun f => productIntegerMap (n + 1) (A f) (A f)) :=
    (((productIntegerMap (n + 1)).bilinearRestrictScalars ℝ).contDiff.comp hA).clm_apply hA
  have hD := ((derivativeNatMap n).restrictScalars ℝ).contDiff.comp hP
  have hL : ContDiff ℝ m (thirdDerivativeNatMap n) := ((thirdDerivativeNatMap n).restrictScalars ℝ).contDiff
  exact hL.neg.add ((contDiff_const (c := (1 / 2 : ℂ))).smul hD)

end KdV
