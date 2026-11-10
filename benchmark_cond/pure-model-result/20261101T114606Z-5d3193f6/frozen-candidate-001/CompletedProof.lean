import RegularityBridges
import StageBridges

/-! This assembly checks the complete consequence chain from the source
propositions defined in OriginalExternals. Source-equivalence certification is
reported separately in result.json and the ledger; compilation is not that audit. -/
namespace BareModelCompletion

theorem completed_theorem_1
    (step : LiWuStep52Grid) (stage : LiWuLemma72Grid) (product : LiWuProduct22)
    (trilinear : LiWuProposition34) (bit41 : BITProposition41) (bit43 : BITTheorems42And43)
    (bit51 : BITTheorem51) (bit63 : BITTheorem63) (bit65 : BITTheorem65) : KdV.TheoremOne := by
  exact theorem_1 (step_grid_to_historical step) (stage_grid_to_historical stage) product
    (trilinear_to_historical trilinear) (galerkin_to_historical (bit42_from_joint bit43))
    (limit_to_historical bit41 bit43) (high_to_historical bit41 bit43 bit51 bit65)
    (low_to_historical bit41 bit43 bit63 bit65) bit65


/-- The exact solution class is inhabited for every positive Sobolev datum. -/
theorem completed_exact_solution_exists
    (bit41 : BITProposition41) (bit43 : BITTheorems42And43) (bit51 : BITTheorem51) (bit63 : BITTheorem63) (bit65 : BITTheorem65)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : KdV.Fourier} (hf : KdV.InSobolev γ f)
    (hfr : KdV.RealValued f) (hfm : KdV.MeanZero f) :
    ∃ u : ℝ → KdV.Fourier, KdV.ExactSolution γ T f u := by
  exact KdV.exact_solution_exists (galerkin_to_historical (bit42_from_joint bit43))
    (limit_to_historical bit41 bit43) (high_to_historical bit41 bit43 bit51 bit65)
    (low_to_historical bit41 bit43 bit63 bit65) bit65 hγ hT hf hfr hfm

/-- Smooth approximation imposes no restriction on the target continuous class. -/
theorem completed_exact_solution_iff
    (bit41 : BITProposition41) (bit43 : BITTheorems42And43) (bit51 : BITTheorem51) (bit63 : BITTheorem63) (bit65 : BITTheorem65)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : KdV.Fourier} (hf : KdV.InSobolev γ f)
    (hfr : KdV.RealValued f) (hfm : KdV.MeanZero f) (u : ℝ → KdV.Fourier) :
    KdV.ExactSolution γ T f u ↔ KdV.KdVSolution γ T f u := by
  exact KdV.exactSolution_iff_kdvSolution (galerkin_to_historical (bit42_from_joint bit43))
    (limit_to_historical bit41 bit43) (high_to_historical bit41 bit43 bit51 bit65)
    (low_to_historical bit41 bit43 bit63 bit65) bit65 hγ hT hf hfr hfm u


/-- The target's exact solution is unique on the entire closed time interval. -/
theorem completed_exact_solution_unique (bit65 : BITTheorem65)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : KdV.Fourier}
    (hf : KdV.InSobolev γ f) (hfr : KdV.RealValued f) (hfm : KdV.MeanZero f)
    {u v : ℝ → KdV.Fourier} (hu : KdV.ExactSolution γ T f u) (hv : KdV.ExactSolution γ T f v) :
    ∀ t ∈ Set.Icc 0 T, u t = v t := by
  exact KdV.kdv_solution_unique bit65 hγ.le hγ.le hT hf hfr hfm hu.1 hv.1

end BareModelCompletion
