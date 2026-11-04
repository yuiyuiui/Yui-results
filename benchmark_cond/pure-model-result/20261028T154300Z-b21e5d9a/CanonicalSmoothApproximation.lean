import SmoothTimeRegularity
import SpatialSmoothFlow
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem smooth_kdv_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {T : ℝ} (hT : 0 < T) {f : Fourier} (hf : ∀ s : ℝ, InSobolev s f)
    (hfr : RealValued f) (hfm : MeanZero f) :
    ∃ u : ℝ → Fourier, SmoothSolution T f u := by
  obtain ⟨u, hd, hc, hr⟩ := all_sobolev_flow_exists externalGalerkin externalLimit externalHigh externalLow externalLipschitz hT hf hfr hfm
  exact ⟨u, all_regular_is_smooth hT ⟨hc 2, hd, hr⟩ hc⟩

/-- Every positive Sobolev Duhamel solution is the limit of actual smooth
 KdV solutions, in precisely the topology specified in the supplied paper. -/
theorem kdv_solution_smooth_approximation (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier} (hf : InSobolev γ f)
    (hfr : RealValued f) (hfm : MeanZero f) {u : ℝ → Fourier} (hu : KdVSolution γ T f u) :
    ObtainedBySmoothApproximation γ T f u := by
  have hf0 := hf.of_le hγ.le
  have hex (m : ℕ) : ∃ v : ℝ → Fourier, SmoothSolution T (cutoff m f) v :=
    smooth_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow externalLipschitz hT
      (fun s => cutoff_inSobolev_all s m f) (cutoff_real hfr m) (cutoff_meanZero hfm m)
  choose v hv using hex
  refine ⟨fun m => cutoff m f, v, hv, cutoff_converges hf, ?_⟩
  obtain ⟨C, hC, hDep⟩ := kdv_flow_l2_lipschitz externalLipschitz
    (show 0 ≤ 2 * hNorm 0 f from mul_nonneg (by norm_num) (hNorm_nonneg _ _)) hT
  have hData : Filter.Tendsto (fun m : ℕ => C * hNorm 0 (cutoff m f - f)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul (cutoff_converges hf0)
  intro ε hε
  have hEvent : ∀ᶠ m : ℕ in Filter.atTop, C * hNorm 0 (cutoff m f - f) < ε := hData.eventually (gt_mem_nhds hε)
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp hEvent
  refine ⟨m0, ?_⟩
  intro m hmm0 t ht
  have hvm : KdVSolution 2 T (cutoff m f) (v m) := ⟨(hv m).2.1 2, (hv m).1, (hv m).2.2.2⟩
  have hInput : hNorm 0 (cutoff m f) + hNorm 0 f ≤ 2 * hNorm 0 f := by linarith [cutoff_hNorm_le hf0 m]
  have h := hDep 2 γ (by norm_num) hγ.le (cutoff m f) f (cutoff_real hfr m) (cutoff_meanZero hfm m)
    (cutoff_inSobolev_all 2 m f) hfr hfm hf hInput (v m) u hvm hu t ht
  exact h.trans_lt (hm0 m hmm0)

/-- The explicit approximation condition does not restrict the continuous
 positive Sobolev solution class. -/
theorem exactSolution_iff_kdvSolution (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier} (hf : InSobolev γ f)
    (hfr : RealValued f) (hfm : MeanZero f) (u : ℝ → Fourier) :
    ExactSolution γ T f u ↔ KdVSolution γ T f u := by
  exact ⟨And.left, fun hu => ⟨hu, kdv_solution_smooth_approximation externalGalerkin externalLimit externalHigh externalLow externalLipschitz hγ hT hf hfr hfm hu⟩⟩

theorem exact_solution_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier} (hf : InSobolev γ f)
    (hfr : RealValued f) (hfm : MeanZero f) : ∃ u : ℝ → Fourier, ExactSolution γ T f u := by
  obtain ⟨u, hu⟩ := positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow hγ hT hf hfr hfm
  exact ⟨u, (exactSolution_iff_kdvSolution externalGalerkin externalLimit externalHigh externalLow externalLipschitz hγ hT hf hfr hfm u).mpr hu⟩

end KdV
