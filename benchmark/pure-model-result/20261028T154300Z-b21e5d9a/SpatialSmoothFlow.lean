import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem kdv_solution_unique (externalLipschitz : BITWeakerLipschitz)
    {s r T : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hT : 0 < T)
    {f : Fourier} (hf : InSobolev s f) (hfr : RealValued f) (hfm : MeanZero f)
    {u v : ℝ → Fourier} (hu : KdVSolution s T f u) (hv : KdVSolution r T f v) :
    ∀ t ∈ Set.Icc 0 T, u t = v t := by
  have hf0 := hf.of_le hs
  have hfr0 : InSobolev r f := by
    have hh := hv.1.1 0 ⟨le_rfl, hT.le⟩
    rwa [hv.2.1.1] at hh
  obtain ⟨C, _, hDep⟩ := kdv_flow_l2_lipschitz externalLipschitz
    (show 0 ≤ 2 * hNorm 0 f by exact mul_nonneg (by norm_num) (hNorm_nonneg _ _)) hT
  intro t ht
  have hn := hDep s r hs hr f f hfr hfm hf hfr hfm hfr0 (by linarith) u v hu hv t ht
  rw [sub_self, hNorm_zero, mul_zero] at hn
  have hmem := ((hu.1.1 t ht).of_le hs).sub ((hv.1.1 t ht).of_le hr)
  funext k
  have hk := weighted_coeff_bound hmem k
  rw [weighted_zero] at hk
  have hkn : ‖(u t - v t) k‖ = 0 := le_antisymm (hk.trans hn) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hkn)

theorem SobolevContinuousOn.congr_on {s T : ℝ} {u v : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) (heq : ∀ t ∈ Set.Icc 0 T, u t = v t) :
    SobolevContinuousOn s T v := by
  refine ⟨fun t ht => heq t ht ▸ hu.1 t ht, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  simpa only [← heq r hr, ← heq t ht] using hb r hr hrt

/-- The cited positive-regularity flow, with smooth data, has every spatial
 Sobolev regularity. No higher regularity is imposed as an external premise. -/
theorem all_sobolev_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {T : ℝ} (hT : 0 < T) {f : Fourier} (hf : ∀ s : ℝ, InSobolev s f)
    (hfr : RealValued f) (hfm : MeanZero f) :
    ∃ u : ℝ → Fourier, Duhamel T f u ∧ (∀ s : ℝ, SobolevContinuousOn s T u) ∧
      ∀ t ∈ Set.Icc 0 T, RealValued (u t) ∧ MeanZero (u t) := by
  obtain ⟨u, hu⟩ := positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow
    (s := 2) (by norm_num) hT (hf 2) hfr hfm
  refine ⟨u, hu.2.1, ?_, hu.2.2⟩
  intro s
  let q : ℝ := max 2 (s + 1)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hsq : s ≤ q := (by linarith : s ≤ s + 1).trans (le_max_right _ _)
  obtain ⟨v, hv⟩ := positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow hq hT (hf q) hfr hfm
  have heq := kdv_solution_unique externalLipschitz hq.le (by norm_num : (0 : ℝ) ≤ 2) hT (hf q) hfr hfm hv hu
  exact (hv.1.of_le hsq).congr_on heq

end KdV
