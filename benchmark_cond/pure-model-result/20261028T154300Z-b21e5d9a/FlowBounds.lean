import ExternalFlowRegularity
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem constructed_limit_unique (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    {f : Fourier} (hfr : RealValued f) (hf : InHomSobolev s f) {v : ℝ → Fourier}
    (hv : SourceConstructedLimit s T f v) : SourceUniqueContinuous s T f v := by
  by_cases hh : 1 / 2 < s
  · exact (externalHigh s hh T hT f hfr hf v hv).2.1
  · exact (externalLow s hs (le_of_not_gt hh) T hT f hfr hf v hv).2.1

/-- Uniformity over the initial ball is derived from the fixed-norm source
estimate, the proved sphere-padding argument, and the source limit theorem. -/
theorem uniform_source_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T R : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : Fourier, RealValued f → InHomSobolev s f →
      homogeneousNorm s f ≤ R → ∃ v : ℝ → Fourier,
        SourceConstructedLimit s T f v ∧ SourceWeakSolution T f v ∧
        HomSobolevContinuousOn s T v ∧ ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hb⟩ := uniform_source_limiting_bound externalGalerkin hs.le hT hR
  refine ⟨A, hA, ?_⟩
  intro f hfr hf hfR
  obtain ⟨v, hv⟩ := externalLimit.constructed hT hs hfr hf
  have hc := constructed_limit_continuous externalHigh externalLow hs hT hfr hf hv
  obtain ⟨σ, hσ0, hσs, hcert⟩ := hv
  obtain ⟨hw, he, Af, hAf, hbound, henergy, G, idx, hidx, hG, hlp, hstar⟩ := hcert
  refine ⟨v, ⟨σ, hσ0, hσs, hw, he, Af, hAf, hbound, henergy, G, idx, hidx, hG, hlp, hstar⟩,
    hw, hc, ?_⟩
  have h2 := hlp 2 (by norm_num)
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => homogeneousNorm σ (G (idx n) t - v t))
      (volume.restrict (Set.Icc 0 T)) := fun n => (h2.1 n).1
  have hconv : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm σ (G (idx n) t - v t)) 2
        (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_ofNat] using h2.2
  exact hb σ hσs.le f hfr hf hfR v hc (fun n => G (idx n)) (fun n => idx n + 1)
    (fun n => Nat.succ_pos _) (fun n => (hG (idx n)).1)
    (fun n => (hG (idx n)).2.1) (fun n => (hG (idx n)).2.2.1) hmeas hconv

/-- The same bound applies to every continuous source solution, by the precise
continuous-class uniqueness conclusions of the cited source. -/
theorem uniform_source_flow_bound (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T R : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : Fourier, RealValued f → InHomSobolev s f →
      homogeneousNorm s f ≤ R → ∀ v : ℝ → Fourier,
        SourceWeakSolution T f v → HomSobolevContinuousOn s T v →
        ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hb⟩ := uniform_source_flow_exists
    externalGalerkin externalLimit externalHigh externalLow hs hT hR
  refine ⟨A, hA, ?_⟩
  intro f hfr hf hfR v hw hc
  obtain ⟨w, hwc, hww, hwC, hwb⟩ := hb f hfr hf hfR
  have heq := constructed_limit_unique externalHigh externalLow hs hT hfr hf hwc v hw hc
  intro t ht
  rw [heq t ht]
  exact hwb t ht

/-- A uniform bound on the exact physical solution follows with constants
chosen before the datum and the flow. No numerical stability is assumed. -/
theorem uniform_kdv_flow_bound (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T R : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hR : 0 < R) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : Fourier, RealValued f → MeanZero f → InSobolev s f →
      hNorm s f ≤ R → ∀ u : ℝ → Fourier, KdVSolution s T f u →
        ∀ t ∈ Set.Icc 0 T, hNorm s (u t) ≤ M := by
  obtain ⟨A, hA, hb⟩ := uniform_source_flow_bound
    externalGalerkin externalLimit externalHigh externalLow hs hT hR
  refine ⟨(2 : ℝ) ^ s * A, mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA, ?_⟩
  intro f hfr hfm hf hfR u hu t ht
  have hfh := hf.to_homogeneous hs.le hfm
  have hfrh := homogeneous_reflectSign hfh
  have hR' : homogeneousNorm s (reflectSign f) ≤ R := by
    rw [homogeneousNorm_reflectSign]
    exact (homogeneousNorm_le_hNorm hs.le hf hfm).trans hfR
  have hc := (kdv_solution_to_source hs.le hu).2.1
  have hw := kdv_solution_sourceWeak hs.le hu
  have hb' := hb (reflectSign f) (reflectSign_real hfr) hfrh hR'
    (fun t => sourceFrame t (u t)) hw hc t ht
  calc
    hNorm s (u t) = hNorm s (sourceFrame t (u t)) := by
      rw [sourceFrame, reflectSign_hNorm, airy_hNorm]
    _ ≤ (2 : ℝ) ^ s * homogeneousNorm s (sourceFrame t (u t)) :=
      hNorm_le_homogeneousNorm hs.le (hc.1 t ht)
    _ ≤ _ := mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg (by norm_num) _)

end KdV
