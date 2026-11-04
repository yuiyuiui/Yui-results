import GalerkinUniform
import TemporalLpLimit
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Combining the internally derived initial-ball Galerkin bound with strong
convergence in a weaker source norm gives the same uniform bound on the limiting
continuous flow. All constants precede the datum, flow, approximation family and
its index map. The time convergence concerns the cited exact-flow construction,
not the numerical method. -/
theorem uniform_source_limiting_bound (externalGalerkin : BITGalerkinEstimate)
    {s T R : ℝ} (hs : 0 ≤ s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ : ℝ, σ ≤ s → ∀ f : Fourier,
      RealValued f → InHomSobolev s f → homogeneousNorm s f ≤ R →
      ∀ v : ℝ → Fourier, HomSobolevContinuousOn s T v →
      ∀ G : ℕ → ℝ → Fourier, ∀ idx : ℕ → ℕ, (∀ n, 0 < idx n) →
      (∀ n, HomSobolevContinuousOn s T (G n)) →
      (∀ n, ∀ t ∈ Set.Icc 0 T, RealValued (G n t)) →
      (∀ n, SourceGalerkinODE (idx n) T f (G n)) →
      (∀ n, AEStronglyMeasurable (fun t : ℝ => homogeneousNorm σ (G n t - v t))
        (volume.restrict (Set.Icc 0 T))) →
      Filter.Tendsto
        (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm σ (G n t - v t)) 2
          (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0) →
        ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hb⟩ := uniform_source_galerkin_bound externalGalerkin hs hT hR
  refine ⟨A, hA, ?_⟩
  intro σ hσ f hfr hf hfR v hv G idx hidx hGC hGR hGODE hmeas hconv
  have hBound (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) : homogeneousNorm s (G n t) ≤ A :=
    hb (idx n) (hidx n) f (G n) hfr hf hfR (hGC n) (hGR n) (hGODE n) t ht
  obtain ⟨ns, hns, hcoeff⟩ := homogeneous_L2_time_subsequence
    (fun n t ht => ((hGC n).1 t ht).of_le hσ) (fun t ht => (hv.1 t ht).of_le hσ) hmeas hconv
  exact homogeneous_uniform_limit_bound hT hA.le
    (fun n t ht => (hGC (ns n)).1 t ht) (fun n t ht => hBound (ns n) t ht) hv hcoeff

end KdV
