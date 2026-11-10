import SourceTrajectories
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Strong convergence in a source homogeneous Sobolev norm and finite real
`L^p` time exponent. The finite extended norm is the ordinary `L^p` error norm. -/
def SourceLpConvergence (s T p : ℝ) (G : ℕ → ℝ → Fourier) (v : ℝ → Fourier) : Prop :=
  (∀ n, MemLp (fun t : ℝ => homogeneousNorm s (G n t - v t)) (ENNReal.ofReal p)
    (volume.restrict (Set.Icc 0 T))) ∧
  Filter.Tendsto
    (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm s (G n t - v t)) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0)

/-- Weak-star convergence in source `L∞ Hdot^s`, expressed on the weighted
`ℓ²` representatives and tested against every Bochner `L¹` dual function.
Representatives are only required to agree almost everywhere, as in the source. -/
def SourceWeakStarConvergence (s T : ℝ) (G : ℕ → ℝ → Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ W : ℕ → ℝ → L2Seq, ∃ w : ℝ → L2Seq,
    (∀ n, MemLp (W n) ∞ (volume.restrict (Set.Icc 0 T)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), (W n t).val = homogeneousWeighted s (G n t)) ∧
    (MemLp w ∞ (volume.restrict (Set.Icc 0 T)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), (w t).val = homogeneousWeighted s (v t)) ∧
    ∀ ψ : ℝ → L2Seq, Integrable ψ (volume.restrict (Set.Icc 0 T)) →
      Filter.Tendsto
        (fun n : ℕ => ∫ t : ℝ, inner ℂ (ψ t) (W n t) ∂volume.restrict (Set.Icc 0 T))
        Filter.atTop (nhds (∫ t : ℝ, inner ℂ (ψ t) (w t) ∂volume.restrict (Set.Icc 0 T)))

/-- The complete limiting-solution certificate asserted by the cited
Theorem 4.3, for its fixed lower regularity `σ`. -/
def SourceLimitCertificate (s T : ℝ) (f : Fourier) (σ : ℝ) (v : ℝ → Fourier) : Prop :=
  SourceWeakSolution T f v ∧ HomogeneousEssentiallyBounded s T v ∧
      ∃ A : ℝ, 0 ≤ A ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm 0 (v t) = homogeneousNorm 0 f) ∧
      ∃ G : ℕ → ℝ → Fourier, ∃ idx : ℕ → ℕ, StrictMono idx ∧
        (∀ m, HomSobolevContinuousOn s T (G m) ∧
          (∀ t ∈ Set.Icc 0 T, RealValued (G m t)) ∧ SourceGalerkinODE (m + 1) T f (G m) ∧
          ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (G m t) ≤ A) ∧
        (∀ p : ℝ, 1 < p → SourceLpConvergence σ T p (fun n => G (idx n)) v) ∧
        SourceWeakStarConvergence s T (fun n => G (idx n)) v

def SourceConstructedLimit (s T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ σ < s ∧ SourceLimitCertificate s T f σ v

/-- Explicit external premise: Babin–Ilyin–Titi Theorem 4.3 (arXiv v2), with
the Galerkin a priori bound from (4.13). It includes existence in Definition 3.1,
the bounded higher norm, almost-everywhere energy conservation, every finite
`L^p Hdot^σ` strong convergence conclusion, and the weak-star conclusion.
The auxiliary lower regularity `σ` is fixed before the subsequence, as in the
primary statement. Its bound `A` is after the datum; no initial-ball uniformity
is assumed here. Galerkin indices are reindexed from the positive integers. -/
def BITExistenceLimit : Prop :=
  ∀ T : ℝ, 0 < T → ∀ s : ℝ, 0 < s → ∀ f : Fourier,
    RealValued f → InHomSobolev s f → ∀ σ : ℝ, 0 < σ → σ < s →
      ∃ v : ℝ → Fourier, SourceLimitCertificate s T f σ v

theorem BITExistenceLimit.constructed {T s : ℝ} (externalLimit : BITExistenceLimit)
    (hT : 0 < T) (hs : 0 < s) {f : Fourier} (hfr : RealValued f) (hf : InHomSobolev s f) :
    ∃ v : ℝ → Fourier, SourceConstructedLimit s T f v := by
  obtain ⟨v, hv⟩ := externalLimit T hT s hs f hfr hf (s / 2) (by linarith) (by linarith)
  exact ⟨v, s / 2, by linarith, by linarith, hv⟩

end KdV
