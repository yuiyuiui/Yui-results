import GalerkinPadding
import HomogeneousOperations
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem SourceGalerkinODE.outside {s T : ℝ} (hs : 0 ≤ s) {m : ℕ}
    {f : Fourier} {v : ℝ → Fourier} (hv : SourceGalerkinODE m T f v)
    (hc : HomSobolevContinuousOn s T v) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (k : ℤ) (hk : k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ)) : v t k = f k := by
  have hcont := (homogeneous_continuity_to_inhomogeneous hs hc).coeff_continuousOn k
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hd (r : ℝ) (hr : r ∈ Set.Ioo 0 t) : HasDerivAt (fun z : ℝ => v z k) (0 : ℂ) r := by
    have h := hv.2 r ⟨hr.1, hr.2.trans_le ht.2⟩ k
    simpa only [cutoff, if_neg hk, mul_zero] using h
  have hi : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 t := continuous_const.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hcont.mono hsub) hd hi
  simp only [intervalIntegral.integral_zero] at hFTC
  have h₀ := congrFun hv.1 k
  linear_combination -hFTC + h₀

theorem SourceGalerkinODE.tail_stationary {s T : ℝ} (hs : 0 ≤ s) {m : ℕ}
    {f : Fourier} {v : ℝ → Fourier} (hv : SourceGalerkinODE m T f v)
    (hc : HomSobolevContinuousOn s T v) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    highCutoff m (v t) = highCutoff m f := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp [highCutoff, cutoff, hk]
  · simpa only [highCutoff, Pi.sub_apply, cutoff, if_neg hk, sub_zero] using hv.outside hs hc ht k hk

def sourcePaddedFlow (m : ℕ) (f g : Fourier) (v : ℝ → Fourier) (t : ℝ) : Fourier :=
  cutoff m (v t) + (g - cutoff m f)

theorem sourcePaddedFlow_low (m : ℕ) (f g : Fourier) (v : ℝ → Fourier)
    (hg : cutoff m g = cutoff m f) (t : ℝ) :
    cutoff m (sourcePaddedFlow m f g v t) = cutoff m (v t) := by
  rw [sourcePaddedFlow, cutoff_add, cutoff_sub, cutoff_idempotent, hg, cutoff_idempotent, sub_self, add_zero]

theorem sourcePaddedFlow_continuous {s T : ℝ} {m : ℕ} {f g : Fourier} {v : ℝ → Fourier}
    (hf : InHomSobolev s f) (hg : InHomSobolev s g) (hc : HomSobolevContinuousOn s T v) :
    HomSobolevContinuousOn s T (sourcePaddedFlow m f g v) :=
  (hc.cutoff m).add_const (hg.sub (hf.cutoff m))

theorem sourcePaddedFlow_real {T : ℝ} {m : ℕ} {f g : Fourier} {v : ℝ → Fourier}
    (hf : RealValued f) (hg : RealValued g) (hv : ∀ t ∈ Set.Icc 0 T, RealValued (v t)) :
    ∀ t ∈ Set.Icc 0 T, RealValued (sourcePaddedFlow m f g v t) := by
  intro t ht
  exact (cutoff_real (hv t ht) m).add (hg.sub (cutoff_real hf m))

theorem SourceGalerkinODE.padded {T : ℝ} {m : ℕ} {f g : Fourier} {v : ℝ → Fourier}
    (hv : SourceGalerkinODE m T f v) (hg : cutoff m g = cutoff m f) :
    SourceGalerkinODE m T g (sourcePaddedFlow m f g v) := by
  refine ⟨?_, ?_⟩
  · change cutoff m (v 0) + (g - cutoff m f) = g
    rw [hv.1]
    abel
  · intro t ht k
    rw [sourcePaddedFlow_low m f g v hg t]
    by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · have heq : (fun r : ℝ => sourcePaddedFlow m f g v r k) =
          (fun r : ℝ => v r k + (g - cutoff m f) k) := by
        funext r
        simp only [sourcePaddedFlow, Pi.add_apply, cutoff, if_pos hk]
      rw [heq]
      exact (hv.2 t ht k).add_const ((g - cutoff m f) k)
    · have heq : (fun r : ℝ => sourcePaddedFlow m f g v r k) =
          (fun _ : ℝ => (g - cutoff m f) k) := by
        funext r
        simp only [sourcePaddedFlow, Pi.add_apply, cutoff, if_neg hk, zero_add]
      rw [heq]
      simp only [cutoff, if_neg hk, mul_zero]
      exact hasDerivAt_const t ((g - cutoff m f) k)

/-- Uniformity over a homogeneous initial-data ball is *derived* from the
fixed-actual-norm source estimate, by padding the stationary source Galerkin tail.
The constant is chosen before every datum, flow and Galerkin index. -/
theorem uniform_source_galerkin_bound (externalGalerkin : BITGalerkinEstimate)
    {s T R : ℝ} (hs : 0 ≤ s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 0 < m → ∀ f : Fourier, ∀ v : ℝ → Fourier,
      RealValued f → InHomSobolev s f → homogeneousNorm s f ≤ R →
      HomSobolevContinuousOn s T v → (∀ t ∈ Set.Icc 0 T, RealValued (v t)) →
      SourceGalerkinODE m T f v → ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hbound⟩ := externalGalerkin s hs R hR.le T hT R hR.le
  refine ⟨A + R, by linarith, ?_⟩
  intro m hm f v hfr hf hfR hc hvr hODE t ht
  obtain ⟨g, hgr, hg, hgN, hg0, hgLow⟩ := homogeneous_sphere_padding hs hR.le hf hfr hfR m
  have hpc := sourcePaddedFlow_continuous (m := m) hf hg hc
  have hpr := sourcePaddedFlow_real (m := m) hfr hgr hvr
  have hpODE := hODE.padded hgLow
  have hpb := hbound m hm g (sourcePaddedFlow m f g v) hgr hg hgN hg0 hpc hpr hpODE
  have hLow : homogeneousNorm s (cutoff m (v t)) ≤ A := by
    calc
      _ = homogeneousNorm s (cutoff m (sourcePaddedFlow m f g v t)) := by
        rw [sourcePaddedFlow_low m f g v hgLow t]
      _ ≤ homogeneousNorm s (sourcePaddedFlow m f g v t) := homogeneousNorm_cutoff_le (hpc.1 t ht) m
      _ ≤ A := hpb t ht
  have hTail : homogeneousNorm s (highCutoff m (v t)) ≤ R := by
    rw [hODE.tail_stationary hs hc ht]
    exact (homogeneousNorm_highCutoff_le hf m).trans hfR
  calc
    _ = homogeneousNorm s (cutoff m (v t) + highCutoff m (v t)) := by
      congr 1
      unfold highCutoff
      abel
    _ ≤ homogeneousNorm s (cutoff m (v t)) + homogeneousNorm s (highCutoff m (v t)) :=
      homogeneousNorm_add_le ((hc.1 t ht).cutoff m) ((hc.1 t ht).sub ((hc.1 t ht).cutoff m))
    _ ≤ A + R := add_le_add hLow hTail

end KdV
