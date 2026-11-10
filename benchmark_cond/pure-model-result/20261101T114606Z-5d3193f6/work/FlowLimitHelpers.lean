import PaddingHelpers
noncomputable section
open scoped ENNReal
open MeasureTheory KdV
namespace BareModelCompletion

/-- The genuine source weaker-norm estimate turns L2 convergence of data into
coefficient convergence of their continuous source flows. -/
theorem source_flow_coefficient_limit (hL : BITWeakerLipschitz)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    {data : ℕ → Fourier} {f : Fourier} {flows : ℕ → ℝ → Fourier} {v : ℝ → Fourier}
    (hdataR : ∀ n, RealValued (data n)) (hfR : RealValued f)
    (hdata : ∀ n, InHomSobolev 0 (data n)) (hf : InHomSobolev 0 f)
    (hbound : ∀ n, homogeneousNorm 0 (data n) + homogeneousNorm 0 f ≤ M)
    (hflows : ∀ n, SourceWeakSolution T (data n) (flows n))
    (hflowsC : ∀ n, HomSobolevContinuousOn 0 T (flows n))
    (hv : SourceWeakSolution T f v) (hvC : HomSobolevContinuousOn 0 T v)
    (hd : Filter.Tendsto (fun n => homogeneousNorm 0 (data n - f)) Filter.atTop (nhds 0)) :
    ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ,
      Filter.Tendsto (fun n => flows n t k) Filter.atTop (nhds (v t k)) := by
  obtain ⟨C, hC, A, hA, hb⟩ := source_flow_lipschitz hL hM
    (by norm_num : (-1 : ℝ) < 0) (le_refl (0 : ℝ))
  intro t ht k
  have hcoeff (n : ℕ) : ‖flows n t k - v t k‖ ≤
      (C * A ^ T) * homogeneousNorm 0 (data n - f) := by
    have hdiff : InSobolev 0 (flows n t - v t) :=
      (((hflowsC n).1 t ht).sub (hvC.1 t ht)).to_inhomogeneous (le_refl 0)
    have hc : ‖flows n t k - v t k‖ ≤ homogeneousNorm 0 (flows n t - v t) := by
      simpa only [homogeneousNorm_zero, weighted_zero, Pi.sub_apply] using weighted_coeff_bound hdiff k
    exact hc.trans (hb T hT (data n) f (hdataR n) hfR (hdata n) hf (hbound n)
      (flows n) v (hflows n) hv (hflowsC n) hvC t ht)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _) hcoeff
  simpa using hd.const_mul (C * A ^ T)


/-- Project-specific consequence: estimates with constants only on exact norm
spheres imply the historical neighborhood estimate. All flow and estimate
hypotheses are explicit here; none is asserted as a literature theorem. -/
theorem local_lipschitz_from_spheres (hL : BITWeakerLipschitz)
    {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    (hexists : ∀ f : Fourier, RealValued f → InHomSobolev s f →
      ∃ v : ℝ → Fourier, SourceWeakSolution T f v ∧ HomSobolevContinuousOn s T v)
    (hsphere : ∀ S : ℝ, 0 < S → ∃ K : ℝ, 0 < K ∧
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev s f → InHomSobolev s g →
      homogeneousNorm s f = S → homogeneousNorm s g = S →
      ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
      HomSobolevContinuousOn s T v → HomSobolevContinuousOn s T w →
      ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t - w t) ≤ K * homogeneousNorm s (f - g))
    {f : Fourier} (hfr : RealValued f) (hf : InHomSobolev s f)
    {v : ℝ → Fourier} (hv : SourceWeakSolution T f v) (hvC : HomSobolevContinuousOn s T v) :
    SourceLocalLipschitz s T f v := by
  let R := homogeneousNorm s f + 1
  have hR : 0 < R := by dsimp [R]; have := homogeneousNorm_nonneg s f; linarith
  have hfR : homogeneousNorm s f ≤ R := by dsimp [R]; linarith
  obtain ⟨K, hK, hb⟩ := hsphere (2 * R) (by positivity)
  apply (source_local_lipschitz_iff hT hvC).mp
  refine ⟨1, by norm_num, 3 * K, by positivity, ?_⟩
  intro g hgr hg hgf w hw hwC
  have hgR : homogeneousNorm s g ≤ R := by
    have hh := (abs_le.mp (abs_homogeneousNorm_sub_le hg hf)).2
    dsimp [R]
    linarith
  let F := fun n => sourceSphereData s R n f hf
  let G := fun n => sourceSphereData s R n g hg
  have hFP (n : ℕ) := sourceSphereData_properties hR n f hf hfr hfR
  have hGP (n : ℕ) := sourceSphereData_properties hR n g hg hgr hgR
  choose vf hvf hvfC using (fun n : ℕ => hexists (F n) (hFP n).1 (hFP n).2.1)
  choose wg hwg hwgC using (fun n : ℕ => hexists (G n) (hGP n).1 (hGP n).2.1)
  have hf0 : InHomSobolev 0 f := hf.of_le hs.le
  have hg0 : InHomSobolev 0 g := hg.of_le hs.le
  have hF0 (n : ℕ) : InHomSobolev 0 (F n) := (hFP n).2.1.of_le hs.le
  have hG0 (n : ℕ) : InHomSobolev 0 (G n) := (hGP n).2.1.of_le hs.le
  have hbf (n : ℕ) : homogeneousNorm 0 (F n) + homogeneousNorm 0 f ≤ 4 * R := by
    have h1 := homogeneousNorm_mono (hFP n).2.1 hs.le
    have h2 := homogeneousNorm_mono hf hs.le
    rw [(hFP n).2.2.1] at h1
    linarith
  have hbg (n : ℕ) : homogeneousNorm 0 (G n) + homogeneousNorm 0 g ≤ 4 * R := by
    have h1 := homogeneousNorm_mono (hGP n).2.1 hs.le
    have h2 := homogeneousNorm_mono hg hs.le
    rw [(hGP n).2.2.1] at h1
    linarith
  have hcv := source_flow_coefficient_limit hL hT (show 0 ≤ 4 * R by positivity)
    (fun n => (hFP n).1) hfr hF0 hf0 hbf hvf (fun n => (hvfC n).of_le hs.le)
    hv (hvC.of_le hs.le) (sourceSphereData_L2_converges hs hR f hf hfr hfR)
  have hcw := source_flow_coefficient_limit hL hT (show 0 ≤ 4 * R by positivity)
    (fun n => (hGP n).1) hgr hG0 hg0 hbg hwg (fun n => (hwgC n).of_le hs.le)
    hw (hwC.of_le hs.le) (sourceSphereData_L2_converges hs hR g hg hgr hgR)
  intro t ht
  have hbound (n : ℕ) : homogeneousNorm s (vf n t - wg n t) ≤
      (3 * K) * homogeneousNorm s (f - g) := by
    have hh := hb (F n) (G n) (hFP n).1 (hGP n).1 (hFP n).2.1 (hGP n).2.1
      (hFP n).2.2.1 (hGP n).2.2.1 (vf n) (wg n) (hvf n) (hwg n) (hvfC n) (hwgC n) t ht
    have hp := sourceSphereData_difference hR n f g hf hg hfR hgR
    have hh2 := mul_le_mul_of_nonneg_left hp hK.le
    exact hh.trans (by nlinarith only [hh2])
  have hA : 0 ≤ (3 * K) * homogeneousNorm s (f - g) :=
    mul_nonneg (by positivity) (homogeneousNorm_nonneg _ _)
  exact (homogeneous_norm_limit hA
    (fun n => ((hvfC n).1 t ht).sub ((hwgC n).1 t ht)) hbound
    (fun k => (hcv t ht k).sub (hcw t ht k))).2

end BareModelCompletion
