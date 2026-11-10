import HomogeneousLimit
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem abs_homogeneousNorm_sub_le {s : ℝ} {f g : Fourier}
    (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    |homogeneousNorm s f - homogeneousNorm s g| ≤ homogeneousNorm s (f - g) := by
  let F := homogeneousLp s f hf
  let G := homogeneousLp s g hg
  have hsub : homogeneousLp s (f - g) (hf.sub hg) = F - G := by
    apply Subtype.ext
    exact homogeneousWeighted_sub s f g
  calc
    _ = |‖F‖ - ‖G‖| := by rw [homogeneousLp_norm, homogeneousLp_norm]
    _ ≤ ‖F - G‖ := abs_norm_sub_norm_le F G
    _ = _ := by rw [← hsub, homogeneousLp_norm]

theorem HomSobolevContinuousOn.norm_continuousOn {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) : ContinuousOn (fun t => homogeneousNorm s (v t)) (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [Real.dist_eq]
  exact (abs_homogeneousNorm_sub_le (hv.1 r hr) (hv.1 t ht)).trans_lt
    (hb r hr (by simpa only [Real.dist_eq] using hrt))

/-- Almost-everywhere bounds on a continuous homogeneous norm hold also at
both endpoints of the positive time interval. -/
theorem homogeneous_bound_of_ae {s T A : ℝ} (hT : 0 < T) {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v)
    (hb : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A) :
    ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  have heq : (fun t : ℝ => min (homogeneousNorm s (v t)) A) =ᵐ[volume.restrict (Set.Icc 0 T)]
      (fun t : ℝ => homogeneousNorm s (v t)) := hb.mono (fun _ ht => min_eq_left ht)
  have hcN := hv.norm_continuousOn
  have hcM : ContinuousOn (fun t : ℝ => min (homogeneousNorm s (v t)) A) (Set.Icc 0 T) :=
    hcN.inf continuousOn_const
  have hset : (Set.Icc (0 : ℝ) T) ⊆ closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo hT.ne]
  have hall := Measure.eqOn_of_ae_eq heq hcM hcN hset
  intro t ht
  exact min_eq_left_iff.mp (hall ht)

/-- The finite-frequency limit argument transfers a uniform Galerkin bound to
a continuous limiting flow. The coefficient convergence is an explicit internal
hypothesis to be obtained from the cited strong-in-time convergence theorem. -/
theorem homogeneous_uniform_limit_bound {s T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    {f : ℕ → ℝ → Fourier} {v : ℝ → Fourier}
    (hf : ∀ n, ∀ t ∈ Set.Icc 0 T, InHomSobolev s (f n t))
    (hb : ∀ n, ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (f n t) ≤ A)
    (hv : HomSobolevContinuousOn s T v)
    (hc : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f n t k) Filter.atTop (nhds (v t k))) :
    ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  apply homogeneous_bound_of_ae hT hv
  filter_upwards [hc, ae_restrict_mem measurableSet_Icc] with t ht htc
  exact (homogeneous_norm_limit hA (fun n => hf n t htc) (fun n => hb n t htc) ht).2

end KdV
