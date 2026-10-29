import HomogeneousTimeLimit
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem homogeneous_coeff_bound {s : ℝ} {f : Fourier} (hf : InHomSobolev s f)
    {k : ℤ} (hk : k ≠ 0) :
    ‖f k‖ ≤ (homogeneousWeight s k)⁻¹ * homogeneousNorm s f := by
  have h : ‖homogeneousWeighted s f k‖ ≤ homogeneousNorm s f := by
    rw [homogeneousNorm_eq_lpNorm hf]
    exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ⟨homogeneousWeighted s f, hf.2⟩ k
  rw [norm_homogeneousWeighted] at h
  calc
    _ = (homogeneousWeight s k)⁻¹ * (homogeneousWeight s k * ‖f k‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (homogeneousWeight_pos_of_ne_zero s hk).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (homogeneousWeight_pos_of_ne_zero s hk).le)

/-- Strong `L²` time convergence in a source homogeneous Sobolev norm supplies
an almost-everywhere coefficientwise convergent subsequence. This implication
uses pinned Mathlib convergence-in-measure results, not an extra source premise. -/
theorem homogeneous_L2_time_subsequence {s T : ℝ} {f : ℕ → ℝ → Fourier} {v : ℝ → Fourier}
    (hf : ∀ n, ∀ t ∈ Set.Icc 0 T, InHomSobolev s (f n t))
    (hv : ∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t))
    (hmeas : ∀ n, AEStronglyMeasurable (fun t : ℝ => homogeneousNorm s (f n t - v t))
      (volume.restrict (Set.Icc 0 T)))
    (hconv : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm s (f n t - v t)) 2
        (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f (ns n) t k) Filter.atTop (nhds (v t k)) := by
  have hnorm : Filter.Tendsto
      (fun n : ℕ => eLpNorm ((fun t : ℝ => homogeneousNorm s (f n t - v t)) - (fun _ : ℝ => (0 : ℝ)))
        2 (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0) := by
    have heq (n : ℕ) : ((fun t : ℝ => homogeneousNorm s (f n t - v t)) -
        (fun _ : ℝ => (0 : ℝ))) = (fun t : ℝ => homogeneousNorm s (f n t - v t)) := by
      funext t
      exact sub_zero _
    simp_rw [heq]
    exact hconv
  have him : TendstoInMeasure (volume.restrict (Set.Icc 0 T))
      (fun n t => homogeneousNorm s (f n t - v t)) Filter.atTop (fun _ : ℝ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hmeas aestronglyMeasurable_const hnorm
  obtain ⟨ns, hns, hlim⟩ := him.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim, ae_restrict_mem measurableSet_Icc] with t ht htc
  intro k
  by_cases hk : k = 0
  · subst k
    have heq : (fun n : ℕ => f (ns n) t 0) = (fun _ : ℕ => (0 : ℂ)) :=
      funext (fun n => (hf (ns n) t htc).1)
    rw [heq, show v t 0 = 0 from (hv t htc).1]
    exact tendsto_const_nhds
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb (n : ℕ) : ‖f (ns n) t k - v t k‖ ≤
        (homogeneousWeight s k)⁻¹ * homogeneousNorm s (f (ns n) t - v t) :=
      homogeneous_coeff_bound ((hf (ns n) t htc).sub (hv t htc)) hk
    exact squeeze_zero (fun _ => norm_nonneg _) hb
      (by simpa only [mul_zero] using tendsto_const_nhds.mul ht)

end KdV
