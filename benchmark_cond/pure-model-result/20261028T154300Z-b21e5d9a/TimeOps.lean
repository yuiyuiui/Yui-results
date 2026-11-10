import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem airy_add_time (t s : ℝ) (f : Fourier) : airy (t + s) f = airy t (airy s f) := by
  funext k
  simp only [airy, Complex.ofReal_add]
  rw [show Complex.I * ((t : ℂ) + s) * (k : ℂ) ^ 3 =
    Complex.I * (t : ℂ) * (k : ℂ) ^ 3 + Complex.I * (s : ℂ) * (k : ℂ) ^ 3 by ring,
    Complex.exp_add, mul_assoc]

theorem airy_neg_inverse (t : ℝ) (f : Fourier) : airy (-t) (airy t f) = f := by
  rw [← airy_add_time, neg_add_cancel, airy_zero]

theorem airy_sub (t : ℝ) (f g : Fourier) : airy t (f - g) = airy t f - airy t g := by
  funext k
  simp [airy, mul_sub]

theorem airy_difference_weight_bound (s t t₀ : ℝ) (f : Fourier) (k : ℤ) :
    ‖weighted s (airy t f - airy t₀ f) k‖ ^ 2 ≤ 4 * ‖weighted s f k‖ ^ 2 := by
  have h : ‖weighted s (airy t f - airy t₀ f) k‖ ≤ 2 * ‖weighted s f k‖ := by
    rw [weighted_sub, Pi.sub_apply]
    exact (norm_sub_le _ _).trans (by rw [norm_weighted_airy, norm_weighted_airy]; linarith)
  nlinarith [norm_nonneg (weighted s f k), norm_nonneg (weighted s (airy t f - airy t₀ f) k)]

/-- Strong continuity in the full weighted completion, for every real index. -/
theorem continuous_airy_fixed (s : ℝ) (f : Sobolev s) :
    Continuous (fun t : ℝ => airyMap s t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  change Filter.Tendsto (fun t : ℝ => airyMap s t f) (nhds t₀) (nhds (airyMap s t₀ f))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Summable (fun k : ℤ => 4 * ‖weighted s f.val k‖ ^ 2) := by
    have h : Summable (fun k : ℤ => ‖weighted s f.val k‖ ^ 2) := by
      simpa using f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact h.mul_left 4
  have hp : ∀ k : ℤ,
      Filter.Tendsto (fun t : ℝ => ‖weighted s (airy t f.val - airy t₀ f.val) k‖ ^ 2)
        (nhds t₀) (nhds (0 : ℝ)) := by
    intro k
    have hc : Continuous (fun t : ℝ => ‖weighted s (airy t f.val - airy t₀ f.val) k‖ ^ 2) := by
      unfold weighted airy
      simp only [Pi.sub_apply]
      fun_prop
    simpa [weighted] using (hc.continuousAt (x := t₀)).tendsto
  have hsum := tendsto_tsum_of_dominated_convergence hs hp
    (Filter.Eventually.of_forall fun t k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact airy_difference_weight_bound s t t₀ f.val k)
  have hn : (fun t : ℝ => ‖airyMap s t f - airyMap s t₀ f‖) =
      (fun t : ℝ => hNorm s (airy t f.val - airy t₀ f.val)) := by
    funext t
    exact sobolev_norm _
  rw [hn]
  simpa only [hNorm, tsum_zero, Real.sqrt_zero] using hsum.sqrt

end KdV
