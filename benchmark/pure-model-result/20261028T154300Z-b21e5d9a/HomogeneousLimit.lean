import HomogeneousOperations
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

theorem homogeneousNorm_sq (s : ℝ) (f : Fourier) :
    homogeneousNorm s f ^ 2 = ∑' k : ℤ, ‖homogeneousWeighted s f k‖ ^ 2 := by
  exact Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)

/-- Lower semicontinuity of the full homogeneous norm under coefficientwise
convergence. In particular no bound on a finite projection replaces the target
Sobolev norm, and membership of the limit is proved. -/
theorem homogeneous_norm_limit {s A : ℝ} (hA : 0 ≤ A) {f : ℕ → Fourier} {g : Fourier}
    (hf : ∀ n, InHomSobolev s (f n)) (hb : ∀ n, homogeneousNorm s (f n) ≤ A)
    (hc : ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f n k) Filter.atTop (nhds (g k))) :
    InHomSobolev s g ∧ homogeneousNorm s g ≤ A := by
  have hzero : g 0 = 0 := by
    have hz : Filter.Tendsto (fun n : ℕ => f n 0) Filter.atTop (nhds (0 : ℂ)) := by
      have heq : (fun n : ℕ => f n 0) = (fun _ : ℕ => (0 : ℂ)) :=
        funext (fun n => (hf n).1)
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hc 0) hz
  have hdot (k : ℤ) : Filter.Tendsto (fun n : ℕ => homogeneousWeighted s (f n) k)
      Filter.atTop (nhds (homogeneousWeighted s g k)) := by
    exact tendsto_const_nhds.mul (hc k)
  have hfin (K : Finset ℤ) : (∑ k ∈ K, ‖homogeneousWeighted s g k‖ ^ 2) ≤ A ^ 2 := by
    have ht : Filter.Tendsto (fun n : ℕ => ∑ k ∈ K, ‖homogeneousWeighted s (f n) k‖ ^ 2)
        Filter.atTop (nhds (∑ k ∈ K, ‖homogeneousWeighted s g k‖ ^ 2)) :=
      tendsto_finsetSum K (fun k _ => (hdot k).norm.pow 2)
    apply le_of_tendsto ht (Filter.Eventually.of_forall ?_)
    intro n
    have hsum : Summable (fun k : ℤ => ‖homogeneousWeighted s (f n) k‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hf n).2.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    calc
      _ ≤ ∑' k : ℤ, ‖homogeneousWeighted s (f n) k‖ ^ 2 :=
        hsum.sum_le_tsum K (fun _ _ => sq_nonneg _)
      _ = homogeneousNorm s (f n) ^ 2 := (homogeneousNorm_sq s (f n)).symm
      _ ≤ A ^ 2 := (sq_le_sq₀ (homogeneousNorm_nonneg s (f n)) hA).mpr (hb n)
  have hs : Summable (fun k : ℤ => ‖homogeneousWeighted s g k‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfin
  have hm : InHomSobolev s g := ⟨hzero, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)⟩
  refine ⟨hm, ?_⟩
  apply (sq_le_sq₀ (homogeneousNorm_nonneg s g) hA).mp
  rw [homogeneousNorm_sq]
  exact Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfin

theorem realValued_of_coefficient_limit {f : ℕ → Fourier} {g : Fourier}
    (hf : ∀ n, RealValued (f n))
    (hc : ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f n k) Filter.atTop (nhds (g k))) : RealValued g := by
  intro k
  have hconj : Filter.Tendsto (fun n : ℕ => conj (f n k)) Filter.atTop (nhds (conj (g k))) :=
    continuous_star.continuousAt.tendsto.comp (hc k)
  have heq : (fun n : ℕ => f n (-k)) = (fun n : ℕ => conj (f n k)) :=
    funext (fun n => hf n k)
  rw [← heq] at hconj
  exact tendsto_nhds_unique (hc (-k)) hconj

end KdV
