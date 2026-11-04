import HomogeneousAlgebra
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

theorem InHomSobolev.add {s : ℝ} {f g : Fourier} (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    InHomSobolev s (f + g) := by
  refine ⟨?_, ?_⟩
  · change f 0 + g 0 = 0
    rw [hf.1, hg.1, add_zero]
  · rw [homogeneousWeighted_add]
    exact hf.2.add hg.2

theorem homogeneousNorm_add_le {s : ℝ} {f g : Fourier} (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    homogeneousNorm s (f + g) ≤ homogeneousNorm s f + homogeneousNorm s g := by
  let F := homogeneousLp s f hf
  let G := homogeneousLp s g hg
  have heq : homogeneousLp s (f + g) (hf.add hg) = F + G := by
    apply Subtype.ext
    exact homogeneousWeighted_add s f g
  rw [← homogeneousLp_norm s (f + g) (hf.add hg), heq, ← homogeneousLp_norm s f hf,
    ← homogeneousLp_norm s g hg]
  exact norm_add_le F G

theorem homogeneousNorm_highCutoff_le {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) (m : ℕ) :
    homogeneousNorm s (highCutoff m f) ≤ homogeneousNorm s f := by
  change homogeneousNorm s (f - cutoff m f) ≤ homogeneousNorm s f
  rw [homogeneousNorm_eq_lpNorm (hf.sub (hf.cutoff m)), homogeneousNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s (highCutoff m f) k‖ ≤ ‖homogeneousWeighted s f k‖
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp only [homogeneousWeighted, highCutoff, Pi.sub_apply, cutoff, if_pos hk, sub_self, mul_zero, norm_zero]
    exact norm_nonneg _
  · simp [homogeneousWeighted, highCutoff, cutoff, hk]

theorem cutoff_add (m : ℕ) (f g : Fourier) : cutoff m (f + g) = cutoff m f + cutoff m g := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

theorem cutoff_sub (m : ℕ) (f g : Fourier) : cutoff m (f - g) = cutoff m f - cutoff m g := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

@[simp] theorem cutoff_idempotent (m : ℕ) (f : Fourier) : cutoff m (cutoff m f) = cutoff m f := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

theorem HomSobolevContinuousOn.cutoff {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) (m : ℕ) :
    HomSobolevContinuousOn s T (fun t => KdV.cutoff m (v t)) := by
  refine ⟨fun t ht => (hv.1 t ht).cutoff m, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [← cutoff_sub]
  exact (homogeneousNorm_cutoff_le ((hv.1 r hr).sub (hv.1 t ht)) m).trans_lt (hb r hr hrt)

theorem HomSobolevContinuousOn.add_const {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) {g : Fourier} (hg : InHomSobolev s g) :
    HomSobolevContinuousOn s T (fun t => v t + g) := by
  refine ⟨fun t ht => (hv.1 t ht).add hg, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [show (v r + g) - (v t + g) = v r - v t by abel]
  exact hb r hr hrt

/-- Norm continuity entails continuity of every actual Fourier coefficient. -/
theorem SobolevContinuousOn.coeff_continuousOn {s T : ℝ} {v : ℝ → Fourier}
    (hv : SobolevContinuousOn s T v) (k : ℤ) :
    ContinuousOn (fun t : ℝ => v t k) (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht (ε * weight s k) (mul_pos hε (weight_pos s k))
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [dist_eq_norm]
  have hc := weighted_coeff_bound ((hv.1 r hr).sub (hv.1 t ht)) k
  rw [norm_weighted] at hc
  change weight s k * ‖v r k - v t k‖ ≤ hNorm s (v r - v t) at hc
  have hlt := hc.trans_lt (hb r hr (by simpa only [Real.dist_eq] using hrt))
  exact (mul_lt_mul_iff_right₀ (weight_pos s k)).mp (by simpa only [mul_comm] using hlt)

end KdV
