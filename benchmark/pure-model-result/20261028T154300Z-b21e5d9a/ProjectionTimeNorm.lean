import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem timeLInfinity_ae_bound {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖f t‖ ≤ timeLInfinity a b f := by
  have hfinite : eLpNormEssSup f (volume.restrict (Set.Icc a b)) ≠ ∞ := by
    simpa only [eLpNorm_exponent_top] using hf.2.ne
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume.restrict (Set.Icc a b))] with t ht
  have hn := ENNReal.toReal_mono hfinite ht
  simpa only [timeLInfinity, eLpNorm_exponent_top, toReal_enorm] using hn

theorem timeLInfinity_le_of_ae_bound {s A a b : ℝ} (hA : 0 ≤ A)
    (f : ℝ → Sobolev s) (hf : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖f t‖ ≤ A) :
    timeLInfinity a b f ≤ A := by
  have hs := sourceLInfinity_le_of_bound hA a b f hf
  change sourceNormalization * timeLInfinity a b f ≤ sourceNormalization * A at hs
  exact (mul_le_mul_iff_right₀ sourceNormalization_pos).mp hs

theorem timeLInfinity_map_bound {s r K a b : ℝ} (hK : 0 ≤ K)
    (L : Sobolev s →L[ℂ] Sobolev r) (hL : ∀ v, ‖L v‖ ≤ K * ‖v‖)
    {f : ℝ → Sobolev s} (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) :
    timeLInfinity a b (fun t => L (f t)) ≤ K * timeLInfinity a b f := by
  apply timeLInfinity_le_of_ae_bound (mul_nonneg hK (timeLInfinity_nonneg _ _ _))
  filter_upwards [timeLInfinity_ae_bound hf] with t ht
  exact (hL (f t)).trans (mul_le_mul_of_nonneg_left ht hK)

theorem timeLInfinity_cutoff_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeLInfinity a b (fun t => cutoffMap s m (f t)) ≤ timeLInfinity a b f := by
  simpa only [one_mul] using timeLInfinity_map_bound (by norm_num : (0 : ℝ) ≤ 1)
    (cutoffMap s m) (fun v => by simpa only [one_mul] using cutoffMap_norm_le s m v) hf

theorem timeLInfinity_highCutoff_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeLInfinity a b (fun t => highCutoffMap s m (f t)) ≤ timeLInfinity a b f := by
  simpa only [one_mul] using timeLInfinity_map_bound (by norm_num : (0 : ℝ) ≤ 1)
    (highCutoffMap s m) (fun v => by simpa only [one_mul] using highCutoffMap_norm_le s m v) hf

theorem timeXNorm_cutoff_le {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeXNorm a b (fun t => cutoffMap 0 m (f t)) (fun t => cutoffMap (-pStar) m (df t)) ≤
      timeXNorm a b f df :=
  add_le_add (timeLInfinity_cutoff_le hf m) (timeLInfinity_cutoff_le hdf m)

theorem timeXNorm_highCutoff_le {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeXNorm a b (fun t => highCutoffMap 0 m (f t)) (fun t => highCutoffMap (-pStar) m (df t)) ≤
      timeXNorm a b f df :=
  add_le_add (timeLInfinity_highCutoff_le hf m) (timeLInfinity_highCutoff_le hdf m)

/-- Negative-norm smallness of a high input, in the actual time norm. -/
theorem time_highCutoff_negative_bound {a b : ℝ} {f : ℝ → Sobolev 0}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (highCutoffMap 0 m (f t))) ≤
      weight (-pStar) (m : ℤ) * timeLInfinity a b f := by
  let L := (inclusionMap (-pStar) 0 (by norm_num [pStar])).comp (highCutoffMap 0 m)
  have hL (v : Sobolev 0) : ‖L v‖ ≤ weight (-pStar) (m : ℤ) * ‖v‖ := by
    rw [sobolev_norm, sobolev_norm]
    change hNorm (-pStar) (highCutoff m v.val) ≤ weight (-pStar) (m : ℤ) * hNorm 0 v.val
    simpa only [sub_zero] using (high_cutoff_bound (by norm_num [pStar] : -pStar ≤ 0) v.property m).2
  exact timeLInfinity_map_bound (weight_pos (-pStar) _).le L hL hf

end KdV
