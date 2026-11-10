import ProjectedInputs
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem highCutoff_add (m : ℕ) (f g : Fourier) :
    highCutoff m (f + g) = highCutoff m f + highCutoff m g := by
  unfold highCutoff
  rw [cutoff_add]
  abel

theorem highCutoff_sub (m : ℕ) (f g : Fourier) :
    highCutoff m (f - g) = highCutoff m f - highCutoff m g := by
  unfold highCutoff
  rw [cutoff_sub]
  abel

def pathCubic (a b : ℝ) (f : Fin 3 → ℝ → Sobolev 1) : Fourier :=
  CIntegral a b (fun t => (f 0 t).val) (fun t => (f 1 t).val) (fun t => (f 2 t).val)

def projectedPathCubic (a b : ℝ) (m : ℕ) (i : Fin 3) (f : Fin 3 → ℝ → Sobolev 1) : Fourier :=
  pathCubic a b (fun j t => inputProjection 1 m i j (f j t))

/-- The high-output telescoping identity, including the exact cancellation of
the low-input term. All projections here belong solely to the proof. -/
theorem high_output_path_split (a b : ℝ) (m : ℕ) {f : Fin 3 → ℝ → Sobolev 1}
    (hf : ∀ j, Continuous (f j)) :
    highCutoff (3 * m) (pathCubic a b f) =
      highCutoff (3 * m) (projectedPathCubic a b m 0 f) +
      highCutoff (3 * m) (projectedPathCubic a b m 1 f) +
      highCutoff (3 * m) (projectedPathCubic a b m 2 f) := by
  let F : ℝ → Sobolev 1 := fun t => cutoffMap 1 m (f 0 t)
  let G : ℝ → Sobolev 1 := fun t => cutoffMap 1 m (f 1 t)
  let H : ℝ → Sobolev 1 := fun t => cutoffMap 1 m (f 2 t)
  have htel := CIntegral_paths_difference a b (hf 0) (hf 1) (hf 2)
    ((cutoffMap 1 m).continuous.comp (hf 0)) ((cutoffMap 1 m).continuous.comp (hf 1))
    ((cutoffMap 1 m).continuous.comp (hf 2))
  change pathCubic a b f - CIntegral a b (fun t => cutoff m (f 0 t).val)
      (fun t => cutoff m (f 1 t).val) (fun t => cutoff m (f 2 t).val) =
    CIntegral a b (fun t => highCutoff m (f 0 t).val) (fun t => (f 1 t).val) (fun t => (f 2 t).val) +
    CIntegral a b (fun t => cutoff m (f 0 t).val) (fun t => highCutoff m (f 1 t).val) (fun t => (f 2 t).val) +
    CIntegral a b (fun t => cutoff m (f 0 t).val) (fun t => cutoff m (f 1 t).val)
      (fun t => highCutoff m (f 2 t).val) at htel
  have hp := congrArg (highCutoff (3 * m)) htel
  rw [highCutoff_sub, high_output_all_low_zero, sub_zero, highCutoff_add, highCutoff_add] at hp
  simpa [projectedPathCubic, pathCubic, inputProjection, cutoffMap_val, highCutoffMap_val] using hp

/-- Estimate (32), with the exact Japanese-weight gain and threshold `3m`.
This is proved by source trilinear estimates on the three high-input terms,
not assumed as an external high-frequency stability estimate. -/
theorem high_output_trilinear_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 1 →
      ∀ f : Fin 3 → ℝ → Sobolev 1, (∀ j, Continuous (f j)) →
      ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
        ∀ m : ℕ, InSobolev 0 (highCutoff (3 * m) (pathCubic a b f)) ∧
          hNorm 0 (highCutoff (3 * m) (pathCubic a b f)) ≤
            C * (b - a) * (∏ j : Fin 3, timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (f j t)) (df j)) +
            C * weight (-pStar) (m : ℤ) *
              (∏ j : Fin 3, timeLInfinity a b (fun t => inclusionMap 0 1 (by norm_num) (f j t))) := by
  obtain ⟨C, hC, hb⟩ := one_high_cubic_bound externalTrilinear
  refine ⟨3 * C, by positivity, ?_⟩
  intro a b ha hab hlen f hf df hdf hd m
  let F : Fin 3 → ℝ → Sobolev 0 := fun j t => inclusionMap 0 1 (by norm_num) (f j t)
  have hF (j : Fin 3) : MemLp (F j) ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc (((inclusionMap 0 1 (by norm_num)).continuous.comp (hf j)).continuousOn)
  have hW (j : Fin 3) : WeakTimeDerivative a b (fun t => (F j t).val) (fun t => (df j t).val) := hd j
  have hterm (i : Fin 3) : InSobolev 0 (projectedPathCubic a b m i f) ∧
      hNorm 0 (projectedPathCubic a b m i f) ≤
        C * (b - a) * (∏ j : Fin 3, timeXNorm a b (F j) (df j)) +
          C * weight (-pStar) (m : ℤ) * (∏ j : Fin 3, timeLInfinity a b (F j)) := by
    have hh := hb a b ha hab hlen F df hF hdf hW m i
    simpa only [F, projectedPathCubic, pathCubic, inputProjection_inclusion_val] using hh
  have hhigh (i : Fin 3) : InSobolev 0 (highCutoff (3 * m) (projectedPathCubic a b m i f)) ∧
      hNorm 0 (highCutoff (3 * m) (projectedPathCubic a b m i f)) ≤
        C * (b - a) * (∏ j : Fin 3, timeXNorm a b (F j) (df j)) +
          C * weight (-pStar) (m : ℤ) * (∏ j : Fin 3, timeLInfinity a b (F j)) := by
    obtain ⟨hmem, hn⟩ := hterm i
    exact ⟨hmem.sub (cutoff_inSobolev hmem _), (highCutoff_hNorm_le hmem _).trans hn⟩
  obtain ⟨h0, hn0⟩ := hhigh 0
  obtain ⟨h1, hn1⟩ := hhigh 1
  obtain ⟨h2, hn2⟩ := hhigh 2
  rw [high_output_path_split a b m hf]
  refine ⟨(h0.add h1).add h2, ?_⟩
  calc
    _ ≤ (hNorm 0 (highCutoff (3 * m) (projectedPathCubic a b m 0 f)) +
        hNorm 0 (highCutoff (3 * m) (projectedPathCubic a b m 1 f))) +
        hNorm 0 (highCutoff (3 * m) (projectedPathCubic a b m 2 f)) :=
      (hNorm_add_le (h0.add h1) h2).trans (add_le_add (hNorm_add_le h0 h1) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hn0 hn1) hn2
    _ = _ := by ring

end KdV
