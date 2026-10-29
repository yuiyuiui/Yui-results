import SmallInputTrilinear
import FrozenTimeBounds
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem numerical_defect_partial_time_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      ∀ hτ : 0 < τ, τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
        let a := (n : ℝ) * τ
        let Y := defectL2Path externalStep τ hτ n f hfr hfm
        let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
        MemLp Y ∞ (volume.restrict (Set.Icc a t)) ∧
        MemLp dY ∞ (volume.restrict (Set.Icc a t)) ∧
        WeakTimeDerivative a t (fun s => (Y s).val) (fun s => (dY s).val) ∧
        timeXNorm a t Y dY ≤ C * (τ ^ γ + hNorm 0 (f.val - w)) ∧
        timeLInfinity a t (fun s => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y s)) ≤
          C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨C, hC, hb⟩ := numerical_defect_time_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  refine ⟨C, hC, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  dsimp only
  let a : ℝ := (n : ℝ) * τ
  let Y := defectL2Path externalStep τ hτ n f hfr hfm
  let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
  obtain ⟨hY, hdY, _, hX, hN⟩ := hb τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ
  have hSub : Set.Icc a t ⊆ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hNY : MemLp (fun s => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y s)) ∞
      (volume.restrict (Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ))) :=
    hY.continuousLinearMap_comp (inclusionMap (-pStar) 0 (by norm_num [pStar]))
  refine ⟨memLp_mono_interval hY hSub, memLp_mono_interval hdY hSub, ?_, ?_,
    (timeLInfinity_mono_interval hNY hSub).trans hN⟩
  · have hh := ((interpolationRemainder_regular externalStep τ hτ n f hfr hfm).restrict le_rfl ht.2).weakTimeDerivative ht.1
    simpa only [Y, dY, defectL2Path, defectNegativeDerivativePath, inclusionMap_val, defectBundled_val, defectDerivativeBundled_val] using hh
  · exact (add_le_add (timeLInfinity_mono_interval hY hSub) (timeLInfinity_mono_interval hdY hSub)).trans hX

end KdV
