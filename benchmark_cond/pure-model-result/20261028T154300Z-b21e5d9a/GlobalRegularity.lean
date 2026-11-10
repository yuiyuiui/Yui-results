import GlobalResidual
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem concatenate_property {E : Type*} (τ : ℝ) (F : ℕ → ℝ → E) (P : E → Prop)
    (hP : ∀ j t, P (F j t)) (k : ℕ) (t : ℝ) : P (concatenate τ F k t) := by
  induction k with
  | zero => exact hP 0 t
  | succ k ih =>
    rw [concatenate]
    dsimp only
    split_ifs
    · exact ih
    · exact hP (k + 1) t

theorem globalInterpolation_meanZero (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) (t : ℝ) :
    MeanZero (globalInterpolation externalStep τ hτ f hfr hfm k t).val := by
  apply concatenate_property τ (interpolationPiece externalStep τ hτ f hfr hfm)
    (fun g : Sobolev 1 => MeanZero g.val)
  intro j s
  rw [interpolationPiece_val]
  exact localInterpolation_meanZero τ _ s (twistedNumericalBundled_meanZero τ hfm j)

theorem exists_open_grid_step {τ : ℝ} (hτ : 0 < τ) (k : ℕ) {t : ℝ}
    (ht0 : 0 < t) (htT : t < ((k + 1 : ℕ) : ℝ) * τ)
    (hnot : ∀ j : ℕ, t ≠ (j : ℝ) * τ) :
    ∃ j : ℕ, j ≤ k ∧ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simpa using And.intro ht0 htT⟩
  | succ k ih =>
    by_cases hlast : ((k + 1 : ℕ) : ℝ) * τ < t
    · exact ⟨k + 1, le_rfl, hlast, htT⟩
    · have ht' : t < ((k + 1 : ℕ) : ℝ) * τ :=
        lt_of_le_of_ne (le_of_not_gt hlast) (hnot (k + 1))
      obtain ⟨j, hj, hjt⟩ := ih ht'
      exact ⟨j, hj.trans (Nat.le_succ _), hjt⟩

theorem globalInterpolation_hasDerivAt_on_step (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (globalInterpolation externalStep τ hτ f hfr hfm k r).val m)
      (localInterpolationDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val m) t := by
  have hE := concatenate_eventuallyEq hτ.le _ (interpolationPiece_glue externalStep τ hτ f hfr hfm) hjk ht
  have hEc : (fun r : ℝ => (globalInterpolation externalStep τ hτ f hfr hfm k r).val m) =ᶠ[nhds t]
      (fun r : ℝ => (interpolationPiece externalStep τ hτ f hfr hfm j r).val m) :=
    hE.mono (fun _ hr => congrArg (fun v : Sobolev 1 => v.val m) hr)
  have hlocal : HasDerivAt (fun r : ℝ => (interpolationPiece externalStep τ hτ f hfr hfm j r).val m)
      (localInterpolationDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val m) t := by
    simp_rw [interpolationPiece_val]
    exact localInterpolation_hasDerivAt _ (twistedNumericalBundled_meanZero τ hfm j) m
  exact hlocal.congr_of_eventuallyEq hEc

theorem globalResidual_hasDerivAt_on_step (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (globalResidual externalStep τ hτ f hfr hfm k r).val m)
      (localResidualDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val m) t := by
  have hE := concatenate_eventuallyEq hτ.le _ (cumulativeResidualPiece_glue externalStep τ hτ f hfr hfm) hjk ht
  have hEc : (fun r : ℝ => (globalResidual externalStep τ hτ f hfr hfm k r).val m) =ᶠ[nhds t]
      (fun r : ℝ => (cumulativeResidualPiece externalStep τ hτ f hfr hfm j r).val m) :=
    hE.mono (fun _ hr => congrArg (fun v : Sobolev 0 => v.val m) hr)
  have hlocal : HasDerivAt (fun r : ℝ => (cumulativeResidualPiece externalStep τ hτ f hfr hfm j r).val m)
      (localResidualDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val m) t := by
    let S : Sobolev 0 := ∑ i ∈ Finset.range j,
      residualPiece externalStep τ hτ f hfr hfm i (((i + 1 : ℕ) : ℝ) * τ)
    change HasDerivAt (fun r : ℝ => S.val m + (residualPiece externalStep τ hτ f hfr hfm j r).val m) _ t
    simp_rw [residualPiece_val]
    simpa only [zero_add] using! (hasDerivAt_const t (S.val m)).add
      (localResidual_hasDerivAt externalStep τ hτ j (twistedNumericalBundled τ f j)
        (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j) t m)
  exact hlocal.congr_of_eventuallyEq hEc

theorem global_perturbation_hasDerivAt_on_step (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (globalInterpolation externalStep τ hτ f hfr hfm k r).val m -
      (globalResidual externalStep τ hτ f hfr hfm k r).val m)
      ((1 / 2 : ℂ) * B t (globalInterpolation externalStep τ hτ f hfr hfm k t).val
        (globalInterpolation externalStep τ hτ f hfr hfm k t).val m) t := by
  have h := (globalInterpolation_hasDerivAt_on_step externalStep τ hτ f hfr hfm hjk ht m).sub
    (globalResidual_hasDerivAt_on_step externalStep τ hτ f hfr hfm hjk ht m)
  have hY : InSobolev 0 (interpolationRemainder τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val) := by
    rw [← defectBundled_val externalStep τ hτ j t (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)]
    exact (defectBundled externalStep τ hτ j t (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)).property.of_le (by norm_num)
  have hp := congrFun (localInterpolation_perturbation_identity
    ((twistedNumericalBundled τ f j).property.of_le (by norm_num)) hY) m
  have hv : (globalInterpolation externalStep τ hτ f hfr hfm k t).val =
      localInterpolation τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val :=
    (congrArg Sobolev.val (globalInterpolation_on_step externalStep τ hτ f hfr hfm hjk
      ⟨ht.1.le, ht.2.le⟩)).trans (interpolationPiece_val externalStep τ hτ f hfr hfm j t)
  rw [← hv] at hp
  apply h.congr_deriv
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right] using
    congrArg (fun z : ℂ => z - localResidualDerivative τ ((j : ℝ) * τ) t
      (twistedNumericalBundled τ f j).val m) hp

end KdV
