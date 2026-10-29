import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def affineL2Path (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (z : ℂ) : ℝ → Sobolev 0 :=
  fun t => inclusionMap 0 1 (by norm_num) (affineErrorPath externalStep hT hτ f hfr hfm hu k z t)

def affineNegativeDerivative (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (z : ℂ) : ℝ → Sobolev (-pStar) :=
  fun t => exactNegativeDerivative hT hu t - z • errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t

theorem affineL2Path_eq (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (z : ℂ) :
    affineL2Path externalStep hT hτ f hfr hfm hu k z =
      (fun t => exactL2Path hT hu t - z • errorL2Path externalStep hT hτ f hfr hfm hu k t) := by
  funext t
  apply Sobolev.ext
  simp only [affineL2Path, affineErrorPath, inclusionMap_val, sobolev_val_sub, sobolev_val_smul,
    exactL2Path, exactTwistedOne, errorL2Path]

theorem affine_input_time_membership (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    MemLp (affineL2Path externalStep hT hτ f hfr hfm hu k z) ∞ (volume.restrict (Set.Icc a b)) ∧
    MemLp (affineNegativeDerivative externalStep hT hτ f hfr hfm hu k z) ∞ (volume.restrict (Set.Icc a b)) ∧
    WeakTimeDerivative a b (fun t => (affineL2Path externalStep hT hτ f hfr hfm hu k z t).val)
      (fun t => (affineNegativeDerivative externalStep hT hτ f hfr hfm hu k z t).val) := by
  obtain ⟨hf, hdf, hw⟩ := affine_error_time_membership externalStep hT hτ k hTotal f hfr hfm hu z ha hab hb
  have hEq := affineL2Path_eq externalStep hT hτ f hfr hfm hu k z
  rw [← hEq] at hf
  have hRaw := congrArg (fun p : ℝ → Sobolev 0 => fun t => (p t).val) hEq
  rw [← hRaw] at hw
  exact ⟨hf, hdf, hw⟩

end KdV
