import Concatenation
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def numericalTwoBundled (τ : ℝ) (f : Sobolev 2) (n : ℕ) : Sobolev 2 :=
  ⟨numerical τ f.val n, by
    have h := numerical_in_integer_sobolev 1 τ (f := f.val) (by norm_num; exact f.property) n
    norm_num at h
    exact h⟩

def twistedNumericalBundled (τ : ℝ) (f : Sobolev 2) (n : ℕ) : Sobolev 2 :=
  airyMap 2 (-((n : ℝ) * τ)) (numericalTwoBundled τ f n)

theorem twistedNumericalBundled_val (τ : ℝ) (f : Sobolev 2) (n : ℕ) :
    (twistedNumericalBundled τ f n).val = airy (-((n : ℝ) * τ)) (numerical τ f.val n) := rfl

theorem twistedNumericalBundled_real (τ : ℝ) {f : Sobolev 2} (hfr : RealValued f.val) (n : ℕ) :
    RealValued (twistedNumericalBundled τ f n).val := (hfr.numerical τ n).airy _

theorem twistedNumericalBundled_meanZero (τ : ℝ) {f : Sobolev 2} (hfm : MeanZero f.val) (n : ℕ) :
    MeanZero (twistedNumericalBundled τ f n).val := by
  change airy (-((n : ℝ) * τ)) (numerical τ f.val n) 0 = 0
  rw [airy_mean]
  exact numerical_meanZero τ hfm n

theorem twistedNumericalBundled_succ (τ : ℝ) (f : Sobolev 2) (n : ℕ) :
    airy (-(((n + 1 : ℕ) : ℝ) * τ))
      (step τ (airy ((n : ℝ) * τ) (twistedNumericalBundled τ f n).val)) =
      (twistedNumericalBundled τ f (n + 1)).val := by
  rw [twistedNumericalBundled_val, airy_inverse_neg, twistedNumericalBundled_val, numerical_succ]

def interpolationPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) : Sobolev 1 :=
  localInterpolationBundled externalStep τ hτ n t (twistedNumericalBundled τ f n)
    (twistedNumericalBundled_real τ hfr n) (twistedNumericalBundled_meanZero τ hfm n)

theorem interpolationPiece_val (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) :
    (interpolationPiece externalStep τ hτ f hfr hfm n t).val =
      localInterpolation τ ((n : ℝ) * τ) t (twistedNumericalBundled τ f n).val :=
  localInterpolationBundled_val externalStep τ hτ n t _ _ _

theorem continuous_interpolationPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    Continuous (interpolationPiece externalStep τ hτ f hfr hfm n) :=
  continuous_localInterpolationBundled externalStep τ hτ n _ _ _

theorem interpolationPiece_glue (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    interpolationPiece externalStep τ hτ f hfr hfm n (((n + 1 : ℕ) : ℝ) * τ) =
      interpolationPiece externalStep τ hτ f hfr hfm (n + 1) (((n + 1 : ℕ) : ℝ) * τ) := by
  apply Sobolev.ext
  rw [interpolationPiece_val, interpolationPiece_val, localInterpolation_left,
    localInterpolation_right externalStep hτ n
      ((twistedNumericalBundled τ f n).property.of_le (by norm_num))
      (twistedNumericalBundled_real τ hfr n) (twistedNumericalBundled_meanZero τ hfm n)]
  exact twistedNumericalBundled_succ τ f n

def globalInterpolation (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) : ℝ → Sobolev 1 :=
  concatenate τ (interpolationPiece externalStep τ hτ f hfr hfm) k

theorem continuous_globalInterpolation (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) :
    Continuous (globalInterpolation externalStep τ hτ f hfr hfm k) :=
  continuous_concatenate hτ.le _ (continuous_interpolationPiece externalStep τ hτ f hfr hfm)
    (interpolationPiece_glue externalStep τ hτ f hfr hfm) k

theorem globalInterpolation_on_step (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    globalInterpolation externalStep τ hτ f hfr hfm k t =
      interpolationPiece externalStep τ hτ f hfr hfm j t :=
  concatenate_on_step hτ.le _ (interpolationPiece_glue externalStep τ hτ f hfr hfm) hjk ht

theorem globalInterpolation_grid (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k + 1) :
    (globalInterpolation externalStep τ hτ f hfr hfm k ((j : ℝ) * τ)).val =
      (twistedNumericalBundled τ f j).val := by
  by_cases hj : j ≤ k
  · rw [globalInterpolation_on_step externalStep τ hτ f hfr hfm hj
      (by constructor; rfl; push_cast; nlinarith), interpolationPiece_val, localInterpolation_left]
  · have heq : j = k + 1 := by omega
    subst j
    rw [globalInterpolation_on_step externalStep τ hτ f hfr hfm (j := k) le_rfl
      (by constructor; push_cast; nlinarith; rfl), interpolationPiece_val,
      localInterpolation_right externalStep hτ k
        ((twistedNumericalBundled τ f k).property.of_le (by norm_num))
        (twistedNumericalBundled_real τ hfr k) (twistedNumericalBundled_meanZero τ hfm k)]
    exact twistedNumericalBundled_succ τ f k

end KdV
