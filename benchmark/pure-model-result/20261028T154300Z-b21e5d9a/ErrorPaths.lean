import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def exactTwistedOne {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : Sobolev 1 :=
  inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)

def errorPath (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (t : ℝ) : Sobolev 1 :=
  exactTwistedOne hT hu t - globalInterpolation externalStep τ hτ f hfr hfm k t

def errorMidpoint (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (t : ℝ) : Sobolev 1 :=
  exactTwistedOne hT hu t - (1 / 2 : ℂ) • errorPath externalStep hT hτ f hfr hfm hu k t

def errorDerivativeFamily (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (j : ℕ) (t : ℝ) : Sobolev 1 :=
  exactTwistedDerivative hT hu t - numericalDerivativeFamily externalStep τ hτ f hfr hfm j t

theorem continuous_errorPath (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) :
    Continuous (errorPath externalStep hT hτ f hfr hfm hu k) :=
  ((inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)).sub
    (continuous_globalInterpolation externalStep τ hτ f hfr hfm k)

theorem continuous_errorMidpoint (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) :
    Continuous (errorMidpoint externalStep hT hτ f hfr hfm hu k) :=
  ((inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)).sub
    ((continuous_const (y := (1 / 2 : ℂ))).smul (continuous_errorPath externalStep hT hτ f hfr hfm hu k))

theorem continuous_errorDerivativeFamily (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (j : ℕ) :
    Continuous (errorDerivativeFamily externalStep hT hτ f hfr hfm hu j) :=
  (continuous_exactTwistedDerivative hT hu).sub (continuous_numericalDerivativeFamily externalStep τ hτ f hfr hfm j)

theorem extendedTwistedPath_bound {T γ M : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (hM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) (r : ℝ) :
    hNorm γ (extendedTwistedPath hT hu r).val ≤ M := by
  let p := Set.projIcc 0 T hT r
  change hNorm γ (airy (-p.val) (u p.val)) ≤ M
  rw [airy_hNorm]
  exact hM p.val p.property

/-- The differential error equation, verified from exact and numerical
equations at every point of each closed step. -/
theorem errorDerivativeFamily_equation (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    (errorDerivativeFamily externalStep hT hτ f hfr hfm hu j t).val =
      B t (errorPath externalStep hT hτ f hfr hfm hu k t).val
        (errorMidpoint externalStep hT hτ f hfr hfm hu k t).val -
      (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t).val := by
  let v := exactTwistedOne hT hu t
  let V := globalInterpolation externalStep τ hτ f hfr hfm k t
  change (exactTwistedDerivative hT hu t).val - (numericalDerivativeFamily externalStep τ hτ f hfr hfm j t).val = _
  rw [exactTwistedDerivative_equation, numerical_derivative_family_equation externalStep τ hτ f hfr hfm hjk ht]
  change (1 / 2 : ℂ) • B t v.val v.val - ((1 / 2 : ℂ) • B t V.val V.val + _) =
    B t (v.val - V.val) (v.val - (1 / 2 : ℂ) • (v.val - V.val)) - _
  rw [B_error_polarization (v.property.of_le (by norm_num)) (V.property.of_le (by norm_num))]
  module

theorem errorPath_hasDerivAt_on_step (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) {j : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (errorPath externalStep hT hτ f hfr hfm hu k r).val m)
      ((errorDerivativeFamily externalStep hT hτ f hfr hfm hu j t).val m) t := by
  have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg j) hτ.le) ht.1
  have htT : t < T := lt_of_lt_of_le ht.2
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal)
  exact (extendedTwistedPath_hasDerivAt hT hu ⟨ht0, htT⟩ m).sub
    (numerical_derivative_family_correct externalStep τ hτ f hfr hfm hjk ht m)

def errorL2Path (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) : ℝ → Sobolev 0 :=
  fun t => inclusionMap 0 1 (by norm_num) (errorPath externalStep hT hτ f hfr hfm hu k t)

def errorNegativeDerivative (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) : ℝ → Sobolev (-pStar) :=
  fun t => inclusionMap (-pStar) 1 (by norm_num [pStar])
    (concatenate τ (errorDerivativeFamily externalStep hT hτ f hfr hfm hu) k t)

theorem error_time_membership (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    MemLp (errorL2Path externalStep hT hτ f hfr hfm hu k) ∞ (volume.restrict (Set.Icc a b)) ∧
    MemLp (errorNegativeDerivative externalStep hT hτ f hfr hfm hu k) ∞ (volume.restrict (Set.Icc a b)) ∧
    WeakTimeDerivative a b (fun t => (errorL2Path externalStep hT hτ f hfr hfm hu k t).val)
      (fun t => (errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t).val) := by
  have hMem : MemLp (concatenate τ (errorDerivativeFamily externalStep hT hτ f hfr hfm hu) k)
      ∞ (volume.restrict (Set.Icc a b)) := memLp_concatenate τ _ (fun j =>
    continuousOn_memLp_top_Icc (continuous_errorDerivativeFamily externalStep hT hτ f hfr hfm hu j).continuousOn) k
  refine ⟨continuousOn_memLp_top_Icc
    (((inclusionMap 0 1 (by norm_num)).continuous.comp (continuous_errorPath externalStep hT hτ f hfr hfm hu k)).continuousOn),
    hMem.continuousLinearMap_comp (inclusionMap (-pStar) 1 (by norm_num [pStar])), ?_⟩
  have hWeak := grid_weakTimeDerivative τ hτ k (errorPath externalStep hT hτ f hfr hfm hu k)
    (errorDerivativeFamily externalStep hT hτ f hfr hfm hu)
    (continuous_errorPath externalStep hT hτ f hfr hfm hu k)
    (continuous_errorDerivativeFamily externalStep hT hτ f hfr hfm hu)
    (fun j hj t ht m => errorPath_hasDerivAt_on_step externalStep hT hτ k hTotal f hfr hfm hu hj ht m) ha hab hb
  exact hWeak

end KdV
