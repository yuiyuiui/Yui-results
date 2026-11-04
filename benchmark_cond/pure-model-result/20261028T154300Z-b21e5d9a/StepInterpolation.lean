import SmoothOperators
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The cross integral `C_n`, with the exact full bilinear stage. -/
def frozenCross (a t : ℝ) (f : Fourier) : Fourier := fun k =>
  ∫ s : ℝ in a..t, B s f (bilinearStage a s f f) k

/-- The quadratic stage integral `Q_n`. -/
def frozenSquare (a t : ℝ) (f : Fourier) : Fourier := fun k =>
  (1 / 2 : ℂ) * ∫ s : ℝ in a..t,
    B s (bilinearStage a s f f) (bilinearStage a s f f) k

def endpointCorrection (τ a : ℝ) (f : Fourier) : Fourier :=
  frozenSquare a (a + τ) f + remainder τ a f f f

/-- The paper's full continuous interpolation on one step. -/
def localInterpolation (τ a t : ℝ) (f : Fourier) : Fourier :=
  f + bilinearStage a t f f + frozenCross a t f + frozenSquare a t f -
    (((t - a) / τ : ℝ) : ℂ) • endpointCorrection τ a f

def interpolationRemainder (τ a t : ℝ) (f : Fourier) : Fourier :=
  localInterpolation τ a t f - (f + bilinearStage a t f f)

/-- Explicit external identity: Li--Wu (4.20)--(4.23), equivalently (5.2),
specialized to order-one inputs. This is an algebraic identity for the actual
unfiltered physical update and the already defined covariance remainder.
No residual or stability estimate is included in this premise. -/
def LiWuStepIdentity : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ n : ℕ, ∀ f : Fourier,
    InSobolev 1 f → RealValued f → MeanZero f →
      airy (-(((n + 1 : ℕ) : ℝ) * τ)) (step τ (airy ((n : ℝ) * τ) f)) =
        f + bilinearStage ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) f f +
          frozenCross ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) f -
          remainder τ ((n : ℝ) * τ) f f f

theorem localInterpolation_left {τ a : ℝ} (f : Fourier) :
    localInterpolation τ a a f = f := by
  funext k
  simp [localInterpolation, frozenCross, frozenSquare, bilinearStage]

theorem localInterpolation_right (externalStep : LiWuStepIdentity)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {f : Fourier}
    (hf : InSobolev 1 f) (hfr : RealValued f) (hfm : MeanZero f) :
    localInterpolation τ ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) f =
      airy (-(((n + 1 : ℕ) : ℝ) * τ)) (step τ (airy ((n : ℝ) * τ) f)) := by
  rw [externalStep τ hτ n f hf hfr hfm]
  have heq : (((n + 1 : ℕ) : ℝ) * τ) = (n : ℝ) * τ + τ := by push_cast; ring
  rw [heq]
  unfold localInterpolation endpointCorrection
  have hfrac : ((n : ℝ) * τ + τ - (n : ℝ) * τ) / τ = 1 := by
    field_simp [hτ.ne']
    ring
  rw [hfrac, Complex.ofReal_one, one_smul]
  abel

theorem stage_meanZero (a t : ℝ) (f g : Fourier) : MeanZero (bilinearStage a t f g) := by
  change (1 / 6 : ℂ) * (J t f g 0 - J a f g 0) = 0
  rw [J_meanZero, J_meanZero, sub_self, mul_zero]

theorem frozenCross_meanZero (a t : ℝ) (f : Fourier) : MeanZero (frozenCross a t f) := by
  change (∫ s : ℝ in a..t, B s f (bilinearStage a s f f) 0) = 0
  simp [B, derivative]

theorem frozenSquare_meanZero (a t : ℝ) (f : Fourier) : MeanZero (frozenSquare a t f) := by
  change (1 / 2 : ℂ) * (∫ s : ℝ in a..t, B s _ _ 0) = 0
  simp [B, derivative]

theorem stage_hasDerivAt {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hfm : MeanZero f) (hgm : MeanZero g) (a t : ℝ) (k : ℤ) :
    HasDerivAt (fun r : ℝ => bilinearStage a r f g k) ((1 / 2 : ℂ) * B t f g k) t := by
  change HasDerivAt (fun r : ℝ => (1 / 6 : ℂ) * (J r f g k - J a f g k))
    ((1 / 2 : ℂ) * B t f g k) t
  have h := ((J_fixed_hasDerivAt hf hg hfm hgm k t).sub_const (J a f g k)).const_mul (1 / 6 : ℂ)
  have hd : (1 / 6 : ℂ) * (3 * B t f g k) = (1 / 2 : ℂ) * B t f g k := by ring
  simpa only [hd] using h

theorem sobolev_integral_val {s : ℝ} {f : ℝ → Sobolev s} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t : ℝ in a..b, f t).val = fun k => ∫ t : ℝ in a..b, (f t).val k := by
  funext k
  exact ((coefficientMap s k).intervalIntegral_comp_comm hf).symm

def frozenCrossBundled (a t : ℝ) (f : Sobolev 2) : Sobolev 1 :=
  ∫ s : ℝ in a..t, BTwoBundled s f (stageTwoBundled a s f f)

def frozenSquareBundled (a t : ℝ) (f : Sobolev 2) : Sobolev 1 :=
  (1 / 2 : ℂ) • ∫ s : ℝ in a..t,
    BTwoBundled s (stageTwoBundled a s f f) (stageTwoBundled a s f f)

theorem continuous_cross_integrand (a : ℝ) (f : Sobolev 2) :
    Continuous (fun s : ℝ => BTwoBundled s f (stageTwoBundled a s f f)) :=
  continuous_BTwoBundled continuous_id continuous_const (continuous_stageTwoBundled a f f)

theorem continuous_square_integrand (a : ℝ) (f : Sobolev 2) :
    Continuous (fun s : ℝ => BTwoBundled s (stageTwoBundled a s f f) (stageTwoBundled a s f f)) :=
  continuous_BTwoBundled continuous_id (continuous_stageTwoBundled a f f) (continuous_stageTwoBundled a f f)

theorem frozenCrossBundled_val (a t : ℝ) (f : Sobolev 2) :
    (frozenCrossBundled a t f).val = frozenCross a t f.val :=
  sobolev_integral_val ((continuous_cross_integrand a f).intervalIntegrable a t)

theorem frozenSquareBundled_val (a t : ℝ) (f : Sobolev 2) :
    (frozenSquareBundled a t f).val = frozenSquare a t f.val := by
  change (1 / 2 : ℂ) • (∫ s : ℝ in a..t,
    BTwoBundled s (stageTwoBundled a s f f) (stageTwoBundled a s f f)).val = _
  rw [sobolev_integral_val ((continuous_square_integrand a f).intervalIntegrable a t)]
  rfl

theorem continuous_frozenCrossBundled (a : ℝ) (f : Sobolev 2) :
    Continuous (fun t : ℝ => frozenCrossBundled a t f) :=
  (intervalIntegral.differentiable_integral_of_continuous (continuous_cross_integrand a f)).continuous

theorem continuous_frozenSquareBundled (a : ℝ) (f : Sobolev 2) :
    Continuous (fun t : ℝ => frozenSquareBundled a t f) := by
  unfold frozenSquareBundled
  exact (continuous_const (y := (1 / 2 : ℂ))).smul
    (intervalIntegral.differentiable_integral_of_continuous (a := a) (continuous_square_integrand a f)).continuous

theorem frozenCross_hasDerivAt (a t : ℝ) (f : Sobolev 2) (k : ℤ) :
    HasDerivAt (fun r : ℝ => frozenCross a r f.val k)
      (B t f.val (bilinearStage a t f.val f.val) k) t := by
  have hc : Continuous (fun s : ℝ => B s f.val (bilinearStage a s f.val f.val) k) :=
    (coefficientMap 1 k).continuous.comp (continuous_cross_integrand a f)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem frozenSquare_hasDerivAt (a t : ℝ) (f : Sobolev 2) (k : ℤ) :
    HasDerivAt (fun r : ℝ => frozenSquare a r f.val k)
      ((1 / 2 : ℂ) * B t (bilinearStage a t f.val f.val) (bilinearStage a t f.val f.val) k) t := by
  have hc : Continuous (fun s : ℝ => B s (bilinearStage a s f.val f.val) (bilinearStage a s f.val f.val) k) :=
    (coefficientMap 1 k).continuous.comp (continuous_square_integrand a f)
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (1 / 2 : ℂ)

/-- The higher norm of the remainder is used only for regularity, and follows
from the exact update identity. Its size will be bounded by the proved rough
remainder estimate, independently of this higher norm. -/
theorem remainder_inSobolev_one (externalStep : LiWuStepIdentity)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    InSobolev 1 (remainder τ ((n : ℝ) * τ) f.val f.val f.val) := by
  let a : ℝ := (n : ℝ) * τ
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  have hf1 := f.property.of_le (by norm_num : (1 : ℝ) ≤ 2)
  have hAlg : SobolevAlgebra 1 := by simpa using integer_sobolev_algebra 0
  have hnext : InSobolev 1 (airy (-b) (step τ (airy a f.val))) :=
    airy_inSobolev (step_in_algebra hAlg τ (airy_inSobolev hf1 a)) (-b)
  have hstage := (bilinearStage_h1_bound (f.property.of_le (by norm_num))
    (f.property.of_le (by norm_num)) a b).1
  have hcross : InSobolev 1 (frozenCross a b f.val) := by
    rw [← frozenCrossBundled_val a b f]
    exact (frozenCrossBundled a b f).property
  have hid := externalStep τ hτ n f.val hf1 hfr hfm
  have heq : remainder τ a f.val f.val f.val =
      f.val + bilinearStage a b f.val f.val + frozenCross a b f.val -
        airy (-b) (step τ (airy a f.val)) := by
    linear_combination hid
  rw [heq]
  exact ((hf1.add hstage).add hcross).sub hnext

theorem endpointCorrection_inSobolev_one (externalStep : LiWuStepIdentity)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    InSobolev 1 (endpointCorrection τ ((n : ℝ) * τ) f.val) := by
  have hQ : InSobolev 1 (frozenSquare ((n : ℝ) * τ) ((n : ℝ) * τ + τ) f.val) := by
    rw [← frozenSquareBundled_val _ _ f]
    exact (frozenSquareBundled _ _ f).property
  exact hQ.add (remainder_inSobolev_one externalStep hτ n f hfr hfm)

def endpointCorrectionBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  ⟨endpointCorrection τ ((n : ℝ) * τ) f.val,
    endpointCorrection_inSobolev_one externalStep hτ n f hfr hfm⟩

def localInterpolationBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  inclusionMap 1 2 (by norm_num) f +
    inclusionMap 1 2 (by norm_num) (stageTwoBundled ((n : ℝ) * τ) t f f) +
    frozenCrossBundled ((n : ℝ) * τ) t f + frozenSquareBundled ((n : ℝ) * τ) t f -
    ((((t - (n : ℝ) * τ) / τ) : ℝ) : ℂ) •
      endpointCorrectionBundled externalStep τ hτ n f hfr hfm

theorem localInterpolationBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (localInterpolationBundled externalStep τ hτ n t f hfr hfm).val =
      localInterpolation τ ((n : ℝ) * τ) t f.val := by
  change f.val + bilinearStage ((n : ℝ) * τ) t f.val f.val +
    (frozenCrossBundled ((n : ℝ) * τ) t f).val +
    (frozenSquareBundled ((n : ℝ) * τ) t f).val - _ = _
  rw [frozenCrossBundled_val, frozenSquareBundled_val]
  rfl

theorem continuous_localInterpolationBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => localInterpolationBundled externalStep τ hτ n t f hfr hfm) := by
  unfold localInterpolationBundled
  have hC := continuous_frozenCrossBundled ((n : ℝ) * τ) f
  have hQ := continuous_frozenSquareBundled ((n : ℝ) * τ) f
  fun_prop

end KdV
