import ExternalFlowExistence
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def SourceUniqueContinuous (s T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∀ w : ℝ → Fourier, SourceWeakSolution T f w → HomSobolevContinuousOn s T w →
    ∀ t ∈ Set.Icc 0 T, w t = v t

/-- Local Lipschitz dependence in the source solution norm. The time conclusion
is the essential-supremum inequality in its almost-everywhere form. -/
def SourceLocalLipschitz (s T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ ∀ g : Fourier,
    RealValued g → InHomSobolev s g → homogeneousNorm s (g - f) < r →
      ∀ w : ℝ → Fourier, SourceWeakSolution T g w → HomSobolevContinuousOn s T w →
        ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
          homogeneousNorm s (v t - w t) ≤ C * homogeneousNorm s (f - g)

/-- Explicit external premise: Theorem 5.1, arXiv v2, for the limiting solution
constructed in Theorem 4.3. Uniqueness is used only in the continuous `Hdot^s`
class; no uniqueness in arbitrary essentially bounded weak classes is assumed.
The Lipschitz conclusion (5.18) is retained in its local solution-map form. -/
def BITHigherRegularity : Prop :=
  ∀ s : ℝ, 1 / 2 < s → ∀ T : ℝ, 0 < T → ∀ f : Fourier,
    RealValued f → InHomSobolev s f → ∀ v : ℝ → Fourier,
      SourceConstructedLimit s T f v →
        HomSobolevContinuousOn s T v ∧ SourceUniqueContinuous s T f v ∧
        SourceLocalLipschitz s T f v ∧
        ∀ t ∈ Set.Icc 0 T, homogeneousNorm 0 (v t) = homogeneousNorm 0 f

/-- Explicit external premise: Theorem 6.3 with its full positive low-regularity
range, the same source construction, and the dependence stated through (6.7). -/
def BITLowRegularity : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → ∀ T : ℝ, 0 < T → ∀ f : Fourier,
    RealValued f → InHomSobolev s f → ∀ v : ℝ → Fourier,
      SourceConstructedLimit s T f v →
        HomSobolevContinuousOn s T v ∧ SourceUniqueContinuous s T f v ∧ SourceLocalLipschitz s T f v

/-- Explicit external premise: Theorem 6.4. The primary statement specifies
uniqueness of class `C([0,T]; Hdot^0)`, which is retained explicitly. It is not
silently strengthened to uniqueness of every `L∞` weak solution. -/
def BITL2Wellposedness : Prop :=
  ∀ T : ℝ, 0 < T → ∀ f : Fourier, RealValued f → InHomSobolev 0 f →
    ∃ v : ℝ → Fourier, SourceWeakSolution T f v ∧ HomSobolevContinuousOn 0 T v ∧
      SourceUniqueContinuous 0 T f v ∧ SourceLocalLipschitz 0 T f v

/-- Explicit external premise: the complete weaker-norm estimate of Theorem 6.5
(6.22), with `-1 < θ ≤ 0` and initial `L²` norms summing to at most `M`.
Its two constants precede `T` and both data, as their stated dependence is only
on `M,θ`. Both flows are in the continuous solution class of Theorem 6.4.
The `L∞` bound is stated almost everywhere; endpoint bounds are internal work. -/
def BITWeakerLipschitz : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∀ θ : ℝ, -1 < θ → θ ≤ 0 →
    ∃ C' : ℝ, 0 < C' ∧ ∃ CM : ℝ, 0 < CM ∧ ∀ T : ℝ, 0 < T →
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev 0 f → InHomSobolev 0 g →
        homogeneousNorm 0 f + homogeneousNorm 0 g ≤ M →
        ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
          HomSobolevContinuousOn 0 T v → HomSobolevContinuousOn 0 T w →
            ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
              homogeneousNorm θ (v t - w t) ≤ C' * CM ^ T * homogeneousNorm θ (f - g)

/-- The regularity conclusion is obtained by the two cited ranges, without
postulating a new a priori bound on the limiting flow. -/
theorem constructed_limit_continuous (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    {f : Fourier} (hfr : RealValued f) (hf : InHomSobolev s f) {v : ℝ → Fourier}
    (hv : SourceConstructedLimit s T f v) : HomSobolevContinuousOn s T v := by
  by_cases hh : 1 / 2 < s
  · exact (externalHigh s hh T hT f hfr hf v hv).1
  · exact (externalLow s hs (le_of_not_gt hh) T hT f hfr hf v hv).1

end KdV
