import OriginalProof

/-! Concrete original-literature proposition types. These are definitions, not
axiom declarations. Their full source correspondence and all project consequences
are recorded in source-and-bridge-ledger.md. -/
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory KdV
namespace BareModelCompletion

/-- Li–Wu (2.2)–(2.3), including all four endpoint cases of (2.3).
The source norm and coefficient convention are defined in OriginalProof. -/
abbrev LiWuProduct22 : Prop := KdV.LiWuProductEstimate

/-- Internal historical endpoint port using the published operator (7.3).
The checked two-way correspondence with (7.2) is in ExternalBridges. -/
abbrev HistoricalEndpointStageEstimate : Prop := KdV.LiWuStageEstimate

/-- The integral definition (7.2), rather than an endpoint surrogate. -/
def liWuStage72 (a t : ℝ) (f g : Fourier) : Fourier := fun k =>
  (1 / 2 : ℂ) * ∫ r : ℝ in a..t, B r f g k

/-- Source (4.10): the cross integral with its original integral stage. -/
def liWuCross410 (a t : ℝ) (f : Fourier) : Fourier := fun k =>
  ∫ r : ℝ in a..t, B r f (liWuStage72 a r f f) k

/-- Internal historical arbitrary-step port, written with the integral (7.2).
The standing zero-mean condition is in the paragraph defining (7.2). -/
def HistoricalIntegralStageEstimate : Prop :=
  ∀ T : ℝ, 0 < T → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∀ β : ℝ, sourceStageLower γ ε ≤ β → β ≤ 1 + γ →
      ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ, 0 < τ → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
        t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
          InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
            InSobolev β (liWuStage72 ((n : ℝ) * τ) t f g) ∧
            sourceNorm β (liWuStage72 ((n : ℝ) * τ) t f g) ≤
              C * τ ^ (sourceStagePower γ ε β) * sourceNorm γ f * sourceNorm γ g

/-- Lemma 7.2 with its original complete time grid tau=T/L. -/
def LiWuLemma72Grid : Prop :=
  ∀ T : ℝ, 0 < T → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∀ β : ℝ, sourceStageLower γ ε ≤ β → β ≤ 1 + γ →
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 0 < L →
      let τ := T / (L : ℝ)
      ∀ n : ℕ, n < L → ∀ t : ℝ,
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
      InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
      InSobolev β (sourceBilinearStage ((n : ℝ) * τ) t f g) ∧
      sourceNorm β (sourceBilinearStage ((n : ℝ) * τ) t f g) ≤
        C * τ ^ (sourceStagePower γ ε β) * sourceNorm γ f * sourceNorm γ g

/-- Actual complete-space-valued weak derivative in H^(-23/14). -/
def BochnerWeakTimeDerivative {α : ℝ} (hα : 0 ≤ α) (a b : ℝ)
    (f : ℝ → Sobolev α) (df : ℝ → Sobolev (-pStar)) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
    Function.support φ ⊆ Set.Ioo a b →
    (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) •
      inclusionMap (-pStar) α (by dsimp [pStar]; linarith) (f t)) =
      -(∫ t : ℝ in a..b, ((φ t : ℝ) : ℂ) • df t)

/-- Both conclusions of Proposition 3.4, with an arbitrary fixed bound on the
interval length. Its bound is a parameter of the implicit estimate constant. -/
structure LiWuProposition34 : Prop where
  dynamic : ∀ H : ℝ, 0 < H → ∀ α : ℝ, ∀ hα : 0 ≤ α, α ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f : Fin 3 → ℝ → Sobolev α, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, BochnerWeakTimeDerivative hα a b (f j) (df j)) →
          InSobolev 0 (CIntegral a b (fun t => (f 0 t).val)
            (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ∧
          ∀ i : Fin 3,
            sourceNorm 0 (CIntegral a b (fun t => (f 0 t).val)
              (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ≤
              C * (b - a) * (∏ j : Fin 3, sourceXNorm hα a b (f j) (df j)) +
              C * sourceLInfinityNegative hα a b (f i) *
                (∏ j : Fin 3, if j = i then 1 else sourceLInfinityZero hα a b (f j))
  timeIndependent : ∀ H : ℝ, 0 < H → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f g h : Fourier, InSobolev α f → InSobolev α g → InSobolev α h →
        InSobolev 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ∧
        sourceNorm 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ≤
          C * (b - a) ^ α * sourceNorm α f * sourceNorm α g * sourceNorm α h

/-- The full weaker-norm result (6.22), including -1 < theta <= 0. -/
abbrev BITTheorem65 : Prop := KdV.BITWeakerLipschitz


/-- Source (3.16), with zero-denominator terms omitted by division by zero = 0.
All arguments in the source applications are mean-zero. -/
def bitB2 (t : ℝ) (f g : Fourier) : Fourier := fun k =>
  if k = 0 then 0 else ∑' a : ℤ, Complex.exp (Complex.I * (3 * (k : ℂ) * (a : ℂ) * ((k-a : ℤ) : ℂ)) * (t : ℂ)) *
    f a * g (k-a) / ((a : ℂ) * ((k-a : ℤ) : ℂ))

/-- Source nonresonant operator (3.25). -/
def bitB3 (t : ℝ) (f g h : Fourier) : Fourier := fun k =>
  if k = 0 then 0 else ∑' ab : ℤ × ℤ,
    let a := ab.1
    let b := ab.2
    let c := k-a-b
    Complex.exp (Complex.I * (3 * ((a+b : ℤ) : ℂ) * ((b+c : ℤ) : ℂ) * ((c+a : ℤ) : ℂ)) * (t : ℂ)) *
      f a * g b * h c /
      ((a : ℂ) * ((a+b : ℤ) : ℂ) * ((b+c : ℤ) : ℂ) * ((c+a : ℤ) : ℂ))

/-- Source (3.28). -/
def bitB14 (t : ℝ) (f g h q : Fourier) : Fourier := fun k =>
  if k = 0 then 0 else ∑' abc : ℤ × ℤ × ℤ,
    let a := abc.1
    let b := abc.2.1
    let c := abc.2.2
    let d := k-a-b-c
    if c + d = 0 then 0 else
    Complex.exp (Complex.I * ((k : ℂ)^3-(a : ℂ)^3-(b : ℂ)^3-(c : ℂ)^3-(d : ℂ)^3) * (t : ℂ)) *
      f a * g b * h c * q d /
      (((a+b : ℤ) : ℂ) * ((a+c+d : ℤ) : ℂ) * ((b+c+d : ℤ) : ℂ))

/-- Source (3.29). -/
def bitB24 (t : ℝ) (f g h q : Fourier) : Fourier := fun k =>
  if k = 0 then 0 else ∑' abc : ℤ × ℤ × ℤ,
    let a := abc.1
    let b := abc.2.1
    let c := abc.2.2
    let d := k-a-b-c
    if c + d = 0 then 0 else
    Complex.exp (Complex.I * ((k : ℂ)^3-(a : ℂ)^3-(b : ℂ)^3-(c : ℂ)^3-(d : ℂ)^3) * (t : ℂ)) *
      ((c+d : ℤ) : ℂ) * f a * g b * h c * q d /
      ((a : ℂ) * ((a+b : ℤ) : ℂ) * ((a+c+d : ℤ) : ℂ) * ((b+c+d : ℤ) : ℂ))

/-- Source (3.27) has coefficient one half on B4^1. -/
def bitB4 (t : ℝ) (f g h q : Fourier) : Fourier :=
  (1 / 2 : ℂ) • bitB14 t f g h q + bitB24 t f g h q

/-- The real-valued resonant expression (3.21). -/
def bitAres (f : Fourier) : Fourier := fun k =>
  f k / (k : ℂ) * ((homogeneousNorm 0 f ^ 2 - ‖f k‖ ^ 2 : ℝ) : ℂ)

/-- The full omitted conclusion (4.10), using the input/output truncations (4.8),
(4.11). Derivatives are within the closed solution interval, including its endpoints. -/
def bitAresM412 (m : ℕ) (f v : Fourier) : Fourier := fun k =>
  if |k| < (m : ℤ) then
    v k / (k : ℂ) * ((homogeneousNorm 0 f ^ 2 - ‖v k‖ ^ 2 : ℝ) : ℂ)
  else 0

def BITNormalForm410 (m : ℕ) (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ, k ≠ 0 →
    HasDerivWithinAt (fun r : ℝ => v r k -
      (1 / 6 : ℂ) * cutoff m (bitB2 r (cutoff m (v r)) (cutoff m (v r))) k -
      (1 / 18 : ℂ) * cutoff m (bitB3 r (cutoff m (v r)) (cutoff m (v r)) (cutoff m (v r))) k)
      ((Complex.I / 6) * bitAresM412 m f (cutoff m (v t)) k +
        (Complex.I / 18) * cutoff m (bitB4 t (cutoff m (v t)) (cutoff m (v t))
          (cutoff m (v t)) (cutoff m (v t))) k) (Set.Icc 0 T) t

/-- Full Theorem 4.2, including both its normal-form and estimate conclusions. -/
def BITTheorem42 : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ M₀ : ℝ, 0 ≤ M₀ → ∀ T : ℝ, 0 < T → ∀ r : ℝ, 0 ≤ r →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∀ f : Fourier, ∀ v : ℝ → Fourier,
      RealValued f → InHomSobolev s f → homogeneousNorm s f = r → homogeneousNorm 0 f ≤ M₀ →
      HomSobolevContinuousOn s T v → (∀ t ∈ Set.Icc 0 T, RealValued (v t)) →
      SourceGalerkinODE m T f v →
        BITNormalForm410 m T f v ∧ ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A


/-- The limit certificate with the previously chosen (4.13) bound visible.
Source H^sigma is defined by (3.4), hence on the zero-mean class its norm is
exactly the homogeneous norm, not the target (1+k^2) norm. -/
def BITLimit43 (A s T : ℝ) (f : Fourier) (σ : ℝ) (v : ℝ → Fourier) : Prop :=
  SourceWeakSolution T f v ∧ HomogeneousEssentiallyBounded s T v ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm 0 (v t) = homogeneousNorm 0 f) ∧
      ∃ G : ℕ → ℝ → Fourier, ∃ idx : ℕ → ℕ, StrictMono idx ∧
        (∀ m, HomSobolevContinuousOn s T (G m) ∧
          (∀ t ∈ Set.Icc 0 T, RealValued (G m t)) ∧ SourceGalerkinODE (m + 1) T f (G m) ∧
          ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (G m t) ≤ A) ∧
        (∀ p : ℝ, 1 < p → SourceLpConvergence σ T p (fun n => G (idx n)) v) ∧
        SourceWeakStarConvergence s T (fun n => G (idx n)) v

/-- The complete global existence and energy statement of BIT Proposition 4.1,
for the source's full-tail Galerkin equation. The printed energy uses squares. -/
def BITProposition41 : Prop :=
  ∀ f : Fourier, RealValued f → InHomSobolev 0 f → ∀ m : ℕ, 0 < m →
    ∃ v : ℝ → Fourier,
      (∀ T : ℝ, 0 < T → HomSobolevContinuousOn 0 T v ∧
        (∀ t ∈ Set.Icc 0 T, RealValued (v t)) ∧ SourceGalerkinODE m T f v) ∧
      ∀ t : ℝ, 0 ≤ t → homogeneousNorm 0 (v t) ^ 2 = homogeneousNorm 0 f ^ 2

/-- The given source Galerkin family is global and energy conserving, as in
Proposition 4.1. These time ranges are not restricted to the limit horizon T. -/
def BITGalerkinFamily (s : ℝ) (f : Fourier) (G : ℕ → ℝ → Fourier) : Prop :=
  ∀ m : ℕ,
    (∀ U : ℝ, 0 < U → HomSobolevContinuousOn s U (G m) ∧
      (∀ t ∈ Set.Icc 0 U, RealValued (G m t)) ∧ SourceGalerkinODE (m + 1) U f (G m)) ∧
    ∀ t : ℝ, 0 ≤ t → homogeneousNorm 0 (G m t) ^ 2 = homogeneousNorm 0 f ^ 2

/-- Literal strong L^p convergence in the source complete homogeneous Hilbert
space, for every finite p>1, with actual vector-valued representatives. -/
def BITStrongLp43 (σ T : ℝ) (G : ℕ → ℝ → Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ W : ℕ → ℝ → L2Seq, ∃ w : ℝ → L2Seq,
    (∀ n, ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), (W n t).val = homogeneousWeighted σ (G n t)) ∧
    (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), (w t).val = homogeneousWeighted σ (v t)) ∧
    ∀ p : ℝ, 1 < p →
      (∀ n, MemLp (W n) (ENNReal.ofReal p) (volume.restrict (Set.Icc 0 T))) ∧
      MemLp w (ENNReal.ofReal p) (volume.restrict (Set.Icc 0 T)) ∧
      Filter.Tendsto (fun n => eLpNorm (fun t => W n t - w t) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0)

/-- All Galerkin family data precede the subsequence in Theorem 4.3. -/
def BITLimit43For (A s T : ℝ) (f : Fourier) (σ : ℝ)
    (G : ℕ → ℝ → Fourier) (v : ℝ → Fourier) : Prop :=
  SourceWeakSolution T f v ∧ HomogeneousEssentiallyBounded s T v ∧
    (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A) ∧
    (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm 0 (v t) = homogeneousNorm 0 f) ∧
    ∃ idx : ℕ → ℕ, StrictMono idx ∧
      BITStrongLp43 σ T (fun n => G (idx n)) v ∧
      SourceWeakStarConvergence s T (fun n => G (idx n)) v

/-- Joint full Theorems 4.2 and 4.3: a common bound with exactly their stated
parameter dependence. This joins source statements, not project consequences. -/
def BITTheorems42And43 : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ M₀ : ℝ, 0 ≤ M₀ → ∀ T : ℝ, 0 < T → ∀ r : ℝ, 0 ≤ r →
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ m : ℕ, 0 < m → ∀ f : Fourier, ∀ v : ℝ → Fourier,
        RealValued f → InHomSobolev s f → homogeneousNorm s f = r → homogeneousNorm 0 f ≤ M₀ →
        HomSobolevContinuousOn s T v → (∀ t ∈ Set.Icc 0 T, RealValued (v t)) →
        SourceGalerkinODE m T f v →
          BITNormalForm410 m T f v ∧ ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A) ∧
      (0 < s → ∀ f : Fourier, RealValued f → InHomSobolev s f →
        homogeneousNorm s f = r → homogeneousNorm 0 f ≤ M₀ →
        ∀ G : ℕ → ℝ → Fourier,
          BITGalerkinFamily s f G →
        ∀ σ : ℝ, 0 < σ → σ < s → ∃ v : ℝ → Fourier, BITLimit43For A s T f σ G v)


/-- Literal averaging covariance (4.15), before combining the exponentials. -/
def liWuEta415 (τ α β : ℝ) : ℂ :=
  (τ : ℂ)⁻¹ * (∫ r : ℝ in (0 : ℝ)..τ,
    Complex.exp (-Complex.I * (r : ℂ) * (α : ℂ)) * Complex.exp (-Complex.I * (r : ℂ) * (β : ℂ))) -
    phaseAverage τ α * phaseAverage τ β

/-- Source remainder (6.1), with exactly the covariance (4.15). -/
def liWuRemainder61 (τ t : ℝ) (f₁ f₂ f₃ : Fourier) : Fourier := fun k =>
  if k = 0 then 0 else
    (-(τ : ℂ) / (18 * Complex.I * (k : ℂ))) *
      ∑' ab : ℤ × ℤ,
        let a := ab.1
        let b := ab.2
        let c := k - a - b
        let p := a + b
        let α : ℝ := 3 * (a : ℝ) * (b : ℝ) * (p : ℝ)
        let β : ℝ := 3 * (k : ℝ) * (c : ℝ) * (p : ℝ)
        let Φ : ℤ := k ^ 3 - a ^ 3 - b ^ 3 - c ^ 3
        if p = 0 then 0 else
          Complex.exp (-Complex.I * (t : ℂ) * (Φ : ℂ)) * liWuEta415 τ α β *
            f₁ a * f₂ b * f₃ c

/-- The algebraic step relation (5.2), (4.20)--(4.23), throughout the source's
positive regularity range. Its stage, cross integral and averaging covariance
are represented by the original defining formulas. -/
def LiWuStep52 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ τ : ℝ, 0 < τ → ∀ n : ℕ, ∀ f : Fourier,
    InSobolev γ f → MeanZero f →
      airy (-(((n + 1 : ℕ) : ℝ) * τ)) (step τ (airy ((n : ℝ) * τ) f)) =
        f + liWuStage72 ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) f f +
          liWuCross410 ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) f -
          liWuRemainder61 τ ((n : ℝ) * τ) f f f


/-- The published identity on the original complete grid tau=T/L. -/
def LiWuStep52Grid : Prop :=
  ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ T : ℝ, 0 < T → ∀ L : ℕ, 0 < L →
    let τ := T / (L : ℝ)
    ∀ n : ℕ, n < L → ∀ f : Fourier,
    InSobolev γ f → MeanZero f →
      airy (-(((n + 1 : ℕ) : ℝ) * τ)) (step τ (airy ((n : ℝ) * τ) f)) =
        f + liWuStage72 ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) f f +
          liWuCross410 ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) f -
          liWuRemainder61 τ ((n : ℝ) * τ) f f f


/-- The local solution-map condition with continuous-time supremum conventions.
This is a concrete comparison predicate, not a new literature input; full
quantitative source inputs are defined separately below. -/
def SourceLocalLipschitzAllTimes (s T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ ∀ g : Fourier,
    RealValued g → InHomSobolev s g → homogeneousNorm s (g - f) < r →
      ∀ w : ℝ → Fourier, SourceWeakSolution T g w → HomSobolevContinuousOn s T w →
        ∀ t ∈ Set.Icc 0 T,
          homogeneousNorm s (v t - w t) ≤ C * homogeneousNorm s (f - g)


/-- The actual constructed-limit class of the original Theorem 4.3, with
vector-valued strong convergence, rather than the historical scalar certificate. -/
def BITConstructedLimit43 (s T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ σ < s ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ G : ℕ → ℝ → Fourier,
    BITGalerkinFamily s f G ∧
    (∀ m, ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (G m t) ≤ A) ∧ BITLimit43For A s T f σ G v

/-- Uniqueness in Definition 3.1, before restricting to the historical continuous
comparison class. -/
def BITUniqueWeak (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∀ w : ℝ → Fourier, SourceWeakSolution T f w → ∀ t ∈ Set.Icc 0 T, w t = v t

/-- Full quantitative (5.18), keeping the printed dependence of T* on
||w0||_s+||w0||_s (p.21) and C' on ||v0||_s+||w0||_s separately. No local
boundedness of either parameter function is imported. -/
def BITDependence518 : Prop :=
  ∀ s : ℝ, 1 / 2 < s → ∀ T : ℝ, 0 < T →
    ∃ δ : ℝ → ℝ, (∀ r : ℝ, 0 ≤ r → 0 < δ r ∧ δ r ≤ T) ∧
    ∃ C' : ℝ → ℝ, (∀ r : ℝ, 0 ≤ r → 0 < C' r) ∧
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev s f → InHomSobolev s g →
      ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
      HomSobolevContinuousOn s T v → HomSobolevContinuousOn s T w →
      ∀ t ∈ Set.Icc 0 T,
        homogeneousNorm s (w t - v t) ≤
          (C' (homogeneousNorm s f + homogeneousNorm s g) + 1) ^
            (⌊T / δ (2 * homogeneousNorm s g)⌋₊ + 1) * homogeneousNorm s (g - f)

/-- Full Theorem 5.1, including the quantitative (5.18). -/
structure BITTheorem51 : Prop where
  regularity : ∀ s : ℝ, 1 / 2 < s → ∀ T : ℝ, 0 < T → ∀ f : Fourier,
    RealValued f → InHomSobolev s f → ∀ v : ℝ → Fourier, BITConstructedLimit43 s T f v →
      HomSobolevContinuousOn s T v ∧ BITUniqueWeak T f v ∧
      ∀ t ∈ Set.Icc 0 T, homogeneousNorm 0 (v t) = homogeneousNorm 0 f
  dependence : BITDependence518

/-- Literal L-infinity homogeneous Sobolev norm, with source spatial measure. -/
def bitHomSup (s T : ℝ) (v : ℝ → Fourier) : ℝ :=
  (eLpNorm (fun t => homogeneousNorm s (v t)) ∞ (volume.restrict (Set.Icc 0 T))).toReal

/-- The theta=s application of (6.7) specified in Theorem 6.3. C0 is the
explicit upper bound from (6.3), and the constant/step choices precede flows.
Its parameter dependence follows (6.2)--(6.5). -/
def BITDependence67 : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → ∀ T : ℝ, 0 < T → ∀ C₀ : ℝ, 0 ≤ C₀ →
    ∃ τ : ℝ, 0 < τ ∧ ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev s f → InHomSobolev s g →
      ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
      HomogeneousEssentiallyBounded s T v → HomogeneousEssentiallyBounded s T w →
      bitHomSup s T v + bitHomSup s T w ≤ C₀ →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t - w t) ≤
        C' * (2 * C + 1) ^ (⌊T / τ⌋₊ + 1) * homogeneousNorm s (f - g)

/-- Literal norm formulation of (6.7); the equivalence with the a.e.
formulation is proved in RegularityBridges. -/
def BITDependence67Norm : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → ∀ T : ℝ, 0 < T → ∀ C₀ : ℝ, 0 ≤ C₀ →
    ∃ τ : ℝ, 0 < τ ∧ ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev s f → InHomSobolev s g →
      ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
      HomogeneousEssentiallyBounded s T v → HomogeneousEssentiallyBounded s T w →
      bitHomSup s T v + bitHomSup s T w ≤ C₀ →
      bitHomSup s T (fun t => v t - w t) ≤
        C' * (2 * C + 1) ^ (⌊T / τ⌋₊ + 1) * homogeneousNorm s (f - g)

/-- The governing index in Theorem 6.1 (p.26), used in (6.2)--(6.7):
zero below the endpoint, and every positive index at the endpoint. -/
def BITComparisonIndex (s θ₀ : ℝ) : Prop :=
  (s < 1 / 2 ∧ θ₀ = 0) ∨ (s = 1 / 2 ∧ 0 < θ₀)

/-- Full original quantitative comparison (6.7), including (6.3)/(6.5).
The choices depend on s, θ₀ and the lower-norm bound C₀. With that bound
fixed they precede the final time, data and flows. The H^s bound is NOT
an argument of these choices. In particular θ₀=0 is retained below 1/2. -/
def BITDependence67OriginalNorm : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → ∀ θ₀ : ℝ, BITComparisonIndex s θ₀ →
    ∀ C₀ : ℝ, 0 ≤ C₀ →
    ∃ τ : ℝ, 0 < τ ∧ ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, 0 < T →
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev s f → InHomSobolev s g →
      ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
      HomogeneousEssentiallyBounded s T v → HomogeneousEssentiallyBounded s T w →
      HomogeneousEssentiallyBounded θ₀ T v → HomogeneousEssentiallyBounded θ₀ T w →
      bitHomSup θ₀ T v + bitHomSup θ₀ T w ≤ C₀ →
      bitHomSup s T (fun t => v t - w t) ≤
        C' * (2 * C + 1) ^ (⌊T / τ⌋₊ + 1) * homogeneousNorm s (f - g)

/-- Full Theorem 6.3, including its quantitative (6.7) dependence. -/
structure BITTheorem63 : Prop where
  regularity : ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → ∀ T : ℝ, 0 < T → ∀ f : Fourier,
    RealValued f → InHomSobolev s f → ∀ v : ℝ → Fourier, BITConstructedLimit43 s T f v →
      HomSobolevContinuousOn s T v ∧ BITUniqueWeak T f v
  dependence : BITDependence67OriginalNorm

/-- Literal L-infinity norm form of Theorem 6.5 (6.22). -/
def BITTheorem65Norm : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∀ θ : ℝ, -1 < θ → θ ≤ 0 →
    ∃ C' : ℝ, 0 < C' ∧ ∃ CM : ℝ, 0 < CM ∧ ∀ T : ℝ, 0 < T →
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev 0 f → InHomSobolev 0 g →
        homogeneousNorm 0 f + homogeneousNorm 0 g ≤ M →
        ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
          HomSobolevContinuousOn 0 T v → HomSobolevContinuousOn 0 T w →
            bitHomSup θ T (fun t => v t - w t) ≤ C' * CM ^ T * homogeneousNorm θ (f - g)


/-- Unrestricted real bound parameters, including the vacuous negative cases. -/
def BITTheorems42And43AllBounds : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ M₀ : ℝ, ∀ T : ℝ, 0 < T → ∀ r : ℝ,
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ m : ℕ, 0 < m → ∀ f : Fourier, ∀ v : ℝ → Fourier,
        RealValued f → InHomSobolev s f → homogeneousNorm s f = r → homogeneousNorm 0 f ≤ M₀ →
        HomSobolevContinuousOn s T v → (∀ t ∈ Set.Icc 0 T, RealValued (v t)) →
        SourceGalerkinODE m T f v →
          BITNormalForm410 m T f v ∧ ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A) ∧
      (0 < s → ∀ f : Fourier, RealValued f → InHomSobolev s f →
        homogeneousNorm s f = r → homogeneousNorm 0 f ≤ M₀ →
        ∀ G : ℕ → ℝ → Fourier,
          BITGalerkinFamily s f G →
        ∀ σ : ℝ, 0 < σ → σ < s → ∃ v : ℝ → Fourier, BITLimit43For A s T f σ G v)



def BITTheorem65AllBounds : Prop :=
  ∀ M : ℝ, ∀ θ : ℝ, -1 < θ → θ ≤ 0 →
    ∃ C' : ℝ, 0 < C' ∧ ∃ CM : ℝ, 0 < CM ∧ ∀ T : ℝ, 0 < T →
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev 0 f → InHomSobolev 0 g →
        homogeneousNorm 0 f + homogeneousNorm 0 g ≤ M →
        ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
          HomSobolevContinuousOn 0 T v → HomSobolevContinuousOn 0 T w →
            bitHomSup θ T (fun t => v t - w t) ≤ C' * CM ^ T * homogeneousNorm θ (f - g)



end BareModelCompletion
