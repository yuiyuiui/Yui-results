import Mathlib

/-!
Work in progress toward Theorem 1 of the supplied paper.
Only proved internal lemmas are present. There is not yet an exported `theorem_1`.
The raw coefficient model is used to retain every integer Fourier mode.
-/

noncomputable section

open scoped ComplexConjugate ENNReal
open MeasureTheory

namespace KdV

abbrev Fourier := ℤ → ℂ

/-- The paper's torus, with period exactly `2π`. -/
abbrev Torus := AddCircle (2 * Real.pi)

instance periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Normalized measure, of total mass one. -/
def normalizedMeasure : Measure Torus := AddCircle.haarAddCircle

instance : IsProbabilityMeasure normalizedMeasure := by
  unfold normalizedMeasure
  infer_instance

/-- `(1+k²)^(s/2)`, the square root of the Sobolev norm weight. -/
def weight (s : ℝ) (k : ℤ) : ℝ := (1 + (k : ℝ) ^ 2) ^ (s / 2)

theorem weight_pos (s : ℝ) (k : ℤ) : 0 < weight s k := by
  unfold weight
  positivity

@[simp] theorem weight_zero (k : ℤ) : weight 0 k = 1 := by simp [weight]

def weighted (s : ℝ) (f : Fourier) : Fourier := fun k => (weight s k : ℂ) * f k

@[simp] theorem weighted_zero (f : Fourier) : weighted 0 f = f := by
  funext k
  simp [weighted]

/-- Weighted square summability; no restriction on Fourier support. -/
def InSobolev (s : ℝ) (f : Fourier) : Prop := Memℓp (weighted s f) 2

@[simp] theorem weighted_add (s : ℝ) (f g : Fourier) :
    weighted s (f + g) = weighted s f + weighted s g := by
  funext k
  simp [weighted, mul_add]

@[simp] theorem weighted_sub (s : ℝ) (f g : Fourier) :
    weighted s (f - g) = weighted s f - weighted s g := by
  funext k
  simp [weighted, mul_sub]

@[simp] theorem weighted_smul (s : ℝ) (z : ℂ) (f : Fourier) :
    weighted s (z • f) = z • weighted s f := by
  funext k
  simp [weighted, mul_left_comm]

theorem InSobolev.add {s : ℝ} {f g : Fourier} (hf : InSobolev s f)
    (hg : InSobolev s g) : InSobolev s (f + g) := by
  unfold InSobolev at *
  rw [weighted_add]
  exact hf.add hg

theorem InSobolev.sub {s : ℝ} {f g : Fourier} (hf : InSobolev s f)
    (hg : InSobolev s g) : InSobolev s (f - g) := by
  unfold InSobolev at *
  rw [weighted_sub]
  exact hf.sub hg

theorem InSobolev.smul {s : ℝ} {f : Fourier} (hf : InSobolev s f)
    (z : ℂ) : InSobolev s (z • f) := by
  unfold InSobolev at *
  rw [weighted_smul]
  exact hf.const_smul z

def sobolevSubmodule (s : ℝ) : Submodule ℂ Fourier where
  carrier := InSobolev s
  zero_mem' := by
    change Memℓp (weighted s (0 : Fourier)) 2
    rw [show weighted s (0 : Fourier) = 0 by funext k; simp [weighted]]
    exact zero_memℓp
  add_mem' := InSobolev.add
  smul_mem' z _ hf := hf.smul z

/-- A type synonym prevents inheriting the pointwise topology on raw sequences.
Its topology below is the complete weighted `ℓ²` norm topology. -/
def Sobolev (s : ℝ) := ↥(sobolevSubmodule s)

instance (s : ℝ) : AddCommGroup (Sobolev s) :=
  inferInstanceAs (AddCommGroup ↥(sobolevSubmodule s))

instance (s : ℝ) : Module ℂ (Sobolev s) :=
  inferInstanceAs (Module ℂ ↥(sobolevSubmodule s))

instance (s : ℝ) : CoeFun (Sobolev s) (fun _ => ℤ → ℂ) := ⟨fun f => f.val⟩

/-- Every weighted square-summable coefficient sequence is a genuine Hilbert-space
element; this equivalence will also transport the complete norm topology. -/
def sobolevEquiv (s : ℝ) : Sobolev s ≃ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun f := ⟨weighted s f.val, f.property⟩
  invFun g := ⟨fun k => (weight s k : ℂ)⁻¹ * g k, by
    change Memℓp (weighted s (fun k => (weight s k : ℂ)⁻¹ * g k)) 2
    have h : weighted s (fun k => (weight s k : ℂ)⁻¹ * g k) = g := by
      funext k
      simp [KdV.weighted, (Complex.ofReal_ne_zero.mpr (weight_pos s k).ne')]
    rw [h]
    exact g.property⟩
  left_inv f := by
    apply Subtype.ext
    funext k
    simp [KdV.weighted, (Complex.ofReal_ne_zero.mpr (weight_pos s k).ne')]
  right_inv g := by
    apply Subtype.ext
    funext k
    simp [KdV.weighted, (Complex.ofReal_ne_zero.mpr (weight_pos s k).ne')]
  map_add' f g := by
    apply Subtype.ext
    exact weighted_add s f.val g.val
  map_smul' z f := by
    apply Subtype.ext
    exact weighted_smul s z f.val

instance sobolevNormedAddCommGroup (s : ℝ) : NormedAddCommGroup (Sobolev s) :=
  NormedAddCommGroup.induced _ _ (sobolevEquiv s).toAddMonoidHom (sobolevEquiv s).injective

instance sobolevNormedSpace (s : ℝ) : NormedSpace ℂ (Sobolev s) where
  norm_smul_le z f := by
    change ‖sobolevEquiv s (z • f)‖ ≤ ‖z‖ * ‖sobolevEquiv s f‖
    rw [map_smul, norm_smul]

def sobolevIsometry (s : ℝ) : Sobolev s ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  { sobolevEquiv s with norm_map' := fun _ => rfl }

instance sobolevCompleteSpace (s : ℝ) : CompleteSpace (Sobolev s) :=
  (sobolevIsometry s).toIsometryEquiv.completeSpace


/-- The norm is only used as a Sobolev norm when `InSobolev s f` is established. -/
def hNorm (s : ℝ) (f : Fourier) : ℝ :=
  Real.sqrt (∑' k : ℤ, ‖weighted s f k‖ ^ 2)

theorem hNorm_nonneg (s : ℝ) (f : Fourier) : 0 ≤ hNorm s f := Real.sqrt_nonneg _

theorem hNorm_eq_lpNorm {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    hNorm s f = ‖(⟨weighted s f, hf⟩ : lp (fun _ : ℤ => ℂ) 2)‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp [hNorm, Real.sqrt_eq_rpow]

theorem sobolev_norm {s : ℝ} (f : Sobolev s) : ‖f‖ = hNorm s f.val :=
  (hNorm_eq_lpNorm f.property).symm

theorem weight_sq (s : ℝ) (k : ℤ) : weight s k ^ 2 = (1 + (k : ℝ) ^ 2) ^ s := by
  unfold weight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + (k : ℝ) ^ 2)]
  congr 1
  norm_num

theorem norm_weighted (s : ℝ) (f : Fourier) (k : ℤ) :
    ‖weighted s f k‖ = weight s k * ‖f k‖ := by
  simp [KdV.weighted, Complex.norm_real, abs_of_pos (weight_pos s k)]

/-- The displayed square of the norm in Section 2, with normalized measure. -/
theorem hNorm_sq (s : ℝ) (f : Fourier) :
    hNorm s f ^ 2 = ∑' k : ℤ, (1 + (k : ℝ) ^ 2) ^ s * ‖f k‖ ^ 2 := by
  rw [hNorm, Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]
  congr 1
  funext k
  rw [norm_weighted, mul_pow, weight_sq]

theorem inSobolev_zero_iff (f : Fourier) : InSobolev 0 f ↔ Memℓp f 2 := by
  unfold InSobolev
  rw [weighted_zero]

/-- Reconstruction in the actual normalized torus `L²` space. -/
def reconstructL2 (f : Sobolev 0) : Lp ℂ 2 normalizedMeasure :=
  fourierBasis.repr.symm ⟨f.val, (inSobolev_zero_iff f.val).mp f.property⟩

theorem reconstructL2_coeff (f : Sobolev 0) (k : ℤ) :
    fourierCoeff (reconstructL2 f) k = f.val k := by
  have h := fourierBasis_repr (T := 2 * Real.pi) (reconstructL2 f) k
  refine h.symm.trans ?_
  change (fourierBasis.repr (fourierBasis.repr.symm
    ⟨f.val, (inSobolev_zero_iff f.val).mp f.property⟩)) k = f.val k
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem reconstructL2_norm (f : Sobolev 0) : ‖reconstructL2 f‖ = hNorm 0 f.val := by
  rw [hNorm_eq_lpNorm f.property]
  change ‖fourierBasis.repr.symm ⟨f.val, _⟩‖ = ‖(⟨weighted 0 f.val, _⟩ : lp _ 2)‖
  rw [LinearIsometryEquiv.norm_map]
  congr 1
  apply Subtype.ext
  funext k
  simp [KdV.weighted]

def normalizedL2Equiv : Sobolev 0 ≃ₗᵢ[ℂ] Lp ℂ 2 normalizedMeasure :=
  (sobolevIsometry 0).trans fourierBasis.repr.symm

theorem normalized_monomial (n : ℤ) (x : ℝ) :
    fourier n (x : Torus) = Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp

/-- The normalization and Fourier sign in the supplied paper, as an actual integral. -/
theorem normalized_fourierCoeff (f : Torus → ℂ) (k : ℤ) :
    fourierCoeff f k = (1 / (2 * Real.pi) : ℝ) •
      ∫ x : ℝ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ)) * f (x : Torus) := by
  rw [fourierCoeff_eq_intervalIntegral f k 0]
  simp only [zero_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change fourier (-k) (x : Torus) * f (x : Torus) =
    Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ)) * f (x : Torus)
  rw [normalized_monomial]
  simp

def RealValued (f : Fourier) : Prop := ∀ k, f (-k) = conj (f k)
def MeanZero (f : Fourier) : Prop := f 0 = 0

/-- Fourier multiplication is full convolution, never cyclic convolution. -/
def product (f g : Fourier) : Fourier := fun k => ∑' a : ℤ, f a * g (k - a)

def mean (f : Fourier) : ℂ := f 0
def removeMean (f : Fourier) : Fourier := fun k => if k = 0 then 0 else f k

/-- `S_t = exp(-t ∂ₓ³)`, with multiplier `exp(i t k³)`. -/
def airy (t : ℝ) (f : Fourier) : Fourier :=
  fun k => Complex.exp (Complex.I * (t : ℂ) * (k : ℂ) ^ 3) * f k

/-- `∂ₓ⁻¹`, set to zero on the zero mode. -/
def inverseDerivative (f : Fourier) : Fourier :=
  fun k => if k = 0 then 0 else (Complex.I * (k : ℂ))⁻¹ * f k

def inverseDerivative₂ (f : Fourier) : Fourier :=
  inverseDerivative (inverseDerivative f)

/-- Exactly the quadratic correction in Section 2, equation (2). -/
def quadratic (τ : ℝ) (f : Fourier) : Fourier :=
  (1 / 6 : ℂ) • removeMean (product (airy τ (inverseDerivative f))
    (airy τ (inverseDerivative f))) -
  (1 / 6 : ℂ) • airy τ (removeMean (product (inverseDerivative f) (inverseDerivative f)))

/-- The expression evaluated at the two endpoints in the third term of `H_τ`. -/
def cubicBoundary (τ s : ℝ) (f : Fourier) : Fourier :=
  let a := airy s (inverseDerivative f)
  airy (τ - s) (inverseDerivative (product (product a a) a))

/-- The expression evaluated at the two endpoints in the fourth term of `H_τ`. -/
def lastBoundary (τ s : ℝ) (f : Fourier) : Fourier :=
  airy (τ - s) (inverseDerivative₂
    (product (airy (s - τ) (inverseDerivative₂ (quadratic τ f)))
      (airy s (inverseDerivative f))))

/-- All four terms of `H_τ`, including the `1/(27τ)` correction. -/
def cubicCorrection (τ : ℝ) (f : Fourier) : Fourier :=
  (1 / 3 : ℂ) • removeMean
    (product (airy τ (inverseDerivative f)) (inverseDerivative (quadratic τ f))) +
  ((τ : ℂ) / 9 * mean (product f f)) • airy τ (inverseDerivative f) -
  (1 / 54 : ℂ) • (cubicBoundary τ τ f - cubicBoundary τ 0 f) -
  (1 / (27 * (τ : ℂ))) • (lastBoundary τ τ f - lastBoundary τ 0 f)

def step (τ : ℝ) (f : Fourier) : Fourier :=
  airy τ f + quadratic τ f + cubicCorrection τ f

/-- The fixed, unfiltered, time-semidiscrete method for every natural step index. -/
def numerical (τ : ℝ) (f : Fourier) : ℕ → Fourier
  | 0 => f
  | n + 1 => step τ (numerical τ f n)

@[simp] theorem numerical_zero (τ : ℝ) (f : Fourier) : numerical τ f 0 = f := rfl

@[simp] theorem numerical_succ (τ : ℝ) (f : Fourier) (n : ℕ) :
    numerical τ f (n + 1) = step τ (numerical τ f n) := rfl

@[simp] theorem airy_zero (f : Fourier) : airy 0 f = f := by
  ext k
  simp [airy]

@[simp] theorem airy_mean (t : ℝ) (f : Fourier) : airy t f 0 = f 0 := by simp [airy]

theorem airy_multiplier_norm (t : ℝ) (k : ℤ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * (k : ℂ) ^ 3)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im, pow_succ]

theorem norm_weighted_airy (s t : ℝ) (f : Fourier) (k : ℤ) :
    ‖weighted s (airy t f) k‖ = ‖weighted s f k‖ := by
  simp [norm_weighted, airy, airy_multiplier_norm]

theorem airy_inSobolev {s : ℝ} {f : Fourier} (hf : InSobolev s f) (t : ℝ) :
    InSobolev s (airy t f) := by
  apply Memℓp.mono' hf
  intro k
  exact le_of_eq (norm_weighted_airy s t f k)

theorem airy_hNorm (s t : ℝ) (f : Fourier) : hNorm s (airy t f) = hNorm s f := by
  simp [hNorm, norm_weighted_airy]

@[simp] theorem removeMean_zero (f : Fourier) : removeMean f 0 = 0 := by simp [removeMean]

@[simp] theorem inverseDerivative_zero (f : Fourier) : inverseDerivative f 0 = 0 := by
  simp [inverseDerivative]

@[simp] theorem inverseDerivative₂_zero (f : Fourier) : inverseDerivative₂ f 0 = 0 := by
  simp [inverseDerivative₂]

theorem quadratic_meanZero (τ : ℝ) (f : Fourier) : MeanZero (quadratic τ f) := by
  simp [MeanZero, quadratic]

theorem cubicCorrection_meanZero (τ : ℝ) (f : Fourier) : MeanZero (cubicCorrection τ f) := by
  simp [MeanZero, cubicCorrection, cubicBoundary, lastBoundary]

theorem step_meanZero (τ : ℝ) {f : Fourier} (hf : MeanZero f) : MeanZero (step τ f) := by
  change airy τ f 0 + quadratic τ f 0 + cubicCorrection τ f 0 = 0
  rw [airy_mean, quadratic_meanZero τ f, cubicCorrection_meanZero τ f, hf]
  simp

theorem numerical_meanZero (τ : ℝ) {f : Fourier} (hf : MeanZero f) (n : ℕ) :
    MeanZero (numerical τ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact step_meanZero τ ih

/-- The exact oscillatory covariance, including its normalization by `τ`. -/
def phaseAverage (τ α : ℝ) : ℂ :=
  (τ : ℂ)⁻¹ * ∫ s : ℝ in (0 : ℝ)..τ, Complex.exp (-Complex.I * (s : ℂ) * (α : ℂ))

def covariance (τ α β : ℝ) : ℂ :=
  phaseAverage τ (α + β) - phaseAverage τ α * phaseAverage τ β

theorem phaseAverage_zero {τ : ℝ} (hτ : τ ≠ 0) : phaseAverage τ 0 = 1 := by
  simp [phaseAverage, Complex.ofReal_ne_zero.mpr hτ]

@[simp] theorem covariance_zero_left {τ : ℝ} (hτ : τ ≠ 0) (β : ℝ) :
    covariance τ 0 β = 0 := by
  simp [covariance, phaseAverage_zero hτ]

@[simp] theorem covariance_zero_right {τ : ℝ} (hτ : τ ≠ 0) (α : ℝ) :
    covariance τ α 0 = 0 := by
  simp [covariance, phaseAverage_zero hτ]

theorem covariance_comm (τ α β : ℝ) : covariance τ α β = covariance τ β α := by
  simp [covariance, add_comm, mul_comm]

theorem phase_identity (a b c : ℤ) :
    3 * a * b * (a + b) + 3 * (a + b + c) * c * (a + b) =
      (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 := by ring

/-- The entire cubic averaging remainder (4), represented without a cutoff. -/
def remainder (τ t : ℝ) (f₁ f₂ f₃ : Fourier) : Fourier := fun k =>
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
          Complex.exp (-Complex.I * (t : ℂ) * (Φ : ℂ)) * covariance τ α β *
            f₁ a * f₂ b * f₃ c

theorem remainder_meanZero (τ t : ℝ) (f₁ f₂ f₃ : Fourier) :
    MeanZero (remainder τ t f₁ f₂ f₃) := by simp [MeanZero, remainder]

/-- Norm continuity of a coefficient-valued path in the specified Sobolev space. -/
def SobolevContinuousOn (s T : ℝ) (u : ℝ → Fourier) : Prop :=
  (∀ t ∈ Set.Icc 0 T, InSobolev s (u t)) ∧
    ∀ t ∈ Set.Icc 0 T, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Set.Icc 0 T,
        |r - t| < δ → hNorm s (u r - u t) < ε

/-- Fourier Duhamel equation for `u_t + u_xxx = ∂ₓ(u²)/2`.
The equivalence with the distributional PDE remains to be proved. -/
def Duhamel (T : ℝ) (u₀ : Fourier) (u : ℝ → Fourier) : Prop :=
  u 0 = u₀ ∧ ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ,
    u t k = airy t u₀ k +
      (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..t,
        Complex.exp (Complex.I * ((t - s) : ℂ) * (k : ℂ) ^ 3) *
          (Complex.I * (k : ℂ)) * product (u s) (u s) k

def KdVSolution (γ T : ℝ) (u₀ : Fourier) (u : ℝ → Fourier) : Prop :=
  SobolevContinuousOn γ T u ∧ Duhamel T u₀ u ∧
    ∀ t ∈ Set.Icc 0 T, RealValued (u t) ∧ MeanZero (u t)

def SmoothSolution (T : ℝ) (u₀ : Fourier) (u : ℝ → Fourier) : Prop :=
  Duhamel T u₀ u ∧ (∀ s : ℝ, SobolevContinuousOn s T u) ∧
    (∀ k : ℤ, ∀ m : ℕ, ContDiffOn ℝ m (fun t => u t k) (Set.Icc 0 T)) ∧
    ∀ t ∈ Set.Icc 0 T, RealValued (u t) ∧ MeanZero (u t)

/-- Smooth approximation in the initial Sobolev norm and uniformly in solution `L²`.
This is part of the solution concept, not an assumed error estimate for the method. -/
def ObtainedBySmoothApproximation (γ T : ℝ) (u₀ : Fourier) (u : ℝ → Fourier) : Prop :=
  ∃ data : ℕ → Fourier, ∃ solutions : ℕ → ℝ → Fourier,
    (∀ m, SmoothSolution T (data m) (solutions m)) ∧
    Filter.Tendsto (fun m => hNorm γ (data m - u₀)) Filter.atTop (nhds 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∀ t ∈ Set.Icc 0 T, hNorm 0 (solutions m t - u t) < ε

def ExactSolution (γ T : ℝ) (u₀ : Fourier) (u : ℝ → Fourier) : Prop :=
  KdVSolution γ T u₀ u ∧ ObtainedBySmoothApproximation γ T u₀ u

/-- A literal maximum over all `L+1` grid points, including both endpoints. -/
def maximumError (T : ℝ) (L : ℕ) (u₀ : Fourier) (u : ℝ → Fourier) : ℝ :=
  (Finset.range (L + 1)).sup' (by simp) fun n =>
    hNorm 0 (u ((n : ℝ) * (T / (L : ℝ))) - numerical (T / (L : ℝ)) u₀ n)

/-- The target quantifiers. This definition asserts no theorem or premise. -/
def TheoremOne : Prop :=
  ∀ T : ℝ, 0 < T → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ R : ℝ, 0 < R →
    ∃ C : ℝ, 0 < C ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ u₀ : Fourier, InSobolev γ u₀ → RealValued u₀ → MeanZero u₀ → hNorm γ u₀ ≤ R →
        ∀ u : ℝ → Fourier, ExactSolution γ T u₀ u →
          ∀ L : ℕ, 0 < L → T / (L : ℝ) ≤ τ₀ →
            maximumError T L u₀ u ≤ C * (T / (L : ℝ)) ^ γ

@[simp] theorem hNorm_zero (s : ℝ) : hNorm s 0 = 0 := by
  simp [hNorm, weighted]

theorem hNorm_add_le {s : ℝ} {f g : Fourier} (hf : InSobolev s f)
    (hg : InSobolev s g) : hNorm s (f + g) ≤ hNorm s f + hNorm s g := by
  rw [hNorm_eq_lpNorm (hf.add hg), hNorm_eq_lpNorm hf, hNorm_eq_lpNorm hg]
  let f' : lp (fun _ : ℤ => ℂ) 2 := ⟨weighted s f, hf⟩
  let g' : lp (fun _ : ℤ => ℂ) 2 := ⟨weighted s g, hg⟩
  have h : (⟨weighted s (f + g), hf.add hg⟩ : lp (fun _ : ℤ => ℂ) 2) = f' + g' := by
    apply Subtype.ext
    exact weighted_add s f g
  rw [h]
  exact norm_add_le f' g'

theorem hNorm_smul {s : ℝ} {f : Fourier} (hf : InSobolev s f) (z : ℂ) :
    hNorm s (z • f) = ‖z‖ * hNorm s f := by
  rw [hNorm_eq_lpNorm (hf.smul z), hNorm_eq_lpNorm hf]
  let f' : lp (fun _ : ℤ => ℂ) 2 := ⟨weighted s f, hf⟩
  have h : (⟨weighted s (z • f), hf.smul z⟩ : lp (fun _ : ℤ => ℂ) 2) = z • f' := by
    apply Subtype.ext
    exact weighted_smul s z f
  rw [h, norm_smul]

theorem weight_mono {s r : ℝ} (h : s ≤ r) (k : ℤ) : weight s k ≤ weight r k := by
  apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (k : ℝ)])
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem InSobolev.of_le {s r : ℝ} {f : Fourier} (hf : InSobolev r f) (h : s ≤ r) :
    InSobolev s f := by
  apply Memℓp.mono' hf
  intro k
  rw [norm_weighted, norm_weighted]
  exact mul_le_mul_of_nonneg_right (weight_mono h k) (norm_nonneg _)

theorem hNorm_mono {s r : ℝ} {f : Fourier} (hf : InSobolev r f) (h : s ≤ r) :
    hNorm s f ≤ hNorm r f := by
  rw [hNorm_eq_lpNorm (hf.of_le h), hNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖weighted s f k‖ ≤ ‖weighted r f k‖
  rw [norm_weighted, norm_weighted]
  exact mul_le_mul_of_nonneg_right (weight_mono h k) (norm_nonneg _)

theorem InSobolev.of_weighted_bound {s r C : ℝ} {f g : Fourier}
    (hg : InSobolev r g) (hC : 0 ≤ C)
    (h : ∀ k, ‖weighted s f k‖ ≤ C * ‖weighted r g k‖) : InSobolev s f := by
  apply Memℓp.mono' (hg.const_smul (C : ℂ))
  intro k
  simpa only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC] using h k

theorem hNorm_le_of_weighted_bound {s r C : ℝ} {f g : Fourier}
    (hg : InSobolev r g) (hC : 0 ≤ C)
    (h : ∀ k, ‖weighted s f k‖ ≤ C * ‖weighted r g k‖) :
    hNorm s f ≤ C * hNorm r g := by
  let hf := InSobolev.of_weighted_bound hg hC h
  rw [hNorm_eq_lpNorm hf, hNorm_eq_lpNorm hg]
  let g' : lp (fun _ : ℤ => ℂ) 2 := ⟨weighted r g, hg⟩
  calc
    ‖(⟨weighted s f, hf⟩ : lp (fun _ : ℤ => ℂ) 2)‖ ≤ ‖(C : ℂ) • g'‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro k
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul,
        Complex.norm_real, Real.norm_of_nonneg hC] using h k
    _ = C * ‖(⟨weighted r g, hg⟩ : lp (fun _ : ℤ => ℂ) 2)‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
      rfl

theorem inverseDerivative_weighted_bound (f : Fourier) (k : ℤ) :
    ‖weighted 1 (inverseDerivative f) k‖ ≤ Real.sqrt 2 * ‖weighted 0 f k‖ := by
  rw [weighted_zero]
  by_cases hk : k = 0
  · subst k
    simp [KdV.weighted]
  have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hkone : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hweight : weight 1 k ≤ Real.sqrt 2 * |(k : ℝ)| := by
    have hw := weight_sq 1 k
    simp only [Real.rpow_one] at hw
    have ha : |(k : ℝ)| ^ 2 = (k : ℝ) ^ 2 := sq_abs _
    apply (sq_le_sq₀ (weight_pos 1 k).le
      (mul_nonneg (Real.sqrt_nonneg 2) (abs_nonneg _))).mp
    rw [hw, mul_pow, hsqrt, ha]
    nlinarith [sq_nonneg (|(k : ℝ)| - 1)]
  rw [norm_weighted]
  simp only [inverseDerivative, if_neg hk, norm_mul, norm_inv, Complex.norm_I,
    one_mul, Complex.norm_intCast]
  calc
    weight 1 k * (|(k : ℝ)|⁻¹ * ‖f k‖) = (weight 1 k / |(k : ℝ)|) * ‖f k‖ := by ring
    _ ≤ Real.sqrt 2 * ‖f k‖ :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ hkpos).mpr hweight) (norm_nonneg _)

theorem inverseDerivative_inSobolev_one {f : Fourier} (hf : InSobolev 0 f) :
    InSobolev 1 (inverseDerivative f) :=
  InSobolev.of_weighted_bound hf (Real.sqrt_nonneg 2) (inverseDerivative_weighted_bound f)

theorem inverseDerivative_hNorm_one {f : Fourier} (hf : InSobolev 0 f) :
    hNorm 1 (inverseDerivative f) ≤ Real.sqrt 2 * hNorm 0 f :=
  hNorm_le_of_weighted_bound hf (Real.sqrt_nonneg 2) (inverseDerivative_weighted_bound f)

/-- Translated reflection is the index change in a convolution coefficient. -/
def reflectAt (k : ℤ) : ℤ ≃ ℤ where
  toFun a := k - a
  invFun a := k - a
  left_inv a := by dsimp; omega
  right_inv a := by dsimp; omega

theorem reflect_inSobolev_zero {g : Fourier} (hg : InSobolev 0 g) (k : ℤ) :
    InSobolev 0 (fun a => g (k - a)) := by
  rw [inSobolev_zero_iff] at hg ⊢
  apply memℓp_gen
  have h := hg.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  exact (reflectAt k).summable_iff.mpr h

theorem reflect_hNorm_zero (g : Fourier) (k : ℤ) :
    hNorm 0 (fun a => g (k - a)) = hNorm 0 g := by
  simp only [hNorm, weighted_zero]
  congr 1
  exact (reflectAt k).tsum_eq (fun a => ‖g a‖ ^ 2)

theorem product_summable {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (k : ℤ) : Summable (fun a : ℤ => f a * g (k - a)) := by
  let f' : lp (fun _ : ℤ => ℂ) 2 := ⟨f, (inSobolev_zero_iff f).mp hf⟩
  let g' : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨fun a => g (k - a), (inSobolev_zero_iff _).mp (reflect_inSobolev_zero hg k)⟩
  apply Summable.of_norm
  simp only [norm_mul]
  exact lp.summable_mul (p := 2) (q := 2)
    (by norm_num; exact Real.HolderConjugate.two_two) f' g'

theorem product_coeff_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (k : ℤ) : ‖product f g k‖ ≤ hNorm 0 f * hNorm 0 g := by
  let f' : lp (fun _ : ℤ => ℂ) 2 := ⟨f, (inSobolev_zero_iff f).mp hf⟩
  let g' : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨fun a => g (k - a), (inSobolev_zero_iff _).mp (reflect_inSobolev_zero hg k)⟩
  have hfg := lp.tsum_mul_le_mul_norm (p := 2) (q := 2)
    (by norm_num; exact Real.HolderConjugate.two_two) f' g'
  calc
    ‖product f g k‖ ≤ ∑' a : ℤ, ‖f a‖ * ‖g (k - a)‖ := by
      have hnorm : Summable (fun a : ℤ => ‖f a * g (k - a)‖) := by
        simpa only [norm_mul] using hfg.1
      simpa only [product, norm_mul] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ‖f'‖ * ‖g'‖ := hfg.2
    _ = hNorm 0 f * hNorm 0 g := by
      have hf' : ‖f'‖ = hNorm 0 f := by simpa [f'] using (hNorm_eq_lpNorm hf).symm
      have hg' : ‖g'‖ = hNorm 0 (fun a => g (k - a)) := by
        simpa [g'] using (hNorm_eq_lpNorm (reflect_inSobolev_zero hg k)).symm
      rw [hf', hg', reflect_hNorm_zero]

/-- The third largest of four numbers, written without choosing a tie ordering. -/
def thirdLargest (A B C D : ℝ) : ℝ :=
  max (min A (min B C))
    (max (min A (min B D)) (max (min A (min C D)) (min B (min C D))))

theorem thirdLargest_of_ordered {A B C D : ℝ} (hAB : B ≤ A)
    (hBC : C ≤ B) (hCD : D ≤ C) : thirdLargest A B C D = C := by
  simp [thirdLargest, min_eq_right hBC, min_eq_right (hBC.trans hAB),
    min_eq_right hCD, min_eq_right (hCD.trans hBC),
    min_eq_right (hCD.trans (hBC.trans hAB)), max_eq_left hCD]

theorem thirdLargest_pos {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    0 < thirdLargest A B C D := by
  exact lt_of_lt_of_le (lt_min hA (lt_min hB hC)) (le_max_left _ _)

theorem ratio_min_le_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    min (x / y) (y / x) ≤ 1 := by
  rcases le_total x y with h | h
  · exact (min_le_left _ _).trans ((div_le_one hy).mpr h)
  · exact (min_le_right _ _).trans ((div_le_one hx).mpr h)

/-- Scalar form of Lemma 3 (7). Only the needed triangle inequality is used. -/
theorem scalar_first_majorant {A B C D : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (htriangle : C ≤ A + B + D) :
    1 / D * min (A * B / (C * D)) (C * D / (A * B)) ≤
      3 / thirdLargest A B C D := by
  let n := min A (min B C)
  let m := max (min A (min B D)) (max (min A (min C D)) (min B (min C D)))
  have hm : m ≤ D := by
    exact max_le
      ((min_le_right _ _).trans (min_le_right _ _))
      (max_le ((min_le_right _ _).trans (min_le_right _ _))
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hnA : n ≤ A := min_le_left _ _
  have hnB : n ≤ B := (min_le_right _ _).trans (min_le_left _ _)
  have hnC : n ≤ C := (min_le_right _ _).trans (min_le_right _ _)
  have hn : 0 < n := lt_min hA (lt_min hB hC)
  have hN := thirdLargest_pos (D := D) hA hB hC
  have hmin := ratio_min_le_one (mul_pos hA hB) (mul_pos hC hD)
  suffices h : thirdLargest A B C D *
      min (A * B / (C * D)) (C * D / (A * B)) ≤ 3 * D by
    apply (le_div_iff₀ hN).mpr
    calc
      (1 / D * min (A * B / (C * D)) (C * D / (A * B))) * thirdLargest A B C D =
          (thirdLargest A B C D * min (A * B / (C * D)) (C * D / (A * B))) / D := by ring
      _ ≤ 3 := (div_le_iff₀ hD).mpr (by linarith)
  by_cases hsmall : n ≤ D
  · have hND : thirdLargest A B C D ≤ D := max_le hsmall hm
    calc
      thirdLargest A B C D * min (A * B / (C * D)) (C * D / (A * B)) ≤
          thirdLargest A B C D * 1 := mul_le_mul_of_nonneg_left hmin hN.le
      _ ≤ 3 * D := by nlinarith
  · have hDn : D ≤ n := (lt_of_not_ge hsmall).le
    have hNeq : thirdLargest A B C D = n := max_eq_left (hm.trans hDn)
    rw [hNeq]
    have hprod : n * C ≤ 3 * (A * B) := by
      have h₁ : n * A ≤ A * B := by nlinarith
      have h₂ : n * B ≤ A * B := mul_le_mul_of_nonneg_right hnA hB.le
      have h₃ : n * D ≤ A * B :=
        mul_le_mul hnA (hDn.trans hnB) hD.le hA.le
      have h₄ := mul_le_mul_of_nonneg_left htriangle hn.le
      nlinarith
    calc
      n * min (A * B / (C * D)) (C * D / (A * B)) ≤ n * (C * D / (A * B)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hn.le
      _ ≤ 3 * D := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (mul_pos hA hB)).mpr
        convert mul_le_mul_of_nonneg_right hprod hD.le using 1 <;> ring

/-- A stronger scalar version of Lemma 3 (8), with constant two. -/
theorem scalar_second_majorant {A B C D p : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hp : 0 ≤ p) (hpAB : p ≤ A + B) (hpCD : p ≤ C + D) :
    p / max (A * B) (C * D) ≤ 2 / thirdLargest A B C D := by
  have hN := thirdLargest_pos (D := D) hA hB hC
  have hmax : 0 < max (A * B) (C * D) := lt_max_of_lt_left (mul_pos hA hB)
  have hpair : ∀ x y n : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ n → n ≤ x → n ≤ y →
      ∀ q : ℝ, q ≤ x + y → n * q ≤ 2 * (x * y) := by
    intro x y n hx hy hn hnx hny q hq
    have h₁ := mul_le_mul_of_nonneg_right hnx hy
    have h₂ := mul_le_mul_of_nonneg_right hny hx
    have h₃ := mul_le_mul_of_nonneg_left hq hn
    nlinarith
  have h₁ : min A (min B C) * p ≤ 2 * max (A * B) (C * D) := by
    apply (hpair A B _ hA.le hB.le (le_min hA.le (le_min hB.le hC.le))
      (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _)) p hpAB).trans
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have h₂ : min A (min B D) * p ≤ 2 * max (A * B) (C * D) := by
    apply (hpair A B _ hA.le hB.le (le_min hA.le (le_min hB.le hD.le))
      (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _)) p hpAB).trans
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have h₃ : min A (min C D) * p ≤ 2 * max (A * B) (C * D) := by
    apply (hpair C D _ hC.le hD.le (le_min hA.le (le_min hC.le hD.le))
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) p hpCD).trans
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  have h₄ : min B (min C D) * p ≤ 2 * max (A * B) (C * D) := by
    apply (hpair C D _ hC.le hD.le (le_min hB.le (le_min hC.le hD.le))
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) p hpCD).trans
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  have hprod : thirdLargest A B C D * p ≤ 2 * max (A * B) (C * D) := by
    simpa only [thirdLargest, max_mul_of_nonneg _ _ hp] using
      max_le h₁ (max_le h₂ (max_le h₃ h₄))
  apply (div_le_div_iff₀ hmax hN).mpr
  nlinarith

def N₃ (a b c d : ℤ) : ℝ :=
  thirdLargest |(a : ℝ)| |(b : ℝ)| |(c : ℝ)| |(d : ℝ)|

theorem abs_cast_pos {k : ℤ} (hk : k ≠ 0) : 0 < |(k : ℝ)| :=
  abs_pos.mpr (by exact_mod_cast hk)

theorem zero_sum_triangle {a b c d : ℤ} (hsum : a + b + c + d = 0) :
    |(c : ℝ)| ≤ |(a : ℝ)| + |(b : ℝ)| + |(d : ℝ)| := by
  have hc : c = -(a + b + d) := by omega
  rw [hc]
  simp only [Int.cast_neg, Int.cast_add, abs_neg]
  calc
    |(a : ℝ) + (b : ℝ) + (d : ℝ)| ≤ |(a : ℝ) + (b : ℝ)| + |(d : ℝ)| := abs_add_le _ _
    _ ≤ |(a : ℝ)| + |(b : ℝ)| + |(d : ℝ)| := by
      linarith [abs_add_le (a : ℝ) (b : ℝ)]

/-- The paper's first pointwise majorant, with all four frequencies included. -/
theorem four_frequency_first_majorant {a b c d : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hsum : a + b + c + d = 0) :
    1 / |(d : ℝ)| * min (|(a : ℝ) * (b : ℝ)| / |(c : ℝ) * (d : ℝ)|)
      (|(c : ℝ) * (d : ℝ)| / |(a : ℝ) * (b : ℝ)|) ≤ 3 / N₃ a b c d := by
  simpa only [abs_mul, N₃] using scalar_first_majorant
    (abs_cast_pos ha) (abs_cast_pos hb) (abs_cast_pos hc) (abs_cast_pos hd)
    (zero_sum_triangle hsum)

/-- The paper's second majorant; the proof gives the stronger numerator constant 2. -/
theorem four_frequency_second_majorant {a b c d : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hsum : a + b + c + d = 0) :
    |(a : ℝ) + (b : ℝ)| / max (|(a : ℝ) * (b : ℝ)|) (|(c : ℝ) * (d : ℝ)|) ≤
      6 / N₃ a b c d := by
  have hpCD : |(a : ℝ) + (b : ℝ)| ≤ |(c : ℝ)| + |(d : ℝ)| := by
    have hp : a + b = -(c + d) := by omega
    have hp' : (a : ℝ) + (b : ℝ) = -((c : ℝ) + (d : ℝ)) := by exact_mod_cast hp
    rw [hp', abs_neg]
    exact abs_add_le _ _
  have h₂ := scalar_second_majorant
    (abs_cast_pos ha) (abs_cast_pos hb) (abs_cast_pos hc) (abs_cast_pos hd)
    (abs_nonneg ((a : ℝ) + (b : ℝ))) (abs_add_le (a : ℝ) (b : ℝ)) hpCD
  have hN : 0 < N₃ a b c d := thirdLargest_pos
    (abs_cast_pos ha) (abs_cast_pos hb) (abs_cast_pos hc)
  have h₂' : |(a : ℝ) + (b : ℝ)| /
      max (|(a : ℝ) * (b : ℝ)|) (|(c : ℝ) * (d : ℝ)|) ≤ 2 / N₃ a b c d := by
    simpa only [abs_mul, N₃] using h₂
  apply h₂'.trans
  exact div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 6) hN.le

/-- Elementary interpolation used between the two covariance endpoints. -/
theorem interpolate_bounds {x A B γ : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hxA : x ≤ A) (hxB : x ≤ B) :
    x ≤ A ^ (1 - γ) * B ^ γ := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0]
    positivity
  calc
    x = x ^ (1 - γ) * x ^ γ := by
      rw [← Real.rpow_add hxpos]
      simp
    _ ≤ A ^ (1 - γ) * B ^ γ := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow hx hxA (by linarith)
      · exact Real.rpow_le_rpow hx hxB hγ
      · positivity
      · positivity

/-- Symmetric projections used only for smooth approximation in the proof.
They do not occur in `step` or in `numerical`. -/
def cutoff (m : ℕ) (f : Fourier) : Fourier :=
  fun k => if k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) then f k else 0

theorem cutoff_norm_weighted_le (s : ℝ) (m : ℕ) (f : Fourier) (k : ℤ) :
    ‖weighted s (cutoff m f) k‖ ≤ ‖weighted s f k‖ := by
  by_cases h : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp only [KdV.weighted, cutoff, if_pos h, le_refl]
  · simp only [KdV.weighted, cutoff, if_neg h, mul_zero, norm_zero]
    positivity

theorem cutoff_inSobolev {s : ℝ} {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    InSobolev s (cutoff m f) := Memℓp.mono' hf (cutoff_norm_weighted_le s m f)

theorem cutoff_hNorm_le {s : ℝ} {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    hNorm s (cutoff m f) ≤ hNorm s f := by
  rw [hNorm_eq_lpNorm (cutoff_inSobolev hf m), hNorm_eq_lpNorm hf]
  exact lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (cutoff_norm_weighted_le s m f)

theorem cutoff_meanZero {f : Fourier} (hf : MeanZero f) (m : ℕ) : MeanZero (cutoff m f) := by
  change f 0 = 0 at hf
  simpa [MeanZero, cutoff] using hf

theorem cutoff_real {f : Fourier} (hf : RealValued f) (m : ℕ) : RealValued (cutoff m f) := by
  intro k
  have hk : (-k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)) ↔
      (k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)) := by
    simp only [Finset.mem_Icc]
    omega
  simp only [cutoff, hk]
  split_ifs <;> simp [hf k]

theorem cutoff_finiteSupport (m : ℕ) (f : Fourier) : (Function.support (cutoff m f)).Finite := by
  apply (Finset.Icc (-(m : ℤ)) (m : ℤ)).finite_toSet.subset
  intro k hk
  by_contra h
  change k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) at h
  exact hk (by simp only [cutoff, if_neg h])

theorem cutoff_inSobolev_all (s : ℝ) (m : ℕ) (f : Fourier) : InSobolev s (cutoff m f) := by
  apply Memℓp.of_exponent_ge (p := 2) (q := 0) _ (by simp)
  apply memℓp_zero
  apply (cutoff_finiteSupport m f).subset
  intro k hk hzero
  apply hk
  simp only [KdV.weighted, hzero, mul_zero]

theorem cutoff_tail_weighted (s : ℝ) (m : ℕ) (f : Fourier) (k : ℤ) :
    ‖weighted s (cutoff m f - f) k‖ ^ 2 ≤ ‖weighted s f k‖ ^ 2 := by
  by_cases h : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp [KdV.weighted, cutoff, h]
    positivity
  · simp [KdV.weighted, cutoff, h]

theorem cutoff_converges {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    Filter.Tendsto (fun m : ℕ => hNorm s (cutoff m f - f)) Filter.atTop (nhds 0) := by
  have hs : Summable (fun k : ℤ => ‖weighted s f k‖ ^ 2) := by
    simpa using hf.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hpoint : ∀ k : ℤ,
      Filter.Tendsto (fun m : ℕ => ‖weighted s (cutoff m f - f) k‖ ^ 2)
        Filter.atTop (nhds (0 : ℝ)) := by
    intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop k.natAbs] with m hm
    have hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
      simp only [Finset.mem_Icc]
      have h₁ : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
      have h₂ : -k ≤ (k.natAbs : ℤ) := by
        simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -k))
      omega
    simp [KdV.weighted, cutoff, hk]
  have hsum := tendsto_tsum_of_dominated_convergence hs hpoint
    (Filter.Eventually.of_forall fun m k => by
      change ‖(‖weighted s (cutoff m f - f) k‖ ^ 2 : ℝ)‖ ≤ ‖weighted s f k‖ ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact cutoff_tail_weighted s m f k)
  simpa only [hNorm, tsum_zero, Real.sqrt_zero] using hsum.sqrt

theorem finiteSupport_inSobolev (s : ℝ) {f : Fourier} (hf : (Function.support f).Finite) :
    InSobolev s f := by
  apply Memℓp.of_exponent_ge (p := 2) (q := 0) _ (by simp)
  apply memℓp_zero
  apply hf.subset
  intro k hk hzero
  apply hk
  simp only [KdV.weighted, hzero, mul_zero]

/-- The isometric completion model contains every trigonometric polynomial. -/
def polynomialToSobolev (s : ℝ) (p : ℤ →₀ ℂ) : Sobolev s :=
  ⟨p, finiteSupport_inSobolev s p.hasFiniteSupport⟩

def approximation {s : ℝ} (f : Sobolev s) (m : ℕ) : Sobolev s :=
  ⟨cutoff m f.val, cutoff_inSobolev f.property m⟩

theorem approximation_converges {s : ℝ} (f : Sobolev s) :
    Filter.Tendsto (approximation f) Filter.atTop (nhds f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : (fun m => ‖approximation f m - f‖) =
      (fun m => hNorm s (cutoff m f.val - f.val)) := by
    funext m
    exact sobolev_norm (approximation f m - f)
  rw [h]
  exact cutoff_converges f.property

/-- Density and completeness identify this space with the completion prescribed
in Section 2, rather than a space with a finite Fourier cutoff. -/
theorem polynomialToSobolev_denseRange (s : ℝ) : DenseRange (polynomialToSobolev s) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨m, hm⟩ := (Metric.tendsto_nhds.mp (approximation_converges f) ε hε).exists
  refine ⟨Finsupp.ofSupportFinite (cutoff m f.val) (cutoff_finiteSupport m f.val), ?_⟩
  have hpoly : polynomialToSobolev s
      (Finsupp.ofSupportFinite (cutoff m f.val) (cutoff_finiteSupport m f.val)) =
      approximation f m := by
    apply Subtype.ext
    rfl
  rw [hpoly, dist_comm]
  exact hm

/-- A finite weighted Cauchy--Schwarz summation lemma. This is an internal
tool for summing the four-frequency majorant; it is not an external premise. -/
theorem finite_weighted_schur_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℝ) (w : ι → ℝ) (v : κ → ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hK : ∀ i j, 0 ≤ K i j)
    (hw : ∀ i, 0 < w i) (hv : ∀ j, 0 < v j)
    (hrow : ∀ i, ∑ j, K i j * v j ≤ C * w i)
    (hcol : ∀ j, ∑ i, K i j * w i ≤ C * v j) :
    (∑ i, ∑ j, K i j * x i * y j) ^ 2 ≤
      C ^ 2 * (∑ i, x i ^ 2) * (∑ j, y j ^ 2) := by
  let U : ℝ := ∑ p : ι × κ, K p.1 p.2 * v p.2 / w p.1 * x p.1 ^ 2
  let V : ℝ := ∑ p : ι × κ, K p.1 p.2 * w p.1 / v p.2 * y p.2 ^ 2
  have hU : U ≤ C * ∑ i, x i ^ 2 := by
    calc
      U = ∑ i, (x i ^ 2 / w i) * (∑ j, K i j * v j) := by
        dsimp only [U]
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ i, (x i ^ 2 / w i) * (C * w i) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hrow i) (div_nonneg (sq_nonneg _) (hw i).le)
      _ = C * ∑ i, x i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(hw i).ne']
  have hV : V ≤ C * ∑ j, y j ^ 2 := by
    calc
      V = ∑ j, (y j ^ 2 / v j) * (∑ i, K i j * w i) := by
        dsimp only [V]
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ j, (y j ^ 2 / v j) * (C * v j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hcol j) (div_nonneg (sq_nonneg _) (hv j).le)
      _ = C * ∑ j, y j ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp [(hv j).ne']
  have hCS : (∑ p : ι × κ, K p.1 p.2 * x p.1 * y p.2) ^ 2 ≤ U * V := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro p _
      exact mul_nonneg (div_nonneg (mul_nonneg (hK _ _) (hv _).le) (hw _).le) (sq_nonneg _)
    · intro p _
      exact mul_nonneg (div_nonneg (mul_nonneg (hK _ _) (hw _).le) (hv _).le) (sq_nonneg _)
    · intro p _
      apply le_of_eq
      field_simp [(hw p.1).ne', (hv p.2).ne']
  have hVnonneg : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro p _
    exact mul_nonneg (div_nonneg (mul_nonneg (hK _ _) (hw _).le) (hv _).le) (sq_nonneg _)
  rw [Fintype.sum_prod_type] at hCS
  calc
    _ ≤ U * V := hCS
    _ ≤ (C * ∑ i, x i ^ 2) * (C * ∑ j, y j ^ 2) :=
      mul_le_mul hU hV hVnonneg (mul_nonneg hC (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = _ := by ring

/-- The lower-frequency half of the summable kernel estimate. -/
theorem sum_inverse_sqrt_le (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), ((i + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      2 * ((N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Set.Icc 1 (1 + (N : ℝ))) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : -(1 / 2 : ℝ) ≤ 0)).mono
    intro t ht
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht.1
  have h := hanti.sum_le_integral
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))] at h
  norm_num at h
  rw [Finset.sum_range_succ']
  norm_num
  simp_rw [add_comm (1 : ℝ), add_assoc] at h
  simp only [add_assoc]
  linarith

/-- The upper-frequency half of the same kernel estimate. -/
theorem sum_inverse_three_halves_tail_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ i ∈ Finset.Ico m N, ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      2 * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Set.Icc (m : ℝ) (N : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : -(3 / 2 : ℝ) ≤ 0)).mono
    intro t ht
    exact lt_of_lt_of_le (by exact_mod_cast hm) ht.1
  have h := hanti.sum_le_integral_Ico hmN
  have hnot : (0 : ℝ) ∉ Set.uIcc (m : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hmN)]
    intro ht
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    linarith [ht.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hnot⟩)] at h
  norm_num at h
  have hp : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

/-- A positive-frequency kernel for the four-linear summation. -/
def hardyKernel (m n : ℕ) : ℝ := (((max (m + 1) (n + 1) : ℕ) : ℝ))⁻¹

def hardyWeight (m : ℕ) : ℝ := ((m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

theorem hardyWeight_pos (m : ℕ) : 0 < hardyWeight m := by unfold hardyWeight; positivity

theorem hardyKernel_nonneg (m n : ℕ) : 0 ≤ hardyKernel m n := by unfold hardyKernel; positivity

theorem hardyKernel_comm (m n : ℕ) : hardyKernel m n = hardyKernel n m := by
  simp [hardyKernel, max_comm]

theorem hardy_row_bound_aux (m N : ℕ) (hmN : m + 1 ≤ N) :
    ∑ n ∈ Finset.range N, hardyKernel m n * hardyWeight n ≤ 4 * hardyWeight m := by
  have hmpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hnear : ∑ n ∈ Finset.range (m + 1), hardyKernel m n * hardyWeight n ≤
      2 * hardyWeight m := by
    calc
      _ = (((m + 1 : ℕ) : ℝ))⁻¹ *
          ∑ n ∈ Finset.range (m + 1), ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have hnm : n + 1 ≤ m + 1 := by simp only [Finset.mem_range] at hn; omega
        simp only [hardyKernel, max_eq_left hnm, hardyWeight]
      _ ≤ (((m + 1 : ℕ) : ℝ))⁻¹ * (2 * ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inverse_sqrt_le m) (by positivity)
      _ = 2 * hardyWeight m := by
        rw [show (((m + 1 : ℕ) : ℝ))⁻¹ * (2 * ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) =
            2 * (((m + 1 : ℕ) : ℝ) ^ (-1 : ℝ) * ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) by
          rw [Real.rpow_neg_one]; ring]
        rw [← Real.rpow_add hmpos]
        norm_num [hardyWeight]
  have hfar : ∑ n ∈ Finset.Ico (m + 1) N, hardyKernel m n * hardyWeight n ≤
      2 * hardyWeight m := by
    have heq : ∑ n ∈ Finset.Ico (m + 1) N, hardyKernel m n * hardyWeight n =
        ∑ n ∈ Finset.Ico (m + 1) N, ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hmn : m + 1 ≤ n + 1 := by simp only [Finset.mem_Ico] at hn; omega
      simp only [hardyKernel, max_eq_right hmn, hardyWeight]
      rw [← Real.rpow_neg_one, ← Real.rpow_add (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
      norm_num
    rw [heq]
    exact sum_inverse_three_halves_tail_le (by omega) hmN
  rw [← Finset.sum_range_add_sum_Ico _ hmN]
  linarith

theorem hardy_row_bound (m N : ℕ) :
    ∑ n ∈ Finset.range N, hardyKernel m n * hardyWeight n ≤ 4 * hardyWeight m := by
  calc
    _ ≤ ∑ n ∈ Finset.range (max (m + 1) N), hardyKernel m n * hardyWeight n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (le_max_right _ _)
      · intro n _ _
        exact mul_nonneg (hardyKernel_nonneg _ _) (hardyWeight_pos _).le
    _ ≤ _ := hardy_row_bound_aux _ _ (le_max_left _ _)

/-- Both signs of each nonzero frequency are retained. -/
abbrev SignedModes (N : ℕ) := Bool × Fin N

theorem signed_hardy_row_bound (N : ℕ) (i : SignedModes N) :
    ∑ j : SignedModes N, hardyKernel i.2.val j.2.val * hardyWeight j.2.val ≤
      8 * hardyWeight i.2.val := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.sum_univ_eq_sum_range (fun n => hardyKernel i.2.val n * hardyWeight n) N]
  have h := hardy_row_bound i.2.val N
  linarith

theorem signed_hardy_bound_sq (N : ℕ) (x y : SignedModes N → ℝ) :
    (∑ i : SignedModes N, ∑ j : SignedModes N,
      hardyKernel i.2.val j.2.val * x i * y j) ^ 2 ≤
      64 * (∑ i : SignedModes N, x i ^ 2) * (∑ j : SignedModes N, y j ^ 2) := by
  have h := finite_weighted_schur_sq
    (fun i j : SignedModes N => hardyKernel i.2.val j.2.val)
    (fun i : SignedModes N => hardyWeight i.2.val)
    (fun j : SignedModes N => hardyWeight j.2.val)
    x y 8 (by norm_num)
    (fun i j => hardyKernel_nonneg _ _)
    (fun i => hardyWeight_pos _) (fun j => hardyWeight_pos _)
    (signed_hardy_row_bound N)
    (fun j => by simpa only [hardyKernel_comm] using signed_hardy_row_bound N j)
  norm_num at h
  exact h

theorem signed_hardy_bound (N : ℕ) (x y : SignedModes N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    ∑ i : SignedModes N, ∑ j : SignedModes N,
      hardyKernel i.2.val j.2.val * x i * y j ≤
      8 * Real.sqrt (∑ i : SignedModes N, x i ^ 2) *
        Real.sqrt (∑ j : SignedModes N, y j ^ 2) := by
  have h := signed_hardy_bound_sq N x y
  have hleft : 0 ≤ ∑ i : SignedModes N, ∑ j : SignedModes N,
      hardyKernel i.2.val j.2.val * x i * y j := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (hardyKernel_nonneg _ _) (hx i)) (hy j)
  apply (sq_le_sq₀ hleft (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  norm_num
  exact h

/-- The reciprocal of the third largest magnitude is bounded by the six choices
of a smaller pair. This permits direct summation of the four-linear majorant. -/
theorem reciprocal_thirdLargest_le_pairs {A B C D : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (_hD : 0 < D) :
    1 / thirdLargest A B C D ≤
      1 / max A B + 1 / max A C + 1 / max A D +
      1 / max B C + 1 / max B D + 1 / max C D := by
  let n := thirdLargest A B C D
  have hABC : A ≤ n ∨ B ≤ n ∨ C ≤ n := by
    have h : min A (min B C) ≤ n := le_max_left _ _
    simpa only [min_le_iff] using h
  have hABD : A ≤ n ∨ B ≤ n ∨ D ≤ n := by
    have h : min A (min B D) ≤ n := (le_max_left _ _).trans (le_max_right _ _)
    simpa only [min_le_iff] using h
  have hACD : A ≤ n ∨ C ≤ n ∨ D ≤ n := by
    have h : min A (min C D) ≤ n :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    simpa only [min_le_iff] using h
  have hBCD : B ≤ n ∨ C ≤ n ∨ D ≤ n := by
    have h : min B (min C D) ≤ n :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    simpa only [min_le_iff] using h
  have hpairs : max A B ≤ n ∨ max A C ≤ n ∨ max A D ≤ n ∨
      max B C ≤ n ∨ max B D ≤ n ∨ max C D ≤ n := by
    simp only [max_le_iff]
    tauto
  have hab : 0 ≤ 1 / max A B := by positivity
  have hac : 0 ≤ 1 / max A C := by positivity
  have had : 0 ≤ 1 / max A D := by positivity
  have hbc : 0 ≤ 1 / max B C := by positivity
  have hbd : 0 ≤ 1 / max B D := by positivity
  have hcd : 0 ≤ 1 / max C D := by positivity
  rcases hpairs with h | h | h | h | h | h
  · have h' := one_div_le_one_div_of_le (lt_max_of_lt_left hA) h
    linarith
  · have h' := one_div_le_one_div_of_le (lt_max_of_lt_left hA) h
    linarith
  · have h' := one_div_le_one_div_of_le (lt_max_of_lt_left hA) h
    linarith
  · have h' := one_div_le_one_div_of_le (lt_max_of_lt_left hB) h
    linarith
  · have h' := one_div_le_one_div_of_le (lt_max_of_lt_left hB) h
    linarith
  · have h' := one_div_le_one_div_of_le (lt_max_of_lt_left hC) h
    linarith

def signedFrequency {N : ℕ} (i : SignedModes N) : ℤ :=
  if i.1 then ((i.2.val + 1 : ℕ) : ℤ) else -((i.2.val + 1 : ℕ) : ℤ)

theorem signedFrequency_abs {N : ℕ} (i : SignedModes N) :
    |(signedFrequency i : ℝ)| = ((i.2.val + 1 : ℕ) : ℝ) := by
  rcases i with ⟨b, n⟩
  cases b <;> simp only [signedFrequency, Bool.false_eq_true, ↓reduceIte,
    Int.cast_neg, Int.cast_natCast, abs_neg]
  all_goals exact abs_of_nonneg (by positivity)

theorem signedFrequency_ne_zero {N : ℕ} (i : SignedModes N) : signedFrequency i ≠ 0 := by
  intro hzero
  have h := signedFrequency_abs i
  rw [hzero, Int.cast_zero, abs_zero] at h
  have hp : (0 : ℝ) < ((i.2.val + 1 : ℕ) : ℝ) := by positivity
  linarith

theorem signedFrequency_injective (N : ℕ) : Function.Injective (@signedFrequency N) := by
  rintro ⟨b, n⟩ ⟨c, m⟩ h
  cases b <;> cases c <;> simp only [signedFrequency, Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals
    have hn : 0 ≤ n.val := Nat.zero_le _
    have hm : 0 ≤ m.val := Nat.zero_le _
    first | omega | congr 1; apply Fin.ext; omega

theorem finite_single_collision_bound {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (c : ℝ) (hc : 0 ≤ c)
    (hunique : ∀ i j, p i → p j → i = j) :
    (∑ i : ι, if p i then c else 0) ≤ c := by
  classical
  by_cases hp : ∃ j, p j
  · obtain ⟨j, hj⟩ := hp
    have hsum : (∑ i : ι, if p i then c else 0) = c := by
      calc
        _ = if p j then c else 0 := by
          apply Finset.sum_eq_single j
          · intro k _ hkj
            have hk : ¬p k := fun hk => hkj (hunique k j hk hj)
            simp [hk]
          · intro hjnot
            exact (hjnot (Finset.mem_univ j)).elim
        _ = c := if_pos hj
    exact hsum.le
  · have hnone : ∀ i, ¬p i := fun i hi => hp ⟨i, hi⟩
    simpa only [if_neg (hnone _), Finset.sum_const_zero] using hc

/-- Cauchy--Schwarz along one zero-sum frequency constraint. -/
theorem finite_convolution_bound {ι : Type*} [Fintype ι]
    (frequency : ι → ℤ) (hfrequency : Function.Injective frequency)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) (s : ℤ) :
    (∑ i : ι, ∑ j : ι, if frequency i + frequency j = s then x i * y j else 0) ≤
      Real.sqrt (∑ i : ι, x i ^ 2) * Real.sqrt (∑ j : ι, y j ^ 2) := by
  classical
  let U : ℝ := ∑ i : ι, ∑ j : ι, if frequency i + frequency j = s then x i ^ 2 else 0
  let V : ℝ := ∑ i : ι, ∑ j : ι, if frequency i + frequency j = s then y j ^ 2 else 0
  have hU : U ≤ ∑ i, x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply finite_single_collision_bound _ _ (sq_nonneg _)
    intro j k hj hk
    exact hfrequency (add_left_cancel (hj.trans hk.symm))
  have hV : V ≤ ∑ j, y j ^ 2 := by
    dsimp only [V]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j _
    apply finite_single_collision_bound _ _ (sq_nonneg _)
    intro i k hi hk
    exact hfrequency (add_right_cancel (hi.trans hk.symm))
  have hCS : (∑ i : ι, ∑ j : ι,
      if frequency i + frequency j = s then x i * y j else 0) ^ 2 ≤ U * V := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun p : ι × ι => if frequency p.1 + frequency p.2 = s then x p.1 * y p.2 else 0)
      (f := fun p : ι × ι => if frequency p.1 + frequency p.2 = s then x p.1 ^ 2 else 0)
      (g := fun p : ι × ι => if frequency p.1 + frequency p.2 = s then y p.2 ^ 2 else 0)
      (fun p _ => by split_ifs <;> positivity)
      (fun p _ => by split_ifs <;> positivity)
      (fun p _ => by split_ifs <;> simp [mul_pow])
    simpa only [Fintype.sum_prod_type] using h
  have hVnonneg : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  have hleft : 0 ≤ ∑ i : ι, ∑ j : ι,
      if frequency i + frequency j = s then x i * y j else 0 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact mul_nonneg (hx i) (hy j)
    · exact le_rfl
  apply (sq_le_sq₀ hleft (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact hCS.trans (mul_le_mul hU hV hVnonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _))

def finiteL2 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

theorem finiteL2_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ finiteL2 x :=
  Real.sqrt_nonneg _

def pairForm (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ) : ℝ :=
  ∑ k : SignedModes N, ∑ l : SignedModes N,
    (hardyKernel k.2.val l.2.val * x₃ k * x₄ l) *
      ∑ i : SignedModes N, ∑ j : SignedModes N,
        if signedFrequency i + signedFrequency j = -(signedFrequency k + signedFrequency l)
        then x₁ i * x₂ j else 0

theorem pairForm_bound (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (h₁ : ∀ i, 0 ≤ x₁ i) (h₂ : ∀ i, 0 ≤ x₂ i)
    (h₃ : ∀ i, 0 ≤ x₃ i) (h₄ : ∀ i, 0 ≤ x₄ i) :
    pairForm N x₁ x₂ x₃ x₄ ≤ 8 * finiteL2 x₁ * finiteL2 x₂ * finiteL2 x₃ * finiteL2 x₄ := by
  calc
    _ ≤ ∑ k : SignedModes N, ∑ l : SignedModes N,
        (hardyKernel k.2.val l.2.val * x₃ k * x₄ l) * (finiteL2 x₁ * finiteL2 x₂) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left
        (finite_convolution_bound signedFrequency (signedFrequency_injective N) x₁ x₂ h₁ h₂ _)
        (mul_nonneg (mul_nonneg (hardyKernel_nonneg _ _) (h₃ k)) (h₄ l))
    _ = (finiteL2 x₁ * finiteL2 x₂) *
        ∑ k : SignedModes N, ∑ l : SignedModes N,
          hardyKernel k.2.val l.2.val * x₃ k * x₄ l := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ (finiteL2 x₁ * finiteL2 x₂) * (8 * finiteL2 x₃ * finiteL2 x₄) :=
      mul_le_mul_of_nonneg_left (signed_hardy_bound N x₃ x₄ h₃ h₄)
        (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
    _ = _ := by ring

def quadSum {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, F i j k l

theorem quadSum_swap12 {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℝ) :
    quadSum F = quadSum (fun i j k l => F j i k l) := by
  exact Finset.sum_comm

theorem quadSum_swap23 {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℝ) :
    quadSum F = quadSum (fun i j k l => F i k j l) := by
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem quadSum_swap34 {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℝ) :
    quadSum F = quadSum (fun i j k l => F i j l k) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem quadSum_rotate {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℝ) :
    quadSum F = quadSum (fun i j k l => F k l i j) := by
  have h := Finset.sum_comm (s := (Finset.univ : Finset (ι × ι)))
    (t := (Finset.univ : Finset (ι × ι))) (f := fun p q => F p.1 p.2 q.1 q.2)
  simpa only [Fintype.sum_prod_type, quadSum] using h

def productTerm (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (i j k l : SignedModes N) : ℝ :=
  if signedFrequency i + signedFrequency j + signedFrequency k + signedFrequency l = 0
  then x₁ i * x₂ j * x₃ k * x₄ l else 0

def weightedFour (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (K : SignedModes N → SignedModes N → SignedModes N → SignedModes N → ℝ) : ℝ :=
  quadSum (fun i j k l => productTerm N x₁ x₂ x₃ x₄ i j k l * K i j k l)

def pairContribution (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ) : ℝ :=
  weightedFour N x₁ x₂ x₃ x₄ (fun _ _ k l => hardyKernel k.2.val l.2.val)

theorem pairContribution_eq_pairForm (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ) :
    pairContribution N x₁ x₂ x₃ x₄ = pairForm N x₁ x₂ x₃ x₄ := by
  unfold pairContribution weightedFour
  rw [quadSum_rotate]
  simp only [quadSum, pairForm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hcond : (signedFrequency i + signedFrequency j + signedFrequency k + signedFrequency l = 0) ↔
      (signedFrequency i + signedFrequency j = -(signedFrequency k + signedFrequency l)) := by omega
  simp only [productTerm, hcond]
  split_ifs <;> ring

theorem weightedFour_swap12 (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (K : SignedModes N → SignedModes N → SignedModes N → SignedModes N → ℝ) :
    weightedFour N x₁ x₂ x₃ x₄ K = weightedFour N x₂ x₁ x₃ x₄ (fun i j k l => K j i k l) := by
  unfold weightedFour
  rw [quadSum_swap12]
  congr 1
  funext i j k l
  have hcond : (signedFrequency j + signedFrequency i + signedFrequency k + signedFrequency l = 0) ↔
      (signedFrequency i + signedFrequency j + signedFrequency k + signedFrequency l = 0) := by omega
  simp only [productTerm, hcond]
  split_ifs <;> ring

theorem weightedFour_swap23 (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (K : SignedModes N → SignedModes N → SignedModes N → SignedModes N → ℝ) :
    weightedFour N x₁ x₂ x₃ x₄ K = weightedFour N x₁ x₃ x₂ x₄ (fun i j k l => K i k j l) := by
  unfold weightedFour
  rw [quadSum_swap23]
  congr 1
  funext i j k l
  have hcond : (signedFrequency i + signedFrequency k + signedFrequency j + signedFrequency l = 0) ↔
      (signedFrequency i + signedFrequency j + signedFrequency k + signedFrequency l = 0) := by omega
  simp only [productTerm, hcond]
  split_ifs <;> ring

theorem weightedFour_swap34 (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (K : SignedModes N → SignedModes N → SignedModes N → SignedModes N → ℝ) :
    weightedFour N x₁ x₂ x₃ x₄ K = weightedFour N x₁ x₂ x₄ x₃ (fun i j k l => K i j l k) := by
  unfold weightedFour
  rw [quadSum_swap34]
  congr 1
  funext i j k l
  have hcond : (signedFrequency i + signedFrequency j + signedFrequency l + signedFrequency k = 0) ↔
      (signedFrequency i + signedFrequency j + signedFrequency k + signedFrequency l = 0) := by omega
  simp only [productTerm, hcond]
  split_ifs <;> ring

theorem weightedFour_rotate (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (K : SignedModes N → SignedModes N → SignedModes N → SignedModes N → ℝ) :
    weightedFour N x₁ x₂ x₃ x₄ K = weightedFour N x₃ x₄ x₁ x₂ (fun i j k l => K k l i j) := by
  unfold weightedFour
  rw [quadSum_rotate]
  congr 1
  funext i j k l
  have hcond : (signedFrequency k + signedFrequency l + signedFrequency i + signedFrequency j = 0) ↔
      (signedFrequency i + signedFrequency j + signedFrequency k + signedFrequency l = 0) := by omega
  simp only [productTerm, hcond]
  split_ifs <;> ring

theorem weightedFour_add (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (K K' : SignedModes N → SignedModes N → SignedModes N → SignedModes N → ℝ) :
    weightedFour N x₁ x₂ x₃ x₄ (fun i j k l => K i j k l + K' i j k l) =
      weightedFour N x₁ x₂ x₃ x₄ K + weightedFour N x₁ x₂ x₃ x₄ K' := by
  simp only [weightedFour, quadSum, mul_add, Finset.sum_add_distrib]

theorem weightedFour_mono (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (h₁ : ∀ i, 0 ≤ x₁ i) (h₂ : ∀ i, 0 ≤ x₂ i)
    (h₃ : ∀ i, 0 ≤ x₃ i) (h₄ : ∀ i, 0 ≤ x₄ i)
    (K K' : SignedModes N → SignedModes N → SignedModes N → SignedModes N → ℝ)
    (hK : ∀ i j k l, K i j k l ≤ K' i j k l) :
    weightedFour N x₁ x₂ x₃ x₄ K ≤ weightedFour N x₁ x₂ x₃ x₄ K' := by
  unfold weightedFour quadSum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left (hK i j k l)
  unfold productTerm
  split_ifs
  · exact mul_nonneg (mul_nonneg (mul_nonneg (h₁ i) (h₂ j)) (h₃ k)) (h₄ l)
  · exact le_rfl

theorem hardyKernel_eq_reciprocal {N : ℕ} (i j : SignedModes N) :
    hardyKernel i.2.val j.2.val =
      1 / max |(signedFrequency i : ℝ)| |(signedFrequency j : ℝ)| := by
  simp only [hardyKernel, signedFrequency_abs, Nat.cast_max, one_div]

theorem pairContribution_bound (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (h₁ : ∀ i, 0 ≤ x₁ i) (h₂ : ∀ i, 0 ≤ x₂ i)
    (h₃ : ∀ i, 0 ≤ x₃ i) (h₄ : ∀ i, 0 ≤ x₄ i) :
    pairContribution N x₁ x₂ x₃ x₄ ≤ 8 * finiteL2 x₁ * finiteL2 x₂ * finiteL2 x₃ * finiteL2 x₄ := by
  rw [pairContribution_eq_pairForm]
  exact pairForm_bound N x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄

/-- Finite form of Lemma 4, with an explicit constant uniform in the support.
The upper bound retains both signs and uses the third largest of all four modes. -/
theorem finite_four_linear (N : ℕ) (x₁ x₂ x₃ x₄ : SignedModes N → ℝ)
    (h₁ : ∀ i, 0 ≤ x₁ i) (h₂ : ∀ i, 0 ≤ x₂ i)
    (h₃ : ∀ i, 0 ≤ x₃ i) (h₄ : ∀ i, 0 ≤ x₄ i) :
    weightedFour N x₁ x₂ x₃ x₄
      (fun i j k l => 1 / N₃ (signedFrequency i) (signedFrequency j) (signedFrequency k) (signedFrequency l)) ≤
      48 * finiteL2 x₁ * finiteL2 x₂ * finiteL2 x₃ * finiteL2 x₄ := by
  let KAB := fun (i j _k _l : SignedModes N) => hardyKernel i.2.val j.2.val
  let KAC := fun (i _j k _l : SignedModes N) => hardyKernel i.2.val k.2.val
  let KAD := fun (i _j _k l : SignedModes N) => hardyKernel i.2.val l.2.val
  let KBC := fun (_i j k _l : SignedModes N) => hardyKernel j.2.val k.2.val
  let KBD := fun (_i j _k l : SignedModes N) => hardyKernel j.2.val l.2.val
  let KCD := fun (_i _j k l : SignedModes N) => hardyKernel k.2.val l.2.val
  have hpoint (i j k l : SignedModes N) :
      1 / N₃ (signedFrequency i) (signedFrequency j) (signedFrequency k) (signedFrequency l) ≤
        KAB i j k l + KAC i j k l + KAD i j k l + KBC i j k l + KBD i j k l + KCD i j k l := by
    simpa only [KAB, KAC, KAD, KBC, KBD, KCD, hardyKernel_eq_reciprocal, N₃] using
      reciprocal_thirdLargest_le_pairs
        (abs_cast_pos (signedFrequency_ne_zero i)) (abs_cast_pos (signedFrequency_ne_zero j))
        (abs_cast_pos (signedFrequency_ne_zero k)) (abs_cast_pos (signedFrequency_ne_zero l))
  have hsum := weightedFour_mono N x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ _ _ hpoint
  simp only [weightedFour_add] at hsum
  have hAB : weightedFour N x₁ x₂ x₃ x₄ KAB = pairContribution N x₃ x₄ x₁ x₂ := by
    rw [weightedFour_rotate]
    rfl
  have hAC : weightedFour N x₁ x₂ x₃ x₄ KAC = pairContribution N x₂ x₄ x₁ x₃ := by
    rw [weightedFour_swap12, weightedFour_swap34, weightedFour_swap23]
    rfl
  have hAD : weightedFour N x₁ x₂ x₃ x₄ KAD = pairContribution N x₂ x₃ x₁ x₄ := by
    rw [weightedFour_swap12, weightedFour_swap23]
    rfl
  have hBC : weightedFour N x₁ x₂ x₃ x₄ KBC = pairContribution N x₁ x₄ x₂ x₃ := by
    rw [weightedFour_swap34, weightedFour_swap23]
    rfl
  have hBD : weightedFour N x₁ x₂ x₃ x₄ KBD = pairContribution N x₁ x₃ x₂ x₄ := by
    rw [weightedFour_swap23]
    rfl
  have hCD : weightedFour N x₁ x₂ x₃ x₄ KCD = pairContribution N x₁ x₂ x₃ x₄ := rfl
  rw [hAB, hAC, hAD, hBC, hBD, hCD] at hsum
  have bAB := pairContribution_bound N x₃ x₄ x₁ x₂ h₃ h₄ h₁ h₂
  have bAC := pairContribution_bound N x₂ x₄ x₁ x₃ h₂ h₄ h₁ h₃
  have bAD := pairContribution_bound N x₂ x₃ x₁ x₄ h₂ h₃ h₁ h₄
  have bBC := pairContribution_bound N x₁ x₄ x₂ x₃ h₁ h₄ h₂ h₃
  have bBD := pairContribution_bound N x₁ x₃ x₂ x₄ h₁ h₃ h₂ h₄
  have bCD := pairContribution_bound N x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄
  nlinarith

theorem signedFrequency_surjective_bounded (N : ℕ) (k : ℤ)
    (hk : k ≠ 0) (hbound : k.natAbs ≤ N) : ∃ i : SignedModes N, signedFrequency i = k := by
  rcases Int.eq_nat_or_neg k with ⟨n, hn | hn⟩
  · have hnpos : 0 < n := by omega
    have hnN : n ≤ N := by simpa only [hn, Int.natAbs_natCast] using hbound
    refine ⟨(true, ⟨n - 1, by omega⟩), ?_⟩
    simp only [signedFrequency, ↓reduceIte]
    omega
  · have hnpos : 0 < n := by omega
    have hnN : n ≤ N := by simpa only [hn, Int.natAbs_neg, Int.natAbs_natCast] using hbound
    refine ⟨(false, ⟨n - 1, by omega⟩), ?_⟩
    simp only [signedFrequency, Bool.false_eq_true, ↓reduceIte]
    omega

def boundedMode {N : ℕ} (k : ℤ) (hk : k ≠ 0) (hbound : k.natAbs ≤ N) : SignedModes N :=
  Classical.choose (signedFrequency_surjective_bounded N k hk hbound)

theorem boundedMode_spec {N : ℕ} (k : ℤ) (hk : k ≠ 0) (hbound : k.natAbs ≤ N) :
    signedFrequency (boundedMode k hk hbound) = k :=
  Classical.choose_spec (signedFrequency_surjective_bounded N k hk hbound)

def realL2Norm (x : ℤ → ℝ) : ℝ := Real.sqrt (∑' k : ℤ, x k ^ 2)

theorem realL2Norm_nonneg (x : ℤ → ℝ) : 0 ≤ realL2Norm x := Real.sqrt_nonneg _

theorem finiteL2_sample_le (N : ℕ) (x : ℤ → ℝ) (hx : Summable (fun k => x k ^ 2)) :
    finiteL2 (fun i : SignedModes N => x (signedFrequency i)) ≤ realL2Norm x := by
  classical
  apply Real.sqrt_le_sqrt
  have heq : (∑ k ∈ (Finset.univ : Finset (SignedModes N)).image signedFrequency, x k ^ 2) =
      ∑ i : SignedModes N, x (signedFrequency i) ^ 2 := by
    apply Finset.sum_image
    intro i _ j _ h
    exact signedFrequency_injective N h
  rw [← heq]
  exact hx.sum_le_tsum _ (fun k _ => sq_nonneg _)

theorem sum_le_univ_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (F : κ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    (∑ i : ι, F (e i)) ≤ ∑ j : κ, F j := by
  classical
  have heq : (∑ j ∈ (Finset.univ : Finset ι).image e, F j) = ∑ i : ι, F (e i) := by
    apply Finset.sum_image
    intro i _ j _ h
    exact he h
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hF j)

structure Interaction where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  nonzero : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0
  zero_sum : a + b + c + d = 0

@[ext] theorem Interaction.ext (q r : Interaction)
    (ha : q.a = r.a) (hb : q.b = r.b) (hc : q.c = r.c) (hd : q.d = r.d) : q = r := by
  cases q
  cases r
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

def fourLinearTerm (x₁ x₂ x₃ x₄ : ℤ → ℝ) (q : Interaction) : ℝ :=
  x₁ q.a * x₂ q.b * x₃ q.c * x₄ q.d / N₃ q.a q.b q.c q.d

theorem fourLinearTerm_nonneg (x₁ x₂ x₃ x₄ : ℤ → ℝ)
    (h₁ : ∀ k, 0 ≤ x₁ k) (h₂ : ∀ k, 0 ≤ x₂ k)
    (h₃ : ∀ k, 0 ≤ x₃ k) (h₄ : ∀ k, 0 ≤ x₄ k) (q : Interaction) :
    0 ≤ fourLinearTerm x₁ x₂ x₃ x₄ q :=
  div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (h₁ _) (h₂ _)) (h₃ _)) (h₄ _))
    (thirdLargest_pos (D := |(q.d : ℝ)|) (abs_cast_pos q.nonzero.1)
      (abs_cast_pos q.nonzero.2.1) (abs_cast_pos q.nonzero.2.2.1)).le

abbrev SignedQuad (N : ℕ) := SignedModes N × SignedModes N × SignedModes N × SignedModes N

theorem four_linear_finset (x₁ x₂ x₃ x₄ : ℤ → ℝ)
    (h₁ : ∀ k, 0 ≤ x₁ k) (h₂ : ∀ k, 0 ≤ x₂ k)
    (h₃ : ∀ k, 0 ≤ x₃ k) (h₄ : ∀ k, 0 ≤ x₄ k)
    (s₁ : Summable (fun k => x₁ k ^ 2)) (s₂ : Summable (fun k => x₂ k ^ 2))
    (s₃ : Summable (fun k => x₃ k ^ 2)) (s₄ : Summable (fun k => x₄ k ^ 2))
    (S : Finset Interaction) :
    ∑ q ∈ S, fourLinearTerm x₁ x₂ x₃ x₄ q ≤
      48 * realL2Norm x₁ * realL2Norm x₂ * realL2Norm x₃ * realL2Norm x₄ := by
  classical
  let N := S.sup (fun q => max q.a.natAbs (max q.b.natAbs (max q.c.natAbs q.d.natAbs)))
  have hbounds (q : Interaction) (hq : q ∈ S) :
      q.a.natAbs ≤ N ∧ q.b.natAbs ≤ N ∧ q.c.natAbs ≤ N ∧ q.d.natAbs ≤ N := by
    have h : max q.a.natAbs (max q.b.natAbs (max q.c.natAbs q.d.natAbs)) ≤ N :=
      Finset.le_sup (f := fun q : Interaction =>
        max q.a.natAbs (max q.b.natAbs (max q.c.natAbs q.d.natAbs))) hq
    exact ⟨(le_max_left _ _).trans h,
      (le_max_left _ _).trans ((le_max_right _ _).trans h),
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans h)),
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans h))⟩
  let e : ↥S → SignedQuad N := fun q =>
    (boundedMode q.val.a q.val.nonzero.1 (hbounds q.val q.property).1,
      boundedMode q.val.b q.val.nonzero.2.1 (hbounds q.val q.property).2.1,
      boundedMode q.val.c q.val.nonzero.2.2.1 (hbounds q.val q.property).2.2.1,
      boundedMode q.val.d q.val.nonzero.2.2.2 (hbounds q.val q.property).2.2.2)
  have heA (q : ↥S) : signedFrequency (e q).1 = q.val.a :=
    boundedMode_spec q.val.a q.val.nonzero.1 (hbounds q.val q.property).1
  have heB (q : ↥S) : signedFrequency (e q).2.1 = q.val.b :=
    boundedMode_spec q.val.b q.val.nonzero.2.1 (hbounds q.val q.property).2.1
  have heC (q : ↥S) : signedFrequency (e q).2.2.1 = q.val.c :=
    boundedMode_spec q.val.c q.val.nonzero.2.2.1 (hbounds q.val q.property).2.2.1
  have heD (q : ↥S) : signedFrequency (e q).2.2.2 = q.val.d :=
    boundedMode_spec q.val.d q.val.nonzero.2.2.2 (hbounds q.val q.property).2.2.2
  have he : Function.Injective e := by
    intro q r h
    apply Subtype.ext
    apply Interaction.ext
    · exact (heA q).symm.trans ((congrArg (fun p : SignedQuad N => signedFrequency p.1) h).trans (heA r))
    · exact (heB q).symm.trans ((congrArg (fun p : SignedQuad N => signedFrequency p.2.1) h).trans (heB r))
    · exact (heC q).symm.trans ((congrArg (fun p : SignedQuad N => signedFrequency p.2.2.1) h).trans (heC r))
    · exact (heD q).symm.trans ((congrArg (fun p : SignedQuad N => signedFrequency p.2.2.2) h).trans (heD r))
  let F : SignedQuad N → ℝ := fun p =>
    productTerm N (fun i => x₁ (signedFrequency i)) (fun i => x₂ (signedFrequency i))
      (fun i => x₃ (signedFrequency i)) (fun i => x₄ (signedFrequency i))
      p.1 p.2.1 p.2.2.1 p.2.2.2 *
        (1 / N₃ (signedFrequency p.1) (signedFrequency p.2.1)
          (signedFrequency p.2.2.1) (signedFrequency p.2.2.2))
  have hF (p : SignedQuad N) : 0 ≤ F p := by
    apply mul_nonneg
    · unfold productTerm
      split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg (h₁ _) (h₂ _)) (h₃ _)) (h₄ _)
      · exact le_rfl
    · apply one_div_nonneg.mpr
      exact (thirdLargest_pos (D := |(signedFrequency p.2.2.2 : ℝ)|)
        (abs_cast_pos (signedFrequency_ne_zero _)) (abs_cast_pos (signedFrequency_ne_zero _))
        (abs_cast_pos (signedFrequency_ne_zero _))).le
  have hFe (q : ↥S) : F (e q) = fourLinearTerm x₁ x₂ x₃ x₄ q.val := by
    simp only [F, productTerm, heA, heB, heC, heD, q.val.zero_sum, ↓reduceIte,
      fourLinearTerm, div_eq_mul_inv, one_mul]
  calc
    _ = ∑ q : ↥S, F (e q) := by
      simp only [hFe]
      exact (Finset.sum_coe_sort S (fun q => fourLinearTerm x₁ x₂ x₃ x₄ q)).symm
    _ ≤ ∑ p : SignedQuad N, F p := sum_le_univ_of_injective e he F hF
    _ ≤ 48 * finiteL2 (fun i : SignedModes N => x₁ (signedFrequency i)) *
        finiteL2 (fun i : SignedModes N => x₂ (signedFrequency i)) *
        finiteL2 (fun i : SignedModes N => x₃ (signedFrequency i)) *
        finiteL2 (fun i : SignedModes N => x₄ (signedFrequency i)) := by
      simpa only [F, Fintype.sum_prod_type, weightedFour, quadSum] using
        finite_four_linear N _ _ _ _ (fun i => h₁ _) (fun i => h₂ _) (fun i => h₃ _) (fun i => h₄ _)
    _ ≤ _ := by
      have p₁ := finiteL2_nonneg (fun i : SignedModes N => x₁ (signedFrequency i))
      have p₂ := finiteL2_nonneg (fun i : SignedModes N => x₂ (signedFrequency i))
      have p₃ := finiteL2_nonneg (fun i : SignedModes N => x₃ (signedFrequency i))
      have p₄ := finiteL2_nonneg (fun i : SignedModes N => x₄ (signedFrequency i))
      have r₁ := realL2Norm_nonneg x₁
      have r₂ := realL2Norm_nonneg x₂
      have r₃ := realL2Norm_nonneg x₃
      have r₄ := realL2Norm_nonneg x₄
      gcongr
      · exact finiteL2_sample_le N x₁ s₁
      · exact finiteL2_sample_le N x₂ s₂
      · exact finiteL2_sample_le N x₃ s₃
      · exact finiteL2_sample_le N x₄ s₄

/-- Lemma 4 on arbitrary nonnegative square-summable sequences. -/
theorem four_linear (x₁ x₂ x₃ x₄ : ℤ → ℝ)
    (h₁ : ∀ k, 0 ≤ x₁ k) (h₂ : ∀ k, 0 ≤ x₂ k)
    (h₃ : ∀ k, 0 ≤ x₃ k) (h₄ : ∀ k, 0 ≤ x₄ k)
    (s₁ : Summable (fun k => x₁ k ^ 2)) (s₂ : Summable (fun k => x₂ k ^ 2))
    (s₃ : Summable (fun k => x₃ k ^ 2)) (s₄ : Summable (fun k => x₄ k ^ 2)) :
    Summable (fourLinearTerm x₁ x₂ x₃ x₄) ∧
      ∑' q : Interaction, fourLinearTerm x₁ x₂ x₃ x₄ q ≤
        48 * realL2Norm x₁ * realL2Norm x₂ * realL2Norm x₃ * realL2Norm x₄ := by
  have hnonneg := fourLinearTerm_nonneg x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄
  have hbound := four_linear_finset x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ s₁ s₂ s₃ s₄
  exact ⟨summable_of_sum_le hnonneg hbound, Real.tsum_le_of_sum_le hnonneg hbound⟩

theorem four_linear_restricted (x₁ x₂ x₃ x₄ : ℤ → ℝ)
    (h₁ : ∀ k, 0 ≤ x₁ k) (h₂ : ∀ k, 0 ≤ x₂ k)
    (h₃ : ∀ k, 0 ≤ x₃ k) (h₄ : ∀ k, 0 ≤ x₄ k)
    (s₁ : Summable (fun k => x₁ k ^ 2)) (s₂ : Summable (fun k => x₂ k ^ 2))
    (s₃ : Summable (fun k => x₃ k ^ 2)) (s₄ : Summable (fun k => x₄ k ^ 2))
    (A : Set Interaction) :
    Summable (A.indicator (fourLinearTerm x₁ x₂ x₃ x₄)) ∧
      ∑' q : Interaction, A.indicator (fourLinearTerm x₁ x₂ x₃ x₄) q ≤
        48 * realL2Norm x₁ * realL2Norm x₂ * realL2Norm x₃ * realL2Norm x₄ := by
  classical
  have h := four_linear x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ s₁ s₂ s₃ s₄
  have hA := h.1.indicator A
  refine ⟨hA, (hA.tsum_le_tsum ?_ h.1).trans h.2⟩
  intro q
  by_cases hq : q ∈ A
  · simp only [Set.indicator_of_mem hq, le_refl]
  · simp only [Set.indicator_of_notMem hq]
    exact fourLinearTerm_nonneg x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ q

def oscillation (α s : ℝ) : ℂ := Complex.exp (-Complex.I * (s : ℂ) * (α : ℂ))

theorem oscillation_continuous (α : ℝ) : Continuous (oscillation α) := by
  unfold oscillation
  fun_prop

theorem oscillation_norm (α s : ℝ) : ‖oscillation α s‖ = 1 := by
  simp [oscillation, Complex.norm_exp]

@[simp] theorem oscillation_zero (α : ℝ) : oscillation α 0 = 1 := by simp [oscillation]

theorem oscillation_add (α β s : ℝ) :
    oscillation α s * oscillation β s = oscillation (α + β) s := by
  rw [oscillation, oscillation, ← Complex.exp_add, oscillation]
  congr 1
  push_cast
  ring

theorem oscillation_derivative (α s : ℝ) :
    HasDerivAt (oscillation α) ((-Complex.I * (α : ℂ)) * oscillation α s) s := by
  have h := ((((hasDerivAt_id s).ofReal_comp).const_mul (-Complex.I)).mul_const (α : ℂ)).cexp
  unfold oscillation
  simpa only [id_eq, Complex.ofReal_one, mul_one, mul_comm] using h

theorem oscillation_lipschitz (α s r : ℝ) :
    ‖oscillation α s - oscillation α r‖ ≤ |α| * |s - r| := by
  have hfactor : oscillation α s = oscillation α r * oscillation α (s - r) := by
    simp only [oscillation, ← Complex.exp_add, Complex.ofReal_sub]
    congr 1
    ring
  have hdiff : oscillation α s - oscillation α r =
      oscillation α r * (oscillation α (s - r) - 1) := by rw [hfactor]; ring
  rw [hdiff, norm_mul, oscillation_norm, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(α * (s - r)))
  have hexp : Complex.exp (Complex.I * ((-(α * (s - r)) : ℝ) : ℂ)) = oscillation α (s - r) := by
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  rw [hexp] at h
  simpa only [Real.norm_eq_abs, abs_neg, abs_mul] using h

def average (τ : ℝ) (g : ℝ → ℂ) : ℂ := (τ : ℂ)⁻¹ * ∫ s : ℝ in (0 : ℝ)..τ, g s

theorem average_oscillation (τ α : ℝ) : average τ (oscillation α) = phaseAverage τ α := rfl

theorem average_const {τ : ℝ} (hτ : τ ≠ 0) (z : ℂ) : average τ (fun _ => z) = z := by
  simp [average, Complex.real_smul, Complex.ofReal_ne_zero.mpr hτ]

theorem average_sub (τ : ℝ) {g h : ℝ → ℂ}
    (hg : IntervalIntegrable g volume 0 τ) (hh : IntervalIntegrable h volume 0 τ) :
    average τ (fun s => g s - h s) = average τ g - average τ h := by
  simp only [average, intervalIntegral.integral_sub hg hh, mul_sub]

theorem average_mul_const (τ : ℝ) (g : ℝ → ℂ) (z : ℂ) :
    average τ (fun s => g s * z) = average τ g * z := by
  simp only [average, intervalIntegral.integral_mul_const, mul_assoc]

theorem average_norm_le_integral {τ : ℝ} (hτ : 0 < τ)
    (g : ℝ → ℂ) (b : ℝ → ℝ) (hb : IntervalIntegrable b volume 0 τ)
    (hbound : ∀ s ∈ Set.Icc 0 τ, ‖g s‖ ≤ b s) :
    ‖average τ g‖ ≤ τ⁻¹ * ∫ s : ℝ in (0 : ℝ)..τ, b s := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le hτ.le
    (Filter.Eventually.of_forall fun s (hs : s ∈ Set.Ioc 0 τ) => hbound s ⟨hs.1.le, hs.2⟩) hb
  simp only [average, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  exact mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hτ.le)

theorem average_norm_le_linear {τ A : ℝ} (hτ : 0 < τ) (g : ℝ → ℂ)
    (hbound : ∀ s ∈ Set.Icc 0 τ, ‖g s‖ ≤ A * s) :
    ‖average τ g‖ ≤ τ * A / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => A * s) volume 0 τ :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have h := average_norm_le_integral hτ g _ hi hbound
  rw [intervalIntegral.integral_const_mul, integral_id] at h
  norm_num at h
  calc
    _ ≤ τ⁻¹ * (A * (τ ^ 2 / 2)) := h
    _ = τ * A / 2 := by field_simp [hτ.ne']

theorem average_norm_le_reverse_linear {τ A : ℝ} (hτ : 0 < τ) (g : ℝ → ℂ)
    (hbound : ∀ s ∈ Set.Icc 0 τ, ‖g s‖ ≤ A * (τ - s)) :
    ‖average τ g‖ ≤ τ * A / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => A * (τ - s)) volume 0 τ :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have h := average_norm_le_integral hτ g _ hi hbound
  have hint : (∫ s : ℝ in (0 : ℝ)..τ, A * (τ - s)) = A * τ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun _ : ℝ => τ) (g := fun s : ℝ => s)
        (continuous_const.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, integral_id, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), smul_eq_mul]
    ring
  rw [hint] at h
  calc
    _ ≤ τ⁻¹ * (A * τ ^ 2 / 2) := h
    _ = τ * A / 2 := by field_simp [hτ.ne']

theorem phaseAverage_norm_le_one {τ : ℝ} (hτ : 0 < τ) (α : ℝ) :
    ‖phaseAverage τ α‖ ≤ 1 := by
  rw [← average_oscillation]
  have h := average_norm_le_integral hτ (oscillation α) (fun _ => 1)
    (continuous_const.intervalIntegrable _ _) (fun s _ => (oscillation_norm α s).le)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
    inv_mul_cancel₀ hτ.ne'] using h

theorem phaseAverage_relation {τ : ℝ} (hτ : τ ≠ 0) (α : ℝ) :
    (-Complex.I * (τ : ℂ) * (α : ℂ)) * phaseAverage τ α = oscillation α τ - 1 := by
  have hi : IntervalIntegrable (fun s => (-Complex.I * (α : ℂ)) * oscillation α s) volume 0 τ :=
    (continuous_const.mul (oscillation_continuous α)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => oscillation_derivative α s) hi
  rw [intervalIntegral.integral_const_mul, oscillation_zero] at h
  calc
    _ = (-Complex.I * (α : ℂ)) * ∫ s : ℝ in (0 : ℝ)..τ, oscillation α s := by
      change (-Complex.I * (τ : ℂ) * (α : ℂ)) *
        ((τ : ℂ)⁻¹ * ∫ s : ℝ in (0 : ℝ)..τ, oscillation α s) = _
      field_simp [Complex.ofReal_ne_zero.mpr hτ]
    _ = _ := h

theorem average_oscillation_sub_one_bound {τ : ℝ} (hτ : 0 < τ) (α : ℝ) :
    ‖average τ (fun s => oscillation α s - 1)‖ ≤ τ * |α| / 2 := by
  apply average_norm_le_linear hτ
  intro s hs
  simpa only [oscillation_zero, sub_zero, abs_of_nonneg hs.1] using oscillation_lipschitz α s 0

theorem phaseAverage_endpoint_zero {τ : ℝ} (hτ : 0 < τ) (α : ℝ) :
    ‖1 - phaseAverage τ α‖ ≤ τ * |α| / 2 := by
  have heq : average τ (fun s => oscillation α s - 1) = phaseAverage τ α - 1 := by
    rw [average_sub τ ((oscillation_continuous α).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), average_oscillation, average_const hτ.ne']
  rw [norm_sub_rev, ← heq]
  exact average_oscillation_sub_one_bound hτ α

theorem phaseAverage_endpoint_top {τ : ℝ} (hτ : 0 < τ) (α : ℝ) :
    ‖oscillation α τ - phaseAverage τ α‖ ≤ τ * |α| / 2 := by
  have heq : average τ (fun s => oscillation α τ - oscillation α s) =
      oscillation α τ - phaseAverage τ α := by
    rw [average_sub τ (continuous_const.intervalIntegrable _ _)
      ((oscillation_continuous α).intervalIntegrable _ _), average_const hτ.ne', average_oscillation]
  rw [← heq]
  apply average_norm_le_reverse_linear hτ
  intro s hs
  simpa only [abs_of_nonneg (sub_nonneg.mpr hs.2)] using oscillation_lipschitz α τ s

theorem covariance_difference_identity {τ : ℝ} (hτ : τ ≠ 0) (α β : ℝ) :
    covariance τ α β =
      average τ (fun s => (oscillation α s - 1) * oscillation β s) -
        average τ (fun s => oscillation α s - 1) * phaseAverage τ β := by
  have hprod : average τ (fun s => oscillation α s * oscillation β s) = phaseAverage τ (α + β) := by
    have hfun : (fun s => oscillation α s * oscillation β s) = oscillation (α + β) :=
      funext (fun s => oscillation_add α β s)
    rw [hfun, average_oscillation]
  have hdiff : average τ (fun s => (oscillation α s - 1) * oscillation β s) =
      phaseAverage τ (α + β) - phaseAverage τ β := by
    have hfun : (fun s => (oscillation α s - 1) * oscillation β s) =
        (fun s => oscillation α s * oscillation β s - oscillation β s) := by funext s; ring
    rw [hfun, average_sub τ (g := fun s => oscillation α s * oscillation β s)
      (h := oscillation β)
      (((oscillation_continuous α).mul (oscillation_continuous β)).intervalIntegrable _ _)
      ((oscillation_continuous β).intervalIntegrable _ _), hprod, average_oscillation]
  have hmean : average τ (fun s => oscillation α s - 1) = phaseAverage τ α - 1 := by
    rw [average_sub τ ((oscillation_continuous α).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), average_oscillation, average_const hτ]
  rw [hdiff, hmean]
  unfold covariance
  ring

theorem covariance_small_phase {τ : ℝ} (hτ : 0 < τ) (α β : ℝ) :
    ‖covariance τ α β‖ ≤ τ * |α| := by
  have hfirst : ‖average τ (fun s => (oscillation α s - 1) * oscillation β s)‖ ≤ τ * |α| / 2 := by
    apply average_norm_le_linear hτ
    intro s hs
    rw [norm_mul, oscillation_norm, mul_one]
    simpa only [oscillation_zero, sub_zero, abs_of_nonneg hs.1] using oscillation_lipschitz α s 0
  have hsecond := average_oscillation_sub_one_bound hτ α
  have hbeta := phaseAverage_norm_le_one hτ β
  have hsecondProd : ‖average τ (fun s => oscillation α s - 1) * phaseAverage τ β‖ ≤ τ * |α| / 2 := by
    rw [norm_mul]
    exact (mul_le_mul hsecond hbeta (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  rw [covariance_difference_identity hτ.ne']
  exact (norm_sub_le _ _).trans (by linarith)

/-- Lemma 2 (6), with the precise endpoint constant from the paper. -/
theorem covariance_small_bound {τ : ℝ} (hτ : 0 < τ) (α β : ℝ) :
    ‖covariance τ α β‖ ≤ τ * min |α| |β| := by
  rw [mul_min_of_nonneg _ _ hτ.le]
  apply le_min
  · exact covariance_small_phase hτ α β
  · rw [covariance_comm]
    exact covariance_small_phase hτ β α

theorem covariance_integration_identity {τ : ℝ} (hτ : τ ≠ 0) (α β : ℝ) :
    (-Complex.I * (τ : ℂ) * (β : ℂ)) * covariance τ α β =
      (oscillation α τ - phaseAverage τ α) * oscillation β τ -
        (1 - phaseAverage τ α) +
          (Complex.I * (τ : ℂ) * (α : ℂ)) * phaseAverage τ (α + β) := by
  have hsum := phaseAverage_relation hτ (α + β)
  have hbeta := phaseAverage_relation hτ β
  rw [← oscillation_add] at hsum
  simp only [Complex.ofReal_add] at hsum
  unfold covariance
  linear_combination hsum - phaseAverage τ α * hbeta

theorem covariance_ratio_phase {τ : ℝ} (hτ : 0 < τ) (α β : ℝ) (hβ : β ≠ 0) :
    ‖covariance τ α β‖ ≤ 2 * |α| / |β| := by
  have hzero := phaseAverage_endpoint_zero hτ α
  have htop := phaseAverage_endpoint_top hτ α
  have hsum := phaseAverage_norm_le_one hτ (α + β)
  have hforce : ‖(Complex.I * (τ : ℂ) * (α : ℂ)) * phaseAverage τ (α + β)‖ ≤ τ * |α| := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hτ.le, one_mul]
    exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg hτ.le (abs_nonneg _))).trans_eq (mul_one _)
  have hnorm : τ * |β| * ‖covariance τ α β‖ ≤ 2 * τ * |α| := by
    calc
      _ = ‖(-Complex.I * (τ : ℂ) * (β : ℂ)) * covariance τ α β‖ := by
        simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hτ.le, one_mul]
      _ = ‖(oscillation α τ - phaseAverage τ α) * oscillation β τ -
          (1 - phaseAverage τ α) + (Complex.I * (τ : ℂ) * (α : ℂ)) * phaseAverage τ (α + β)‖ := by
        rw [covariance_integration_identity hτ.ne']
      _ ≤ ‖(oscillation α τ - phaseAverage τ α) * oscillation β τ -
          (1 - phaseAverage τ α)‖ +
          ‖(Complex.I * (τ : ℂ) * (α : ℂ)) * phaseAverage τ (α + β)‖ := norm_add_le _ _
      _ ≤ (‖oscillation α τ - phaseAverage τ α‖ + ‖1 - phaseAverage τ α‖) +
          ‖(Complex.I * (τ : ℂ) * (α : ℂ)) * phaseAverage τ (α + β)‖ := by
        have h := norm_sub_le
          ((oscillation α τ - phaseAverage τ α) * oscillation β τ) (1 - phaseAverage τ α)
        simp only [norm_mul, oscillation_norm, mul_one] at h
        linarith
      _ ≤ 2 * τ * |α| := by linarith
  apply (le_div_iff₀ (abs_pos.mpr hβ)).mpr
  apply (mul_le_mul_iff_right₀ hτ).mp
  nlinarith only [hnorm]

/-- Lemma 2 (5): retain both ratios rather than selecting only one phase. -/
theorem covariance_ratio_bound {τ : ℝ} (hτ : 0 < τ) (α β : ℝ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    ‖covariance τ α β‖ ≤ 2 * min |α / β| |β / α| := by
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_min
  · simpa only [abs_div, mul_div_assoc] using covariance_ratio_phase hτ α β hβ
  · rw [covariance_comm]
    simpa only [abs_div, mul_div_assoc] using covariance_ratio_phase hτ β α hα

def phaseAlpha (a b : ℤ) : ℝ := 3 * (a : ℝ) * (b : ℝ) * ((a + b : ℤ) : ℝ)
def phaseBeta (k c p : ℤ) : ℝ := 3 * (k : ℝ) * (c : ℝ) * (p : ℝ)

theorem intCast_ne_zero {k : ℤ} (hk : k ≠ 0) : (k : ℝ) ≠ 0 := by exact_mod_cast hk

theorem phaseAlpha_ne_zero {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hp : a + b ≠ 0) :
    phaseAlpha a b ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (intCast_ne_zero ha)) (intCast_ne_zero hb))
    (intCast_ne_zero hp)

theorem phaseBeta_ne_zero {k c p : ℤ} (hk : k ≠ 0) (hc : c ≠ 0) (hp : p ≠ 0) :
    phaseBeta k c p ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (intCast_ne_zero hk)) (intCast_ne_zero hc))
    (intCast_ne_zero hp)

theorem phase_ratio_forward {a b c k : ℤ} (hc : c ≠ 0) (hk : k ≠ 0) (hp : a + b ≠ 0) :
    |phaseAlpha a b / phaseBeta k c (a + b)| =
      |(a : ℝ) * (b : ℝ)| / |(k : ℝ) * (c : ℝ)| := by
  have h : phaseAlpha a b / phaseBeta k c (a + b) =
      ((a : ℝ) * (b : ℝ)) / ((k : ℝ) * (c : ℝ)) := by
    unfold phaseAlpha phaseBeta
    field_simp [intCast_ne_zero hc, intCast_ne_zero hk, intCast_ne_zero hp]
  rw [h, abs_div]

theorem phase_ratio_backward {a b c k : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hp : a + b ≠ 0) :
    |phaseBeta k c (a + b) / phaseAlpha a b| =
      |(k : ℝ) * (c : ℝ)| / |(a : ℝ) * (b : ℝ)| := by
  have h : phaseBeta k c (a + b) / phaseAlpha a b =
      ((k : ℝ) * (c : ℝ)) / ((a : ℝ) * (b : ℝ)) := by
    unfold phaseAlpha phaseBeta
    field_simp [intCast_ne_zero ha, intCast_ne_zero hb, intCast_ne_zero hp]
  rw [h, abs_div]

theorem phaseAlpha_abs (a b : ℤ) :
    |phaseAlpha a b| = 3 * |((a + b : ℤ) : ℝ)| * |(a : ℝ) * (b : ℝ)| := by
  simp only [phaseAlpha, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  ring

theorem phaseBeta_abs (k c p : ℤ) :
    |phaseBeta k c p| = 3 * |(p : ℝ)| * |(k : ℝ) * (c : ℝ)| := by
  simp only [phaseBeta, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  ring

theorem min_div_product {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    min A B / (A * B) = 1 / max A B := by
  rcases le_total A B with h | h
  · rw [min_eq_left h, max_eq_right h]
    field_simp [hA.ne', hB.ne']
  · rw [min_eq_right h, max_eq_left h]
    field_simp [hA.ne', hB.ne']

theorem scalar_covariance_endpoints {η τ A B p D N : ℝ}
    (hτ : 0 < τ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hzero : η ≤ 2 * min (A / B) (B / A))
    (hone : η ≤ 3 * τ * p * min A B)
    (hmzero : 1 / D * min (A / B) (B / A) ≤ 3 / N)
    (hmone : p / max A B ≤ 6 / N) :
    η / D ≤ 6 / N ∧ η / (τ * (A * B)) ≤ 18 / N := by
  constructor
  · calc
      _ ≤ (2 * min (A / B) (B / A)) / D := div_le_div_of_nonneg_right hzero hD.le
      _ = 2 * (1 / D * min (A / B) (B / A)) := by ring
      _ ≤ 2 * (3 / N) := mul_le_mul_of_nonneg_left hmzero (by norm_num)
      _ = _ := by ring
  · calc
      _ ≤ (3 * τ * p * min A B) / (τ * (A * B)) :=
        div_le_div_of_nonneg_right hone (mul_nonneg hτ.le (mul_nonneg hA.le hB.le))
      _ = 3 * p * (min A B / (A * B)) := by field_simp [hτ.ne', hA.ne', hB.ne']
      _ = 3 * (p / max A B) := by rw [min_div_product hA hB]; ring
      _ ≤ 3 * (6 / N) := mul_le_mul_of_nonneg_left hmone (by norm_num)
      _ = _ := by ring

theorem covariance_frequency_endpoints {τ : ℝ} (hτ : 0 < τ) {a b c k : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hk : k ≠ 0)
    (hp : a + b ≠ 0) (hsum : a + b + c = k) :
    (‖covariance τ (phaseAlpha a b) (phaseBeta k c (a + b))‖ / |(k : ℝ)| ≤
      6 / N₃ a b c (-k)) ∧
    (‖covariance τ (phaseAlpha a b) (phaseBeta k c (a + b))‖ /
      (τ * |(a : ℝ) * (b : ℝ) * (c : ℝ) * (k : ℝ)|) ≤ 18 / N₃ a b c (-k)) := by
  have hrat : ‖covariance τ (phaseAlpha a b) (phaseBeta k c (a + b))‖ ≤
      2 * min (|(a : ℝ) * (b : ℝ)| / |(k : ℝ) * (c : ℝ)|)
        (|(k : ℝ) * (c : ℝ)| / |(a : ℝ) * (b : ℝ)|) := by
    have h := covariance_ratio_bound hτ (phaseAlpha a b) (phaseBeta k c (a + b))
      (phaseAlpha_ne_zero ha hb hp) (phaseBeta_ne_zero hk hc hp)
    rw [phase_ratio_forward hc hk hp, phase_ratio_backward ha hb hp] at h
    exact h
  have hsmall : ‖covariance τ (phaseAlpha a b) (phaseBeta k c (a + b))‖ ≤
      3 * τ * |((a + b : ℤ) : ℝ)| * min |(a : ℝ) * (b : ℝ)| |(k : ℝ) * (c : ℝ)| := by
    have h := covariance_small_bound hτ (phaseAlpha a b) (phaseBeta k c (a + b))
    rw [phaseAlpha_abs, phaseBeta_abs,
      ← mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 3 * |((a + b : ℤ) : ℝ)|)] at h
    nlinarith only [h]
  have hz : a + b + c + -k = 0 := by omega
  have hmzero : 1 / |(k : ℝ)| * min
      (|(a : ℝ) * (b : ℝ)| / |(k : ℝ) * (c : ℝ)|)
      (|(k : ℝ) * (c : ℝ)| / |(a : ℝ) * (b : ℝ)|) ≤ 3 / N₃ a b c (-k) := by
    simpa only [Int.cast_neg, mul_neg, abs_neg, mul_comm (c : ℝ) (k : ℝ)] using
      four_frequency_first_majorant ha hb hc (neg_ne_zero.mpr hk) hz
  have hmone : |((a + b : ℤ) : ℝ)| /
      max |(a : ℝ) * (b : ℝ)| |(k : ℝ) * (c : ℝ)| ≤ 6 / N₃ a b c (-k) := by
    simpa only [Int.cast_add, Int.cast_neg, mul_neg, abs_neg, mul_comm (c : ℝ) (k : ℝ)] using
      four_frequency_second_majorant ha hb hc (neg_ne_zero.mpr hk) hz
  have hA : 0 < |(a : ℝ) * (b : ℝ)| := abs_pos.mpr (mul_ne_zero (intCast_ne_zero ha) (intCast_ne_zero hb))
  have hB : 0 < |(k : ℝ) * (c : ℝ)| := abs_pos.mpr (mul_ne_zero (intCast_ne_zero hk) (intCast_ne_zero hc))
  have h := scalar_covariance_endpoints hτ hA hB (abs_cast_pos hk) hrat hsmall hmzero hmone
  refine ⟨h.1, ?_⟩
  have hprod : |(a : ℝ) * (b : ℝ) * (c : ℝ) * (k : ℝ)| =
      |(a : ℝ) * (b : ℝ)| * |(k : ℝ) * (c : ℝ)| := by simp only [abs_mul]; ring
  rw [hprod]
  exact h.2

theorem normalized_interpolation {x A B P γ : ℝ}
    (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 < P)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hxA : x ≤ A) (hxB : x ≤ B * P) :
    x / P ^ γ ≤ A ^ (1 - γ) * B ^ γ := by
  have h := interpolate_bounds hx hA (mul_nonneg hB hP.le) hγ hγ₁ hxA hxB
  calc
    _ ≤ (A ^ (1 - γ) * (B * P) ^ γ) / P ^ γ :=
      div_le_div_of_nonneg_right h (Real.rpow_nonneg hP.le _)
    _ = _ := by
      rw [Real.mul_rpow hB hP.le]
      field_simp [(Real.rpow_pos_of_pos hP γ).ne']

theorem scalar_multiplier_interpolation {η τ D P N γ : ℝ}
    (hη : 0 ≤ η) (hτ : 0 < τ) (hD : 0 < D) (hP : 0 < P) (hN : 0 < N)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (hzero : η / D ≤ 6 / N) (hone : η / (τ * (D * P)) ≤ 18 / N) :
    η / (D * P ^ γ) ≤ 6 ^ (1 - γ) * 18 ^ γ * τ ^ γ / N := by
  have hstrong : η / D ≤ (18 * τ / N) * P := by
    apply (div_le_iff₀ hD).mpr
    have h := (div_le_iff₀ (mul_pos hτ (mul_pos hD hP))).mp hone
    calc
      η ≤ 18 / N * (τ * (D * P)) := h
      _ = (18 * τ / N) * P * D := by ring
  have h := normalized_interpolation (div_nonneg hη hD.le)
    (div_nonneg (by norm_num) hN.le) (by positivity : (0 : ℝ) ≤ 18 * τ / N)
    hP hγ hγ₁ hzero hstrong
  have hNsplit : N ^ (1 - γ) * N ^ γ = N := by
    rw [← Real.rpow_add hN]
    simp
  calc
    _ = (η / D) / P ^ γ := by rw [div_div]
    _ ≤ (6 / N) ^ (1 - γ) * (18 * τ / N) ^ γ := h
    _ = (6 ^ (1 - γ) * (18 * τ) ^ γ) / (N ^ (1 - γ) * N ^ γ) := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 6) hN.le,
        Real.div_rpow (by positivity : (0 : ℝ) ≤ 18 * τ) hN.le]
      field_simp [(Real.rpow_pos_of_pos hN (1 - γ)).ne', (Real.rpow_pos_of_pos hN γ).ne']
    _ = _ := by
      rw [hNsplit, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 18) hτ.le]
      ring

/-- The pointwise interpolated multiplier estimate (11), including `γ=0`. -/
theorem covariance_frequency_interpolated {τ γ : ℝ} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) {a b c k : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hk : k ≠ 0)
    (hp : a + b ≠ 0) (hsum : a + b + c = k) :
    ‖covariance τ (phaseAlpha a b) (phaseBeta k c (a + b))‖ /
      (|(k : ℝ)| * |(a : ℝ) * (b : ℝ) * (c : ℝ)| ^ γ) ≤
        6 ^ (1 - γ) * 18 ^ γ * τ ^ γ / N₃ a b c (-k) := by
  have h := covariance_frequency_endpoints hτ ha hb hc hk hp hsum
  have hprod : |(a : ℝ) * (b : ℝ) * (c : ℝ) * (k : ℝ)| =
      |(k : ℝ)| * |(a : ℝ) * (b : ℝ) * (c : ℝ)| := by simp only [abs_mul]; ring
  rw [hprod] at h
  exact scalar_multiplier_interpolation (norm_nonneg _) hτ (abs_cast_pos hk)
    (abs_pos.mpr (mul_ne_zero (mul_ne_zero (intCast_ne_zero ha) (intCast_ne_zero hb)) (intCast_ne_zero hc)))
    (thirdLargest_pos (D := |((-k : ℤ) : ℝ)|) (abs_cast_pos ha) (abs_cast_pos hb) (abs_cast_pos hc))
    hγ hγ₁ h.1 h.2

abbrev L2Seq := lp (fun _ : ℤ => ℂ) 2

theorem l2_norm_squares_summable (f : L2Seq) : Summable (fun k : ℤ => ‖f k‖ ^ 2) := by
  simpa using f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

theorem realL2Norm_coeffNorm (f : L2Seq) : realL2Norm (fun k => ‖f k‖) = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp [realL2Norm, Real.sqrt_eq_rpow]

def interactionTerm (μ : Interaction → ℂ) (f₁ f₂ f₃ g : L2Seq) (q : Interaction) : ℂ :=
  μ q * f₁ q.a * f₂ q.b * f₃ q.c * g q.d

theorem interactionTerm_bound (μ : Interaction → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hμ : ∀ q, ‖μ q‖ ≤ K / N₃ q.a q.b q.c q.d) (f₁ f₂ f₃ g : L2Seq) :
    Summable (interactionTerm μ f₁ f₂ f₃ g) ∧
      ‖∑' q : Interaction, interactionTerm μ f₁ f₂ f₃ g q‖ ≤
        (48 * K * ‖f₁‖ * ‖f₂‖ * ‖f₃‖) * ‖g‖ := by
  have hfour := four_linear (fun k => ‖f₁ k‖) (fun k => ‖f₂ k‖)
    (fun k => ‖f₃ k‖) (fun k => ‖g k‖)
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) (fun k => norm_nonneg _) (fun k => norm_nonneg _)
    (l2_norm_squares_summable f₁) (l2_norm_squares_summable f₂)
    (l2_norm_squares_summable f₃) (l2_norm_squares_summable g)
  have hpoint (q : Interaction) : ‖interactionTerm μ f₁ f₂ f₃ g q‖ ≤
      K * fourLinearTerm (fun k => ‖f₁ k‖) (fun k => ‖f₂ k‖) (fun k => ‖f₃ k‖) (fun k => ‖g k‖) q := by
    simp only [interactionTerm, norm_mul]
    calc
      _ ≤ (K / N₃ q.a q.b q.c q.d) * ‖f₁ q.a‖ * ‖f₂ q.b‖ * ‖f₃ q.c‖ * ‖g q.d‖ := by
        gcongr
        exact hμ q
      _ = _ := by unfold fourLinearTerm; ring
  have hmajor := hfour.1.mul_left K
  have habs : Summable (fun q => ‖interactionTerm μ f₁ f₂ f₃ g q‖) :=
    hmajor.of_nonneg_of_le (fun q => norm_nonneg _) hpoint
  refine ⟨habs.of_norm, ?_⟩
  calc
    _ ≤ ∑' q : Interaction, ‖interactionTerm μ f₁ f₂ f₃ g q‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' q : Interaction, K * fourLinearTerm (fun k => ‖f₁ k‖) (fun k => ‖f₂ k‖)
        (fun k => ‖f₃ k‖) (fun k => ‖g k‖) q := habs.tsum_le_tsum hpoint hmajor
    _ = K * ∑' q : Interaction, fourLinearTerm (fun k => ‖f₁ k‖) (fun k => ‖f₂ k‖)
        (fun k => ‖f₃ k‖) (fun k => ‖g k‖) q := hfour.1.tsum_mul_left _
    _ ≤ K * (48 * realL2Norm (fun k => ‖f₁ k‖) * realL2Norm (fun k => ‖f₂ k‖) *
        realL2Norm (fun k => ‖f₃ k‖) * realL2Norm (fun k => ‖g k‖)) :=
      mul_le_mul_of_nonneg_left hfour.2 hK
    _ = _ := by simp only [realL2Norm_coeffNorm]; ring

def interactionLinear (μ : Interaction → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hμ : ∀ q, ‖μ q‖ ≤ K / N₃ q.a q.b q.c q.d) (f₁ f₂ f₃ : L2Seq) : L2Seq →ₗ[ℂ] ℂ where
  toFun g := ∑' q : Interaction, interactionTerm μ f₁ f₂ f₃ g q
  map_add' g h := by
    have hg := (interactionTerm_bound μ hK hμ f₁ f₂ f₃ g).1
    have hh := (interactionTerm_bound μ hK hμ f₁ f₂ f₃ h).1
    calc
      _ = ∑' q : Interaction, (interactionTerm μ f₁ f₂ f₃ g q + interactionTerm μ f₁ f₂ f₃ h q) := by
        apply tsum_congr
        intro q
        simp only [interactionTerm, lp.coeFn_add, Pi.add_apply, mul_add]
      _ = _ := hg.tsum_add hh
  map_smul' z g := by
    have hg := (interactionTerm_bound μ hK hμ f₁ f₂ f₃ g).1
    change (∑' q : Interaction, interactionTerm μ f₁ f₂ f₃ (z • g) q) =
      z * ∑' q : Interaction, interactionTerm μ f₁ f₂ f₃ g q
    rw [← hg.tsum_mul_left z]
    apply tsum_congr
    intro q
    simp only [interactionTerm, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

def interactionFunctional (μ : Interaction → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hμ : ∀ q, ‖μ q‖ ≤ K / N₃ q.a q.b q.c q.d) (f₁ f₂ f₃ : L2Seq) : L2Seq →L[ℂ] ℂ :=
  (interactionLinear μ hK hμ f₁ f₂ f₃).mkContinuous (48 * K * ‖f₁‖ * ‖f₂‖ * ‖f₃‖)
    (fun g => (interactionTerm_bound μ hK hμ f₁ f₂ f₃ g).2)

theorem interactionFunctional_norm (μ : Interaction → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hμ : ∀ q, ‖μ q‖ ≤ K / N₃ q.a q.b q.c q.d) (f₁ f₂ f₃ : L2Seq) :
    ‖interactionFunctional μ hK hμ f₁ f₂ f₃‖ ≤ 48 * K * ‖f₁‖ * ‖f₂‖ * ‖f₃‖ := by
  apply LinearMap.mkContinuous_norm_le
  positivity

def interactionOutput (μ : Interaction → ℂ) (f₁ f₂ f₃ : L2Seq) : Fourier := fun d =>
  ∑' q : Interaction, if q.d = d then μ q * f₁ q.a * f₂ q.b * f₃ q.c else 0

theorem interactionTerm_single (μ : Interaction → ℂ) (f₁ f₂ f₃ : L2Seq)
    (d : ℤ) (q : Interaction) :
    interactionTerm μ f₁ f₂ f₃ (lp.single 2 d (1 : ℂ)) q =
      if q.d = d then μ q * f₁ q.a * f₂ q.b * f₃ q.c else 0 := by
  classical
  by_cases h : q.d = d
  · simp [interactionTerm, lp.single_apply, h]
  · simp [interactionTerm, lp.single_apply, h]

theorem interactionFunctional_single (μ : Interaction → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hμ : ∀ q, ‖μ q‖ ≤ K / N₃ q.a q.b q.c q.d) (f₁ f₂ f₃ : L2Seq) (d : ℤ) :
    interactionFunctional μ hK hμ f₁ f₂ f₃ (lp.single 2 d (1 : ℂ)) =
      interactionOutput μ f₁ f₂ f₃ d := by
  change (∑' q : Interaction, interactionTerm μ f₁ f₂ f₃ (lp.single 2 d (1 : ℂ)) q) = _
  simp only [interactionTerm_single, interactionOutput]

theorem interactionOutput_summable (μ : Interaction → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hμ : ∀ q, ‖μ q‖ ≤ K / N₃ q.a q.b q.c q.d) (f₁ f₂ f₃ : L2Seq) (d : ℤ) :
    Summable (fun q : Interaction => if q.d = d then μ q * f₁ q.a * f₂ q.b * f₃ q.c else 0) := by
  have h := (interactionTerm_bound μ hK hμ f₁ f₂ f₃ (lp.single 2 d (1 : ℂ))).1
  have heq : interactionTerm μ f₁ f₂ f₃ (lp.single 2 d (1 : ℂ)) =
      (fun q : Interaction => if q.d = d then μ q * f₁ q.a * f₂ q.b * f₃ q.c else 0) :=
    funext (interactionTerm_single μ f₁ f₂ f₃ d)
  rw [heq] at h
  exact h

theorem hNorm_zero_lp (f : L2Seq) : hNorm 0 (fun k => f k) = ‖f‖ := by
  simpa only [hNorm, weighted_zero, realL2Norm] using realL2Norm_coeffNorm f

/-- The four-linear estimate constructs an actual `L²` trilinear output by Riesz
duality. Its coefficients are the absolutely convergent infinite sums above. -/
theorem interactionOutput_bound (μ : Interaction → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hμ : ∀ q, ‖μ q‖ ≤ K / N₃ q.a q.b q.c q.d) (f₁ f₂ f₃ : L2Seq) :
    InSobolev 0 (interactionOutput μ f₁ f₂ f₃) ∧
      hNorm 0 (interactionOutput μ f₁ f₂ f₃) ≤ 48 * K * ‖f₁‖ * ‖f₂‖ * ‖f₃‖ := by
  let L := interactionFunctional μ hK hμ f₁ f₂ f₃
  let r : L2Seq := (InnerProductSpace.toDual ℂ L2Seq).symm L
  have hr (d : ℤ) : conj (r d) = interactionOutput μ f₁ f₂ f₃ d := by
    have h : inner ℂ r (lp.single 2 d (1 : ℂ)) = L (lp.single 2 d (1 : ℂ)) :=
      InnerProductSpace.toDual_symm_apply
    rw [lp.inner_single_right] at h
    have h' := h.trans (interactionFunctional_single μ hK hμ f₁ f₂ f₃ d)
    simpa only [RCLike.inner_apply', mul_one] using h'
  have hraw : interactionOutput μ f₁ f₂ f₃ = (fun k => (star r : L2Seq) k) := by
    funext d
    simpa only [lp.star_apply, RCLike.star_def] using (hr d).symm
  have hmem : InSobolev 0 (interactionOutput μ f₁ f₂ f₃) := by
    rw [hraw, inSobolev_zero_iff]
    exact (star r : L2Seq).property
  refine ⟨hmem, ?_⟩
  rw [hraw, hNorm_zero_lp, norm_star]
  calc
    ‖r‖ = ‖L‖ := (InnerProductSpace.toDual ℂ L2Seq).symm.norm_map L
    _ ≤ _ := interactionFunctional_norm μ hK hμ f₁ f₂ f₃

theorem abs_rpow_le_weight {s : ℝ} (hs : 0 ≤ s) (k : ℤ) : |(k : ℝ)| ^ s ≤ weight s k := by
  have hbase : |(k : ℝ)| ≤ Real.sqrt (1 + (k : ℝ) ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + (k : ℝ) ^ 2)]
    linarith
  calc
    _ ≤ (Real.sqrt (1 + (k : ℝ) ^ 2)) ^ s := Real.rpow_le_rpow (abs_nonneg _) hbase hs
    _ = weight s k := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + (k : ℝ) ^ 2)]
      unfold weight
      congr 1
      ring

theorem product_rpow_le_weights {s : ℝ} (hs : 0 ≤ s) (a b c : ℤ) :
    |(a : ℝ) * (b : ℝ) * (c : ℝ)| ^ s ≤ weight s a * weight s b * weight s c := by
  rw [abs_mul, abs_mul,
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ |(a : ℝ)| * |(b : ℝ)|) (abs_nonneg _),
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have h₁ := abs_rpow_le_weight hs a
  have h₂ := abs_rpow_le_weight hs b
  have h₃ := abs_rpow_le_weight hs c
  exact mul_le_mul
    (mul_le_mul h₁ h₂ (Real.rpow_nonneg (abs_nonneg _) _) (weight_pos _ _).le)
    h₃ (Real.rpow_nonneg (abs_nonneg _) _) (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le)

def weightProduct (γ : ℝ) (q : Interaction) : ℝ := weight γ q.a * weight γ q.b * weight γ q.c

theorem weightProduct_pos (γ : ℝ) (q : Interaction) : 0 < weightProduct γ q :=
  mul_pos (mul_pos (weight_pos _ _) (weight_pos _ _)) (weight_pos _ _)

def interactionPhase (q : Interaction) : ℝ :=
  (((-q.d) ^ 3 - q.a ^ 3 - q.b ^ 3 - q.c ^ 3 : ℤ) : ℝ)

/-- The exact multiplier in (4), with `d=-k`; its zero intermediate mode
is treated as in the original unrestricted Fourier formula. -/
def cubicCoefficient (τ t : ℝ) (q : Interaction) : ℂ :=
  if q.a + q.b = 0 then 0 else
    (-(τ : ℂ) / (18 * Complex.I * ((-q.d : ℤ) : ℂ))) *
      oscillation (interactionPhase q) t *
        covariance τ (phaseAlpha q.a q.b) (phaseBeta (-q.d) q.c (q.a + q.b))

def normalizedCubicCoefficient (τ t γ : ℝ) (q : Interaction) : ℂ :=
  cubicCoefficient τ t q / (weightProduct γ q : ℂ)

def remainderScale (τ γ : ℝ) : ℝ := (τ / 18) * (6 ^ (1 - γ) * 18 ^ γ * τ ^ γ)

theorem remainderScale_pos {τ : ℝ} (hτ : 0 < τ) (γ : ℝ) : 0 < remainderScale τ γ := by
  unfold remainderScale
  positivity

theorem cubic_prefactor_norm {τ : ℝ} (hτ : 0 ≤ τ) (k : ℤ) :
    ‖-(τ : ℂ) / (18 * Complex.I * (k : ℂ))‖ = τ / (18 * |(k : ℝ)|) := by
  simp only [norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hτ, norm_mul,
    Complex.norm_I, Complex.norm_intCast, mul_one]
  norm_num

theorem normalizedCubicCoefficient_bound {τ γ : ℝ} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (t : ℝ) (q : Interaction) :
    ‖normalizedCubicCoefficient τ t γ q‖ ≤ remainderScale τ γ / N₃ q.a q.b q.c q.d := by
  have hN : 0 < N₃ q.a q.b q.c q.d := thirdLargest_pos
    (abs_cast_pos q.nonzero.1) (abs_cast_pos q.nonzero.2.1) (abs_cast_pos q.nonzero.2.2.1)
  by_cases hp : q.a + q.b = 0
  · simp only [normalizedCubicCoefficient, cubicCoefficient, if_pos hp, zero_div, norm_zero]
    exact div_nonneg (remainderScale_pos hτ γ).le hN.le
  have hk : -q.d ≠ 0 := neg_ne_zero.mpr q.nonzero.2.2.2
  have hsum : q.a + q.b + q.c = -q.d := by have h := q.zero_sum; omega
  have hinterp := covariance_frequency_interpolated hτ hγ hγ₁ q.nonzero.1 q.nonzero.2.1
    q.nonzero.2.2.1 hk hp hsum
  simp only [neg_neg] at hinterp
  have hD : 0 < |((-q.d : ℤ) : ℝ)| := abs_cast_pos hk
  have hP : 0 < |(q.a : ℝ) * (q.b : ℝ) * (q.c : ℝ)| ^ γ :=
    Real.rpow_pos_of_pos (abs_pos.mpr (mul_ne_zero
      (mul_ne_zero (intCast_ne_zero q.nonzero.1) (intCast_ne_zero q.nonzero.2.1))
      (intCast_ne_zero q.nonzero.2.2.1))) γ
  have hW := weightProduct_pos γ q
  have hPW : |(q.a : ℝ) * (q.b : ℝ) * (q.c : ℝ)| ^ γ ≤ weightProduct γ q :=
    product_rpow_le_weights hγ _ _ _
  have hnormW : ‖(weightProduct γ q : ℂ)‖ = weightProduct γ q := by
    rw [Complex.norm_real, Real.norm_of_nonneg hW.le]
  calc
    _ = (τ / 18) *
        (‖covariance τ (phaseAlpha q.a q.b) (phaseBeta (-q.d) q.c (q.a + q.b))‖ /
          (|((-q.d : ℤ) : ℝ)| * weightProduct γ q)) := by
      simp only [normalizedCubicCoefficient, cubicCoefficient, if_neg hp, norm_div,
        norm_mul, cubic_prefactor_norm hτ.le, oscillation_norm, mul_one, hnormW]
      field_simp [hD.ne', hW.ne']
    _ ≤ (τ / 18) *
        (‖covariance τ (phaseAlpha q.a q.b) (phaseBeta (-q.d) q.c (q.a + q.b))‖ /
          (|((-q.d : ℤ) : ℝ)| * |(q.a : ℝ) * (q.b : ℝ) * (q.c : ℝ)| ^ γ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ τ / 18)
      apply (div_le_div_iff₀ (mul_pos hD hW) (mul_pos hD hP)).mpr
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPW hD.le) (norm_nonneg _)
    _ ≤ (τ / 18) * (6 ^ (1 - γ) * 18 ^ γ * τ ^ γ / N₃ q.a q.b q.c q.d) :=
      mul_le_mul_of_nonneg_left hinterp (by positivity)
    _ = _ := by unfold remainderScale; ring

def remainderConstant (γ : ℝ) : ℝ := (48 / 18 : ℝ) * 6 ^ (1 - γ) * 18 ^ γ

theorem remainderConstant_pos (γ : ℝ) : 0 < remainderConstant γ := by
  unfold remainderConstant
  positivity

def remainderRepresentation (τ t γ : ℝ) (f₁ f₂ f₃ : Sobolev γ) : Fourier := fun k =>
  interactionOutput (normalizedCubicCoefficient τ t γ)
    (sobolevEquiv γ f₁) (sobolevEquiv γ f₂) (sobolevEquiv γ f₃) (-k)

theorem remainderRepresentation_bound {τ γ : ℝ} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (t : ℝ) (f₁ f₂ f₃ : Sobolev γ) :
    InSobolev 0 (remainderRepresentation τ t γ f₁ f₂ f₃) ∧
      hNorm 0 (remainderRepresentation τ t γ f₁ f₂ f₃) ≤
        remainderConstant γ * τ ^ (1 + γ) * hNorm γ f₁.val * hNorm γ f₂.val * hNorm γ f₃.val := by
  have hb := interactionOutput_bound (normalizedCubicCoefficient τ t γ) (remainderScale_pos hτ γ).le
    (normalizedCubicCoefficient_bound hτ hγ hγ₁ t)
    (sobolevEquiv γ f₁) (sobolevEquiv γ f₂) (sobolevEquiv γ f₃)
  have hm : InSobolev 0 (remainderRepresentation τ t γ f₁ f₂ f₃) := by
    unfold remainderRepresentation
    have h := reflect_inSobolev_zero hb.1 0
    simpa only [zero_sub] using h
  refine ⟨hm, ?_⟩
  have hnorm : hNorm 0 (remainderRepresentation τ t γ f₁ f₂ f₃) =
      hNorm 0 (interactionOutput (normalizedCubicCoefficient τ t γ)
        (sobolevEquiv γ f₁) (sobolevEquiv γ f₂) (sobolevEquiv γ f₃)) := by
    unfold remainderRepresentation
    have h := reflect_hNorm_zero (interactionOutput (normalizedCubicCoefficient τ t γ)
      (sobolevEquiv γ f₁) (sobolevEquiv γ f₂) (sobolevEquiv γ f₃)) 0
    simpa only [zero_sub] using h
  rw [hnorm]
  have hf₁ : ‖sobolevEquiv γ f₁‖ = hNorm γ f₁.val := (hNorm_eq_lpNorm f₁.property).symm
  have hf₂ : ‖sobolevEquiv γ f₂‖ = hNorm γ f₂.val := (hNorm_eq_lpNorm f₂.property).symm
  have hf₃ : ‖sobolevEquiv γ f₃‖ = hNorm γ f₃.val := (hNorm_eq_lpNorm f₃.property).symm
  have hscale : 48 * remainderScale τ γ = remainderConstant γ * τ ^ (1 + γ) := by
    rw [Real.rpow_add hτ, Real.rpow_one]
    unfold remainderScale remainderConstant
    ring
  calc
    _ ≤ 48 * remainderScale τ γ * ‖sobolevEquiv γ f₁‖ * ‖sobolevEquiv γ f₂‖ * ‖sobolevEquiv γ f₃‖ := hb.2
    _ = _ := by rw [hscale, hf₁, hf₂, hf₃]

/-- The same covariance remainder as an unweighted sum over zero-sum quadruples.
Identification with `remainder`'s pair-indexed formula is a separate obligation. -/
def interactionRemainder (τ t : ℝ) (f₁ f₂ f₃ : Fourier) : Fourier := fun k =>
  ∑' q : Interaction, if q.d = -k then cubicCoefficient τ t q * f₁ q.a * f₂ q.b * f₃ q.c else 0

theorem remainderRepresentation_eq (τ t γ : ℝ) (f₁ f₂ f₃ : Sobolev γ) :
    remainderRepresentation τ t γ f₁ f₂ f₃ = interactionRemainder τ t f₁.val f₂.val f₃.val := by
  funext k
  unfold remainderRepresentation interactionOutput interactionRemainder
  apply tsum_congr
  intro q
  split_ifs
  · change (cubicCoefficient τ t q / (weightProduct γ q : ℂ)) *
        ((weight γ q.a : ℂ) * f₁.val q.a) * ((weight γ q.b : ℂ) * f₂.val q.b) *
        ((weight γ q.c : ℂ) * f₃.val q.c) =
      cubicCoefficient τ t q * f₁.val q.a * f₂.val q.b * f₃.val q.c
    simp only [weightProduct, Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr (weight_pos γ q.a).ne',
      Complex.ofReal_ne_zero.mpr (weight_pos γ q.b).ne',
      Complex.ofReal_ne_zero.mpr (weight_pos γ q.c).ne']
  · rfl

theorem interactionRemainder_bound {τ γ : ℝ} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (t : ℝ) {f₁ f₂ f₃ : Fourier}
    (hf₁ : InSobolev γ f₁) (hf₂ : InSobolev γ f₂) (hf₃ : InSobolev γ f₃) :
    InSobolev 0 (interactionRemainder τ t f₁ f₂ f₃) ∧
      hNorm 0 (interactionRemainder τ t f₁ f₂ f₃) ≤
        remainderConstant γ * τ ^ (1 + γ) * hNorm γ f₁ * hNorm γ f₂ * hNorm γ f₃ := by
  have h := remainderRepresentation_bound hτ hγ hγ₁ t
    (⟨f₁, hf₁⟩ : Sobolev γ) (⟨f₂, hf₂⟩ : Sobolev γ) (⟨f₃, hf₃⟩ : Sobolev γ)
  rw [remainderRepresentation_eq] at h
  exact h

def pairRemainderTerm (τ t : ℝ) (f₁ f₂ f₃ : Fourier) (k : ℤ) (ab : ℤ × ℤ) : ℂ :=
  let a := ab.1
  let b := ab.2
  let c := k - a - b
  if a + b = 0 then 0 else
    (-(τ : ℂ) / (18 * Complex.I * (k : ℂ))) *
      oscillation (((k ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 : ℤ) : ℝ)) t *
        covariance τ (phaseAlpha a b) (phaseBeta k c (a + b)) * f₁ a * f₂ b * f₃ c

theorem pairRemainderTerm_eq_interaction (τ t : ℝ) (f₁ f₂ f₃ : Fourier) (k : ℤ)
    (q : Interaction) (hqd : q.d = -k) :
    pairRemainderTerm τ t f₁ f₂ f₃ k (q.a, q.b) =
      if q.d = -k then cubicCoefficient τ t q * f₁ q.a * f₂ q.b * f₃ q.c else 0 := by
  have hk : -q.d = k := by omega
  have hc : k - q.a - q.b = q.c := by have h := q.zero_sum; omega
  simp only [pairRemainderTerm, hc, hqd, ↓reduceIte, cubicCoefficient, interactionPhase, neg_neg]
  split_ifs <;> ring

theorem remainder_eq_pairSum (τ t : ℝ) (f₁ f₂ f₃ : Fourier) {k : ℤ} (hk : k ≠ 0) :
    remainder τ t f₁ f₂ f₃ k = ∑' ab : ℤ × ℤ, pairRemainderTerm τ t f₁ f₂ f₃ k ab := by
  rw [remainder, if_neg hk, ← tsum_mul_left]
  apply tsum_congr
  intro ab
  dsimp only
  unfold pairRemainderTerm
  dsimp only
  by_cases hp : ab.1 + ab.2 = 0
  · simp only [if_pos hp, mul_zero]
  · simp only [if_neg hp, phaseAlpha, phaseBeta, oscillation, Complex.ofReal_intCast]
    ring

theorem remainder_eq_interactionRemainder (τ t : ℝ) {f₁ f₂ f₃ : Fourier}
    (hf₁ : MeanZero f₁) (hf₂ : MeanZero f₂) (hf₃ : MeanZero f₃) :
    remainder τ t f₁ f₂ f₃ = interactionRemainder τ t f₁ f₂ f₃ := by
  classical
  change f₁ 0 = 0 at hf₁
  change f₂ 0 = 0 at hf₂
  change f₃ 0 = 0 at hf₃
  funext k
  by_cases hk : k = 0
  · subst k
    rw [remainder_meanZero]
    symm
    unfold interactionRemainder
    simp only [neg_zero]
    have hz (q : Interaction) :
        (if q.d = 0 then cubicCoefficient τ t q * f₁ q.a * f₂ q.b * f₃ q.c else 0) = 0 :=
      if_neg q.nonzero.2.2.2
    simp only [hz, tsum_zero]
  rw [remainder_eq_pairSum τ t f₁ f₂ f₃ hk]
  let g : Interaction → ℂ := fun q =>
    if q.d = -k then cubicCoefficient τ t q * f₁ q.a * f₂ q.b * f₃ q.c else 0
  have houtput (q : Function.support g) : q.val.d = -k := by
    by_contra h
    exact q.property (by simp only [g, if_neg h])
  let e : Function.support g → ℤ × ℤ := fun q => (q.val.a, q.val.b)
  have he : Function.Injective e := by
    intro q r h
    have ha : q.val.a = r.val.a := congrArg Prod.fst h
    have hb : q.val.b = r.val.b := congrArg Prod.snd h
    have hqd := houtput q
    have hrd := houtput r
    have hqsum := q.val.zero_sum
    have hrsum := r.val.zero_sum
    apply Subtype.ext
    apply Interaction.ext
    · exact ha
    · exact hb
    · omega
    · omega
  have hcover : Function.support (pairRemainderTerm τ t f₁ f₂ f₃ k) ⊆ Set.range e := by
    intro ab hab
    have hnonzero : pairRemainderTerm τ t f₁ f₂ f₃ k ab ≠ 0 := hab
    have ha : ab.1 ≠ 0 := by
      intro h
      apply hnonzero
      simp [pairRemainderTerm, h, hf₁]
    have hb : ab.2 ≠ 0 := by
      intro h
      apply hnonzero
      simp [pairRemainderTerm, h, hf₂]
    have hc : k - ab.1 - ab.2 ≠ 0 := by
      intro h
      apply hnonzero
      simp [pairRemainderTerm, h, hf₃]
    let q : Interaction := ⟨ab.1, ab.2, k - ab.1 - ab.2, -k,
      ⟨ha, hb, hc, neg_ne_zero.mpr hk⟩, by omega⟩
    have hqd : q.d = -k := rfl
    have hmatch := pairRemainderTerm_eq_interaction τ t f₁ f₂ f₃ k q hqd
    have hgq : g q ≠ 0 := by
      change (if q.d = -k then cubicCoefficient τ t q * f₁ q.a * f₂ q.b * f₃ q.c else 0) ≠ 0
      rw [← hmatch]
      exact hnonzero
    exact ⟨⟨q, hgq⟩, rfl⟩
  have hmatch (q : Function.support g) : pairRemainderTerm τ t f₁ f₂ f₃ k (e q) = g q.val :=
    pairRemainderTerm_eq_interaction τ t f₁ f₂ f₃ k q.val (houtput q)
  exact tsum_eq_tsum_of_ne_zero_bij e he hcover hmatch

/-- Theorem 5 for the exact pair-indexed remainder (4), without a frequency cutoff. -/
theorem mixed_remainder_bound {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (t : ℝ) {f₁ f₂ f₃ : Fourier}
    (hf₁ : InSobolev γ f₁) (hf₂ : InSobolev γ f₂) (hf₃ : InSobolev γ f₃)
    (hm₁ : MeanZero f₁) (hm₂ : MeanZero f₂) (hm₃ : MeanZero f₃) :
    InSobolev 0 (remainder τ t f₁ f₂ f₃) ∧
      hNorm 0 (remainder τ t f₁ f₂ f₃) ≤
        remainderConstant γ * τ ^ (1 + γ) * hNorm γ f₁ * hNorm γ f₂ * hNorm γ f₃ := by
  rw [remainder_eq_interactionRemainder τ t hm₁ hm₂ hm₃]
  exact interactionRemainder_bound hτ hγ hγ₁ t hf₁ hf₂ hf₃

theorem cubicCoefficient_bound_zero {τ : ℝ} (hτ : 0 < τ) (t : ℝ) (q : Interaction) :
    ‖cubicCoefficient τ t q‖ ≤ remainderScale τ 0 / N₃ q.a q.b q.c q.d := by
  simpa only [normalizedCubicCoefficient, weightProduct, weight_zero, one_mul,
    Complex.ofReal_one, div_one] using
    normalizedCubicCoefficient_bound hτ (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) t q

theorem interactionRemainder_summable {τ : ℝ} (hτ : 0 < τ) (t : ℝ) {f₁ f₂ f₃ : Fourier}
    (hf₁ : InSobolev 0 f₁) (hf₂ : InSobolev 0 f₂) (hf₃ : InSobolev 0 f₃) (k : ℤ) :
    Summable (fun q : Interaction =>
      if q.d = -k then cubicCoefficient τ t q * f₁ q.a * f₂ q.b * f₃ q.c else 0) :=
  interactionOutput_summable (cubicCoefficient τ t) (remainderScale_pos hτ 0).le
    (cubicCoefficient_bound_zero hτ t)
    ⟨f₁, (inSobolev_zero_iff _).mp hf₁⟩ ⟨f₂, (inSobolev_zero_iff _).mp hf₂⟩
    ⟨f₃, (inSobolev_zero_iff _).mp hf₃⟩ (-k)

theorem interactionRemainder_sub_left {τ : ℝ} (hτ : 0 < τ) (t : ℝ) {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) :
    interactionRemainder τ t (f - g) h l = interactionRemainder τ t f h l - interactionRemainder τ t g h l := by
  funext k
  unfold interactionRemainder
  calc
    _ = ∑' q : Interaction,
        ((if q.d = -k then cubicCoefficient τ t q * f q.a * h q.b * l q.c else 0) -
          (if q.d = -k then cubicCoefficient τ t q * g q.a * h q.b * l q.c else 0)) := by
      apply tsum_congr
      intro q
      dsimp only [Pi.sub_apply]
      split_ifs <;> ring
    _ = _ := (interactionRemainder_summable hτ t hf hh hl k).tsum_sub
      (interactionRemainder_summable hτ t hg hh hl k)

theorem interactionRemainder_sub_middle {τ : ℝ} (hτ : 0 < τ) (t : ℝ) {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) :
    interactionRemainder τ t f (g - h) l = interactionRemainder τ t f g l - interactionRemainder τ t f h l := by
  funext k
  unfold interactionRemainder
  calc
    _ = ∑' q : Interaction,
        ((if q.d = -k then cubicCoefficient τ t q * f q.a * g q.b * l q.c else 0) -
          (if q.d = -k then cubicCoefficient τ t q * f q.a * h q.b * l q.c else 0)) := by
      apply tsum_congr
      intro q
      dsimp only [Pi.sub_apply]
      split_ifs <;> ring
    _ = _ := (interactionRemainder_summable hτ t hf hg hl k).tsum_sub
      (interactionRemainder_summable hτ t hf hh hl k)

theorem interactionRemainder_sub_right {τ : ℝ} (hτ : 0 < τ) (t : ℝ) {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) :
    interactionRemainder τ t f g (h - l) = interactionRemainder τ t f g h - interactionRemainder τ t f g l := by
  funext k
  unfold interactionRemainder
  calc
    _ = ∑' q : Interaction,
        ((if q.d = -k then cubicCoefficient τ t q * f q.a * g q.b * h q.c else 0) -
          (if q.d = -k then cubicCoefficient τ t q * f q.a * g q.b * l q.c else 0)) := by
      apply tsum_congr
      intro q
      dsimp only [Pi.sub_apply]
      split_ifs <;> ring
    _ = _ := (interactionRemainder_summable hτ t hf hg hh k).tsum_sub
      (interactionRemainder_summable hτ t hf hg hl k)

@[simp] theorem remainderConstant_zero : remainderConstant 0 = 16 := by norm_num [remainderConstant]

theorem interactionRemainder_endpoint {τ : ℝ} (hτ : 0 < τ) (t : ℝ) {f₁ f₂ f₃ : Fourier}
    (hf₁ : InSobolev 0 f₁) (hf₂ : InSobolev 0 f₂) (hf₃ : InSobolev 0 f₃) :
    InSobolev 0 (interactionRemainder τ t f₁ f₂ f₃) ∧
      hNorm 0 (interactionRemainder τ t f₁ f₂ f₃) ≤
        16 * τ * hNorm 0 f₁ * hNorm 0 f₂ * hNorm 0 f₃ := by
  have h := interactionRemainder_bound hτ (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 1) t hf₁ hf₂ hf₃
  simpa only [add_zero, Real.rpow_one, remainderConstant_zero] using h

theorem cubic_difference_identity {τ : ℝ} (hτ : 0 < τ) (t : ℝ) {f w : Fourier}
    (hf : InSobolev 0 f) (hw : InSobolev 0 w) :
    interactionRemainder τ t f f f - interactionRemainder τ t w w w =
      interactionRemainder τ t (f - w) f f + interactionRemainder τ t w (f - w) f +
        interactionRemainder τ t w w (f - w) := by
  rw [interactionRemainder_sub_left hτ t hf hw hf hf,
    interactionRemainder_sub_middle hτ t hw hf hw hf,
    interactionRemainder_sub_right hτ t hw hw hf hw]
  abel

theorem cubic_difference_bound {τ : ℝ} (hτ : 0 < τ) (t : ℝ) {f w : Fourier}
    (hf : InSobolev 0 f) (hw : InSobolev 0 w) :
    hNorm 0 (interactionRemainder τ t f f f - interactionRemainder τ t w w w) ≤
      16 * τ * hNorm 0 (f - w) * (hNorm 0 f + hNorm 0 w) ^ 2 := by
  have hδnonneg := hNorm_nonneg 0 (f - w)
  have hd := hf.sub hw
  have b₁ := interactionRemainder_endpoint hτ t hd hf hf
  have b₂ := interactionRemainder_endpoint hτ t hw hd hf
  have b₃ := interactionRemainder_endpoint hτ t hw hw hd
  have ht := hNorm_add_le (b₁.1.add b₂.1) b₃.1
  have ht' := hNorm_add_le b₁.1 b₂.1
  rw [← cubic_difference_identity hτ t hf hw] at ht
  have hsum : hNorm 0 (interactionRemainder τ t f f f - interactionRemainder τ t w w w) ≤
      16 * τ * hNorm 0 (f - w) *
        (hNorm 0 f ^ 2 + hNorm 0 f * hNorm 0 w + hNorm 0 w ^ 2) := by
    nlinarith only [ht, ht', b₁.2, b₂.2, b₃.2]
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 16 * τ * hNorm 0 (f - w))
  have hprod : 0 ≤ hNorm 0 f * hNorm 0 w := mul_nonneg (hNorm_nonneg _ _) (hNorm_nonneg _ _)
  nlinarith

def numericalRemainderConstant (γ M : ℝ) : ℝ := remainderConstant γ * M ^ 3 + 16 * (2 * M + 1) ^ 2

theorem numericalRemainderConstant_pos (γ : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    0 < numericalRemainderConstant γ M := by
  unfold numericalRemainderConstant
  have hC := remainderConstant_pos γ
  have hterm : 0 < 16 * (2 * M + 1) ^ 2 := by positivity
  have hfirst : 0 ≤ remainderConstant γ * M ^ 3 := mul_nonneg hC.le (by positivity)
  linarith

theorem interaction_numerical_state_estimate {τ γ M : ℝ} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (t : ℝ) {f w : Fourier}
    (hf : InSobolev 0 f) (hw : InSobolev γ w) (hwM : hNorm γ w ≤ M)
    (hδ : hNorm 0 (f - w) ≤ 1) :
    hNorm 0 (interactionRemainder τ t f f f) ≤
      numericalRemainderConstant γ M * τ * (τ ^ γ + hNorm 0 (f - w)) := by
  have hδnonneg := hNorm_nonneg 0 (f - w)
  have hwγnonneg := hNorm_nonneg γ w
  have hw₀ := hw.of_le hγ
  have hM : 0 ≤ M := (hNorm_nonneg γ w).trans hwM
  have hwL2 : hNorm 0 w ≤ M := (hNorm_mono hw hγ).trans hwM
  have htriangle := hNorm_add_le (hf.sub hw₀) hw₀
  rw [sub_add_cancel] at htriangle
  have hfL2 : hNorm 0 f ≤ M + 1 := by linarith
  have hsquare : (hNorm 0 f + hNorm 0 w) ^ 2 ≤ (2 * M + 1) ^ 2 := by
    apply (sq_le_sq₀ (add_nonneg (hNorm_nonneg _ _) (hNorm_nonneg _ _)) (by linarith)).mpr
    linarith
  have hdiff := cubic_difference_bound hτ t hf hw₀
  have hdiff' : hNorm 0 (interactionRemainder τ t f f f - interactionRemainder τ t w w w) ≤
      16 * τ * hNorm 0 (f - w) * (2 * M + 1) ^ 2 :=
    hdiff.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))
  have hsmooth := interactionRemainder_bound hτ hγ hγ₁ t hw hw hw
  have hC := remainderConstant_pos γ
  have hbase : hNorm 0 (interactionRemainder τ t w w w) ≤ remainderConstant γ * τ ^ (1 + γ) * M ^ 3 := by
    calc
      _ ≤ remainderConstant γ * τ ^ (1 + γ) * hNorm γ w * hNorm γ w * hNorm γ w := hsmooth.2
      _ ≤ remainderConstant γ * τ ^ (1 + γ) * M * M * M := by gcongr
      _ = _ := by ring
  rw [Real.rpow_add hτ, Real.rpow_one] at hbase
  have hrough := interactionRemainder_endpoint hτ t hf hf hf
  have hout := hNorm_add_le (hrough.1.sub hsmooth.1) hsmooth.1
  rw [sub_add_cancel] at hout
  have hfirst : 0 ≤ remainderConstant γ * M ^ 3 * τ * hNorm 0 (f - w) := by positivity
  have hsecond : 0 ≤ 16 * (2 * M + 1) ^ 2 * τ * τ ^ γ := by positivity
  unfold numericalRemainderConstant
  nlinarith only [hout, hdiff', hbase, hfirst, hsecond]

/-- Corollary 7: only the exact comparison state has an `H^γ` bound. -/
theorem numerical_state_estimate {τ γ M : ℝ} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (t : ℝ) {f w : Fourier}
    (hf : InSobolev 0 f) (hw : InSobolev γ w) (hmf : MeanZero f) (_hmw : MeanZero w)
    (hwM : hNorm γ w ≤ M) (hδ : hNorm 0 (f - w) ≤ 1) :
    hNorm 0 (remainder τ t f f f) ≤
      numericalRemainderConstant γ M * τ * (τ ^ γ + hNorm 0 (f - w)) := by
  rw [remainder_eq_interactionRemainder τ t hmf hmf hmf]
  exact interaction_numerical_state_estimate hτ hγ hγ₁ t hf hw hwM hδ

def translation (a : ℤ) : ℤ ≃ ℤ where
  toFun k := k - a
  invFun k := k + a
  left_inv k := by dsimp; omega
  right_inv k := by dsimp; omega

def translatedLp {𝕜 : Type*} [RCLike 𝕜] (a : ℤ) (g : lp (fun _ : ℤ => 𝕜) 2) :
    lp (fun _ : ℤ => 𝕜) 2 :=
  ⟨fun k => g (k - a), by
    apply memℓp_gen
    exact (translation a).summable_iff.mpr
      (g.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

theorem translatedLp_norm {𝕜 : Type*} [RCLike 𝕜] (a : ℤ) (g : lp (fun _ : ℤ => 𝕜) 2) :
    ‖translatedLp a g‖ = ‖g‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  exact (translation a).tsum_eq (fun k => ‖g k‖ ^ (2 : ℝ≥0∞).toReal)

def convolutionLp {𝕜 : Type*} [RCLike 𝕜] (f : ℤ → 𝕜) (g : lp (fun _ : ℤ => 𝕜) 2) :
    lp (fun _ : ℤ => 𝕜) 2 := ∑' a : ℤ, f a • translatedLp a g

theorem young_family_norm_summable {𝕜 : Type*} [RCLike 𝕜]
    (f : ℤ → 𝕜) (g : lp (fun _ : ℤ => 𝕜) 2) (hf : Summable (fun k => ‖f k‖)) :
    Summable (fun a : ℤ => ‖f a • translatedLp a g‖) := by
  simpa only [norm_smul, translatedLp_norm] using hf.mul_right ‖g‖

theorem convolutionLp_coeff {𝕜 : Type*} [RCLike 𝕜]
    (f : ℤ → 𝕜) (g : lp (fun _ : ℤ => 𝕜) 2) (hf : Summable (fun k => ‖f k‖)) (k : ℤ) :
    convolutionLp f g k = ∑' a : ℤ, f a * g (k - a) := by
  have hs := (young_family_norm_summable f g hf).of_norm
  have h := (lp.evalCLM 𝕜 (fun _ : ℤ => 𝕜) 2 k).map_tsum hs
  exact h.trans (tsum_congr (fun a => rfl))

/-- Discrete Young inequality `ℓ¹ * ℓ² → ℓ²`, used for the full products. -/
theorem convolutionLp_norm {𝕜 : Type*} [RCLike 𝕜]
    (f : ℤ → 𝕜) (g : lp (fun _ : ℤ => 𝕜) 2) (hf : Summable (fun k => ‖f k‖)) :
    ‖convolutionLp f g‖ ≤ (∑' k : ℤ, ‖f k‖) * ‖g‖ := by
  calc
    _ ≤ ∑' a : ℤ, ‖f a • translatedLp a g‖ :=
      norm_tsum_le_tsum_norm (young_family_norm_summable f g hf)
    _ = _ := by
      simp only [norm_smul, translatedLp_norm]
      exact hf.tsum_mul_right ‖g‖

theorem convolution_scalar_summable {𝕜 : Type*} [RCLike 𝕜]
    (f : ℤ → 𝕜) (g : lp (fun _ : ℤ => 𝕜) 2) (hf : Summable (fun k => ‖f k‖)) (k : ℤ) :
    Summable (fun a : ℤ => f a * g (k - a)) := by
  apply Summable.of_norm
  apply (hf.mul_right ‖g‖).of_nonneg_of_le (fun a => norm_nonneg _)
  intro a
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) g (k - a))
    (norm_nonneg _)

def inverseWeightOne (k : ℤ) : ℝ := (weight 1 k)⁻¹

theorem inverseWeightOne_sq (k : ℤ) : inverseWeightOne k ^ 2 = 1 / (1 + (k : ℝ) ^ 2) := by
  simp only [inverseWeightOne, inv_pow, weight_sq, Real.rpow_one, one_div]

theorem inverseWeightOne_square_summable : Summable (fun k : ℤ => inverseWeightOne k ^ 2) := by
  have htail : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hdelta : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq 0 1).summable
  apply (htail.add hdelta).of_nonneg_of_le (fun k => sq_nonneg _)
  intro k
  rw [inverseWeightOne_sq]
  by_cases hk : k = 0
  · subst k
    norm_num
  · simp only [if_neg hk, add_zero]
    apply one_div_le_one_div_of_le (sq_pos_of_ne_zero (intCast_ne_zero hk))
    linarith

def inverseWeightOneLp : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨inverseWeightOne, memℓp_gen (by
    have hn (k : ℤ) : ‖inverseWeightOne k‖ = inverseWeightOne k :=
      Real.norm_of_nonneg (inv_nonneg.mpr (weight_pos 1 k).le)
    simpa only [hn, ENNReal.toReal_ofNat, Real.rpow_two] using inverseWeightOne_square_summable)⟩

def h1EmbeddingConstant : ℝ := ‖inverseWeightOneLp‖

theorem h1EmbeddingConstant_ge_one : 1 ≤ h1EmbeddingConstant := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) inverseWeightOneLp 0
  have hz : ‖inverseWeightOneLp 0‖ = 1 := by
    change ‖(weight 1 0)⁻¹‖ = 1
    norm_num [weight]
  rw [hz] at h
  exact h

theorem h1_absolute_coefficients {f : Fourier} (hf : InSobolev 1 f) :
    Summable (fun k : ℤ => ‖f k‖) ∧ (∑' k : ℤ, ‖f k‖) ≤ h1EmbeddingConstant * hNorm 1 f := by
  let F : lp (fun _ : ℤ => ℝ) 2 := ⟨fun k => ‖weighted 1 f k‖, hf.norm⟩
  have h := lp.tsum_mul_le_mul_norm (p := 2) (q := 2)
    (by norm_num; exact Real.HolderConjugate.two_two) F inverseWeightOneLp
  have heq : (fun k : ℤ => ‖F k‖ * ‖inverseWeightOneLp k‖) = (fun k : ℤ => ‖f k‖) := by
    funext k
    change ‖‖weighted 1 f k‖‖ * ‖(weight 1 k)⁻¹‖ = ‖f k‖
    rw [norm_norm, norm_inv, Real.norm_of_nonneg (weight_pos 1 k).le, norm_weighted]
    field_simp [(weight_pos 1 k).ne']
  rw [heq] at h
  have hFnorm : ‖F‖ = hNorm 1 f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp [F, hNorm, Real.sqrt_eq_rpow]
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ ‖F‖ * ‖inverseWeightOneLp‖ := h.2
    _ = _ := by rw [hFnorm]; unfold h1EmbeddingConstant; ring

theorem convolution_tsum_comm {𝕜 : Type*} [RCLike 𝕜] (f g : ℤ → 𝕜) (k : ℤ) :
    (∑' a : ℤ, f a * g (k - a)) = ∑' a : ℤ, g a * f (k - a) := by
  calc
    _ = ∑' a : ℤ, f ((reflectAt k) a) * g (k - (reflectAt k) a) := ((reflectAt k).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro a
      change f (k - a) * g (k - (k - a)) = g a * f (k - a)
      rw [show k - (k - a) = a by omega]
      ring

theorem convolution_summable_comm {𝕜 : Type*} [RCLike 𝕜] (f g : ℤ → 𝕜) (k : ℤ)
    (h : Summable (fun a : ℤ => f a * g (k - a))) :
    Summable (fun a : ℤ => g a * f (k - a)) := by
  have heq : (fun a : ℤ => g a * f (k - a)) =
      (fun a : ℤ => f ((reflectAt k) a) * g (k - (reflectAt k) a)) := by
    funext a
    change g a * f (k - a) = f (k - a) * g (k - (k - a))
    rw [show k - (k - a) = a by omega]
    ring
  rw [heq]
  exact (reflectAt k).summable_iff.mpr h

def normWeightedLp (s : ℝ) (f : Fourier) (hf : InSobolev s f) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun k => ‖weighted s f k‖, hf.norm⟩

theorem norm_normWeightedLp (s : ℝ) (f : Fourier) (hf : InSobolev s f) :
    ‖normWeightedLp s f hf‖ = hNorm s f := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp [normWeightedLp, hNorm, Real.sqrt_eq_rpow]

theorem hNorm_le_lp_envelope {s : ℝ} {f : Fourier} (G : lp (fun _ : ℤ => ℝ) 2)
    (hG : ∀ k, ‖weighted s f k‖ ≤ G k) : InSobolev s f ∧ hNorm s f ≤ ‖G‖ := by
  have hf : InSobolev s f := Memℓp.mono G.property hG
  refine ⟨hf, ?_⟩
  rw [hNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  exact (hG k).trans (Real.le_norm_self _)

theorem weight_one_add (a b : ℤ) : weight 1 (a + b) ≤ weight 1 a + weight 1 b := by
  have ha : |(a : ℝ)| ≤ weight 1 a := by simpa only [Real.rpow_one] using abs_rpow_le_weight (by norm_num : (0 : ℝ) ≤ 1) a
  have hb : |(b : ℝ)| ≤ weight 1 b := by simpa only [Real.rpow_one] using abs_rpow_le_weight (by norm_num : (0 : ℝ) ≤ 1) b
  have hab : (a : ℝ) * (b : ℝ) ≤ weight 1 a * weight 1 b := by
    apply (le_abs_self ((a : ℝ) * (b : ℝ))).trans
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (weight_pos _ _).le
  have haSq := weight_sq 1 a
  have hbSq := weight_sq 1 b
  have hsumSq := weight_sq 1 (a + b)
  simp only [Real.rpow_one, Int.cast_add] at haSq hbSq hsumSq
  apply (sq_le_sq₀ (weight_pos 1 (a + b)).le (add_pos (weight_pos 1 a) (weight_pos 1 b)).le).mp
  nlinarith

theorem weighted_product_term_bound (f g : Fourier) (k a : ℤ) :
    weight 1 k * ‖f a‖ * ‖g (k - a)‖ ≤
      ‖weighted 1 f a‖ * ‖g (k - a)‖ + ‖f a‖ * ‖weighted 1 g (k - a)‖ := by
  have hweight : weight 1 k ≤ weight 1 a + weight 1 (k - a) := by
    simpa only [add_sub_cancel] using weight_one_add a (k - a)
  have h := mul_le_mul_of_nonneg_right hweight (mul_nonneg (norm_nonneg (f a)) (norm_nonneg (g (k - a))))
  rw [norm_weighted, norm_weighted]
  nlinarith only [h]

set_option maxHeartbeats 800000 in
/-- The elementary `H¹` algebra estimate from Section 4.2, for the full
integer convolution. All convergence is proved before the norm estimate. -/
theorem h1_product_bound {f g : Fourier} (hf : InSobolev 1 f) (hg : InSobolev 1 g) :
    InSobolev 1 (product f g) ∧
      hNorm 1 (product f g) ≤ 2 * h1EmbeddingConstant * hNorm 1 f * hNorm 1 g := by
  have hfabs := h1_absolute_coefficients hf
  have hgabs := h1_absolute_coefficients hg
  have hfnorm : Summable (fun k : ℤ => ‖(‖f k‖ : ℝ)‖) := by simpa only [norm_norm] using hfabs.1
  have hgnorm : Summable (fun k : ℤ => ‖(‖g k‖ : ℝ)‖) := by simpa only [norm_norm] using hgabs.1
  let F := normWeightedLp 1 f hf
  let G := normWeightedLp 1 g hg
  let A := convolutionLp (fun k : ℤ => ‖f k‖) G
  let B := convolutionLp (fun k : ℤ => ‖g k‖) F
  have hAcoeff (k : ℤ) : A k = ∑' a : ℤ, ‖f a‖ * ‖weighted 1 g (k - a)‖ :=
    convolutionLp_coeff _ G hfnorm k
  have hBcoeff (k : ℤ) : B k = ∑' a : ℤ, ‖weighted 1 f a‖ * ‖g (k - a)‖ := by
    calc
      _ = ∑' a : ℤ, ‖g a‖ * ‖weighted 1 f (k - a)‖ := convolutionLp_coeff _ F hgnorm k
      _ = _ := convolution_tsum_comm (fun a : ℤ => ‖g a‖) (fun a => ‖weighted 1 f a‖) k
  have hAsum (k : ℤ) : Summable (fun a : ℤ => ‖f a‖ * ‖weighted 1 g (k - a)‖) :=
    convolution_scalar_summable _ G hfnorm k
  have hBsum (k : ℤ) : Summable (fun a : ℤ => ‖weighted 1 f a‖ * ‖g (k - a)‖) :=
    convolution_summable_comm (fun a : ℤ => ‖g a‖) (fun a => ‖weighted 1 f a‖) k
      (convolution_scalar_summable (fun a : ℤ => ‖g a‖) F hgnorm k)
  have hbase (k : ℤ) : Summable (fun a : ℤ => ‖f a‖ * ‖g (k - a)‖) := by
    have hg₀ := hg.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have h := convolution_scalar_summable (fun a => ‖f a‖) (normWeightedLp 0 g hg₀) hfnorm k
    change Summable (fun a : ℤ => ‖f a‖ * ‖weighted 0 g (k - a)‖) at h
    simpa only [weighted_zero] using h
  have hbound (k : ℤ) : ‖weighted 1 (product f g) k‖ ≤ (A + B) k := by
    have hcomplex : Summable (fun a : ℤ => ‖f a * g (k - a)‖) := by simpa only [norm_mul] using hbase k
    have hcoef : ‖product f g k‖ ≤ ∑' a : ℤ, ‖f a‖ * ‖g (k - a)‖ := by
      simpa only [product, norm_mul] using norm_tsum_le_tsum_norm hcomplex
    have hleft : Summable (fun a : ℤ => weight 1 k * ‖f a‖ * ‖g (k - a)‖) := by
      simpa only [mul_assoc] using (hbase k).mul_left (weight 1 k)
    rw [norm_weighted]
    calc
      _ ≤ weight 1 k * ∑' a : ℤ, ‖f a‖ * ‖g (k - a)‖ :=
        mul_le_mul_of_nonneg_left hcoef (weight_pos _ _).le
      _ = ∑' a : ℤ, weight 1 k * ‖f a‖ * ‖g (k - a)‖ := by
        rw [← (hbase k).tsum_mul_left (weight 1 k)]
        apply tsum_congr
        intro a
        ring
      _ ≤ ∑' a : ℤ, (‖weighted 1 f a‖ * ‖g (k - a)‖ + ‖f a‖ * ‖weighted 1 g (k - a)‖) :=
        hleft.tsum_le_tsum (fun a => weighted_product_term_bound f g k a) ((hBsum k).add (hAsum k))
      _ = B k + A k := by rw [(hBsum k).tsum_add (hAsum k), ← hBcoeff k, ← hAcoeff k]
      _ = _ := by simp only [lp.coeFn_add, Pi.add_apply]; ring
  have hout := hNorm_le_lp_envelope (A + B) hbound
  have hFnorm : ‖F‖ = hNorm 1 f := norm_normWeightedLp 1 f hf
  have hGnorm : ‖G‖ = hNorm 1 g := norm_normWeightedLp 1 g hg
  have hA : ‖A‖ ≤ h1EmbeddingConstant * hNorm 1 f * hNorm 1 g := by
    calc
      _ ≤ (∑' k : ℤ, ‖f k‖) * ‖G‖ := by
        simpa only [norm_norm] using convolutionLp_norm (fun k => ‖f k‖) G hfnorm
      _ ≤ (h1EmbeddingConstant * hNorm 1 f) * ‖G‖ := mul_le_mul_of_nonneg_right hfabs.2 (norm_nonneg _)
      _ = _ := by rw [hGnorm]
  have hB : ‖B‖ ≤ h1EmbeddingConstant * hNorm 1 g * hNorm 1 f := by
    calc
      _ ≤ (∑' k : ℤ, ‖g k‖) * ‖F‖ := by
        simpa only [norm_norm] using convolutionLp_norm (fun k => ‖g k‖) F hgnorm
      _ ≤ (h1EmbeddingConstant * hNorm 1 g) * ‖F‖ := mul_le_mul_of_nonneg_right hgabs.2 (norm_nonneg _)
      _ = _ := by rw [hFnorm]
  refine ⟨hout.1, ?_⟩
  calc
    _ ≤ ‖A + B‖ := hout.2
    _ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith only [hA, hB]

theorem removeMean_inSobolev {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    InSobolev s (removeMean f) := by
  apply Memℓp.mono' hf
  intro k
  by_cases hk : k = 0
  · subst k
    simp only [KdV.weighted, removeMean_zero, mul_zero, norm_zero]
    positivity
  · simp only [KdV.weighted, removeMean, if_neg hk, le_refl]

theorem removeMean_hNorm_le {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    hNorm s (removeMean f) ≤ hNorm s f := by
  rw [hNorm_eq_lpNorm (removeMean_inSobolev hf), hNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖weighted s (removeMean f) k‖ ≤ ‖weighted s f k‖
  by_cases hk : k = 0
  · subst k
    simp only [KdV.weighted, removeMean_zero, mul_zero, norm_zero]
    positivity
  · simp only [KdV.weighted, removeMean, if_neg hk, le_refl]

theorem inverseDerivative₂_inSobolev_one {f : Fourier} (hf : InSobolev 0 f) :
    InSobolev 1 (inverseDerivative₂ f) :=
  inverseDerivative_inSobolev_one ((inverseDerivative_inSobolev_one hf).of_le (by norm_num))

theorem quadratic_inSobolev_one (τ : ℝ) {f : Fourier} (hf : InSobolev 0 f) :
    InSobolev 1 (quadratic τ f) := by
  have hd := inverseDerivative_inSobolev_one hf
  have hsd := airy_inSobolev hd τ
  have hfirst := removeMean_inSobolev (h1_product_bound hsd hsd).1
  have hsecond := airy_inSobolev (removeMean_inSobolev (h1_product_bound hd hd).1) τ
  exact (hfirst.smul (1 / 6 : ℂ)).sub (hsecond.smul (1 / 6 : ℂ))

theorem cubicBoundary_inSobolev_one (τ s : ℝ) {f : Fourier} (hf : InSobolev 0 f) :
    InSobolev 1 (cubicBoundary τ s f) := by
  have ha := airy_inSobolev (inverseDerivative_inSobolev_one hf) s
  have hp := (h1_product_bound (h1_product_bound ha ha).1 ha).1
  exact airy_inSobolev (inverseDerivative_inSobolev_one (hp.of_le (by norm_num))) (τ - s)

theorem lastBoundary_inSobolev_one (τ s : ℝ) {f : Fourier} (hf : InSobolev 0 f) :
    InSobolev 1 (lastBoundary τ s f) := by
  have hF := quadratic_inSobolev_one τ hf
  have ha := airy_inSobolev (inverseDerivative₂_inSobolev_one (hF.of_le (by norm_num))) (s - τ)
  have hb := airy_inSobolev (inverseDerivative_inSobolev_one hf) s
  have hp := (h1_product_bound ha hb).1
  exact airy_inSobolev (inverseDerivative₂_inSobolev_one (hp.of_le (by norm_num))) (τ - s)

theorem cubicCorrection_inSobolev_one (τ : ℝ) {f : Fourier} (hf : InSobolev 0 f) :
    InSobolev 1 (cubicCorrection τ f) := by
  have hF := quadratic_inSobolev_one τ hf
  have hfirst := (removeMean_inSobolev (h1_product_bound
    (airy_inSobolev (inverseDerivative_inSobolev_one hf) τ)
    (inverseDerivative_inSobolev_one (hF.of_le (by norm_num)))).1).smul (1 / 3 : ℂ)
  have hsecond := (airy_inSobolev (inverseDerivative_inSobolev_one hf) τ).smul
    ((τ : ℂ) / 9 * mean (product f f))
  have hthird := ((cubicBoundary_inSobolev_one τ τ hf).sub
    (cubicBoundary_inSobolev_one τ 0 hf)).smul (1 / 54 : ℂ)
  have hfourth := ((lastBoundary_inSobolev_one τ τ hf).sub
    (lastBoundary_inSobolev_one τ 0 hf)).smul (1 / (27 * (τ : ℂ)))
  exact ((hfirst.add hsecond).sub hthird).sub hfourth

theorem step_inSobolev {γ : ℝ} (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (τ : ℝ) {f : Fourier} (hf : InSobolev γ f) : InSobolev γ (step τ f) := by
  have hf₀ := hf.of_le hγ
  exact ((airy_inSobolev hf τ).add ((quadratic_inSobolev_one τ hf₀).of_le hγ₁)).add
    ((cubicCorrection_inSobolev_one τ hf₀).of_le hγ₁)

theorem numerical_inSobolev {γ : ℝ} (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (τ : ℝ) {f : Fourier} (hf : InSobolev γ f) (n : ℕ) : InSobolev γ (numerical τ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact step_inSobolev hγ hγ₁ τ ih

theorem product_comm (f g : Fourier) : product f g = product g f := by
  funext k
  exact convolution_tsum_comm f g k

theorem product_add_left {f g h : Fourier} (hf : InSobolev 0 f)
    (hg : InSobolev 0 g) (hh : InSobolev 0 h) : product (f + g) h = product f h + product g h := by
  funext k
  unfold product
  calc
    _ = ∑' a : ℤ, (f a * h (k - a) + g a * h (k - a)) := by
      apply tsum_congr
      intro a
      dsimp only [Pi.add_apply]
      ring
    _ = _ := (product_summable hf hh k).tsum_add (product_summable hg hh k)

theorem product_add_right {f g h : Fourier} (hf : InSobolev 0 f)
    (hg : InSobolev 0 g) (hh : InSobolev 0 h) : product f (g + h) = product f g + product f h := by
  rw [product_comm f (g + h), product_add_left hg hh hf, product_comm g f, product_comm h f]

theorem product_smul_left (z : ℂ) (f g : Fourier) : product (z • f) g = z • product f g := by
  funext k
  unfold product
  change (∑' a : ℤ, (z * f a) * g (k - a)) = z * ∑' a : ℤ, f a * g (k - a)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  ring

theorem product_smul_right (z : ℂ) (f g : Fourier) : product f (z • g) = z • product f g := by
  rw [product_comm f (z • g), product_smul_left, product_comm g f]

theorem airy_add (t : ℝ) (f g : Fourier) : airy t (f + g) = airy t f + airy t g := by
  funext k
  simp only [airy, Pi.add_apply, mul_add]

theorem airy_smul (t : ℝ) (z : ℂ) (f : Fourier) : airy t (z • f) = z • airy t f := by
  funext k
  simp only [airy, Pi.smul_apply, smul_eq_mul]
  ring

theorem inverseDerivative_add (f g : Fourier) :
    inverseDerivative (f + g) = inverseDerivative f + inverseDerivative g := by
  funext k
  by_cases hk : k = 0 <;> simp [inverseDerivative, hk, mul_add]

theorem inverseDerivative_smul (z : ℂ) (f : Fourier) :
    inverseDerivative (z • f) = z • inverseDerivative f := by
  funext k
  by_cases hk : k = 0
  · simp [inverseDerivative, hk]
  · simp only [inverseDerivative, if_neg hk, Pi.smul_apply, smul_eq_mul]
    ring

theorem removeMean_add (f g : Fourier) : removeMean (f + g) = removeMean f + removeMean g := by
  funext k
  by_cases hk : k = 0 <;> simp [removeMean, hk]

theorem removeMean_smul (z : ℂ) (f : Fourier) : removeMean (z • f) = z • removeMean f := by
  funext k
  by_cases hk : k = 0 <;> simp [removeMean, hk]

def inclusionLinear (s r : ℝ) (hsr : s ≤ r) : Sobolev r →ₗ[ℂ] Sobolev s where
  toFun f := ⟨f.val, f.property.of_le hsr⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 0 in
theorem inclusionLinear_bound (s r : ℝ) (hsr : s ≤ r) (f : Sobolev r) :
    ‖inclusionLinear s r hsr f‖ ≤ ‖f‖ := by
  calc
    _ = hNorm s f.val := sobolev_norm (inclusionLinear s r hsr f)
    _ ≤ hNorm r f.val := hNorm_mono f.property hsr
    _ = _ := (sobolev_norm f).symm

def inclusionMap (s r : ℝ) (hsr : s ≤ r) : Sobolev r →L[ℂ] Sobolev s :=
  (inclusionLinear s r hsr).mkContinuous 1 (fun f => by
    simpa only [one_mul] using inclusionLinear_bound s r hsr f)


end KdV
