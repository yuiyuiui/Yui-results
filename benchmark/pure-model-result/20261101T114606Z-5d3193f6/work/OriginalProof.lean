import Mathlib

/-!
Formal development of Theorem 1 of the supplied paper.
The exported `theorem_1` proves the uniform error bound conditional on the cited
external parameters. Smooth approximation, existence and the distributional
Sobolev representation are proved internally.
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

/-- Weighted square-summable Fourier coefficients, with the Sobolev index kept
as a structure parameter. This avoids any inherited pointwise topology. -/
structure Sobolev (s : ℝ) where
  val : Fourier
  property : InSobolev s val

@[ext] theorem Sobolev.ext {s : ℝ} {f g : Sobolev s} (h : f.val = g.val) : f = g := by
  cases f
  cases g
  cases h
  rfl

def sobolevUnderlying (s : ℝ) : Sobolev s ≃ ↥(sobolevSubmodule s) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (s : ℝ) : AddCommGroup (Sobolev s) := (sobolevUnderlying s).addCommGroup

instance (s : ℝ) : Module ℂ (Sobolev s) := (sobolevUnderlying s).module ℂ

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
    apply Sobolev.ext
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
Its distributional Sobolev realization is proved below. -/
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
    apply Sobolev.ext
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

theorem inclusionLinear_bound (s r : ℝ) (hsr : s ≤ r) (f : Sobolev r) :
    ‖inclusionLinear s r hsr f‖ ≤ ‖f‖ := by
  calc
    _ = hNorm s f.val := sobolev_norm (inclusionLinear s r hsr f)
    _ ≤ hNorm r f.val := hNorm_mono f.property hsr
    _ = _ := (sobolev_norm f).symm

def inclusionMap (s r : ℝ) (hsr : s ≤ r) : Sobolev r →L[ℂ] Sobolev s :=
  (inclusionLinear s r hsr).mkContinuous 1 (fun f => by
    simpa only [one_mul] using inclusionLinear_bound s r hsr f)

def airyLinear (s t : ℝ) : Sobolev s →ₗ[ℂ] Sobolev s where
  toFun f := ⟨airy t f.val, airy_inSobolev f.property t⟩
  map_add' f g := by apply Sobolev.ext; exact airy_add t f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact airy_smul t z f.val

def airyMap (s t : ℝ) : Sobolev s →L[ℂ] Sobolev s :=
  (airyLinear s t).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (airy t f.val) ≤ hNorm s f.val
    exact (airy_hNorm s t f.val).le)

def inverseDerivativeLinear : Sobolev 0 →ₗ[ℂ] Sobolev 1 where
  toFun f := ⟨inverseDerivative f.val, inverseDerivative_inSobolev_one f.property⟩
  map_add' f g := by apply Sobolev.ext; exact inverseDerivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact inverseDerivative_smul z f.val

def inverseDerivativeMap : Sobolev 0 →L[ℂ] Sobolev 1 :=
  inverseDerivativeLinear.mkContinuous (Real.sqrt 2) (fun f => by
    simp only [sobolev_norm]
    change hNorm 1 (inverseDerivative f.val) ≤ Real.sqrt 2 * hNorm 0 f.val
    exact inverseDerivative_hNorm_one f.property)

def removeMeanLinear (s : ℝ) : Sobolev s →ₗ[ℂ] Sobolev s where
  toFun f := ⟨removeMean f.val, removeMean_inSobolev f.property⟩
  map_add' f g := by apply Sobolev.ext; exact removeMean_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact removeMean_smul z f.val

def removeMeanMap (s : ℝ) : Sobolev s →L[ℂ] Sobolev s :=
  (removeMeanLinear s).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (removeMean f.val) ≤ hNorm s f.val
    exact removeMean_hNorm_le f.property)

def productBilinear : Sobolev 1 →ₗ[ℂ] Sobolev 1 →ₗ[ℂ] Sobolev 1 where
  toFun f := {
    toFun g := ⟨product f.val g.val, (h1_product_bound f.property g.property).1⟩
    map_add' g h := by
      apply Sobolev.ext
      exact product_add_right (f.property.of_le (by norm_num))
        (g.property.of_le (by norm_num)) (h.property.of_le (by norm_num))
    map_smul' z g := by apply Sobolev.ext; exact product_smul_right z f.val g.val }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Sobolev.ext
    exact product_add_left (f.property.of_le (by norm_num))
      (g.property.of_le (by norm_num)) (h.property.of_le (by norm_num))
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply Sobolev.ext
    exact product_smul_left z f.val g.val

def productMap : Sobolev 1 →L[ℂ] Sobolev 1 →L[ℂ] Sobolev 1 :=
  productBilinear.mkContinuous₂ (2 * h1EmbeddingConstant) (fun f g => by
    simp only [sobolev_norm]
    change hNorm 1 (product f.val g.val) ≤ (2 * h1EmbeddingConstant) * hNorm 1 f.val * hNorm 1 g.val
    exact (h1_product_bound f.property g.property).2)

def meanProductBilinear : Sobolev 0 →ₗ[ℂ] Sobolev 0 →ₗ[ℂ] ℂ where
  toFun f := {
    toFun g := mean (product f.val g.val)
    map_add' g h := by exact congrArg (fun u : Fourier => u 0) (product_add_right f.property g.property h.property)
    map_smul' z g := by exact congrArg (fun u : Fourier => u 0) (product_smul_right z f.val g.val) }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    exact congrArg (fun u : Fourier => u 0) (product_add_left f.property g.property h.property)
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    exact congrArg (fun u : Fourier => u 0) (product_smul_left z f.val g.val)

def meanProductMap : Sobolev 0 →L[ℂ] Sobolev 0 →L[ℂ] ℂ :=
  meanProductBilinear.mkContinuous₂ 1 (fun f g => by
    simp only [sobolev_norm, one_mul]
    exact product_coeff_bound f.property g.property 0)

def lowerOne : Sobolev 1 →L[ℂ] Sobolev 0 := inclusionMap 0 1 (by norm_num)

def inverseDerivativeTwiceMap : Sobolev 0 →L[ℂ] Sobolev 1 :=
  inverseDerivativeMap.comp (lowerOne.comp inverseDerivativeMap)

def quadraticBundled (τ : ℝ) (f : Sobolev 0) : Sobolev 1 :=
  let d := inverseDerivativeMap f
  let sd := airyMap 1 τ d
  (1 / 6 : ℂ) • removeMeanMap 1 (productMap sd sd) -
    (1 / 6 : ℂ) • airyMap 1 τ (removeMeanMap 1 (productMap d d))

theorem quadraticBundled_val (τ : ℝ) (f : Sobolev 0) :
    (quadraticBundled τ f).val = quadratic τ f.val := rfl

@[fun_prop] theorem continuous_quadraticBundled (τ : ℝ) : Continuous (quadraticBundled τ) := by
  unfold quadraticBundled
  fun_prop

def cubicBoundaryBundled (τ s : ℝ) (f : Sobolev 0) : Sobolev 1 :=
  let a := airyMap 1 s (inverseDerivativeMap f)
  airyMap 1 (τ - s) (inverseDerivativeMap (lowerOne (productMap (productMap a a) a)))

theorem cubicBoundaryBundled_val (τ s : ℝ) (f : Sobolev 0) :
    (cubicBoundaryBundled τ s f).val = cubicBoundary τ s f.val := rfl

@[fun_prop] theorem continuous_cubicBoundaryBundled (τ s : ℝ) : Continuous (cubicBoundaryBundled τ s) := by
  unfold cubicBoundaryBundled
  fun_prop

def lastBoundaryBundled (τ s : ℝ) (f : Sobolev 0) : Sobolev 1 :=
  airyMap 1 (τ - s) (inverseDerivativeTwiceMap (lowerOne
    (productMap (airyMap 1 (s - τ) (inverseDerivativeTwiceMap (lowerOne (quadraticBundled τ f))))
      (airyMap 1 s (inverseDerivativeMap f)))))

theorem lastBoundaryBundled_val (τ s : ℝ) (f : Sobolev 0) :
    (lastBoundaryBundled τ s f).val = lastBoundary τ s f.val := rfl

@[fun_prop] theorem continuous_lastBoundaryBundled (τ s : ℝ) : Continuous (lastBoundaryBundled τ s) := by
  unfold lastBoundaryBundled
  fun_prop

def cubicCorrectionBundled (τ : ℝ) (f : Sobolev 0) : Sobolev 1 :=
  (1 / 3 : ℂ) • removeMeanMap 1
    (productMap (airyMap 1 τ (inverseDerivativeMap f))
      (inverseDerivativeMap (lowerOne (quadraticBundled τ f)))) +
  ((τ : ℂ) / 9 * meanProductMap f f) • airyMap 1 τ (inverseDerivativeMap f) -
  (1 / 54 : ℂ) • (cubicBoundaryBundled τ τ f - cubicBoundaryBundled τ 0 f) -
  (1 / (27 * (τ : ℂ))) • (lastBoundaryBundled τ τ f - lastBoundaryBundled τ 0 f)

theorem cubicCorrectionBundled_val (τ : ℝ) (f : Sobolev 0) :
    (cubicCorrectionBundled τ f).val = cubicCorrection τ f.val := rfl

@[fun_prop] theorem continuous_cubicCorrectionBundled (τ : ℝ) : Continuous (cubicCorrectionBundled τ) := by
  unfold cubicCorrectionBundled
  fun_prop

/-- A continuous map on the full `L²` completion whose coefficients are exactly
the displayed fixed update (2), including both endpoint differences. -/
def stepBundled (τ : ℝ) (f : Sobolev 0) : Sobolev 0 :=
  airyMap 0 τ f + lowerOne (quadraticBundled τ f) + lowerOne (cubicCorrectionBundled τ f)

theorem stepBundled_val (τ : ℝ) (f : Sobolev 0) : (stepBundled τ f).val = step τ f.val := rfl

@[fun_prop] theorem continuous_stepBundled (τ : ℝ) : Continuous (stepBundled τ) := by
  unfold stepBundled
  fun_prop

def numericalBundled (τ : ℝ) : ℕ → Sobolev 0 → Sobolev 0
  | 0 => id
  | n + 1 => fun f => stepBundled τ (numericalBundled τ n f)

theorem numericalBundled_val (τ : ℝ) (n : ℕ) (f : Sobolev 0) :
    (numericalBundled τ n f).val = numerical τ f.val n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (stepBundled τ (numericalBundled τ n f)).val = _
    rw [stepBundled_val, ih]
    rfl

@[fun_prop] theorem continuous_numericalBundled (τ : ℝ) (n : ℕ) : Continuous (numericalBundled τ n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact (continuous_stepBundled τ).comp ih



theorem RealValued.add {f g : Fourier} (hf : RealValued f) (hg : RealValued g) :
    RealValued (f + g) := by
  intro k
  simp only [Pi.add_apply, hf k, hg k, map_add]

theorem RealValued.sub {f g : Fourier} (hf : RealValued f) (hg : RealValued g) :
    RealValued (f - g) := by
  intro k
  simp only [Pi.sub_apply, hf k, hg k, map_sub]

theorem RealValued.real_smul {f : Fourier} (hf : RealValued f) (r : ℝ) :
    RealValued ((r : ℂ) • f) := by
  intro k
  simp [Pi.smul_apply, hf k]

theorem RealValued.smul {f : Fourier} (hf : RealValued f) {z : ℂ} (hz : conj z = z) :
    RealValued (z • f) := by
  intro k
  simp [Pi.smul_apply, hf k, hz]

theorem RealValued.product {f g : Fourier} (hf : RealValued f) (hg : RealValued g) :
    RealValued (KdV.product f g) := by
  intro k
  change (∑' a : ℤ, f a * g (-k - a)) = conj (∑' a : ℤ, f a * g (k - a))
  rw [RCLike.conj_tsum]
  calc
    (∑' a : ℤ, f a * g (-k - a)) = ∑' a : ℤ, f (-a) * g (-k - -a) :=
      (Equiv.neg ℤ).tsum_eq (fun a : ℤ => f a * g (-k - a)) |>.symm
    _ = ∑' a : ℤ, conj (f a * g (k - a)) := by
      apply tsum_congr
      intro a
      rw [show -k - -a = -(k - a) by ring, hf a, hg (k - a), map_mul]

theorem RealValued.airy {f : Fourier} (hf : RealValued f) (t : ℝ) :
    RealValued (KdV.airy t f) := by
  intro k
  simp only [KdV.airy, hf k, map_mul, ← Complex.exp_conj, map_pow, map_intCast,
    Complex.conj_I, Complex.conj_ofReal, Int.cast_neg]
  congr 2
  ring

theorem RealValued.inverseDerivative {f : Fourier} (hf : RealValued f) :
    RealValued (KdV.inverseDerivative f) := by
  intro k
  by_cases hk : k = 0
  · simp [hk, KdV.inverseDerivative]
  · simp [KdV.inverseDerivative, hk, hf k, map_mul, map_inv₀]

theorem RealValued.removeMean {f : Fourier} (hf : RealValued f) :
    RealValued (KdV.removeMean f) := by
  intro k
  by_cases hk : k = 0 <;> simp [KdV.removeMean, hk, hf k]

theorem RealValued.mean {f : Fourier} (hf : RealValued f) : conj (KdV.mean f) = KdV.mean f := by
  exact (hf 0).symm

theorem RealValued.quadratic {f : Fourier} (hf : RealValued f) (τ : ℝ) :
    RealValued (KdV.quadratic τ f) := by
  unfold KdV.quadratic
  exact ((hf.inverseDerivative.airy τ).product (hf.inverseDerivative.airy τ)).removeMean.smul
    (by simp [map_ofNat]) |>.sub ((hf.inverseDerivative.product hf.inverseDerivative).removeMean.airy τ |>.smul
      (by simp [map_ofNat]))

theorem RealValued.cubicBoundary {f : Fourier} (hf : RealValued f) (τ s : ℝ) :
    RealValued (KdV.cubicBoundary τ s f) := by
  exact (((hf.inverseDerivative.airy s).product (hf.inverseDerivative.airy s)).product
    (hf.inverseDerivative.airy s)).inverseDerivative.airy (τ - s)

theorem RealValued.lastBoundary {f : Fourier} (hf : RealValued f) (τ s : ℝ) :
    RealValued (KdV.lastBoundary τ s f) := by
  exact (((hf.quadratic τ).inverseDerivative.inverseDerivative.airy (s - τ)).product
    (hf.inverseDerivative.airy s)).inverseDerivative.inverseDerivative.airy (τ - s)

theorem RealValued.cubicCorrection {f : Fourier} (hf : RealValued f) (τ : ℝ) :
    RealValued (KdV.cubicCorrection τ f) := by
  unfold KdV.cubicCorrection
  apply RealValued.sub
  · apply RealValued.sub
    · apply RealValued.add
      · exact ((hf.inverseDerivative.airy τ).product (hf.quadratic τ).inverseDerivative).removeMean.smul
          (by simp [map_ofNat])
      · exact (hf.inverseDerivative.airy τ).smul (by simp [map_ofNat, hf.product hf |>.mean])
    · exact ((hf.cubicBoundary τ τ).sub (hf.cubicBoundary τ 0)).smul (by simp [map_ofNat])
  · exact ((hf.lastBoundary τ τ).sub (hf.lastBoundary τ 0)).smul (by simp [map_ofNat])

theorem RealValued.step {f : Fourier} (hf : RealValued f) (τ : ℝ) : RealValued (KdV.step τ f) :=
  ((hf.airy τ).add (hf.quadratic τ)).add (hf.cubicCorrection τ)

theorem RealValued.numerical {f : Fourier} (hf : RealValued f) (τ : ℝ) (n : ℕ) :
    RealValued (KdV.numerical τ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.step τ




theorem airy_add_time (t s : ℝ) (f : Fourier) : airy (t + s) f = airy t (airy s f) := by
  funext k
  simp only [airy, Complex.ofReal_add]
  rw [show Complex.I * ((t : ℂ) + s) * (k : ℂ) ^ 3 =
    Complex.I * (t : ℂ) * (k : ℂ) ^ 3 + Complex.I * (s : ℂ) * (k : ℂ) ^ 3 by ring,
    Complex.exp_add, mul_assoc]

theorem airy_neg_inverse (t : ℝ) (f : Fourier) : airy (-t) (airy t f) = f := by
  rw [← airy_add_time, neg_add_cancel, airy_zero]

theorem airy_sub (t : ℝ) (f g : Fourier) : airy t (f - g) = airy t f - airy t g := by
  funext k
  simp [airy, mul_sub]

theorem airy_difference_weight_bound (s t t₀ : ℝ) (f : Fourier) (k : ℤ) :
    ‖weighted s (airy t f - airy t₀ f) k‖ ^ 2 ≤ 4 * ‖weighted s f k‖ ^ 2 := by
  have h : ‖weighted s (airy t f - airy t₀ f) k‖ ≤ 2 * ‖weighted s f k‖ := by
    rw [weighted_sub, Pi.sub_apply]
    exact (norm_sub_le _ _).trans (by rw [norm_weighted_airy, norm_weighted_airy]; linarith)
  nlinarith [norm_nonneg (weighted s f k), norm_nonneg (weighted s (airy t f - airy t₀ f) k)]

/-- Strong continuity in the full weighted completion, for every real index. -/
theorem continuous_airy_fixed (s : ℝ) (f : Sobolev s) :
    Continuous (fun t : ℝ => airyMap s t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  change Filter.Tendsto (fun t : ℝ => airyMap s t f) (nhds t₀) (nhds (airyMap s t₀ f))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Summable (fun k : ℤ => 4 * ‖weighted s f.val k‖ ^ 2) := by
    have h : Summable (fun k : ℤ => ‖weighted s f.val k‖ ^ 2) := by
      simpa using f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact h.mul_left 4
  have hp : ∀ k : ℤ,
      Filter.Tendsto (fun t : ℝ => ‖weighted s (airy t f.val - airy t₀ f.val) k‖ ^ 2)
        (nhds t₀) (nhds (0 : ℝ)) := by
    intro k
    have hc : Continuous (fun t : ℝ => ‖weighted s (airy t f.val - airy t₀ f.val) k‖ ^ 2) := by
      unfold weighted airy
      simp only [Pi.sub_apply]
      fun_prop
    simpa [weighted] using (hc.continuousAt (x := t₀)).tendsto
  have hsum := tendsto_tsum_of_dominated_convergence hs hp
    (Filter.Eventually.of_forall fun t k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact airy_difference_weight_bound s t t₀ f.val k)
  have hn : (fun t : ℝ => ‖airyMap s t f - airyMap s t₀ f‖) =
      (fun t : ℝ => hNorm s (airy t f.val - airy t₀ f.val)) := by
    funext t
    exact sobolev_norm _
  rw [hn]
  simpa only [hNorm, tsum_zero, Real.sqrt_zero] using hsum.sqrt




theorem airyMap_norm (s t : ℝ) (f : Sobolev s) : ‖airyMap s t f‖ = ‖f‖ := by
  rw [sobolev_norm, sobolev_norm]
  exact airy_hNorm s t f.val

set_option maxHeartbeats 800000 in
/-- Joint continuity of the unitary group action. -/
theorem continuous_airy_action (s : ℝ) :
    Continuous (fun p : ℝ × Sobolev s => airyMap s p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t₀, f₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h₁ : Filter.Tendsto (fun p : ℝ × Sobolev s => ‖p.2 - f₀‖)
      (nhds (t₀, f₀)) (nhds 0) := by
    simpa using ((continuous_snd.sub (continuous_const (y := f₀))).norm.continuousAt
      (x := (t₀, f₀))).tendsto
  have h₂ : Filter.Tendsto (fun p : ℝ × Sobolev s => ‖airyMap s p.1 f₀ - airyMap s t₀ f₀‖)
      (nhds (t₀, f₀)) (nhds 0) := by
    simpa using (((continuous_airy_fixed s f₀).comp continuous_fst).sub
      (continuous_const (y := airyMap s t₀ f₀))).norm.continuousAt (x := (t₀, f₀)) |>.tendsto
  have hb (p : ℝ × Sobolev s) : ‖airyMap s p.1 p.2 - airyMap s t₀ f₀‖ ≤
      ‖p.2 - f₀‖ + ‖airyMap s p.1 f₀ - airyMap s t₀ f₀‖ := by
    calc
      _ ≤ ‖airyMap s p.1 p.2 - airyMap s p.1 f₀‖ + ‖airyMap s p.1 f₀ - airyMap s t₀ f₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub (airyMap s p.1 p.2)
          (airyMap s p.1 f₀) (airyMap s t₀ f₀)
      _ = _ := by rw [← map_sub, airyMap_norm]
  exact squeeze_zero (fun p : ℝ × Sobolev s =>
    norm_nonneg (airyMap s p.1 p.2 - airyMap s t₀ f₀)) hb (by simpa using h₁.add h₂)

theorem weight_add (s r : ℝ) (k : ℤ) : weight (s + r) k = weight s k * weight r k := by
  unfold weight
  rw [add_div, Real.rpow_add (by positivity : 0 < 1 + (k : ℝ) ^ 2)]

theorem weight_one_ge_abs (k : ℤ) : |(k : ℝ)| ≤ weight 1 k := by
  have h := weight_sq 1 k
  rw [Real.rpow_one] at h
  nlinarith [weight_pos 1 k, sq_abs (k : ℝ), abs_nonneg (k : ℝ)]

/-- The distributional spatial derivative on Fourier coefficients. -/
def derivative (f : Fourier) : Fourier := fun k => Complex.I * (k : ℂ) * f k

theorem derivative_weighted_bound (s : ℝ) (f : Fourier) (k : ℤ) :
    ‖weighted s (derivative f) k‖ ≤ ‖weighted (s + 1) f k‖ := by
  rw [norm_weighted, norm_weighted, weight_add]
  simp only [derivative, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (weight_one_ge_abs k) (weight_pos s k).le) (norm_nonneg (f k))

theorem derivative_inSobolev {s : ℝ} {f : Fourier} (hf : InSobolev (s + 1) f) :
    InSobolev s (derivative f) := by
  apply Memℓp.mono' hf
  exact derivative_weighted_bound s f

theorem derivative_hNorm {s : ℝ} {f : Fourier} (hf : InSobolev (s + 1) f) :
    hNorm s (derivative f) ≤ hNorm (s + 1) f := by
  simpa using hNorm_le_of_weighted_bound hf (by norm_num : (0 : ℝ) ≤ 1)
    (fun k => by simpa using derivative_weighted_bound s f k)

/-- Every inverse Sobolev weight of order strictly larger than one half is in ℓ². -/
theorem negative_weight_square_summable {q : ℝ} (hq : 1 / 2 < q) :
    Summable (fun k : ℤ => weight (-q) k ^ 2) := by
  have htail := Real.summable_abs_int_rpow (b := 2 * q) (by linarith)
  have hdelta : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq 0 1).summable
  apply (htail.add hdelta).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro k
  rw [weight_sq]
  by_cases hk : k = 0
  · subst k
    norm_num
    positivity
  · simp only [if_neg hk, add_zero]
    have ha : 0 < |(k : ℝ)| := abs_pos.mpr (intCast_ne_zero hk)
    calc
      _ ≤ (|(k : ℝ)| ^ 2) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha) (by rw [sq_abs]; linarith) (by linarith)
      _ = |(k : ℝ)| ^ (-(2 * q)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
        congr 1
        ring

def negativeWeightLp (q : ℝ) (hq : 1 / 2 < q) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun k => (weight (-q) k : ℂ), memℓp_gen (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos (-q) _),
      ENNReal.toReal_ofNat, Real.rpow_two]
      using negative_weight_square_summable hq)⟩

def negativeProductConstant (q : ℝ) (hq : 1 / 2 < q) : ℝ := ‖negativeWeightLp q hq‖

theorem negative_product_bound {q : ℝ} (hq : 1 / 2 < q) {f g : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) :
    InSobolev (-q) (product f g) ∧
      hNorm (-q) (product f g) ≤ negativeProductConstant q hq * hNorm 0 f * hNorm 0 g := by
  have hb (k : ℤ) : ‖weighted (-q) (product f g) k‖ ≤
      (hNorm 0 f * hNorm 0 g) * ‖negativeWeightLp q hq k‖ := by
    rw [norm_weighted]
    have hp := product_coeff_bound hf hg k
    change weight (-q) k * ‖product f g k‖ ≤
      (hNorm 0 f * hNorm 0 g) * ‖(weight (-q) k : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (weight_pos (-q) k).le]
    nlinarith [weight_pos (-q) k]
  have hh : Memℓp (weighted (-q) (product f g)) 2 := by
    apply Memℓp.mono' ((negativeWeightLp q hq).property.const_smul
      ((hNorm 0 f * hNorm 0 g : ℝ) : ℂ))
    intro k
    simpa only [Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g))] using hb k
  refine ⟨hh, ?_⟩
  rw [hNorm_eq_lpNorm hh]
  calc
    _ ≤ ‖((hNorm 0 f * hNorm 0 g : ℝ) : ℂ) • negativeWeightLp q hq‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro k
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g))] using hb k
    _ = _ := by
      simp only [norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g)), negativeProductConstant]
      ring




/-- The fixed negative Sobolev exponent in the continuous estimates. -/
def pStar : ℝ := 23 / 14

/-- The twisted KdV bilinear vector field, retaining every Fourier mode. -/
def B (t : ℝ) (f g : Fourier) : Fourier :=
  airy (-t) (derivative (product (airy t f) (airy t g)))

/-- The symmetric quadratic normal-form boundary operator. -/
def J (t : ℝ) (f g : Fourier) : Fourier :=
  airy (-t) (removeMean
    (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))))

/-- The trilinear time integral appearing in the cited Proposition 3.4.
Its coefficients are integrals; membership and bounds require proved hypotheses. -/
def CIntegral (a b : ℝ) (f g h : ℝ → Fourier) : Fourier := fun k =>
  ∫ t : ℝ in a..b,
    airy (-t) (removeMean (product (removeMean (product (airy t (f t)) (airy t (g t))))
      (airy t (inverseDerivative (h t))))) k

/-- The bilinear stage in its exact endpoint form. -/
def bilinearStage (a t : ℝ) (f g : Fourier) : Fourier :=
  (1 / 6 : ℂ) • (J t f g - J a f g)

theorem B_meanZero (t : ℝ) (f g : Fourier) : MeanZero (B t f g) := by
  simp [MeanZero, B, derivative]

theorem J_meanZero (t : ℝ) (f g : Fourier) : MeanZero (J t f g) := by
  simp [MeanZero, J]

theorem B_comm (t : ℝ) (f g : Fourier) : B t f g = B t g f := by
  rw [B, product_comm]
  rfl

theorem J_comm (t : ℝ) (f g : Fourier) : J t f g = J t g f := by
  rw [J, product_comm]
  rfl

theorem B_negative_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : InSobolev (-pStar) (B t f g) ∧
      hNorm (-pStar) (B t f g) ≤
        negativeProductConstant (9 / 14) (by norm_num) * hNorm 0 f * hNorm 0 g := by
  have hp := negative_product_bound (q := 9 / 14) (by norm_num) (airy_inSobolev hf t)
    (airy_inSobolev hg t)
  have hd : InSobolev (-pStar + 1) (product (airy t f) (airy t g)) := by
    convert hp.1 using 1; norm_num [pStar]
  refine ⟨airy_inSobolev (derivative_inSobolev hd) (-t), ?_⟩
  rw [B, airy_hNorm]
  calc
    _ ≤ hNorm (-pStar + 1) (product (airy t f) (airy t g)) := derivative_hNorm hd
    _ = hNorm (-(9 / 14)) (product (airy t f) (airy t g)) := by norm_num [pStar]
    _ ≤ _ := by simpa only [airy_hNorm] using hp.2

theorem J_h1_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : InSobolev 1 (J t f g) ∧
      hNorm 1 (J t f g) ≤ 4 * h1EmbeddingConstant * hNorm 0 f * hNorm 0 g := by
  have hp := h1_product_bound (airy_inSobolev (inverseDerivative_inSobolev_one hf) t)
    (airy_inSobolev (inverseDerivative_inSobolev_one hg) t)
  refine ⟨airy_inSobolev (removeMean_inSobolev hp.1) (-t), ?_⟩
  rw [J, airy_hNorm]
  calc
    _ ≤ hNorm 1 (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))) :=
      removeMean_hNorm_le hp.1
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 (inverseDerivative f) * hNorm 1 (inverseDerivative g) := by
      simpa only [airy_hNorm] using hp.2
    _ ≤ (2 * h1EmbeddingConstant) * (Real.sqrt 2 * hNorm 0 f) * (Real.sqrt 2 * hNorm 0 g) := by
      have hC : 0 ≤ h1EmbeddingConstant := le_trans zero_le_one h1EmbeddingConstant_ge_one
      have hF := hNorm_nonneg 0 f
      have hG := hNorm_nonneg 0 g
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (inverseDerivative_hNorm_one hf) (by positivity))
        (inverseDerivative_hNorm_one hg) (hNorm_nonneg 1 _) (by positivity)
    _ = (2 * h1EmbeddingConstant) * (Real.sqrt 2) ^ 2 * hNorm 0 f * hNorm 0 g := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

theorem l2_h1_product_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 1 g) :
    InSobolev 0 (product f g) ∧
      hNorm 0 (product f g) ≤ h1EmbeddingConstant * hNorm 0 f * hNorm 1 g := by
  let F : L2Seq := ⟨f, (inSobolev_zero_iff f).mp hf⟩
  have hc := h1_absolute_coefficients hg
  have heq : (convolutionLp g F).val = product f g := by
    funext k
    rw [product_comm f g]
    exact convolutionLp_coeff g F hc.1 k
  have hm : InSobolev 0 (product f g) := by
    apply (inSobolev_zero_iff _).mpr
    rw [← heq]
    exact (convolutionLp g F).property
  refine ⟨hm, ?_⟩
  have hn : hNorm 0 (product f g) = ‖convolutionLp g F‖ := by
    rw [hNorm_eq_lpNorm hm]
    congr 1
    apply Subtype.ext
    simpa only [weighted_zero] using heq.symm
  rw [hn]
  calc
    _ ≤ (∑' k : ℤ, ‖g k‖) * ‖F‖ := convolutionLp_norm g F hc.1
    _ ≤ (h1EmbeddingConstant * hNorm 1 g) * ‖F‖ :=
      mul_le_mul_of_nonneg_right hc.2 (norm_nonneg F)
    _ = _ := by
      have hF : ‖F‖ = hNorm 0 f := by
        rw [hNorm_eq_lpNorm hf]
        congr 1
        apply Subtype.ext
        exact (weighted_zero f).symm
      rw [hF]
      ring

/-- The sharper `J` estimate used when its first input has a small inverse derivative. -/
theorem J_inverse_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : hNorm 0 (J t f g) ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * hNorm 0 (inverseDerivative f) * hNorm 0 g := by
  have hfi := (inverseDerivative_inSobolev_one hf).of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hp := l2_h1_product_bound (airy_inSobolev hfi t)
    (airy_inSobolev (inverseDerivative_inSobolev_one hg) t)
  rw [J, airy_hNorm]
  calc
    _ ≤ hNorm 0 (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))) :=
      removeMean_hNorm_le hp.1
    _ ≤ h1EmbeddingConstant * hNorm 0 (inverseDerivative f) * hNorm 1 (inverseDerivative g) := by
      simpa only [airy_hNorm] using hp.2
    _ ≤ h1EmbeddingConstant * hNorm 0 (inverseDerivative f) * (Real.sqrt 2 * hNorm 0 g) := by
      apply mul_le_mul_of_nonneg_left (inverseDerivative_hNorm_one hg)
      exact mul_nonneg (le_trans zero_le_one h1EmbeddingConstant_ge_one) (hNorm_nonneg 0 _)
    _ = _ := by ring




/-- Complementary projection, used only in the stability proof. -/
def highCutoff (m : ℕ) (f : Fourier) : Fourier := f - cutoff m f

theorem cutoff_frequency_bound {m : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)) : (k : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
  have h := (Finset.mem_Icc.mp hk)
  have hlo : -(m : ℝ) ≤ (k : ℝ) := by exact_mod_cast h.1
  have hhi : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.2
  nlinarith

theorem high_frequency_bound {m : ℕ} {k : ℤ}
    (hk : k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ)) : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hlo | hhi
  · have h : (k : ℝ) < -(m : ℝ) := by exact_mod_cast hlo
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  · have h : (m : ℝ) < (k : ℝ) := by exact_mod_cast hhi
    nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Bernstein bound for the proof projection; it does not change the method. -/
theorem cutoff_gain_bound {s q : ℝ} (hq : 0 ≤ q) {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    InSobolev (s + q) (cutoff m f) ∧
      hNorm (s + q) (cutoff m f) ≤ weight q (m : ℤ) * hNorm s f := by
  have hb (k : ℤ) : ‖weighted (s + q) (cutoff m f) k‖ ≤
      weight q (m : ℤ) * ‖weighted s f k‖ := by
    by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · rw [norm_weighted, norm_weighted]
      simp only [cutoff, if_pos hk]
      have hw : weight q k ≤ weight q (m : ℤ) := by
        unfold weight
        apply Real.rpow_le_rpow (by positivity)
          (by simpa using add_le_add_left (cutoff_frequency_bound hk) 1) (by positivity)
      rw [weight_add]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hw (mul_nonneg (weight_pos s k).le (norm_nonneg (f k)))
    · simp only [weighted, cutoff, if_neg hk, mul_zero, norm_zero]
      exact mul_nonneg (weight_pos q (m : ℤ)).le (norm_nonneg _)
  exact ⟨InSobolev.of_weighted_bound hf (weight_pos q (m : ℤ)).le hb,
    hNorm_le_of_weighted_bound hf (weight_pos q (m : ℤ)).le hb⟩

/-- Negative-order smallness of a high-frequency input, with the exact Japanese weight. -/
theorem high_cutoff_bound {s r : ℝ} (hsr : s ≤ r) {f : Fourier} (hf : InSobolev r f) (m : ℕ) :
    InSobolev s (highCutoff m f) ∧
      hNorm s (highCutoff m f) ≤ weight (s - r) (m : ℤ) * hNorm r f := by
  have hb (k : ℤ) : ‖weighted s (highCutoff m f) k‖ ≤
      weight (s - r) (m : ℤ) * ‖weighted r f k‖ := by
    by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · simp only [highCutoff, weighted, Pi.sub_apply, cutoff, if_pos hk, sub_self, mul_zero, norm_zero]
      exact mul_nonneg (weight_pos (s - r) (m : ℤ)).le (norm_nonneg _)
    · rw [norm_weighted, norm_weighted]
      simp only [highCutoff, Pi.sub_apply, cutoff, if_neg hk, sub_zero]
      have hw : weight (s - r) k ≤ weight (s - r) (m : ℤ) := by
        unfold weight
        apply Real.rpow_le_rpow_of_nonpos (by positivity)
          (by simpa using add_le_add_left (high_frequency_bound hk) 1) (by linarith)
      have hweight : weight s k = weight (s - r) k * weight r k := by
        simpa only [sub_add_cancel] using weight_add (s - r) r k
      rw [hweight]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hw (mul_nonneg (weight_pos r k).le (norm_nonneg (f k)))
  exact ⟨InSobolev.of_weighted_bound hf (weight_pos (s - r) (m : ℤ)).le hb,
    hNorm_le_of_weighted_bound hf (weight_pos (s - r) (m : ℤ)).le hb⟩

theorem cutoff_airy (m : ℕ) (t : ℝ) (f : Fourier) : cutoff m (airy t f) = airy t (cutoff m f) := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, airy, hk]

theorem cutoff_derivative (m : ℕ) (f : Fourier) :
    cutoff m (derivative f) = derivative (cutoff m f) := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, derivative, hk]




theorem product_airy_zero (t : ℝ) (f g : Fourier) :
    product (airy t f) (airy t g) 0 = product f g 0 := by
  unfold product
  apply tsum_congr
  intro a
  simp only [airy, zero_sub, Int.cast_neg]
  calc
    _ = (Complex.exp (Complex.I * (t : ℂ) * (a : ℂ) ^ 3) *
        Complex.exp (Complex.I * (t : ℂ) * (-(a : ℂ)) ^ 3)) * (f a * g (-a)) := by ring
    _ = _ := by
      rw [← Complex.exp_add,
        show Complex.I * (t : ℂ) * (a : ℂ) ^ 3 +
          Complex.I * (t : ℂ) * (-(a : ℂ)) ^ 3 = 0 by ring]
      simp

/-- The stage written exactly as Li–Wu (7.3), before deleting the mean. -/
def sourceBilinearStage (a t : ℝ) (f g : Fourier) : Fourier :=
  (1 / 6 : ℂ) •
    (airy (-t) (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))) -
      airy (-a) (product (airy a (inverseDerivative f)) (airy a (inverseDerivative g))))

/-- Deleting the mean in each boundary value leaves its endpoint difference unchanged. -/
theorem bilinearStage_eq_source (a t : ℝ) (f g : Fourier) :
    bilinearStage a t f g = sourceBilinearStage a t f g := by
  unfold bilinearStage sourceBilinearStage
  congr 1
  funext k
  by_cases hk : k = 0
  · subst k
    simp only [Pi.sub_apply, J, airy_mean, removeMean_zero, sub_self, product_airy_zero]
  · simp [J, airy, removeMean, hk]




/-- Li–Wu use unnormalized Lebesgue measure on the period-`2π` torus. -/
def sourceNormalization : ℝ := Real.sqrt (2 * Real.pi)

theorem sourceNormalization_pos : 0 < sourceNormalization := by
  unfold sourceNormalization
  positivity

def sourceNorm (s : ℝ) (f : Fourier) : ℝ := sourceNormalization * hNorm s f

/-- The `+` losses in Li–Wu (2.3) are represented by a fixed positive `ε`. -/
def sourceProductExponent (γ ε : ℝ) : ℝ :=
  if γ = 0 then 1 / 2 + ε else if γ < 1 / 2 then 1 / 2 - γ
  else if γ = 1 / 2 then ε else 0

/-- Explicit external premise: Li–Wu, author manuscript (2.2)–(2.3).
This imports only the spatial product theorem, with its two positive losses,
and with the source's unnormalized norms. It asserts no numerical estimate. -/
def LiWuProductEstimate : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ f g : Fourier,
      InSobolev γ f → InSobolev (sourceProductExponent γ ε) g →
        InSobolev 0 (product f g) ∧
        sourceNorm 0 (product f g) ≤ C * sourceNorm γ f * sourceNorm (sourceProductExponent γ ε) g

/-- The three lower endpoints in the full cited stage estimate. -/
def sourceStageLower (γ ε : ℝ) : ℝ :=
  if γ < 1 / 2 then 2 * γ - 3 / 2 else if γ = 1 / 2 then -1 / 2 - ε else γ - 1

def sourceStagePower (γ ε β : ℝ) : ℝ := (1 + γ - β) / (1 + γ - sourceStageLower γ ε)

/-- Explicit external premise: Li–Wu Lemma 7.2, with the stage represented by
its source endpoint formula (7.3). The bound is bilinear, over the whole source
regularity interval; constants precede the time step, starting time and inputs.
The source's standing zero-mode convention is included. -/
def LiWuStageEstimate : Prop :=
  ∀ T : ℝ, 0 < T → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∀ β : ℝ, sourceStageLower γ ε ≤ β → β ≤ 1 + γ →
      ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ, 0 < τ → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
        t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
          InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
            InSobolev β (sourceBilinearStage ((n : ℝ) * τ) t f g) ∧
            sourceNorm β (sourceBilinearStage ((n : ℝ) * τ) t f g) ≤
              C * τ ^ (sourceStagePower γ ε β) * sourceNorm γ f * sourceNorm γ g

/-- Normalization is derived, rather than silently built into the external premise. -/
theorem normalized_product_estimate (externalProduct : LiWuProductEstimate)
    {γ ε : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : Fourier,
      InSobolev γ f → InSobolev (sourceProductExponent γ ε) g →
        InSobolev 0 (product f g) ∧
        hNorm 0 (product f g) ≤ C * hNorm γ f * hNorm (sourceProductExponent γ ε) g := by
  obtain ⟨C, hC, hb⟩ := externalProduct γ hγ hγ1 ε hε
  refine ⟨C * sourceNormalization, mul_pos hC sourceNormalization_pos, ?_⟩
  intro f g hf hg
  obtain ⟨hm, hn⟩ := hb f g hf hg
  refine ⟨hm, (mul_le_mul_iff_right₀ sourceNormalization_pos).mp ?_⟩
  unfold sourceNorm at hn
  nlinarith [hn]

theorem normalized_stage_estimate (externalStage : LiWuStageEstimate)
    {T γ ε β : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hβ : sourceStageLower γ ε ≤ β) (hβ1 : β ≤ 1 + γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ, 0 < τ → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
        InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
          InSobolev β (bilinearStage ((n : ℝ) * τ) t f g) ∧
          hNorm β (bilinearStage ((n : ℝ) * τ) t f g) ≤
            C * τ ^ (sourceStagePower γ ε β) * hNorm γ f * hNorm γ g := by
  obtain ⟨C, hC, hb⟩ := externalStage T hT γ hγ hγ1 ε hε β hβ hβ1
  refine ⟨C * sourceNormalization, mul_pos hC sourceNormalization_pos, ?_⟩
  intro τ n t hτ hnT ht f g hf hg hfm hgm
  obtain ⟨hm, hn⟩ := hb τ n t hτ hnT ht f g hf hg hfm hgm
  rw [← bilinearStage_eq_source] at hm hn
  refine ⟨hm, (mul_le_mul_iff_right₀ sourceNormalization_pos).mp ?_⟩
  unfold sourceNorm at hn
  nlinarith [hn]

/-- The paper's fixed choice of the product exponent; its endpoint loss is `1/8`. -/
def aGamma (γ : ℝ) : ℝ := sourceProductExponent γ (1 / 8)

theorem aGamma_parameters {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    0 ≤ aGamma γ ∧ aGamma γ < 1 ∧
    sourceStageLower γ (1 / 8) ≤ aGamma γ ∧ aGamma γ ≤ 1 + γ ∧
    0 < 1 + γ - sourceStageLower γ (1 / 8) ∧
    γ ≤ sourceStagePower γ (1 / 8) (aGamma γ) := by
  by_cases hlow : γ < 1 / 2
  · simp only [aGamma, sourceProductExponent, ne_of_gt hγ, if_false, hlow, if_true,
      sourceStageLower, sourceStagePower]
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
    apply (le_div_iff₀ (by linarith : 0 < 1 + γ - (2 * γ - 3 / 2))).mpr
    nlinarith [sq_nonneg γ]
  · by_cases hmid : γ = 1 / 2
    · subst γ
      norm_num [aGamma, sourceProductExponent, sourceStageLower, sourceStagePower]
    · have hhigh : 1 / 2 < γ := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hmid)
      simp only [aGamma, sourceProductExponent, ne_of_gt hγ, if_false, hlow, hmid,
        sourceStageLower, sourceStagePower]
      refine ⟨le_rfl, by norm_num, by linarith, by linarith, by linarith, ?_⟩
      apply (le_div_iff₀ (by linarith : 0 < 1 + γ - (γ - 1))).mpr
      nlinarith

/-- The two stage bounds (18) follow from the full cited estimate; no stage
bound specialized to the desired numerical trajectory is assumed. -/
theorem paper_stage_bounds (externalStage : LiWuStageEstimate)
    {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ, 0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
        InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
          InSobolev (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f g) ∧
          InSobolev (1 + γ) (bilinearStage ((n : ℝ) * τ) t f g) ∧
          hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f g) ≤ C * τ ^ γ * hNorm γ f * hNorm γ g ∧
          hNorm (1 + γ) (bilinearStage ((n : ℝ) * τ) t f g) ≤ C * hNorm γ f * hNorm γ g := by
  obtain ⟨ha0, ha1, hba, hab, hd, hpower⟩ := aGamma_parameters hγ hγ1
  obtain ⟨C₁, hC₁, hb₁⟩ := normalized_stage_estimate externalStage hT hγ hγ1
    (by norm_num : (0 : ℝ) < 1 / 8) hba hab
  obtain ⟨C₂, hC₂, hb₂⟩ := normalized_stage_estimate externalStage hT hγ hγ1
    (by norm_num : (0 : ℝ) < 1 / 8) (β := 1 + γ) (by linarith) le_rfl
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro τ n t hτ hτ1 hnT ht f g hf hg hfm hgm
  obtain ⟨hm₁, hn₁⟩ := hb₁ τ n t hτ hnT ht f g hf hg hfm hgm
  obtain ⟨hm₂, hn₂⟩ := hb₂ τ n t hτ hnT ht f g hf hg hfm hgm
  refine ⟨hm₁, hm₂, hn₁.trans ?_, hn₂.trans ?_⟩
  · have hp := Real.rpow_le_rpow_of_exponent_ge hτ hτ1 hpower
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_left C₁ C₂) hp (Real.rpow_nonneg hτ.le _) (by positivity))
        (hNorm_nonneg γ f)) (hNorm_nonneg γ g)
  · simp only [sourceStagePower, sub_self, zero_div, Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (hNorm_nonneg γ f)) (hNorm_nonneg γ g)




theorem airy_inverse_neg (t : ℝ) (f : Fourier) : airy t (airy (-t) f) = f := by
  rw [← airy_add_time, add_neg_cancel, airy_zero]

theorem inverseDerivative_airy (t : ℝ) (f : Fourier) :
    inverseDerivative (airy t f) = airy t (inverseDerivative f) := by
  funext k
  by_cases hk : k = 0
  · simp [inverseDerivative, airy, hk]
  · simp only [inverseDerivative, if_neg hk, airy]
    ring

theorem removeMean_airy (t : ℝ) (f : Fourier) : removeMean (airy t f) = airy t (removeMean f) := by
  funext k
  by_cases hk : k = 0 <;> simp [removeMean, airy, hk]

theorem derivative_airy (t : ℝ) (f : Fourier) : derivative (airy t f) = airy t (derivative f) := by
  funext k
  simp only [derivative, airy]
  ring

theorem inverseDerivative_derivative (f : Fourier) : inverseDerivative (derivative f) = removeMean f := by
  funext k
  by_cases hk : k = 0
  · simp [inverseDerivative, removeMean, hk]
  · simp only [inverseDerivative, removeMean, if_neg hk, derivative]
    rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk : (k : ℂ) ≠ 0)), one_mul]

theorem derivative_inverseDerivative (f : Fourier) : derivative (inverseDerivative f) = removeMean f := by
  funext k
  by_cases hk : k = 0
  · simp [derivative, inverseDerivative, removeMean, hk]
  · simp only [derivative, inverseDerivative, removeMean, if_neg hk]
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk : (k : ℂ) ≠ 0)), one_mul]

/-- The substitution in (14), with no commutation through a product. -/
theorem J_B (t : ℝ) (f g h : Fourier) :
    J t (B t f g) h = airy (-t) (removeMean
      (product (removeMean (product (airy t f) (airy t g))) (airy t (inverseDerivative h)))) := by
  unfold J B
  rw [inverseDerivative_airy, inverseDerivative_derivative, airy_inverse_neg]

theorem J_B_integral (a b : ℝ) (f g h : ℝ → Fourier) (k : ℤ) :
    (∫ t : ℝ in a..b, J t (B t (f t) (g t)) (h t) k) = CIntegral a b f g h k := by
  unfold CIntegral
  apply intervalIntegral.integral_congr
  intro t _
  exact congrFun (J_B t (f t) (g t) (h t)) k

@[simp] theorem hNorm_neg (s : ℝ) (f : Fourier) : hNorm s (-f) = hNorm s f := by
  unfold hNorm
  congr 1
  apply tsum_congr
  intro k
  simp [weighted]

theorem hNorm_sub_le {s : ℝ} {f g : Fourier} (hf : InSobolev s f) (hg : InSobolev s g) :
    hNorm s (f - g) ≤ hNorm s f + hNorm s g := by
  let F : Sobolev s := ⟨f, hf⟩
  let G : Sobolev s := ⟨g, hg⟩
  have h := norm_sub_le F G
  simp only [sobolev_norm] at h
  change hNorm s (f - g) ≤ hNorm s f + hNorm s g at h
  exact h

theorem bilinearStage_h1_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (a t : ℝ) : InSobolev 1 (bilinearStage a t f g) ∧
      hNorm 1 (bilinearStage a t f g) ≤
        (4 / 3 : ℝ) * h1EmbeddingConstant * hNorm 0 f * hNorm 0 g := by
  obtain ⟨hm₁, hn₁⟩ := J_h1_bound hf hg t
  obtain ⟨hm₂, hn₂⟩ := J_h1_bound hf hg a
  refine ⟨(hm₁.sub hm₂).smul _, ?_⟩
  rw [bilinearStage, hNorm_smul (hm₁.sub hm₂)]
  have hn : ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) := by norm_num
  rw [hn]
  have hs := hNorm_sub_le hm₁ hm₂
  nlinarith




theorem inverseDerivative_sub (f g : Fourier) :
    inverseDerivative (f - g) = inverseDerivative f - inverseDerivative g := by
  funext k
  by_cases hk : k = 0 <;> simp [inverseDerivative, hk, mul_sub]

theorem removeMean_sub (f g : Fourier) : removeMean (f - g) = removeMean f - removeMean g := by
  funext k
  by_cases hk : k = 0 <;> simp [removeMean, hk]

theorem J_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t (f - g) h = J t f h - J t g h := by
  have hfi := airy_inSobolev ((inverseDerivative_inSobolev_one hf).of_le (by norm_num : (0 : ℝ) ≤ 1)) t
  have hgi := airy_inSobolev ((inverseDerivative_inSobolev_one hg).of_le (by norm_num : (0 : ℝ) ≤ 1)) t
  have hhi := airy_inSobolev ((inverseDerivative_inSobolev_one hh).of_le (by norm_num : (0 : ℝ) ≤ 1)) t
  unfold J
  rw [inverseDerivative_sub, airy_sub]
  have hp : product (airy t (inverseDerivative f) - airy t (inverseDerivative g))
      (airy t (inverseDerivative h)) =
      product (airy t (inverseDerivative f)) (airy t (inverseDerivative h)) -
        product (airy t (inverseDerivative g)) (airy t (inverseDerivative h)) := by
    funext k
    unfold product
    simp only [Pi.sub_apply, sub_mul]
    exact (product_summable hfi hhi k).tsum_sub (product_summable hgi hhi k)
  rw [hp, removeMean_sub, airy_sub]

theorem J_sub_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t f (g - h) = J t f g - J t f h := by
  rw [J_comm t f (g - h), J_sub_left hg hh hf, J_comm t g f, J_comm t h f]

theorem bilinearStage_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (a t : ℝ) :
    bilinearStage a t (f - g) h = bilinearStage a t f h - bilinearStage a t g h := by
  unfold bilinearStage
  rw [J_sub_left hf hg hh, J_sub_left hf hg hh]
  module

theorem bilinearStage_sub_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (a t : ℝ) :
    bilinearStage a t f (g - h) = bilinearStage a t f g - bilinearStage a t f h := by
  unfold bilinearStage
  rw [J_sub_right hf hg hh, J_sub_right hf hg hh]
  module

/-- Exact polarization of the stage; the numerical input needs only `L²`. -/
theorem bilinearStage_diagonal_sub {f w : Fourier} (hf : InSobolev 0 f) (hw : InSobolev 0 w)
    (a t : ℝ) : bilinearStage a t f f - bilinearStage a t w w =
      bilinearStage a t (f - w) f + bilinearStage a t w (f - w) := by
  rw [bilinearStage_sub_left hf hw hf, bilinearStage_sub_right hw hf hw]
  abel

theorem bilinearStage_diagonal_lipschitz {f w : Fourier} (hf : InSobolev 0 f) (hw : InSobolev 0 w)
    (a t : ℝ) :
    hNorm 1 (bilinearStage a t f f - bilinearStage a t w w) ≤
      ((4 / 3 : ℝ) * h1EmbeddingConstant) * (hNorm 0 f + hNorm 0 w) * hNorm 0 (f - w) := by
  rw [bilinearStage_diagonal_sub hf hw]
  obtain ⟨hm₁, hn₁⟩ := bilinearStage_h1_bound (hf.sub hw) hf a t
  obtain ⟨hm₂, hn₂⟩ := bilinearStage_h1_bound hw (hf.sub hw) a t
  calc
    _ ≤ hNorm 1 (bilinearStage a t (f - w) f) + hNorm 1 (bilinearStage a t w (f - w)) :=
      hNorm_add_le hm₁ hm₂
    _ ≤ _ := by nlinarith




/-- The stage estimates used in (20), uniform over numerical `L²` inputs close
to an exact `H^γ` state. No numerical higher Sobolev bound is assumed. -/
theorem numerical_stage_bounds (externalStage : LiWuStageEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f) ≤ C ∧
        hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) ≤
          C * hNorm 0 (f - w) ∧
        hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f f) ≤ C * (τ ^ γ + hNorm 0 (f - w)) ∧
        hNorm 0 (bilinearStage ((n : ℝ) * τ) t f f) ≤ C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cs, hCs, hstage⟩ := paper_stage_bounds externalStage hT hγ hγ1
  obtain ⟨ha0, ha1, hrest⟩ := aGamma_parameters hγ hγ1
  let K : ℝ := (4 / 3 : ℝ) * h1EmbeddingConstant
  have hK : 0 < K := mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one)
  let A : ℝ := K * (M + 1) ^ 2
  let D : ℝ := K * (2 * M + 1)
  let E : ℝ := Cs * M ^ 2
  have hA : 0 ≤ A := mul_nonneg hK.le (sq_nonneg _)
  have hD : 0 ≤ D := mul_nonneg hK.le (by linarith)
  have hE : 0 ≤ E := mul_nonneg hCs.le (sq_nonneg _)
  let C : ℝ := 1 + A + D + E
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  have hw0 := hw.of_le hγ.le
  have hwM0 : hNorm 0 w ≤ M := (hNorm_mono hw hγ.le).trans hwM
  have hfM : hNorm 0 f ≤ M + 1 := by
    have hs := hNorm_add_le (hf.sub hw0) hw0
    rw [sub_add_cancel] at hs
    linarith
  obtain ⟨hf1, hfb⟩ := bilinearStage_h1_bound hf hf ((n : ℝ) * τ) t
  obtain ⟨hw1, hwb⟩ := bilinearStage_h1_bound hw0 hw0 ((n : ℝ) * τ) t
  have hdiff := bilinearStage_diagonal_lipschitz hf hw0 ((n : ℝ) * τ) t
  have hDb : hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) ≤
      D * hNorm 0 (f - w) := by
    calc
      _ ≤ K * (hNorm 0 f + hNorm 0 w) * hNorm 0 (f - w) := hdiff
      _ ≤ K * ((M + 1) + M) * hNorm 0 (f - w) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hfM hwM0) hK.le) (hNorm_nonneg 0 _)
      _ = _ := by dsimp [D]; ring
  have hAb : hNorm 1 (bilinearStage ((n : ℝ) * τ) t f f) ≤ A := by
    calc
      _ ≤ K * hNorm 0 f * hNorm 0 f := hfb
      _ ≤ A := by
        dsimp [A]
        have hs : hNorm 0 f * hNorm 0 f ≤ (M + 1) ^ 2 := by nlinarith [hNorm_nonneg 0 f]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hK.le
  obtain ⟨hwA, hwHigh, hwAB, hwHighB⟩ := hstage τ n t hτ hτ1 hnT ht w w hw hw hwm hwm
  have hEb : hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t w w) ≤ E * τ ^ γ := by
    calc
      _ ≤ Cs * τ ^ γ * hNorm γ w * hNorm γ w := hwAB
      _ ≤ E * τ ^ γ := by
        have hs : hNorm γ w * hNorm γ w ≤ M ^ 2 := by nlinarith [hNorm_nonneg γ w]
        have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hCs.le (Real.rpow_nonneg hτ.le γ))
        dsimp [E]
        nlinarith only [hm]
  have hsum : hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f f) ≤
      E * τ ^ γ + D * hNorm 0 (f - w) := by
    have hdA : InSobolev (aGamma γ)
        (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) :=
      (hf1.sub hw1).of_le ha1.le
    have hs := hNorm_add_le hwA hdA
    rw [show bilinearStage ((n : ℝ) * τ) t w w +
      (bilinearStage ((n : ℝ) * τ) t f f - bilinearStage ((n : ℝ) * τ) t w w) =
      bilinearStage ((n : ℝ) * τ) t f f by abel] at hs
    exact hs.trans (add_le_add hEb ((hNorm_mono (hf1.sub hw1) ha1.le).trans hDb))
  have hbound : hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f f) ≤
      C * (τ ^ γ + hNorm 0 (f - w)) := by
    calc
      _ ≤ E * τ ^ γ + D * hNorm 0 (f - w) := hsum
      _ ≤ C * τ ^ γ + C * hNorm 0 (f - w) :=
        add_le_add (mul_le_mul_of_nonneg_right hEC (Real.rpow_nonneg hτ.le _))
          (mul_le_mul_of_nonneg_right hDC (hNorm_nonneg 0 _))
      _ = _ := by ring
  exact ⟨hAb.trans hAC, hDb.trans (mul_le_mul_of_nonneg_right hDC (hNorm_nonneg 0 _)),
    hbound, (hNorm_mono (hf1.of_le ha1.le) ha0).trans hbound⟩




theorem derivative_product {f g : Fourier} (hf : InSobolev 1 f) (hg : InSobolev 1 g) :
    derivative (product f g) = product (derivative f) g + product f (derivative g) := by
  have hf0 := hf.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hg0 := hg.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hdf : InSobolev 0 (derivative f) := derivative_inSobolev (s := 0) (by simpa using hf)
  have hdg : InSobolev 0 (derivative g) := derivative_inSobolev (s := 0) (by simpa using hg)
  funext k
  change Complex.I * (k : ℂ) * (∑' a : ℤ, f a * g (k - a)) =
    (∑' a : ℤ, (Complex.I * (a : ℂ) * f a) * g (k - a)) +
    ∑' a : ℤ, f a * (Complex.I * ((k - a : ℤ) : ℂ) * g (k - a))
  have hs := (product_summable hdf hg0 k).tsum_add (product_summable hf0 hdg k)
  simp only [derivative] at hs
  rw [← hs, ← tsum_mul_left]
  apply tsum_congr
  intro a
  push_cast
  ring

theorem derivative_square {f : Fourier} (hf : InSobolev 1 f) :
    derivative (product f f) = (2 : ℂ) • product (derivative f) f := by
  rw [derivative_product hf hf, product_comm f (derivative f)]
  module

/-- The product input (17) gives the exact-data square estimate needed in (21). -/
theorem derivative_square_bound (externalProduct : LiWuProductEstimate)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fourier,
      InSobolev (1 + γ) f → InSobolev (aGamma γ) f →
        InSobolev 0 (derivative (product f f)) ∧
        hNorm 0 (derivative (product f f)) ≤ C * hNorm (1 + γ) f * hNorm (aGamma γ) f := by
  obtain ⟨Cp, hCp, hprod⟩ := normalized_product_estimate externalProduct hγ.le hγ1
    (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨2 * Cp, by positivity, ?_⟩
  intro f hf hfa
  have hf1 := hf.of_le (by linarith : (1 : ℝ) ≤ 1 + γ)
  have hfplus : InSobolev (γ + 1) f := by simpa [add_comm] using hf
  have hdf := derivative_inSobolev hfplus
  obtain ⟨hm, hn⟩ := hprod (derivative f) f hdf hfa
  change hNorm 0 (product (derivative f) f) ≤ Cp * hNorm γ (derivative f) * hNorm (aGamma γ) f at hn
  rw [derivative_square hf1]
  refine ⟨hm.smul _, ?_⟩
  rw [hNorm_smul hm]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  calc
    _ ≤ 2 * (Cp * hNorm γ (derivative f) * hNorm (aGamma γ) f) := by linarith
    _ ≤ 2 * (Cp * hNorm (1 + γ) f * hNorm (aGamma γ) f) := by
      have hd : hNorm γ (derivative f) ≤ hNorm (1 + γ) f := by
        simpa only [add_comm] using derivative_hNorm hfplus
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hCp.le) (hNorm_nonneg _ _))
        (by norm_num)
    _ = _ := by ring

theorem B_h1_bound {f g : Fourier} (hf : InSobolev 1 f) (hg : InSobolev 1 g) (t : ℝ) :
    InSobolev 0 (B t f g) ∧
      hNorm 0 (B t f g) ≤ 2 * h1EmbeddingConstant * hNorm 1 f * hNorm 1 g := by
  obtain ⟨hp, hn⟩ := h1_product_bound (airy_inSobolev hf t) (airy_inSobolev hg t)
  have hd : InSobolev 0 (derivative (product (airy t f) (airy t g))) :=
    derivative_inSobolev (s := 0) (by simpa using hp)
  refine ⟨airy_inSobolev hd (-t), ?_⟩
  rw [B, airy_hNorm]
  calc
    _ ≤ hNorm 1 (product (airy t f) (airy t g)) := by
      simpa using derivative_hNorm (s := 0) (by simpa using hp)
    _ ≤ _ := by simpa only [airy_hNorm] using hn

theorem product_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) : product (f - g) h = product f h - product g h := by
  funext k
  unfold product
  simp only [Pi.sub_apply, sub_mul]
  exact (product_summable hf hh k).tsum_sub (product_summable hg hh k)

theorem product_difference_squares {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g) :
    product f f - product g g = product (f - g) (f + g) := by
  rw [product_add_right (hf.sub hg) hf hg, product_sub_left hf hg hf,
    product_sub_left hf hg hg, product_comm g f]
  abel

/-- The low-output estimate needed for (30), without any cutoff in the scheme. -/
theorem B_low_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) (m : ℕ) : hNorm 0 (cutoff m (B t f g)) ≤
      (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * hNorm 0 f * hNorm 0 g := by
  obtain ⟨hp, hn⟩ := negative_product_bound (q := 1) (by norm_num)
    (airy_inSobolev hf t) (airy_inSobolev hg t)
  have hgain := cutoff_gain_bound (s := -1) (q := 2) (by norm_num) hp m
  have hcut : InSobolev (0 + 1) (cutoff m (product (airy t f) (airy t g))) := by
    convert hgain.1 using 1; norm_num
  rw [B, cutoff_airy, cutoff_derivative, airy_hNorm]
  calc
    _ ≤ hNorm 1 (cutoff m (product (airy t f) (airy t g))) := by
      simpa using derivative_hNorm hcut
    _ ≤ weight 2 (m : ℤ) * hNorm (-1) (product (airy t f) (airy t g)) := by
      convert hgain.2 using 1; norm_num
    _ ≤ weight 2 (m : ℤ) * (negativeProductConstant 1 (by norm_num) * hNorm 0 f * hNorm 0 g) := by
      apply mul_le_mul_of_nonneg_left _ (weight_pos 2 (m : ℤ)).le
      simpa only [airy_hNorm] using hn
    _ = _ := by simp [weight, mul_assoc]




/-- Distributional time derivative on the open interval. In particular this
is stronger than merely prescribing an almost-everywhere classical derivative. -/
def WeakTimeDerivative (a b : ℝ) (f df : ℝ → Fourier) : Prop :=
  ∀ k : ℤ, ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
    Function.support φ ⊆ Set.Ioo a b →
      (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) * f t k) =
        -(∫ t : ℝ in a..b, (φ t : ℂ) * df t k)

/-- The unnormalized spatial norm, with the essential supremum in time.
Finiteness is always supplied separately as `MemLp ... ∞`. -/
def sourceLInfinity {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) : ℝ :=
  sourceNormalization * (eLpNorm f ∞ (volume.restrict (Set.Icc a b))).toReal

def sourceLInfinityZero {α : ℝ} (hα : 0 ≤ α) (a b : ℝ) (f : ℝ → Sobolev α) : ℝ :=
  sourceLInfinity a b (fun t => inclusionMap 0 α hα (f t))

def sourceLInfinityNegative {α : ℝ} (hα : 0 ≤ α) (a b : ℝ) (f : ℝ → Sobolev α) : ℝ :=
  sourceLInfinity a b (fun t => inclusionMap (-pStar) α (by dsimp [pStar]; linarith) (f t))

def sourceXNorm {α : ℝ} (hα : 0 ≤ α) (a b : ℝ)
    (f : ℝ → Sobolev α) (df : ℝ → Sobolev (-pStar)) : ℝ :=
  sourceLInfinityZero hα a b f + sourceLInfinity a b df

/-- Explicit external premise: both parts of Li–Wu Proposition 3.4.
The derivative is distributional, the input hypotheses are essential bounds
in the actual complete Sobolev spaces, and the operator is (3.13). The negative
norm may be placed on any specified input while leaving the operator's slots
fixed, exactly as the source's permutation sentence states. A fixed bound `H`
on the interval length makes the implicit bounded-length convention explicit. -/
structure LiWuTrilinearEstimate : Prop where
  dynamic : ∀ H : ℝ, 0 < H → H ≤ 1 → ∀ α : ℝ, ∀ hα : 0 ≤ α, α ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f : Fin 3 → ℝ → Sobolev α, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
          InSobolev 0 (CIntegral a b (fun t => (f 0 t).val)
            (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ∧
          ∀ i : Fin 3,
            sourceNorm 0 (CIntegral a b (fun t => (f 0 t).val)
              (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ≤
              C * (b - a) * (∏ j : Fin 3, sourceXNorm hα a b (f j) (df j)) +
              C * sourceLInfinityNegative hα a b (f i) *
                (∏ j : Fin 3, if j = i then 1 else sourceLInfinityZero hα a b (f j))
  timeIndependent : ∀ H : ℝ, 0 < H → H ≤ 1 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f g h : Fourier, InSobolev α f → InSobolev α g → InSobolev α h →
        InSobolev 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ∧
        sourceNorm 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ≤
          C * (b - a) ^ α * sourceNorm α f * sourceNorm α g * sourceNorm α h

theorem sourceLInfinity_nonneg {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) :
    0 ≤ sourceLInfinity a b f :=
  mul_nonneg sourceNormalization_pos.le ENNReal.toReal_nonneg

theorem sourceXNorm_nonneg {α : ℝ} (hα : 0 ≤ α) (a b : ℝ)
    (f : ℝ → Sobolev α) (df : ℝ → Sobolev (-pStar)) : 0 ≤ sourceXNorm hα a b f df :=
  add_nonneg (sourceLInfinity_nonneg _ _ _) (sourceLInfinity_nonneg _ _ _)

/-- Normalizing a trilinear source estimate contributes two powers of the
fixed spatial measure factor. This does not import any residual estimate. -/
theorem normalized_static_trilinear (externalTrilinear : LiWuTrilinearEstimate)
    {H α : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f g h : Fourier, InSobolev α f → InSobolev α g → InSobolev α h →
        InSobolev 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ∧
        hNorm 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ≤
          C * (b - a) ^ α * hNorm α f * hNorm α g * hNorm α h := by
  obtain ⟨C, hC, hb⟩ := externalTrilinear.timeIndependent H hH hH1 α hα hα1
  refine ⟨C * sourceNormalization ^ 2, mul_pos hC (sq_pos_of_pos sourceNormalization_pos), ?_⟩
  intro a b ha hab hHbound f g h hf hg hh
  obtain ⟨hm, hn⟩ := hb a b ha hab hHbound f g h hf hg hh
  refine ⟨hm, (mul_le_mul_iff_right₀ sourceNormalization_pos).mp ?_⟩
  unfold sourceNorm at hn
  nlinarith only [hn]




def bilinearPhase (k a : ℤ) : ℝ := 3 * (k : ℝ) * (a : ℝ) * ((k - a : ℤ) : ℝ)

theorem airy_convolution_phase (t : ℝ) (k a : ℤ) (x y : ℂ) :
    Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3) *
      ((Complex.exp (Complex.I * (t : ℂ) * (a : ℂ) ^ 3) * x) *
        (Complex.exp (Complex.I * (t : ℂ) * ((k - a : ℤ) : ℂ) ^ 3) * y)) =
      oscillation (bilinearPhase k a) t * x * y := by
  have hp : -Complex.I * (t : ℂ) * (bilinearPhase k a : ℂ) =
      Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3 +
        (Complex.I * (t : ℂ) * (a : ℂ) ^ 3 +
          Complex.I * (t : ℂ) * ((k - a : ℤ) : ℂ) ^ 3) := by
    unfold bilinearPhase
    push_cast
    ring
  rw [oscillation, hp, Complex.exp_add, Complex.exp_add]
  ring

def JMode (k a : ℤ) (f g : Fourier) (t : ℝ) : ℂ :=
  oscillation (bilinearPhase k a) t *
    (inverseDerivative f a * inverseDerivative g (k - a))

def BMode (k a : ℤ) (f g : Fourier) (t : ℝ) : ℂ :=
  (Complex.I * (k : ℂ)) * (oscillation (bilinearPhase k a) t * f a * g (k - a))

theorem J_coefficient_series {k : ℤ} (hk : k ≠ 0) (f g : Fourier) (t : ℝ) :
    J t f g k = ∑' a : ℤ, JMode k a f g t := by
  simp only [J, airy, removeMean, if_neg hk, product]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  exact (airy_convolution_phase t k a (inverseDerivative f a) (inverseDerivative g (k - a))).trans
    (by unfold JMode; ring)

theorem B_coefficient_series (k : ℤ) (f g : Fourier) (t : ℝ) :
    B t f g k = ∑' a : ℤ, BMode k a f g t := by
  simp only [B, airy, derivative, product]
  rw [← mul_assoc, mul_comm (Complex.exp _) (Complex.I * (k : ℂ)), mul_assoc,
    ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro a
  unfold BMode
  rw [airy_convolution_phase]

theorem JMode_derivative_factor {f g : Fourier} (hfm : MeanZero f) (hgm : MeanZero g)
    (k a : ℤ) (t : ℝ) :
    ((-Complex.I * (bilinearPhase k a : ℂ)) * oscillation (bilinearPhase k a) t) *
      (inverseDerivative f a * inverseDerivative g (k - a)) = 3 * BMode k a f g t := by
  change f 0 = 0 at hfm
  change g 0 = 0 at hgm
  by_cases ha : a = 0
  · subst a
    simp [inverseDerivative, BMode, hfm]
  · by_cases hb : k - a = 0
    · simp [inverseDerivative, hb, BMode, hgm]
    · have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      have hbC : ((k - a : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hb
      have hbD : (k : ℂ) - (a : ℂ) ≠ 0 := by exact_mod_cast hb
      simp only [inverseDerivative, if_neg ha, if_neg hb]
      have hc : (-Complex.I * (bilinearPhase k a : ℂ)) *
          ((Complex.I * (a : ℂ))⁻¹ * (Complex.I * ((k - a : ℤ) : ℂ))⁻¹) =
          3 * (Complex.I * (k : ℂ)) := by
        unfold bilinearPhase
        push_cast
        field_simp [haC, hbD]
        simp [Complex.I_sq]
      calc
        _ = ((-Complex.I * (bilinearPhase k a : ℂ)) *
            ((Complex.I * (a : ℂ))⁻¹ * (Complex.I * ((k - a : ℤ) : ℂ))⁻¹)) *
              (oscillation (bilinearPhase k a) t * f a * g (k - a)) := by ring
        _ = _ := by rw [hc]; unfold BMode; ring

theorem JMode_hasDerivAt {f g : Fourier} (hfm : MeanZero f) (hgm : MeanZero g)
    (k a : ℤ) (t : ℝ) : HasDerivAt (JMode k a f g) (3 * BMode k a f g t) t := by
  have h := (oscillation_derivative (bilinearPhase k a) t).mul_const
    (inverseDerivative f a * inverseDerivative g (k - a))
  rw [JMode_derivative_factor hfm hgm k a t] at h
  exact h


theorem BMode_norm (k a : ℤ) (f g : Fourier) (t : ℝ) :
    ‖BMode k a f g t‖ = |(k : ℝ)| * (‖f a‖ * ‖g (k - a)‖) := by
  simp [BMode, oscillation_norm, Complex.norm_intCast, mul_assoc]

theorem BMode_continuous (k a : ℤ) (f g : Fourier) : Continuous (BMode k a f g) := by
  unfold BMode
  exact continuous_const.mul (((oscillation_continuous _).mul continuous_const).mul continuous_const)

theorem absolute_convolution_summable {f g : Fourier} (hf : InSobolev 0 f)
    (hg : InSobolev 0 g) (k : ℤ) : Summable (fun a : ℤ => ‖f a‖ * ‖g (k - a)‖) := by
  simpa only [norm_mul] using (product_summable hf hg k).norm

theorem continuous_B_coefficient {f g : Fourier} (hf : InSobolev 0 f)
    (hg : InSobolev 0 g) (k : ℤ) : Continuous (fun t : ℝ => B t f g k) := by
  have heq : (fun t : ℝ => B t f g k) = (fun t : ℝ => ∑' a : ℤ, BMode k a f g t) :=
    funext (B_coefficient_series k f g)
  rw [heq]
  exact continuous_tsum (fun a => BMode_continuous k a f g)
    ((absolute_convolution_summable hf hg k).mul_left |(k : ℝ)|)
    (fun a t => (BMode_norm k a f g t).le)

/-- The normal-form phase derivative is proved on the full `L²` space,
with no Fourier truncation and no smoothness assumption. -/
theorem J_fixed_hasDerivAt {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hfm : MeanZero f) (hgm : MeanZero g) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => J r f g k) (3 * B t f g k) t := by
  by_cases hk : k = 0
  · subst k
    have hz : (fun r : ℝ => J r f g 0) = (fun _ : ℝ => (0 : ℂ)) :=
      funext (fun r => J_meanZero r f g)
    rw [hz, show B t f g 0 = 0 from B_meanZero t f g, mul_zero]
    exact hasDerivAt_const t (0 : ℂ)
  · have hfi := (inverseDerivative_inSobolev_one hf).of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hgi := (inverseDerivative_inSobolev_one hg).of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hj0 : Summable (fun a : ℤ => JMode k a f g 0) := by
      simpa only [JMode, oscillation_zero, one_mul] using product_summable hfi hgi k
    have hu := (absolute_convolution_summable hf hg k).mul_left (3 * |(k : ℝ)|)
    have hb (a : ℤ) (r : ℝ) : ‖(3 : ℂ) * BMode k a f g r‖ ≤
        (3 * |(k : ℝ)|) * (‖f a‖ * ‖g (k - a)‖) := by
      rw [norm_mul, BMode_norm]
      have hthree : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
      rw [hthree]
      exact le_of_eq (by ring)
    have h := hasDerivAt_tsum hu
      (fun a r => JMode_hasDerivAt hfm hgm k a r) hb hj0 t
    have hj : (fun r : ℝ => ∑' a : ℤ, JMode k a f g r) = (fun r : ℝ => J r f g k) :=
      funext (fun r => (J_coefficient_series hk f g r).symm)
    rw [hj] at h
    have heq : (∑' a : ℤ, (3 : ℂ) * BMode k a f g t) = 3 * B t f g k := by
      rw [tsum_mul_left, ← B_coefficient_series]
    rw [heq] at h
    exact h

/-- The constant-input normal form, with both endpoints retained. -/
theorem fixed_normal_form {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hfm : MeanZero f) (hgm : MeanZero g) (a b : ℝ) (k : ℤ) :
    (∫ t : ℝ in a..b, B t f g k) = (1 / 3 : ℂ) * (J b f g k - J a f g k) := by
  have hi : IntervalIntegrable (fun t : ℝ => (3 : ℂ) * B t f g k) volume a b :=
    (continuous_const.mul (continuous_B_coefficient hf hg k)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => J_fixed_hasDerivAt hf hg hfm hgm k t) hi
  rw [intervalIntegral.integral_const_mul] at h
  calc
    _ = (1 / 3 : ℂ) * (3 * ∫ t : ℝ in a..b, B t f g k) := by ring
    _ = _ := by rw [h]




theorem inverseDerivative_coeff_norm_le (f : Fourier) (k : ℤ) :
    ‖inverseDerivative f k‖ ≤ ‖f k‖ := by
  by_cases hk : k = 0
  · simp [inverseDerivative, hk]
  · have hkone : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    simp only [inverseDerivative, if_neg hk, norm_mul, norm_inv, Complex.norm_I,
      Complex.norm_intCast, one_mul]
    have hi : |(k : ℝ)|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hkone
    nlinarith [norm_nonneg (f k)]

theorem JMode_norm_le (k a : ℤ) (f g : Fourier) (t : ℝ) :
    ‖JMode k a f g t‖ ≤ ‖f a‖ * ‖g (k - a)‖ := by
  simp only [JMode, norm_mul, oscillation_norm, one_mul]
  exact mul_le_mul (inverseDerivative_coeff_norm_le f a) (inverseDerivative_coeff_norm_le g (k - a))
    (norm_nonneg _) (norm_nonneg _)

theorem inverseDerivative_coeff_hasDerivAt {f df : ℝ → Fourier} {t : ℝ}
    (hf : ∀ k : ℤ, HasDerivAt (fun r : ℝ => f r k) (df t k) t) (k : ℤ) :
    HasDerivAt (fun r : ℝ => inverseDerivative (f r) k) (inverseDerivative (df t) k) t := by
  by_cases hk : k = 0
  · simpa only [inverseDerivative, if_pos hk] using hasDerivAt_const t (0 : ℂ)
  · simpa only [inverseDerivative, if_neg hk] using (hf k).const_mul (Complex.I * (k : ℂ))⁻¹

def variableJMode (k a : ℤ) (f g : ℝ → Fourier) (t : ℝ) : ℂ := JMode k a (f t) (g t) t

theorem variableJMode_hasDerivAt {f df g dg : ℝ → Fourier} {t : ℝ}
    (hf : ∀ k : ℤ, HasDerivAt (fun r : ℝ => f r k) (df t k) t)
    (hg : ∀ k : ℤ, HasDerivAt (fun r : ℝ => g r k) (dg t k) t)
    (hfm : MeanZero (f t)) (hgm : MeanZero (g t)) (k a : ℤ) :
    HasDerivAt (variableJMode k a f g)
      (3 * BMode k a (f t) (g t) t + JMode k a (df t) (g t) t + JMode k a (f t) (dg t) t) t := by
  have h := (oscillation_derivative (bilinearPhase k a) t).mul
    ((inverseDerivative_coeff_hasDerivAt hf a).mul (inverseDerivative_coeff_hasDerivAt hg (k - a)))
  apply h.congr_deriv
  have he := JMode_derivative_factor hfm hgm k a t
  dsimp [JMode] at *
  linear_combination he

/-- A common square-summable envelope supplies the analytic justification for
termwise differentiation. This is an internal regularity condition; deriving it
for the smooth trajectories used in the proof remains a separate obligation. -/
structure RegularFourierPath (a b : ℝ) (f df : ℝ → Fourier) : Prop where
  continuous : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b)
  derivative_continuous : ∀ k, ContinuousOn (fun t : ℝ => df t k) (Set.Icc a b)
  hasDerivAt : ∀ t ∈ Set.Ioo a b, ∀ k, HasDerivAt (fun r : ℝ => f r k) (df t k) t
  envelope : ∃ F Fd : Fourier, InSobolev 0 F ∧ InSobolev 0 Fd ∧
    ∀ t ∈ Set.Icc a b, ∀ k, ‖f t k‖ ≤ ‖F k‖ ∧ ‖df t k‖ ≤ ‖Fd k‖

theorem inSobolev_zero_of_coeff_bound {f F : Fourier} (hF : InSobolev 0 F)
    (hb : ∀ k, ‖f k‖ ≤ ‖F k‖) : InSobolev 0 f := by
  rw [inSobolev_zero_iff] at hF ⊢
  exact Memℓp.mono' hF hb

theorem inverseDerivative_coeff_continuousOn {f : ℝ → Fourier} {S : Set ℝ}
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) S) (k : ℤ) :
    ContinuousOn (fun t : ℝ => inverseDerivative (f t) k) S := by
  by_cases hk : k = 0
  · simpa only [inverseDerivative, if_pos hk] using continuousOn_const (c := (0 : ℂ))
  · simpa only [inverseDerivative, if_neg hk] using (hf k).const_mul (Complex.I * (k : ℂ))⁻¹

theorem variableJMode_continuousOn {f g : ℝ → Fourier} {S : Set ℝ}
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) S)
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) S) (k a : ℤ) :
    ContinuousOn (variableJMode k a f g) S := by
  exact (oscillation_continuous _).continuousOn.mul
    ((inverseDerivative_coeff_continuousOn hf a).mul (inverseDerivative_coeff_continuousOn hg (k - a)))

theorem variableBMode_continuousOn {f g : ℝ → Fourier} {S : Set ℝ}
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) S)
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) S) (k a : ℤ) :
    ContinuousOn (fun t : ℝ => BMode k a (f t) (g t) t) S := by
  exact continuousOn_const.mul (((oscillation_continuous _).continuousOn.mul (hf a)).mul (hg (k - a)))




theorem JMode_envelope {f g F G : Fourier} (hf : ∀ k, ‖f k‖ ≤ ‖F k‖)
    (hg : ∀ k, ‖g k‖ ≤ ‖G k‖) (k a : ℤ) (t : ℝ) :
    ‖JMode k a f g t‖ ≤ ‖F a‖ * ‖G (k - a)‖ :=
  (JMode_norm_le k a f g t).trans (mul_le_mul (hf a) (hg (k - a)) (norm_nonneg _) (norm_nonneg _))

theorem three_BMode_envelope {f g F G : Fourier} (hf : ∀ k, ‖f k‖ ≤ ‖F k‖)
    (hg : ∀ k, ‖g k‖ ≤ ‖G k‖) (k a : ℤ) (t : ℝ) :
    ‖(3 : ℂ) * BMode k a f g t‖ ≤ (3 * |(k : ℝ)|) * (‖F a‖ * ‖G (k - a)‖) := by
  rw [norm_mul, BMode_norm]
  have hthree : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
  rw [hthree, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hf a) (hg (k - a)) (norm_nonneg _) (norm_nonneg _))
    (by positivity)

theorem variable_J_continuousOn {a b : ℝ} {f g : ℝ → Fourier} {F G : Fourier}
    (hF : InSobolev 0 F) (hG : InSobolev 0 G)
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b))
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) (Set.Icc a b))
    (hfb : ∀ t ∈ Set.Icc a b, ∀ k, ‖f t k‖ ≤ ‖F k‖)
    (hgb : ∀ t ∈ Set.Icc a b, ∀ k, ‖g t k‖ ≤ ‖G k‖) (k : ℤ) :
    ContinuousOn (fun t : ℝ => J t (f t) (g t) k) (Set.Icc a b) := by
  by_cases hk : k = 0
  · subst k
    have heq : (fun t : ℝ => J t (f t) (g t) 0) = (fun _ : ℝ => (0 : ℂ)) :=
      funext (fun t => J_meanZero t (f t) (g t))
    rw [heq]
    exact continuousOn_const
  · have heq : (fun t : ℝ => J t (f t) (g t) k) =
        (fun t : ℝ => ∑' j : ℤ, variableJMode k j f g t) :=
      funext (fun t => J_coefficient_series hk (f t) (g t) t)
    rw [heq]
    exact continuousOn_tsum (fun j => variableJMode_continuousOn hf hg k j)
      (absolute_convolution_summable hF hG k)
      (fun j t ht => JMode_envelope (hfb t ht) (hgb t ht) k j t)

theorem variable_B_continuousOn {a b : ℝ} {f g : ℝ → Fourier} {F G : Fourier}
    (hF : InSobolev 0 F) (hG : InSobolev 0 G)
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b))
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) (Set.Icc a b))
    (hfb : ∀ t ∈ Set.Icc a b, ∀ k, ‖f t k‖ ≤ ‖F k‖)
    (hgb : ∀ t ∈ Set.Icc a b, ∀ k, ‖g t k‖ ≤ ‖G k‖) (k : ℤ) :
    ContinuousOn (fun t : ℝ => B t (f t) (g t) k) (Set.Icc a b) := by
  have heq : (fun t : ℝ => B t (f t) (g t) k) =
      (fun t : ℝ => ∑' j : ℤ, BMode k j (f t) (g t) t) :=
    funext (fun t => B_coefficient_series k (f t) (g t) t)
  rw [heq]
  apply continuousOn_tsum (fun j => variableBMode_continuousOn hf hg k j)
    ((absolute_convolution_summable hF hG k).mul_left |(k : ℝ)|)
  intro j t ht
  rw [BMode_norm]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (hfb t ht j) (hgb t ht (k - j)) (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)

/-- Full time-dependent normal-form differentiation under explicit internal
regularity hypotheses. It is not imported as an external theorem. -/
theorem variable_J_hasDerivAt {a b : ℝ} {f df g dg : ℝ → Fourier}
    (hf : RegularFourierPath a b f df) (hg : RegularFourierPath a b g dg)
    (hfm : ∀ t ∈ Set.Icc a b, MeanZero (f t)) (hgm : ∀ t ∈ Set.Icc a b, MeanZero (g t))
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (k : ℤ) :
    HasDerivAt (fun r : ℝ => J r (f r) (g r) k)
      (3 * B t (f t) (g t) k + J t (df t) (g t) k + J t (f t) (dg t) k) t := by
  by_cases hk : k = 0
  · subst k
    have heq : (fun r : ℝ => J r (f r) (g r) 0) = (fun _ : ℝ => (0 : ℂ)) :=
      funext (fun r => J_meanZero r (f r) (g r))
    rw [heq, show B t (f t) (g t) 0 = 0 from B_meanZero _ _ _,
      show J t (df t) (g t) 0 = 0 from J_meanZero _ _ _,
      show J t (f t) (dg t) 0 = 0 from J_meanZero _ _ _]
    simpa using hasDerivAt_const t (0 : ℂ)
  · obtain ⟨F, Fd, hF, hFd, hfb⟩ := hf.envelope
    obtain ⟨G, Gd, hG, hGd, hgb⟩ := hg.envelope
    have hFt r hr k := (hfb r hr k).1
    have hFdt r hr k := (hfb r hr k).2
    have hGt r hr k := (hgb r hr k).1
    have hGdt r hr k := (hgb r hr k).2
    have htc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    have huB := (absolute_convolution_summable hF hG k).mul_left (3 * |(k : ℝ)|)
    have huD := absolute_convolution_summable hFd hG k
    have huE := absolute_convolution_summable hF hGd k
    have hu := (huB.add huD).add huE
    have hb (j : ℤ) (r : ℝ) (hr : r ∈ Set.Ioo a b) :
        ‖3 * BMode k j (f r) (g r) r + JMode k j (df r) (g r) r + JMode k j (f r) (dg r) r‖ ≤
          ((3 * |(k : ℝ)|) * (‖F j‖ * ‖G (k - j)‖) + ‖Fd j‖ * ‖G (k - j)‖) +
            ‖F j‖ * ‖Gd (k - j)‖ := by
      have hrc : r ∈ Set.Icc a b := ⟨hr.1.le, hr.2.le⟩
      calc
        _ ≤ (‖(3 : ℂ) * BMode k j (f r) (g r) r‖ + ‖JMode k j (df r) (g r) r‖) +
            ‖JMode k j (f r) (dg r) r‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ _ := add_le_add
          (add_le_add (three_BMode_envelope (hFt r hrc) (hGt r hrc) k j r)
            (JMode_envelope (hFdt r hrc) (hGt r hrc) k j r))
          (JMode_envelope (hFt r hrc) (hGdt r hrc) k j r)
    have hj0 : Summable (fun j : ℤ => variableJMode k j f g t) :=
      Summable.of_norm_bounded (absolute_convolution_summable hF hG k)
        (fun j => JMode_envelope (hFt t htc) (hGt t htc) k j t)
    have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      (fun j r hr => variableJMode_hasDerivAt (hf.hasDerivAt r hr) (hg.hasDerivAt r hr)
        (hfm r ⟨hr.1.le, hr.2.le⟩) (hgm r ⟨hr.1.le, hr.2.le⟩) k j)
      hb ht hj0 ht
    have heq : (fun r : ℝ => ∑' j : ℤ, variableJMode k j f g r) =
        (fun r : ℝ => J r (f r) (g r) k) :=
      funext (fun r => (J_coefficient_series hk (f r) (g r) r).symm)
    rw [heq] at h
    have hsB : Summable (fun j : ℤ => (3 : ℂ) * BMode k j (f t) (g t) t) :=
      Summable.of_norm_bounded huB (fun j => three_BMode_envelope (hFt t htc) (hGt t htc) k j t)
    have hsD : Summable (fun j : ℤ => JMode k j (df t) (g t) t) :=
      Summable.of_norm_bounded huD (fun j => JMode_envelope (hFdt t htc) (hGt t htc) k j t)
    have hsE : Summable (fun j : ℤ => JMode k j (f t) (dg t) t) :=
      Summable.of_norm_bounded huE (fun j => JMode_envelope (hFt t htc) (hGdt t htc) k j t)
    rw [(hsB.add hsD).tsum_add hsE, hsB.tsum_add hsD, tsum_mul_left,
      ← B_coefficient_series, ← J_coefficient_series hk, ← J_coefficient_series hk] at h
    exact h


/-- Equation (13), including the initial boundary value, proved by termwise
Fourier differentiation and the fundamental theorem of calculus. -/
theorem variable_normal_form {a b : ℝ} (hab : a ≤ b) {f df g dg : ℝ → Fourier}
    (hf : RegularFourierPath a b f df) (hg : RegularFourierPath a b g dg)
    (hfm : ∀ t ∈ Set.Icc a b, MeanZero (f t)) (hgm : ∀ t ∈ Set.Icc a b, MeanZero (g t))
    (k : ℤ) :
    (∫ t : ℝ in a..b, B t (f t) (g t) k) =
      (1 / 3 : ℂ) * (J b (f b) (g b) k - J a (f a) (g a) k) -
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b, (J t (df t) (g t) k + J t (f t) (dg t) k) := by
  obtain ⟨F, Fd, hF, hFd, hfb⟩ := hf.envelope
  obtain ⟨G, Gd, hG, hGd, hgb⟩ := hg.envelope
  have hFt r hr k := (hfb r hr k).1
  have hFdt r hr k := (hfb r hr k).2
  have hGt r hr k := (hgb r hr k).1
  have hGdt r hr k := (hgb r hr k).2
  have hcJ := variable_J_continuousOn hF hG hf.continuous hg.continuous hFt hGt k
  have hcB := variable_B_continuousOn hF hG hf.continuous hg.continuous hFt hGt k
  have hcD := variable_J_continuousOn hFd hG hf.derivative_continuous hg.continuous hFdt hGt k
  have hcE := variable_J_continuousOn hF hGd hf.continuous hg.derivative_continuous hFt hGdt k
  have hiB := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hcB
  have hiD := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hcD
  have hiE := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hcE
  have hi3B := hiB.const_mul (3 : ℂ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcJ
    (fun t ht => variable_J_hasDerivAt hf hg hfm hgm ht k) ((hi3B.add hiD).add hiE)
  rw [intervalIntegral.integral_add (hi3B.add hiD) hiE,
    intervalIntegral.integral_add hi3B hiD, intervalIntegral.integral_const_mul] at hFTC
  rw [intervalIntegral.integral_add hiD hiE]
  linear_combination (1 / 3 : ℂ) * hFTC




theorem weighted_coeff_bound {s : ℝ} {f : Fourier} (hf : InSobolev s f) (k : ℤ) :
    ‖weighted s f k‖ ≤ hNorm s f := by
  rw [hNorm_eq_lpNorm hf]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ⟨weighted s f, hf⟩ k

theorem weight_neg (s : ℝ) (k : ℤ) : weight (-s) k = (weight s k)⁻¹ := by
  unfold weight
  rw [neg_div, Real.rpow_neg (by positivity)]

def sobolevEnvelope (M : ℝ) : Fourier := fun k => (M : ℂ) * (weight (-1) k : ℂ)

theorem sobolevEnvelope_inSobolev (M : ℝ) : InSobolev 0 (sobolevEnvelope M) := by
  rw [inSobolev_zero_iff]
  exact (negativeWeightLp 1 (by norm_num)).property.const_smul (M : ℂ)

theorem h1_coeff_envelope {f : Fourier} (hf : InSobolev 1 f) {M : ℝ}
    (hM : 0 ≤ M) (hfM : hNorm 1 f ≤ M) (k : ℤ) : ‖f k‖ ≤ ‖sobolevEnvelope M k‖ := by
  have hw := (weighted_coeff_bound hf k).trans hfM
  rw [norm_weighted] at hw
  change ‖f k‖ ≤ ‖(M : ℂ) * (weight (-1) k : ℂ)‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hM,
    Complex.norm_real, Real.norm_of_nonneg (weight_pos (-1) k).le, weight_neg]
  have heq : ‖f k‖ = (weight 1 k)⁻¹ * (weight 1 k * ‖f k‖) := by
    rw [← mul_assoc, inv_mul_cancel₀ (weight_pos 1 k).ne', one_mul]
  rw [heq]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr (weight_pos 1 k).le)

/-- The envelope hypothesis in the internally proved normal form follows from
ordinary uniform `H¹` bounds; no uniform higher norm is needed in its conclusion. -/
theorem regularFourierPath_of_h1_bounds {a b M Md : ℝ} (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    {f df : ℝ → Fourier}
    (hc : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b))
    (hdc : ∀ k, ContinuousOn (fun t : ℝ => df t k) (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k, HasDerivAt (fun r : ℝ => f r k) (df t k) t)
    (hb : ∀ t ∈ Set.Icc a b, InSobolev 1 (f t) ∧ hNorm 1 (f t) ≤ M)
    (hdb : ∀ t ∈ Set.Icc a b, InSobolev 1 (df t) ∧ hNorm 1 (df t) ≤ Md) :
    RegularFourierPath a b f df where
  continuous := hc
  derivative_continuous := hdc
  hasDerivAt := hd
  envelope := by
    refine ⟨sobolevEnvelope M, sobolevEnvelope Md, sobolevEnvelope_inSobolev M,
      sobolevEnvelope_inSobolev Md, ?_⟩
    intro t ht k
    exact ⟨h1_coeff_envelope (hb t ht).1 hM (hb t ht).2 k,
      h1_coeff_envelope (hdb t ht).1 hMd (hdb t ht).2 k⟩

set_option maxHeartbeats 800000 in
/-- Smooth inputs supply the regularity of their twisted vector field needed
only to justify normal-form identities. Final estimates use the negative norm. -/
theorem B_h1_of_h2 {f g : Fourier} (hf : InSobolev 2 f) (hg : InSobolev 2 g) (t : ℝ) :
    InSobolev 1 (B t f g) ∧
      hNorm 1 (B t f g) ≤ 4 * h1EmbeddingConstant * hNorm 2 f * hNorm 2 g := by
  have hf1 := (airy_inSobolev hf t).of_le (by norm_num : (1 : ℝ) ≤ 2)
  have hg1 := (airy_inSobolev hg t).of_le (by norm_num : (1 : ℝ) ≤ 2)
  have hfp : InSobolev ((1 : ℝ) + 1) (airy t f) := by
    norm_num
    exact airy_inSobolev hf t
  have hgp : InSobolev ((1 : ℝ) + 1) (airy t g) := by
    norm_num
    exact airy_inSobolev hg t
  have hdf : InSobolev 1 (derivative (airy t f)) := derivative_inSobolev hfp
  have hdg : InSobolev 1 (derivative (airy t g)) := derivative_inSobolev hgp
  have hprod1 := h1_product_bound hdf hg1
  have hprod2 := h1_product_bound hf1 hdg
  have heq := derivative_product hf1 hg1
  have hdprod : InSobolev 1 (derivative (product (airy t f) (airy t g))) := by
    rw [heq]
    exact hprod1.1.add hprod2.1
  refine ⟨airy_inSobolev hdprod (-t), ?_⟩
  rw [B, airy_hNorm, heq]
  calc
    _ ≤ hNorm 1 (product (derivative (airy t f)) (airy t g)) +
        hNorm 1 (product (airy t f) (derivative (airy t g))) := hNorm_add_le hprod1.1 hprod2.1
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 (derivative (airy t f)) * hNorm 1 (airy t g) +
        (2 * h1EmbeddingConstant) * hNorm 1 (airy t f) * hNorm 1 (derivative (airy t g)) :=
      add_le_add hprod1.2 hprod2.2
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g +
        (2 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g := by
      have hC : 0 ≤ 2 * h1EmbeddingConstant := by linarith [h1EmbeddingConstant_ge_one]
      have hfD : hNorm 1 (derivative (airy t f)) ≤ hNorm 2 f := by
        have h := derivative_hNorm hfp
        norm_num at h
        simpa only [airy_hNorm] using h
      have hgD : hNorm 1 (derivative (airy t g)) ≤ hNorm 2 g := by
        have h := derivative_hNorm hgp
        norm_num at h
        simpa only [airy_hNorm] using h
      have hfL : hNorm 1 (airy t f) ≤ hNorm 2 f := by
        simpa only [airy_hNorm] using hNorm_mono (airy_inSobolev hf t) (by norm_num : (1 : ℝ) ≤ 2)
      have hgL : hNorm 1 (airy t g) ≤ hNorm 2 g := by
        simpa only [airy_hNorm] using hNorm_mono (airy_inSobolev hg t) (by norm_num : (1 : ℝ) ≤ 2)
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hfD hC) hgL (hNorm_nonneg _ _)
          (mul_nonneg hC (hNorm_nonneg _ _)))
        (mul_le_mul (mul_le_mul_of_nonneg_left hfL hC) hgD (hNorm_nonneg _ _)
          (mul_nonneg hC (hNorm_nonneg _ _)))
    _ = _ := by ring




theorem weight_one_le_one_add_abs (k : ℤ) : weight 1 k ≤ 1 + |(k : ℝ)| := by
  have h := weight_sq 1 k
  rw [Real.rpow_one] at h
  nlinarith [weight_pos 1 k, abs_nonneg (k : ℝ), sq_abs (k : ℝ)]

/-- A derivative characterization in the actual complete weighted sequence spaces. -/
theorem sobolev_succ_bound {s : ℝ} {f : Fourier} (hf : InSobolev s f)
    (hdf : InSobolev s (derivative f)) :
    InSobolev (s + 1) f ∧ hNorm (s + 1) f ≤ hNorm s f + hNorm s (derivative f) := by
  let F := normWeightedLp s f hf
  let D := normWeightedLp s (derivative f) hdf
  have hb (k : ℤ) : ‖weighted (s + 1) f k‖ ≤ (F + D) k := by
    change ‖weighted (s + 1) f k‖ ≤ ‖weighted s f k‖ + ‖weighted s (derivative f) k‖
    rw [norm_weighted, norm_weighted, norm_weighted, weight_add]
    simp only [derivative, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]
    have h := mul_le_mul_of_nonneg_left (weight_one_le_one_add_abs k)
      (mul_nonneg (weight_pos s k).le (norm_nonneg (f k)))
    simpa only [mul_add, add_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using h
  obtain ⟨hm, hn⟩ := hNorm_le_lp_envelope (F + D) hb
  refine ⟨hm, hn.trans ?_⟩
  calc
    _ ≤ ‖F‖ + ‖D‖ := norm_add_le F D
    _ = _ := by rw [norm_normWeightedLp, norm_normWeightedLp]

theorem inSobolev_succ_iff {s : ℝ} {f : Fourier} :
    InSobolev (s + 1) f ↔ InSobolev s f ∧ InSobolev s (derivative f) := by
  constructor
  · intro hf
    exact ⟨hf.of_le (by linarith), derivative_inSobolev hf⟩
  · rintro ⟨hf, hdf⟩
    exact (sobolev_succ_bound hf hdf).1

theorem inverseDerivative_inSobolev_same {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    InSobolev s (inverseDerivative f) := by
  apply Memℓp.mono' hf
  intro k
  rw [norm_weighted, norm_weighted]
  exact mul_le_mul_of_nonneg_left (inverseDerivative_coeff_norm_le f k) (weight_pos s k).le

theorem inverseDerivative_hNorm_same {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    hNorm s (inverseDerivative f) ≤ hNorm s f := by
  simpa only [one_mul] using hNorm_le_of_weighted_bound hf (by norm_num : (0 : ℝ) ≤ 1)
    (fun k => by
      rw [norm_weighted, norm_weighted, one_mul]
      exact mul_le_mul_of_nonneg_left (inverseDerivative_coeff_norm_le f k) (weight_pos s k).le)

/-- All positive integer Sobolev orders are convolution algebras; no Fourier
support restriction is used in this induction. -/
theorem integer_product_inSobolev (n : ℕ) {f g : Fourier}
    (hf : InSobolev ((n + 1 : ℕ) : ℝ) f) (hg : InSobolev ((n + 1 : ℕ) : ℝ) g) :
    InSobolev ((n + 1 : ℕ) : ℝ) (product f g) := by
  induction n generalizing f g with
  | zero =>
    norm_num at hf hg ⊢
    exact (h1_product_bound hf hg).1
  | succ n ih =>
    have hfp : InSobolev (((n + 1 : ℕ) : ℝ) + 1) f := by
      simpa only [Nat.cast_add, Nat.cast_one] using hf
    have hgp : InSobolev (((n + 1 : ℕ) : ℝ) + 1) g := by
      simpa only [Nat.cast_add, Nat.cast_one] using hg
    obtain ⟨hfl, hfd⟩ := inSobolev_succ_iff.mp hfp
    obtain ⟨hgl, hgd⟩ := inSobolev_succ_iff.mp hgp
    have hf1 : InSobolev 1 f := hfl.of_le (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
    have hg1 : InSobolev 1 g := hgl.of_le (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
    have hder : InSobolev ((n + 1 : ℕ) : ℝ) (derivative (product f g)) := by
      rw [derivative_product hf1 hg1]
      exact (ih hfd hgl).add (ih hfl hgd)
    have hp := (inSobolev_succ_iff).mpr ⟨ih hfl hgl, hder⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hp

/-- An explicit bound supplies continuity of multiplication at order two. -/
theorem h2_product_bound {f g : Fourier} (hf : InSobolev 2 f) (hg : InSobolev 2 g) :
    InSobolev 2 (product f g) ∧
      hNorm 2 (product f g) ≤ 6 * h1EmbeddingConstant * hNorm 2 f * hNorm 2 g := by
  have hf1 := hf.of_le (by norm_num : (1 : ℝ) ≤ 2)
  have hg1 := hg.of_le (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨hp, hpb⟩ := h1_product_bound hf1 hg1
  obtain ⟨hdp, hdpb⟩ := B_h1_of_h2 hf hg 0
  have heq : B 0 f g = derivative (product f g) := by simp [B]
  rw [heq] at hdp hdpb
  have hb := sobolev_succ_bound hp hdp
  norm_num at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 f * hNorm 1 g +
        (4 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g := add_le_add hpb hdpb
    _ ≤ (2 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g +
        (4 * h1EmbeddingConstant) * hNorm 2 f * hNorm 2 g := by
      have hC : 0 ≤ 2 * h1EmbeddingConstant := by linarith [h1EmbeddingConstant_ge_one]
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left (hNorm_mono hf (by norm_num : (1 : ℝ) ≤ 2)) hC)
          (hNorm_mono hg (by norm_num : (1 : ℝ) ≤ 2)) (hNorm_nonneg 1 _)
          (mul_nonneg hC (hNorm_nonneg 2 _))) le_rfl
    _ = _ := by ring




/-- An algebra property, instantiated below by an internal proof. -/
def SobolevAlgebra (s : ℝ) : Prop :=
  ∀ f g : Fourier, InSobolev s f → InSobolev s g → InSobolev s (product f g)

theorem integer_sobolev_algebra (n : ℕ) : SobolevAlgebra ((n + 1 : ℕ) : ℝ) :=
  fun _ _ hf hg => integer_product_inSobolev n hf hg

theorem quadratic_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (quadratic τ f) := by
  have hd := inverseDerivative_inSobolev_same hf
  have ha := airy_inSobolev hd τ
  exact ((removeMean_inSobolev (hAlg _ _ ha ha)).smul (1 / 6 : ℂ)).sub
    ((airy_inSobolev (removeMean_inSobolev (hAlg _ _ hd hd)) τ).smul (1 / 6 : ℂ))

theorem cubicBoundary_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ r : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (cubicBoundary τ r f) := by
  have ha := airy_inSobolev (inverseDerivative_inSobolev_same hf) r
  exact airy_inSobolev (inverseDerivative_inSobolev_same (hAlg _ _ (hAlg _ _ ha ha) ha)) (τ - r)

theorem lastBoundary_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ r : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (lastBoundary τ r f) := by
  have hF := quadratic_in_algebra hAlg τ hf
  have ha := airy_inSobolev (inverseDerivative_inSobolev_same
    (inverseDerivative_inSobolev_same hF)) (r - τ)
  have hb := airy_inSobolev (inverseDerivative_inSobolev_same hf) r
  exact airy_inSobolev (inverseDerivative_inSobolev_same
    (inverseDerivative_inSobolev_same (hAlg _ _ ha hb))) (τ - r)

theorem cubicCorrection_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (cubicCorrection τ f) := by
  have hF := quadratic_in_algebra hAlg τ hf
  have hfirst := (removeMean_inSobolev (hAlg _ _
    (airy_inSobolev (inverseDerivative_inSobolev_same hf) τ)
    (inverseDerivative_inSobolev_same hF))).smul (1 / 3 : ℂ)
  have hsecond := (airy_inSobolev (inverseDerivative_inSobolev_same hf) τ).smul
    ((τ : ℂ) / 9 * mean (product f f))
  have hthird := ((cubicBoundary_in_algebra hAlg τ τ hf).sub
    (cubicBoundary_in_algebra hAlg τ 0 hf)).smul (1 / 54 : ℂ)
  have hfourth := ((lastBoundary_in_algebra hAlg τ τ hf).sub
    (lastBoundary_in_algebra hAlg τ 0 hf)).smul (1 / (27 * (τ : ℂ)))
  exact ((hfirst.add hsecond).sub hthird).sub hfourth

theorem step_in_algebra {s : ℝ} (hAlg : SobolevAlgebra s) (τ : ℝ)
    {f : Fourier} (hf : InSobolev s f) : InSobolev s (step τ f) :=
  ((airy_inSobolev hf τ).add (quadratic_in_algebra hAlg τ hf)).add
    (cubicCorrection_in_algebra hAlg τ hf)

/-- Spatial smoothness of finite iterates is proved for the specified update,
only for the smooth-data part of the proof, with no alteration of the method. -/
theorem numerical_in_integer_sobolev (n : ℕ) (τ : ℝ) {f : Fourier}
    (hf : InSobolev ((n + 1 : ℕ) : ℝ) f) (j : ℕ) :
    InSobolev ((n + 1 : ℕ) : ℝ) (numerical τ f j) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact step_in_algebra (integer_sobolev_algebra n) τ ih




theorem removeMean_coeff_norm_le (f : Fourier) (k : ℤ) : ‖removeMean f k‖ ≤ ‖f k‖ := by
  by_cases hk : k = 0
  · simp [removeMean, hk]
  · simp [removeMean, hk]

/-- Absolute convergence of a bounded coefficient sequence convolved with an
`H¹` input. This is used for the actual nested trilinear operator. -/
theorem bounded_h1_convolution {f g : Fourier} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ k, ‖f k‖ ≤ A) (hg : InSobolev 1 g) (k : ℤ) :
    Summable (fun a : ℤ => f a * g (k - a)) ∧
      ‖product f g k‖ ≤ A * h1EmbeddingConstant * hNorm 1 g := by
  obtain ⟨hgs, hgb⟩ := h1_absolute_coefficients hg
  have hgr : Summable (fun a : ℤ => ‖g (k - a)‖) := (reflectAt k).summable_iff.mpr hgs
  have hen : Summable (fun a : ℤ => A * ‖g (k - a)‖) := hgr.mul_left A
  have hs : Summable (fun a : ℤ => ‖f a * g (k - a)‖) := by
    apply hen.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)
  refine ⟨hs.of_norm, ?_⟩
  calc
    _ ≤ ∑' a : ℤ, ‖f a * g (k - a)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' a : ℤ, A * ‖g (k - a)‖ := by
      apply hs.tsum_le_tsum _ hen
      intro a
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)
    _ = A * ∑' a : ℤ, ‖g (k - a)‖ := tsum_mul_left
    _ = A * ∑' a : ℤ, ‖g a‖ := by
      congr 1
      exact (reflectAt k).tsum_eq (fun a => ‖g a‖)
    _ ≤ A * (h1EmbeddingConstant * hNorm 1 g) := mul_le_mul_of_nonneg_left hgb hA
    _ = _ := by ring

def CIntegrand (t : ℝ) (f g h : Fourier) : Fourier :=
  airy (-t) (removeMean (product (removeMean (product (airy t f) (airy t g)))
    (airy t (inverseDerivative h))))

/-- The nested convolution in (3.13) is absolutely convergent even though its
inner `L² × L²` product need not itself have square-summable coefficients. -/
theorem CIntegrand_summable_bound {f g h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (t : ℝ) (k : ℤ) :
    Summable (fun a : ℤ => removeMean (product (airy t f) (airy t g)) a *
      airy t (inverseDerivative h) (k - a)) ∧
    ‖CIntegrand t f g h k‖ ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * hNorm 0 f * hNorm 0 g * hNorm 0 h := by
  have hb (a : ℤ) : ‖removeMean (product (airy t f) (airy t g)) a‖ ≤ hNorm 0 f * hNorm 0 g := by
    exact (removeMean_coeff_norm_le _ a).trans (by
      simpa only [airy_hNorm] using product_coeff_bound (airy_inSobolev hf t) (airy_inSobolev hg t) a)
  obtain ⟨hs, hn⟩ := bounded_h1_convolution (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g)) hb
    (airy_inSobolev (inverseDerivative_inSobolev_one hh) t) k
  refine ⟨hs, ?_⟩
  have hC : 0 ≤ h1EmbeddingConstant := le_trans zero_le_one h1EmbeddingConstant_ge_one
  have hnon : 0 ≤ (hNorm 0 f * hNorm 0 g) * h1EmbeddingConstant := by
    exact mul_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g)) hC
  calc
    _ = ‖removeMean (product (removeMean (product (airy t f) (airy t g)))
        (airy t (inverseDerivative h))) k‖ := by
      simp only [CIntegrand, airy, norm_mul, airy_multiplier_norm, one_mul]
    _ ≤ ‖product (removeMean (product (airy t f) (airy t g))) (airy t (inverseDerivative h)) k‖ :=
      removeMean_coeff_norm_le _ k
    _ ≤ (hNorm 0 f * hNorm 0 g) * h1EmbeddingConstant * hNorm 1 (inverseDerivative h) := by
      simpa only [airy_hNorm] using hn
    _ ≤ (hNorm 0 f * hNorm 0 g) * h1EmbeddingConstant * (Real.sqrt 2 * hNorm 0 h) :=
      mul_le_mul_of_nonneg_left (inverseDerivative_hNorm_one hh) hnon
    _ = _ := by ring

theorem CIntegral_eq_integrand (a b : ℝ) (f g h : ℝ → Fourier) (k : ℤ) :
    CIntegral a b f g h k = ∫ t : ℝ in a..b, CIntegrand t (f t) (g t) (h t) k := rfl

@[simp] theorem CIntegrand_meanZero (t : ℝ) (f g h : Fourier) : MeanZero (CIntegrand t f g h) := by
  simp [CIntegrand, MeanZero]

theorem CIntegral_meanZero (a b : ℝ) (f g h : ℝ → Fourier) : MeanZero (CIntegral a b f g h) := by
  change (∫ t : ℝ in a..b, CIntegrand t (f t) (g t) (h t) 0) = 0
  simp [CIntegrand, airy, removeMean]




/-- The internal normal-form regularity condition implies the actual weak time
derivative required by the cited trilinear estimate. -/
theorem RegularFourierPath.weakTimeDerivative {a b : ℝ} (hab : a ≤ b)
    {f df : ℝ → Fourier} (hf : RegularFourierPath a b f df) : WeakTimeDerivative a b f df := by
  intro k φ hφ _ hsupp
  have ha : φ a = 0 := by
    by_contra ha
    have hm : a ∈ Function.support φ := ha
    exact (lt_irrefl a) (hsupp hm).1
  have hb : φ b = 0 := by
    by_contra hb
    have hm : b ∈ Function.support φ := hb
    exact (lt_irrefl b) (hsupp hm).2
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcprod : ContinuousOn (fun t : ℝ => (φ t : ℂ) * f t k) (Set.Icc a b) :=
    hcφ.continuousOn.mul (hf.continuous k)
  have hc1 : ContinuousOn (fun t : ℝ => ((deriv φ t : ℝ) : ℂ) * f t k) (Set.Icc a b) :=
    hcDφ.continuousOn.mul (hf.continuous k)
  have hc2 : ContinuousOn (fun t : ℝ => (φ t : ℂ) * df t k) (Set.Icc a b) :=
    hcφ.continuousOn.mul (hf.derivative_continuous k)
  have hi1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hc1
  have hi2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hc2
  have hd (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun r : ℝ => (φ r : ℂ) * f r k)
        (((deriv φ t : ℝ) : ℂ) * f t k + (φ t : ℂ) * df t k) t :=
    ((hφdiff t).hasDerivAt.ofReal_comp).mul (hf.hasDerivAt t ht k)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcprod hd (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  simp only [ha, hb, Complex.ofReal_zero, zero_mul, sub_self] at hFTC
  linear_combination hFTC

/-- Pointwise bounds on a Sobolev-valued path imply the corresponding source
essential bound. No continuity or value-at-endpoints convention is hidden here. -/
theorem sourceLInfinity_le_of_bound {s A : ℝ} (hA : 0 ≤ A) (a b : ℝ)
    (f : ℝ → Sobolev s) (hf : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖f t‖ ≤ A) :
    sourceLInfinity a b f ≤ sourceNormalization * A := by
  have he : eLpNorm f ∞ (volume.restrict (Set.Icc a b)) ≤ ENNReal.ofReal A := by
    simpa only [eLpNorm_exponent_top] using eLpNormEssSup_le_of_ae_bound hf
  unfold sourceLInfinity
  apply mul_le_mul_of_nonneg_left _ sourceNormalization_pos.le
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ENNReal.toReal_ofReal hA] using ht




/-- The reflection and sign change taking the cited source's equation
`U_t = U U_x + U_xxx` to the paper's equation. -/
def reflectSign (f : Fourier) : Fourier := fun k => -f (-k)

@[simp] theorem reflectSign_involutive (f : Fourier) : reflectSign (reflectSign f) = f := by
  funext k
  simp [reflectSign]

@[simp] theorem weight_even (s : ℝ) (k : ℤ) : weight s (-k) = weight s k := by
  simp [weight]

theorem reflectSign_inSobolev {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    InSobolev s (reflectSign f) := by
  have hs := hf.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply memℓp_gen
  have hr := (Equiv.neg ℤ).summable_iff.mpr hs
  simpa only [Function.comp_def, Equiv.neg_apply, norm_weighted, reflectSign, norm_neg, weight_even] using hr

theorem reflectSign_hNorm (s : ℝ) (f : Fourier) : hNorm s (reflectSign f) = hNorm s f := by
  unfold hNorm
  congr 1
  calc
    _ = ∑' k : ℤ, ‖weighted s f (-k)‖ ^ 2 := by
      apply tsum_congr
      intro k
      simp [norm_weighted, reflectSign]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ‖weighted s f k‖ ^ 2)

theorem reflectSign_meanZero {f : Fourier} (hf : MeanZero f) : MeanZero (reflectSign f) := by
  simpa [MeanZero, reflectSign] using hf

theorem reflectSign_real {f : Fourier} (hf : RealValued f) : RealValued (reflectSign f) := by
  intro k
  simp only [reflectSign, neg_neg, map_neg]
  rw [hf k, starRingEnd_self_apply]

theorem reflectSign_airy (t : ℝ) (f : Fourier) :
    reflectSign (airy t f) = airy (-t) (reflectSign f) := by
  funext k
  simp only [reflectSign, airy, Int.cast_neg, Complex.ofReal_neg]
  rw [show Complex.I * (t : ℂ) * (-(k : ℂ)) ^ 3 = Complex.I * (-(t : ℂ)) * (k : ℂ) ^ 3 by ring]
  ring

theorem reflectSign_derivative (f : Fourier) : reflectSign (derivative f) = -derivative (reflectSign f) := by
  funext k
  simp only [reflectSign, derivative, Int.cast_neg, Pi.neg_apply]
  ring

theorem reflectSign_product (f g : Fourier) :
    reflectSign (product f g) = -product (reflectSign f) (reflectSign g) := by
  funext k
  change -(∑' a : ℤ, f a * g (-k - a)) = -(∑' a : ℤ, (-f (-a)) * (-g (-(k - a))))
  congr 1
  calc
    _ = ∑' a : ℤ, f (-a) * g (-k - -a) :=
      ((Equiv.neg ℤ).tsum_eq (fun a : ℤ => f a * g (-k - a))).symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [show -k - -a = -(k - a) by ring]
      ring

@[simp] theorem derivative_neg (f : Fourier) : derivative (-f) = -derivative f := by
  funext k
  simp [derivative]

/-- The full twisted vector field has the source sign after reflection. -/
theorem reflectSign_B (t : ℝ) (f g : Fourier) :
    reflectSign (B (-t) f g) = B t (reflectSign f) (reflectSign g) := by
  unfold B
  rw [reflectSign_airy, reflectSign_derivative, reflectSign_product, derivative_neg,
    neg_neg, reflectSign_airy, reflectSign_airy]
  simp only [neg_neg]




/-- Homogeneous weights used by Babin–Ilyin–Titi, with zero mean required
separately so that the zero frequency contributes nothing. -/
def homogeneousWeight (s : ℝ) (k : ℤ) : ℝ := |(k : ℝ)| ^ s

def homogeneousWeighted (s : ℝ) (f : Fourier) : Fourier := fun k => (homogeneousWeight s k : ℂ) * f k

def InHomSobolev (s : ℝ) (f : Fourier) : Prop :=
  MeanZero f ∧ Memℓp (homogeneousWeighted s f) 2

def homogeneousNorm (s : ℝ) (f : Fourier) : ℝ :=
  Real.sqrt (∑' k : ℤ, ‖homogeneousWeighted s f k‖ ^ 2)

theorem homogeneousNorm_nonneg (s : ℝ) (f : Fourier) : 0 ≤ homogeneousNorm s f := Real.sqrt_nonneg _

theorem norm_homogeneousWeighted (s : ℝ) (f : Fourier) (k : ℤ) :
    ‖homogeneousWeighted s f k‖ = homogeneousWeight s k * ‖f k‖ := by
  simp only [homogeneousWeighted, homogeneousWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (k : ℝ)) s)]

theorem homogeneousNorm_eq_lpNorm {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) :
    homogeneousNorm s f = ‖(⟨homogeneousWeighted s f, hf.2⟩ : L2Seq)‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp [homogeneousNorm, Real.sqrt_eq_rpow]

@[simp] theorem homogeneousWeighted_zero (f : Fourier) : homogeneousWeighted 0 f = f := by
  funext k
  simp [homogeneousWeighted, homogeneousWeight]

@[simp] theorem homogeneousNorm_zero (f : Fourier) : homogeneousNorm 0 f = hNorm 0 f := by
  simp only [homogeneousNorm, homogeneousWeighted_zero, hNorm, weighted_zero]

theorem weight_eq_weightOne_rpow (s : ℝ) (k : ℤ) : weight s k = (weight 1 k) ^ s := by
  unfold weight
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + (k : ℝ) ^ 2)]
  congr 1
  ring

/-- An explicit comparison constant is sufficient for transferring the source
norms; it depends only on the fixed regularity. -/
theorem weight_le_homogeneous {s : ℝ} (hs : 0 ≤ s) {k : ℤ} (hk : k ≠ 0) :
    weight s k ≤ (2 : ℝ) ^ s * homogeneousWeight s k := by
  have hkone : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hw : weight 1 k ≤ 2 * |(k : ℝ)| := (weight_one_le_one_add_abs k).trans (by linarith)
  rw [weight_eq_weightOne_rpow]
  calc
    _ ≤ (2 * |(k : ℝ)|) ^ s := Real.rpow_le_rpow (weight_pos 1 k).le hw hs
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (k : ℝ))]; rfl

theorem InSobolev.to_homogeneous {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InSobolev s f) (hfm : MeanZero f) : InHomSobolev s f := by
  refine ⟨hfm, ?_⟩
  apply Memℓp.mono' hf
  intro k
  rw [norm_homogeneousWeighted, norm_weighted]
  exact mul_le_mul_of_nonneg_right (abs_rpow_le_weight hs k) (norm_nonneg _)

theorem homogeneousNorm_le_hNorm {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InSobolev s f) (hfm : MeanZero f) : homogeneousNorm s f ≤ hNorm s f := by
  rw [homogeneousNorm_eq_lpNorm (hf.to_homogeneous hs hfm), hNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s f k‖ ≤ ‖weighted s f k‖
  rw [norm_homogeneousWeighted, norm_weighted]
  exact mul_le_mul_of_nonneg_right (abs_rpow_le_weight hs k) (norm_nonneg _)

theorem homogeneous_weighted_comparison {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hfm : MeanZero f) (k : ℤ) :
    ‖weighted s f k‖ ≤ (2 : ℝ) ^ s * ‖homogeneousWeighted s f k‖ := by
  by_cases hk : k = 0
  · subst k
    change f 0 = 0 at hfm
    simp [weighted, homogeneousWeighted, hfm]
  · rw [norm_weighted, norm_homogeneousWeighted]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (weight_le_homogeneous hs hk) (norm_nonneg (f k))

theorem InHomSobolev.to_inhomogeneous {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InHomSobolev s f) : InSobolev s f := by
  apply Memℓp.mono' (hf.2.const_smul (((2 : ℝ) ^ s : ℝ) : ℂ))
  intro k
  have hb := homogeneous_weighted_comparison hs hf.1 k
  simpa only [Pi.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)] using hb

theorem hNorm_le_homogeneousNorm {s : ℝ} (hs : 0 ≤ s) {f : Fourier}
    (hf : InHomSobolev s f) : hNorm s f ≤ (2 : ℝ) ^ s * homogeneousNorm s f := by
  have hi := hf.to_inhomogeneous hs
  rw [hNorm_eq_lpNorm hi, homogeneousNorm_eq_lpNorm hf]
  calc
    _ ≤ ‖(((2 : ℝ) ^ s : ℝ) : ℂ) • (⟨homogeneousWeighted s f, hf.2⟩ : L2Seq)‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro k
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)]
        using homogeneous_weighted_comparison hs hf.1 k
    _ = _ := by
      rw [norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)]

theorem homogeneous_reflectSign {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) :
    InHomSobolev s (reflectSign f) := by
  refine ⟨reflectSign_meanZero hf.1, ?_⟩
  apply memℓp_gen
  have h := (Equiv.neg ℤ).summable_iff.mpr (hf.2.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
  simpa only [Function.comp_def, Equiv.neg_apply, norm_homogeneousWeighted,
    homogeneousWeight, reflectSign, Int.cast_neg, abs_neg, norm_neg] using h

theorem homogeneousNorm_reflectSign (s : ℝ) (f : Fourier) :
    homogeneousNorm s (reflectSign f) = homogeneousNorm s f := by
  unfold homogeneousNorm
  congr 1
  calc
    _ = ∑' k : ℤ, ‖homogeneousWeighted s f (-k)‖ ^ 2 := by
      apply tsum_congr
      intro k
      simp [norm_homogeneousWeighted, homogeneousWeight, reflectSign]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ‖homogeneousWeighted s f k‖ ^ 2)




@[simp] theorem homogeneousWeighted_sub (s : ℝ) (f g : Fourier) :
    homogeneousWeighted s (f - g) = homogeneousWeighted s f - homogeneousWeighted s g := by
  funext k
  simp [homogeneousWeighted, mul_sub]

theorem InHomSobolev.sub {s : ℝ} {f g : Fourier} (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    InHomSobolev s (f - g) := by
  refine ⟨?_, ?_⟩
  · change f 0 - g 0 = 0
    rw [hf.1, hg.1, sub_self]
  · rw [homogeneousWeighted_sub]
    exact hf.2.sub hg.2

/-- Norm continuity in the cited source's homogeneous Sobolev spaces. -/
def HomSobolevContinuousOn (s T : ℝ) (v : ℝ → Fourier) : Prop :=
  (∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t)) ∧
    ∀ t ∈ Set.Icc 0 T, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Set.Icc 0 T,
        |r - t| < δ → homogeneousNorm s (v r - v t) < ε

theorem homogeneous_continuity_to_inhomogeneous {s T : ℝ} (hs : 0 ≤ s) {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) : SobolevContinuousOn s T v := by
  refine ⟨fun t ht => (hv.1 t ht).to_inhomogeneous hs, ?_⟩
  intro t ht ε hε
  have hC : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht (ε / (2 : ℝ) ^ s) (div_pos hε hC)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  calc
    _ ≤ (2 : ℝ) ^ s * homogeneousNorm s (v r - v t) :=
      hNorm_le_homogeneousNorm hs ((hv.1 r hr).sub (hv.1 t ht))
    _ < (2 : ℝ) ^ s * (ε / (2 : ℝ) ^ s) := mul_lt_mul_of_pos_left (hb r hr hrt) hC
    _ = ε := by field_simp [hC.ne']

theorem reflectSign_sub (f g : Fourier) : reflectSign (f - g) = reflectSign f - reflectSign g := by
  funext k
  simp only [reflectSign, Pi.sub_apply]
  ring

theorem HomSobolevContinuousOn.reflectSign {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) :
    HomSobolevContinuousOn s T (fun t => KdV.reflectSign (v t)) := by
  refine ⟨fun t ht => homogeneous_reflectSign (hv.1 t ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [← reflectSign_sub, homogeneousNorm_reflectSign]
  exact hb r hr hrt

/-- Definition 3.1 / equation (3.9) in Babin–Ilyin–Titi, retaining the source
phase sign. Membership and continuity hypotheses are stated separately. -/
def SourceTwistedEquation (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ,
    v t k = f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..t, B (-s) (v s) (v s) k

/-- The target equation after conjugation by `S_{-t}`. -/
def TwistedEquation (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ,
    v t k = f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..t, B s (v s) (v s) k

/-- The source-to-target transformation is proved, rather than being silently
incorporated into an external well-posedness assumption. -/
theorem sourceTwisted_to_target {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : SourceTwistedEquation T f v) :
    TwistedEquation T (reflectSign f) (fun t => reflectSign (v t)) := by
  refine ⟨congrArg reflectSign hv.1, ?_⟩
  intro t ht k
  have hs := hv.2 t ht (-k)
  have hi : (∫ s : ℝ in (0 : ℝ)..t, -B (-s) (v s) (v s) (-k)) =
      ∫ s : ℝ in (0 : ℝ)..t, B s (reflectSign (v s)) (reflectSign (v s)) k := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrFun (reflectSign_B s (v s) (v s)) k
  change -v t (-k) = -f (-k) + (1 / 2 : ℂ) * _
  rw [← hi, intervalIntegral.integral_neg]
  linear_combination -hs




/-- The source's coefficient equation is stated only on nonzero modes. -/
def SourceNonzeroEquation (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ, k ≠ 0 →
    v t k = f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..t, B (-s) (v s) (v s) k

theorem SourceNonzeroEquation.all_modes {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : SourceNonzeroEquation T f v) (hfm : MeanZero f)
    (hvm : ∀ t ∈ Set.Icc 0 T, MeanZero (v t)) : SourceTwistedEquation T f v := by
  refine ⟨hv.1, ?_⟩
  intro t ht k
  by_cases hk : k = 0
  · subst k
    rw [hvm t ht, hfm]
    simp [B, airy, derivative]
  · exact hv.2 t ht k hk

theorem source_phase_formula (s : ℝ) (k : ℤ) (f g : Fourier) :
    B (-s) f g k = (Complex.I * (k : ℂ)) *
      ∑' a : ℤ, Complex.exp (Complex.I * (s : ℂ) *
        (3 * (k : ℂ) * (a : ℂ) * ((k - a : ℤ) : ℂ))) * f a * g (k - a) := by
  rw [B_coefficient_series, ← tsum_mul_left]
  apply tsum_congr
  intro a
  unfold BMode oscillation bilinearPhase
  congr 3
  push_cast
  ring_nf

theorem reflectSign_B_reverse (t : ℝ) (f g : Fourier) :
    reflectSign (B t f g) = B (-t) (reflectSign f) (reflectSign g) := by
  simpa only [neg_neg] using reflectSign_B (-t) f g

theorem targetTwisted_to_source {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : TwistedEquation T f v) :
    SourceTwistedEquation T (reflectSign f) (fun t => reflectSign (v t)) := by
  refine ⟨congrArg reflectSign hv.1, ?_⟩
  intro t ht k
  have hs := hv.2 t ht (-k)
  have hi : (∫ s : ℝ in (0 : ℝ)..t, -B s (v s) (v s) (-k)) =
      ∫ s : ℝ in (0 : ℝ)..t, B (-s) (reflectSign (v s)) (reflectSign (v s)) k := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrFun (reflectSign_B_reverse s (v s) (v s)) k
  change -v t (-k) = -f (-k) + (1 / 2 : ℂ) * _
  rw [← hi, intervalIntegral.integral_neg]
  linear_combination -hs

theorem airy_kernel_mul (t s : ℝ) (k : ℤ) :
    Complex.exp (Complex.I * (t : ℂ) * (k : ℂ) ^ 3) *
      Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) =
      Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem untwist_Duhamel {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : TwistedEquation T f v) : Duhamel T f (fun t => airy t (v t)) := by
  refine ⟨?_, ?_⟩
  · simpa only [airy_zero] using hv.1
  · intro t ht k
    let E : ℂ := Complex.exp (Complex.I * (t : ℂ) * (k : ℂ) ^ 3)
    have hi : E * (∫ s : ℝ in (0 : ℝ)..t, B s (v s) (v s) k) =
        ∫ s : ℝ in (0 : ℝ)..t,
          Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
            (Complex.I * (k : ℂ)) * product (airy s (v s)) (airy s (v s)) k := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      change E * (Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) *
        ((Complex.I * (k : ℂ)) * product (airy s (v s)) (airy s (v s)) k)) = _
      rw [← mul_assoc E, airy_kernel_mul]
      ring_nf
    change E * v t k = E * f k + (1 / 2 : ℂ) * _
    rw [hv.2 t ht k]
    calc
      _ = E * f k + (1 / 2 : ℂ) * (E * ∫ s : ℝ in (0 : ℝ)..t, B s (v s) (v s) k) := by ring
      _ = _ := by rw [hi]

/-- Conjugating the paper's Duhamel equation recovers the exact twisted
coefficient equation, without an extra solution premise. -/
theorem twist_Duhamel {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hu : Duhamel T f u) : TwistedEquation T f (fun t => airy (-t) (u t)) := by
  refine ⟨?_, ?_⟩
  · simpa only [neg_zero, airy_zero] using hu.1
  · intro t ht k
    let E : ℂ := Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3)
    have hi : E * (∫ s : ℝ in (0 : ℝ)..t,
          Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
            (Complex.I * (k : ℂ)) * product (u s) (u s) k) =
        ∫ s : ℝ in (0 : ℝ)..t,
          B s (airy (-s) (u s)) (airy (-s) (u s)) k := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only [B]
      rw [airy_inverse_neg]
      change E * (Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
          (Complex.I * (k : ℂ)) * product (u s) (u s) k) =
        Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) *
          ((Complex.I * (k : ℂ)) * product (u s) (u s) k)
      have he : E * Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) =
          Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) := by
        dsimp [E]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      rw [mul_assoc (Complex.exp _) (Complex.I * (k : ℂ)) (product (u s) (u s) k), ← mul_assoc E, he]
    change E * u t k = f k + (1 / 2 : ℂ) * _
    rw [hu.2 t ht k]
    have he : E * airy t f k = f k := by
      change airy (-t) (airy t f) k = f k
      rw [airy_neg_inverse]
    calc
      _ = E * airy t f k + (1 / 2 : ℂ) * (E * ∫ s : ℝ in (0 : ℝ)..t,
          Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
            (Complex.I * (k : ℂ)) * product (u s) (u s) k) := by ring
      _ = _ := by rw [he, hi]




def sobolevRestriction (s T : ℝ) (u : ℝ → Fourier)
    (hu : ∀ t ∈ Set.Icc 0 T, InSobolev s (u t)) : Set.Icc (0 : ℝ) T → Sobolev s :=
  fun t => ⟨u t.val, hu t.val t.property⟩

theorem sobolevRestriction_norm_sub (s T : ℝ) (u : ℝ → Fourier)
    (hu : ∀ t ∈ Set.Icc 0 T, InSobolev s (u t)) (r t : Set.Icc (0 : ℝ) T) :
    ‖sobolevRestriction s T u hu r - sobolevRestriction s T u hu t‖ =
      hNorm s (u r.val - u t.val) := sobolev_norm _

theorem SobolevContinuousOn.continuous_restriction {s T : ℝ} {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) : Continuous (sobolevRestriction s T u hu.1) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t.val t.property ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  rw [dist_eq_norm, sobolevRestriction_norm_sub]
  exact hb r.val r.property (by simpa only [Subtype.dist_eq, Real.dist_eq] using hr)

theorem sobolevContinuousOn_of_restriction {s T : ℝ} {u : ℝ → Fourier}
    (hu : ∀ t ∈ Set.Icc 0 T, InSobolev s (u t))
    (hc : Continuous (sobolevRestriction s T u hu)) : SobolevContinuousOn s T u := by
  refine ⟨hu, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuous_iff.mp hc ⟨t, ht⟩ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  have hd : dist (⟨r, hr⟩ : Set.Icc (0 : ℝ) T) ⟨t, ht⟩ < δ := by
    simpa only [Subtype.dist_eq, Real.dist_eq] using hrt
  have h := hb ⟨r, hr⟩ hd
  simpa only [dist_eq_norm, sobolevRestriction_norm_sub] using h

set_option maxHeartbeats 800000 in
theorem SobolevContinuousOn.airy_path {s T : ℝ} {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) (a : ℝ → ℝ) (ha : Continuous a) :
    SobolevContinuousOn s T (fun t => airy (a t) (u t)) := by
  have hm : ∀ t ∈ Set.Icc 0 T, InSobolev s (airy (a t) (u t)) :=
    fun t ht => airy_inSobolev (hu.1 t ht) (a t)
  apply sobolevContinuousOn_of_restriction hm
  have heq : sobolevRestriction s T (fun t => airy (a t) (u t)) hm =
      (fun t : Set.Icc (0 : ℝ) T => airyMap s (a t.val) (sobolevRestriction s T u hu.1 t)) := by
    funext t
    apply Sobolev.ext
    rfl
  rw [heq]
  have hcTime : Continuous (fun t : Set.Icc (0 : ℝ) T => a t.val) :=
    ha.comp continuous_subtype_val
  have hcData : Continuous (sobolevRestriction s T u hu.1) := hu.continuous_restriction
  have hcPair : Continuous (fun t : Set.Icc (0 : ℝ) T => (a t.val, sobolevRestriction s T u hu.1 t)) :=
    hcTime.prodMk hcData
  exact (continuous_airy_action s).comp hcPair

theorem SobolevContinuousOn.of_le {s r T : ℝ} (hsr : s ≤ r) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn r T u) : SobolevContinuousOn s T u := by
  refine ⟨fun t ht => (hu.1 t ht).of_le hsr, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  exact (hNorm_mono ((hu.1 r hr).sub (hu.1 t ht)) hsr).trans_lt (hb r hr hrt)

theorem inhomogeneous_continuity_to_homogeneous {s T : ℝ} (hs : 0 ≤ s) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) (hum : ∀ t ∈ Set.Icc 0 T, MeanZero (u t)) :
    HomSobolevContinuousOn s T u := by
  refine ⟨fun t ht => (hu.1 t ht).to_homogeneous hs (hum t ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  have hm : MeanZero (u r - u t) := by
    change u r 0 - u t 0 = 0
    rw [hum r hr, hum t ht, sub_self]
  exact (homogeneousNorm_le_hNorm hs ((hu.1 r hr).sub (hu.1 t ht)) hm).trans_lt (hb r hr hrt)




/-- Source regularity and its original coefficient equation give exactly the
paper's Sobolev Duhamel solution after the proved reflection and Airy changes. -/
theorem source_solution_to_kdv {s T : ℝ} (hs : 0 ≤ s) {f : Fourier} {v : ℝ → Fourier}
    (hf : InHomSobolev s f) (hEq : SourceNonzeroEquation T f v)
    (hc : HomSobolevContinuousOn s T v) (hr : ∀ t ∈ Set.Icc 0 T, RealValued (v t)) :
    KdVSolution s T (reflectSign f) (fun t => airy t (reflectSign (v t))) := by
  have hm : ∀ t ∈ Set.Icc 0 T, MeanZero (v t) := fun t ht => (hc.1 t ht).1
  have htarget := sourceTwisted_to_target (hEq.all_modes hf.1 hm)
  have hcont := homogeneous_continuity_to_inhomogeneous hs hc.reflectSign
  refine ⟨hcont.airy_path id continuous_id, untwist_Duhamel htarget, ?_⟩
  intro t ht
  refine ⟨(reflectSign_real (hr t ht)).airy t, ?_⟩
  change airy t (reflectSign (v t)) 0 = 0
  rw [airy_mean]
  exact reflectSign_meanZero (hm t ht)

/-- Conversely every target Sobolev solution has the source coefficient
representation. This is needed when applying source uniqueness and dependence
results to the solution quantified in Theorem 1. -/
theorem kdv_solution_to_source {s T : ℝ} (hs : 0 ≤ s) {f : Fourier} {u : ℝ → Fourier}
    (hu : KdVSolution s T f u) :
    SourceNonzeroEquation T (reflectSign f) (fun t => reflectSign (airy (-t) (u t))) ∧
    HomSobolevContinuousOn s T (fun t => reflectSign (airy (-t) (u t))) ∧
    ∀ t ∈ Set.Icc 0 T, RealValued (reflectSign (airy (-t) (u t))) := by
  have hEq := targetTwisted_to_source (twist_Duhamel hu.2.1)
  have hc := hu.1.airy_path (fun t : ℝ => -t) continuous_neg
  have hm : ∀ t ∈ Set.Icc 0 T, MeanZero (airy (-t) (u t)) := by
    intro t ht
    change airy (-t) (u t) 0 = 0
    rw [airy_mean]
    exact (hu.2.2 t ht).2
  refine ⟨⟨hEq.1, fun t ht k _ => hEq.2 t ht k⟩,
    (inhomogeneous_continuity_to_homogeneous hs hc hm).reflectSign, ?_⟩
  intro t ht
  exact reflectSign_real ((hu.2.2 t ht).1.airy (-t))

def sourceFrame (t : ℝ) (f : Fourier) : Fourier := reflectSign (airy (-t) f)

/-- Exact normalization of the source `L²` distance under the change of frame. -/
theorem sourceFrame_difference_norm (t : ℝ) (f g : Fourier) :
    homogeneousNorm 0 (sourceFrame t f - sourceFrame t g) = hNorm 0 (f - g) := by
  rw [homogeneousNorm_zero]
  change hNorm 0 (reflectSign (airy (-t) f) - reflectSign (airy (-t) g)) = _
  rw [← reflectSign_sub, reflectSign_hNorm, ← airy_sub, airy_hNorm]




theorem fourierCoeff_conjugate (f : Torus → ℂ) (k : ℤ) :
    fourierCoeff (fun x => conj (f x)) k = conj (fourierCoeff f (-k)) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul, neg_neg, fourier_neg]

theorem fourierCoeff_star_lp (F : Lp ℂ 2 normalizedMeasure) (k : ℤ) :
    fourierCoeff (star F : Lp ℂ 2 normalizedMeasure) k = conj (fourierCoeff F (-k)) := by
  calc
    _ = fourierCoeff (fun x => conj (F x)) k :=
      congrFun (fourierCoeff_congr_ae (Lp.coeFn_star F)) k
    _ = _ := fourierCoeff_conjugate F k

theorem normalized_L2_fourier_ext {F G : Lp ℂ 2 normalizedMeasure}
    (h : ∀ k : ℤ, fourierCoeff F k = fourierCoeff G k) : F = G := by
  apply fourierBasis.repr.injective
  apply Subtype.ext
  funext k
  rw [fourierBasis_repr, fourierBasis_repr]
  exact h k

/-- Conjugate symmetry of coefficients is actual reality of the reconstructed
normalized torus `L²` element, not an unrelated predicate on sequences. -/
theorem reconstructL2_star (f : Sobolev 0) (hf : RealValued f.val) :
    star (reconstructL2 f) = reconstructL2 f := by
  apply normalized_L2_fourier_ext
  intro k
  rw [fourierCoeff_star_lp, reconstructL2_coeff, reconstructL2_coeff, hf k]
  simp

theorem reconstructL2_real_ae (f : Sobolev 0) (hf : RealValued f.val) :
    ∀ᵐ x ∂normalizedMeasure, (reconstructL2 f x).im = 0 := by
  have h := Lp.coeFn_star (reconstructL2 f)
  rw [reconstructL2_star f hf] at h
  filter_upwards [h] with x hx
  change reconstructL2 f x = conj (reconstructL2 f x) at hx
  have hi := congrArg Complex.im hx
  simp only [Complex.conj_im] at hi
  linarith

theorem reconstructL2_integrable (f : Sobolev 0) : Integrable (reconstructL2 f) normalizedMeasure := by
  exact (Lp.memLp (reconstructL2 f)).integrable (by norm_num)

theorem reconstructL2_mean (f : Sobolev 0) :
    (∫ x : Torus, reconstructL2 f x ∂normalizedMeasure) = f.val 0 := by
  have h := reconstructL2_coeff f 0
  simpa [fourierCoeff, normalizedMeasure] using h

theorem reconstructL2_meanZero (f : Sobolev 0) (hf : MeanZero f.val) :
    (∫ x : Torus, reconstructL2 f x ∂normalizedMeasure) = 0 := by
  rw [reconstructL2_mean]
  exact hf


theorem real_ae_fourier_symmetry (F : Lp ℂ 2 normalizedMeasure)
    (hf : ∀ᵐ x ∂normalizedMeasure, (F x).im = 0) : RealValued (fourierCoeff F) := by
  have hconj : (fun x => conj (F x)) =ᵐ[normalizedMeasure] F := by
    filter_upwards [hf] with x hx
    apply Complex.ext
    · simp
    · simp [hx]
  have hc := fourierCoeff_congr_ae hconj
  intro k
  calc
    _ = fourierCoeff (fun x => conj (F x)) (-k) := (congrFun hc (-k)).symm
    _ = conj (fourierCoeff F (-(-k))) := fourierCoeff_conjugate F (-k)
    _ = _ := by rw [neg_neg]

theorem reconstructL2_real_iff (f : Sobolev 0) :
    RealValued f.val ↔ ∀ᵐ x ∂normalizedMeasure, (reconstructL2 f x).im = 0 := by
  constructor
  · exact reconstructL2_real_ae f
  · intro h
    have hr := real_ae_fourier_symmetry (reconstructL2 f) h
    intro k
    simpa only [reconstructL2_coeff] using hr k




theorem fourier_character_memLp_top (n : ℤ) : MemLp (fourier n : Torus → ℂ) ∞ normalizedMeasure := by
  exact (memLp_congr_ae (coeFn_fourierLp ∞ n)).mp (Lp.memLp (fourierLp ∞ n))

theorem character_product_memLp (n : ℤ) (F : Lp ℂ 2 normalizedMeasure) :
    MemLp (fun x : Torus => fourier n x * F x) 2 normalizedMeasure :=
  (Lp.memLp F).mul' (fourier_character_memLp_top n)

def characterMultiplyLp (n : ℤ) (F : Lp ℂ 2 normalizedMeasure) : Lp ℂ 2 normalizedMeasure :=
  (character_product_memLp n F).toLp _

theorem characterMultiplyLp_ae (n : ℤ) (F : Lp ℂ 2 normalizedMeasure) :
    characterMultiplyLp n F =ᵐ[normalizedMeasure] (fun x : Torus => fourier n x * F x) :=
  MemLp.coeFn_toLp _

theorem fourierCoeff_character_mul (n a : ℤ) (f : Torus → ℂ) :
    fourierCoeff (fun x => fourier n x * f x) a = fourierCoeff f (a - n) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← fourier_add]
  rw [show -a + n = -(a - n) by omega]

theorem fourierCoeff_characterMultiplyLp (n a : ℤ) (F : Lp ℂ 2 normalizedMeasure) :
    fourierCoeff (characterMultiplyLp n F) a = fourierCoeff F (a - n) := by
  calc
    _ = fourierCoeff (fun x : Torus => fourier n x * F x) a :=
      congrFun (fourierCoeff_congr_ae (characterMultiplyLp_ae n F)) a
    _ = _ := fourierCoeff_character_mul n a F

/-- The actual pointwise product of two normalized torus `L²` functions is
integrable, including for rough data. -/
theorem normalized_L2_product_integrable (F G : Lp ℂ 2 normalizedMeasure) :
    Integrable (fun x : Torus => F x * G x) normalizedMeasure := by
  have h : MemLp (fun x : Torus => F x * G x) 1 normalizedMeasure := (Lp.memLp G).mul' (Lp.memLp F)
  exact memLp_one_iff_integrable.mp h

theorem productCoeff_eq_inner (F G : Lp ℂ 2 normalizedMeasure) (k : ℤ) :
    fourierCoeff (fun x : Torus => F x * G x) k =
      inner ℂ (star F : Lp ℂ 2 normalizedMeasure) (characterMultiplyLp (-k) G) := by
  rw [MeasureTheory.L2.inner_def]
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star F, characterMultiplyLp_ae (-k) G] with x hx hxG
  rw [hx, hxG]
  simp only [smul_eq_mul, RCLike.inner_apply']
  change fourier (-k) x * (F x * G x) = conj (conj (F x)) * (fourier (-k) x * G x)
  rw [starRingEnd_self_apply]
  ring

/-- Exact convolution formula for every pair of `L²` inputs. The proof is
Parseval's identity in the pinned Fourier Hilbert basis, not a formal interchange
of conditionally convergent Fourier series. -/
theorem normalized_L2_product_coeff (F G : Lp ℂ 2 normalizedMeasure) (k : ℤ) :
    fourierCoeff (fun x : Torus => F x * G x) k =
      ∑' a : ℤ, fourierCoeff F a * fourierCoeff G (k - a) := by
  rw [productCoeff_eq_inner]
  calc
    _ = inner ℂ (fourierBasis.repr (star F : Lp ℂ 2 normalizedMeasure))
        (fourierBasis.repr (characterMultiplyLp (-k) G)) :=
      (fourierBasis.repr.inner_map_map _ _).symm
    _ = ∑' a : ℤ, conj (fourierCoeff (star F : Lp ℂ 2 normalizedMeasure) a) *
        fourierCoeff (characterMultiplyLp (-k) G) a := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro a
      simp only [RCLike.inner_apply', fourierBasis_repr]
      rfl
    _ = ∑' a : ℤ, fourierCoeff F (-a) * fourierCoeff G (a + k) := by
      apply tsum_congr
      intro a
      rw [fourierCoeff_star_lp, starRingEnd_self_apply, fourierCoeff_characterMultiplyLp, sub_neg_eq_add]
    _ = _ := by
      simpa only [Equiv.neg_apply, sub_neg_eq_add, add_comm] using
        (Equiv.neg ℤ).tsum_eq (fun a : ℤ => fourierCoeff F a * fourierCoeff G (k - a))

/-- The raw product used in the method and PDE is the Fourier sequence of
physical multiplication, with the prescribed normalized measure. -/
theorem reconstructL2_product_coeff (f g : Sobolev 0) (k : ℤ) :
    fourierCoeff (fun x : Torus => reconstructL2 f x * reconstructL2 g x) k = product f.val g.val k := by
  rw [normalized_L2_product_coeff]
  apply tsum_congr
  intro a
  rw [reconstructL2_coeff, reconstructL2_coeff]




/-- The cited source's Galerkin equation (4.1), with its original phase sign.
The projection belongs to the source's exact-flow construction, not the numerical
method. Classical differentiation is required on the interval interior, with
continuity on the closed interval supplied in the a priori theorem's hypotheses. -/
def SourceGalerkinODE (m : ℕ) (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Ioo 0 T, ∀ k : ℤ,
    HasDerivAt (fun r : ℝ => v r k)
      ((1 / 2 : ℂ) * cutoff m (B (-t) (cutoff m (v t)) (cutoff m (v t))) k) t

/-- Explicit external premise: the a priori estimate clause (4.13) of
Babin–Ilyin–Titi Theorem 4.2, arXiv:0910.1389v2. The dependence on the *actual*
initial homogeneous norm is represented by equality to `r`, with the constant
chosen before the datum and the Galerkin index. This does not assume a bound
uniform over all data of norm at most `r`; that implication remains internal work.
The theorem's unused second-normal-form identity (4.10) is not asserted here. -/
def BITGalerkinEstimate : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ M₀ : ℝ, 0 ≤ M₀ → ∀ T : ℝ, 0 < T → ∀ r : ℝ, 0 ≤ r →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∀ f : Fourier, ∀ v : ℝ → Fourier,
      RealValued f → InHomSobolev s f → homogeneousNorm s f = r → homogeneousNorm 0 f ≤ M₀ →
      HomSobolevContinuousOn s T v → (∀ t ∈ Set.Icc 0 T, RealValued (v t)) →
      SourceGalerkinODE m T f v → ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A




@[simp] theorem homogeneousWeighted_add (s : ℝ) (f g : Fourier) :
    homogeneousWeighted s (f + g) = homogeneousWeighted s f + homogeneousWeighted s g := by
  funext k
  simp [homogeneousWeighted, mul_add]

@[simp] theorem homogeneousWeighted_smul (s : ℝ) (z : ℂ) (f : Fourier) :
    homogeneousWeighted s (z • f) = z • homogeneousWeighted s f := by
  funext k
  simp [homogeneousWeighted, mul_left_comm]

theorem homogeneousWeighted_cutoff (s : ℝ) (m : ℕ) (f : Fourier) :
    homogeneousWeighted s (cutoff m f) = cutoff m (homogeneousWeighted s f) := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [homogeneousWeighted, cutoff, hk]

theorem homogeneousWeighted_real (s : ℝ) {f : Fourier} (hf : RealValued f) :
    RealValued (homogeneousWeighted s f) := by
  intro k
  simp [homogeneousWeighted, homogeneousWeight, hf k]

theorem homogeneousWeight_pos_of_ne_zero (s : ℝ) {k : ℤ} (hk : k ≠ 0) :
    0 < homogeneousWeight s k :=
  Real.rpow_pos_of_pos (abs_pos.mpr (intCast_ne_zero hk)) s

theorem InHomSobolev.of_le {s r : ℝ} {f : Fourier} (hf : InHomSobolev r f) (hsr : s ≤ r) :
    InHomSobolev s f := by
  refine ⟨hf.1, ?_⟩
  apply Memℓp.mono' hf.2
  intro k
  by_cases hk : k = 0
  · subst k
    have hf0 : f 0 = 0 := hf.1
    simp [homogeneousWeighted, hf0]
  · rw [norm_homogeneousWeighted, norm_homogeneousWeighted]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Int.one_le_abs hk) hsr

theorem homogeneousNorm_mono {s r : ℝ} {f : Fourier} (hf : InHomSobolev r f) (hsr : s ≤ r) :
    homogeneousNorm s f ≤ homogeneousNorm r f := by
  rw [homogeneousNorm_eq_lpNorm (hf.of_le hsr), homogeneousNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s f k‖ ≤ ‖homogeneousWeighted r f k‖
  by_cases hk : k = 0
  · subst k
    have hf0 : f 0 = 0 := hf.1
    simp [homogeneousWeighted, hf0]
  · rw [norm_homogeneousWeighted, norm_homogeneousWeighted]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Int.one_le_abs hk) hsr) (norm_nonneg _)

theorem InHomSobolev.cutoff {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) (m : ℕ) :
    InHomSobolev s (KdV.cutoff m f) := by
  refine ⟨cutoff_meanZero hf.1 m, ?_⟩
  apply Memℓp.mono' hf.2
  intro k
  rw [homogeneousWeighted_cutoff]
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp [KdV.cutoff, hk]
  · simp [KdV.cutoff, hk]

theorem homogeneousNorm_cutoff_le {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) (m : ℕ) :
    homogeneousNorm s (cutoff m f) ≤ homogeneousNorm s f := by
  rw [homogeneousNorm_eq_lpNorm (hf.cutoff m), homogeneousNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s (cutoff m f) k‖ ≤ ‖homogeneousWeighted s f k‖
  rw [homogeneousWeighted_cutoff]
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

def homogeneousLp (s : ℝ) (f : Fourier) (hf : InHomSobolev s f) : L2Seq :=
  ⟨homogeneousWeighted s f, hf.2⟩

theorem homogeneousLp_norm (s : ℝ) (f : Fourier) (hf : InHomSobolev s f) :
    ‖homogeneousLp s f hf‖ = homogeneousNorm s f := (homogeneousNorm_eq_lpNorm hf).symm

def homogeneousReconstruct (s : ℝ) (F : L2Seq) : Fourier := fun k =>
  if k = 0 then 0 else (homogeneousWeight s k : ℂ)⁻¹ * F k

theorem homogeneousReconstruct_weighted (s : ℝ) (F : L2Seq) (hF0 : F 0 = 0) :
    homogeneousWeighted s (homogeneousReconstruct s F) = F := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [homogeneousWeighted, homogeneousReconstruct, hF0]
  · simp [homogeneousWeighted, homogeneousReconstruct, hk,
      Complex.ofReal_ne_zero.mpr (homogeneousWeight_pos_of_ne_zero s hk).ne']

theorem homogeneousReconstruct_inHomSobolev (s : ℝ) (F : L2Seq) (hF0 : F 0 = 0) :
    InHomSobolev s (homogeneousReconstruct s F) := by
  refine ⟨by simp [MeanZero, homogeneousReconstruct], ?_⟩
  rw [homogeneousReconstruct_weighted s F hF0]
  exact F.property

theorem homogeneousReconstruct_norm (s : ℝ) (F : L2Seq) (hF0 : F 0 = 0) :
    homogeneousNorm s (homogeneousReconstruct s F) = ‖F‖ := by
  rw [homogeneousNorm_eq_lpNorm (homogeneousReconstruct_inHomSobolev s F hF0)]
  congr 1
  apply Subtype.ext
  exact homogeneousReconstruct_weighted s F hF0

theorem homogeneousReconstruct_real (s : ℝ) (F : L2Seq) (hF : RealValued F.val) :
    RealValued (homogeneousReconstruct s F) := by
  intro k
  by_cases hk : k = 0 <;> simp [homogeneousReconstruct, homogeneousWeight, hk, hF k]




theorem InHomSobolev.add {s : ℝ} {f g : Fourier} (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    InHomSobolev s (f + g) := by
  refine ⟨?_, ?_⟩
  · change f 0 + g 0 = 0
    rw [hf.1, hg.1, add_zero]
  · rw [homogeneousWeighted_add]
    exact hf.2.add hg.2

theorem homogeneousNorm_add_le {s : ℝ} {f g : Fourier} (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    homogeneousNorm s (f + g) ≤ homogeneousNorm s f + homogeneousNorm s g := by
  let F := homogeneousLp s f hf
  let G := homogeneousLp s g hg
  have heq : homogeneousLp s (f + g) (hf.add hg) = F + G := by
    apply Subtype.ext
    exact homogeneousWeighted_add s f g
  rw [← homogeneousLp_norm s (f + g) (hf.add hg), heq, ← homogeneousLp_norm s f hf,
    ← homogeneousLp_norm s g hg]
  exact norm_add_le F G

theorem homogeneousNorm_highCutoff_le {s : ℝ} {f : Fourier} (hf : InHomSobolev s f) (m : ℕ) :
    homogeneousNorm s (highCutoff m f) ≤ homogeneousNorm s f := by
  change homogeneousNorm s (f - cutoff m f) ≤ homogeneousNorm s f
  rw [homogeneousNorm_eq_lpNorm (hf.sub (hf.cutoff m)), homogeneousNorm_eq_lpNorm hf]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  change ‖homogeneousWeighted s (highCutoff m f) k‖ ≤ ‖homogeneousWeighted s f k‖
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp only [homogeneousWeighted, highCutoff, Pi.sub_apply, cutoff, if_pos hk, sub_self, mul_zero, norm_zero]
    exact norm_nonneg _
  · simp [homogeneousWeighted, highCutoff, cutoff, hk]

theorem cutoff_add (m : ℕ) (f g : Fourier) : cutoff m (f + g) = cutoff m f + cutoff m g := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

theorem cutoff_sub (m : ℕ) (f g : Fourier) : cutoff m (f - g) = cutoff m f - cutoff m g := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

@[simp] theorem cutoff_idempotent (m : ℕ) (f : Fourier) : cutoff m (cutoff m f) = cutoff m f := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

theorem HomSobolevContinuousOn.cutoff {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) (m : ℕ) :
    HomSobolevContinuousOn s T (fun t => KdV.cutoff m (v t)) := by
  refine ⟨fun t ht => (hv.1 t ht).cutoff m, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [← cutoff_sub]
  exact (homogeneousNorm_cutoff_le ((hv.1 r hr).sub (hv.1 t ht)) m).trans_lt (hb r hr hrt)

theorem HomSobolevContinuousOn.add_const {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) {g : Fourier} (hg : InHomSobolev s g) :
    HomSobolevContinuousOn s T (fun t => v t + g) := by
  refine ⟨fun t ht => (hv.1 t ht).add hg, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [show (v r + g) - (v t + g) = v r - v t by abel]
  exact hb r hr hrt

/-- Norm continuity entails continuity of every actual Fourier coefficient. -/
theorem SobolevContinuousOn.coeff_continuousOn {s T : ℝ} {v : ℝ → Fourier}
    (hv : SobolevContinuousOn s T v) (k : ℤ) :
    ContinuousOn (fun t : ℝ => v t k) (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht (ε * weight s k) (mul_pos hε (weight_pos s k))
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [dist_eq_norm]
  have hc := weighted_coeff_bound ((hv.1 r hr).sub (hv.1 t ht)) k
  rw [norm_weighted] at hc
  change weight s k * ‖v r k - v t k‖ ≤ hNorm s (v r - v t) at hc
  have hlt := hc.trans_lt (hb r hr (by simpa only [Real.dist_eq] using hrt))
  exact (mul_lt_mul_iff_right₀ (weight_pos s k)).mp (by simpa only [mul_comm] using hlt)




def symmetricSpike (p : ℤ) (a : ℝ) : L2Seq :=
  lp.single 2 p (a : ℂ) + lp.single 2 (-p) (a : ℂ)

theorem symmetricSpike_zero {p : ℤ} (hp : p ≠ 0) (a : ℝ) : symmetricSpike p a 0 = 0 := by
  simp [symmetricSpike, lp.single_apply, hp, eq_comm]

theorem symmetricSpike_real (p : ℤ) (a : ℝ) : RealValued (symmetricSpike p a).val := by
  intro k
  simp only [symmetricSpike, lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply]
  have h₁ : (-k = p) ↔ (k = -p) := by omega
  have h₂ : (-k = -p) ↔ (k = p) := by omega
  simp only [h₁, h₂, map_add]
  split_ifs <;> simp

theorem symmetricSpike_norm_sq {p : ℤ} (hp : p ≠ 0) (a : ℝ) :
    ‖symmetricSpike p a‖ ^ 2 = 2 * a ^ 2 := by
  have hpneg : p ≠ -p := by omega
  have horth : inner ℂ (lp.single 2 p (a : ℂ) : L2Seq) (lp.single 2 (-p) (a : ℂ) : L2Seq) = 0 := by
    rw [lp.inner_single_left]
    simp [lp.single_apply, hpneg]
  have hsq : ‖symmetricSpike p a‖ ^ 2 = ‖(lp.single 2 p (a : ℂ) : L2Seq)‖ ^ 2 +
      ‖(lp.single 2 (-p) (a : ℂ) : L2Seq)‖ ^ 2 := by
    simpa only [symmetricSpike, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [hsq, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_add_symmetricSpike_sq {p : ℤ} (hp : p ≠ 0) (a : ℝ)
    (F : L2Seq) (hFp : F p = 0) (hFm : F (-p) = 0) :
    ‖F + symmetricSpike p a‖ ^ 2 = ‖F‖ ^ 2 + 2 * a ^ 2 := by
  have horth : inner ℂ F (symmetricSpike p a) = 0 := by
    rw [symmetricSpike, inner_add_right, lp.inner_single_right, lp.inner_single_right, hFp, hFm]
    simp
  have hsq : ‖F + symmetricSpike p a‖ ^ 2 = ‖F‖ ^ 2 + ‖symmetricSpike p a‖ ^ 2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [hsq, symmetricSpike_norm_sq hp]

/-- A datum in a homogeneous norm ball can be padded outside any given source
Galerkin projection to lie on the exact norm sphere. The low modes are unchanged,
and reality, zero mean and the `L²` bound are retained. This is solely an exact-
flow argument; no projection or padding is made in the numerical method. -/
theorem homogeneous_sphere_padding {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    {f : Fourier} (hf : InHomSobolev s f) (hfr : RealValued f) (hfR : homogeneousNorm s f ≤ R)
    (m : ℕ) : ∃ g : Fourier,
      RealValued g ∧ InHomSobolev s g ∧ homogeneousNorm s g = R ∧
      homogeneousNorm 0 g ≤ R ∧ cutoff m g = cutoff m f := by
  let p : ℤ := (m : ℤ) + 1
  have hp : p ≠ 0 := by dsimp [p]; omega
  have hpo : p ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by simp [p]
  have hmo : -p ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by simp [p]
  let C : L2Seq := homogeneousLp s (cutoff m f) (hf.cutoff m)
  have hCp : C p = 0 := by
    change homogeneousWeighted s (cutoff m f) p = 0
    rw [homogeneousWeighted_cutoff]
    simp [cutoff, hpo]
  have hCm : C (-p) = 0 := by
    change homogeneousWeighted s (cutoff m f) (-p) = 0
    rw [homogeneousWeighted_cutoff]
    simp [cutoff, hmo]
  have hC0 : C 0 = 0 := by
    change (homogeneousWeight s 0 : ℂ) * cutoff m f 0 = 0
    rw [cutoff_meanZero hf.1 m, mul_zero]
  have hCR : ‖C‖ ≤ R := by
    rw [homogeneousLp_norm]
    exact (homogeneousNorm_cutoff_le hf m).trans hfR
  let a : ℝ := Real.sqrt ((R ^ 2 - ‖C‖ ^ 2) / 2)
  have hRad : 0 ≤ (R ^ 2 - ‖C‖ ^ 2) / 2 := by nlinarith [norm_nonneg C]
  have haSq : a ^ 2 = (R ^ 2 - ‖C‖ ^ 2) / 2 := Real.sq_sqrt hRad
  let Q : L2Seq := C + symmetricSpike p a
  have hQ0 : Q 0 = 0 := by
    change C 0 + symmetricSpike p a 0 = 0
    rw [hC0, symmetricSpike_zero hp, zero_add]
  have hQr : RealValued Q.val :=
    (homogeneousWeighted_real s (cutoff_real hfr m)).add (symmetricSpike_real p a)
  have hQs : ‖Q‖ ^ 2 = R ^ 2 := by
    have h := norm_add_symmetricSpike_sq hp a C hCp hCm
    change ‖Q‖ ^ 2 = ‖C‖ ^ 2 + 2 * a ^ 2 at h
    nlinarith only [h, haSq]
  have hQN : ‖Q‖ = R := by nlinarith [norm_nonneg Q]
  let g : Fourier := homogeneousReconstruct s Q
  have hg := homogeneousReconstruct_inHomSobolev s Q hQ0
  have hgn : homogeneousNorm s g = R := by
    rw [homogeneousReconstruct_norm s Q hQ0, hQN]
  refine ⟨g, homogeneousReconstruct_real s Q hQr, hg, hgn, ?_, ?_⟩
  · exact (homogeneousNorm_mono hg hs).trans_eq hgn
  · funext k
    by_cases hki : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · simp only [cutoff, if_pos hki]
      by_cases hk : k = 0
      · subst k
        have hf0 : f 0 = 0 := hf.1
        simp [g, homogeneousReconstruct, hf0]
      · have hpk : p ≠ k := by intro he; subst k; exact hpo hki
        have hmk : -p ≠ k := by intro he; subst k; exact hmo hki
        have hsk : symmetricSpike p a k = 0 := by simp [symmetricSpike, lp.single_apply, hpk, hmk]
        have hQk : Q k = (homogeneousWeight s k : ℂ) * f k := by
          change C k + symmetricSpike p a k = _
          rw [hsk, add_zero]
          change (homogeneousWeight s k : ℂ) * cutoff m f k = _
          simp [cutoff, hki]
        change (if k = 0 then 0 else (homogeneousWeight s k : ℂ)⁻¹ * Q k) = f k
        rw [if_neg hk, hQk, ← mul_assoc,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (homogeneousWeight_pos_of_ne_zero s hk).ne'), one_mul]
    · simp [cutoff, hki]




theorem SourceGalerkinODE.outside {s T : ℝ} (hs : 0 ≤ s) {m : ℕ}
    {f : Fourier} {v : ℝ → Fourier} (hv : SourceGalerkinODE m T f v)
    (hc : HomSobolevContinuousOn s T v) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (k : ℤ) (hk : k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ)) : v t k = f k := by
  have hcont := (homogeneous_continuity_to_inhomogeneous hs hc).coeff_continuousOn k
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hd (r : ℝ) (hr : r ∈ Set.Ioo 0 t) : HasDerivAt (fun z : ℝ => v z k) (0 : ℂ) r := by
    have h := hv.2 r ⟨hr.1, hr.2.trans_le ht.2⟩ k
    simpa only [cutoff, if_neg hk, mul_zero] using h
  have hi : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 t := continuous_const.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hcont.mono hsub) hd hi
  simp only [intervalIntegral.integral_zero] at hFTC
  have h₀ := congrFun hv.1 k
  linear_combination -hFTC + h₀

theorem SourceGalerkinODE.tail_stationary {s T : ℝ} (hs : 0 ≤ s) {m : ℕ}
    {f : Fourier} {v : ℝ → Fourier} (hv : SourceGalerkinODE m T f v)
    (hc : HomSobolevContinuousOn s T v) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    highCutoff m (v t) = highCutoff m f := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp [highCutoff, cutoff, hk]
  · simpa only [highCutoff, Pi.sub_apply, cutoff, if_neg hk, sub_zero] using hv.outside hs hc ht k hk

def sourcePaddedFlow (m : ℕ) (f g : Fourier) (v : ℝ → Fourier) (t : ℝ) : Fourier :=
  cutoff m (v t) + (g - cutoff m f)

theorem sourcePaddedFlow_low (m : ℕ) (f g : Fourier) (v : ℝ → Fourier)
    (hg : cutoff m g = cutoff m f) (t : ℝ) :
    cutoff m (sourcePaddedFlow m f g v t) = cutoff m (v t) := by
  rw [sourcePaddedFlow, cutoff_add, cutoff_sub, cutoff_idempotent, hg, cutoff_idempotent, sub_self, add_zero]

theorem sourcePaddedFlow_continuous {s T : ℝ} {m : ℕ} {f g : Fourier} {v : ℝ → Fourier}
    (hf : InHomSobolev s f) (hg : InHomSobolev s g) (hc : HomSobolevContinuousOn s T v) :
    HomSobolevContinuousOn s T (sourcePaddedFlow m f g v) :=
  (hc.cutoff m).add_const (hg.sub (hf.cutoff m))

theorem sourcePaddedFlow_real {T : ℝ} {m : ℕ} {f g : Fourier} {v : ℝ → Fourier}
    (hf : RealValued f) (hg : RealValued g) (hv : ∀ t ∈ Set.Icc 0 T, RealValued (v t)) :
    ∀ t ∈ Set.Icc 0 T, RealValued (sourcePaddedFlow m f g v t) := by
  intro t ht
  exact (cutoff_real (hv t ht) m).add (hg.sub (cutoff_real hf m))

theorem SourceGalerkinODE.padded {T : ℝ} {m : ℕ} {f g : Fourier} {v : ℝ → Fourier}
    (hv : SourceGalerkinODE m T f v) (hg : cutoff m g = cutoff m f) :
    SourceGalerkinODE m T g (sourcePaddedFlow m f g v) := by
  refine ⟨?_, ?_⟩
  · change cutoff m (v 0) + (g - cutoff m f) = g
    rw [hv.1]
    abel
  · intro t ht k
    rw [sourcePaddedFlow_low m f g v hg t]
    by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · have heq : (fun r : ℝ => sourcePaddedFlow m f g v r k) =
          (fun r : ℝ => v r k + (g - cutoff m f) k) := by
        funext r
        simp only [sourcePaddedFlow, Pi.add_apply, cutoff, if_pos hk]
      rw [heq]
      exact (hv.2 t ht k).add_const ((g - cutoff m f) k)
    · have heq : (fun r : ℝ => sourcePaddedFlow m f g v r k) =
          (fun _ : ℝ => (g - cutoff m f) k) := by
        funext r
        simp only [sourcePaddedFlow, Pi.add_apply, cutoff, if_neg hk, zero_add]
      rw [heq]
      simp only [cutoff, if_neg hk, mul_zero]
      exact hasDerivAt_const t ((g - cutoff m f) k)

/-- Uniformity over a homogeneous initial-data ball is *derived* from the
fixed-actual-norm source estimate, by padding the stationary source Galerkin tail.
The constant is chosen before every datum, flow and Galerkin index. -/
theorem uniform_source_galerkin_bound (externalGalerkin : BITGalerkinEstimate)
    {s T R : ℝ} (hs : 0 ≤ s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 0 < m → ∀ f : Fourier, ∀ v : ℝ → Fourier,
      RealValued f → InHomSobolev s f → homogeneousNorm s f ≤ R →
      HomSobolevContinuousOn s T v → (∀ t ∈ Set.Icc 0 T, RealValued (v t)) →
      SourceGalerkinODE m T f v → ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hbound⟩ := externalGalerkin s hs R hR.le T hT R hR.le
  refine ⟨A + R, by linarith, ?_⟩
  intro m hm f v hfr hf hfR hc hvr hODE t ht
  obtain ⟨g, hgr, hg, hgN, hg0, hgLow⟩ := homogeneous_sphere_padding hs hR.le hf hfr hfR m
  have hpc := sourcePaddedFlow_continuous (m := m) hf hg hc
  have hpr := sourcePaddedFlow_real (m := m) hfr hgr hvr
  have hpODE := hODE.padded hgLow
  have hpb := hbound m hm g (sourcePaddedFlow m f g v) hgr hg hgN hg0 hpc hpr hpODE
  have hLow : homogeneousNorm s (cutoff m (v t)) ≤ A := by
    calc
      _ = homogeneousNorm s (cutoff m (sourcePaddedFlow m f g v t)) := by
        rw [sourcePaddedFlow_low m f g v hgLow t]
      _ ≤ homogeneousNorm s (sourcePaddedFlow m f g v t) := homogeneousNorm_cutoff_le (hpc.1 t ht) m
      _ ≤ A := hpb t ht
  have hTail : homogeneousNorm s (highCutoff m (v t)) ≤ R := by
    rw [hODE.tail_stationary hs hc ht]
    exact (homogeneousNorm_highCutoff_le hf m).trans hfR
  calc
    _ = homogeneousNorm s (cutoff m (v t) + highCutoff m (v t)) := by
      congr 1
      unfold highCutoff
      abel
    _ ≤ homogeneousNorm s (cutoff m (v t)) + homogeneousNorm s (highCutoff m (v t)) :=
      homogeneousNorm_add_le ((hc.1 t ht).cutoff m) ((hc.1 t ht).sub ((hc.1 t ht).cutoff m))
    _ ≤ A + R := add_le_add hLow hTail




theorem homogeneousNorm_sq (s : ℝ) (f : Fourier) :
    homogeneousNorm s f ^ 2 = ∑' k : ℤ, ‖homogeneousWeighted s f k‖ ^ 2 := by
  exact Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)

/-- Lower semicontinuity of the full homogeneous norm under coefficientwise
convergence. In particular no bound on a finite projection replaces the target
Sobolev norm, and membership of the limit is proved. -/
theorem homogeneous_norm_limit {s A : ℝ} (hA : 0 ≤ A) {f : ℕ → Fourier} {g : Fourier}
    (hf : ∀ n, InHomSobolev s (f n)) (hb : ∀ n, homogeneousNorm s (f n) ≤ A)
    (hc : ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f n k) Filter.atTop (nhds (g k))) :
    InHomSobolev s g ∧ homogeneousNorm s g ≤ A := by
  have hzero : g 0 = 0 := by
    have hz : Filter.Tendsto (fun n : ℕ => f n 0) Filter.atTop (nhds (0 : ℂ)) := by
      have heq : (fun n : ℕ => f n 0) = (fun _ : ℕ => (0 : ℂ)) :=
        funext (fun n => (hf n).1)
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hc 0) hz
  have hdot (k : ℤ) : Filter.Tendsto (fun n : ℕ => homogeneousWeighted s (f n) k)
      Filter.atTop (nhds (homogeneousWeighted s g k)) := by
    exact tendsto_const_nhds.mul (hc k)
  have hfin (K : Finset ℤ) : (∑ k ∈ K, ‖homogeneousWeighted s g k‖ ^ 2) ≤ A ^ 2 := by
    have ht : Filter.Tendsto (fun n : ℕ => ∑ k ∈ K, ‖homogeneousWeighted s (f n) k‖ ^ 2)
        Filter.atTop (nhds (∑ k ∈ K, ‖homogeneousWeighted s g k‖ ^ 2)) :=
      tendsto_finsetSum K (fun k _ => (hdot k).norm.pow 2)
    apply le_of_tendsto ht (Filter.Eventually.of_forall ?_)
    intro n
    have hsum : Summable (fun k : ℤ => ‖homogeneousWeighted s (f n) k‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hf n).2.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    calc
      _ ≤ ∑' k : ℤ, ‖homogeneousWeighted s (f n) k‖ ^ 2 :=
        hsum.sum_le_tsum K (fun _ _ => sq_nonneg _)
      _ = homogeneousNorm s (f n) ^ 2 := (homogeneousNorm_sq s (f n)).symm
      _ ≤ A ^ 2 := (sq_le_sq₀ (homogeneousNorm_nonneg s (f n)) hA).mpr (hb n)
  have hs : Summable (fun k : ℤ => ‖homogeneousWeighted s g k‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfin
  have hm : InHomSobolev s g := ⟨hzero, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)⟩
  refine ⟨hm, ?_⟩
  apply (sq_le_sq₀ (homogeneousNorm_nonneg s g) hA).mp
  rw [homogeneousNorm_sq]
  exact Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfin

theorem realValued_of_coefficient_limit {f : ℕ → Fourier} {g : Fourier}
    (hf : ∀ n, RealValued (f n))
    (hc : ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f n k) Filter.atTop (nhds (g k))) : RealValued g := by
  intro k
  have hconj : Filter.Tendsto (fun n : ℕ => conj (f n k)) Filter.atTop (nhds (conj (g k))) :=
    continuous_star.continuousAt.tendsto.comp (hc k)
  have heq : (fun n : ℕ => f n (-k)) = (fun n : ℕ => conj (f n k)) :=
    funext (fun n => hf n k)
  rw [← heq] at hconj
  exact tendsto_nhds_unique (hc (-k)) hconj




theorem abs_homogeneousNorm_sub_le {s : ℝ} {f g : Fourier}
    (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    |homogeneousNorm s f - homogeneousNorm s g| ≤ homogeneousNorm s (f - g) := by
  let F := homogeneousLp s f hf
  let G := homogeneousLp s g hg
  have hsub : homogeneousLp s (f - g) (hf.sub hg) = F - G := by
    apply Subtype.ext
    exact homogeneousWeighted_sub s f g
  calc
    _ = |‖F‖ - ‖G‖| := by rw [homogeneousLp_norm, homogeneousLp_norm]
    _ ≤ ‖F - G‖ := abs_norm_sub_norm_le F G
    _ = _ := by rw [← hsub, homogeneousLp_norm]

theorem HomSobolevContinuousOn.norm_continuousOn {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) : ContinuousOn (fun t => homogeneousNorm s (v t)) (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [Real.dist_eq]
  exact (abs_homogeneousNorm_sub_le (hv.1 r hr) (hv.1 t ht)).trans_lt
    (hb r hr (by simpa only [Real.dist_eq] using hrt))

/-- Almost-everywhere bounds on a continuous homogeneous norm hold also at
both endpoints of the positive time interval. -/
theorem homogeneous_bound_of_ae {s T A : ℝ} (hT : 0 < T) {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v)
    (hb : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A) :
    ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  have heq : (fun t : ℝ => min (homogeneousNorm s (v t)) A) =ᵐ[volume.restrict (Set.Icc 0 T)]
      (fun t : ℝ => homogeneousNorm s (v t)) := hb.mono (fun _ ht => min_eq_left ht)
  have hcN := hv.norm_continuousOn
  have hcM : ContinuousOn (fun t : ℝ => min (homogeneousNorm s (v t)) A) (Set.Icc 0 T) :=
    hcN.inf continuousOn_const
  have hset : (Set.Icc (0 : ℝ) T) ⊆ closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo hT.ne]
  have hall := Measure.eqOn_of_ae_eq heq hcM hcN hset
  intro t ht
  exact min_eq_left_iff.mp (hall ht)

/-- The finite-frequency limit argument transfers a uniform Galerkin bound to
a continuous limiting flow. The coefficient convergence is an explicit internal
hypothesis to be obtained from the cited strong-in-time convergence theorem. -/
theorem homogeneous_uniform_limit_bound {s T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    {f : ℕ → ℝ → Fourier} {v : ℝ → Fourier}
    (hf : ∀ n, ∀ t ∈ Set.Icc 0 T, InHomSobolev s (f n t))
    (hb : ∀ n, ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (f n t) ≤ A)
    (hv : HomSobolevContinuousOn s T v)
    (hc : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f n t k) Filter.atTop (nhds (v t k))) :
    ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  apply homogeneous_bound_of_ae hT hv
  filter_upwards [hc, ae_restrict_mem measurableSet_Icc] with t ht htc
  exact (homogeneous_norm_limit hA (fun n => hf n t htc) (fun n => hb n t htc) ht).2




theorem homogeneous_coeff_bound {s : ℝ} {f : Fourier} (hf : InHomSobolev s f)
    {k : ℤ} (hk : k ≠ 0) :
    ‖f k‖ ≤ (homogeneousWeight s k)⁻¹ * homogeneousNorm s f := by
  have h : ‖homogeneousWeighted s f k‖ ≤ homogeneousNorm s f := by
    rw [homogeneousNorm_eq_lpNorm hf]
    exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ⟨homogeneousWeighted s f, hf.2⟩ k
  rw [norm_homogeneousWeighted] at h
  calc
    _ = (homogeneousWeight s k)⁻¹ * (homogeneousWeight s k * ‖f k‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (homogeneousWeight_pos_of_ne_zero s hk).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (homogeneousWeight_pos_of_ne_zero s hk).le)

/-- Strong `L²` time convergence in a source homogeneous Sobolev norm supplies
an almost-everywhere coefficientwise convergent subsequence. This implication
uses pinned Mathlib convergence-in-measure results, not an extra source premise. -/
theorem homogeneous_L2_time_subsequence {s T : ℝ} {f : ℕ → ℝ → Fourier} {v : ℝ → Fourier}
    (hf : ∀ n, ∀ t ∈ Set.Icc 0 T, InHomSobolev s (f n t))
    (hv : ∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t))
    (hmeas : ∀ n, AEStronglyMeasurable (fun t : ℝ => homogeneousNorm s (f n t - v t))
      (volume.restrict (Set.Icc 0 T)))
    (hconv : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm s (f n t - v t)) 2
        (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => f (ns n) t k) Filter.atTop (nhds (v t k)) := by
  have hnorm : Filter.Tendsto
      (fun n : ℕ => eLpNorm ((fun t : ℝ => homogeneousNorm s (f n t - v t)) - (fun _ : ℝ => (0 : ℝ)))
        2 (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0) := by
    have heq (n : ℕ) : ((fun t : ℝ => homogeneousNorm s (f n t - v t)) -
        (fun _ : ℝ => (0 : ℝ))) = (fun t : ℝ => homogeneousNorm s (f n t - v t)) := by
      funext t
      exact sub_zero _
    simp_rw [heq]
    exact hconv
  have him : TendstoInMeasure (volume.restrict (Set.Icc 0 T))
      (fun n t => homogeneousNorm s (f n t - v t)) Filter.atTop (fun _ : ℝ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hmeas aestronglyMeasurable_const hnorm
  obtain ⟨ns, hns, hlim⟩ := him.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim, ae_restrict_mem measurableSet_Icc] with t ht htc
  intro k
  by_cases hk : k = 0
  · subst k
    have heq : (fun n : ℕ => f (ns n) t 0) = (fun _ : ℕ => (0 : ℂ)) :=
      funext (fun n => (hf (ns n) t htc).1)
    rw [heq, show v t 0 = 0 from (hv t htc).1]
    exact tendsto_const_nhds
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb (n : ℕ) : ‖f (ns n) t k - v t k‖ ≤
        (homogeneousWeight s k)⁻¹ * homogeneousNorm s (f (ns n) t - v t) :=
      homogeneous_coeff_bound ((hf (ns n) t htc).sub (hv t htc)) hk
    exact squeeze_zero (fun _ => norm_nonneg _) hb
      (by simpa only [mul_zero] using tendsto_const_nhds.mul ht)




/-- Combining the internally derived initial-ball Galerkin bound with strong
convergence in a weaker source norm gives the same uniform bound on the limiting
continuous flow. All constants precede the datum, flow, approximation family and
its index map. The time convergence concerns the cited exact-flow construction,
not the numerical method. -/
theorem uniform_source_limiting_bound (externalGalerkin : BITGalerkinEstimate)
    {s T R : ℝ} (hs : 0 ≤ s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ : ℝ, σ ≤ s → ∀ f : Fourier,
      RealValued f → InHomSobolev s f → homogeneousNorm s f ≤ R →
      ∀ v : ℝ → Fourier, HomSobolevContinuousOn s T v →
      ∀ G : ℕ → ℝ → Fourier, ∀ idx : ℕ → ℕ, (∀ n, 0 < idx n) →
      (∀ n, HomSobolevContinuousOn s T (G n)) →
      (∀ n, ∀ t ∈ Set.Icc 0 T, RealValued (G n t)) →
      (∀ n, SourceGalerkinODE (idx n) T f (G n)) →
      (∀ n, AEStronglyMeasurable (fun t : ℝ => homogeneousNorm σ (G n t - v t))
        (volume.restrict (Set.Icc 0 T))) →
      Filter.Tendsto
        (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm σ (G n t - v t)) 2
          (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0) →
        ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hb⟩ := uniform_source_galerkin_bound externalGalerkin hs hT hR
  refine ⟨A, hA, ?_⟩
  intro σ hσ f hfr hf hfR v hv G idx hidx hGC hGR hGODE hmeas hconv
  have hBound (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) : homogeneousNorm s (G n t) ≤ A :=
    hb (idx n) (hidx n) f (G n) hfr hf hfR (hGC n) (hGR n) (hGODE n) t ht
  obtain ⟨ns, hns, hcoeff⟩ := homogeneous_L2_time_subsequence
    (fun n t ht => ((hGC n).1 t ht).of_le hσ) (fun t ht => (hv.1 t ht).of_le hσ) hmeas hconv
  exact homogeneous_uniform_limit_bound hT hA.le
    (fun n t ht => (hGC (ns n)).1 t ht) (fun n t ht => hBound (ns n) t ht) hv hcoeff




def HomogeneousEssentiallyBounded (s T : ℝ) (v : ℝ → Fourier) : Prop :=
  ∃ w : ℝ → L2Seq, MemLp w ∞ (volume.restrict (Set.Icc 0 T)) ∧
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), MeanZero (v t) ∧ (w t).val = homogeneousWeighted s (v t)

theorem HomogeneousEssentiallyBounded.inHom_ae {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomogeneousEssentiallyBounded s T v) :
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), InHomSobolev s (v t) := by
  obtain ⟨w, hw, heq⟩ := hv
  filter_upwards [heq] with t ht
  refine ⟨ht.1, ?_⟩
  rw [← ht.2]
  exact (w t).property

def homogeneousTrajectory (s T : ℝ) (v : ℝ → Fourier)
    (hv : ∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t)) (t : ℝ) : L2Seq :=
  if ht : t ∈ Set.Icc 0 T then homogeneousLp s (v t) (hv t ht) else 0

theorem homogeneousTrajectory_norm_sub (s T : ℝ) (v : ℝ → Fourier)
    (hv : ∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t)) {r t : ℝ}
    (hr : r ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T) :
    ‖homogeneousTrajectory s T v hv r - homogeneousTrajectory s T v hv t‖ = homogeneousNorm s (v r - v t) := by
  simp only [homogeneousTrajectory, dif_pos hr, dif_pos ht]
  have heq : homogeneousLp s (v r - v t) ((hv r hr).sub (hv t ht)) =
      homogeneousLp s (v r) (hv r hr) - homogeneousLp s (v t) (hv t ht) := by
    apply Subtype.ext
    exact homogeneousWeighted_sub s (v r) (v t)
  rw [← heq, homogeneousLp_norm]

theorem HomSobolevContinuousOn.continuous_homogeneousTrajectory {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) :
    ContinuousOn (homogeneousTrajectory s T v hv.1) (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [dist_eq_norm, homogeneousTrajectory_norm_sub s T v hv.1 hr ht]
  exact hb r hr (by simpa only [Real.dist_eq] using hrt)

/-- Continuous homogeneous paths have actual `L∞` representatives in time;
this is proved rather than assumed when applying the cited weak-flow results. -/
theorem HomSobolevContinuousOn.essentiallyBounded {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) : HomogeneousEssentiallyBounded s T v := by
  let w := homogeneousTrajectory s T v hv.1
  have hc : ContinuousOn w (Set.Icc 0 T) := hv.continuous_homogeneousTrajectory
  have hbd : BddAbove ((fun t : ℝ => ‖w t‖) '' Set.Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn hc.norm).bddAbove
  obtain ⟨B, hB⟩ := hbd
  have hw : MemLp w ∞ (volume.restrict (Set.Icc 0 T)) :=
    MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) B (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hB ⟨t, ht, rfl⟩)
  refine ⟨w, hw, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  refine ⟨(hv.1 t ht).1, ?_⟩
  simp only [w, homogeneousTrajectory, dif_pos ht, homogeneousLp]

theorem HomSobolevContinuousOn.of_le {s r T : ℝ} (hsr : s ≤ r) {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn r T v) : HomSobolevContinuousOn s T v := by
  refine ⟨fun t ht => (hv.1 t ht).of_le hsr, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  exact (homogeneousNorm_mono ((hv.1 r hr).sub (hv.1 t ht)) hsr).trans_lt (hb r hr hrt)

/-- The cited source's mean-zero real weak solution class, in the precise
integrated Fourier representation of Definition 3.1. Its time-space requirement
is actual essential boundedness in the complete weighted `ℓ²` space. -/
def SourceWeakSolution (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  SourceNonzeroEquation T f v ∧ (∀ t ∈ Set.Icc 0 T, RealValued (v t) ∧ MeanZero (v t)) ∧
    HomogeneousEssentiallyBounded 0 T v

/-- Every target Sobolev solution satisfies the full weak source hypotheses
under the proved change of equation. -/
theorem kdv_solution_sourceWeak {s T : ℝ} (hs : 0 ≤ s) {f : Fourier} {u : ℝ → Fourier}
    (hu : KdVSolution s T f u) :
    SourceWeakSolution T (reflectSign f) (fun t => sourceFrame t (u t)) := by
  obtain ⟨hEq, hc, hr⟩ := kdv_solution_to_source hs hu
  refine ⟨hEq, ?_, (hc.of_le hs).essentiallyBounded⟩
  intro t ht
  exact ⟨hr t ht, (hc.1 t ht).1⟩




/-- Strong convergence in a source homogeneous Sobolev norm and finite real
`L^p` time exponent. The finite extended norm is the ordinary `L^p` error norm. -/
def SourceLpConvergence (s T p : ℝ) (G : ℕ → ℝ → Fourier) (v : ℝ → Fourier) : Prop :=
  (∀ n, MemLp (fun t : ℝ => homogeneousNorm s (G n t - v t)) (ENNReal.ofReal p)
    (volume.restrict (Set.Icc 0 T))) ∧
  Filter.Tendsto
    (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm s (G n t - v t)) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0)

/-- Weak-star convergence in source `L∞ Hdot^s`, expressed on the weighted
`ℓ²` representatives and tested against every Bochner `L¹` dual function.
Representatives are only required to agree almost everywhere, as in the source. -/
def SourceWeakStarConvergence (s T : ℝ) (G : ℕ → ℝ → Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ W : ℕ → ℝ → L2Seq, ∃ w : ℝ → L2Seq,
    (∀ n, MemLp (W n) ∞ (volume.restrict (Set.Icc 0 T)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), (W n t).val = homogeneousWeighted s (G n t)) ∧
    (MemLp w ∞ (volume.restrict (Set.Icc 0 T)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), (w t).val = homogeneousWeighted s (v t)) ∧
    ∀ ψ : ℝ → L2Seq, Integrable ψ (volume.restrict (Set.Icc 0 T)) →
      Filter.Tendsto
        (fun n : ℕ => ∫ t : ℝ, inner ℂ (ψ t) (W n t) ∂volume.restrict (Set.Icc 0 T))
        Filter.atTop (nhds (∫ t : ℝ, inner ℂ (ψ t) (w t) ∂volume.restrict (Set.Icc 0 T)))

/-- The complete limiting-solution certificate asserted by the cited
Theorem 4.3, for its fixed lower regularity `σ`. -/
def SourceLimitCertificate (s T : ℝ) (f : Fourier) (σ : ℝ) (v : ℝ → Fourier) : Prop :=
  SourceWeakSolution T f v ∧ HomogeneousEssentiallyBounded s T v ∧
      ∃ A : ℝ, 0 ≤ A ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm 0 (v t) = homogeneousNorm 0 f) ∧
      ∃ G : ℕ → ℝ → Fourier, ∃ idx : ℕ → ℕ, StrictMono idx ∧
        (∀ m, HomSobolevContinuousOn s T (G m) ∧
          (∀ t ∈ Set.Icc 0 T, RealValued (G m t)) ∧ SourceGalerkinODE (m + 1) T f (G m) ∧
          ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (G m t) ≤ A) ∧
        (∀ p : ℝ, 1 < p → SourceLpConvergence σ T p (fun n => G (idx n)) v) ∧
        SourceWeakStarConvergence s T (fun n => G (idx n)) v

def SourceConstructedLimit (s T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ σ < s ∧ SourceLimitCertificate s T f σ v

/-- Explicit external premise: Babin–Ilyin–Titi Theorem 4.3 (arXiv v2), with
the Galerkin a priori bound from (4.13). It includes existence in Definition 3.1,
the bounded higher norm, almost-everywhere energy conservation, every finite
`L^p Hdot^σ` strong convergence conclusion, and the weak-star conclusion.
The auxiliary lower regularity `σ` is fixed before the subsequence, as in the
primary statement. Its bound `A` is after the datum; no initial-ball uniformity
is assumed here. Galerkin indices are reindexed from the positive integers. -/
def BITExistenceLimit : Prop :=
  ∀ T : ℝ, 0 < T → ∀ s : ℝ, 0 < s → ∀ f : Fourier,
    RealValued f → InHomSobolev s f → ∀ σ : ℝ, 0 < σ → σ < s →
      ∃ v : ℝ → Fourier, SourceLimitCertificate s T f σ v

theorem BITExistenceLimit.constructed {T s : ℝ} (externalLimit : BITExistenceLimit)
    (hT : 0 < T) (hs : 0 < s) {f : Fourier} (hfr : RealValued f) (hf : InHomSobolev s f) :
    ∃ v : ℝ → Fourier, SourceConstructedLimit s T f v := by
  obtain ⟨v, hv⟩ := externalLimit T hT s hs f hfr hf (s / 2) (by linarith) (by linarith)
  exact ⟨v, s / 2, by linarith, by linarith, hv⟩




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




theorem constructed_limit_unique (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    {f : Fourier} (hfr : RealValued f) (hf : InHomSobolev s f) {v : ℝ → Fourier}
    (hv : SourceConstructedLimit s T f v) : SourceUniqueContinuous s T f v := by
  by_cases hh : 1 / 2 < s
  · exact (externalHigh s hh T hT f hfr hf v hv).2.1
  · exact (externalLow s hs (le_of_not_gt hh) T hT f hfr hf v hv).2.1

/-- Uniformity over the initial ball is derived from the fixed-norm source
estimate, the proved sphere-padding argument, and the source limit theorem. -/
theorem uniform_source_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T R : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : Fourier, RealValued f → InHomSobolev s f →
      homogeneousNorm s f ≤ R → ∃ v : ℝ → Fourier,
        SourceConstructedLimit s T f v ∧ SourceWeakSolution T f v ∧
        HomSobolevContinuousOn s T v ∧ ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hb⟩ := uniform_source_limiting_bound externalGalerkin hs.le hT hR
  refine ⟨A, hA, ?_⟩
  intro f hfr hf hfR
  obtain ⟨v, hv⟩ := externalLimit.constructed hT hs hfr hf
  have hc := constructed_limit_continuous externalHigh externalLow hs hT hfr hf hv
  obtain ⟨σ, hσ0, hσs, hcert⟩ := hv
  obtain ⟨hw, he, Af, hAf, hbound, henergy, G, idx, hidx, hG, hlp, hstar⟩ := hcert
  refine ⟨v, ⟨σ, hσ0, hσs, hw, he, Af, hAf, hbound, henergy, G, idx, hidx, hG, hlp, hstar⟩,
    hw, hc, ?_⟩
  have h2 := hlp 2 (by norm_num)
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => homogeneousNorm σ (G (idx n) t - v t))
      (volume.restrict (Set.Icc 0 T)) := fun n => (h2.1 n).1
  have hconv : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun t : ℝ => homogeneousNorm σ (G (idx n) t - v t)) 2
        (volume.restrict (Set.Icc 0 T))) Filter.atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_ofNat] using h2.2
  exact hb σ hσs.le f hfr hf hfR v hc (fun n => G (idx n)) (fun n => idx n + 1)
    (fun n => Nat.succ_pos _) (fun n => (hG (idx n)).1)
    (fun n => (hG (idx n)).2.1) (fun n => (hG (idx n)).2.2.1) hmeas hconv

/-- The same bound applies to every continuous source solution, by the precise
continuous-class uniqueness conclusions of the cited source. -/
theorem uniform_source_flow_bound (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T R : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : Fourier, RealValued f → InHomSobolev s f →
      homogeneousNorm s f ≤ R → ∀ v : ℝ → Fourier,
        SourceWeakSolution T f v → HomSobolevContinuousOn s T v →
        ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hb⟩ := uniform_source_flow_exists
    externalGalerkin externalLimit externalHigh externalLow hs hT hR
  refine ⟨A, hA, ?_⟩
  intro f hfr hf hfR v hw hc
  obtain ⟨w, hwc, hww, hwC, hwb⟩ := hb f hfr hf hfR
  have heq := constructed_limit_unique externalHigh externalLow hs hT hfr hf hwc v hw hc
  intro t ht
  rw [heq t ht]
  exact hwb t ht

/-- A uniform bound on the exact physical solution follows with constants
chosen before the datum and the flow. No numerical stability is assumed. -/
theorem uniform_kdv_flow_bound (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T R : ℝ}
    (hs : 0 < s) (hT : 0 < T) (hR : 0 < R) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : Fourier, RealValued f → MeanZero f → InSobolev s f →
      hNorm s f ≤ R → ∀ u : ℝ → Fourier, KdVSolution s T f u →
        ∀ t ∈ Set.Icc 0 T, hNorm s (u t) ≤ M := by
  obtain ⟨A, hA, hb⟩ := uniform_source_flow_bound
    externalGalerkin externalLimit externalHigh externalLow hs hT hR
  refine ⟨(2 : ℝ) ^ s * A, mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA, ?_⟩
  intro f hfr hfm hf hfR u hu t ht
  have hfh := hf.to_homogeneous hs.le hfm
  have hfrh := homogeneous_reflectSign hfh
  have hR' : homogeneousNorm s (reflectSign f) ≤ R := by
    rw [homogeneousNorm_reflectSign]
    exact (homogeneousNorm_le_hNorm hs.le hf hfm).trans hfR
  have hc := (kdv_solution_to_source hs.le hu).2.1
  have hw := kdv_solution_sourceWeak hs.le hu
  have hb' := hb (reflectSign f) (reflectSign_real hfr) hfrh hR'
    (fun t => sourceFrame t (u t)) hw hc t ht
  calc
    hNorm s (u t) = hNorm s (sourceFrame t (u t)) := by
      rw [sourceFrame, reflectSign_hNorm, airy_hNorm]
    _ ≤ (2 : ℝ) ^ s * homogeneousNorm s (sourceFrame t (u t)) :=
      hNorm_le_homogeneousNorm hs.le (hc.1 t ht)
    _ ≤ _ := mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg (by norm_num) _)




theorem homogeneousNorm_sub_le {s : ℝ} {f g : Fourier}
    (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    homogeneousNorm s (f - g) ≤ homogeneousNorm s f + homogeneousNorm s g := by
  have heq : homogeneousLp s (f - g) (hf.sub hg) =
      homogeneousLp s f hf - homogeneousLp s g hg := by
    apply Subtype.ext
    exact homogeneousWeighted_sub s f g
  rw [← homogeneousLp_norm s (f - g) (hf.sub hg), heq,
    ← homogeneousLp_norm s f hf, ← homogeneousLp_norm s g hg]
  exact norm_sub_le _ _

theorem HomSobolevContinuousOn.sub {s T : ℝ} {v w : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) (hw : HomSobolevContinuousOn s T w) :
    HomSobolevContinuousOn s T (fun t => v t - w t) := by
  refine ⟨fun t ht => (hv.1 t ht).sub (hw.1 t ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δv, hδv, hbv⟩ := hv.2 t ht (ε / 2) (by linarith)
  obtain ⟨δw, hδw, hbw⟩ := hw.2 t ht (ε / 2) (by linarith)
  refine ⟨min δv δw, lt_min hδv hδw, ?_⟩
  intro r hr hrt
  have heq : (v r - w r) - (v t - w t) = (v r - v t) - (w r - w t) := by
    abel
  rw [heq]
  exact (homogeneousNorm_sub_le ((hv.1 r hr).sub (hv.1 t ht))
    ((hw.1 r hr).sub (hw.1 t ht))).trans_lt
      (by have hvb := hbv r hr (lt_of_lt_of_le hrt (min_le_left _ _))
          have hwb := hbw r hr (lt_of_lt_of_le hrt (min_le_right _ _))
          linarith)

/-- The source essential-supremum dependence estimate holds at every time,
including zero and the terminal time, in its continuous solution class. -/
theorem source_flow_lipschitz (externalLipschitz : BITWeakerLipschitz)
    {M θ : ℝ} (hM : 0 ≤ M) (hθ : -1 < θ) (hθ0 : θ ≤ 0) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ CM : ℝ, 0 < CM ∧ ∀ T : ℝ, 0 < T →
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev 0 f → InHomSobolev 0 g →
        homogeneousNorm 0 f + homogeneousNorm 0 g ≤ M →
        ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
          HomSobolevContinuousOn 0 T v → HomSobolevContinuousOn 0 T w →
            ∀ t ∈ Set.Icc 0 T,
              homogeneousNorm θ (v t - w t) ≤ C' * CM ^ T * homogeneousNorm θ (f - g) := by
  obtain ⟨C', hC', CM, hCM, hb⟩ := externalLipschitz M hM θ hθ hθ0
  refine ⟨C', hC', CM, hCM, ?_⟩
  intro T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC
  exact homogeneous_bound_of_ae hT ((hvC.sub hwC).of_le hθ0)
    (hb T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC)

/-- Uniform physical `L²` solution dependence on each initial-data ball. Both
flows may have different positive Sobolev orders; their norms enter only through
the initial `L²` ball. -/
theorem kdv_flow_l2_lipschitz (externalLipschitz : BITWeakerLipschitz)
    {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ s r : ℝ, 0 ≤ s → 0 ≤ r → ∀ f g : Fourier,
      RealValued f → MeanZero f → InSobolev s f →
      RealValued g → MeanZero g → InSobolev r g → hNorm 0 f + hNorm 0 g ≤ M →
      ∀ u w : ℝ → Fourier, KdVSolution s T f u → KdVSolution r T g w →
        ∀ t ∈ Set.Icc 0 T, hNorm 0 (u t - w t) ≤ C * hNorm 0 (f - g) := by
  obtain ⟨C', hC', CM, hCM, hb⟩ := source_flow_lipschitz externalLipschitz hM
    (by norm_num : (-1 : ℝ) < 0) le_rfl
  refine ⟨C' * CM ^ T, mul_pos hC' (Real.rpow_pos_of_pos hCM _), ?_⟩
  intro s r hs hr f g hfr hfm hf hgr hgm hg hfg u w hu hw t ht
  have hf0 := hf.of_le hs
  have hg0 := hg.of_le hr
  have hfh := homogeneous_reflectSign (hf0.to_homogeneous le_rfl hfm)
  have hgh := homogeneous_reflectSign (hg0.to_homogeneous le_rfl hgm)
  have hfg' : homogeneousNorm 0 (reflectSign f) + homogeneousNorm 0 (reflectSign g) ≤ M := by
    simpa only [homogeneousNorm_reflectSign, homogeneousNorm_zero] using hfg
  have hb' := hb T hT (reflectSign f) (reflectSign g) (reflectSign_real hfr)
    (reflectSign_real hgr) hfh hgh hfg' (fun t => sourceFrame t (u t))
    (fun t => sourceFrame t (w t)) (kdv_solution_sourceWeak hs hu)
    (kdv_solution_sourceWeak hr hw) ((kdv_solution_to_source hs hu).2.1.of_le hs)
    ((kdv_solution_to_source hr hw).2.1.of_le hr) t ht
  rw [sourceFrame_difference_norm] at hb'
  simpa only [← reflectSign_sub, homogeneousNorm_reflectSign,
    homogeneousNorm_zero] using hb'




theorem derivative_add (f g : Fourier) : derivative (f + g) = derivative f + derivative g := by
  funext k
  simp [derivative, mul_add]

theorem derivative_smul (z : ℂ) (f : Fourier) : derivative (z • f) = z • derivative f := by
  funext k
  simp [derivative, mul_left_comm]

theorem derivative_sub (f g : Fourier) : derivative (f - g) = derivative f - derivative g := by
  funext k
  simp [derivative, mul_sub]

def derivativeLinear (s : ℝ) : Sobolev (s + 1) →ₗ[ℂ] Sobolev s where
  toFun f := ⟨derivative f.val, derivative_inSobolev f.property⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeMap (s : ℝ) : Sobolev (s + 1) →L[ℂ] Sobolev s :=
  (derivativeLinear s).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (derivative f.val) ≤ hNorm (s + 1) f.val
    exact derivative_hNorm f.property)

def inverseDerivativeSameLinear (s : ℝ) : Sobolev s →ₗ[ℂ] Sobolev s where
  toFun f := ⟨inverseDerivative f.val, inverseDerivative_inSobolev_same f.property⟩
  map_add' f g := by apply Sobolev.ext; exact inverseDerivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact inverseDerivative_smul z f.val

def inverseDerivativeSameMap (s : ℝ) : Sobolev s →L[ℂ] Sobolev s :=
  (inverseDerivativeSameLinear s).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (inverseDerivative f.val) ≤ hNorm s f.val
    exact inverseDerivative_hNorm_same f.property)

def coefficientLinear (s : ℝ) (k : ℤ) : Sobolev s →ₗ[ℂ] ℂ where
  toFun f := f.val k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientMap (s : ℝ) (k : ℤ) : Sobolev s →L[ℂ] ℂ :=
  (coefficientLinear s k).mkContinuous (weight s k)⁻¹ (fun f => by
    have h := weighted_coeff_bound f.property k
    rw [norm_weighted] at h
    simp only [sobolev_norm]
    change ‖f.val k‖ ≤ (weight s k)⁻¹ * hNorm s f.val
    calc
      _ = (weight s k)⁻¹ * (weight s k * ‖f.val k‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (weight_pos s k).ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (weight_pos s k).le))

def productTwoBilinear : Sobolev 2 →ₗ[ℂ] Sobolev 2 →ₗ[ℂ] Sobolev 2 where
  toFun f := {
    toFun g := ⟨product f.val g.val, (h2_product_bound f.property g.property).1⟩
    map_add' g h := by
      apply Sobolev.ext
      exact product_add_right (f.property.of_le (by norm_num))
        (g.property.of_le (by norm_num)) (h.property.of_le (by norm_num))
    map_smul' z g := by apply Sobolev.ext; exact product_smul_right z f.val g.val }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Sobolev.ext
    exact product_add_left (f.property.of_le (by norm_num))
      (g.property.of_le (by norm_num)) (h.property.of_le (by norm_num))
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply Sobolev.ext
    exact product_smul_left z f.val g.val

def productTwoMap : Sobolev 2 →L[ℂ] Sobolev 2 →L[ℂ] Sobolev 2 :=
  productTwoBilinear.mkContinuous₂ (6 * h1EmbeddingConstant) (fun f g => by
    simp only [sobolev_norm]
    exact (h2_product_bound f.property g.property).2)

set_option maxHeartbeats 800000 in
theorem continuous_airy_apply {X : Type*} [TopologicalSpace X]
    (s : ℝ) {a : X → ℝ} {f : X → Sobolev s} (ha : Continuous a) (hf : Continuous f) :
    Continuous (fun x => airyMap s (a x) (f x)) :=
  (continuous_airy_action s).comp (ha.prodMk hf)

def JTwoBundled (t : ℝ) (f g : Sobolev 2) : Sobolev 2 :=
  airyMap 2 (-t) (removeMeanMap 2 (productTwoMap
    (airyMap 2 t (inverseDerivativeSameMap 2 f))
    (airyMap 2 t (inverseDerivativeSameMap 2 g))))

theorem JTwoBundled_val (t : ℝ) (f g : Sobolev 2) :
    (JTwoBundled t f g).val = J t f.val g.val := rfl

@[fun_prop] theorem continuous_JTwoBundled (f g : Sobolev 2) :
    Continuous (fun t : ℝ => JTwoBundled t f g) := by
  unfold JTwoBundled
  have hf' := continuous_airy_fixed 2 (inverseDerivativeSameMap 2 f)
  have hg' := continuous_airy_fixed 2 (inverseDerivativeSameMap 2 g)
  apply continuous_airy_apply 2 continuous_neg
  fun_prop

def stageTwoBundled (a t : ℝ) (f g : Sobolev 2) : Sobolev 2 :=
  (1 / 6 : ℂ) • (JTwoBundled t f g - JTwoBundled a f g)

theorem stageTwoBundled_val (a t : ℝ) (f g : Sobolev 2) :
    (stageTwoBundled a t f g).val = bilinearStage a t f.val g.val := rfl

@[fun_prop] theorem continuous_stageTwoBundled (a : ℝ) (f g : Sobolev 2) :
    Continuous (fun t : ℝ => stageTwoBundled a t f g) := by
  unfold stageTwoBundled
  fun_prop

def derivativeTwoLinear : Sobolev 2 →ₗ[ℂ] Sobolev 1 where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := 1) (by norm_num; exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeTwoMap : Sobolev 2 →L[ℂ] Sobolev 1 :=
  derivativeTwoLinear.mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm 1 (derivative f.val) ≤ hNorm 2 f.val
    have h := derivative_hNorm (s := 1) (by norm_num; exact f.property)
    norm_num at h
    exact h)

def BTwoBundled (t : ℝ) (f g : Sobolev 2) : Sobolev 1 :=
  airyMap 1 (-t) (derivativeTwoMap (productTwoMap (airyMap 2 t f) (airyMap 2 t g)))

theorem BTwoBundled_val (t : ℝ) (f g : Sobolev 2) :
    (BTwoBundled t f g).val = B t f.val g.val := rfl

theorem continuous_BTwoBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g : X → Sobolev 2} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => BTwoBundled (t x) (f x) (g x)) := by
  unfold BTwoBundled
  have hf' := continuous_airy_apply 2 ht hf
  have hg' := continuous_airy_apply 2 ht hg
  apply continuous_airy_apply 1 ht.neg
  fun_prop

theorem B_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t (f - g) h = B t f h - B t g h := by
  unfold B
  rw [airy_sub, product_sub_left (airy_inSobolev hf t) (airy_inSobolev hg t)
    (airy_inSobolev hh t), derivative_sub, airy_sub]

theorem B_sub_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t f (g - h) = B t f g - B t f h := by
  rw [B_comm t f (g - h), B_sub_left hg hh hf, B_comm t g f, B_comm t h f]

theorem B_diagonal_sub {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : B t f f - B t g g = B t (f - g) f + B t g (f - g) := by
  rw [B_sub_left hf hg hf, B_sub_right hg hf hg]
  abel




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




theorem coefficient_integral_bound {s A a b : ℝ} {f : ℝ → Sobolev s}
    (hf : Continuous f) (hab : a ≤ b) (hb : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ A) :
    InSobolev s (fun k => ∫ t : ℝ in a..b, (f t).val k) ∧
      hNorm s (fun k => ∫ t : ℝ in a..b, (f t).val k) ≤ A * (b - a) := by
  have heq := sobolev_integral_val (hf.intervalIntegrable a b)
  rw [← heq]
  refine ⟨(∫ t : ℝ in a..b, f t).property, ?_⟩
  rw [← sobolev_norm]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (f := f)
    (fun t ht => hb t (by rw [Set.uIoc_of_le hab] at ht; exact ⟨ht.1.le, ht.2⟩))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hn

/-- Compactness supplies coefficient envelopes used solely to justify the
normal-form identities, without asserting uniformity in these higher norms. -/
theorem regularFourierPath_of_bundled {a b : ℝ} {f df : ℝ → Sobolev 1}
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (f r).val k) ((df t).val k) t) :
    RegularFourierPath a b (fun t => (f t).val) (fun t => (df t).val) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image (hf.norm)).bddAbove
  obtain ⟨Md, hMd⟩ := (isCompact_Icc.image (hdf.norm)).bddAbove
  apply regularFourierPath_of_h1_bounds (M := |M|) (Md := |Md|) (abs_nonneg _) (abs_nonneg _)
  · intro k
    exact ((coefficientMap 1 k).continuous.comp hf).continuousOn
  · intro k
    exact ((coefficientMap 1 k).continuous.comp hdf).continuousOn
  · exact hd
  · intro t ht
    exact ⟨(f t).property, (by rw [← sobolev_norm]; exact (hM ⟨t, ht, rfl⟩).trans (le_abs_self _))⟩
  · intro t ht
    exact ⟨(df t).property, (by rw [← sobolev_norm]; exact (hMd ⟨t, ht, rfl⟩).trans (le_abs_self _))⟩

def localInterpolationDerivative (τ a t : ℝ) (f : Fourier) : Fourier :=
  (1 / 2 : ℂ) • B t f f + B t f (bilinearStage a t f f) +
    (1 / 2 : ℂ) • B t (bilinearStage a t f f) (bilinearStage a t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f

theorem localInterpolation_hasDerivAt {τ a t : ℝ} (f : Sobolev 2)
    (hfm : MeanZero f.val) (k : ℤ) :
    HasDerivAt (fun r : ℝ => localInterpolation τ a r f.val k)
      (localInterpolationDerivative τ a t f.val k) t := by
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hF := stage_hasDerivAt hf0 hf0 hfm hfm a t k
  have hC := frozenCross_hasDerivAt a t f k
  have hQ := frozenSquare_hasDerivAt a t f k
  have hlin : HasDerivAt (fun r : ℝ => (((r - a) / τ : ℝ) : ℂ))
      ((τ⁻¹ : ℝ) : ℂ) t := by
    simpa only [one_div, id_eq] using! (((hasDerivAt_id t).sub_const a).div_const τ).ofReal_comp
  have hc := hlin.mul_const (endpointCorrection τ a f.val k)
  simpa only [localInterpolation, localInterpolationDerivative, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, zero_add] using!
      (((hasDerivAt_const t (f.val k)).add hF).add hC |>.add hQ).sub hc

def localDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  (1 / 2 : ℂ) • BTwoBundled t f f + BTwoBundled t f (stageTwoBundled ((n : ℝ) * τ) t f f) +
    (1 / 2 : ℂ) • BTwoBundled t (stageTwoBundled ((n : ℝ) * τ) t f f)
      (stageTwoBundled ((n : ℝ) * τ) t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrectionBundled externalStep τ hτ n f hfr hfm

theorem localDerivativeBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (localDerivativeBundled externalStep τ hτ n t f hfr hfm).val =
      localInterpolationDerivative τ ((n : ℝ) * τ) t f.val := rfl

theorem continuous_localDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => localDerivativeBundled externalStep τ hτ n t f hfr hfm) := by
  unfold localDerivativeBundled
  have hf := continuous_BTwoBundled continuous_id (continuous_const (y := f)) (continuous_const (y := f))
  have hC := continuous_cross_integrand ((n : ℝ) * τ) f
  have hQ := continuous_square_integrand ((n : ℝ) * τ) f
  fun_prop

/-- The actual interpolation satisfies all regularity hypotheses of the
internally proved time-dependent normal form. -/
theorem localInterpolation_regular (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    RegularFourierPath ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)
      (fun t => localInterpolation τ ((n : ℝ) * τ) t f.val)
      (fun t => localInterpolationDerivative τ ((n : ℝ) * τ) t f.val) := by
  have h := regularFourierPath_of_bundled
    (a := (n : ℝ) * τ) (b := ((n + 1 : ℕ) : ℝ) * τ)
    (continuous_localInterpolationBundled externalStep τ hτ n f hfr hfm)
    (continuous_localDerivativeBundled externalStep τ hτ n f hfr hfm)
    (fun t _ k => by
      simp_rw [localInterpolationBundled_val, localDerivativeBundled_val]
      exact localInterpolation_hasDerivAt f hfm k)
  simpa only [localInterpolationBundled_val, localDerivativeBundled_val] using h




/-- The first estimate in (21). The numerical input only has an `L²` bound
relative to the exact `H^γ` state; its higher Sobolev norm is not used. -/
theorem numerical_stage_square_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        InSobolev 0 (B t (bilinearStage ((n : ℝ) * τ) t f f)
          (bilinearStage ((n : ℝ) * τ) t f f)) ∧
        hNorm 0 (B t (bilinearStage ((n : ℝ) * τ) t f f)
          (bilinearStage ((n : ℝ) * τ) t f f)) ≤ C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cs, hCs, hstage⟩ := paper_stage_bounds externalStage hT hγ hγ1
  obtain ⟨Cn, hCn, hnum⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hsquare⟩ := derivative_square_bound externalProduct hγ hγ1
  let K : ℝ := Cs * M ^ 2
  let E : ℝ := Cd * K * K
  let D : ℝ := 4 * h1EmbeddingConstant * Cn * Cn
  have hK : 0 ≤ K := mul_nonneg hCs.le (sq_nonneg _)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg hCd.le hK) hK
  have hC1 : 0 < h1EmbeddingConstant := lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + E + D, by linarith, ?_⟩
  intro τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  have hδ0 := hNorm_nonneg 0 (f - w)
  let a : ℝ := (n : ℝ) * τ
  let F : Fourier := bilinearStage a t f f
  let A : Fourier := bilinearStage a t w w
  have hw0 := hw.of_le hγ.le
  obtain ⟨hAα, hAh, hAαb, hAhb⟩ := hstage τ n t hτ hτ1 hnT ht w w hw hw hwm hwm
  have hAhb' : hNorm (1 + γ) A ≤ K := by
    calc
      _ ≤ Cs * hNorm γ w * hNorm γ w := hAhb
      _ ≤ K := by
        have hb : hNorm γ w * hNorm γ w ≤ M ^ 2 := by nlinarith [hNorm_nonneg γ w]
        simpa only [K, mul_assoc] using mul_le_mul_of_nonneg_left hb hCs.le
  have hAαb' : hNorm (aGamma γ) A ≤ K * τ ^ γ := by
    calc
      _ ≤ Cs * τ ^ γ * hNorm γ w * hNorm γ w := hAαb
      _ ≤ K * τ ^ γ := by
        have hb : hNorm γ w * hNorm γ w ≤ M ^ 2 := by nlinarith [hNorm_nonneg γ w]
        have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hCs.le (Real.rpow_nonneg hτ.le γ))
        dsimp [K]
        nlinarith only [hh]
  have hF1 := (bilinearStage_h1_bound hf hf a t).1
  have hA1 := (bilinearStage_h1_bound hw0 hw0 a t).1
  have hFA := hF1.sub hA1
  obtain ⟨hFbound, hDiff, hFa, hF0⟩ := hnum τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  have hAw : hNorm 1 A ≤ Cn :=
    (hnum τ n t hτ hτ1 hnT ht w w hw0 hw hwm hwM (by simp)).1
  obtain ⟨hBAraw, hBAb⟩ := hsquare (airy t A) (airy_inSobolev hAh t) (airy_inSobolev hAα t)
  have hBA : InSobolev 0 (B t A A) := airy_inSobolev hBAraw (-t)
  have hBA_bound : hNorm 0 (B t A A) ≤ E * τ ^ γ := by
    change hNorm 0 (airy (-t) (derivative (product (airy t A) (airy t A)))) ≤ _
    rw [airy_hNorm]
    simp only [airy_hNorm] at hBAb
    calc
      _ ≤ Cd * hNorm (1 + γ) A * hNorm (aGamma γ) A := hBAb
      _ ≤ Cd * K * (K * τ ^ γ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAhb' hCd.le) hAαb'
          (hNorm_nonneg _ _) (mul_nonneg hCd.le hK)
      _ = E * τ ^ γ := by dsimp [E]; ring
  obtain ⟨hBDF, hBDFb⟩ := B_h1_bound hFA hF1 t
  obtain ⟨hBAD, hBADb⟩ := B_h1_bound hA1 hFA t
  have heq : B t F F = B t A A + (B t (F - A) F + B t A (F - A)) := by
    have hh := B_diagonal_sub (hF1.of_le (by norm_num)) (hA1.of_le (by norm_num)) t
    linear_combination hh
  rw [heq]
  refine ⟨hBA.add (hBDF.add hBAD), ?_⟩
  have hCalg : 0 ≤ 2 * h1EmbeddingConstant := by linarith [h1EmbeddingConstant_ge_one]
  have hBDbound : hNorm 0 (B t (F - A) F) + hNorm 0 (B t A (F - A)) ≤
      D * hNorm 0 (f - w) := by
    calc
      _ ≤ (2 * h1EmbeddingConstant) * hNorm 1 (F - A) * hNorm 1 F +
          (2 * h1EmbeddingConstant) * hNorm 1 A * hNorm 1 (F - A) := add_le_add hBDFb hBADb
      _ ≤ (2 * h1EmbeddingConstant) * (Cn * hNorm 0 (f - w)) * Cn +
          (2 * h1EmbeddingConstant) * Cn * (Cn * hNorm 0 (f - w)) :=
        add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hDiff hCalg) hFbound
            (hNorm_nonneg _ _) (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left hAw hCalg) hDiff
            (hNorm_nonneg _ _) (by positivity))
      _ = _ := by dsimp [D]; ring
  calc
    _ ≤ hNorm 0 (B t A A) + hNorm 0 (B t (F - A) F + B t A (F - A)) :=
      hNorm_add_le hBA (hBDF.add hBAD)
    _ ≤ hNorm 0 (B t A A) + (hNorm 0 (B t (F - A) F) + hNorm 0 (B t A (F - A))) :=
      add_le_add le_rfl (hNorm_add_le hBDF hBAD)
    _ ≤ E * τ ^ γ + D * hNorm 0 (f - w) := add_le_add hBA_bound hBDbound
    _ ≤ (1 + E + D) * (τ ^ γ + hNorm 0 (f - w)) := by
      have ht0 := Real.rpow_nonneg hτ.le γ
      have hd0 := hNorm_nonneg 0 (f - w)
      nlinarith




/-- Integrating the stage square bound gives the full quadratic correction
bound in (21), with no higher norm in its constant. -/
theorem numerical_square_integral_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (frozenSquare ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (frozenSquare ((n : ℝ) * τ) t f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cs, hCs, hb⟩ := numerical_stage_square_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Cs / 2, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let g : ℝ → Sobolev 0 := fun s => inclusionMap 0 1 (by norm_num)
    (BTwoBundled s (stageTwoBundled a s f f) (stageTwoBundled a s f f))
  have hg : Continuous g := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_square_integrand a f)
  have hB : ∀ s ∈ Set.Icc a t, ‖g s‖ ≤ Cs * q := by
    intro s hs
    have hs' : s ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) :=
      ⟨hs.1, hs.2.trans ht.2⟩
    rw [sobolev_norm]
    change hNorm 0 (B s (bilinearStage a s f.val f.val) (bilinearStage a s f.val f.val)) ≤ Cs * q
    exact (hb τ n s hτ hτ1 hnT hs' f.val w
      (f.property.of_le (by norm_num)) hw hwm hwM hδ).2
  obtain ⟨hI, hIb⟩ := coefficient_integral_bound hg ht.1 hB
  have hQ : InSobolev 0 (frozenSquare a t f.val) := hI.smul (1 / 2 : ℂ)
  refine ⟨hQ, ?_⟩
  have heq : frozenSquare a t f.val = (1 / 2 : ℂ) •
      (fun k => ∫ s : ℝ in a..t, (g s).val k) := rfl
  change hNorm 0 (frozenSquare a t f.val) ≤ (Cs / 2) * τ * q
  rw [heq, hNorm_smul hI]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  have hlength : t - a ≤ τ := by
    have heq : b = a + τ := by dsimp [a, b]; push_cast; ring
    have htb : t ≤ b := ht.2
    linarith
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  calc
    _ ≤ (1 / 2 : ℝ) * (Cs * q * (t - a)) := mul_le_mul_of_nonneg_left hIb (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (Cs * q * τ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlength (mul_nonneg hCs.le hq)) (by norm_num)
    _ = _ := by ring

/-- The complete endpoint correction is small even for a merely `L²`-close
numerical state. The source identity is not an estimate premise here. -/
theorem numerical_endpoint_correction_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
          InSobolev 0 (endpointCorrection τ ((n : ℝ) * τ) f.val) ∧
          hNorm 0 (endpointCorrection τ ((n : ℝ) * τ) f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cq, hCq, hb⟩ := numerical_square_integral_bound externalStage externalProduct hT hγ hγ1 hM
  let Cr := numericalRemainderConstant γ M
  have hCr : 0 < Cr := numericalRemainderConstant_pos γ hM
  refine ⟨Cq + Cr, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have heq : ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ := by push_cast; ring
  have ht : ((n + 1 : ℕ) : ℝ) * τ ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) := by
    rw [heq]
    exact ⟨le_add_of_nonneg_right hτ.le, le_rfl⟩
  obtain ⟨hQ, hQb⟩ := hb τ n hτ hτ1 hnT f w hw hwm hwM hδ _ ht
  rw [heq] at hQ hQb
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hR : InSobolev 0 (remainder τ ((n : ℝ) * τ) f.val f.val f.val) := by
    rw [remainder_eq_interactionRemainder τ _ hfm hfm hfm]
    exact (interactionRemainder_endpoint hτ _ hf0 hf0 hf0).1
  have hRb := numerical_state_estimate hτ hγ.le hγ1 ((n : ℝ) * τ)
    hf0 hw hfm hwm hwM hδ
  refine ⟨hQ.add hR, ?_⟩
  calc
    _ ≤ hNorm 0 (frozenSquare ((n : ℝ) * τ) ((n : ℝ) * τ + τ) f.val) +
        hNorm 0 (remainder τ ((n : ℝ) * τ) f.val f.val f.val) := hNorm_add_le hQ hR
    _ ≤ Cq * τ * (τ ^ γ + hNorm 0 (f.val - w)) + Cr * τ * (τ ^ γ + hNorm 0 (f.val - w)) :=
      add_le_add hQb hRb
    _ = _ := by ring




theorem inverseDerivative_B (t : ℝ) (f g : Fourier) :
    inverseDerivative (B t f g) =
      airy (-t) (removeMean (product (airy t f) (airy t g))) := by
  rw [B, inverseDerivative_airy, inverseDerivative_derivative]

/-- The asymmetric product decomposition used in (22). -/
theorem numerical_cross_inverse_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        InSobolev 0 (inverseDerivative (B t f (bilinearStage ((n : ℝ) * τ) t f f))) ∧
        hNorm 0 (inverseDerivative (B t f (bilinearStage ((n : ℝ) * τ) t f f))) ≤
          C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cn, hCn, hnum⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cp, hCp, hprod⟩ := normalized_product_estimate externalProduct hγ.le hγ1
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hC1 : 0 < h1EmbeddingConstant := lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one
  let C : ℝ := 1 + Cp * M * Cn + h1EmbeddingConstant * Cn
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  let F : Fourier := bilinearStage ((n : ℝ) * τ) t f f
  let q : ℝ := τ ^ γ + hNorm 0 (f - w)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hδq : hNorm 0 (f - w) ≤ q := le_add_of_nonneg_left (Real.rpow_nonneg hτ.le γ)
  have hw0 := hw.of_le hγ.le
  have hF1 := (bilinearStage_h1_bound hf hf ((n : ℝ) * τ) t).1
  have hF0 := hF1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have ha1 := (aGamma_parameters hγ hγ1).2.1
  have hFa := hF1.of_le ha1.le
  obtain ⟨hFbound, hDiff, hFaB, hF0B⟩ := hnum τ n t hτ hτ1 hnT ht f w hf hw hwm hwM hδ
  obtain ⟨hPw, hPwb⟩ := hprod (airy t w) (airy t F) (airy_inSobolev hw t) (airy_inSobolev hFa t)
  obtain ⟨hPd, hPdb⟩ := l2_h1_product_bound (airy_inSobolev (hf.sub hw0) t) (airy_inSobolev hF1 t)
  have heq : product (airy t f) (airy t F) = product (airy t w) (airy t F) +
      product (airy t (f - w)) (airy t F) := by
    rw [airy_sub, product_sub_left (airy_inSobolev hf t) (airy_inSobolev hw0 t) (airy_inSobolev hF0 t)]
    abel
  have hP : InSobolev 0 (product (airy t f) (airy t F)) := by rw [heq]; exact hPw.add hPd
  rw [inverseDerivative_B]
  refine ⟨airy_inSobolev (removeMean_inSobolev hP) (-t), ?_⟩
  rw [airy_hNorm]
  calc
    _ ≤ hNorm 0 (product (airy t f) (airy t F)) := removeMean_hNorm_le hP
    _ ≤ hNorm 0 (product (airy t w) (airy t F)) + hNorm 0 (product (airy t (f - w)) (airy t F)) := by
      rw [heq]
      exact hNorm_add_le hPw hPd
    _ ≤ Cp * hNorm γ w * hNorm (aGamma γ) F +
        h1EmbeddingConstant * hNorm 0 (f - w) * hNorm 1 F := by
      simpa only [airy_hNorm, aGamma, F] using add_le_add hPwb hPdb
    _ ≤ Cp * M * (Cn * q) + h1EmbeddingConstant * q * Cn :=
      add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hwM hCp.le) hFaB
          (hNorm_nonneg _ _) (mul_nonneg hCp.le hM))
        (mul_le_mul (mul_le_mul_of_nonneg_left hδq hC1.le) hFbound
          (hNorm_nonneg _ _) (mul_nonneg hC1.le hq))
    _ ≤ C * q := by dsimp [C]; nlinarith

theorem inverseDerivative_integral (a b : ℝ) (f : ℝ → Fourier) :
    inverseDerivative (fun k => ∫ t : ℝ in a..b, f t k) =
      (fun k => ∫ t : ℝ in a..b, inverseDerivative (f t) k) := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [inverseDerivative]
  · simp only [inverseDerivative, if_neg hk, intervalIntegral.integral_const_mul]




theorem J_smul_left (t : ℝ) (z : ℂ) (f g : Fourier) : J t (z • f) g = z • J t f g := by
  unfold J
  rw [inverseDerivative_smul, airy_smul, product_smul_left, removeMean_smul, airy_smul]

theorem J_smul_right (t : ℝ) (z : ℂ) (f g : Fourier) : J t f (z • g) = z • J t f g := by
  rw [J_comm t f (z • g), J_smul_left, J_comm t g f]

@[simp] theorem J_zero_left (t : ℝ) (g : Fourier) : J t 0 g = 0 := by
  simpa only [zero_smul] using J_smul_left t 0 g g

@[simp] theorem J_zero_right (t : ℝ) (f : Fourier) : J t f 0 = 0 := by
  rw [J_comm, J_zero_left]

@[simp] theorem bilinearStage_self (a : ℝ) (f g : Fourier) : bilinearStage a a f g = 0 := by
  simp [bilinearStage]

theorem stage_regular {a b : ℝ} (f : Sobolev 2) (hfm : MeanZero f.val) :
    RegularFourierPath a b (fun t => bilinearStage a t f.val f.val)
      (fun t => (1 / 2 : ℂ) • B t f.val f.val) := by
  have hc : Continuous (fun t : ℝ => inclusionMap 1 2 (by norm_num) (stageTwoBundled a t f f)) :=
    (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_stageTwoBundled a f f)
  have hdc : Continuous (fun t : ℝ => (1 / 2 : ℂ) • BTwoBundled t f f) :=
    (continuous_const (y := (1 / 2 : ℂ))).smul
      (continuous_BTwoBundled continuous_id continuous_const continuous_const)
  exact regularFourierPath_of_bundled hc hdc (by
    intro t _ k
    exact stage_hasDerivAt (f.property.of_le (by norm_num))
      (f.property.of_le (by norm_num)) hfm hfm a t k)

theorem constant_regular (a b : ℝ) (f : Sobolev 1) :
    RegularFourierPath a b (fun _ => f.val) (fun _ => 0) := by
  exact regularFourierPath_of_bundled (continuous_const (y := f))
    (continuous_const (y := (0 : Sobolev 1))) (fun t _ k => hasDerivAt_const t _)

/-- Identity (23), derived from the proved variable-input normal form. The
initial boundary vanishes because the actual stage is zero there. -/
theorem frozenCross_normal_form {a b : ℝ} (hab : a ≤ b) (f : Sobolev 2)
    (hfm : MeanZero f.val) :
    frozenCross a b f.val = (1 / 3 : ℂ) • J b f.val (bilinearStage a b f.val f.val) -
      (1 / 6 : ℂ) • CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun _ => f.val) := by
  have hreg := constant_regular a b (inclusionMap 1 2 (by norm_num) f)
  have hFreg := stage_regular (a := a) (b := b) f hfm
  funext k
  have hnf := variable_normal_form hab hreg hFreg (fun _ _ => hfm)
    (fun t _ => stage_meanZero a t f.val f.val) k
  have hInt : (fun t : ℝ => J t 0 (bilinearStage a t f.val f.val) k +
      J t f.val ((1 / 2 : ℂ) • B t f.val f.val) k) =
      (fun t : ℝ => (1 / 2 : ℂ) * J t (B t f.val f.val) f.val k) := by
    funext t
    rw [J_zero_left, J_smul_right, J_comm t f.val (B t f.val f.val)]
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul]
  change (∫ t : ℝ in a..b, B t f.val (bilinearStage a t f.val f.val) k) =
    (1 / 3 : ℂ) * (J b f.val (bilinearStage a b f.val f.val) k -
      J a f.val (bilinearStage a a f.val f.val) k) -
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b,
        (J t 0 (bilinearStage a t f.val f.val) k + J t f.val ((1 / 2 : ℂ) • B t f.val f.val) k) at hnf
  rw [hInt, intervalIntegral.integral_const_mul, J_B_integral,
    bilinearStage_self, J_zero_right] at hnf
  simp only [Pi.zero_apply, sub_zero] at hnf
  change frozenCross a b f.val k = (1 / 3 : ℂ) * J b f.val (bilinearStage a b f.val f.val) k -
    (1 / 6 : ℂ) * CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun _ => f.val) k
  dsimp only [frozenCross]
  linear_combination hnf

theorem continuous_airy_coefficient (f : Fourier) (k : ℤ) :
    Continuous (fun t : ℝ => airy t f k) := by
  unfold airy
  fun_prop

theorem norm_airy_coefficient (f : Fourier) (t : ℝ) (k : ℤ) : ‖airy t f k‖ = ‖f k‖ := by
  simp only [airy, norm_mul, airy_multiplier_norm, one_mul]

theorem continuous_airy_product_coefficient {f g : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (k : ℤ) :
    Continuous (fun t : ℝ => product (airy t f) (airy t g) k) := by
  apply continuous_tsum
  · intro a
    exact (continuous_airy_coefficient f a).mul (continuous_airy_coefficient g (k - a))
  · exact absolute_convolution_summable hf hg k
  · intro a t
    rw [norm_mul, norm_airy_coefficient, norm_airy_coefficient]

theorem continuous_CIntegrand_fixed {f g h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (k : ℤ) :
    Continuous (fun t : ℝ => CIntegrand t f g h k) := by
  by_cases hk : k = 0
  · subst k
    simpa [CIntegrand, airy, removeMean] using (continuous_const (y := (0 : ℂ)))
  · have hinv := inverseDerivative_inSobolev_one hh
    have hs := (reflectAt k).summable_iff.mpr (h1_absolute_coefficients hinv).1
    have hu : Summable (fun a : ℤ => (hNorm 0 f * hNorm 0 g) * ‖inverseDerivative h (k - a)‖) :=
      hs.mul_left _
    have hinner (a : ℤ) : Continuous (fun t : ℝ =>
        removeMean (product (airy t f) (airy t g)) a * airy t (inverseDerivative h) (k - a)) := by
      by_cases ha : a = 0
      · subst a
        simpa using (continuous_const (y := (0 : ℂ)))
      · have hca : Continuous (fun t : ℝ => removeMean (product (airy t f) (airy t g)) a) := by
          simpa only [removeMean, if_neg ha] using continuous_airy_product_coefficient hf hg a
        exact hca.mul (continuous_airy_coefficient _ _)
    have hb (a : ℤ) (t : ℝ) :
        ‖removeMean (product (airy t f) (airy t g)) a * airy t (inverseDerivative h) (k - a)‖ ≤
          (hNorm 0 f * hNorm 0 g) * ‖inverseDerivative h (k - a)‖ := by
      rw [norm_mul, norm_airy_coefficient]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (removeMean_coeff_norm_le _ a).trans (by
        simpa only [airy_hNorm] using product_coeff_bound (airy_inSobolev hf t) (airy_inSobolev hg t) a)
    have hc := continuous_tsum hinner hu hb
    change Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3) *
      removeMean (product (removeMean (product (airy t f) (airy t g)))
        (airy t (inverseDerivative h))) k)
    simp only [removeMean, if_neg hk]
    have he : Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3)) := by fun_prop
    exact he.mul hc




theorem product_add_left_summable {f g h : Fourier}
    (hf : ∀ k, Summable (fun a : ℤ => f a * h (k - a)))
    (hg : ∀ k, Summable (fun a : ℤ => g a * h (k - a))) :
    product (f + g) h = product f h + product g h := by
  funext k
  simpa only [product, Pi.add_apply, add_mul] using (hf k).tsum_add (hg k)

theorem product_add_right_summable {f g h : Fourier}
    (hg : ∀ k, Summable (fun a : ℤ => f a * g (k - a)))
    (hh : ∀ k, Summable (fun a : ℤ => f a * h (k - a))) :
    product f (g + h) = product f g + product f h := by
  funext k
  simpa only [product, Pi.add_apply, mul_add] using (hg k).tsum_add (hh k)

theorem CIntegrand_add_left {f l g h : Fourier}
    (hf : InSobolev 0 f) (hl : InSobolev 0 l) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (t : ℝ) :
    CIntegrand t (f + l) g h = CIntegrand t f g h + CIntegrand t l g h := by
  have hout := product_add_left_summable
    (fun k => (CIntegrand_summable_bound hf hg hh t k).1)
    (fun k => (CIntegrand_summable_bound hl hg hh t k).1)
  unfold CIntegrand
  rw [airy_add, product_add_left (airy_inSobolev hf t) (airy_inSobolev hl t) (airy_inSobolev hg t),
    removeMean_add, hout, removeMean_add, airy_add]

theorem CIntegrand_comm (t : ℝ) (f g h : Fourier) : CIntegrand t f g h = CIntegrand t g f h := by
  unfold CIntegrand
  rw [product_comm (airy t f) (airy t g)]

theorem CIntegrand_add_middle {f g l h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hl : InSobolev 0 l) (hh : InSobolev 0 h) (t : ℝ) :
    CIntegrand t f (g + l) h = CIntegrand t f g h + CIntegrand t f l h := by
  rw [CIntegrand_comm t f (g + l), CIntegrand_add_left hg hl hf hh,
    CIntegrand_comm t g f, CIntegrand_comm t l f]

theorem CIntegrand_add_right {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) (t : ℝ) :
    CIntegrand t f g (h + l) = CIntegrand t f g h + CIntegrand t f g l := by
  have hout := product_add_right_summable
    (fun k => (CIntegrand_summable_bound hf hg hh t k).1)
    (fun k => (CIntegrand_summable_bound hf hg hl t k).1)
  unfold CIntegrand
  rw [inverseDerivative_add, airy_add, hout, removeMean_add, airy_add]

theorem CIntegrand_smul_left (t : ℝ) (z : ℂ) (f g h : Fourier) :
    CIntegrand t (z • f) g h = z • CIntegrand t f g h := by
  unfold CIntegrand
  rw [airy_smul, product_smul_left, removeMean_smul, product_smul_left, removeMean_smul, airy_smul]

theorem CIntegrand_smul_middle (t : ℝ) (z : ℂ) (f g h : Fourier) :
    CIntegrand t f (z • g) h = z • CIntegrand t f g h := by
  rw [CIntegrand_comm t f (z • g), CIntegrand_smul_left, CIntegrand_comm t g f]

theorem CIntegrand_smul_right (t : ℝ) (z : ℂ) (f g h : Fourier) :
    CIntegrand t f g (z • h) = z • CIntegrand t f g h := by
  unfold CIntegrand
  rw [inverseDerivative_smul, airy_smul, product_smul_right, removeMean_smul, airy_smul]

theorem CIntegral_static_add_left {f l g h : Fourier}
    (hf : InSobolev 0 f) (hl : InSobolev 0 l) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f + l) (fun _ => g) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) +
        CIntegral a b (fun _ => l) (fun _ => g) (fun _ => h) := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_add_left hf hl hg hh]
  exact intervalIntegral.integral_add
    ((continuous_CIntegrand_fixed hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_fixed hl hg hh k).intervalIntegrable a b)

theorem CIntegral_static_comm (a b : ℝ) (f g h : Fourier) :
    CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) =
      CIntegral a b (fun _ => g) (fun _ => f) (fun _ => h) := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_comm _ f g h]

theorem CIntegral_static_add_middle {f g l h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hl : InSobolev 0 l) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g + l) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) +
        CIntegral a b (fun _ => f) (fun _ => l) (fun _ => h) := by
  rw [CIntegral_static_comm a b f (g + l), CIntegral_static_add_left hg hl hf hh,
    CIntegral_static_comm a b g f, CIntegral_static_comm a b l f]

theorem CIntegral_static_add_right {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h + l) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) +
        CIntegral a b (fun _ => f) (fun _ => g) (fun _ => l) := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_add_right hf hg hh hl]
  exact intervalIntegral.integral_add
    ((continuous_CIntegrand_fixed hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_fixed hf hg hl k).intervalIntegrable a b)




theorem CIntegral_static_sub_left {f l g h : Fourier}
    (hf : InSobolev 0 f) (hl : InSobolev 0 l) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f - l) (fun _ => g) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) -
        CIntegral a b (fun _ => l) (fun _ => g) (fun _ => h) := by
  have ha := CIntegral_static_add_left (hf.sub hl) hl hg hh a b
  simp only [sub_add_cancel] at ha
  exact eq_sub_iff_add_eq.mpr ha.symm

theorem CIntegral_static_sub_middle {f g l h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hl : InSobolev 0 l) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g - l) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) -
        CIntegral a b (fun _ => f) (fun _ => l) (fun _ => h) := by
  have ha := CIntegral_static_add_middle hf (hg.sub hl) hl hh a b
  simp only [sub_add_cancel] at ha
  exact eq_sub_iff_add_eq.mpr ha.symm

theorem CIntegral_static_sub_right {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h - l) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) -
        CIntegral a b (fun _ => f) (fun _ => g) (fun _ => l) := by
  have ha := CIntegral_static_add_right hf hg (hh.sub hl) hl a b
  simp only [sub_add_cancel] at ha
  exact eq_sub_iff_add_eq.mpr ha.symm

theorem CIntegral_static_diagonal_sub {f w : Fourier}
    (hf : InSobolev 0 f) (hw : InSobolev 0 w) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f) -
      CIntegral a b (fun _ => w) (fun _ => w) (fun _ => w) =
      CIntegral a b (fun _ => f - w) (fun _ => f) (fun _ => f) +
      CIntegral a b (fun _ => w) (fun _ => f - w) (fun _ => f) +
      CIntegral a b (fun _ => w) (fun _ => w) (fun _ => f - w) := by
  rw [CIntegral_static_sub_left hf hw hf hf,
    CIntegral_static_sub_middle hw hf hw hf, CIntegral_static_sub_right hw hw hf hw]
  abel

/-- The static trilinear term at a numerical state is controlled by the exact
state's Sobolev norm and their `L²` distance, by three internal telescoping terms. -/
theorem numerical_static_cubic_bound (externalTrilinear : LiWuTrilinearEstimate)
    {γ M : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ τ →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        InSobolev 0 (CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f)) ∧
        hNorm 0 (CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f)) ≤
          C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cγ, hCγ, hbγ⟩ := normalized_static_trilinear externalTrilinear
    (by norm_num : (0 : ℝ) < 1) le_rfl hγ.le hγ1
  obtain ⟨C0, hC0, hb0⟩ := normalized_static_trilinear externalTrilinear
    (by norm_num : (0 : ℝ) < 1) le_rfl (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
  let A : ℝ := Cγ * M ^ 3
  let D : ℝ := 3 * C0 * (M + 1) ^ 2
  have hA : 0 ≤ A := mul_nonneg hCγ.le (by positivity)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + A + D, by linarith, ?_⟩
  intro τ hτ hτ1 a b ha hab hb f w hf hw hwM hδ
  have hwγ0 := hNorm_nonneg γ w
  have hw00 := hNorm_nonneg 0 w
  have hf00 := hNorm_nonneg 0 f
  have hd00 := hNorm_nonneg 0 (f - w)
  have hb1 : b - a ≤ 1 := hb.trans hτ1
  have hw0 := hw.of_le hγ.le
  have hd := hf.sub hw0
  have hwM0 : hNorm 0 w ≤ M := (hNorm_mono hw hγ.le).trans hwM
  have hfM0 : hNorm 0 f ≤ M + 1 := by
    have hh := hNorm_add_le hd hw0
    rw [sub_add_cancel] at hh
    linarith
  obtain ⟨hww, hwwb⟩ := hbγ a b ha hab hb1 w w w hw hw hw
  have hwwb' : hNorm 0 (CIntegral a b (fun _ => w) (fun _ => w) (fun _ => w)) ≤ A * τ ^ γ := by
    calc
      _ ≤ Cγ * (b - a) ^ γ * hNorm γ w * hNorm γ w * hNorm γ w := hwwb
      _ ≤ Cγ * τ ^ γ * M * M * M := by
        gcongr
      _ = _ := by dsimp [A]; ring
  obtain ⟨h1, hb1'⟩ := hb0 a b ha hab hb1 (f - w) f f hd hf hf
  obtain ⟨h2, hb2'⟩ := hb0 a b ha hab hb1 w (f - w) f hw0 hd hf
  obtain ⟨h3, hb3'⟩ := hb0 a b ha hab hb1 w w (f - w) hw0 hw0 hd
  simp only [Real.rpow_zero, mul_one] at hb1' hb2' hb3'
  have h1b : hNorm 0 (CIntegral a b (fun _ => f - w) (fun _ => f) (fun _ => f)) ≤
      C0 * (M + 1) ^ 2 * hNorm 0 (f - w) := by
    calc
      _ ≤ C0 * hNorm 0 (f - w) * hNorm 0 f * hNorm 0 f := hb1'
      _ ≤ C0 * hNorm 0 (f - w) * (M + 1) * (M + 1) := by gcongr
      _ = _ := by ring
  have h2b : hNorm 0 (CIntegral a b (fun _ => w) (fun _ => f - w) (fun _ => f)) ≤
      C0 * (M + 1) ^ 2 * hNorm 0 (f - w) := by
    calc
      _ ≤ C0 * hNorm 0 w * hNorm 0 (f - w) * hNorm 0 f := hb2'
      _ ≤ C0 * (M + 1) * hNorm 0 (f - w) * (M + 1) := by gcongr; linarith
      _ = _ := by ring
  have h3b : hNorm 0 (CIntegral a b (fun _ => w) (fun _ => w) (fun _ => f - w)) ≤
      C0 * (M + 1) ^ 2 * hNorm 0 (f - w) := by
    calc
      _ ≤ C0 * hNorm 0 w * hNorm 0 w * hNorm 0 (f - w) := hb3'
      _ ≤ C0 * (M + 1) * (M + 1) * hNorm 0 (f - w) := by gcongr <;> linarith
      _ = _ := by ring
  have hEq : CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f) =
      CIntegral a b (fun _ => w) (fun _ => w) (fun _ => w) +
        ((CIntegral a b (fun _ => f - w) (fun _ => f) (fun _ => f) +
          CIntegral a b (fun _ => w) (fun _ => f - w) (fun _ => f)) +
          CIntegral a b (fun _ => w) (fun _ => w) (fun _ => f - w)) := by
    have hh := CIntegral_static_diagonal_sub hf hw0 a b
    linear_combination hh
  rw [hEq]
  refine ⟨hww.add ((h1.add h2).add h3), ?_⟩
  have hsum := hNorm_add_le hww ((h1.add h2).add h3)
  have hsum' := hNorm_add_le (h1.add h2) h3
  have hsum'' := hNorm_add_le h1 h2
  have hq0 := Real.rpow_nonneg hτ.le γ
  have hd0 := hNorm_nonneg 0 (f - w)
  dsimp [D]
  nlinarith




/-- The `L²` cross-integral bound obtained from identity (23), using the
mixed static trilinear estimate and the sharper boundary estimate. -/
theorem numerical_cross_bound (externalStage : LiWuStageEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (frozenCross ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (frozenCross ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cn, hCn, hnum⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cc, hCc, hcubic⟩ := numerical_static_cubic_bound externalTrilinear hγ hγ1 hM
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 < K := mul_pos (by positivity)
    (lt_of_lt_of_le zero_lt_one h1EmbeddingConstant_ge_one)
  let C : ℝ := 1 + K * Cn * (M + 1) / 3 + Cc / 6
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let F : Fourier := bilinearStage a t f.val f.val
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hw0 := hw.of_le hγ.le
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hb := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hb
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hF1 := (bilinearStage_h1_bound hf0 hf0 a t).1
  have hF0 := hF1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hF0b := (hnum τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ).2.2.2
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg n) hτ.le
  have hlength : t - a ≤ τ := by
    have hEnd : ((n + 1 : ℕ) : ℝ) * τ = a + τ := by dsimp [a]; push_cast; ring
    linarith [ht.2]
  obtain ⟨hCI, hCIb⟩ := hcubic τ hτ hτ1 a t ha ht.1 hlength f.val w hf0 hw hwM hδ
  have hJ : InSobolev 0 (J t f.val F) := (J_h1_bound hf0 hF0 t).1.of_le (by norm_num)
  have hJb : hNorm 0 (J t f.val F) ≤ K * Cn * (M + 1) * q := by
    rw [J_comm]
    calc
      _ ≤ K * hNorm 0 (inverseDerivative F) * hNorm 0 f.val := J_inverse_bound hF0 hf0 t
      _ ≤ K * (Cn * q) * (M + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ((inverseDerivative_hNorm_same hF0).trans hF0b) hK.le)
          hfM (hNorm_nonneg _ _) (mul_nonneg hK.le (mul_nonneg hCn.le hq))
      _ = _ := by ring
  rw [frozenCross_normal_form ht.1 f hfm]
  refine ⟨(hJ.smul _).sub (hCI.smul _), ?_⟩
  have hs := hNorm_sub_le (hJ.smul (1 / 3 : ℂ)) (hCI.smul (1 / 6 : ℂ))
  rw [hNorm_smul hJ, hNorm_smul hCI] at hs
  have hn3 : ‖(1 / 3 : ℂ)‖ = (1 / 3 : ℝ) := by norm_num
  have hn6 : ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) := by norm_num
  rw [hn3, hn6] at hs
  change hNorm 0 _ ≤ C * q
  dsimp [C]
  nlinarith




def timeLInfinity {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) : ℝ :=
  (eLpNorm f ∞ (volume.restrict (Set.Icc a b))).toReal

def timeXNorm (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) : ℝ :=
  timeLInfinity a b f + timeLInfinity a b df

theorem inclusionMap_self_apply (s : ℝ) (h : s ≤ s) (f : Sobolev s) :
    inclusionMap s s h f = f := by apply Sobolev.ext; rfl

theorem source_zero_time_norm (a b : ℝ) (f : ℝ → Sobolev 0) :
    sourceLInfinityZero le_rfl a b f = sourceNormalization * timeLInfinity a b f := by
  unfold sourceLInfinityZero sourceLInfinity timeLInfinity
  simp only [inclusionMap_self_apply]

theorem source_x_time_norm (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) :
    sourceXNorm le_rfl a b f df = sourceNormalization * timeXNorm a b f df := by
  rw [sourceXNorm, source_zero_time_norm]
  simp only [sourceLInfinity, timeLInfinity, timeXNorm]
  ring

theorem fin_three_product_scalar (κ : ℝ) (x : Fin 3 → ℝ) :
    (∏ j : Fin 3, κ * x j) = κ ^ 3 * ∏ j : Fin 3, x j := by
  simp only [Fin.prod_univ_three]
  ring

theorem fin_three_product_except_scalar (κ : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    (∏ j : Fin 3, if j = i then 1 else κ * x j) =
      κ ^ 2 * ∏ j : Fin 3, if j = i then 1 else x j := by
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

/-- The dynamic source trilinear estimate, normalized on the paper's torus.
Every time norm and weak derivative is retained. Only the fixed spatial measure
factor changes the constant; no interpolation or stability estimate is imported. -/
theorem normalized_dynamic_trilinear (externalTrilinear : LiWuTrilinearEstimate)
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f : Fin 3 → ℝ → Sobolev 0, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
          InSobolev 0 (CIntegral a b (fun t => (f 0 t).val)
            (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ∧
          ∀ i : Fin 3,
            hNorm 0 (CIntegral a b (fun t => (f 0 t).val)
              (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ≤
              C * (b - a) * (∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
              C * timeLInfinity a b (fun t => inclusionMap (-pStar) 0
                (by dsimp [pStar]; norm_num) (f i t)) *
                (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) := by
  obtain ⟨C, hC, hb⟩ := externalTrilinear.dynamic H hH hH1 0 le_rfl (by norm_num)
  refine ⟨C * sourceNormalization ^ 2, mul_pos hC (sq_pos_of_pos sourceNormalization_pos), ?_⟩
  intro a b ha hab hlength f df hf hdf hd
  obtain ⟨hmem, hbound⟩ := hb a b ha hab hlength f df hf hdf hd
  refine ⟨hmem, ?_⟩
  intro i
  have h := hbound i
  simp_rw [source_x_time_norm, source_zero_time_norm, fin_three_product_scalar,
    fin_three_product_except_scalar] at h
  change sourceNormalization * hNorm 0 _ ≤ C * (b - a) *
    (sourceNormalization ^ 3 * ∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
    C * (sourceNormalization * timeLInfinity a b (fun t => inclusionMap (-pStar) 0
      (by dsimp [pStar]; norm_num) (f i t))) *
    (sourceNormalization ^ 2 * ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) at h
  apply (mul_le_mul_iff_right₀ sourceNormalization_pos).mp
  calc
    _ ≤ _ := h
    _ = _ := by ring




theorem interpolationRemainder_eq (τ a t : ℝ) (f : Fourier) :
    interpolationRemainder τ a t f = frozenCross a t f + frozenSquare a t f -
      (((t - a) / τ : ℝ) : ℂ) • endpointCorrection τ a f := by
  unfold interpolationRemainder localInterpolation
  abel

theorem grid_interval_length {τ : ℝ} (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)) :
    t - (n : ℝ) * τ ≤ τ := by
  have hEnd : ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ := by push_cast; ring
  linarith [ht.2]

theorem grid_interval_fraction {τ : ℝ} (hτ : 0 < τ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)) :
    0 ≤ (t - (n : ℝ) * τ) / τ ∧ (t - (n : ℝ) * τ) / τ ≤ 1 :=
  ⟨div_nonneg (sub_nonneg.mpr ht.1) hτ.le, (div_le_one hτ).mpr (grid_interval_length n ht)⟩

/-- The strong defect norm (23), with constants before the numerical input. -/
theorem numerical_defect_l2_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate) (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cc, hCc, hcross⟩ := numerical_cross_bound externalStage externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cq, hCq, hsquare⟩ := numerical_square_integral_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Cc + Cq + Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  obtain ⟨hC, hCb⟩ := hcross τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  obtain ⟨hQ, hQb⟩ := hsquare τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let rfrac : ℝ := (t - (n : ℝ) * τ) / τ
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hrfrac := grid_interval_fraction hτ n ht
  have hscaled : hNorm 0 ((rfrac : ℂ) • endpointCorrection τ ((n : ℝ) * τ) f.val) ≤ Cw * τ * q := by
    rw [hNorm_smul hW0, Complex.norm_real, Real.norm_of_nonneg hrfrac.1]
    exact (mul_le_mul_of_nonneg_right hrfrac.2 (hNorm_nonneg _ _)).trans (by simpa only [one_mul] using hWb)
  rw [interpolationRemainder_eq]
  refine ⟨(hC.add hQ).sub (hW0.smul _), ?_⟩
  have hb := hNorm_sub_le (hC.add hQ) (hW0.smul (rfrac : ℂ))
  have hb' := hNorm_add_le hC hQ
  change hNorm 0 _ ≤ (Cc + Cq + Cw) * q
  have hQb' : hNorm 0 (frozenSquare ((n : ℝ) * τ) t f.val) ≤ Cq * q :=
    hQb.trans (by nlinarith [mul_nonneg hCq.le hq])
  have hscaled' : hNorm 0 ((rfrac : ℂ) • endpointCorrection τ ((n : ℝ) * τ) f.val) ≤ Cw * q :=
    hscaled.trans (by nlinarith [mul_nonneg hCw.le hq])
  linarith

/-- The inverse-derivative cross-integral bound in (22), proved by commuting
the coefficient multiplier with the Bochner integral. -/
theorem numerical_cross_inverse_integral_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (inverseDerivative (frozenCross ((n : ℝ) * τ) t f.val)) ∧
          hNorm 0 (inverseDerivative (frozenCross ((n : ℝ) * τ) t f.val)) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨C, hC, hb⟩ := numerical_cross_inverse_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨C, hC, ?_⟩
  intro τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let g : ℝ → Sobolev 0 := fun s => inverseDerivativeSameMap 0
    (inclusionMap 0 1 (by norm_num) (BTwoBundled s f (stageTwoBundled a s f f)))
  have hg : Continuous g := (inverseDerivativeSameMap 0).continuous.comp
    ((inclusionMap 0 1 (by norm_num)).continuous.comp (continuous_cross_integrand a f))
  have hB : ∀ s ∈ Set.Icc a t, ‖g s‖ ≤ C * q := by
    intro s hs
    rw [sobolev_norm]
    exact (hb τ n s hτ hτ1 hnT ⟨hs.1, hs.2.trans ht.2⟩ f.val w
      (f.property.of_le (by norm_num)) hw hwm hwM hδ).2
  obtain ⟨hI, hIb⟩ := coefficient_integral_bound hg ht.1 hB
  have heq : inverseDerivative (frozenCross a t f.val) =
      fun k => ∫ s : ℝ in a..t, (g s).val k :=
    inverseDerivative_integral a t (fun s => B s f.val (bilinearStage a s f.val f.val))
  rw [heq]
  refine ⟨hI, hIb.trans ?_⟩
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  calc
    C * q * (t - a) ≤ C * q * τ := mul_le_mul_of_nonneg_left (grid_interval_length n ht) (mul_nonneg hC.le hq)
    _ = _ := by ring




theorem MeanZero.add {f g : Fourier} (hf : MeanZero f) (hg : MeanZero g) : MeanZero (f + g) := by
  change f 0 + g 0 = 0
  rw [hf, hg, add_zero]

theorem MeanZero.sub {f g : Fourier} (hf : MeanZero f) (hg : MeanZero g) : MeanZero (f - g) := by
  change f 0 - g 0 = 0
  rw [hf, hg, sub_zero]

theorem MeanZero.smul {f : Fourier} (hf : MeanZero f) (z : ℂ) : MeanZero (z • f) := by
  change z * f 0 = 0
  rw [hf, mul_zero]

theorem endpointCorrection_meanZero (τ a : ℝ) (f : Fourier) : MeanZero (endpointCorrection τ a f) :=
  (frozenSquare_meanZero a (a + τ) f).add (remainder_meanZero τ a f f f)

theorem localInterpolation_meanZero (τ a t : ℝ) {f : Fourier} (hf : MeanZero f) :
    MeanZero (localInterpolation τ a t f) :=
  (((hf.add (stage_meanZero a t f f)).add (frozenCross_meanZero a t f)).add
    (frozenSquare_meanZero a t f)).sub ((endpointCorrection_meanZero τ a f).smul _)

theorem interpolationRemainder_meanZero (τ a t : ℝ) {f : Fourier} (hf : MeanZero f) :
    MeanZero (interpolationRemainder τ a t f) :=
  (localInterpolation_meanZero τ a t hf).sub (hf.add (stage_meanZero a t f f))

/-- Mean-zero negative norms of order at least one are controlled by the
inverse derivative, exactly as used in the small-norm part of (24). -/
theorem negative_hNorm_le_inverse {p : ℝ} (hp : 1 ≤ p) {f : Fourier}
    (hf : InSobolev 0 f) (hfm : MeanZero f) :
    hNorm (-p) f ≤ hNorm 0 (inverseDerivative f) := by
  have hi := inverseDerivative_inSobolev_same hf
  have hb (k : ℤ) : ‖weighted (-p) f k‖ ≤ 1 * ‖weighted 0 (inverseDerivative f) k‖ := by
    by_cases hk : k = 0
    · subst k
      have hz : f 0 = 0 := hfm
      simp [weighted, hz, inverseDerivative]
    · have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (intCast_ne_zero hk)
      have hw : weight (-p) k ≤ |(k : ℝ)|⁻¹ := by
        calc
          _ ≤ weight (-1) k := weight_mono (by linarith : -p ≤ -1) k
          _ = (weight 1 k)⁻¹ := by simpa using weight_neg 1 k
          _ ≤ _ := inv_anti₀ hkpos (weight_one_ge_abs k)
      rw [norm_weighted, weighted_zero]
      simp only [one_mul, inverseDerivative, if_neg hk, norm_mul, norm_inv,
        Complex.norm_I, Complex.norm_intCast]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (f k))
  simpa only [one_mul] using hNorm_le_of_weighted_bound hi (by norm_num : (0 : ℝ) ≤ 1) hb




theorem interpolationRemainder_inverse_estimate {τ a t A B D : ℝ} {f : Fourier}
    (hc : InSobolev 0 (frozenCross a t f)) (hq : InSobolev 0 (frozenSquare a t f))
    (hw : InSobolev 0 (endpointCorrection τ a f))
    (hfrac : 0 ≤ (t - a) / τ ∧ (t - a) / τ ≤ 1)
    (hC : hNorm 0 (inverseDerivative (frozenCross a t f)) ≤ A)
    (hQ : hNorm 0 (frozenSquare a t f) ≤ B)
    (hW : hNorm 0 (endpointCorrection τ a f) ≤ D) :
    hNorm 0 (inverseDerivative (interpolationRemainder τ a t f)) ≤ A + B + D := by
  have hci := inverseDerivative_inSobolev_same hc
  have hqi := inverseDerivative_inSobolev_same hq
  have hwi := inverseDerivative_inSobolev_same hw
  rw [interpolationRemainder_eq, inverseDerivative_sub, inverseDerivative_add, inverseDerivative_smul]
  have hs := hNorm_sub_le (hci.add hqi) (hwi.smul ((((t - a) / τ) : ℝ) : ℂ))
  have hs' := hNorm_add_le hci hqi
  have hQ' := (inverseDerivative_hNorm_same hq).trans hQ
  have hW' : hNorm 0 (((((t - a) / τ) : ℝ) : ℂ) • inverseDerivative (endpointCorrection τ a f)) ≤ D := by
    rw [hNorm_smul hwi, Complex.norm_real, Real.norm_of_nonneg hfrac.1]
    exact (mul_le_mul_of_nonneg_right hfrac.2 (hNorm_nonneg _ _)).trans
      (by simpa only [one_mul] using (inverseDerivative_hNorm_same hw).trans hW)
  linarith

/-- The small inverse-derivative and negative-norm bounds in (22),(24),
with constants independent of all higher numerical Sobolev norms. -/
theorem numerical_defect_negative_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (inverseDerivative (interpolationRemainder τ ((n : ℝ) * τ) t f.val)) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          hNorm (-pStar) (interpolationRemainder τ ((n : ℝ) * τ) t f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cc, hCc, hcross⟩ := numerical_cross_inverse_integral_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cq, hCq, hsquare⟩ := numerical_square_integral_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Cc + Cq + Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  obtain ⟨hIC, hICb⟩ := hcross τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  obtain ⟨hQ, hQb⟩ := hsquare τ n hτ hτ1 hnT f w hw hwm hwM hδ t ht
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have hC : InSobolev 0 (frozenCross ((n : ℝ) * τ) t f.val) := by
    rw [← frozenCrossBundled_val _ _ f]
    exact (frozenCrossBundled _ _ f).property.of_le (by norm_num)
  have hY : InSobolev 0 (interpolationRemainder τ ((n : ℝ) * τ) t f.val) := by
    rw [interpolationRemainder_eq]
    exact (hC.add hQ).sub (hW0.smul _)
  have hInv := interpolationRemainder_inverse_estimate hC hQ hW0
    (grid_interval_fraction hτ n ht) hICb hQb hWb
  have hInv' : hNorm 0 (inverseDerivative (interpolationRemainder τ ((n : ℝ) * τ) t f.val)) ≤
      (Cc + Cq + Cw) * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
    calc
      _ ≤ _ := hInv
      _ = _ := by ring
  exact ⟨hY, hInv', (negative_hNorm_le_inverse (by norm_num [pStar]) hY
    (interpolationRemainder_meanZero τ _ t hfm)).trans hInv'⟩




def interpolationRemainderDerivative (τ a t : ℝ) (f : Fourier) : Fourier :=
  B t f (bilinearStage a t f f) +
    (1 / 2 : ℂ) • B t (bilinearStage a t f f) (bilinearStage a t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f

theorem interpolationRemainderDerivative_meanZero (τ a t : ℝ) (f : Fourier) :
    MeanZero (interpolationRemainderDerivative τ a t f) :=
  ((B_meanZero t _ _).add ((B_meanZero t _ _).smul _)).sub ((endpointCorrection_meanZero τ a f).smul _)

theorem interpolationRemainder_hasDerivAt {τ a t : ℝ} (f : Sobolev 2)
    (hfm : MeanZero f.val) (k : ℤ) :
    HasDerivAt (fun r : ℝ => interpolationRemainder τ a r f.val k)
      (interpolationRemainderDerivative τ a t f.val k) t := by
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hv := localInterpolation_hasDerivAt (τ := τ) (a := a) (t := t) f hfm k
  have hz := (hasDerivAt_const t (f.val k)).add (stage_hasDerivAt hf0 hf0 hfm hfm a t k)
  have h := hv.sub hz
  have hd : localInterpolationDerivative τ a t f.val k -
      (0 + (1 / 2 : ℂ) * B t f.val f.val k) = interpolationRemainderDerivative τ a t f.val k := by
    change (1 / 2 : ℂ) * B t f.val f.val k + _ + _ - _ -
      (0 + (1 / 2 : ℂ) * B t f.val f.val k) = _
    simp only [interpolationRemainderDerivative, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [interpolationRemainder, Pi.add_apply, Pi.sub_apply, hd] using! h

def defectBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  frozenCrossBundled ((n : ℝ) * τ) t f + frozenSquareBundled ((n : ℝ) * τ) t f -
    ((((t - (n : ℝ) * τ) / τ) : ℝ) : ℂ) •
      endpointCorrectionBundled externalStep τ hτ n f hfr hfm

def defectDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 1 :=
  BTwoBundled t f (stageTwoBundled ((n : ℝ) * τ) t f f) +
    (1 / 2 : ℂ) • BTwoBundled t (stageTwoBundled ((n : ℝ) * τ) t f f)
      (stageTwoBundled ((n : ℝ) * τ) t f f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrectionBundled externalStep τ hτ n f hfr hfm

theorem defectBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (defectBundled externalStep τ hτ n t f hfr hfm).val =
      interpolationRemainder τ ((n : ℝ) * τ) t f.val := by
  change (frozenCrossBundled _ t f).val + (frozenSquareBundled _ t f).val - _ = _
  rw [frozenCrossBundled_val, frozenSquareBundled_val, interpolationRemainder_eq]
  rfl

theorem defectDerivativeBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (defectDerivativeBundled externalStep τ hτ n t f hfr hfm).val =
      interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val := rfl

theorem continuous_defectBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => defectBundled externalStep τ hτ n t f hfr hfm) := by
  unfold defectBundled
  have hC := continuous_frozenCrossBundled ((n : ℝ) * τ) f
  have hQ := continuous_frozenSquareBundled ((n : ℝ) * τ) f
  fun_prop

theorem continuous_defectDerivativeBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => defectDerivativeBundled externalStep τ hτ n t f hfr hfm) := by
  unfold defectDerivativeBundled
  have hC := continuous_cross_integrand ((n : ℝ) * τ) f
  have hQ := continuous_square_integrand ((n : ℝ) * τ) f
  fun_prop

theorem interpolationRemainder_regular (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    RegularFourierPath ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ)
      (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val)
      (fun t => interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val) := by
  have h := regularFourierPath_of_bundled
    (a := (n : ℝ) * τ) (b := ((n + 1 : ℕ) : ℝ) * τ)
    (continuous_defectBundled externalStep τ hτ n f hfr hfm)
    (continuous_defectDerivativeBundled externalStep τ hτ n f hfr hfm)
    (fun t _ k => by
      simp_rw [defectBundled_val, defectDerivativeBundled_val]
      exact interpolationRemainder_hasDerivAt f hfm k)
  simpa only [defectBundled_val, defectDerivativeBundled_val] using h




/-- The derivative bound in (22), hence the negative derivative norm needed
for (24). Every estimate is derived from the actual interpolation formula. -/
theorem numerical_defect_derivative_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (inverseDerivative (interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val)) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          hNorm (-pStar) (interpolationRemainderDerivative τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Ci, hCi, hcross⟩ := numerical_cross_inverse_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cb, hCb, hquad⟩ := numerical_stage_square_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨Ci + Cb / 2 + Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let F : Fourier := bilinearStage a t f.val f.val
  let W : Fourier := endpointCorrection τ a f.val
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  obtain ⟨hIC, hICb⟩ := hcross τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ
  obtain ⟨hB, hBb⟩ := hquad τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have hC0 : InSobolev 0 (B t f.val F) :=
    (B_h1_of_h2 f.property (stageTwoBundled a t f f).property t).1.of_le (by norm_num)
  have hY : InSobolev 0 (interpolationRemainderDerivative τ a t f.val) :=
    (hC0.add (hB.smul (1 / 2 : ℂ))).sub (hW0.smul _)
  have hIB := inverseDerivative_inSobolev_same hB
  have hIW := inverseDerivative_inSobolev_same hW0
  have hSW : hNorm 0 (((τ⁻¹ : ℝ) : ℂ) • inverseDerivative W) ≤ Cw * q := by
    rw [hNorm_smul hIW, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hτ.le)]
    calc
      _ ≤ τ⁻¹ * (Cw * τ * q) :=
        mul_le_mul_of_nonneg_left ((inverseDerivative_hNorm_same hW0).trans hWb) (inv_nonneg.mpr hτ.le)
      _ = _ := by field_simp [hτ.ne']
  have hSB : hNorm 0 ((1 / 2 : ℂ) • inverseDerivative (B t F F)) ≤ (Cb / 2) * q := by
    rw [hNorm_smul hIB]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    have hh := (inverseDerivative_hNorm_same hB).trans hBb
    linarith
  have hInv : hNorm 0 (inverseDerivative (interpolationRemainderDerivative τ a t f.val)) ≤
      (Ci + Cb / 2 + Cw) * q := by
    rw [interpolationRemainderDerivative, inverseDerivative_sub, inverseDerivative_add,
      inverseDerivative_smul, inverseDerivative_smul]
    have hnorm := hNorm_sub_le (hIC.add (hIB.smul (1 / 2 : ℂ))) (hIW.smul ((τ⁻¹ : ℝ) : ℂ))
    have hnorm' := hNorm_add_le hIC (hIB.smul (1 / 2 : ℂ))
    linarith
  exact ⟨hY, hInv, (negative_hNorm_le_inverse (by norm_num [pStar]) hY
    (interpolationRemainderDerivative_meanZero τ a t f.val)).trans hInv⟩




theorem continuousOn_memLp_top_Icc {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → E} (hf : ContinuousOn f (Set.Icc a b)) :
    MemLp f ∞ (volume.restrict (Set.Icc a b)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hf.norm).bddAbove
  exact MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) B (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hB ⟨t, ht, rfl⟩)

theorem timeLInfinity_le_of_bound {s A a b : ℝ} (hA : 0 ≤ A)
    (f : ℝ → Sobolev s) (hf : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ A) :
    timeLInfinity a b f ≤ A := by
  have hs := sourceLInfinity_le_of_bound hA a b f (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hf t ht)
  change sourceNormalization * timeLInfinity a b f ≤ sourceNormalization * A at hs
  exact (mul_le_mul_iff_right₀ sourceNormalization_pos).mp hs

def defectL2Path (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) : Sobolev 0 :=
  inclusionMap 0 1 (by norm_num) (defectBundled externalStep τ hτ n t f hfr hfm)

def defectNegativeDerivativePath (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) : Sobolev (-pStar) :=
  inclusionMap (-pStar) 1 (by norm_num [pStar]) (defectDerivativeBundled externalStep τ hτ n t f hfr hfm)

/-- All hypotheses and both time-norm bounds in (24) for the actual defect
path. The weak derivative is proved, and the essential time norms are genuine
`eLpNorm` values on the closed step interval. -/
theorem numerical_defect_time_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      ∀ hτ : 0 < τ, τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        let a := (n : ℝ) * τ
        let b := ((n + 1 : ℕ) : ℝ) * τ
        let Y := defectL2Path externalStep τ hτ n f hfr hfm
        let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
        MemLp Y ∞ (volume.restrict (Set.Icc a b)) ∧
        MemLp dY ∞ (volume.restrict (Set.Icc a b)) ∧
        WeakTimeDerivative a b (fun t => (Y t).val) (fun t => (dY t).val) ∧
        timeXNorm a b Y dY ≤ C * (τ ^ γ + hNorm 0 (f.val - w)) ∧
        timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤
          C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨C0, hC0, hL2⟩ := numerical_defect_l2_bound externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hd⟩ := numerical_defect_derivative_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cn, hCn, hn⟩ := numerical_defect_negative_bound externalStage externalProduct hT hγ hγ1 hM
  refine ⟨C0 + Cd + Cn, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ
  dsimp only
  let a : ℝ := (n : ℝ) * τ
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  let Y := defectL2Path externalStep τ hτ n f hfr hfm
  let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hYC : Continuous Y := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_defectBundled externalStep τ hτ n f hfr hfm)
  have hdYC : Continuous dY := (inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp
    (continuous_defectDerivativeBundled externalStep τ hτ n f hfr hfm)
  refine ⟨continuousOn_memLp_top_Icc hYC.continuousOn,
    continuousOn_memLp_top_Icc hdYC.continuousOn, ?_, ?_, ?_⟩
  · have hab : a ≤ b := by
      dsimp [a, b]
      push_cast
      nlinarith
    have hw' := (interpolationRemainder_regular externalStep τ hτ n f hfr hfm).weakTimeDerivative hab
    simpa only [Y, dY, defectL2Path, defectNegativeDerivativePath,
      show ∀ s r h (f : Sobolev r), (inclusionMap s r h f).val = f.val from fun _ _ _ _ => rfl,
      defectBundled_val, defectDerivativeBundled_val] using hw'
  · have hYb : timeLInfinity a b Y ≤ C0 * q := timeLInfinity_le_of_bound (mul_nonneg hC0.le hq) Y (by
      intro t ht
      rw [sobolev_norm]
      change hNorm 0 (defectBundled externalStep τ hτ n t f hfr hfm).val ≤ C0 * q
      rw [defectBundled_val]
      exact (hL2 τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2)
    have hdYb : timeLInfinity a b dY ≤ Cd * q := timeLInfinity_le_of_bound (mul_nonneg hCd.le hq) dY (by
      intro t ht
      rw [sobolev_norm]
      change hNorm (-pStar) (defectDerivativeBundled externalStep τ hτ n t f hfr hfm).val ≤ Cd * q
      rw [defectDerivativeBundled_val]
      exact (hd τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2.2)
    change timeLInfinity a b Y + timeLInfinity a b dY ≤ _
    nlinarith
  · have hnb : timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤
        Cn * τ * q := timeLInfinity_le_of_bound (mul_nonneg (mul_nonneg hCn.le hτ.le) hq) _ (by
      intro t ht
      rw [sobolev_norm]
      change hNorm (-pStar) (defectBundled externalStep τ hτ n t f hfr hfm).val ≤ Cn * τ * q
      rw [defectBundled_val]
      exact (hn τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2.2)
    exact hnb.trans (by nlinarith [mul_nonneg hC0.le (mul_nonneg hτ.le hq), mul_nonneg hCd.le (mul_nonneg hτ.le hq)])




theorem RegularFourierPath.restrict {a b c d : ℝ} {f df : ℝ → Fourier}
    (hf : RegularFourierPath a b f df) (hac : a ≤ c) (hdb : d ≤ b) :
    RegularFourierPath c d f df where
  continuous k := (hf.continuous k).mono (fun _ ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩)
  derivative_continuous k := (hf.derivative_continuous k).mono (fun _ ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩)
  hasDerivAt t ht := hf.hasDerivAt t ⟨lt_of_le_of_lt hac ht.1, lt_of_lt_of_le ht.2 hdb⟩
  envelope := by
    obtain ⟨F, Fd, hF, hFd, hb⟩ := hf.envelope
    exact ⟨F, Fd, hF, hFd, fun t ht => hb t ⟨hac.trans ht.1, ht.2.trans hdb⟩⟩

theorem timeLInfinity_mono_interval {s a b c d : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (hsub : Set.Icc c d ⊆ Set.Icc a b) :
    timeLInfinity c d f ≤ timeLInfinity a b f := by
  exact ENNReal.toReal_mono hf.2.ne (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))

theorem memLp_mono_interval {s a b c d : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (hsub : Set.Icc c d ⊆ Set.Icc a b) :
    MemLp f ∞ (volume.restrict (Set.Icc c d)) :=
  MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hf

theorem timeLInfinity_nonneg {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) :
    0 ≤ timeLInfinity a b f := ENNReal.toReal_nonneg

theorem timeXNorm_nonneg (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) :
    0 ≤ timeXNorm a b f df := add_nonneg (timeLInfinity_nonneg _ _ _) (timeLInfinity_nonneg _ _ _)

def JZeroBundled (t : ℝ) (f g : Sobolev 0) : Sobolev 1 :=
  airyMap 1 (-t) (removeMeanMap 1 (productMap
    (airyMap 1 t (inverseDerivativeMap f)) (airyMap 1 t (inverseDerivativeMap g))))

theorem JZeroBundled_val (t : ℝ) (f g : Sobolev 0) : (JZeroBundled t f g).val = J t f.val g.val := rfl

theorem continuous_JZeroBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g : X → Sobolev 0} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => JZeroBundled (t x) (f x) (g x)) := by
  unfold JZeroBundled
  have hf' := continuous_airy_apply 1 ht ((inverseDerivativeMap).continuous.comp hf)
  have hg' := continuous_airy_apply 1 ht ((inverseDerivativeMap).continuous.comp hg)
  apply continuous_airy_apply 1 ht.neg
  fun_prop

theorem B_add_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t (f + g) h = B t f h + B t g h := by
  unfold B
  rw [airy_add, product_add_left (airy_inSobolev hf t) (airy_inSobolev hg t)
    (airy_inSobolev hh t), derivative_add, airy_add]

theorem B_add_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t f (g + h) = B t f g + B t f h := by
  rw [B_comm t f (g + h), B_add_left hg hh hf, B_comm t g f, B_comm t h f]

theorem B_smul_left (t : ℝ) (z : ℂ) (f g : Fourier) : B t (z • f) g = z • B t f g := by
  unfold B
  rw [airy_smul, product_smul_left, derivative_smul, airy_smul]

theorem B_smul_right (t : ℝ) (z : ℂ) (f g : Fourier) : B t f (z • g) = z • B t f g := by
  rw [B_comm t f (z • g), B_smul_left, B_comm t g f]

theorem B_diagonal_add {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g) (t : ℝ) :
    B t (f + g) (f + g) = B t f f + (2 : ℂ) • B t f g + B t g g := by
  rw [B_add_left hf hg (hf.add hg), B_add_right hf hf hg, B_add_right hg hf hg, B_comm t g f]
  module




/-- A useful specialization of the dynamic trilinear estimate: two frozen
inputs and a moving defect, with the small negative norm on the moving slot. -/
theorem dynamic_constant_pair_bound (externalTrilinear : LiWuTrilinearEstimate)
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f : Sobolev 1, ∀ Y : ℝ → Sobolev 0, ∀ dY : ℝ → Sobolev (-pStar),
        MemLp Y ∞ (volume.restrict (Set.Icc a b)) →
        MemLp dY ∞ (volume.restrict (Set.Icc a b)) →
        WeakTimeDerivative a b (fun t => (Y t).val) (fun t => (dY t).val) →
        ∀ M A B : ℝ, 0 ≤ M → 0 ≤ A → 0 ≤ B → hNorm 0 f.val ≤ M →
          timeXNorm a b Y dY ≤ A →
          timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤ B →
          InSobolev 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)) ∧
          hNorm 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)) ≤
            C * (b - a) * M ^ 2 * A + C * B * M ^ 2 := by
  obtain ⟨C, hC, hb⟩ := normalized_dynamic_trilinear externalTrilinear hH hH1
  refine ⟨C, hC, ?_⟩
  intro a b ha hab hlen f Y dY hY hdY hweak M A B hM hA hB hfM hXA hNB
  let F : ℝ → Sobolev 0 := fun _ => inclusionMap 0 1 (by norm_num) f
  let Z : ℝ → Sobolev (-pStar) := fun _ => 0
  have hF : MemLp F ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc continuousOn_const
  have hZ : MemLp Z ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc continuousOn_const
  have hW : WeakTimeDerivative a b (fun t => (F t).val) (fun t => (Z t).val) :=
    (constant_regular a b f).weakTimeDerivative hab
  let fs : Fin 3 → ℝ → Sobolev 0 := ![F, F, Y]
  let ds : Fin 3 → ℝ → Sobolev (-pStar) := ![Z, Z, dY]
  obtain ⟨hmem, hbound⟩ := hb a b ha hab hlen fs ds
    (by intro j; fin_cases j <;> first | exact hF | exact hY)
    (by intro j; fin_cases j <;> first | exact hZ | exact hdY)
    (by intro j; fin_cases j <;> first | exact hW | exact hweak)
  have hconst : timeLInfinity a b F ≤ M := timeLInfinity_le_of_bound hM F (by
    intro t _
    rw [sobolev_norm]
    exact hfM)
  have hzero : timeLInfinity a b Z = 0 := by
    change (eLpNorm (0 : ℝ → Sobolev (-pStar)) ∞ (volume.restrict (Set.Icc a b))).toReal = 0
    rw [eLpNorm_zero, ENNReal.toReal_zero]
  have hconstX : timeXNorm a b F Z ≤ M := by simpa only [timeXNorm, hzero, add_zero] using hconst
  have hprod := hbound 2
  simp [fs, ds, Fin.prod_univ_three] at hprod
  refine ⟨hmem, hprod.trans ?_⟩
  have hF0 := timeLInfinity_nonneg a b F
  have hFX0 := timeXNorm_nonneg a b F Z
  have hYX0 := timeXNorm_nonneg a b Y dY
  have hYN0 := timeLInfinity_nonneg a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t))
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  calc
    _ ≤ C * (b - a) * (M * M * A) + C * B * (M * M) := by gcongr
    _ = _ := by ring




theorem coefficientMap_apply (s : ℝ) (k : ℤ) (f : Sobolev s) :
    coefficientMap s k f = f.val k := rfl

def frozenZ (a t : ℝ) (f : Fourier) : Fourier := f + bilinearStage a t f f

def localResidualDerivative (τ a t : ℝ) (f : Fourier) : Fourier :=
  - B t (interpolationRemainder τ a t f) (frozenZ a t f) -
    (1 / 2 : ℂ) • B t (interpolationRemainder τ a t f) (interpolationRemainder τ a t f) -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f

def localResidual (τ a t : ℝ) (f : Fourier) : Fourier := fun k =>
  -(∫ s : ℝ in a..t, B s (interpolationRemainder τ a s f) (frozenZ a s f) k) -
    (1 / 2 : ℂ) * (∫ s : ℝ in a..t,
      B s (interpolationRemainder τ a s f) (interpolationRemainder τ a s f) k) -
    (((t - a) / τ : ℝ) : ℂ) * endpointCorrection τ a f k

@[simp] theorem localResidual_left (τ a : ℝ) (f : Fourier) : localResidual τ a a f = 0 := by
  funext k
  simp [localResidual]

/-- The differential perturbation identity for the actual interpolation. -/
theorem localInterpolation_perturbation_identity {τ a t : ℝ} {f : Fourier}
    (hf : InSobolev 0 f) (hY : InSobolev 0 (interpolationRemainder τ a t f)) :
    localInterpolationDerivative τ a t f =
      (1 / 2 : ℂ) • B t (localInterpolation τ a t f) (localInterpolation τ a t f) +
        localResidualDerivative τ a t f := by
  have hF := (bilinearStage_h1_bound hf hf a t).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hZ : InSobolev 0 (frozenZ a t f) := hf.add hF
  have heq : localInterpolation τ a t f = frozenZ a t f + interpolationRemainder τ a t f := by
    unfold frozenZ interpolationRemainder
    abel
  rw [heq, B_diagonal_add hZ hY]
  rw [B_comm t (frozenZ a t f) (interpolationRemainder τ a t f)]
  change localInterpolationDerivative τ a t f =
    (1 / 2 : ℂ) • (B t (f + bilinearStage a t f f) (f + bilinearStage a t f f) +
      (2 : ℂ) • B t (interpolationRemainder τ a t f) (frozenZ a t f) +
      B t (interpolationRemainder τ a t f) (interpolationRemainder τ a t f)) + _
  rw [B_diagonal_add hf hF]
  unfold localInterpolationDerivative localResidualDerivative
  module

def derivativeOneLinear : Sobolev 1 →ₗ[ℂ] Sobolev 0 where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := 0) (by norm_num; exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeOneMap : Sobolev 1 →L[ℂ] Sobolev 0 :=
  derivativeOneLinear.mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm 0 (derivative f.val) ≤ hNorm 1 f.val
    have h := derivative_hNorm (s := 0) (by norm_num; exact f.property)
    norm_num at h
    exact h)

def BOneBundled (t : ℝ) (f g : Sobolev 1) : Sobolev 0 :=
  airyMap 0 (-t) (derivativeOneMap (productMap (airyMap 1 t f) (airyMap 1 t g)))

theorem BOneBundled_val (t : ℝ) (f g : Sobolev 1) :
    (BOneBundled t f g).val = B t f.val g.val := rfl

theorem continuous_BOneBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g : X → Sobolev 1} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => BOneBundled (t x) (f x) (g x)) := by
  unfold BOneBundled
  have hf' := continuous_airy_apply 1 ht hf
  have hg' := continuous_airy_apply 1 ht hg
  apply continuous_airy_apply 0 ht.neg
  fun_prop

def frozenZBundled (a t : ℝ) (f : Sobolev 2) : Sobolev 1 :=
  inclusionMap 1 2 (by norm_num) (f + stageTwoBundled a t f f)

theorem frozenZBundled_val (a t : ℝ) (f : Sobolev 2) :
    (frozenZBundled a t f).val = frozenZ a t f.val := rfl

theorem continuous_frozenZBundled (a : ℝ) (f : Sobolev 2) :
    Continuous (fun t : ℝ => frozenZBundled a t f) := by
  unfold frozenZBundled
  fun_prop

theorem continuous_residual_integrands (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => BOneBundled t (defectBundled externalStep τ hτ n t f hfr hfm)
      (frozenZBundled ((n : ℝ) * τ) t f)) ∧
    Continuous (fun t : ℝ => BOneBundled t (defectBundled externalStep τ hτ n t f hfr hfm)
      (defectBundled externalStep τ hτ n t f hfr hfm)) := by
  have hY := continuous_defectBundled externalStep τ hτ n f hfr hfm
  exact ⟨continuous_BOneBundled continuous_id hY (continuous_frozenZBundled _ f),
    continuous_BOneBundled continuous_id hY hY⟩

theorem localResidual_hasDerivAt (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun r : ℝ => localResidual τ ((n : ℝ) * τ) r f.val k)
      (localResidualDerivative τ ((n : ℝ) * τ) t f.val k) t := by
  let a : ℝ := (n : ℝ) * τ
  obtain ⟨hC, hQ⟩ := continuous_residual_integrands externalStep τ hτ n f hfr hfm
  have hc : Continuous (fun s : ℝ => B s (interpolationRemainder τ a s f.val) (frozenZ a s f.val) k) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, defectBundled_val, frozenZBundled_val] using
      (coefficientMap 0 k).continuous.comp hC
  have hq : Continuous (fun s : ℝ => B s (interpolationRemainder τ a s f.val)
      (interpolationRemainder τ a s f.val) k) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, defectBundled_val] using (coefficientMap 0 k).continuous.comp hQ
  have hci := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hqi := intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a t)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hlin : HasDerivAt (fun r : ℝ => (((r - a) / τ : ℝ) : ℂ)) ((τ⁻¹ : ℝ) : ℂ) t := by
    simpa only [one_div, id_eq] using! (((hasDerivAt_id t).sub_const a).div_const τ).ofReal_comp
  have h := (hci.neg.sub (hqi.const_mul (1 / 2 : ℂ))).sub
    (hlin.mul_const (endpointCorrection τ a f.val k))
  simpa only [localResidual, localResidualDerivative, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul] using! h




/-- Equation (25) on one step, proved from the actual interpolation and its
residual. It is not a replacement definition of the numerical method. -/
theorem localInterpolation_integral_identity (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) (t : ℝ) :
    localInterpolation τ ((n : ℝ) * τ) t f.val = f.val +
      (1 / 2 : ℂ) • (fun k => ∫ s : ℝ in (n : ℝ) * τ..t,
        B s (localInterpolation τ ((n : ℝ) * τ) s f.val)
          (localInterpolation τ ((n : ℝ) * τ) s f.val) k) +
      localResidual τ ((n : ℝ) * τ) t f.val := by
  let a : ℝ := (n : ℝ) * τ
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hVC := continuous_localInterpolationBundled externalStep τ hτ n f hfr hfm
  have hBC := continuous_BOneBundled continuous_id hVC hVC
  funext k
  have hB : Continuous (fun s : ℝ => B s (localInterpolation τ a s f.val)
      (localInterpolation τ a s f.val) k) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val,
      localInterpolationBundled_val, id_eq, a] using (coefficientMap 0 k).continuous.comp hBC
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ =>
      localInterpolation τ a s f.val k - localResidual τ a s f.val k)
      ((1 / 2 : ℂ) * B r (localInterpolation τ a r f.val) (localInterpolation τ a r f.val) k) r := by
    have hY : InSobolev 0 (interpolationRemainder τ a r f.val) := by
      rw [← defectBundled_val externalStep τ hτ n r f hfr hfm]
      exact (defectBundled externalStep τ hτ n r f hfr hfm).property.of_le (by norm_num)
    have hp := congrFun (localInterpolation_perturbation_identity hf0 hY) k
    have h := (localInterpolation_hasDerivAt (τ := τ) (a := a) (t := r) f hfm k).sub
      (localResidual_hasDerivAt externalStep τ hτ n f hfr hfm r k)
    apply h.congr_deriv
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right] using
      congrArg (fun z : ℂ => z - localResidualDerivative τ a r f.val k) hp
  have hi : IntervalIntegrable (fun r : ℝ => (1 / 2 : ℂ) * B r
      (localInterpolation τ a r f.val) (localInterpolation τ a r f.val) k) volume a t :=
    (continuous_const.mul hB).intervalIntegrable a t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hv0 : localInterpolation τ a a f.val k = f.val k := congrFun (localInterpolation_left f.val) k
  have hr0 : localResidual τ a a f.val k = 0 := congrFun (localResidual_left τ a f.val) k
  rw [hv0, hr0, sub_zero] at hFTC
  change localInterpolation τ a t f.val k = f.val k + (1 / 2 : ℂ) *
    (∫ s : ℝ in a..t, B s (localInterpolation τ a s f.val) (localInterpolation τ a s f.val) k) +
      localResidual τ a t f.val k
  linear_combination -hFTC




theorem InSobolev.neg {s : ℝ} {f : Fourier} (hf : InSobolev s f) : InSobolev s (-f) := by
  simpa only [neg_one_smul] using hf.smul (-1 : ℂ)

set_option maxHeartbeats 800000 in
/-- The negative Sobolev bound for the actual residual derivative in (26). -/
theorem numerical_residual_derivative_bound (externalStage : LiWuStageEstimate)
    (externalProduct : LiWuProductEstimate) (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ∧
          hNorm (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cn, hCn, hstage⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cy, hCy, hdefect⟩ := numerical_defect_l2_bound externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  let Z : ℝ := M + 1 + 2 * Cn
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C : ℝ := 1 + K * Cy * Z + K * Cy * Cy + Cw
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let Y := interpolationRemainder τ a t f.val
  let z := frozenZ a t f.val
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq0 : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hq2 : q ≤ 2 := by dsimp [q]; linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hw0 := hw.of_le hγ.le
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hF0 := (bilinearStage_h1_bound hf0 hf0 a t).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hFb := (hstage τ n t hτ hτ1 hnT ht f.val w hf0 hw hwm hwM hδ).2.2.2
  have hFb' : hNorm 0 (bilinearStage a t f.val f.val) ≤ 2 * Cn :=
    hFb.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq2 hCn.le)
  have hz0 : InSobolev 0 z := hf0.add hF0
  have hzb : hNorm 0 z ≤ Z := by
    have hh := hNorm_add_le hf0 hF0
    change hNorm 0 z ≤ _ at hh
    dsimp [Z]
    linarith only [hh, hfM, hFb']
  obtain ⟨hY0, hYb⟩ := hdefect τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  have hYb' : hNorm 0 Y ≤ 2 * Cy :=
    hYb.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq2 hCy.le)
  obtain ⟨hB1, hB1b⟩ := B_negative_bound hY0 hz0 t
  obtain ⟨hB2, hB2b⟩ := B_negative_bound hY0 hY0 t
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  have hp : -pStar ≤ (0 : ℝ) := by norm_num [pStar]
  have hWneg := hW0.of_le hp
  have hSW : hNorm (-pStar) (((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) ≤ Cw * q := by
    rw [hNorm_smul hWneg, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hτ.le)]
    calc
      _ ≤ τ⁻¹ * (Cw * τ * q) := mul_le_mul_of_nonneg_left
        ((hNorm_mono hW0 hp).trans hWb) (inv_nonneg.mpr hτ.le)
      _ = _ := by field_simp [hτ.ne']
  have hB1b' : hNorm (-pStar) (B t Y z) ≤ K * Cy * Z * q := by
    calc
      _ ≤ K * hNorm 0 Y * hNorm 0 z := hB1b
      _ ≤ K * (Cy * q) * Z := mul_le_mul (mul_le_mul_of_nonneg_left hYb hK) hzb
        (hNorm_nonneg _ _) (mul_nonneg hK (mul_nonneg hCy.le hq0))
      _ = _ := by ring
  have hB2b' : hNorm (-pStar) (B t Y Y) ≤ 2 * K * Cy * Cy * q := by
    calc
      _ ≤ K * hNorm 0 Y * hNorm 0 Y := hB2b
      _ ≤ K * (Cy * q) * (2 * Cy) := mul_le_mul (mul_le_mul_of_nonneg_left hYb hK) hYb'
        (hNorm_nonneg _ _) (mul_nonneg hK (mul_nonneg hCy.le hq0))
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · change InSobolev (-pStar) (-B t Y z - (1 / 2 : ℂ) • B t Y Y -
      ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val)
    exact ((hB1.neg).sub (hB2.smul (1 / 2 : ℂ))).sub (hWneg.smul ((τ⁻¹ : ℝ) : ℂ))
  have hh := hNorm_sub_le ((hB1.neg).sub (hB2.smul (1 / 2 : ℂ))) (hWneg.smul ((τ⁻¹ : ℝ) : ℂ))
  have hh' := hNorm_sub_le (hB1.neg) (hB2.smul (1 / 2 : ℂ))
  rw [hNorm_neg, hNorm_smul hB2] at hh'
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf] at hh'
  change hNorm (-pStar) (-B t Y z - (1 / 2 : ℂ) • B t Y Y -
    ((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) ≤ C * q
  calc
    _ ≤ hNorm (-pStar) (-B t Y z - (1 / 2 : ℂ) • B t Y Y) +
        hNorm (-pStar) (((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) := hh
    _ ≤ (hNorm (-pStar) (B t Y z) + (1 / 2 : ℝ) * hNorm (-pStar) (B t Y Y)) +
        hNorm (-pStar) (((τ⁻¹ : ℝ) : ℂ) • endpointCorrection τ a f.val) := add_le_add hh' le_rfl
    _ ≤ (K * Cy * Z * q + (1 / 2 : ℝ) * (2 * K * Cy * Cy * q)) + Cw * q :=
      add_le_add (add_le_add hB1b' (mul_le_mul_of_nonneg_left hB2b' (by norm_num))) hSW
    _ ≤ C * q := by dsimp [C]; nlinarith only [hq0]




/-- An internal normal-form estimate retaining the endpoint and integrating
the actual differentiated path. Its hypotheses will be supplied by (22)-(24). -/
theorem integral_B_self_bound {a b A Ad M : ℝ} (hab : a ≤ b)
    (hA : 0 ≤ A) (hAd : 0 ≤ Ad) (_hM : 0 ≤ M)
    (Y dY : ℝ → Sobolev 1) (hYC : Continuous Y) (hdYC : Continuous dY)
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (Y r).val k) ((dY t).val k) t)
    (hm : ∀ t ∈ Set.Icc a b, MeanZero (Y t).val) (hleft : (Y a).val = 0)
    (hY : ∀ t ∈ Set.Icc a b, hNorm 0 (Y t).val ≤ M)
    (hIb : hNorm 0 (inverseDerivative (Y b).val) ≤ A)
    (hId : ∀ t ∈ Set.Icc a b, hNorm 0 (inverseDerivative (dY t).val) ≤ Ad) :
    InSobolev 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) ∧
    hNorm 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * A * M / 3 +
        (2 / 3 : ℝ) * (Real.sqrt 2 * h1EmbeddingConstant) * Ad * M * (b - a) := by
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one h1EmbeddingConstant_ge_one)
  let g : ℝ → Sobolev 0 := fun t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t (inclusionMap 0 1 (by norm_num) (dY t)) (inclusionMap 0 1 (by norm_num) (Y t)))
  have hg : Continuous g := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id ((inclusionMap 0 1 (by norm_num)).continuous.comp hdYC)
      ((inclusionMap 0 1 (by norm_num)).continuous.comp hYC))
  have hgb : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ K * Ad * M := by
    intro t ht
    rw [sobolev_norm]
    change hNorm 0 (J t (dY t).val (Y t).val) ≤ _
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (dY t).val) * hNorm 0 (Y t).val :=
        J_inverse_bound ((dY t).property.of_le (by norm_num)) ((Y t).property.of_le (by norm_num)) t
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hId t ht) hK) (hY t ht)
        (hNorm_nonneg _ _) (mul_nonneg hK hAd)
  obtain ⟨hI, hIn⟩ := coefficient_integral_bound hg hab hgb
  have hJ : InSobolev 0 (J b (Y b).val (Y b).val) :=
    (J_h1_bound ((Y b).property.of_le (by norm_num)) ((Y b).property.of_le (by norm_num)) b).1.of_le (by norm_num)
  have hJn : hNorm 0 (J b (Y b).val (Y b).val) ≤ K * A * M := by
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (Y b).val) * hNorm 0 (Y b).val :=
        J_inverse_bound ((Y b).property.of_le (by norm_num)) ((Y b).property.of_le (by norm_num)) b
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hIb hK) (hY b ⟨hab, le_rfl⟩)
        (hNorm_nonneg _ _) (mul_nonneg hK hA)
  have hreg := regularFourierPath_of_bundled hYC hdYC hd
  have heq : (fun k => ∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) =
      (1 / 3 : ℂ) • J b (Y b).val (Y b).val -
        (2 / 3 : ℂ) • (fun k => ∫ t : ℝ in a..b, (g t).val k) := by
    funext k
    have hn := variable_normal_form hab hreg hreg hm hm k
    have hfun : (fun t : ℝ => J t (dY t).val (Y t).val k + J t (Y t).val (dY t).val k) =
        (fun t : ℝ => (2 : ℂ) * J t (dY t).val (Y t).val k) := by
      funext t
      rw [J_comm t (Y t).val (dY t).val]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hleft, J_zero_left] at hn
    simp only [Pi.zero_apply, sub_zero] at hn
    change (∫ t : ℝ in a..b, B t (Y t).val (Y t).val k) =
      (1 / 3 : ℂ) * J b (Y b).val (Y b).val k -
        (2 / 3 : ℂ) * (∫ t : ℝ in a..b, J t (dY t).val (Y t).val k)
    linear_combination hn
  rw [heq]
  refine ⟨(hJ.smul _).sub (hI.smul _), ?_⟩
  have hs := hNorm_sub_le (hJ.smul (1 / 3 : ℂ)) (hI.smul (2 / 3 : ℂ))
  rw [hNorm_smul hJ, hNorm_smul hI] at hs
  have hn3 : ‖(1 / 3 : ℂ)‖ = (1 / 3 : ℝ) := by norm_num
  have hn23 : ‖(2 / 3 : ℂ)‖ = (2 / 3 : ℝ) := by norm_num
  rw [hn3, hn23] at hs
  change hNorm 0 _ ≤ K * A * M / 3 + (2 / 3 : ℝ) * K * Ad * M * (b - a)
  linarith




theorem inclusionMap_val (s r : ℝ) (h : s ≤ r) (f : Sobolev r) :
    (inclusionMap s r h f).val = f.val := rfl

theorem frozenZ_regular {a b : ℝ} (f : Sobolev 2) (hfm : MeanZero f.val) :
    RegularFourierPath a b (fun t => frozenZ a t f.val) (fun t => (1 / 2 : ℂ) • B t f.val f.val) := by
  have hdC : Continuous (fun t : ℝ => (1 / 2 : ℂ) • BTwoBundled t f f) :=
    (continuous_const (y := (1 / 2 : ℂ))).smul
      (continuous_BTwoBundled continuous_id continuous_const continuous_const)
  apply regularFourierPath_of_bundled (continuous_frozenZBundled a f) hdC
  intro t _ k
  have h := (hasDerivAt_const t (f.val k)).add (stage_hasDerivAt
    (f.property.of_le (by norm_num)) (f.property.of_le (by norm_num)) hfm hfm a t k)
  simpa only [zero_add] using! h

/-- Internal cross normal-form bound. The trilinear term is explicit; its
bound is supplied separately by the cited dynamic theorem with proved paths. -/
theorem integral_B_cross_bound {a b A Ad M E : ℝ} (hab : a ≤ b)
    (hA : 0 ≤ A) (hAd : 0 ≤ Ad) (_hM : 0 ≤ M)
    (f : Sobolev 2) (hfm : MeanZero f.val)
    (Y dY : ℝ → Sobolev 1) (hYC : Continuous Y) (hdYC : Continuous dY)
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (Y r).val k) ((dY t).val k) t)
    (hm : ∀ t ∈ Set.Icc a b, MeanZero (Y t).val) (hleft : (Y a).val = 0)
    (hZ : ∀ t ∈ Set.Icc a b, hNorm 0 (frozenZ a t f.val) ≤ M)
    (hIb : hNorm 0 (inverseDerivative (Y b).val) ≤ A)
    (hId : ∀ t ∈ Set.Icc a b, hNorm 0 (inverseDerivative (dY t).val) ≤ Ad)
    (hCI : InSobolev 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)))
    (hCIn : hNorm 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)) ≤ E) :
    InSobolev 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) ∧
    hNorm 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * A * M / 3 +
        (Real.sqrt 2 * h1EmbeddingConstant) * Ad * M * (b - a) / 3 + E / 6 := by
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one h1EmbeddingConstant_ge_one)
  let g : ℝ → Sobolev 0 := fun t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t (inclusionMap 0 1 (by norm_num) (dY t))
      (inclusionMap 0 1 (by norm_num) (frozenZBundled a t f)))
  have hg : Continuous g := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id ((inclusionMap 0 1 (by norm_num)).continuous.comp hdYC)
      ((inclusionMap 0 1 (by norm_num)).continuous.comp (continuous_frozenZBundled a f)))
  have hgb : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ K * Ad * M := by
    intro t ht
    rw [sobolev_norm]
    change hNorm 0 (J t (dY t).val (frozenZ a t f.val)) ≤ _
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (dY t).val) * hNorm 0 (frozenZ a t f.val) :=
        J_inverse_bound ((dY t).property.of_le (by norm_num))
          ((frozenZBundled a t f).property.of_le (by norm_num)) t
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hId t ht) hK) (hZ t ht)
        (hNorm_nonneg _ _) (mul_nonneg hK hAd)
  obtain ⟨hI, hIn⟩ := coefficient_integral_bound hg hab hgb
  have hJ : InSobolev 0 (J b (Y b).val (frozenZ a b f.val)) :=
    (J_h1_bound ((Y b).property.of_le (by norm_num))
      ((frozenZBundled a b f).property.of_le (by norm_num)) b).1.of_le (by norm_num)
  have hJn : hNorm 0 (J b (Y b).val (frozenZ a b f.val)) ≤ K * A * M := by
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (Y b).val) * hNorm 0 (frozenZ a b f.val) :=
        J_inverse_bound ((Y b).property.of_le (by norm_num))
          ((frozenZBundled a b f).property.of_le (by norm_num)) b
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hIb hK) (hZ b ⟨hab, le_rfl⟩)
        (hNorm_nonneg _ _) (mul_nonneg hK hA)
  have hregY := regularFourierPath_of_bundled hYC hdYC hd
  have hregZ := frozenZ_regular (a := a) (b := b) f hfm
  have hCIcont := continuous_JZeroBundled continuous_id
    ((inclusionMap 0 1 (by norm_num)).continuous.comp
      (continuous_BTwoBundled continuous_id (continuous_const (y := f)) (continuous_const (y := f))))
    ((inclusionMap 0 1 (by norm_num)).continuous.comp hYC)
  have heq : (fun k => ∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) =
      (1 / 3 : ℂ) • J b (Y b).val (frozenZ a b f.val) -
        (1 / 3 : ℂ) • (fun k => ∫ t : ℝ in a..b, (g t).val k) -
        (1 / 6 : ℂ) • CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val) := by
    funext k
    have hn := variable_normal_form hab hregY hregZ hm (fun t _ => hfm.add (stage_meanZero a t f.val f.val)) k
    have hfun : (fun t : ℝ => J t (dY t).val (frozenZ a t f.val) k +
        J t (Y t).val ((1 / 2 : ℂ) • B t f.val f.val) k) =
        (fun t : ℝ => (g t).val k + (1 / 2 : ℂ) * J t (B t f.val f.val) (Y t).val k) := by
      funext t
      rw [J_smul_right, J_comm t (Y t).val (B t f.val f.val)]
      rfl
    have hi1 : IntervalIntegrable (fun t : ℝ => (g t).val k) volume a b :=
      ((coefficientMap 0 k).continuous.comp hg).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun t : ℝ => J t (B t f.val f.val) (Y t).val k) volume a b := by
      have hc : Continuous (fun t : ℝ => J t (B t f.val f.val) (Y t).val k) := by
        simpa only [Function.comp_def, coefficientMap_apply, JZeroBundled_val,
          inclusionMap_val, BTwoBundled_val, id_eq] using
          (coefficientMap 1 k).continuous.comp hCIcont
      exact hc.intervalIntegrable a b
    rw [hfun, intervalIntegral.integral_add hi1 (hi2.const_mul _),
      intervalIntegral.integral_const_mul, J_B_integral, hleft, J_zero_left] at hn
    simp only [Pi.zero_apply, sub_zero] at hn
    change (∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) =
      (1 / 3 : ℂ) * J b (Y b).val (frozenZ a b f.val) k -
        (1 / 3 : ℂ) * (∫ t : ℝ in a..b, (g t).val k) -
        (1 / 6 : ℂ) * CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val) k
    linear_combination hn
  rw [heq]
  refine ⟨((hJ.smul _).sub (hI.smul _)).sub (hCI.smul _), ?_⟩
  have hs := hNorm_sub_le ((hJ.smul (1 / 3 : ℂ)).sub (hI.smul (1 / 3 : ℂ))) (hCI.smul (1 / 6 : ℂ))
  have hs' := hNorm_sub_le (hJ.smul (1 / 3 : ℂ)) (hI.smul (1 / 3 : ℂ))
  rw [hNorm_smul hCI] at hs
  rw [hNorm_smul hJ, hNorm_smul hI] at hs'
  have hn3 : ‖(1 / 3 : ℂ)‖ = (1 / 3 : ℝ) := by norm_num
  have hn6 : ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) := by norm_num
  rw [hn6] at hs
  rw [hn3] at hs'
  change hNorm 0 _ ≤ K * A * M / 3 + K * Ad * M * (b - a) / 3 + E / 6
  linarith




/-- The moving-defect trilinear bound needed for (26), on every subinterval
of the actual step. Every weak derivative and time-norm hypothesis is proved. -/
theorem numerical_cubic_defect_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (CIntegral ((n : ℝ) * τ) t (fun _ => f.val) (fun _ => f.val)
            (fun s => interpolationRemainder τ ((n : ℝ) * τ) s f.val)) ∧
          hNorm 0 (CIntegral ((n : ℝ) * τ) t (fun _ => f.val) (fun _ => f.val)
            (fun s => interpolationRemainder τ ((n : ℝ) * τ) s f.val)) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cp, hCp, hpair⟩ := dynamic_constant_pair_bound externalTrilinear (by norm_num : (0 : ℝ) < 1) le_rfl
  obtain ⟨Cy, hCy, htime⟩ := numerical_defect_time_bounds externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  refine ⟨2 * Cp * Cy * (M + 1) ^ 2, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let b : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let Y := defectL2Path externalStep τ hτ n f hfr hfm
  let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
  let NY := fun s => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y s)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  obtain ⟨hY, hdY, hWeak, hX, hN⟩ := htime τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ
  have hSub : Set.Icc a t ⊆ Set.Icc a b := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hYs := memLp_mono_interval hY hSub
  have hdYs := memLp_mono_interval hdY hSub
  have hYC : Continuous Y := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_defectBundled externalStep τ hτ n f hfr hfm)
  have hNY : MemLp NY ∞ (volume.restrict (Set.Icc a b)) := continuousOn_memLp_top_Icc
    (((inclusionMap (-pStar) 0 (by norm_num [pStar])).continuous.comp hYC).continuousOn)
  have hNX : timeLInfinity a t NY ≤ Cy * τ * q :=
    (timeLInfinity_mono_interval hNY hSub).trans hN
  have hXs : timeXNorm a t Y dY ≤ Cy * q := by
    exact (add_le_add (timeLInfinity_mono_interval hY hSub)
      (timeLInfinity_mono_interval hdY hSub)).trans hX
  have hWs : WeakTimeDerivative a t (fun s => (Y s).val) (fun s => (dY s).val) := by
    have hh := ((interpolationRemainder_regular externalStep τ hτ n f hfr hfm).restrict
      le_rfl ht.2).weakTimeDerivative ht.1
    simpa only [Y, dY, defectL2Path, defectNegativeDerivativePath,
      show ∀ s r h (f : Sobolev r), (inclusionMap s r h f).val = f.val from fun _ _ _ _ => rfl,
      defectBundled_val, defectDerivativeBundled_val] using hh
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
    have hw0 := hw.of_le hγ.le
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  obtain ⟨hCI, hCIb⟩ := hpair a t (mul_nonneg (Nat.cast_nonneg n) hτ.le) ht.1
    ((grid_interval_length n ht).trans hτ1) (inclusionMap 1 2 (by norm_num) f) Y dY hYs hdYs hWs
    (M + 1) (Cy * q) (Cy * τ * q) (by linarith) (mul_nonneg hCy.le hq)
    (mul_nonneg (mul_nonneg hCy.le hτ.le) hq) hfM hXs hNX
  have hbound : hNorm 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) ≤
      (2 * Cp * Cy * (M + 1) ^ 2) * τ * q := by
    calc
      _ ≤ Cp * (t - a) * (M + 1) ^ 2 * (Cy * q) + Cp * (Cy * τ * q) * (M + 1) ^ 2 := hCIb
      _ ≤ Cp * τ * (M + 1) ^ 2 * (Cy * q) + Cp * (Cy * τ * q) * (M + 1) ^ 2 := by
        gcongr
        exact grid_interval_length n ht
      _ = _ := by ring
  have hval (s : ℝ) : (Y s).val = interpolationRemainder τ a s f.val :=
    defectBundled_val externalStep τ hτ n s f hfr hfm
  change InSobolev 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) at hCI
  simpa only [hval, a, q] using And.intro hCI hbound




/-- The two integrated bilinear terms of the actual residual are small.
Their estimates follow from the proved normal forms and the moving-defect
trilinear bound, with no numerical higher norm in the constants. -/
theorem numerical_residual_bilinear_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          let IC := fun k => ∫ s : ℝ in (n : ℝ) * τ..t,
            B s (interpolationRemainder τ ((n : ℝ) * τ) s f.val) (frozenZ ((n : ℝ) * τ) s f.val) k
          let IQ := fun k => ∫ s : ℝ in (n : ℝ) * τ..t,
            B s (interpolationRemainder τ ((n : ℝ) * τ) s f.val)
              (interpolationRemainder τ ((n : ℝ) * τ) s f.val) k
          InSobolev 0 IC ∧ hNorm 0 IC ≤ C * τ * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          InSobolev 0 IQ ∧ hNorm 0 IQ ≤ C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cn, hCn, hstage⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cy, hCy, hL2⟩ := numerical_defect_l2_bound externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Ci, hCi, hInv⟩ := numerical_defect_negative_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hDeriv⟩ := numerical_defect_derivative_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Ct, hCt, hCubic⟩ := numerical_cubic_defect_bound externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one h1EmbeddingConstant_ge_one)
  let Mz : ℝ := M + 1 + 2 * Cn
  let My : ℝ := 2 * Cy
  have hMz : 0 ≤ Mz := by dsimp [Mz]; positivity
  have hMy : 0 ≤ My := by dsimp [My]; positivity
  let Cc : ℝ := K * Ci * Mz / 3 + K * Cd * Mz / 3 + Ct / 6
  let Cq : ℝ := K * Ci * My / 3 + (2 / 3 : ℝ) * K * Cd * My
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hCq : 0 ≤ Cq := by dsimp [Cq]; positivity
  refine ⟨1 + Cc + Cq, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  dsimp only
  let a : ℝ := (n : ℝ) * τ
  let Y := fun s => defectBundled externalStep τ hτ n s f hfr hfm
  let dY := fun s => defectDerivativeBundled externalStep τ hτ n s f hfr hfm
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq0 : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hq2 : q ≤ 2 := by dsimp [q]; linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  have hval (s : ℝ) : (Y s).val = interpolationRemainder τ a s f.val :=
    defectBundled_val externalStep τ hτ n s f hfr hfm
  have hdval (s : ℝ) : (dY s).val = interpolationRemainderDerivative τ a s f.val := rfl
  have hYC := continuous_defectBundled externalStep τ hτ n f hfr hfm
  have hdYC := continuous_defectDerivativeBundled externalStep τ hτ n f hfr hfm
  have hSub (s : ℝ) (hs : s ∈ Set.Icc a t) :
      s ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) := ⟨hs.1, hs.2.trans ht.2⟩
  have hd : ∀ s ∈ Set.Ioo a t, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (Y r).val k) ((dY s).val k) s := by
    intro s _ k
    simp_rw [hval, hdval]
    exact interpolationRemainder_hasDerivAt f hfm k
  have hm : ∀ s ∈ Set.Icc a t, MeanZero (Y s).val := by
    intro s _
    rw [hval]
    exact interpolationRemainder_meanZero τ a s hfm
  have hleft : (Y a).val = 0 := by
    rw [hval]
    unfold interpolationRemainder
    rw [localInterpolation_left, bilinearStage_self, add_zero, sub_self]
  have hY : ∀ s ∈ Set.Icc a t, hNorm 0 (Y s).val ≤ My := by
    intro s hs
    rw [hval]
    exact ((hL2 τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ s (hSub s hs)).2).trans
      (by simpa only [My, mul_comm] using mul_le_mul_of_nonneg_left hq2 hCy.le)
  have hIb : hNorm 0 (inverseDerivative (Y t).val) ≤ Ci * τ * q := by
    rw [hval]
    exact (hInv τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2.1
  have hId : ∀ s ∈ Set.Icc a t, hNorm 0 (inverseDerivative (dY s).val) ≤ Cd * q := by
    intro s hs
    rw [hdval]
    exact (hDeriv τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ s (hSub s hs)).2.1
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hw0 := hw.of_le hγ.le
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hZ : ∀ s ∈ Set.Icc a t, hNorm 0 (frozenZ a s f.val) ≤ Mz := by
    intro s hs
    have hF0 := (bilinearStage_h1_bound hf0 hf0 a s).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hFb := (hstage τ n s hτ hτ1 hnT (hSub s hs) f.val w hf0 hw hwm hwM hδ).2.2.2
    have hFb' : hNorm 0 (bilinearStage a s f.val f.val) ≤ 2 * Cn :=
      hFb.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq2 hCn.le)
    have hh := hNorm_add_le hf0 hF0
    change hNorm 0 (frozenZ a s f.val) ≤ _ at hh
    dsimp [Mz]
    linarith only [hh, hfM, hFb']
  obtain ⟨hCI, hCIn⟩ := hCubic τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  have hCI' : InSobolev 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) := by
    simpa only [hval] using hCI
  have hCIn' : hNorm 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) ≤ Ct * τ * q := by
    simpa only [hval] using hCIn
  obtain ⟨hCross, hCrossN⟩ := integral_B_cross_bound ht.1
    (mul_nonneg (mul_nonneg hCi.le hτ.le) hq0) (mul_nonneg hCd.le hq0) hMz
    f hfm Y dY hYC hdYC hd hm hleft hZ hIb hId hCI' hCIn'
  obtain ⟨hSelf, hSelfN⟩ := integral_B_self_bound ht.1
    (mul_nonneg (mul_nonneg hCi.le hτ.le) hq0) (mul_nonneg hCd.le hq0) hMy
    Y dY hYC hdYC hd hm hleft hY hIb hId
  have hCrossN' : hNorm 0 (fun k => ∫ s : ℝ in a..t, B s (Y s).val (frozenZ a s f.val) k) ≤
      Cc * τ * q := by
    calc
      _ ≤ K * (Ci * τ * q) * Mz / 3 + K * (Cd * q) * Mz * (t - a) / 3 + (Ct * τ * q) / 6 := hCrossN
      _ ≤ K * (Ci * τ * q) * Mz / 3 + K * (Cd * q) * Mz * τ / 3 + (Ct * τ * q) / 6 := by
        gcongr
        exact grid_interval_length n ht
      _ = _ := by dsimp [Cc]; ring
  have hSelfN' : hNorm 0 (fun k => ∫ s : ℝ in a..t, B s (Y s).val (Y s).val k) ≤ Cq * τ * q := by
    calc
      _ ≤ K * (Ci * τ * q) * My / 3 + (2 / 3 : ℝ) * K * (Cd * q) * My * (t - a) := hSelfN
      _ ≤ K * (Ci * τ * q) * My / 3 + (2 / 3 : ℝ) * K * (Cd * q) * My * τ := by
        gcongr
        exact grid_interval_length n ht
      _ = _ := by dsimp [Cq]; ring
  have hCC : Cc ≤ 1 + Cc + Cq := by linarith
  have hCQ : Cq ≤ 1 + Cc + Cq := by linarith
  have hc := hCrossN'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hτ.le) hq0)
  have hs := hSelfN'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCQ hτ.le) hq0)
  simpa only [hval, a, q] using And.intro hCross (And.intro hc (And.intro hSelf hs))




/-- Both estimates (26), for the residual of the specified full unfiltered
update. Constants precede every state, step count, and grid point. -/
theorem numerical_residual_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          InSobolev 0 (localResidual τ ((n : ℝ) * τ) t f.val) ∧
          hNorm 0 (localResidual τ ((n : ℝ) * τ) t f.val) ≤
            C * τ * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          InSobolev (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ∧
          hNorm (-pStar) (localResidualDerivative τ ((n : ℝ) * τ) t f.val) ≤
            C * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cb, hCb, hbil⟩ := numerical_residual_bilinear_bounds externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cw, hCw, hW⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hder⟩ := numerical_residual_derivative_bound externalStage externalProduct externalTrilinear
    hT hγ hγ1 hM
  let C : ℝ := 2 * Cb + Cw + Cd
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  let a : ℝ := (n : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let IC : Fourier := fun k => ∫ s : ℝ in a..t,
    B s (interpolationRemainder τ a s f.val) (frozenZ a s f.val) k
  let IQ : Fourier := fun k => ∫ s : ℝ in a..t,
    B s (interpolationRemainder τ a s f.val) (interpolationRemainder τ a s f.val) k
  let rfrac : ℝ := (t - a) / τ
  obtain ⟨hIC, hICb, hIQ, hIQb⟩ := hbil τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  obtain ⟨hW0, hWb⟩ := hW τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ
  obtain ⟨hD, hDb⟩ := hder τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  have hfrac := grid_interval_fraction hτ n ht
  have hq0 : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hScaled : hNorm 0 ((rfrac : ℂ) • endpointCorrection τ a f.val) ≤ Cw * τ * q := by
    rw [hNorm_smul hW0, Complex.norm_real, Real.norm_of_nonneg hfrac.1]
    exact (mul_le_mul_of_nonneg_right hfrac.2 (hNorm_nonneg _ _)).trans
      (by simpa only [one_mul] using hWb)
  have hR : InSobolev 0 (localResidual τ a t f.val) := by
    change InSobolev 0 (-IC - (1 / 2 : ℂ) • IQ - (rfrac : ℂ) • endpointCorrection τ a f.val)
    exact ((hIC.neg).sub (hIQ.smul (1 / 2 : ℂ))).sub (hW0.smul (rfrac : ℂ))
  refine ⟨hR, ?_, hD, hDb.trans ?_⟩
  · have hh := hNorm_sub_le ((hIC.neg).sub (hIQ.smul (1 / 2 : ℂ))) (hW0.smul (rfrac : ℂ))
    have hh' := hNorm_sub_le (hIC.neg) (hIQ.smul (1 / 2 : ℂ))
    rw [hNorm_neg, hNorm_smul hIQ] at hh'
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf] at hh'
    change hNorm 0 (-IC - (1 / 2 : ℂ) • IQ - (rfrac : ℂ) • endpointCorrection τ a f.val) ≤ C * τ * q
    have hpos := mul_nonneg hCb.le (mul_nonneg hτ.le hq0)
    have hposd := mul_nonneg hCd.le (mul_nonneg hτ.le hq0)
    calc
      _ ≤ hNorm 0 (-IC - (1 / 2 : ℂ) • IQ) +
          hNorm 0 ((rfrac : ℂ) • endpointCorrection τ a f.val) := hh
      _ ≤ (hNorm 0 IC + (1 / 2 : ℝ) * hNorm 0 IQ) +
          hNorm 0 ((rfrac : ℂ) • endpointCorrection τ a f.val) := add_le_add hh' le_rfl
      _ ≤ (Cb * τ * q + (1 / 2 : ℝ) * (Cb * τ * q)) + Cw * τ * q :=
        add_le_add (add_le_add hICb (mul_le_mul_of_nonneg_left hIQb (by norm_num))) hScaled
      _ ≤ C * τ * q := by dsimp [C]; nlinarith only [hpos, hposd]
  · have hCdC : Cd ≤ C := by dsimp [C]; linarith
    exact mul_le_mul_of_nonneg_right hCdC hq0




/-- Concatenate the first `k+1` full step functions at their grid endpoints.
Each function is defined for every real time; only its own step is used inside
the integration interval. -/
def concatenate {E : Type*} (τ : ℝ) (F : ℕ → ℝ → E) : ℕ → ℝ → E
  | 0 => F 0
  | k + 1 => fun t => if t ≤ ((k + 1 : ℕ) : ℝ) * τ then concatenate τ F k t else F (k + 1) t

theorem concatenate_tail {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    (k : ℕ) {t : ℝ} (ht : (k : ℝ) * τ ≤ t) : concatenate τ F k t = F k t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [concatenate]
    dsimp only
    split_ifs with h
    · have heq : t = ((k + 1 : ℕ) : ℝ) * τ := le_antisymm h ht
      subst t
      rw [ih (by push_cast; nlinarith), hglue k]
    · rfl

theorem concatenate_eq_earlier {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ)
    (F : ℕ → ℝ → E) {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ≤ ((j + 1 : ℕ) : ℝ) * τ) : concatenate τ F k t = concatenate τ F j t := by
  induction k with
  | zero =>
    have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
    subst j
    rfl
  | succ k ih =>
    by_cases hj : j = k + 1
    · subst j
      rfl
    · have hj' : j ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne hjk hj)
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj'
      have hbound := ht.trans (mul_le_mul_of_nonneg_right hcast hτ)
      rw [concatenate]
      dsimp only
      rw [if_pos hbound]
      exact ih hj'

theorem concatenate_on_step {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    concatenate τ F k t = F j t := by
  rw [concatenate_eq_earlier hτ F hjk ht.2]
  exact concatenate_tail hτ F hglue j ht.1

theorem continuous_concatenate {E : Type*} [TopologicalSpace E] {τ : ℝ} (hτ : 0 ≤ τ)
    (F : ℕ → ℝ → E) (hF : ∀ j, Continuous (F j))
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    (k : ℕ) : Continuous (concatenate τ F k) := by
  induction k with
  | zero => exact hF 0
  | succ k ih =>
    apply ih.if_le (hF (k + 1)) continuous_id continuous_const
    intro t ht
    change t = ((k + 1 : ℕ) : ℝ) * τ at ht
    rw [ht, concatenate_tail hτ F hglue k (by push_cast; nlinarith), hglue k]

theorem concatenate_eventuallyEq {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    (hglue : ∀ n, F n (((n + 1 : ℕ) : ℝ) * τ) = F (n + 1) (((n + 1 : ℕ) : ℝ) * τ))
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    concatenate τ F k =ᶠ[nhds t] F j := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
  exact concatenate_on_step hτ F hglue hjk ⟨hr.1.le, hr.2.le⟩




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




def localResidualBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) : Sobolev 0 :=
  -(∫ s : ℝ in (n : ℝ) * τ..t,
      BOneBundled s (defectBundled externalStep τ hτ n s f hfr hfm) (frozenZBundled ((n : ℝ) * τ) s f)) -
    (1 / 2 : ℂ) • (∫ s : ℝ in (n : ℝ) * τ..t,
      BOneBundled s (defectBundled externalStep τ hτ n s f hfr hfm)
        (defectBundled externalStep τ hτ n s f hfr hfm)) -
    ((((t - (n : ℝ) * τ) / τ) : ℝ) : ℂ) •
      inclusionMap 0 1 (by norm_num) (endpointCorrectionBundled externalStep τ hτ n f hfr hfm)

theorem localResidualBundled_val (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (t : ℝ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    (localResidualBundled externalStep τ hτ n t f hfr hfm).val =
      localResidual τ ((n : ℝ) * τ) t f.val := by
  obtain ⟨hC, hQ⟩ := continuous_residual_integrands externalStep τ hτ n f hfr hfm
  unfold localResidualBundled
  change -(∫ s : ℝ in (n : ℝ) * τ..t, BOneBundled s _ _).val -
    (1 / 2 : ℂ) • (∫ s : ℝ in (n : ℝ) * τ..t, BOneBundled s _ _).val - _ = _
  rw [sobolev_integral_val (hC.intervalIntegrable _ _), sobolev_integral_val (hQ.intervalIntegrable _ _)]
  simp only [BOneBundled_val, defectBundled_val, frozenZBundled_val]
  rfl

theorem continuous_localResidualBundled (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    Continuous (fun t : ℝ => localResidualBundled externalStep τ hτ n t f hfr hfm) := by
  obtain ⟨hC, hQ⟩ := continuous_residual_integrands externalStep τ hτ n f hfr hfm
  have hCI := (intervalIntegral.differentiable_integral_of_continuous (a := (n : ℝ) * τ) hC).continuous
  have hQI := (intervalIntegral.differentiable_integral_of_continuous (a := (n : ℝ) * τ) hQ).continuous
  unfold localResidualBundled
  fun_prop

theorem localResidualBundled_left (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val) :
    localResidualBundled externalStep τ hτ n ((n : ℝ) * τ) f hfr hfm = 0 := by
  apply Sobolev.ext
  rw [localResidualBundled_val, localResidual_left]
  rfl

def residualPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) : Sobolev 0 :=
  localResidualBundled externalStep τ hτ n t (twistedNumericalBundled τ f n)
    (twistedNumericalBundled_real τ hfr n) (twistedNumericalBundled_meanZero τ hfm n)

theorem residualPiece_val (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) :
    (residualPiece externalStep τ hτ f hfr hfm n t).val =
      localResidual τ ((n : ℝ) * τ) t (twistedNumericalBundled τ f n).val :=
  localResidualBundled_val externalStep τ hτ n t _ _ _

theorem residualPiece_left (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    residualPiece externalStep τ hτ f hfr hfm n ((n : ℝ) * τ) = 0 :=
  localResidualBundled_left externalStep τ hτ n _ _ _

theorem continuous_residualPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    Continuous (residualPiece externalStep τ hτ f hfr hfm n) :=
  continuous_localResidualBundled externalStep τ hτ n _ _ _

def cumulativeResidualPiece (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) (t : ℝ) : Sobolev 0 :=
  (∑ j ∈ Finset.range n, residualPiece externalStep τ hτ f hfr hfm j (((j + 1 : ℕ) : ℝ) * τ)) +
    residualPiece externalStep τ hτ f hfr hfm n t

theorem cumulativeResidualPiece_glue (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (n : ℕ) :
    cumulativeResidualPiece externalStep τ hτ f hfr hfm n (((n + 1 : ℕ) : ℝ) * τ) =
      cumulativeResidualPiece externalStep τ hτ f hfr hfm (n + 1) (((n + 1 : ℕ) : ℝ) * τ) := by
  simp only [cumulativeResidualPiece, residualPiece_left, add_zero, Finset.sum_range_succ]

def globalResidual (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) : ℝ → Sobolev 0 :=
  concatenate τ (cumulativeResidualPiece externalStep τ hτ f hfr hfm) k

theorem continuous_globalResidual (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) :
    Continuous (globalResidual externalStep τ hτ f hfr hfm k) := by
  apply continuous_concatenate hτ.le
  · intro j
    exact continuous_const.add (continuous_residualPiece externalStep τ hτ f hfr hfm j)
  · exact cumulativeResidualPiece_glue externalStep τ hτ f hfr hfm

theorem globalResidual_on_step (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    globalResidual externalStep τ hτ f hfr hfm k t =
      cumulativeResidualPiece externalStep τ hτ f hfr hfm j t :=
  concatenate_on_step hτ.le _ (cumulativeResidualPiece_glue externalStep τ hτ f hfr hfm) hjk ht

theorem globalResidual_step_increment (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    globalResidual externalStep τ hτ f hfr hfm k t -
      globalResidual externalStep τ hτ f hfr hfm k ((j : ℝ) * τ) =
        residualPiece externalStep τ hτ f hfr hfm j t := by
  rw [globalResidual_on_step externalStep τ hτ f hfr hfm hjk ht,
    globalResidual_on_step externalStep τ hτ f hfr hfm hjk
      (by constructor; rfl; push_cast; nlinarith)]
  simp only [cumulativeResidualPiece, residualPiece_left, add_zero, add_sub_cancel_left]

theorem globalResidual_zero (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) :
    globalResidual externalStep τ hτ f hfr hfm k 0 = 0 := by
  have ht : (0 : ℝ) ∈ Set.Icc ((0 : ℕ) : ℝ) (((0 + 1 : ℕ) : ℝ) * τ) := by simp [hτ.le]
  have hh := globalResidual_on_step externalStep τ hτ f hfr hfm (j := 0) (Nat.zero_le k)
    (t := 0) (by simpa using ht)
  rw [hh]
  simp only [cumulativeResidualPiece, Finset.range_zero, Finset.sum_empty, zero_add]
  simpa using residualPiece_left externalStep τ hτ f hfr hfm 0




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

theorem exists_open_grid_step {τ : ℝ} (_hτ : 0 < τ) (k : ℕ) {t : ℝ}
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




/-- The perturbation identity on any restarted interval. The finite grid is
handled by Mathlib's fundamental theorem off a countable exceptional set;
continuity at every grid point was proved by exact endpoint matching. -/
theorem global_perturbation_integral_identity (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    (globalInterpolation externalStep τ hτ f hfr hfm k b).val -
      (globalInterpolation externalStep τ hτ f hfr hfm k a).val =
        (1 / 2 : ℂ) • (fun m => ∫ t : ℝ in a..b,
          B t (globalInterpolation externalStep τ hτ f hfr hfm k t).val
            (globalInterpolation externalStep τ hτ f hfr hfm k t).val m) +
        ((globalResidual externalStep τ hτ f hfr hfm k b).val -
          (globalResidual externalStep τ hτ f hfr hfm k a).val) := by
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let R := globalResidual externalStep τ hτ f hfr hfm k
  have hVC := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  have hRC := continuous_globalResidual externalStep τ hτ f hfr hfm k
  have hBC := continuous_BOneBundled continuous_id hVC hVC
  funext m
  have hB : Continuous (fun t : ℝ => B t (V t).val (V t).val m) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using
      (coefficientMap 0 m).continuous.comp hBC
  have hC : Continuous (fun t : ℝ => (V t).val m - (R t).val m) := by
    simpa only [Function.comp_def, coefficientMap_apply, Pi.sub_apply, V, R] using!
      ((coefficientMap 1 m).continuous.comp hVC).sub ((coefficientMap 0 m).continuous.comp hRC)
  have hD : ∀ t ∈ Set.Ioo a b \ Set.range (fun j : ℕ => (j : ℝ) * τ),
      HasDerivAt (fun r : ℝ => (V r).val m - (R r).val m)
        ((1 / 2 : ℂ) * B t (V t).val (V t).val m) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1.1
    have htT : t < ((k + 1 : ℕ) : ℝ) * τ := lt_of_lt_of_le ht.1.2 hb
    have hnot : ∀ j : ℕ, t ≠ (j : ℝ) * τ := by
      intro j heq
      exact ht.2 ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k ht0 htT hnot
    exact global_perturbation_hasDerivAt_on_step externalStep τ hτ f hfr hfm hj hstep m
  have hi : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℂ) * B t (V t).val (V t).val m) volume a b :=
    (continuous_const.mul hB).intervalIntegrable a b
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ => (V t).val m - (R t).val m)
    (fun t : ℝ => (1 / 2 : ℂ) * B t (V t).val (V t).val m) hab
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)) hC.continuousOn hD hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  change (V b).val m - (V a).val m =
    (1 / 2 : ℂ) * (∫ t : ℝ in a..b, B t (V t).val (V t).val m) + ((R b).val m - (R a).val m)
  linear_combination -hFTC

theorem globalInterpolation_zero (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (k : ℕ) :
    (globalInterpolation externalStep τ hτ f hfr hfm k 0).val = f.val := by
  have h := globalInterpolation_grid externalStep τ hτ f hfr hfm (j := 0) (Nat.zero_le (k + 1))
  simpa only [Nat.cast_zero, zero_mul, twistedNumericalBundled_val, neg_zero, airy_zero, numerical_zero] using h

theorem globalInterpolation_integral_identity (externalStep : LiWuStepIdentity)
    (τ : ℝ) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 (((k + 1 : ℕ) : ℝ) * τ)) :
    (globalInterpolation externalStep τ hτ f hfr hfm k t).val = f.val +
      (1 / 2 : ℂ) • (fun m => ∫ s : ℝ in (0 : ℝ)..t,
        B s (globalInterpolation externalStep τ hτ f hfr hfm k s).val
          (globalInterpolation externalStep τ hτ f hfr hfm k s).val m) +
      (globalResidual externalStep τ hτ f hfr hfm k t).val := by
  have h := global_perturbation_integral_identity externalStep τ hτ f hfr hfm k le_rfl ht.1 ht.2
  rw [globalInterpolation_zero, globalResidual_zero] at h
  change (globalInterpolation externalStep τ hτ f hfr hfm k t).val - f.val = _ at h
  have hz : (0 : Sobolev 0).val = (0 : Fourier) := rfl
  rw [hz, sub_zero] at h
  linear_combination h




theorem concatenate_tail_strict {E : Type*} (τ : ℝ) (F : ℕ → ℝ → E) (j : ℕ) {t : ℝ}
    (ht : (j : ℝ) * τ < t) : concatenate τ F j t = F j t := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [concatenate]
    dsimp only
    exact if_neg (not_le.mpr ht)

/-- Derivative pieces need not match at the grid: on an open step the correct
piece is selected without any endpoint-gluing hypothesis. -/
theorem concatenate_on_open_step {E : Type*} {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ → E)
    {j k : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    concatenate τ F k t = F j t := by
  rw [concatenate_eq_earlier hτ F hjk ht.2.le]
  exact concatenate_tail_strict τ F j ht.1

theorem concatenate_map {E F : Type*} (τ : ℝ) (u : ℕ → ℝ → E) (G : ℝ → E → F)
    (k : ℕ) (t : ℝ) :
    concatenate τ (fun j r => G r (u j r)) k t = G t (concatenate τ u k t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [concatenate, concatenate]
    dsimp only
    split_ifs <;> first | exact ih | rfl

theorem intervalIntegrable_concatenate {E : Type*} [NormedAddCommGroup E]
    (τ : ℝ) (F : ℕ → ℝ → E) {a b : ℝ}
    (hF : ∀ j, IntervalIntegrable (F j) volume a b) (k : ℕ) :
    IntervalIntegrable (concatenate τ F k) volume a b := by
  induction k with
  | zero => exact hF 0
  | succ k ih =>
    constructor
    · change Integrable ((Set.Iic (((k + 1 : ℕ) : ℝ) * τ)).piecewise
        (concatenate τ F k) (F (k + 1))) (volume.restrict (Set.Ioc a b))
      exact Integrable.piecewise measurableSet_Iic ih.1.integrableOn (hF (k + 1)).1.integrableOn
    · change Integrable ((Set.Iic (((k + 1 : ℕ) : ℝ) * τ)).piecewise
        (concatenate τ F k) (F (k + 1))) (volume.restrict (Set.Ioc b a))
      exact Integrable.piecewise measurableSet_Iic ih.2.integrableOn (hF (k + 1)).2.integrableOn

theorem memLp_concatenate {E : Type*} [NormedAddCommGroup E]
    (τ : ℝ) (F : ℕ → ℝ → E) {μ : Measure ℝ} {p : ℝ≥0∞}
    (hF : ∀ j, MemLp (F j) p μ) (k : ℕ) : MemLp (concatenate τ F k) p μ := by
  induction k with
  | zero => exact hF 0
  | succ k ih =>
    change MemLp ((Set.Iic (((k + 1 : ℕ) : ℝ) * τ)).piecewise
      (concatenate τ F k) (F (k + 1))) p μ
    exact MemLp.piecewise measurableSet_Iic (ih.restrict _) ((hF (k + 1)).restrict _)




/-- The proved normal form across grid points, where the derivative may jump.
The functions themselves are continuous and every open step has an explicitly
proved derivative. No differentiability at grid points is required. -/
theorem variable_normal_form_grid (τ : ℝ) (hτ : 0 < τ) (k : ℕ)
    (f g : ℝ → Sobolev 1) (df dg : ℕ → ℝ → Sobolev 1)
    (hf : Continuous f) (hg : Continuous g) (hdf : ∀ j, Continuous (df j)) (hdg : ∀ j, Continuous (dg j))
    (hfd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun r : ℝ => (f r).val m) ((df j t).val m) t)
    (hgd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun r : ℝ => (g r).val m) ((dg j t).val m) t)
    (hfm : ∀ t, MeanZero (f t).val) (hgm : ∀ t, MeanZero (g t).val)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (m : ℤ) :
    (∫ t : ℝ in a..b, B t (f t).val (g t).val m) =
      (1 / 3 : ℂ) * (J b (f b).val (g b).val m - J a (f a).val (g a).val m) -
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b,
        (J t (concatenate τ df k t).val (g t).val m + J t (f t).val (concatenate τ dg k t).val m) := by
  have hcB : Continuous (fun t : ℝ => B t (f t).val (g t).val m) := by
    simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using
      (coefficientMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hf hg)
  have hcJ : Continuous (fun t : ℝ => J t (f t).val (g t).val m) := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hf)
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hg))
    simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
    exact h
  have hcD (j : ℕ) : Continuous (fun t : ℝ => J t (df j t).val (g t).val m) := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
        ((inclusionMap 0 1 (by norm_num)).continuous.comp (hdf j))
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hg))
    simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
    exact h
  have hcE (j : ℕ) : Continuous (fun t : ℝ => J t (f t).val (dg j t).val m) := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hf)
        ((inclusionMap 0 1 (by norm_num)).continuous.comp (hdg j)))
    simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
    exact h
  have hiD : IntervalIntegrable (fun t : ℝ => J t (concatenate τ df k t).val (g t).val m) volume a b := by
    have hi := intervalIntegrable_concatenate τ (fun j t => J t (df j t).val (g t).val m)
      (fun j => (hcD j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => J t (df j t).val (g t).val m) k =
        (fun t => J t (concatenate τ df k t).val (g t).val m) := by
      funext t
      exact concatenate_map τ df (fun r v => J r v.val (g r).val m) k t
    rwa [hmap] at hi
  have hiE : IntervalIntegrable (fun t : ℝ => J t (f t).val (concatenate τ dg k t).val m) volume a b := by
    have hi := intervalIntegrable_concatenate τ (fun j t => J t (f t).val (dg j t).val m)
      (fun j => (hcE j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => J t (f t).val (dg j t).val m) k =
        (fun t => J t (f t).val (concatenate τ dg k t).val m) := by
      funext t
      exact concatenate_map τ dg (fun r v => J r (f r).val v.val m) k t
    rwa [hmap] at hi
  have hiB : IntervalIntegrable (fun t : ℝ => B t (f t).val (g t).val m) volume a b :=
    hcB.intervalIntegrable a b
  have hi3B := hiB.const_mul (3 : ℂ)
  have hD : ∀ t ∈ Set.Ioo a b \ Set.range (fun j : ℕ => (j : ℝ) * τ),
      HasDerivAt (fun r : ℝ => J r (f r).val (g r).val m)
        (3 * B t (f t).val (g t).val m + J t (concatenate τ df k t).val (g t).val m +
          J t (f t).val (concatenate τ dg k t).val m) t := by
    intro t ht
    have hnot : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => ht.2 ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k
      (lt_of_le_of_lt ha ht.1.1) (lt_of_lt_of_le ht.1.2 hb) hnot
    have hfreg := regularFourierPath_of_bundled hf (hdf j) (hfd j hj)
    have hgreg := regularFourierPath_of_bundled hg (hdg j) (hgd j hj)
    rw [concatenate_on_open_step hτ.le df hj hstep, concatenate_on_open_step hτ.le dg hj hstep]
    exact variable_J_hasDerivAt hfreg hgreg (fun t _ => hfm t) (fun t _ => hgm t) hstep m
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ => J t (f t).val (g t).val m)
    (fun t : ℝ => 3 * B t (f t).val (g t).val m + J t (concatenate τ df k t).val (g t).val m +
      J t (f t).val (concatenate τ dg k t).val m) hab
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)) hcJ.continuousOn hD ((hi3B.add hiD).add hiE)
  rw [intervalIntegral.integral_add (hi3B.add hiD) hiE,
    intervalIntegral.integral_add hi3B hiD, intervalIntegral.integral_const_mul] at hFTC
  rw [intervalIntegral.integral_add hiD hiE]
  linear_combination (1 / 3 : ℂ) * hFTC




/-- Continuous paths with stepwise classical derivatives have the actual
distributional derivative given by the concatenated pieces, even when those
pieces jump at grid points. -/
theorem grid_weakTimeDerivative (τ : ℝ) (hτ : 0 < τ) (k : ℕ)
    (f : ℝ → Sobolev 1) (df : ℕ → ℝ → Sobolev 1)
    (hf : Continuous f) (hdf : ∀ j, Continuous (df j))
    (hfd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun r : ℝ => (f r).val m) ((df j t).val m) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    WeakTimeDerivative a b (fun t => (f t).val) (fun t => (concatenate τ df k t).val) := by
  intro m φ hφ _ hsupp
  have hφa : φ a = 0 := by
    by_contra ha'
    exact (lt_irrefl a) (hsupp (show a ∈ Function.support φ from ha')).1
  have hφb : φ b = 0 := by
    by_contra hb'
    exact (lt_irrefl b) (hsupp (show b ∈ Function.support φ from hb')).2
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hfc : Continuous (fun t : ℝ => (f t).val m) :=
    (coefficientMap 1 m).continuous.comp hf
  have hcprod : Continuous (fun t : ℝ => (φ t : ℂ) * (f t).val m) := hcφ.mul hfc
  have hi1 : IntervalIntegrable (fun t : ℝ => ((deriv φ t : ℝ) : ℂ) * (f t).val m) volume a b :=
    (hcDφ.mul hfc).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t : ℝ => (φ t : ℂ) * (concatenate τ df k t).val m) volume a b := by
    have hc (j : ℕ) : Continuous (fun t : ℝ => (φ t : ℂ) * (df j t).val m) :=
      hcφ.mul ((coefficientMap 1 m).continuous.comp (hdf j))
    have hi := intervalIntegrable_concatenate τ (fun j t => (φ t : ℂ) * (df j t).val m)
      (fun j => (hc j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => (φ t : ℂ) * (df j t).val m) k =
        (fun t => (φ t : ℂ) * (concatenate τ df k t).val m) := by
      funext t
      exact concatenate_map τ df (fun r v => (φ r : ℂ) * v.val m) k t
    rwa [hmap] at hi
  have hd : ∀ t ∈ Set.Ioo a b \ Set.range (fun j : ℕ => (j : ℝ) * τ),
      HasDerivAt (fun r : ℝ => (φ r : ℂ) * (f r).val m)
        (((deriv φ t : ℝ) : ℂ) * (f t).val m + (φ t : ℂ) * (concatenate τ df k t).val m) t := by
    intro t ht
    have hnot : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => ht.2 ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k
      (lt_of_le_of_lt ha ht.1.1) (lt_of_lt_of_le ht.1.2 hb) hnot
    rw [concatenate_on_open_step hτ.le df hj hstep]
    exact ((hφdiff t).hasDerivAt.ofReal_comp).mul (hfd j hj t hstep m)
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ => (φ t : ℂ) * (f t).val m)
    (fun t : ℝ => ((deriv φ t : ℝ) : ℂ) * (f t).val m + (φ t : ℂ) * (concatenate τ df k t).val m)
    hab (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)) hcprod.continuousOn hd (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  simp only [hφa, hφb, Complex.ofReal_zero, zero_mul, sub_self] at hFTC
  linear_combination hFTC




/-- A proof-only Fourier support condition. It does not occur in the method. -/
def SupportedIn (m : ℕ) (f : Fourier) : Prop :=
  ∀ k : ℤ, k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) → f k = 0

theorem supportedIn_cutoff (m : ℕ) (f : Fourier) : SupportedIn m (cutoff m f) := by
  intro k hk
  exact if_neg hk

theorem SupportedIn.airy {m : ℕ} {f : Fourier} (hf : SupportedIn m f) (t : ℝ) :
    SupportedIn m (airy t f) := by
  intro k hk
  simp only [KdV.airy, hf k hk, mul_zero]

theorem SupportedIn.removeMean {m : ℕ} {f : Fourier} (hf : SupportedIn m f) :
    SupportedIn m (removeMean f) := by
  intro k hk
  by_cases hk0 : k = 0
  · simp [KdV.removeMean, hk0]
  · simp only [KdV.removeMean, if_neg hk0, hf k hk]

theorem SupportedIn.inverseDerivative {m : ℕ} {f : Fourier} (hf : SupportedIn m f) :
    SupportedIn m (inverseDerivative f) := by
  intro k hk
  by_cases hk0 : k = 0
  · simp [KdV.inverseDerivative, hk0]
  · simp only [KdV.inverseDerivative, if_neg hk0, hf k hk, mul_zero]

theorem SupportedIn.product {m n : ℕ} {f g : Fourier}
    (hf : SupportedIn m f) (hg : SupportedIn n g) : SupportedIn (m + n) (product f g) := by
  intro k hk
  have heq (a : ℤ) : f a * g (k - a) = 0 := by
    by_cases ha : a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · have hga : k - a ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
        intro hga
        apply hk
        simp only [Finset.mem_Icc, Nat.cast_add] at ha hga ⊢
        constructor <;> omega
      rw [hg (k - a) hga, mul_zero]
    · rw [hf a ha, zero_mul]
  simp only [KdV.product, heq, tsum_zero]

theorem SupportedIn.CIntegrand {m n l : ℕ} {f g h : Fourier}
    (hf : SupportedIn m f) (hg : SupportedIn n g) (hh : SupportedIn l h) (t : ℝ) :
    SupportedIn (m + n + l) (CIntegrand t f g h) := by
  have hinner := ((hf.airy t).product (hg.airy t)).removeMean
  have houter := hinner.product (hh.inverseDerivative.airy t)
  exact houter.removeMean.airy (-t)

theorem CIntegral_cutoff_supported (m : ℕ) (a b : ℝ) (f g h : ℝ → Fourier) :
    SupportedIn (3 * m) (CIntegral a b (fun t => cutoff m (f t))
      (fun t => cutoff m (g t)) (fun t => cutoff m (h t))) := by
  intro k hk
  have hm : m + m + m = 3 * m := by omega
  change (∫ t : ℝ in a..b, CIntegrand t (cutoff m (f t)) (cutoff m (g t)) (cutoff m (h t)) k) = 0
  have heq : (fun t : ℝ => CIntegrand t (cutoff m (f t)) (cutoff m (g t)) (cutoff m (h t)) k) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext t
    exact (SupportedIn.CIntegrand (supportedIn_cutoff m (f t)) (supportedIn_cutoff m (g t))
      (supportedIn_cutoff m (h t)) t) k (by simpa only [hm] using hk)
  rw [heq, intervalIntegral.integral_zero]

theorem SupportedIn.highCutoff_eq_zero {m : ℕ} {f : Fourier} (hf : SupportedIn m f) :
    highCutoff m f = 0 := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp [highCutoff, cutoff, hk]
  · simp [highCutoff, cutoff, hk, hf k hk]

theorem high_output_all_low_zero (m : ℕ) (a b : ℝ) (f g h : ℝ → Fourier) :
    highCutoff (3 * m) (CIntegral a b (fun t => cutoff m (f t))
      (fun t => cutoff m (g t)) (fun t => cutoff m (h t))) = 0 :=
  (CIntegral_cutoff_supported m a b f g h).highCutoff_eq_zero

theorem cutoff_smul (m : ℕ) (z : ℂ) (f : Fourier) : cutoff m (z • f) = z • cutoff m f := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

def cutoffLinear (s : ℝ) (m : ℕ) : Sobolev s →ₗ[ℂ] Sobolev s where
  toFun f := ⟨cutoff m f.val, cutoff_inSobolev f.property m⟩
  map_add' f g := by apply Sobolev.ext; exact cutoff_add m f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact cutoff_smul m z f.val

def cutoffMap (s : ℝ) (m : ℕ) : Sobolev s →L[ℂ] Sobolev s :=
  (cutoffLinear s m).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (cutoff m f.val) ≤ hNorm s f.val
    exact cutoff_hNorm_le f.property m)

def highCutoffMap (s : ℝ) (m : ℕ) : Sobolev s →L[ℂ] Sobolev s :=
  ContinuousLinearMap.id ℂ (Sobolev s) - cutoffMap s m

theorem cutoffMap_val (s : ℝ) (m : ℕ) (f : Sobolev s) : (cutoffMap s m f).val = cutoff m f.val := rfl

theorem highCutoffMap_val (s : ℝ) (m : ℕ) (f : Sobolev s) :
    (highCutoffMap s m f).val = highCutoff m f.val := rfl

theorem highCutoff_hNorm_le {s : ℝ} {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    hNorm s (highCutoff m f) ≤ hNorm s f := by
  simpa only [sub_self, weight, zero_div, Real.rpow_zero, one_mul] using high_cutoff_bound (s := s) le_rfl hf m |>.2

theorem cutoffMap_norm_le (s : ℝ) (m : ℕ) (f : Sobolev s) : ‖cutoffMap s m f‖ ≤ ‖f‖ := by
  rw [sobolev_norm, sobolev_norm, cutoffMap_val]
  exact cutoff_hNorm_le f.property m

theorem highCutoffMap_norm_le (s : ℝ) (m : ℕ) (f : Sobolev s) : ‖highCutoffMap s m f‖ ≤ ‖f‖ := by
  rw [sobolev_norm, sobolev_norm, highCutoffMap_val]
  exact highCutoff_hNorm_le f.property m

theorem WeakTimeDerivative.cutoff {a b : ℝ} {f df : ℝ → Fourier}
    (hf : WeakTimeDerivative a b f df) (m : ℕ) :
    WeakTimeDerivative a b (fun t => cutoff m (f t)) (fun t => cutoff m (df t)) := by
  intro k φ hφ hsupp hs
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simpa only [KdV.cutoff, if_pos hk] using hf k φ hφ hsupp hs
  · simp only [KdV.cutoff, if_neg hk, mul_zero, intervalIntegral.integral_zero, neg_zero]

theorem WeakTimeDerivative.highCutoff {a b : ℝ} {f df : ℝ → Fourier}
    (hf : WeakTimeDerivative a b f df) (m : ℕ) :
    WeakTimeDerivative a b (fun t => highCutoff m (f t)) (fun t => highCutoff m (df t)) := by
  intro k φ hφ hsupp hs
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp only [KdV.highCutoff, Pi.sub_apply, KdV.cutoff, if_pos hk, sub_self, mul_zero,
      intervalIntegral.integral_zero, neg_zero]
  · simpa only [KdV.highCutoff, Pi.sub_apply, KdV.cutoff, if_neg hk, sub_zero] using hf k φ hφ hsupp hs




def COneBundled (t : ℝ) (f g h : Sobolev 1) : Sobolev 1 :=
  airyMap 1 (-t) (removeMeanMap 1 (productMap
    (removeMeanMap 1 (productMap (airyMap 1 t f) (airyMap 1 t g)))
    (airyMap 1 t (inverseDerivativeSameMap 1 h))))

theorem COneBundled_val (t : ℝ) (f g h : Sobolev 1) :
    (COneBundled t f g h).val = CIntegrand t f.val g.val h.val := rfl

theorem continuous_COneBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g h : X → Sobolev 1} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun x => COneBundled (t x) (f x) (g x) (h x)) := by
  unfold COneBundled
  have hF := continuous_airy_apply 1 ht hf
  have hG := continuous_airy_apply 1 ht hg
  have hH := continuous_airy_apply 1 ht ((inverseDerivativeSameMap 1).continuous.comp hh)
  apply continuous_airy_apply 1 ht.neg
  fun_prop

theorem continuous_CIntegrand_paths {f g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (k : ℤ) :
    Continuous (fun t : ℝ => CIntegrand t (f t).val (g t).val (h t).val k) := by
  have hc := (coefficientMap 1 k).continuous.comp (continuous_COneBundled continuous_id hf hg hh)
  simpa only [Function.comp_def, coefficientMap_apply, COneBundled_val, id_eq] using hc

def CIntegralPathBundled (a b : ℝ) (f g h : ℝ → Sobolev 1) : Sobolev 1 :=
  ∫ t : ℝ in a..b, COneBundled t (f t) (g t) (h t)

theorem CIntegralPathBundled_val (a b : ℝ) {f g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    (CIntegralPathBundled a b f g h).val =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) := by
  exact sobolev_integral_val ((continuous_COneBundled continuous_id hf hg hh).intervalIntegrable a b)

theorem CIntegral_comm (a b : ℝ) (f g h : ℝ → Fourier) : CIntegral a b f g h = CIntegral a b g f h := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_comm]

theorem CIntegral_paths_add_left (a b : ℝ) {f l g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hl : Continuous l) (hg : Continuous g) (hh : Continuous h) :
    CIntegral a b (fun t => ((f + l) t).val) (fun t => (g t).val) (fun t => (h t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (l t).val) (fun t => (g t).val) (fun t => (h t).val) := by
  funext k
  have heq (t : ℝ) : CIntegrand t ((f + l) t).val (g t).val (h t).val =
      CIntegrand t (f t).val (g t).val (h t).val + CIntegrand t (l t).val (g t).val (h t).val :=
    CIntegrand_add_left ((f t).property.of_le (by norm_num)) ((l t).property.of_le (by norm_num))
      ((g t).property.of_le (by norm_num)) ((h t).property.of_le (by norm_num)) t
  simp_rw [CIntegral_eq_integrand, heq, Pi.add_apply]
  exact intervalIntegral.integral_add ((continuous_CIntegrand_paths hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_paths hl hg hh k).intervalIntegrable a b)

theorem CIntegral_paths_sub_left (a b : ℝ) {f l g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hl : Continuous l) (hg : Continuous g) (hh : Continuous h) :
    CIntegral a b (fun t => ((f - l) t).val) (fun t => (g t).val) (fun t => (h t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (l t).val) (fun t => (g t).val) (fun t => (h t).val) := by
  have heq := CIntegral_paths_add_left a b (hf.sub hl) hl hg hh
  simp only [sub_add_cancel] at heq
  exact eq_sub_iff_add_eq.mpr heq.symm

theorem CIntegral_paths_sub_middle (a b : ℝ) {f g l h : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hl : Continuous l) (hh : Continuous h) :
    CIntegral a b (fun t => (f t).val) (fun t => ((g - l) t).val) (fun t => (h t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (f t).val) (fun t => (l t).val) (fun t => (h t).val) := by
  rw [CIntegral_comm a b _ (fun t => ((g - l) t).val), CIntegral_paths_sub_left a b hg hl hf hh,
    CIntegral_comm a b (fun t => (g t).val), CIntegral_comm a b (fun t => (l t).val)]

theorem CIntegral_paths_add_right (a b : ℝ) {f g h l : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hl : Continuous l) :
    CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => ((h + l) t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (l t).val) := by
  funext k
  have heq (t : ℝ) : CIntegrand t (f t).val (g t).val ((h + l) t).val =
      CIntegrand t (f t).val (g t).val (h t).val + CIntegrand t (f t).val (g t).val (l t).val :=
    CIntegrand_add_right ((f t).property.of_le (by norm_num)) ((g t).property.of_le (by norm_num))
      ((h t).property.of_le (by norm_num)) ((l t).property.of_le (by norm_num)) t
  simp_rw [CIntegral_eq_integrand, heq, Pi.add_apply]
  exact intervalIntegral.integral_add ((continuous_CIntegrand_paths hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_paths hf hg hl k).intervalIntegrable a b)

theorem CIntegral_paths_sub_right (a b : ℝ) {f g h l : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hl : Continuous l) :
    CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => ((h - l) t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (l t).val) := by
  have heq := CIntegral_paths_add_right a b hf hg (hh.sub hl) hl
  simp only [sub_add_cancel] at heq
  exact eq_sub_iff_add_eq.mpr heq.symm

theorem CIntegral_paths_difference (a b : ℝ) {f g h F G H : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (F t).val) (fun t => (G t).val) (fun t => (H t).val) =
      CIntegral a b (fun t => ((f - F) t).val) (fun t => (g t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (F t).val) (fun t => ((g - G) t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (F t).val) (fun t => (G t).val) (fun t => ((h - H) t).val) := by
  rw [CIntegral_paths_sub_left a b hf hF hg hh, CIntegral_paths_sub_middle a b hF hg hG hh,
    CIntegral_paths_sub_right a b hF hG hh hH]
  abel




theorem timeLInfinity_ae_bound {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖f t‖ ≤ timeLInfinity a b f := by
  have hfinite : eLpNormEssSup f (volume.restrict (Set.Icc a b)) ≠ ∞ := by
    simpa only [eLpNorm_exponent_top] using hf.2.ne
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume.restrict (Set.Icc a b))] with t ht
  have hn := ENNReal.toReal_mono hfinite ht
  simpa only [timeLInfinity, eLpNorm_exponent_top, toReal_enorm] using hn

theorem timeLInfinity_le_of_ae_bound {s A a b : ℝ} (hA : 0 ≤ A)
    (f : ℝ → Sobolev s) (hf : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖f t‖ ≤ A) :
    timeLInfinity a b f ≤ A := by
  have hs := sourceLInfinity_le_of_bound hA a b f hf
  change sourceNormalization * timeLInfinity a b f ≤ sourceNormalization * A at hs
  exact (mul_le_mul_iff_right₀ sourceNormalization_pos).mp hs

theorem timeLInfinity_map_bound {s r K a b : ℝ} (hK : 0 ≤ K)
    (L : Sobolev s →L[ℂ] Sobolev r) (hL : ∀ v, ‖L v‖ ≤ K * ‖v‖)
    {f : ℝ → Sobolev s} (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) :
    timeLInfinity a b (fun t => L (f t)) ≤ K * timeLInfinity a b f := by
  apply timeLInfinity_le_of_ae_bound (mul_nonneg hK (timeLInfinity_nonneg _ _ _))
  filter_upwards [timeLInfinity_ae_bound hf] with t ht
  exact (hL (f t)).trans (mul_le_mul_of_nonneg_left ht hK)

theorem timeLInfinity_cutoff_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeLInfinity a b (fun t => cutoffMap s m (f t)) ≤ timeLInfinity a b f := by
  simpa only [one_mul] using timeLInfinity_map_bound (by norm_num : (0 : ℝ) ≤ 1)
    (cutoffMap s m) (fun v => by simpa only [one_mul] using cutoffMap_norm_le s m v) hf

theorem timeLInfinity_highCutoff_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeLInfinity a b (fun t => highCutoffMap s m (f t)) ≤ timeLInfinity a b f := by
  simpa only [one_mul] using timeLInfinity_map_bound (by norm_num : (0 : ℝ) ≤ 1)
    (highCutoffMap s m) (fun v => by simpa only [one_mul] using highCutoffMap_norm_le s m v) hf

theorem timeXNorm_cutoff_le {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeXNorm a b (fun t => cutoffMap 0 m (f t)) (fun t => cutoffMap (-pStar) m (df t)) ≤
      timeXNorm a b f df :=
  add_le_add (timeLInfinity_cutoff_le hf m) (timeLInfinity_cutoff_le hdf m)

theorem timeXNorm_highCutoff_le {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeXNorm a b (fun t => highCutoffMap 0 m (f t)) (fun t => highCutoffMap (-pStar) m (df t)) ≤
      timeXNorm a b f df :=
  add_le_add (timeLInfinity_highCutoff_le hf m) (timeLInfinity_highCutoff_le hdf m)

/-- Negative-norm smallness of a high input, in the actual time norm. -/
theorem time_highCutoff_negative_bound {a b : ℝ} {f : ℝ → Sobolev 0}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) :
    timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (highCutoffMap 0 m (f t))) ≤
      weight (-pStar) (m : ℤ) * timeLInfinity a b f := by
  let L := (inclusionMap (-pStar) 0 (by norm_num [pStar])).comp (highCutoffMap 0 m)
  have hL (v : Sobolev 0) : ‖L v‖ ≤ weight (-pStar) (m : ℤ) * ‖v‖ := by
    rw [sobolev_norm, sobolev_norm]
    change hNorm (-pStar) (highCutoff m v.val) ≤ weight (-pStar) (m : ℤ) * hNorm 0 v.val
    simpa only [sub_zero] using (high_cutoff_bound (by norm_num [pStar] : -pStar ≤ 0) v.property m).2
  exact timeLInfinity_map_bound (weight_pos (-pStar) _).le L hL hf




/-- The three terms of the proof's trilinear telescoping: slots before `i`
are low, slot `i` is high, and subsequent slots are unchanged. -/
def inputProjection (s : ℝ) (m : ℕ) (i j : Fin 3) : Sobolev s →L[ℂ] Sobolev s :=
  if j < i then cutoffMap s m else if j = i then highCutoffMap s m else ContinuousLinearMap.id ℂ _

theorem inputProjection_norm_le (s : ℝ) (m : ℕ) (i j : Fin 3) (f : Sobolev s) :
    ‖inputProjection s m i j f‖ ≤ ‖f‖ := by
  unfold inputProjection
  split_ifs
  · exact cutoffMap_norm_le s m f
  · exact highCutoffMap_norm_le s m f
  · exact le_rfl

theorem inputProjection_inclusion_val (s r : ℝ) (hsr : s ≤ r) (m : ℕ) (i j : Fin 3) (f : Sobolev r) :
    (inputProjection s m i j (inclusionMap s r hsr f)).val = (inputProjection r m i j f).val := by
  unfold inputProjection
  split_ifs <;> simp only [cutoffMap_val, highCutoffMap_val, inclusionMap_val, ContinuousLinearMap.id_apply]

theorem inputProjection_memLp {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i j : Fin 3) :
    MemLp (fun t => inputProjection s m i j (f t)) ∞ (volume.restrict (Set.Icc a b)) :=
  hf.continuousLinearMap_comp (inputProjection s m i j)

theorem inputProjection_time_norm_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i j : Fin 3) :
    timeLInfinity a b (fun t => inputProjection s m i j (f t)) ≤ timeLInfinity a b f := by
  simpa only [one_mul] using timeLInfinity_map_bound (by norm_num : (0 : ℝ) ≤ 1)
    (inputProjection s m i j) (fun v => by simpa only [one_mul] using inputProjection_norm_le s m i j v) hf

theorem inputProjection_timeX_le {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i j : Fin 3) :
    timeXNorm a b (fun t => inputProjection 0 m i j (f t)) (fun t => inputProjection (-pStar) m i j (df t)) ≤
      timeXNorm a b f df :=
  add_le_add (inputProjection_time_norm_le hf m i j) (inputProjection_time_norm_le hdf m i j)

theorem inputProjection_weak {a b : ℝ} {f : ℝ → Sobolev 0} {df : ℝ → Sobolev (-pStar)}
    (hf : WeakTimeDerivative a b (fun t => (f t).val) (fun t => (df t).val)) (m : ℕ) (i j : Fin 3) :
    WeakTimeDerivative a b (fun t => (inputProjection 0 m i j (f t)).val)
      (fun t => (inputProjection (-pStar) m i j (df t)).val) := by
  unfold inputProjection
  split_ifs
  · simpa only [cutoffMap_val] using hf.cutoff m
  · simpa only [highCutoffMap_val] using hf.highCutoff m
  · exact hf

theorem inputProjection_high_negative {a b : ℝ} {f : ℝ → Sobolev 0}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (m : ℕ) (i : Fin 3) :
    timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (inputProjection 0 m i i (f t))) ≤
      weight (-pStar) (m : ℤ) * timeLInfinity a b f := by
  simp only [inputProjection, lt_irrefl, if_false, if_true]
  exact time_highCutoff_negative_bound hf m

theorem fin_three_selected_mul_others (x : Fin 3 → ℝ) (i : Fin 3) :
    x i * (∏ j : Fin 3, if j = i then 1 else x j) = ∏ j : Fin 3, x j := by
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

/-- The cited dynamic estimate applied to one of the three internally
specified high-input terms. The high-frequency gain is proved from projection
norms and every time-derivative hypothesis is preserved. -/
theorem one_high_cubic_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 1 →
      ∀ f : Fin 3 → ℝ → Sobolev 0, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
        ∀ m : ℕ, ∀ i : Fin 3,
          InSobolev 0 (CIntegral a b (fun t => (inputProjection 0 m i 0 (f 0 t)).val)
            (fun t => (inputProjection 0 m i 1 (f 1 t)).val) (fun t => (inputProjection 0 m i 2 (f 2 t)).val)) ∧
          hNorm 0 (CIntegral a b (fun t => (inputProjection 0 m i 0 (f 0 t)).val)
            (fun t => (inputProjection 0 m i 1 (f 1 t)).val) (fun t => (inputProjection 0 m i 2 (f 2 t)).val)) ≤
            C * (b - a) * (∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
              C * weight (-pStar) (m : ℤ) * (∏ j : Fin 3, timeLInfinity a b (f j)) := by
  obtain ⟨C, hC, hb⟩ := normalized_dynamic_trilinear externalTrilinear (by norm_num : (0 : ℝ) < 1) le_rfl
  refine ⟨C, hC, ?_⟩
  intro a b ha hab hlen f df hf hdf hd m i
  let F : Fin 3 → ℝ → Sobolev 0 := fun j t => inputProjection 0 m i j (f j t)
  let D : Fin 3 → ℝ → Sobolev (-pStar) := fun j t => inputProjection (-pStar) m i j (df j t)
  obtain ⟨hmem, hn⟩ := hb a b ha hab hlen F D
    (fun j => inputProjection_memLp (hf j) m i j)
    (fun j => inputProjection_memLp (hdf j) m i j)
    (fun j => inputProjection_weak (hd j) m i j)
  have hPX : (∏ j : Fin 3, timeXNorm a b (F j) (D j)) ≤ ∏ j : Fin 3, timeXNorm a b (f j) (df j) := by
    apply Finset.prod_le_prod
    · intro j _
      exact timeXNorm_nonneg _ _ _ _
    · intro j _
      exact inputProjection_timeX_le (hf j) (hdf j) m i j
  have hPO : (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (F j)) ≤
      ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j) := by
    apply Finset.prod_le_prod
    · intro j _
      split_ifs
      · norm_num
      · exact timeLInfinity_nonneg _ _ _
    · intro j _
      split_ifs
      · exact le_rfl
      · exact inputProjection_time_norm_le (hf j) m i j
  have hNi := inputProjection_high_negative (hf i) m i
  have hPO0 : 0 ≤ ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (F j) := by
    apply Finset.prod_nonneg
    intro j _
    split_ifs
    · norm_num
    · exact timeLInfinity_nonneg _ _ _
  refine ⟨hmem, (hn i).trans ?_⟩
  calc
    _ ≤ C * (b - a) * (∏ j : Fin 3, timeXNorm a b (f j) (df j)) +
        C * (weight (-pStar) (m : ℤ) * timeLInfinity a b (f i)) *
          (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) :=
      add_le_add (mul_le_mul_of_nonneg_left hPX (mul_nonneg hC.le (sub_nonneg.mpr hab)))
        (mul_le_mul (mul_le_mul_of_nonneg_left hNi hC.le) hPO hPO0
          (mul_nonneg hC.le (mul_nonneg (weight_pos _ _).le (timeLInfinity_nonneg _ _ _))))
    _ = _ := by
      rw [← mul_assoc C (weight (-pStar) (m : ℤ)) (timeLInfinity a b (f i)),
        mul_assoc (C * weight (-pStar) (m : ℤ)),
        fin_three_selected_mul_others (fun j => timeLInfinity a b (f j)) i]




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




theorem J_add_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t (f + g) h = J t f h + J t g h := by
  have heq := J_sub_left (hf.add hg) hg hh t
  rw [add_sub_cancel_right] at heq
  exact (eq_sub_iff_add_eq.mp heq).symm

theorem J_add_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t f (g + h) = J t f g + J t f h := by
  rw [J_comm t f (g + h), J_add_left hg hh hf, J_comm t g f, J_comm t h f]

theorem B_error_polarization {v V : Fourier} (hv : InSobolev 0 v) (hV : InSobolev 0 V) (t : ℝ) :
    B t (v - V) (v - (1 / 2 : ℂ) • (v - V)) = (1 / 2 : ℂ) • (B t v v - B t V V) := by
  have hg : v - (1 / 2 : ℂ) • (v - V) = (1 / 2 : ℂ) • (v + V) := by module
  rw [hg, B_smul_right, B_sub_left hv hV (hv.add hV), B_add_right hv hv hV,
    B_add_right hV hv hV, B_comm t V v]
  module

/-- The differentiated algebra in (31), before time integration. It is proved
for actual `H¹` states and an arbitrary `L²` residual derivative. -/
theorem error_normal_form_integrand (t : ℝ) (v V : Sobolev 1) (r : Sobolev 0) :
    let e := v.val - V.val
    let g := v.val - (1 / 2 : ℂ) • e
    let de := B t e g - r.val
    let dg := (1 / 2 : ℂ) • B t v.val v.val - (1 / 2 : ℂ) • B t e g + (1 / 2 : ℂ) • r.val
    J t de g + J t e dg = CIntegrand t e g V.val +
      (1 / 2 : ℂ) • CIntegrand t v.val v.val e - J t r.val V.val := by
  dsimp only
  let e := v.val - V.val
  let g := v.val - (1 / 2 : ℂ) • e
  have he1 : InSobolev 1 e := v.property.sub V.property
  have hg1 : InSobolev 1 g := v.property.sub (he1.smul (1 / 2 : ℂ))
  have he := he1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hg := hg1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hv := v.property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hB := (B_h1_bound he1 hg1 t).1
  have hBv := (B_h1_bound v.property v.property t).1
  change J t (B t e g - r.val) g + J t e
      ((1 / 2 : ℂ) • B t v.val v.val - (1 / 2 : ℂ) • B t e g + (1 / 2 : ℂ) • r.val) = _
  rw [J_sub_left hB r.property hg, J_add_right he
      ((hBv.smul (1 / 2 : ℂ)).sub (hB.smul (1 / 2 : ℂ))) (r.property.smul (1 / 2 : ℂ)),
    J_sub_right he (hBv.smul (1 / 2 : ℂ)) (hB.smul (1 / 2 : ℂ)),
    J_smul_right, J_smul_right, J_smul_right,
    J_comm t e (B t v.val v.val), J_comm t e (B t e g), J_comm t e r.val]
  rw [J_B, J_B, J_B]
  have hV : V.val = g - (1 / 2 : ℂ) • e := by dsimp [g, e]; module
  have hc : CIntegrand t e g V.val = CIntegrand t e g g - (1 / 2 : ℂ) • CIntegrand t e g e := by
    have hh := CIntegrand_add_right he hg (V.property.of_le (by norm_num : (0 : ℝ) ≤ 1))
      (he.smul (1 / 2 : ℂ)) t
    have hsum : V.val + (1 / 2 : ℂ) • e = g := by dsimp [g, e]; module
    rw [hsum, CIntegrand_smul_right] at hh
    exact eq_sub_iff_add_eq.mpr hh.symm
  have hj : J t r.val V.val = J t r.val g - (1 / 2 : ℂ) • J t r.val e := by
    rw [hV, J_sub_right r.property hg (he.smul (1 / 2 : ℂ)), J_smul_right]
  rw [hc, hj]
  change (CIntegrand t e g g - J t r.val g) +
    (((1 / 2 : ℂ) • CIntegrand t v.val v.val e - (1 / 2 : ℂ) • CIntegrand t e g e) +
      (1 / 2 : ℂ) • J t r.val e) = _
  module




theorem sobolev_val_sub {s : ℝ} (f g : Sobolev s) : (f - g).val = f.val - g.val := rfl

theorem sobolev_val_smul {s : ℝ} (z : ℂ) (f : Sobolev s) : (z • f).val = z • f.val := rfl

/-- Equation (31) on a restarted interval. The exact and perturbed equations
are explicit internal hypotheses; their algebra is proved here, and the
normal-form integration handles derivative jumps at the numerical grid. -/
theorem error_normal_form_grid (τ : ℝ) (hτ : 0 < τ) (k : ℕ)
    (v V : ℝ → Sobolev 1) (dv dV : ℕ → ℝ → Sobolev 1) (r : ℕ → ℝ → Sobolev 0)
    (hv : Continuous v) (hV : Continuous V)
    (hdv : ∀ j, Continuous (dv j)) (hdV : ∀ j, Continuous (dV j)) (hr : ∀ j, Continuous (r j))
    (hvd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun s : ℝ => (v s).val m) ((dv j t).val m) t)
    (hVd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun s : ℝ => (V s).val m) ((dV j t).val m) t)
    (hvEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dv j t).val = (1 / 2 : ℂ) • B t (v t).val (v t).val)
    (hVEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dV j t).val = (1 / 2 : ℂ) • B t (V t).val (V t).val + (r j t).val)
    (hvm : ∀ t, MeanZero (v t).val) (hVm : ∀ t, MeanZero (V t).val)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (m : ℤ) :
    let e : ℝ → Sobolev 1 := fun t => v t - V t
    let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
    (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
      (1 / 3 : ℂ) * (J b (e b).val (g b).val m - J a (e a).val (g a).val m) -
      (1 / 3 : ℂ) * CIntegral a b (fun t => (e t).val) (fun t => (g t).val) (fun t => (V t).val) m -
      (1 / 6 : ℂ) * CIntegral a b (fun t => (v t).val) (fun t => (v t).val) (fun t => (e t).val) m +
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b, J t (concatenate τ r k t).val (V t).val m := by
  dsimp only
  let e : ℝ → Sobolev 1 := fun t => v t - V t
  let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
  let de : ℕ → ℝ → Sobolev 1 := fun j t => dv j t - dV j t
  let dg : ℕ → ℝ → Sobolev 1 := fun j t => dv j t - (1 / 2 : ℂ) • de j t
  have heC : Continuous e := hv.sub hV
  have hgC : Continuous g := hv.sub ((continuous_const (y := (1 / 2 : ℂ))).smul heC)
  have hdeC (j : ℕ) : Continuous (de j) := (hdv j).sub (hdV j)
  have hdgC (j : ℕ) : Continuous (dg j) := (hdv j).sub ((continuous_const (y := (1 / 2 : ℂ))).smul (hdeC j))
  have hed : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (e s).val l) ((de j t).val l) t := by
    intro j hj t ht l
    exact (hvd j hj t ht l).sub (hVd j hj t ht l)
  have hgd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (g s).val l) ((dg j t).val l) t := by
    intro j hj t ht l
    exact (hvd j hj t ht l).sub ((hed j hj t ht l).const_mul (1 / 2 : ℂ))
  have hem (t : ℝ) : MeanZero (e t).val := (hvm t).sub (hVm t)
  have hgm (t : ℝ) : MeanZero (g t).val := (hvm t).sub ((hem t).smul (1 / 2 : ℂ))
  have hNF := variable_normal_form_grid τ hτ k e g de dg heC hgC hdeC hdgC hed hgd hem hgm ha hab hb m
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioo a b) (hnot : t ∉ Set.range (fun j : ℕ => (j : ℝ) * τ)) :
      J t (concatenate τ de k t).val (g t).val m + J t (e t).val (concatenate τ dg k t).val m =
        CIntegrand t (e t).val (g t).val (V t).val m +
        (1 / 2 : ℂ) * CIntegrand t (v t).val (v t).val (e t).val m -
        J t (concatenate τ r k t).val (V t).val m := by
    have hnot' : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => hnot ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k
      (lt_of_le_of_lt ha ht.1) (lt_of_lt_of_le ht.2 hb) hnot'
    have hstepc : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) := ⟨hstep.1.le, hstep.2.le⟩
    have hdeEq : (de j t).val = B t (e t).val (g t).val - (r j t).val := by
      change (dv j t).val - (dV j t).val = _
      rw [hvEq j hj t hstepc, hVEq j hj t hstepc]
      change (1 / 2 : ℂ) • B t (v t).val (v t).val -
        ((1 / 2 : ℂ) • B t (V t).val (V t).val + (r j t).val) =
        B t ((v t).val - (V t).val) ((v t).val - (1 / 2 : ℂ) • ((v t).val - (V t).val)) - (r j t).val
      rw [B_error_polarization ((v t).property.of_le (by norm_num)) ((V t).property.of_le (by norm_num))]
      module
    have hdgEq : (dg j t).val = (1 / 2 : ℂ) • B t (v t).val (v t).val -
        (1 / 2 : ℂ) • B t (e t).val (g t).val + (1 / 2 : ℂ) • (r j t).val := by
      change (dv j t).val - (1 / 2 : ℂ) • (de j t).val = _
      rw [hvEq j hj t hstepc, hdeEq]
      module
    rw [concatenate_on_open_step hτ.le de hj hstep, concatenate_on_open_step hτ.le dg hj hstep,
      concatenate_on_open_step hτ.le r hj hstep, hdeEq, hdgEq]
    simpa only [e, g, sobolev_val_sub, sobolev_val_smul,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (error_normal_form_integrand t (v t) (V t) (r j t)) m
  have hIntEq : (∫ t : ℝ in a..b,
      (J t (concatenate τ de k t).val (g t).val m + J t (e t).val (concatenate τ dg k t).val m)) =
      ∫ t : ℝ in a..b, (CIntegrand t (e t).val (g t).val (V t).val m +
        (1 / 2 : ℂ) * CIntegrand t (v t).val (v t).val (e t).val m -
        J t (concatenate τ r k t).val (V t).val m) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_range (fun j : ℕ => (j : ℝ) * τ)).ae_notMem volume, volume.ae_ne b]
      with t hnot htb
    intro ht
    rw [Set.uIoc_of_le hab] at ht
    exact hpoint t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩ hnot
  have hiC : IntervalIntegrable (fun t : ℝ => CIntegrand t (e t).val (g t).val (V t).val m) volume a b :=
    (continuous_CIntegrand_paths heC hgC hV m).intervalIntegrable a b
  have hiC2 : IntervalIntegrable (fun t : ℝ => CIntegrand t (v t).val (v t).val (e t).val m) volume a b :=
    (continuous_CIntegrand_paths hv hv heC m).intervalIntegrable a b
  have hiR : IntervalIntegrable (fun t : ℝ => J t (concatenate τ r k t).val (V t).val m) volume a b := by
    have hc (j : ℕ) : Continuous (fun t : ℝ => J t (r j t).val (V t).val m) := by
      have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id (hr j)
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hV))
      simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
      exact h
    have hi := intervalIntegrable_concatenate τ (fun j t => J t (r j t).val (V t).val m)
      (fun j => (hc j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => J t (r j t).val (V t).val m) k =
        (fun t => J t (concatenate τ r k t).val (V t).val m) := by
      funext t
      exact concatenate_map τ r (fun s w => J s w.val (V s).val m) k t
    rwa [hmap] at hi
  rw [hIntEq, intervalIntegral.integral_sub (hiC.add (hiC2.const_mul _)) hiR,
    intervalIntegral.integral_add hiC (hiC2.const_mul _), intervalIntegral.integral_const_mul] at hNF
  change (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
    (1 / 3 : ℂ) * (J b (e b).val (g b).val m - J a (e a).val (g a).val m) -
    (1 / 3 : ℂ) * (∫ t : ℝ in a..b, CIntegrand t (e t).val (g t).val (V t).val m) -
    (1 / 6 : ℂ) * (∫ t : ℝ in a..b, CIntegrand t (v t).val (v t).val (e t).val m) +
    (1 / 3 : ℂ) * (∫ t : ℝ in a..b, J t (concatenate τ r k t).val (V t).val m)
  linear_combination hNF




/-- A continuous Sobolev path extended constantly past both endpoints. Only
this auxiliary extension is used outside the physical time interval. -/
def sobolevExtension {s T : ℝ} (hT : 0 ≤ T) (u : ℝ → Fourier)
    (hu : SobolevContinuousOn s T u) : ℝ → Sobolev s :=
  fun t => sobolevRestriction s T u hu.1 (Set.projIcc 0 T hT t)

theorem continuous_sobolevExtension {s T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) : Continuous (sobolevExtension hT u hu) :=
  hu.continuous_restriction.comp continuous_projIcc

theorem sobolevExtension_val_on {s T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (sobolevExtension hT u hu t).val = u t := by
  unfold sobolevExtension
  rw [Set.projIcc_of_mem hT ht]
  rfl

def extendedTwistedPath {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : ℝ → Sobolev 2 :=
  sobolevExtension hT (fun t => airy (-t) (u t)) (hu.1.airy_path (fun t => -t) continuous_neg)

theorem continuous_extendedTwistedPath {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : Continuous (extendedTwistedPath hT hu) :=
  continuous_sobolevExtension hT _

theorem extendedTwistedPath_val_on {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (extendedTwistedPath hT hu t).val = airy (-t) (u t) :=
  sobolevExtension_val_on hT _ ht

theorem extendedTwistedPath_meanZero {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : MeanZero (extendedTwistedPath hT hu t).val := by
  let p := Set.projIcc 0 T hT t
  change airy (-p.val) (u p.val) 0 = 0
  rw [airy_mean]
  exact (hu.2.2 p.val p.property).2

theorem extendedTwistedPath_zero {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : (extendedTwistedPath hT hu 0).val = u0 := by
  rw [extendedTwistedPath_val_on hT hu ⟨le_rfl, hT⟩, neg_zero, airy_zero]
  exact hu.2.1.1

theorem extendedTwistedPath_equation {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (k : ℤ) :
    (extendedTwistedPath hT hu t).val k = u0 k + (1 / 2 : ℂ) *
      ∫ s : ℝ in (0 : ℝ)..t, B s (extendedTwistedPath hT hu s).val (extendedTwistedPath hT hu s).val k := by
  have hv := twist_Duhamel hu.2.1
  have hInt : (∫ s : ℝ in (0 : ℝ)..t, B s (extendedTwistedPath hT hu s).val (extendedTwistedPath hT hu s).val k) =
      (∫ s : ℝ in (0 : ℝ)..t, B s (airy (-s) (u s)) (airy (-s) (u s)) k) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    dsimp only
    rw [extendedTwistedPath_val_on hT hu ⟨hs.1, hs.2.trans ht.2⟩]
  rw [hInt, extendedTwistedPath_val_on hT hu ht]
  exact hv.2 t ht k

def exactTwistedDerivative {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : Sobolev 1 :=
  (1 / 2 : ℂ) • BTwoBundled t (extendedTwistedPath hT hu t) (extendedTwistedPath hT hu t)

theorem continuous_exactTwistedDerivative {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) : Continuous (exactTwistedDerivative hT hu) := by
  exact (continuous_const (y := (1 / 2 : ℂ))).smul (continuous_BTwoBundled continuous_id
    (continuous_extendedTwistedPath hT hu) (continuous_extendedTwistedPath hT hu))

/-- Actual coefficient differentiation of the source-prescribed Duhamel
solution. No exact-trajectory derivative premise is introduced. -/
theorem extendedTwistedPath_hasDerivAt {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => (extendedTwistedPath hT hu r).val k)
      ((exactTwistedDerivative hT hu t).val k) t := by
  have hV := continuous_extendedTwistedPath hT hu
  have hc : Continuous (fun r : ℝ => B r (extendedTwistedPath hT hu r).val (extendedTwistedPath hT hu r).val k) := by
    have h := (coefficientMap 1 k).continuous.comp (continuous_BTwoBundled continuous_id hV hV)
    simpa only [Function.comp_def, coefficientMap_apply, BTwoBundled_val, id_eq] using h
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hDF := (hasDerivAt_const t (u0 k)).add (hi.const_mul (1 / 2 : ℂ))
  have hE : (fun r : ℝ => (extendedTwistedPath hT hu r).val k) =ᶠ[nhds t]
      (fun r : ℝ => u0 k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..r,
        B s (extendedTwistedPath hT hu s).val (extendedTwistedPath hT hu s).val k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    exact extendedTwistedPath_equation hT hu hr k
  simpa only [zero_add] using! hDF.congr_of_eventuallyEq hE

theorem exactTwistedDerivative_equation {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) :
    (exactTwistedDerivative hT hu t).val =
      (1 / 2 : ℂ) • B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val := rfl




def numericalDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) : Sobolev 1 :=
  localDerivativeBundled externalStep τ hτ j t (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)

theorem numericalDerivativeFamily_val (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) :
    (numericalDerivativeFamily externalStep τ hτ f hfr hfm j t).val =
      localInterpolationDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val := rfl

theorem continuous_numericalDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) :
    Continuous (numericalDerivativeFamily externalStep τ hτ f hfr hfm j) :=
  continuous_localDerivativeBundled externalStep τ hτ j _ _ _

def numericalResidualDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) : Sobolev 0 :=
  let fj := twistedNumericalBundled τ f j
  let hjr := twistedNumericalBundled_real τ hfr j
  let hjm := twistedNumericalBundled_meanZero τ hfm j;
  -BOneBundled t (defectBundled externalStep τ hτ j t fj hjr hjm) (frozenZBundled ((j : ℝ) * τ) t fj) -
    (1 / 2 : ℂ) • BOneBundled t (defectBundled externalStep τ hτ j t fj hjr hjm)
      (defectBundled externalStep τ hτ j t fj hjr hjm) -
    ((τ⁻¹ : ℝ) : ℂ) • inclusionMap 0 1 (by norm_num)
      (endpointCorrectionBundled externalStep τ hτ j fj hjr hjm)

theorem numericalResidualDerivativeFamily_val (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) (t : ℝ) :
    (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t).val =
      localResidualDerivative τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val := by
  unfold numericalResidualDerivativeFamily
  dsimp only
  change -B t (defectBundled externalStep τ hτ j t _ _ _).val (frozenZBundled _ t _).val -
    (1 / 2 : ℂ) • B t (defectBundled externalStep τ hτ j t _ _ _).val
      (defectBundled externalStep τ hτ j t _ _ _).val - _ = _
  rw [defectBundled_val, frozenZBundled_val]
  rfl

theorem continuous_numericalResidualDerivativeFamily (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) (j : ℕ) :
    Continuous (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j) := by
  have hC := (continuous_residual_integrands externalStep τ hτ j (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)).1
  have hQ := (continuous_residual_integrands externalStep τ hτ j (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)).2
  unfold numericalResidualDerivativeFamily
  dsimp only
  fun_prop

/-- The derivative callback used by the global error normal form is verified
for the actual concatenated numerical interpolation. -/
theorem numerical_derivative_family_correct (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (globalInterpolation externalStep τ hτ f hfr hfm k r).val m)
      ((numericalDerivativeFamily externalStep τ hτ f hfr hfm j t).val m) t := by
  rw [numericalDerivativeFamily_val]
  exact globalInterpolation_hasDerivAt_on_step externalStep τ hτ f hfr hfm hjk ht m

/-- The perturbed equation callback is also proved, including at both step
endpoints. It is not an assumed numerical differential equation. -/
theorem numerical_derivative_family_equation (externalStep : LiWuStepIdentity) (τ : ℝ) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val) {j k : ℕ} (hjk : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    (numericalDerivativeFamily externalStep τ hτ f hfr hfm j t).val =
      (1 / 2 : ℂ) • B t (globalInterpolation externalStep τ hτ f hfr hfm k t).val
        (globalInterpolation externalStep τ hτ f hfr hfm k t).val +
      (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t).val := by
  have hv : (globalInterpolation externalStep τ hτ f hfr hfm k t).val =
      localInterpolation τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val :=
    (congrArg Sobolev.val (globalInterpolation_on_step externalStep τ hτ f hfr hfm hjk ht)).trans
      (interpolationPiece_val externalStep τ hτ f hfr hfm j t)
  rw [numericalDerivativeFamily_val, numericalResidualDerivativeFamily_val, hv]
  have hY : InSobolev 0 (interpolationRemainder τ ((j : ℝ) * τ) t (twistedNumericalBundled τ f j).val) := by
    rw [← defectBundled_val externalStep τ hτ j t (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)]
    exact (defectBundled externalStep τ hτ j t (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)).property.of_le (by norm_num)
  exact localInterpolation_perturbation_identity ((twistedNumericalBundled τ f j).property.of_le (by norm_num)) hY




/-- Equation (31) for the actual exact Duhamel solution and the actual
numerical interpolation. All derivative and equation callbacks of the internal
grid normal form are discharged, rather than imposed as new source premises. -/
theorem actual_error_normal_form (externalStep : LiWuStepIdentity)
    {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (m : ℤ) :
    let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
    let V := globalInterpolation externalStep τ hτ f hfr hfm k
    let e : ℝ → Sobolev 1 := fun t => v t - V t
    let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
    (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
      (1 / 3 : ℂ) * (J b (e b).val (g b).val m - J a (e a).val (g a).val m) -
      (1 / 3 : ℂ) * CIntegral a b (fun t => (e t).val) (fun t => (g t).val) (fun t => (V t).val) m -
      (1 / 6 : ℂ) * CIntegral a b (fun t => (v t).val) (fun t => (v t).val) (fun t => (e t).val) m +
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b,
        J t (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t).val (V t).val m := by
  dsimp only
  let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let dv : ℕ → ℝ → Sobolev 1 := fun _ t => exactTwistedDerivative hT hu t
  let dV := numericalDerivativeFamily externalStep τ hτ f hfr hfm
  let r := numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm
  have hvC : Continuous v := (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
  have hVC : Continuous V := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  have hdvC (j : ℕ) : Continuous (dv j) := continuous_exactTwistedDerivative hT hu
  have hdVC (j : ℕ) : Continuous (dV j) := continuous_numericalDerivativeFamily externalStep τ hτ f hfr hfm j
  have hrC (j : ℕ) : Continuous (r j) := continuous_numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j
  have hvd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (v s).val l) ((dv j t).val l) t := by
    intro j hj t ht l
    have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg j) hτ.le) ht.1
    have hbound : ((j + 1 : ℕ) : ℝ) * τ ≤ ((k + 1 : ℕ) : ℝ) * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hj) hτ.le
    have htT : t < T := lt_of_lt_of_le ht.2 (hbound.trans hTotal)
    exact extendedTwistedPath_hasDerivAt hT hu ⟨ht0, htT⟩ l
  have hVd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (V s).val l) ((dV j t).val l) t := by
    intro j hj t ht l
    exact numerical_derivative_family_correct externalStep τ hτ f hfr hfm hj ht l
  have hvEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dv j t).val = (1 / 2 : ℂ) • B t (v t).val (v t).val := by
    intro j _ t _
    exact exactTwistedDerivative_equation hT hu t
  have hVEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dV j t).val = (1 / 2 : ℂ) • B t (V t).val (V t).val + (r j t).val := by
    intro j hj t ht
    exact numerical_derivative_family_equation externalStep τ hτ f hfr hfm hj ht
  have hvm (t : ℝ) : MeanZero (v t).val := extendedTwistedPath_meanZero hT hu t
  have hVm (t : ℝ) : MeanZero (V t).val := globalInterpolation_meanZero externalStep τ hτ f hfr hfm k t
  exact error_normal_form_grid τ hτ k v V dv dV r hvC hVC hdvC hdVC hrC hvd hVd hvEq hVEq hvm hVm ha hab hb m




theorem extendedTwistedPath_integral_difference {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (extendedTwistedPath hT hu b).val - (extendedTwistedPath hT hu a).val =
      (1 / 2 : ℂ) • (fun k => ∫ t : ℝ in a..b,
        B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) := by
  have hC := continuous_extendedTwistedPath hT hu
  funext k
  have hc : Continuous (fun t : ℝ => B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) := by
    have hh := (coefficientMap 1 k).continuous.comp (continuous_BTwoBundled continuous_id hC hC)
    simpa only [Function.comp_def, coefficientMap_apply, BTwoBundled_val, id_eq] using hh
  have hder : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun r : ℝ => (extendedTwistedPath hT hu r).val k)
      ((1 / 2 : ℂ) * B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) t := by
    intro t ht
    exact extendedTwistedPath_hasDerivAt hT hu ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩ k
  have hi : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℂ) *
      B t (extendedTwistedPath hT hu t).val (extendedTwistedPath hT hu t).val k) volume a b :=
    (continuous_const.mul hc).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (((coefficientMap 2 k).continuous.comp hC).continuousOn) hder hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  exact hFTC.symm

/-- The exact restarted error identity (29), with the residual increment
already proved to belong to the specified numerical interpolation. -/
theorem actual_error_integral_identity (externalStep : LiWuStepIdentity)
    {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
    let V := globalInterpolation externalStep τ hτ f hfr hfm k
    let R := globalResidual externalStep τ hτ f hfr hfm k
    let e : ℝ → Sobolev 1 := fun t => v t - V t
    let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
    (e b).val = (e a).val + (fun m => ∫ t : ℝ in a..b, B t (e t).val (g t).val m) -
      ((R b).val - (R a).val) := by
  dsimp only
  let v : ℝ → Sobolev 1 := fun t => inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu t)
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let R := globalResidual externalStep τ hτ f hfr hfm k
  let e : ℝ → Sobolev 1 := fun t => v t - V t
  let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
  have hdiffv := extendedTwistedPath_integral_difference hT hu ha hab (hb.trans hTotal)
  have hdiffV := global_perturbation_integral_identity externalStep τ hτ f hfr hfm k ha hab hb
  have hvC : Continuous v := (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
  have hVC := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  funext m
  have hi1 : IntervalIntegrable (fun t : ℝ => B t (v t).val (v t).val m) volume a b := by
    have hc := (coefficientMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hvC hvC)
    have hcc : Continuous (fun t : ℝ => B t (v t).val (v t).val m) := by
      simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using hc
    exact hcc.intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t : ℝ => B t (V t).val (V t).val m) volume a b := by
    have hc := (coefficientMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hVC hVC)
    have hcc : Continuous (fun t : ℝ => B t (V t).val (V t).val m) := by
      simpa only [Function.comp_def, coefficientMap_apply, BOneBundled_val, id_eq] using hc
    exact hcc.intervalIntegrable a b
  have hFI : (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
      (1 / 2 : ℂ) * ((∫ t : ℝ in a..b, B t (v t).val (v t).val m) -
        (∫ t : ℝ in a..b, B t (V t).val (V t).val m)) := by
    have heq : (fun t : ℝ => B t (e t).val (g t).val m) =
        (fun t : ℝ => (1 / 2 : ℂ) * (B t (v t).val (v t).val m - B t (V t).val (V t).val m)) := by
      funext t
      exact congrFun (B_error_polarization ((v t).property.of_le (by norm_num)) ((V t).property.of_le (by norm_num)) t) m
    rw [heq, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2]
  have hv := congrFun hdiffv m
  have hV := congrFun hdiffV m
  change (v b).val m - (v a).val m = (1 / 2 : ℂ) * (∫ t : ℝ in a..b, B t (v t).val (v t).val m) at hv
  change (V b).val m - (V a).val m = (1 / 2 : ℂ) * (∫ t : ℝ in a..b, B t (V t).val (V t).val m) +
    ((R b).val m - (R a).val m) at hV
  change (v b).val m - (V b).val m = (v a).val m - (V a).val m +
    (∫ t : ℝ in a..b, B t (e t).val (g t).val m) - ((R b).val m - (R a).val m)
  linear_combination hv - hV - hFI

theorem actual_error_grid_norm (externalStep : LiWuStepIdentity)
    {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) {j : ℕ} (hj : j ≤ k + 1) :
    hNorm 0 ((inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu ((j : ℝ) * τ)) -
      globalInterpolation externalStep τ hτ f hfr hfm k ((j : ℝ) * τ)).val) =
      hNorm 0 (u ((j : ℝ) * τ) - numerical τ f.val j) := by
  have ht : (j : ℝ) * τ ∈ Set.Icc 0 T := ⟨mul_nonneg (Nat.cast_nonneg j) hτ.le,
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hj : (j : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) hτ.le).trans hTotal⟩
  rw [sobolev_val_sub, inclusionMap_val, extendedTwistedPath_val_on hT hu ht,
    globalInterpolation_grid externalStep τ hτ f hfr hfm hj, twistedNumericalBundled_val,
    ← airy_sub, airy_hNorm]




theorem exists_closed_grid_step {τ : ℝ} (_hτ : 0 < τ) (k : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    ∃ j : ℕ, j ≤ k ∧ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simpa using And.intro ht0 htT⟩
  | succ k ih =>
    by_cases hlast : t ≤ ((k + 1 : ℕ) : ℝ) * τ
    · obtain ⟨j, hj, hjt⟩ := ih hlast
      exact ⟨j, hj.trans (Nat.le_succ _), hjt⟩
    · exact ⟨k + 1, le_rfl, (le_of_not_ge hlast), htT⟩

/-- The number of residual increments is controlled by interval length plus
one step. This is a proved finite-sum estimate for the actual concatenation. -/
theorem globalResidual_interval_bound (externalStep : LiWuStepIdentity)
    {τ : ℝ} (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {j0 k : ℕ} (hj0 : j0 ≤ k) {b A q : ℝ} (hab : (j0 : ℝ) * τ ≤ b)
    (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hLocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b →
        ‖residualPiece externalStep τ hτ f hfr hfm j t‖ ≤ A * τ * q) :
    ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
      ‖globalResidual externalStep τ hτ f hfr hfm k t -
        globalResidual externalStep τ hτ f hfr hfm k ((j0 : ℝ) * τ)‖ ≤
          A * (b - (j0 : ℝ) * τ + τ) * q := by
  intro t ht
  by_cases hta : t = (j0 : ℝ) * τ
  · subst t
    rw [sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg hA (by linarith)) hq
  · have hat : (j0 : ℝ) * τ < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
    obtain ⟨n, hn, hnt⟩ := exists_closed_grid_step hτ k
      ((mul_nonneg (Nat.cast_nonneg j0) hτ.le).trans ht.1) (ht.2.trans hb)
    have hjn : j0 ≤ n := by
      by_contra h
      have hh : n + 1 ≤ j0 := by omega
      have hc : ((n + 1 : ℕ) : ℝ) * τ ≤ (j0 : ℝ) * τ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hτ.le
      linarith [hnt.2]
    let F : ℕ → Sobolev 0 := fun j => residualPiece externalStep τ hτ f hfr hfm j (((j + 1 : ℕ) : ℝ) * τ)
    have hstart : (j0 : ℝ) * τ ∈ Set.Icc ((j0 : ℝ) * τ) (((j0 + 1 : ℕ) : ℝ) * τ) := by
      constructor
      · rfl
      · push_cast
        nlinarith
    rw [globalResidual_on_step externalStep τ hτ f hfr hfm hn hnt,
      globalResidual_on_step externalStep τ hτ f hfr hfm hj0 hstart]
    change ‖((∑ j ∈ Finset.range n, F j) + residualPiece externalStep τ hτ f hfr hfm n t) -
      ((∑ j ∈ Finset.range j0, F j) + residualPiece externalStep τ hτ f hfr hfm j0 ((j0 : ℝ) * τ))‖ ≤ _
    rw [residualPiece_left, add_zero]
    have heq : ((∑ j ∈ Finset.range n, F j) + residualPiece externalStep τ hτ f hfr hfm n t) -
        (∑ j ∈ Finset.range j0, F j) =
        ((∑ j ∈ Finset.range n, F j) - ∑ j ∈ Finset.range j0, F j) + residualPiece externalStep τ hτ f hfr hfm n t := by
      abel
    rw [heq, ← Finset.sum_Ico_eq_sub F hjn]
    have hFn : ‖residualPiece externalStep τ hτ f hfr hfm n t‖ ≤ A * τ * q := hLocal n hjn hn t hnt ht.2
    have hsum : ‖∑ j ∈ Finset.Ico j0 n, F j‖ ≤ (n - j0 : ℕ) * (A * τ * q) := by
      calc
        _ ≤ ∑ j ∈ Finset.Ico j0 n, ‖F j‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.Ico j0 n, A * τ * q := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Finset.mem_Ico.mp hj
          have hjk : j ≤ k := hj'.2.le.trans hn
          have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ b :=
            ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj'.2) hτ.le).trans hnt.1).trans ht.2
          exact hLocal j hj'.1 hjk _
            ⟨by push_cast; nlinarith, le_rfl⟩ hEnd
        _ = _ := by simp
    have hlength : ((n - j0 + 1 : ℕ) : ℝ) * τ ≤ b - (j0 : ℝ) * τ + τ := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn]
      linarith [hnt.1, ht.2]
    calc
      _ ≤ ‖∑ j ∈ Finset.Ico j0 n, F j‖ + ‖residualPiece externalStep τ hτ f hfr hfm n t‖ := norm_add_le _ _
      _ ≤ (n - j0 : ℕ) * (A * τ * q) + A * τ * q := add_le_add hsum hFn
      _ = A * (((n - j0 + 1 : ℕ) : ℝ) * τ) * q := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength hA) hq

theorem hNorm_sub_symm (s : ℝ) (f g : Fourier) : hNorm s (f - g) = hNorm s (g - f) := by
  rw [← neg_sub g f, hNorm_neg]

/-- Restarted residual estimate (27), derived from (26) and the actual grid
error bound. The exact Sobolev bound is explicit and will be supplied by the
previously proved initial-ball flow theorem. -/
theorem restarted_residual_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 ((inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT.le hu t) -
              globalInterpolation externalStep τ hτ f hfr hfm k t).val) ≤ E) →
          ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            ‖globalResidual externalStep τ hτ f hfr hfm k t -
              globalResidual externalStep τ hτ f hfr hfm k ((j0 : ℝ) * τ)‖ ≤
              C * (b - (j0 : ℝ) * τ + τ) * (τ ^ γ + E) := by
  obtain ⟨C, hC, hb⟩ := numerical_residual_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  apply globalResidual_interval_bound externalStep hτ f hfr hfm hj0 hab hbT hC.le
    (add_nonneg (Real.rpow_nonneg hτ.le γ) hE)
  intro j hj0j hjk s hs hsb
  have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal
  have hgridI : (j : ℝ) * τ ∈ Set.Icc ((j0 : ℝ) * τ) b :=
    ⟨mul_le_mul_of_nonneg_right (by exact_mod_cast hj0j) hτ.le, hs.1.trans hsb⟩
  have hgridT : (j : ℝ) * τ ∈ Set.Icc 0 T :=
    ⟨mul_nonneg (Nat.cast_nonneg j) hτ.le, hgridI.2.trans (hbT.trans hTotal)⟩
  let fj := twistedNumericalBundled τ f j
  let w := (extendedTwistedPath hT.le hu ((j : ℝ) * τ)).val
  have hw : InSobolev γ w := (extendedTwistedPath hT.le hu ((j : ℝ) * τ)).property.of_le (by linarith : γ ≤ 2)
  have hwm : MeanZero w := extendedTwistedPath_meanZero hT.le hu _
  have hwM : hNorm γ w ≤ M := by
    dsimp [w]
    rw [extendedTwistedPath_val_on hT.le hu hgridT, airy_hNorm]
    exact huM _ hgridT
  have hδ : hNorm 0 (fj.val - w) ≤ E := by
    have hh := he _ hgridI
    rw [sobolev_val_sub, inclusionMap_val, globalInterpolation_grid externalStep τ hτ f hfr hfm (hjk.trans (Nat.le_succ _))] at hh
    rw [hNorm_sub_symm]
    exact hh
  have hrho := (hb τ j hτ hτ1 hEnd fj (twistedNumericalBundled_real τ hfr j)
    (twistedNumericalBundled_meanZero τ hfm j) w hw hwm hwM (hδ.trans hE1) s hs).2.1
  rw [sobolev_norm, residualPiece_val]
  exact hrho.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) (mul_nonneg hC.le hτ.le))




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




theorem concatenate_ae_bound_on_steps {s τ b A : ℝ} (hτ : 0 < τ) (F : ℕ → ℝ → Sobolev s)
    {j0 k : ℕ} (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ)
    (hLocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b → ‖F j t‖ ≤ A) :
    ∀ᵐ t ∂volume.restrict (Set.Icc ((j0 : ℝ) * τ) b), ‖concatenate τ F k t‖ ≤ A := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)).ae_notMem
      (volume.restrict (Set.Icc ((j0 : ℝ) * τ) b))] with t ht hnot
  have hneq : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => hnot ⟨j, heq.symm⟩
  have hat : (j0 : ℝ) * τ < t := lt_of_le_of_ne ht.1 (Ne.symm (hneq j0))
  have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg j0) hτ.le) hat
  have htT : t < ((k + 1 : ℕ) : ℝ) * τ := lt_of_le_of_ne (ht.2.trans hb) (hneq (k + 1))
  obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k ht0 htT hneq
  have hj0 : j0 ≤ j := by
    by_contra hn
    have hn' : j + 1 ≤ j0 := by omega
    have hbound : ((j + 1 : ℕ) : ℝ) * τ ≤ (j0 : ℝ) * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn') hτ.le
    linarith [hstep.2]
  rw [concatenate_on_open_step hτ.le F hj hstep]
  exact hLocal j hj0 hj t ⟨hstep.1.le, hstep.2.le⟩ ht.2

theorem frozen_comparison_bound (externalStep : LiWuStepIdentity) {T τ γ M E b : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k j0 : ℕ) (_hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (_hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (hγ2 : γ ≤ 2)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    (huM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M)
    (he : ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
      hNorm 0 (errorPath externalStep hT hτ f hfr hfm hu k t).val ≤ E)
    {j : ℕ} (hj0 : j0 ≤ j) (hjk : j ≤ k) (hjb : (j : ℝ) * τ ≤ b) :
    let w := (extendedTwistedPath hT hu ((j : ℝ) * τ)).val
    InSobolev γ w ∧ MeanZero w ∧ hNorm γ w ≤ M ∧
      hNorm 0 ((twistedNumericalBundled τ f j).val - w) ≤ E := by
  dsimp only
  have hgrid : (j : ℝ) * τ ∈ Set.Icc ((j0 : ℝ) * τ) b :=
    ⟨mul_le_mul_of_nonneg_right (by exact_mod_cast hj0) hτ.le, hjb⟩
  refine ⟨(extendedTwistedPath hT hu _).property.of_le hγ2,
    extendedTwistedPath_meanZero hT hu _, extendedTwistedPath_bound hT hu huM _, ?_⟩
  have hh := he _ hgrid
  change hNorm 0 ((inclusionMap 1 2 (by norm_num) (extendedTwistedPath hT hu ((j : ℝ) * τ)) -
    globalInterpolation externalStep τ hτ f hfr hfm k ((j : ℝ) * τ)).val) ≤ E at hh
  rw [sobolev_val_sub, inclusionMap_val,
    globalInterpolation_grid externalStep τ hτ f hfr hfm (hjk.trans (Nat.le_succ _))] at hh
  rw [hNorm_sub_symm]
  exact hh

/-- The global residual derivative estimate needed for (28), in its genuine
essential time norm. The possible previous-step value at the restart point is
handled as a null singleton, rather than assigned an unsupported pointwise bound. -/
theorem restarted_residual_derivative_time_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          timeLInfinity ((j0 : ℝ) * τ) b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar])
            (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t)) ≤
              C * (τ ^ γ + E) := by
  obtain ⟨C, hC, hb⟩ := numerical_residual_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  let F : ℕ → ℝ → Sobolev (-pStar) := fun j t => inclusionMap (-pStar) 0 (by norm_num [pStar])
    (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t)
  have hmap : concatenate τ F k = (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar])
      (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t)) := by
    funext t
    exact concatenate_map τ _ (fun _ v => inclusionMap (-pStar) 0 (by norm_num [pStar]) v) k t
  rw [← hmap]
  apply timeLInfinity_le_of_ae_bound (mul_nonneg hC.le (add_nonneg (Real.rpow_nonneg hτ.le γ) hE))
  apply concatenate_ae_bound_on_steps hτ F hbT
  intro j hj0j hjk t ht htb
  obtain ⟨hw, hwm, hwM, hδ⟩ := frozen_comparison_bound externalStep hT.le hτ k j0 hTotal hbT
    (by linarith : γ ≤ 2) f hfr hfm hu huM he hj0j hjk (ht.1.trans htb)
  have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal
  have hR := (hb τ j hτ hτ1 hEnd (twistedNumericalBundled τ f j)
    (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)
    _ hw hwm hwM (hδ.trans hE1) t ht).2.2.2
  rw [sobolev_norm]
  change hNorm (-pStar) (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j t).val ≤ _
  rw [numericalResidualDerivativeFamily_val]
  exact hR.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) hC.le)




theorem timeLInfinity_sub_le {s a b : ℝ} {f g : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hg : MemLp g ∞ (volume.restrict (Set.Icc a b))) :
    timeLInfinity a b (fun t => f t - g t) ≤ timeLInfinity a b f + timeLInfinity a b g := by
  apply timeLInfinity_le_of_ae_bound (add_nonneg (timeLInfinity_nonneg _ _ _) (timeLInfinity_nonneg _ _ _))
  filter_upwards [timeLInfinity_ae_bound hf, timeLInfinity_ae_bound hg] with t ht ht'
  exact (norm_sub_le _ _).trans (add_le_add ht ht')

theorem timeLInfinity_smul_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (z : ℂ) :
    timeLInfinity a b (fun t => z • f t) ≤ ‖z‖ * timeLInfinity a b f := by
  apply timeLInfinity_le_of_ae_bound (mul_nonneg (norm_nonneg _) (timeLInfinity_nonneg _ _ _))
  filter_upwards [timeLInfinity_ae_bound hf] with t ht
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

theorem timeXNorm_affine_le {a b : ℝ} {f g : ℝ → Sobolev 0} {df dg : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (hg : MemLp g ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (hdg : MemLp dg ∞ (volume.restrict (Set.Icc a b))) (z : ℂ) :
    timeXNorm a b (fun t => f t - z • g t) (fun t => df t - z • dg t) ≤
      timeXNorm a b f df + ‖z‖ * timeXNorm a b g dg := by
  have h0 := timeLInfinity_sub_le hf (hg.const_smul z)
  have hd0 := timeLInfinity_sub_le hdf (hdg.const_smul z)
  have hs := timeLInfinity_smul_le hg z
  have hds := timeLInfinity_smul_le hdg z
  change timeLInfinity a b (fun t => f t - z • g t) + timeLInfinity a b (fun t => df t - z • dg t) ≤ _
  calc
    _ ≤ (timeLInfinity a b f + ‖z‖ * timeLInfinity a b g) +
        (timeLInfinity a b df + ‖z‖ * timeLInfinity a b dg) :=
      add_le_add (h0.trans (add_le_add le_rfl hs)) (hd0.trans (add_le_add le_rfl hds))
    _ = _ := by unfold timeXNorm; ring

def exactL2Path {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : Sobolev 0 :=
  inclusionMap 0 2 (by norm_num) (extendedTwistedPath hT hu t)

def exactNegativeDerivative {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : Sobolev (-pStar) :=
  inclusionMap (-pStar) 1 (by norm_num [pStar]) (exactTwistedDerivative hT hu t)

theorem exactL2Path_bound {T γ M : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hu : KdVSolution 2 T u0 u)
    (hM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) (r : ℝ) : ‖exactL2Path hT hu r‖ ≤ M := by
  rw [sobolev_norm]
  exact (hNorm_mono ((extendedTwistedPath hT hu r).property.of_le hγ2) hγ).trans
    (extendedTwistedPath_bound hT hu hM r)

theorem exact_time_bounds {T γ M : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hM : 0 ≤ M) (hu : KdVSolution 2 T u0 u)
    (huM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    MemLp (exactL2Path hT hu) ∞ (volume.restrict (Set.Icc a b)) ∧
    MemLp (exactNegativeDerivative hT hu) ∞ (volume.restrict (Set.Icc a b)) ∧
    WeakTimeDerivative a b (fun t => (exactL2Path hT hu t).val) (fun t => (exactNegativeDerivative hT hu t).val) ∧
    timeXNorm a b (exactL2Path hT hu) (exactNegativeDerivative hT hu) ≤
      M + (1 / 2 : ℝ) * negativeProductConstant (9 / 14) (by norm_num) * M ^ 2 := by
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  have hfC : Continuous (exactL2Path hT hu) :=
    (inclusionMap 0 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
  have hdfC : Continuous (exactNegativeDerivative hT hu) :=
    (inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp (continuous_exactTwistedDerivative hT hu)
  refine ⟨continuousOn_memLp_top_Icc hfC.continuousOn, continuousOn_memLp_top_Icc hdfC.continuousOn, ?_, ?_⟩
  · have hvc : Continuous (exactTwistedOne hT hu) :=
      (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
    have hreg := regularFourierPath_of_bundled (a := a) (b := b) hvc (continuous_exactTwistedDerivative hT hu)
      (fun t ht k => extendedTwistedPath_hasDerivAt hT hu
        ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩ k)
    exact hreg.weakTimeDerivative hab
  · have hfb : timeLInfinity a b (exactL2Path hT hu) ≤ M := timeLInfinity_le_of_bound hM _
      (fun t _ => exactL2Path_bound hT hγ hγ2 hu huM t)
    have hdfb : timeLInfinity a b (exactNegativeDerivative hT hu) ≤ (1 / 2 : ℝ) * K * M ^ 2 := by
      apply timeLInfinity_le_of_bound (by positivity)
      intro t _
      have hf0 := (extendedTwistedPath hT hu t).property.of_le (by norm_num : (0 : ℝ) ≤ 2)
      obtain ⟨hB, hBn⟩ := B_negative_bound hf0 hf0 t
      have hvM : hNorm 0 (extendedTwistedPath hT hu t).val ≤ M := by
        simpa only [sobolev_norm, exactL2Path, inclusionMap_val] using exactL2Path_bound hT hγ hγ2 hu huM t
      rw [sobolev_norm]
      change hNorm (-pStar) (exactTwistedDerivative hT hu t).val ≤ _
      rw [exactTwistedDerivative_equation, hNorm_smul hB]
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      have hv0 := hNorm_nonneg 0 (extendedTwistedPath hT hu t).val
      calc
        _ ≤ (1 / 2 : ℝ) * (K * hNorm 0 (extendedTwistedPath hT hu t).val * hNorm 0 (extendedTwistedPath hT hu t).val) :=
          mul_le_mul_of_nonneg_left hBn (by norm_num)
        _ ≤ (1 / 2 : ℝ) * (K * M * M) := by gcongr
        _ = _ := by ring
    exact add_le_add hfb hdfb



theorem errorDerivative_ae_equation (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (_hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t).val =
        B t (errorPath externalStep hT hτ f hfr hfm hu k t).val
          (errorMidpoint externalStep hT hτ f hfr hfm hu k t).val -
        (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t).val := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (Set.countable_range (fun j : ℕ => (j : ℝ) * τ)).ae_notMem (volume.restrict (Set.Icc a b))] with t ht hnot
  have hneq : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => hnot ⟨j, heq.symm⟩
  have htz : t ≠ 0 := by simpa only [Nat.cast_zero, zero_mul] using hneq 0
  have ht0 : 0 < t := lt_of_le_of_ne (ha.trans ht.1) (Ne.symm htz)
  have htT : t < ((k + 1 : ℕ) : ℝ) * τ := lt_of_le_of_ne (ht.2.trans hb) (hneq (k + 1))
  obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k ht0 htT hneq
  simp only [errorNegativeDerivative, inclusionMap_val]
  rw [concatenate_on_open_step hτ.le _ hj hstep, concatenate_on_open_step hτ.le _ hj hstep]
  exact errorDerivativeFamily_equation externalStep hT hτ f hfr hfm hu hj ⟨hstep.1.le, hstep.2.le⟩

/-- The small error `X` norm in (28), with actual weak derivatives and time
memberships. This follows from the proved restarted residual derivative bound. -/
theorem restarted_error_time_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          timeXNorm ((j0 : ℝ) * τ) b (errorL2Path externalStep hT.le hτ f hfr hfm hu k)
            (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k) ≤ C * (τ ^ γ + E) := by
  obtain ⟨Cr, hCr, hR⟩ := restarted_residual_derivative_time_bound externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  let D : ℝ := K * (M + 1) + Cr
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + D, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  let a : ℝ := (j0 : ℝ) * τ
  let q : ℝ := τ ^ γ + E
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  let de := errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k
  let rn := numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm
  let Rn : ℝ → Sobolev (-pStar) := fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (concatenate τ rn k t)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) hE
  have hEq : E ≤ q := le_add_of_nonneg_left (Real.rpow_nonneg hτ.le γ)
  have hRN := hR τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  have hMemR : MemLp (concatenate τ rn k) ∞ (volume.restrict (Set.Icc a b)) :=
    memLp_concatenate τ rn (fun j => continuousOn_memLp_top_Icc
      (continuous_numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j).continuousOn) k
  have hMemRn : MemLp Rn ∞ (volume.restrict (Set.Icc a b)) :=
    hMemR.continuousLinearMap_comp (inclusionMap (-pStar) 0 (by norm_num [pStar]))
  have hRae : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖Rn t‖ ≤ Cr * q :=
    (timeLInfinity_ae_bound hMemRn).mono (fun _ ht => ht.trans hRN)
  have hdeEq := errorDerivative_ae_equation externalStep hT.le hτ k hTotal f hfr hfm hu
    (mul_nonneg (Nat.cast_nonneg j0) hτ.le) hbT
  have hdeb : timeLInfinity a b de ≤ D * q := by
    apply timeLInfinity_le_of_ae_bound (mul_nonneg hD hq)
    filter_upwards [hdeEq, hRae, ae_restrict_mem measurableSet_Icc] with t hdt hrt ht
    have he0 := (e t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hg0 := (g t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have heb : hNorm 0 (e t).val ≤ E := he t ht
    have hv0 : hNorm 0 (exactTwistedOne hT.le hu t).val ≤ M := by
      simpa only [sobolev_norm, exactL2Path, exactTwistedOne, inclusionMap_val] using
        exactL2Path_bound hT.le hγ.le (by linarith : γ ≤ 2) hu huM t
    have hgb : hNorm 0 (g t).val ≤ M + 1 := by
      have hG := hNorm_sub_le ((exactTwistedOne hT.le hu t).property.of_le (by norm_num)) (he0.smul (1 / 2 : ℂ))
      rw [hNorm_smul he0] at hG
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf] at hG
      change hNorm 0 (g t).val ≤ _ at hG
      linarith
    obtain ⟨hB, hBn⟩ := B_negative_bound he0 hg0 t
    have hBbound : hNorm (-pStar) (B t (e t).val (g t).val) ≤ K * (M + 1) * q := by
      calc
        _ ≤ K * hNorm 0 (e t).val * hNorm 0 (g t).val := hBn
        _ ≤ K * q * (M + 1) := mul_le_mul (mul_le_mul_of_nonneg_left (heb.trans hEq) hK) hgb
          (hNorm_nonneg _ _) (mul_nonneg hK hq)
        _ = _ := by ring
    rw [sobolev_norm]
    change hNorm (-pStar) (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k t).val ≤ D * q
    rw [hdt]
    have hrt' : hNorm (-pStar) (concatenate τ rn k t).val ≤ Cr * q := by
      simpa only [sobolev_norm, Rn, inclusionMap_val] using hrt
    calc
      _ ≤ hNorm (-pStar) (B t (e t).val (g t).val) + hNorm (-pStar) (concatenate τ rn k t).val :=
        hNorm_sub_le hB (Rn t).property
      _ ≤ K * (M + 1) * q + Cr * q := add_le_add hBbound hrt'
      _ = _ := by dsimp [D]; ring
  have heb : timeLInfinity a b (errorL2Path externalStep hT.le hτ f hfr hfm hu k) ≤ E :=
    timeLInfinity_le_of_bound hE _ (fun t ht => by rw [sobolev_norm]; exact he t ht)
  change timeLInfinity a b (errorL2Path externalStep hT.le hτ f hfr hfm hu k) + timeLInfinity a b de ≤ _
  calc
    _ ≤ E + D * q := add_le_add heb hdeb
    _ ≤ (1 + D) * q := by linarith




def affineErrorPath (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (z : ℂ) (t : ℝ) : Sobolev 1 :=
  exactTwistedOne hT hu t - z • errorPath externalStep hT hτ f hfr hfm hu k t

def affineErrorDerivativeFamily (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) (j : ℕ) (t : ℝ) : Sobolev 1 :=
  exactTwistedDerivative hT hu t - z • errorDerivativeFamily externalStep hT hτ f hfr hfm hu j t

theorem continuous_affineErrorPath (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (z : ℂ) :
    Continuous (affineErrorPath externalStep hT hτ f hfr hfm hu k z) :=
  ((inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)).sub
    ((continuous_const (y := z)).smul (continuous_errorPath externalStep hT hτ f hfr hfm hu k))

theorem continuous_affineErrorDerivativeFamily (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) (j : ℕ) :
    Continuous (affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z j) :=
  (continuous_exactTwistedDerivative hT hu).sub
    ((continuous_const (y := z)).smul (continuous_errorDerivativeFamily externalStep hT hτ f hfr hfm hu j))

theorem affineErrorPath_hasDerivAt_on_step (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) {j : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (affineErrorPath externalStep hT hτ f hfr hfm hu k z r).val m)
      ((affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z j t).val m) t := by
  have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg j) hτ.le) ht.1
  have htT : t < T := lt_of_lt_of_le ht.2
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal)
  exact (extendedTwistedPath_hasDerivAt hT hu ⟨ht0, htT⟩ m).sub
    ((errorPath_hasDerivAt_on_step externalStep hT hτ k hTotal f hfr hfm hu hjk ht m).const_mul z)

/-- Every affine combination used in (28) has the actual piecewise weak
 derivative, not a formally assigned derivative. -/
theorem affine_error_time_membership (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    MemLp (fun t => exactL2Path hT hu t - z • errorL2Path externalStep hT hτ f hfr hfm hu k t)
      ∞ (volume.restrict (Set.Icc a b)) ∧
    MemLp (fun t => exactNegativeDerivative hT hu t - z • errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t)
      ∞ (volume.restrict (Set.Icc a b)) ∧
    WeakTimeDerivative a b
      (fun t => (exactL2Path hT hu t - z • errorL2Path externalStep hT hτ f hfr hfm hu k t).val)
      (fun t => (exactNegativeDerivative hT hu t - z • errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t).val) := by
  have he := error_time_membership externalStep hT hτ k hTotal f hfr hfm hu ha hab hb
  have hv : MemLp (exactL2Path hT hu) ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc (((inclusionMap 0 2 (by norm_num)).continuous.comp
      (continuous_extendedTwistedPath hT hu)).continuousOn)
  have hdv : MemLp (exactNegativeDerivative hT hu) ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc (((inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp
      (continuous_exactTwistedDerivative hT hu)).continuousOn)
  refine ⟨hv.sub (he.1.const_smul z), hdv.sub (he.2.1.const_smul z), ?_⟩
  have hw := grid_weakTimeDerivative τ hτ k
    (affineErrorPath externalStep hT hτ f hfr hfm hu k z)
    (affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z)
    (continuous_affineErrorPath externalStep hT hτ f hfr hfm hu k z)
    (continuous_affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z)
    (fun j hj t ht m => affineErrorPath_hasDerivAt_on_step externalStep hT hτ k hTotal f hfr hfm hu z hj ht m)
    ha hab hb
  have hd (t : ℝ) : concatenate τ (affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z) k t =
      exactTwistedDerivative hT hu t - z • concatenate τ (errorDerivativeFamily externalStep hT hτ f hfr hfm hu) k t :=
    concatenate_map τ _ (fun r w => exactTwistedDerivative hT hu r - z • w) k t
  simpa only [affineErrorPath, hd, sobolev_val_sub, sobolev_val_smul, exactL2Path,
    exactNegativeDerivative, errorL2Path, errorNegativeDerivative, exactTwistedOne, inclusionMap_val] using hw

/-- The remaining uniform `X` bounds in (28). The coefficient `z=1` gives
 the numerical interpolation and `z=1/2` the midpoint in the error equation. -/
theorem restarted_affine_error_time_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          ∀ z : ℂ, ‖z‖ ≤ 1 →
          timeXNorm ((j0 : ℝ) * τ) b
            (fun t => exactL2Path hT.le hu t - z • errorL2Path externalStep hT.le hτ f hfr hfm hu k t)
            (fun t => exactNegativeDerivative hT.le hu t - z • errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k t) ≤ C := by
  obtain ⟨Ce, hCe, he⟩ := restarted_error_time_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  let Cv := M + (1 / 2 : ℝ) * negativeProductConstant (9 / 14) (by norm_num) * M ^ 2
  have hK : 0 ≤ negativeProductConstant (9 / 14) (by norm_num) := norm_nonneg _
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  refine ⟨1 + Cv + 2 * Ce, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 hbound z hz
  have ha : 0 ≤ (j0 : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ.le
  obtain ⟨hv, hdv, _, hxv⟩ := exact_time_bounds hT.le hγ.le (by linarith : γ ≤ 2) hM hu huM ha hab (hb.trans hTotal)
  obtain ⟨he0, hde, _⟩ := error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu ha hab hb
  have hxe := he τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 hbound
  have hq2 : τ ^ γ + E ≤ 2 := by linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  calc
    _ ≤ timeXNorm ((j0 : ℝ) * τ) b (exactL2Path hT.le hu) (exactNegativeDerivative hT.le hu) +
        ‖z‖ * timeXNorm ((j0 : ℝ) * τ) b (errorL2Path externalStep hT.le hτ f hfr hfm hu k)
          (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k) := timeXNorm_affine_le hv he0 hdv hde z
    _ ≤ Cv + 2 * Ce := by
      have he2 : timeXNorm ((j0 : ℝ) * τ) b (errorL2Path externalStep hT.le hτ f hfr hfm hu k)
          (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k) ≤ 2 * Ce := by nlinarith
      exact add_le_add hxv (calc
        _ ≤ 1 * (2 * Ce) := mul_le_mul hz he2 (timeXNorm_nonneg _ _ _ _) (by norm_num)
        _ = _ := one_mul _)
    _ ≤ _ := by linarith

theorem affineErrorPath_one (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (t : ℝ) :
    affineErrorPath externalStep hT hτ f hfr hfm hu k 1 t = globalInterpolation externalStep τ hτ f hfr hfm k t := by
  simp only [affineErrorPath, errorPath, one_smul, sub_sub_cancel]

theorem affineErrorPath_half (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (t : ℝ) :
    affineErrorPath externalStep hT hτ f hfr hfm hu k (1 / 2) t = errorMidpoint externalStep hT hτ f hfr hfm hu k t := rfl



theorem timeLInfinity_le_timeXNorm (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) :
    timeLInfinity a b f ≤ timeXNorm a b f df :=
  le_add_of_nonneg_right (timeLInfinity_nonneg _ _ _)

/-- A moving small input, in any position allowed by the primary trilinear
 estimate, gives one full time-step gain. The operator slots stay fixed. -/
theorem dynamic_small_input_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b τ A B : ℝ, 0 ≤ a → a ≤ b → b - a ≤ τ → τ ≤ 1 →
      0 ≤ τ → 0 ≤ A → 0 ≤ B →
      ∀ f : Fin 3 → ℝ → Sobolev 0, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
      (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
      (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
      (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
      ∀ i : Fin 3,
        timeXNorm a b (f i) (df i) ≤ A →
        (∀ j, j ≠ i → timeXNorm a b (f j) (df j) ≤ B) →
        timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (f i t)) ≤ τ * A →
        InSobolev 0 (CIntegral a b (fun t => (f 0 t).val) (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ∧
        hNorm 0 (CIntegral a b (fun t => (f 0 t).val) (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ≤
          C * τ * A * B ^ 2 := by
  obtain ⟨C, hC, hd⟩ := normalized_dynamic_trilinear externalTrilinear (H := 1) (by norm_num) le_rfl
  refine ⟨2 * C, by positivity, ?_⟩
  intro a b τ A B ha hab hlen hτ1 hτ hA hB f df hf hdf hw i hXi hX hNi
  obtain ⟨hmem, hbound⟩ := hd a b ha hab (hlen.trans hτ1) f df hf hdf hw
  have hprod : (∏ j : Fin 3, timeXNorm a b (f j) (df j)) ≤ A * B ^ 2 := by
    fin_cases i <;> simp only [Fin.prod_univ_three]
    · change timeXNorm a b (f 0) (df 0) ≤ A at hXi
      have hX1 := hX 1 (by decide); have hX2 := hX 2 (by decide)
      simpa only [pow_two, mul_assoc] using mul_le_mul
        (mul_le_mul hXi hX1 (timeXNorm_nonneg _ _ _ _) hA) hX2
        (timeXNorm_nonneg _ _ _ _) (mul_nonneg hA hB)
    · change timeXNorm a b (f 1) (df 1) ≤ A at hXi
      have hX0 := hX 0 (by decide); have hX2 := hX 2 (by decide)
      have h012 := mul_le_mul (mul_le_mul hX0 hXi (timeXNorm_nonneg _ _ _ _) hB) hX2
        (timeXNorm_nonneg _ _ _ _) (mul_nonneg hB hA)
      calc
        _ ≤ B * A * B := h012
        _ = _ := by ring
    · change timeXNorm a b (f 2) (df 2) ≤ A at hXi
      have hX0 := hX 0 (by decide); have hX1 := hX 1 (by decide)
      have h012 := mul_le_mul (mul_le_mul hX0 hX1 (timeXNorm_nonneg _ _ _ _) hB) hXi
        (timeXNorm_nonneg _ _ _ _) (mul_nonneg hB hB)
      calc
        _ ≤ B * B * A := h012
        _ = _ := by ring
  have hothers : (∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j)) ≤ B ^ 2 := by
    have hL (j : Fin 3) (hji : j ≠ i) : timeLInfinity a b (f j) ≤ B :=
      (timeLInfinity_le_timeXNorm a b _ _).trans (hX j hji)
    fin_cases i <;> simp [Fin.prod_univ_three]
    · simpa only [pow_two] using mul_le_mul (hL 1 (by decide)) (hL 2 (by decide))
        (timeLInfinity_nonneg _ _ _) hB
    · simpa only [pow_two] using mul_le_mul (hL 0 (by decide)) (hL 2 (by decide))
        (timeLInfinity_nonneg _ _ _) hB
    · simpa only [pow_two] using mul_le_mul (hL 0 (by decide)) (hL 1 (by decide))
        (timeLInfinity_nonneg _ _ _) hB
  refine ⟨hmem, (hbound i).trans ?_⟩
  have hp0 : 0 ≤ ∏ j : Fin 3, if j = i then 1 else timeLInfinity a b (f j) :=
    Finset.prod_nonneg (fun j _ => by split_ifs; exact zero_le_one; exact timeLInfinity_nonneg _ _ _)
  calc
    _ ≤ C * τ * (A * B ^ 2) + C * (τ * A) * B ^ 2 :=
      add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hlen hC.le) hprod
        (Finset.prod_nonneg (fun j _ => timeXNorm_nonneg _ _ _ _)) (mul_nonneg hC.le hτ))
        (mul_le_mul (mul_le_mul_of_nonneg_left hNi hC.le) hothers hp0 (by positivity))
    _ = _ := by ring



def frozenL2Path (a : ℝ) (f : Sobolev 2) (t : ℝ) : Sobolev 0 :=
  inclusionMap 0 1 (by norm_num) (frozenZBundled a t f)

def frozenNegativeDerivative (f : Sobolev 2) (t : ℝ) : Sobolev (-pStar) :=
  inclusionMap (-pStar) 1 (by norm_num [pStar]) ((1 / 2 : ℂ) • BTwoBundled t f f)

theorem numerical_frozen_time_bounds (externalStage : LiWuStageEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          let a := (n : ℝ) * τ
          MemLp (frozenL2Path a f) ∞ (volume.restrict (Set.Icc a t)) ∧
          MemLp (frozenNegativeDerivative f) ∞ (volume.restrict (Set.Icc a t)) ∧
          WeakTimeDerivative a t (fun s => (frozenL2Path a f s).val) (fun s => (frozenNegativeDerivative f s).val) ∧
          timeXNorm a t (frozenL2Path a f) (frozenNegativeDerivative f) ≤ C := by
  obtain ⟨Cn, hCn, hstage⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  let Z := M + 1 + 2 * Cn
  let D := (1 / 2 : ℝ) * K * (M + 1) ^ 2
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + Z + D, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  dsimp only
  let a : ℝ := (n : ℝ) * τ
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hw0 := hw.of_le hγ.le
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hfc : Continuous (frozenL2Path a f) := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_frozenZBundled a f)
  have hdc : Continuous (frozenNegativeDerivative f) := (inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp
    ((continuous_const (y := (1 / 2 : ℂ))).smul (continuous_BTwoBundled continuous_id (continuous_const (y := f)) (continuous_const (y := f))))
  refine ⟨continuousOn_memLp_top_Icc hfc.continuousOn, continuousOn_memLp_top_Icc hdc.continuousOn,
    (frozenZ_regular f hfm).weakTimeDerivative ht.1, ?_⟩
  have hfb : timeLInfinity a t (frozenL2Path a f) ≤ Z := by
    apply timeLInfinity_le_of_bound hZ
    intro s hs
    have hss : s ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) := ⟨hs.1, hs.2.trans ht.2⟩
    have hFb := (hstage τ n s hτ hτ1 hnT hss f.val w hf0 hw hwm hwM hδ).2.2.2
    have hq2 : τ ^ γ + hNorm 0 (f.val - w) ≤ 2 := by linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
    have hF0 := (bilinearStage_h1_bound hf0 hf0 a s).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hF2 : hNorm 0 (bilinearStage a s f.val f.val) ≤ 2 * Cn :=
      hFb.trans (by nlinarith)
    rw [sobolev_norm]
    exact (hNorm_add_le hf0 hF0).trans (by change hNorm 0 f.val + hNorm 0 (bilinearStage a s f.val f.val) ≤ Z; dsimp [Z]; linarith)
  have hdb : timeLInfinity a t (frozenNegativeDerivative f) ≤ D := by
    apply timeLInfinity_le_of_bound hD
    intro s _
    obtain ⟨hB, hBn⟩ := B_negative_bound hf0 hf0 s
    have hfnonneg := hNorm_nonneg 0 f.val
    rw [sobolev_norm]
    change hNorm (-pStar) ((1 / 2 : ℂ) • B s f.val f.val) ≤ D
    rw [hNorm_smul hB, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    calc
      _ ≤ (1 / 2 : ℝ) * (K * hNorm 0 f.val * hNorm 0 f.val) := mul_le_mul_of_nonneg_left hBn (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (K * (M + 1) * (M + 1)) := by gcongr
      _ = D := by dsimp [D]; ring
  exact (add_le_add hfb hdb).trans (by linarith)



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



theorem J_neg_left (t : ℝ) (f g : Fourier) : J t (-f) g = -J t f g := by
  simpa only [neg_one_smul] using J_smul_left t (-1 : ℂ) f g

theorem residual_forcing_integrand_identity {τ t : ℝ} (Y Z V : Sobolev 1) (W : Sobolev 0) :
    J t (- B t Y.val Z.val - (1 / 2 : ℂ) • B t Y.val Y.val - ((τ⁻¹ : ℝ) : ℂ) • W.val) V.val =
      - CIntegrand t Y.val Z.val V.val - (1 / 2 : ℂ) • CIntegrand t Y.val Y.val V.val -
        ((τ⁻¹ : ℝ) : ℂ) • J t W.val V.val := by
  have hB := (B_h1_bound Y.property Z.property t).1
  have hB2 := (B_h1_bound Y.property Y.property t).1
  have hV := V.property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  rw [J_sub_left ((hB.neg).sub (hB2.smul (1 / 2 : ℂ))) (W.property.smul _) hV,
    J_sub_left hB.neg (hB2.smul (1 / 2 : ℂ)) hV, J_neg_left, J_smul_left, J_smul_left,
    J_B, J_B]
  rfl

/-- Integrating the actual residual derivative yields two explicit cubic
 integrals and the constant endpoint correction. -/
theorem residual_forcing_integral_identity (externalStep : LiWuStepIdentity)
    {τ : ℝ} (hτ : 0 < τ) (n : ℕ) (f : Sobolev 2)
    (hfr : RealValued f.val) (hfm : MeanZero f.val)
    (V : ℝ → Sobolev 1) (hV : Continuous V) (b : ℝ) :
    (fun m => ∫ t : ℝ in (n : ℝ) * τ..b,
      J t (localResidualDerivative τ ((n : ℝ) * τ) t f.val) (V t).val m) =
      - CIntegral ((n : ℝ) * τ) b
        (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val)
        (fun t => frozenZ ((n : ℝ) * τ) t f.val) (fun t => (V t).val) -
      (1 / 2 : ℂ) • CIntegral ((n : ℝ) * τ) b
        (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val)
        (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val) (fun t => (V t).val) -
      ((τ⁻¹ : ℝ) : ℂ) • (fun m => ∫ t : ℝ in (n : ℝ) * τ..b,
        J t (endpointCorrection τ ((n : ℝ) * τ) f.val) (V t).val m) := by
  let a : ℝ := (n : ℝ) * τ
  let Y := fun t => defectBundled externalStep τ hτ n t f hfr hfm
  let Z := fun t => frozenZBundled a t f
  let W := inclusionMap 0 1 (by norm_num) (endpointCorrectionBundled externalStep τ hτ n f hfr hfm)
  have hYC : Continuous Y := continuous_defectBundled externalStep τ hτ n f hfr hfm
  have hZC : Continuous Z := continuous_frozenZBundled a f
  funext m
  have hpoint (t : ℝ) : J t (localResidualDerivative τ a t f.val) (V t).val m =
      - CIntegrand t (Y t).val (Z t).val (V t).val m -
      (1 / 2 : ℂ) * CIntegrand t (Y t).val (Y t).val (V t).val m -
      ((τ⁻¹ : ℝ) : ℂ) * J t W.val (V t).val m := by
    have h := congrFun (residual_forcing_integrand_identity (τ := τ) (t := t) (Y t) (Z t) (V t) W) m
    simpa only [Y, Z, W, localResidualDerivative, defectBundled_val, frozenZBundled_val,
      inclusionMap_val, endpointCorrectionBundled, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using h
  have hi1 : IntervalIntegrable (fun t => CIntegrand t (Y t).val (Z t).val (V t).val m) volume a b :=
    (continuous_CIntegrand_paths hYC hZC hV m).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t => CIntegrand t (Y t).val (Y t).val (V t).val m) volume a b :=
    (continuous_CIntegrand_paths hYC hYC hV m).intervalIntegrable a b
  have hi3 : IntervalIntegrable (fun t => J t W.val (V t).val m) volume a b := by
    have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
      (continuous_const (y := W)) ((inclusionMap 0 1 (by norm_num)).continuous.comp hV))
    exact h.intervalIntegrable a b
  have hiN : IntervalIntegrable (fun t => - CIntegrand t (Y t).val (Z t).val (V t).val m) volume a b := hi1.neg
  have hint := intervalIntegral.integral_congr (μ := volume) (a := a) (b := b) (fun t _ => hpoint t)
  rw [intervalIntegral.integral_sub (hiN.sub (hi2.const_mul (1 / 2 : ℂ))) (hi3.const_mul (((τ⁻¹ : ℝ) : ℂ))),
    intervalIntegral.integral_sub hiN (hi2.const_mul (1 / 2 : ℂ)), intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  simpa only [CIntegral, CIntegrand, Y, Z, W, a, defectBundled_val, frozenZBundled_val, inclusionMap_val,
    endpointCorrectionBundled, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using hint



theorem dynamic_small_first_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b τ A B : ℝ, 0 ≤ a → a ≤ b → b - a ≤ τ → τ ≤ 1 →
      0 ≤ τ → 0 ≤ A → 0 ≤ B →
      ∀ Y Z V : ℝ → Sobolev 0, ∀ dY dZ dV : ℝ → Sobolev (-pStar),
      MemLp Y ∞ (volume.restrict (Set.Icc a b)) →
      MemLp Z ∞ (volume.restrict (Set.Icc a b)) →
      MemLp V ∞ (volume.restrict (Set.Icc a b)) →
      MemLp dY ∞ (volume.restrict (Set.Icc a b)) →
      MemLp dZ ∞ (volume.restrict (Set.Icc a b)) →
      MemLp dV ∞ (volume.restrict (Set.Icc a b)) →
      WeakTimeDerivative a b (fun t => (Y t).val) (fun t => (dY t).val) →
      WeakTimeDerivative a b (fun t => (Z t).val) (fun t => (dZ t).val) →
      WeakTimeDerivative a b (fun t => (V t).val) (fun t => (dV t).val) →
      timeXNorm a b Y dY ≤ A → timeXNorm a b Z dZ ≤ B → timeXNorm a b V dV ≤ B →
      timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤ τ * A →
      InSobolev 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) ∧
      hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) ≤ C * τ * A * B ^ 2 := by
  obtain ⟨C, hC, hd⟩ := dynamic_small_input_bound externalTrilinear
  refine ⟨C, hC, ?_⟩
  intro a b τ A B ha hab hlen hτ1 hτ hA hB Y Z V dY dZ dV hY hZ hV hdY hdZ hdV hwY hwZ hwV hxY hxZ hxV hnY
  exact hd a b τ A B ha hab hlen hτ1 hτ hA hB ![Y,Z,V] ![dY,dZ,dV]
    (by intro j; fin_cases j <;> first | exact hY | exact hZ | exact hV)
    (by intro j; fin_cases j <;> first | exact hdY | exact hdZ | exact hdV)
    (by intro j; fin_cases j <;> first | exact hwY | exact hwZ | exact hwV)
    0 hxY (by intro j hj; fin_cases j; exact (hj rfl).elim; exact hxZ; exact hxV) hnY



set_option maxHeartbeats 800000 in
/-- The forcing term on a whole or partial step. All hypotheses concerning
 the moving third input are explicit internal analytic hypotheses. -/
theorem local_residual_forcing_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      ∀ hτ : 0 < τ, τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ b ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
        ∀ V : ℝ → Sobolev 1, Continuous V → ∀ dV : ℝ → Sobolev (-pStar), ∀ B : ℝ, 1 ≤ B →
        let a := (n : ℝ) * τ
        let V0 := fun t => inclusionMap 0 1 (by norm_num) (V t)
        MemLp V0 ∞ (volume.restrict (Set.Icc a b)) →
        MemLp dV ∞ (volume.restrict (Set.Icc a b)) →
        WeakTimeDerivative a b (fun t => (V0 t).val) (fun t => (dV t).val) →
        timeXNorm a b V0 dV ≤ B →
        (∀ t ∈ Set.Icc a b, hNorm 0 (V t).val ≤ B) →
        InSobolev 0 (fun m => ∫ t : ℝ in a..b, J t (localResidualDerivative τ a t f.val) (V t).val m) ∧
        hNorm 0 (fun m => ∫ t : ℝ in a..b, J t (localResidualDerivative τ a t f.val) (V t).val m) ≤
          C * τ * (τ ^ γ + hNorm 0 (f.val - w)) * B ^ 2 := by
  obtain ⟨Cy, hCy, hy⟩ := numerical_defect_partial_time_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cz, hCz, hz⟩ := numerical_frozen_time_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cp, hCp, hp⟩ := dynamic_small_first_bound externalTrilinear
  obtain ⟨Cw, hCw, hw⟩ := numerical_endpoint_correction_bound externalStage externalProduct hT hγ hγ1 hM
  let N := 1 + Cz + 2 * Cy
  let K := 4 * h1EmbeddingConstant
  have hK : 0 ≤ K := by dsimp [K]; have h := h1EmbeddingConstant_ge_one; positivity
  have hN : 1 ≤ N := by dsimp [N]; linarith
  let D := Cp * Cy * N ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + 2 * D + K * Cw, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hwγ hwm hwM hδ b hb V hVC dV B hB
  dsimp only
  intro hV hdV hwV hXV hVB
  let a : ℝ := (n : ℝ) * τ
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  let Y := defectL2Path externalStep τ hτ n f hfr hfm
  let dY := defectNegativeDerivativePath externalStep τ hτ n f hfr hfm
  let Z := frozenL2Path a f
  let dZ := frozenNegativeDerivative f
  let V0 := fun t => inclusionMap 0 1 (by norm_num) (V t)
  have hq : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hq2 : q ≤ 2 := by dsimp [q]; linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  have hB0 : 0 ≤ B := by linarith
  have hNB : B ≤ N * B := by nlinarith
  have hNleNB : N ≤ N * B := by nlinarith
  obtain ⟨hY, hdY, hwY, hXY, hNY⟩ := hy τ n hτ hτ1 hnT f hfr hfm w hwγ hwm hwM hδ b hb
  obtain ⟨hZ, hdZ, hwZ, hXZ⟩ := hz τ n hτ hτ1 hnT f hfm w hwγ hwm hwM hδ b hb
  have hNY' : timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤ τ * (Cy * q) := by
    calc
      _ ≤ Cy * τ * q := hNY
      _ = _ := by ring
  have hXZ' : timeXNorm a b Z dZ ≤ N * B := hXZ.trans (by dsimp [N] at *; linarith)
  have hXY' : timeXNorm a b Y dY ≤ N * B := hXY.trans (calc
    _ ≤ 2 * Cy := by nlinarith
    _ ≤ N := by dsimp [N]; linarith
    _ ≤ _ := hNleNB)
  have hXV' : timeXNorm a b V0 dV ≤ N * B := hXV.trans hNB
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
  have hlen : b - a ≤ τ := grid_interval_length n hb
  obtain ⟨hCI, hCIn⟩ := hp a b τ (Cy * q) (N * B) ha hb.1 hlen hτ1 hτ.le (by positivity) (by positivity)
    Y Z V0 dY dZ dV hY hZ hV hdY hdZ hdV hwY hwZ hwV hXY hXZ' hXV' hNY'
  obtain ⟨hCI2, hCI2n⟩ := hp a b τ (Cy * q) (N * B) ha hb.1 hlen hτ1 hτ.le (by positivity) (by positivity)
    Y Y V0 dY dY dV hY hY hV hdY hdY hdV hwY hwY hwV hXY hXY' hXV' hNY'
  have hCIn' : hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) ≤ D * τ * q * B ^ 2 :=
    hCIn.trans_eq (by dsimp [D]; ring)
  have hCI2n' : hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Y t).val) (fun t => (V t).val)) ≤ D * τ * q * B ^ 2 :=
    hCI2n.trans_eq (by dsimp [D]; ring)
  obtain ⟨hW, hWn⟩ := hw τ n hτ hτ1 hnT f hfm w hwγ hwm hwM hδ
  let W : Sobolev 0 := ⟨endpointCorrection τ a f.val, hW⟩
  let JW := fun t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t W (inclusionMap 0 1 (by norm_num) (V t)))
  have hJWC : Continuous JW := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id (continuous_const (y := W))
      ((inclusionMap 0 1 (by norm_num)).continuous.comp hVC))
  have hJWb : ∀ t ∈ Set.Icc a b, ‖JW t‖ ≤ K * (Cw * τ * q) * B := by
    intro t ht
    have hv0 := (V t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    obtain ⟨hj, hjn⟩ := J_h1_bound W.property hv0 t
    rw [sobolev_norm]
    change hNorm 0 (J t W.val (V t).val) ≤ _
    calc
      _ ≤ hNorm 1 (J t W.val (V t).val) := hNorm_mono hj (by norm_num)
      _ ≤ K * hNorm 0 W.val * hNorm 0 (V t).val := hjn
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hWn hK) (hVB t ht)
        (hNorm_nonneg _ _) (by positivity)
  obtain ⟨hI, hIn⟩ := coefficient_integral_bound hJWC hb.1 hJWb
  change InSobolev 0 (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m) at hI
  change hNorm 0 (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m) ≤ K * (Cw * τ * q) * B * (b - a) at hIn
  have hIs : hNorm 0 (((τ⁻¹ : ℝ) : ℂ) • (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m)) ≤
      K * Cw * τ * q * B := by
    rw [hNorm_smul hI, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hτ]
    calc
      _ ≤ τ⁻¹ * (K * (Cw * τ * q) * B * (b - a)) := mul_le_mul_of_nonneg_left hIn (inv_nonneg.mpr hτ.le)
      _ ≤ τ⁻¹ * (K * (Cw * τ * q) * B * τ) := by gcongr
      _ = _ := by field_simp
  have hId := residual_forcing_integral_identity externalStep hτ n f hfr hfm V hVC b
  have hvY : (fun t => (Y t).val) = (fun t => interpolationRemainder τ ((n : ℝ) * τ) t f.val) :=
    funext (fun t => defectBundled_val externalStep τ hτ n t f hfr hfm)
  have hvZ : (fun t => (Z t).val) = (fun t => frozenZ ((n : ℝ) * τ) t f.val) := rfl
  rw [← hvY, ← hvZ] at hId
  rw [hId]
  refine ⟨(hCI.neg.sub (hCI2.smul (1 / 2 : ℂ))).sub (hI.smul _), ?_⟩
  have htriangle := hNorm_sub_le (hCI.neg.sub (hCI2.smul (1 / 2 : ℂ))) (hI.smul (((τ⁻¹ : ℝ) : ℂ)))
  have htriangle2 := hNorm_sub_le hCI.neg (hCI2.smul (1 / 2 : ℂ))
  rw [hNorm_neg, hNorm_smul hCI2, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at htriangle2
  have hBsq : B ≤ B ^ 2 := by nlinarith
  calc
    _ ≤ hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) +
        (1 / 2 : ℝ) * hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Y t).val) (fun t => (V t).val)) +
        hNorm 0 (((τ⁻¹ : ℝ) : ℂ) • (fun m => ∫ t : ℝ in a..b, J t W.val (V t).val m)) :=
      htriangle.trans (add_le_add htriangle2 le_rfl)
    _ ≤ D * τ * q * B ^ 2 + (1 / 2 : ℝ) * (D * τ * q * B ^ 2) + K * Cw * τ * q * B :=
      add_le_add (add_le_add hCIn' (mul_le_mul_of_nonneg_left hCI2n' (by norm_num))) hIs
    _ ≤ (1 + 2 * D + K * Cw) * τ * q * B ^ 2 := by
      have hBterm := mul_le_mul_of_nonneg_left hBsq (show 0 ≤ K * Cw * τ * q by positivity)
      have hbase : 0 ≤ τ * q * B ^ 2 := by positivity
      nlinarith



theorem integral_concatenate_on_step {s τ : ℝ} (hτ : 0 < τ) (F : ℕ → ℝ → Sobolev s)
    {j k : ℕ} (hjk : j ≤ k) {b : ℝ}
    (hb : b ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) :
    (∫ t : ℝ in (j : ℝ) * τ..b, concatenate τ F k t) =
      ∫ t : ℝ in (j : ℝ) * τ..b, F j t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (((j + 1 : ℕ) : ℝ) * τ)] with t hne
  intro ht
  rw [Set.uIoc_of_le hb.1] at ht
  exact concatenate_on_open_step hτ.le F hjk ⟨ht.1, lt_of_le_of_ne (ht.2.trans hb.2) hne⟩

/-- Finite-step accumulation for genuine Bochner integrals. It includes the
 possible partial final step and requires no agreement of derivative pieces. -/
theorem grid_integral_bound {s τ b A q : ℝ} (hτ : 0 < τ) (F : ℕ → ℝ → Sobolev s)
    (hF : ∀ j, Continuous (F j)) {j0 k : ℕ} (_hj0 : j0 ≤ k)
    (hab : (j0 : ℝ) * τ ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ)
    (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hLocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b →
        ‖∫ r : ℝ in (j : ℝ) * τ..t, F j r‖ ≤ A * τ * q) :
    ‖∫ t : ℝ in (j0 : ℝ) * τ..b, concatenate τ F k t‖ ≤
      A * (b - (j0 : ℝ) * τ + τ) * q := by
  by_cases hba : b = (j0 : ℝ) * τ
  · subst b
    simp only [intervalIntegral.integral_same, norm_zero, sub_self, zero_add]
    positivity
  have hab' : (j0 : ℝ) * τ < b := lt_of_le_of_ne hab (Ne.symm hba)
  obtain ⟨n, hn, hnt⟩ := exists_closed_grid_step hτ k
    ((mul_nonneg (Nat.cast_nonneg j0) hτ.le).trans hab) hb
  have hjn : j0 ≤ n := by
    by_contra h
    have hh : n + 1 ≤ j0 := by omega
    have hc : ((n + 1 : ℕ) : ℝ) * τ ≤ (j0 : ℝ) * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hτ.le
    linarith [hnt.2]
  have hi (a c : ℝ) : IntervalIntegrable (concatenate τ F k) volume a c :=
    intervalIntegrable_concatenate τ F (fun j => (hF j).intervalIntegrable a c) k
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun j : ℕ => (j : ℝ) * τ)
    (f := concatenate τ F k) (μ := volume) hjn (fun j _ => hi _ _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi ((j0 : ℝ) * τ) ((n : ℝ) * τ))
    (hi ((n : ℝ) * τ) b)
  rw [← hsplit, ← hsum]
  have hEach (j : ℕ) (hj : j ∈ Finset.Ico j0 n) :
      (∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, concatenate τ F k t) =
        ∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t :=
    integral_concatenate_on_step hτ F ((Finset.mem_Ico.mp hj).2.le.trans hn)
      ⟨by push_cast; nlinarith, le_rfl⟩
  rw [Finset.sum_congr rfl hEach, integral_concatenate_on_step hτ F hn hnt]
  have hsumBound : ‖∑ j ∈ Finset.Ico j0 n, ∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t‖ ≤
      (n - j0 : ℕ) * (A * τ * q) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico j0 n, ‖∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.Ico j0 n, A * τ * q := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        apply hLocal j hj'.1 (hj'.2.le.trans hn) _ ⟨by push_cast; nlinarith, le_rfl⟩
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj'.2) hτ.le).trans hnt.1
      _ = _ := by simp
  have hlength : ((n - j0 + 1 : ℕ) : ℝ) * τ ≤ b - (j0 : ℝ) * τ + τ := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn]
    linarith [hnt.1]
  calc
    _ ≤ ‖∑ j ∈ Finset.Ico j0 n, ∫ t : ℝ in (j : ℝ) * τ..((j + 1 : ℕ) : ℝ) * τ, F j t‖ +
      ‖∫ t : ℝ in (n : ℝ) * τ..b, F n t‖ := norm_add_le _ _
    _ ≤ (n - j0 : ℕ) * (A * τ * q) + A * τ * q :=
      add_le_add hsumBound (hLocal n hjn hn b hnt le_rfl)
    _ = A * (((n - j0 + 1 : ℕ) : ℝ) * τ) * q := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength hA) hq




theorem numericalL2_eq_affine (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) :
    (fun t => inclusionMap 0 1 (by norm_num) (globalInterpolation externalStep τ hτ f hfr hfm k t)) =
      (fun t => exactL2Path hT hu t - (1 : ℂ) • errorL2Path externalStep hT hτ f hfr hfm hu k t) := by
  funext t
  apply Sobolev.ext
  simp only [sobolev_val_sub, one_smul, errorL2Path, inclusionMap_val, exactL2Path,
    errorPath, sobolev_val_sub, exactTwistedOne]
  module

set_option maxHeartbeats 800000 in
/-- The restarted forcing estimate in (33), applied to the actual full
 unfiltered interpolation and its actual residual derivative. -/
theorem restarted_forcing_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          let R' := concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k
          let V := globalInterpolation externalStep τ hτ f hfr hfm k
          InSobolev 0 (fun m => ∫ t : ℝ in (j0 : ℝ) * τ..b, J t (R' t).val (V t).val m) ∧
          hNorm 0 (fun m => ∫ t : ℝ in (j0 : ℝ) * τ..b, J t (R' t).val (V t).val m) ≤
            C * (b - (j0 : ℝ) * τ + τ) * (τ ^ γ + E) := by
  obtain ⟨Ca, hCa, hAffine⟩ := restarted_affine_error_time_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cl, hCl, hLocal⟩ := local_residual_forcing_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  let B : ℝ := 1 + Ca + M
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by linarith
  refine ⟨Cl * B ^ 2, mul_pos hCl (sq_pos_of_pos (by linarith)), ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let V0 := fun t => inclusionMap 0 1 (by norm_num) (V t)
  let dV := fun t => exactNegativeDerivative hT.le hu t - (1 : ℂ) • errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k t
  let rn := numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm
  let F : ℕ → ℝ → Sobolev 0 := fun j t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t (rn j t) (V0 t))
  have hVC : Continuous V := continuous_globalInterpolation externalStep τ hτ f hfr hfm k
  have hFC (j : ℕ) : Continuous (F j) := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id (continuous_numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm j)
      ((inclusionMap 0 1 (by norm_num)).continuous.comp hVC))
  have hEqV := numericalL2_eq_affine externalStep hT.le hτ f hfr hfm hu k
  have hEqRaw : (fun t => (V0 t).val) =
      (fun t => (exactL2Path hT.le hu t - (1 : ℂ) • errorL2Path externalStep hT.le hτ f hfr hfm hu k t).val) :=
    congrArg (fun p : ℝ → Sobolev 0 => fun t => (p t).val) hEqV
  obtain ⟨hV, hdV, _⟩ := affine_error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu 1
    (mul_nonneg (Nat.cast_nonneg j0) hτ.le) hab hbT
  rw [← hEqV] at hV
  have hVX : timeXNorm a b V0 dV ≤ Ca := by
    have h := hAffine τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hbT hE hE1 he 1 (by norm_num)
    rwa [← hEqV] at h
  have hVB : ∀ t ∈ Set.Icc a b, hNorm 0 (V t).val ≤ B := by
    intro t ht
    have he0 := (errorPath externalStep hT.le hτ f hfr hfm hu k t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hv0 := (exactTwistedOne hT.le hu t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hvM : hNorm 0 (exactTwistedOne hT.le hu t).val ≤ M := by
      simpa only [sobolev_norm, exactL2Path, exactTwistedOne, inclusionMap_val] using
        exactL2Path_bound hT.le hγ.le (by linarith : γ ≤ 2) hu huM t
    have hn := hNorm_sub_le hv0 he0
    have heq : (exactTwistedOne hT.le hu t).val - (errorPath externalStep hT.le hτ f hfr hfm hu k t).val = (V t).val := by
      simp only [errorPath, sobolev_val_sub]; exact sub_sub_cancel _ _
    rw [heq] at hn
    have heb := he t ht
    dsimp [B]
    linarith
  have hlocal : ∀ j : ℕ, j0 ≤ j → j ≤ k → ∀ t : ℝ,
      t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) → t ≤ b →
      ‖∫ r : ℝ in (j : ℝ) * τ..t, F j r‖ ≤ (Cl * B ^ 2) * τ * (τ ^ γ + E) := by
    intro j hj0j hjk t ht htb
    have hSub : Set.Icc ((j : ℝ) * τ) t ⊆ Set.Icc a b := fun r hr =>
      ⟨(mul_le_mul_of_nonneg_right (by exact_mod_cast hj0j) hτ.le).trans hr.1, hr.2.trans htb⟩
    have hEnd : ((j + 1 : ℕ) : ℝ) * τ ≤ T :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal
    have htTotal : t ≤ ((k + 1 : ℕ) : ℝ) * τ := htb.trans hbT
    obtain ⟨_, _, hW⟩ := affine_error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu 1
      (mul_nonneg (Nat.cast_nonneg j) hτ.le) ht.1 htTotal
    rw [← hEqRaw] at hW
    have hXs : timeXNorm ((j : ℝ) * τ) t V0 dV ≤ B := by
      exact ((add_le_add (timeLInfinity_mono_interval hV hSub)
        (timeLInfinity_mono_interval hdV hSub)).trans hVX).trans (by dsimp [B]; linarith)
    obtain ⟨hw, hwm, hwM, hδ⟩ := frozen_comparison_bound externalStep hT.le hτ k j0 hTotal hbT
      (by linarith : γ ≤ 2) f hfr hfm hu huM he hj0j hjk (ht.1.trans htb)
    obtain ⟨hI, hIn⟩ := hLocal τ j hτ hτ1 hEnd (twistedNumericalBundled τ f j)
      (twistedNumericalBundled_real τ hfr j) (twistedNumericalBundled_meanZero τ hfm j)
      _ hw hwm hwM (hδ.trans hE1) t ht V hVC dV B hB
      (memLp_mono_interval hV hSub) (memLp_mono_interval hdV hSub) hW hXs
      (fun r hr => hVB r (hSub hr))
    have hval : (∫ r : ℝ in (j : ℝ) * τ..t, F j r).val =
        (fun m => ∫ r : ℝ in (j : ℝ) * τ..t,
          J r (localResidualDerivative τ ((j : ℝ) * τ) r (twistedNumericalBundled τ f j).val) (V r).val m) := by
      rw [sobolev_integral_val ((hFC j).intervalIntegrable _ _)]
      funext m
      apply intervalIntegral.integral_congr
      intro r _
      change J r (rn j r).val (V r).val m = _
      rw [numericalResidualDerivativeFamily_val]
    rw [sobolev_norm, hval]
    calc
      _ ≤ Cl * τ * (τ ^ γ + hNorm 0 ((twistedNumericalBundled τ f j).val - (extendedTwistedPath hT.le hu ((j : ℝ) * τ)).val)) * B ^ 2 := hIn
      _ ≤ Cl * τ * (τ ^ γ + E) * B ^ 2 := by gcongr
      _ = _ := by ring
  have hbnd := grid_integral_bound hτ F hFC hj0 hab hbT (mul_nonneg hCl.le (sq_nonneg B))
    (add_nonneg (Real.rpow_nonneg hτ.le γ) hE) hlocal
  have hi : IntervalIntegrable (concatenate τ F k) volume a b :=
    intervalIntegrable_concatenate τ F (fun j => (hFC j).intervalIntegrable a b) k
  have hval : (∫ t : ℝ in a..b, concatenate τ F k t).val =
      (fun m => ∫ t : ℝ in a..b, J t (concatenate τ rn k t).val (V t).val m) := by
    rw [sobolev_integral_val hi]
    funext m
    apply intervalIntegral.integral_congr
    intro t _
    have hmap : concatenate τ F k t = inclusionMap 0 1 (by norm_num)
        (JZeroBundled t (concatenate τ rn k t) (V0 t)) :=
      concatenate_map τ rn (fun r w => inclusionMap 0 1 (by norm_num) (JZeroBundled r w (V0 r))) k t
    dsimp only
    rw [hmap]
    rfl
  rw [← hval]
  exact ⟨(∫ t : ℝ in a..b, concatenate τ F k t).property, by rwa [← sobolev_norm]⟩



theorem cutoff_coefficient_integral (m : ℕ) (f : ℝ → Fourier) (a b : ℝ) :
    cutoff m (fun k => ∫ t : ℝ in a..b, f t k) =
      (fun k => ∫ t : ℝ in a..b, cutoff m (f t) k) := by
  funext k
  unfold cutoff
  split_ifs <;> simp

theorem integrated_B_low_bound {a b E G : ℝ} (hab : a ≤ b) (hE : 0 ≤ E) (_hG : 0 ≤ G)
    (f g : ℝ → Sobolev 1) (hf : Continuous f) (hg : Continuous g)
    (hfn : ∀ t ∈ Set.Icc a b, hNorm 0 (f t).val ≤ E)
    (hgn : ∀ t ∈ Set.Icc a b, hNorm 0 (g t).val ≤ G) (m : ℕ) :
    InSobolev 0 (cutoff m (fun k => ∫ t : ℝ in a..b, B t (f t).val (g t).val k)) ∧
    hNorm 0 (cutoff m (fun k => ∫ t : ℝ in a..b, B t (f t).val (g t).val k)) ≤
      (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * E * G * (b - a) := by
  let F := fun t => cutoffMap 0 m (BOneBundled t (f t) (g t))
  have hC : Continuous F := (cutoffMap 0 m).continuous.comp (continuous_BOneBundled continuous_id hf hg)
  have hK : 0 ≤ negativeProductConstant 1 (by norm_num) := norm_nonneg _
  have hbound : ∀ t ∈ Set.Icc a b, ‖F t‖ ≤ (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * E * G := by
    intro t ht
    rw [sobolev_norm]
    change hNorm 0 (cutoff m (B t (f t).val (g t).val)) ≤ _
    calc
      _ ≤ (1 + (m : ℝ) ^ 2) * negativeProductConstant 1 (by norm_num) * hNorm 0 (f t).val * hNorm 0 (g t).val :=
        B_low_bound ((f t).property.of_le (by norm_num)) ((g t).property.of_le (by norm_num)) t m
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hfn t ht) (by positivity)) (hgn t ht)
        (hNorm_nonneg _ _) (by positivity)
  have hb := coefficient_integral_bound hC hab hbound
  rwa [cutoff_coefficient_integral]

theorem hNorm_low_high_le {s : ℝ} {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    hNorm s f ≤ hNorm s (cutoff m f) + hNorm s (highCutoff m f) := by
  have hh := hNorm_add_le (cutoff_inSobolev hf m) (hf.sub (cutoff_inSobolev hf m))
  have heq : cutoff m f + (f - cutoff m f) = f := by abel
  rw [heq] at hh
  exact hh

theorem high_J_bound {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g) (t : ℝ) (m : ℕ) :
    InSobolev 0 (highCutoff m (J t f g)) ∧
    hNorm 0 (highCutoff m (J t f g)) ≤ weight (-1) (m : ℤ) * (4 * h1EmbeddingConstant * hNorm 0 f * hNorm 0 g) := by
  obtain ⟨hJ, hJn⟩ := J_h1_bound hf hg t
  obtain ⟨hm, hmn⟩ := high_cutoff_bound (s := 0) (by norm_num : (0 : ℝ) ≤ 1) hJ m
  refine ⟨hm, ?_⟩
  calc
    _ ≤ weight (0 - 1) (m : ℤ) * hNorm 1 (J t f g) := hmn
    _ ≤ _ := by norm_num only [zero_sub]; exact mul_le_mul_of_nonneg_left hJn (weight_pos _ _).le



theorem fin_three_prod_bound {x : Fin 3 → ℝ} {A B : ℝ} (i : Fin 3)
    (hx : ∀ j, 0 ≤ x j) (hi : x i ≤ A) (hothers : ∀ j, j ≠ i → x j ≤ B) :
    (∏ j : Fin 3, x j) ≤ A * B ^ 2 := by
  have hp : (∏ j : Fin 3, x j) ≤ ∏ j : Fin 3, if j = i then A else B := by
    apply Finset.prod_le_prod (fun j _ => hx j)
    intro j _
    split_ifs with h
    · subst j; exact hi
    · exact hothers j h
  have heq : (∏ j : Fin 3, if j = i then A else B) = A * B ^ 2 := by
    fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
  rwa [heq] at hp

/-- A specialization of (32) which preserves separate small error and error
 derivative norms. It leaves both terms needed for absorption explicit. -/
theorem high_output_small_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 1 →
      ∀ f : Fin 3 → ℝ → Sobolev 1, (∀ j, Continuous (f j)) →
      ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
        ∀ m : ℕ, ∀ i : Fin 3, ∀ A E B : ℝ,
        timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (f i t)) (df i) ≤ A →
        timeLInfinity a b (fun t => inclusionMap 0 1 (by norm_num) (f i t)) ≤ E →
        (∀ j, j ≠ i → timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (f j t)) (df j) ≤ B) →
        InSobolev 0 (highCutoff (3 * m) (pathCubic a b f)) ∧
        hNorm 0 (highCutoff (3 * m) (pathCubic a b f)) ≤
          C * (b - a) * A * B ^ 2 + C * weight (-pStar) (m : ℤ) * E * B ^ 2 := by
  obtain ⟨C, hC, hd⟩ := high_output_trilinear_bound externalTrilinear
  refine ⟨C, hC, ?_⟩
  intro a b ha hab hlen f hf df hdf hw m i A E B hXi hLi hX
  obtain ⟨hmem, hbound⟩ := hd a b ha hab hlen f hf df hdf hw m
  have hprodX := fin_three_prod_bound (x := fun j => timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (f j t)) (df j)) i (fun j => timeXNorm_nonneg a b _ _) hXi hX
  have hprodL := fin_three_prod_bound (x := fun j => timeLInfinity a b (fun t => inclusionMap 0 1 (by norm_num) (f j t))) i (fun j => timeLInfinity_nonneg a b _) hLi (fun j hj =>
    (le_add_of_nonneg_right (timeLInfinity_nonneg a b (df j))).trans (hX j hj))
  refine ⟨hmem, hbound.trans ?_⟩
  calc
    _ ≤ C * (b - a) * (A * B ^ 2) + C * weight (-pStar) (m : ℤ) * (E * B ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hprodX (mul_nonneg hC.le (sub_nonneg.mpr hab)))
        (mul_le_mul_of_nonneg_left hprodL (mul_nonneg hC.le (weight_pos _ _).le))
    _ = _ := by ring



section

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


end

section
set_option maxHeartbeats 800000

def errorCubicInputs (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ)
    (i : Fin 3) (z : Fin 3 → ℂ) (j : Fin 3) (t : ℝ) : Sobolev 1 :=
  if j = i then errorPath externalStep hT hτ f hfr hfm hu k t
  else affineErrorPath externalStep hT hτ f hfr hfm hu k (z j) t

/-- The two cubic terms in (31) are covered by choosing the error slot and
 the affine coefficients. The small error factor remains explicit. -/
theorem restarted_cubic_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          b - (j0 : ℝ) * τ ≤ 1 → 0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          ∀ m : ℕ, ∀ i : Fin 3, ∀ z : Fin 3 → ℂ, (∀ j, ‖z j‖ ≤ 1) →
          let F := errorCubicInputs externalStep hT.le hτ f hfr hfm hu k i z
          InSobolev 0 (highCutoff (3 * m) (pathCubic ((j0 : ℝ) * τ) b F)) ∧
          hNorm 0 (highCutoff (3 * m) (pathCubic ((j0 : ℝ) * τ) b F)) ≤
            C * ((b - (j0 : ℝ) * τ) * τ ^ γ +
              (b - (j0 : ℝ) * τ + weight (-pStar) (m : ℤ)) * E) := by
  obtain ⟨Ce, hCe, hError⟩ := restarted_error_time_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Ca, hCa, hAffine⟩ := restarted_affine_error_time_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cp, hCp, hHigh⟩ := high_output_small_bound externalTrilinear
  refine ⟨Cp * (Ce + 1) * Ca ^ 2, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m i z hz
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let q := τ ^ γ + E
  let F := errorCubicInputs externalStep hT.le hτ f hfr hfm hu k i z
  let D : Fin 3 → ℝ → Sobolev (-pStar) := fun j => if j = i then
    errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k else
    affineNegativeDerivative externalStep hT.le hτ f hfr hfm hu k (z j)
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
  obtain ⟨he0, hde, hwe⟩ := error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu ha hab hb
  have hxa := hError τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he
  have haff (j : Fin 3) := affine_input_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu (z j) ha hab hb
  have hFC (j : Fin 3) : Continuous (F j) := by
    change Continuous (fun t => if j = i then errorPath externalStep hT.le hτ f hfr hfm hu k t
      else affineErrorPath externalStep hT.le hτ f hfr hfm hu k (z j) t)
    by_cases hj : j = i
    · simp only [if_pos hj]
      exact continuous_errorPath externalStep hT.le hτ f hfr hfm hu k
    · simp only [if_neg hj]
      exact continuous_affineErrorPath externalStep hT.le hτ f hfr hfm hu k (z j)
  have hDm (j : Fin 3) : MemLp (D j) ∞ (volume.restrict (Set.Icc a b)) := by
    dsimp [D]
    split_ifs
    · exact hde
    · exact (haff j).2.1
  have hW (j : Fin 3) : WeakTimeDerivative a b (fun t => (F j t).val) (fun t => (D j t).val) := by
    by_cases hj : j = i
    · simpa only [F, D, errorCubicInputs, hj, if_pos rfl, ↓reduceIte, errorL2Path, inclusionMap_val] using hwe
    · simpa only [F, D, errorCubicInputs, if_neg hj, affineL2Path, inclusionMap_val] using (haff j).2.2
  have hXi : timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (F i t)) (D i) ≤ Ce * q := by
    simp only [F, D, errorCubicInputs, if_pos rfl, ite_true]
    exact hxa
  have hLi : timeLInfinity a b (fun t => inclusionMap 0 1 (by norm_num) (F i t)) ≤ E := by
    apply timeLInfinity_le_of_bound hE
    intro t ht
    rw [sobolev_norm]
    simpa only [F, errorCubicInputs, if_pos rfl, ite_true, inclusionMap_val] using he t ht
  have hX (j : Fin 3) (hj : j ≠ i) : timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (F j t)) (D j) ≤ Ca := by
    simp only [F, D, errorCubicInputs, if_neg hj]
    change timeXNorm a b (affineL2Path externalStep hT.le hτ f hfr hfm hu k (z j))
      (affineNegativeDerivative externalStep hT.le hτ f hfr hfm hu k (z j)) ≤ Ca
    rw [affineL2Path_eq]
    exact hAffine τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he (z j) (hz j)
  obtain ⟨hmem, hn⟩ := hHigh a b ha hab hlen F hFC D hDm hW m i (Ce * q) E Ca hXi hLi hX
  refine ⟨hmem, hn.trans ?_⟩
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hweight := (weight_pos (-pStar) (m : ℤ)).le
  dsimp [q]
  apply sub_nonneg.mp
  calc
    _ = Cp * Ca ^ 2 * ((b - a) * τ ^ γ + (b - a) * E + Ce * weight (-pStar) (m : ℤ) * E) := by ring
    _ ≥ 0 := by positivity


end

section

theorem highCutoff_smul (m : ℕ) (z : ℂ) (f : Fourier) : highCutoff m (z • f) = z • highCutoff m f := by
  unfold highCutoff
  rw [cutoff_smul]
  module

theorem hNorm_normal_form_sum {s : ℝ} {A B C D : Fourier}
    (hA : InSobolev s A) (hB : InSobolev s B) (hC : InSobolev s C) (hD : InSobolev s D) :
    InSobolev s ((1 / 3 : ℂ) • A - (1 / 3 : ℂ) • B - (1 / 6 : ℂ) • C + (1 / 3 : ℂ) • D) ∧
    hNorm s ((1 / 3 : ℂ) • A - (1 / 3 : ℂ) • B - (1 / 6 : ℂ) • C + (1 / 3 : ℂ) • D) ≤
      hNorm s A + hNorm s B + hNorm s C + hNorm s D := by
  have hAB := (hA.smul (1 / 3 : ℂ)).sub (hB.smul (1 / 3 : ℂ))
  have hABC := hAB.sub (hC.smul (1 / 6 : ℂ))
  refine ⟨hABC.add (hD.smul _), ?_⟩
  have h1 := hNorm_sub_le (hA.smul (1 / 3 : ℂ)) (hB.smul (1 / 3 : ℂ))
  have h2 := hNorm_sub_le hAB (hC.smul (1 / 6 : ℂ))
  have h3 := hNorm_add_le hABC (hD.smul (1 / 3 : ℂ))
  rw [hNorm_smul hA, hNorm_smul hB] at h1
  rw [hNorm_smul hC] at h2
  rw [hNorm_smul hD] at h3
  norm_num only [norm_div, norm_one, Complex.norm_ofNat] at h1 h2 h3
  linarith [hNorm_nonneg s A, hNorm_nonneg s B, hNorm_nonneg s C, hNorm_nonneg s D]

/-- High-output consequence of the retained-endpoint normal form. Only the
 explicit cubic terms and residual forcing remain to be estimated. -/
theorem normal_form_high_bound {F Jb Ja C₁ C₂ I : Fourier} (m : ℕ)
    (hJb : InSobolev 1 Jb) (hJa : InSobolev 1 Ja)
    (hC₁ : InSobolev 0 (highCutoff m C₁)) (hC₂ : InSobolev 0 (highCutoff m C₂)) (hI : InSobolev 0 I)
    (hNF : F = (1 / 3 : ℂ) • (Jb - Ja) - (1 / 3 : ℂ) • C₁ - (1 / 6 : ℂ) • C₂ + (1 / 3 : ℂ) • I) :
    InSobolev 0 (highCutoff m F) ∧
    hNorm 0 (highCutoff m F) ≤ weight (-1) (m : ℤ) * (hNorm 1 Jb + hNorm 1 Ja) +
      hNorm 0 (highCutoff m C₁) + hNorm 0 (highCutoff m C₂) + hNorm 0 I := by
  have hDiff := hJb.sub hJa
  obtain ⟨hA, hAn⟩ := high_cutoff_bound (s := 0) (by norm_num : (0 : ℝ) ≤ 1) hDiff m
  have hD : InSobolev 0 (highCutoff m I) := hI.sub (cutoff_inSobolev hI m)
  have hlin := hNorm_normal_form_sum hA hC₁ hC₂ hD
  have heq : highCutoff m F = (1 / 3 : ℂ) • highCutoff m (Jb - Ja) -
      (1 / 3 : ℂ) • highCutoff m C₁ - (1 / 6 : ℂ) • highCutoff m C₂ + (1 / 3 : ℂ) • highCutoff m I := by
    rw [hNF, highCutoff_add, highCutoff_sub, highCutoff_sub, highCutoff_smul, highCutoff_smul,
      highCutoff_smul, highCutoff_smul]
  rw [heq]
  refine ⟨hlin.1, hlin.2.trans ?_⟩
  have hAb : hNorm 0 (highCutoff m (Jb - Ja)) ≤ weight (-1) (m : ℤ) * (hNorm 1 Jb + hNorm 1 Ja) := by
    calc
      _ ≤ weight (0 - 1) (m : ℤ) * hNorm 1 (Jb - Ja) := hAn
      _ ≤ _ := by norm_num only [zero_sub]; exact mul_le_mul_of_nonneg_left (hNorm_sub_le hJb hJa) (weight_pos _ _).le
  exact add_le_add (add_le_add (add_le_add hAb le_rfl) le_rfl) (highCutoff_hNorm_le hI m)


end

section
set_option maxHeartbeats 800000

theorem affine_error_pointwise_bound (externalStep : LiWuStepIdentity) {T τ γ M E : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (_hE : 0 ≤ E)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u)
    (huM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) (k : ℕ) (t : ℝ)
    (he : hNorm 0 (errorPath externalStep hT hτ f hfr hfm hu k t).val ≤ E)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    hNorm 0 (affineErrorPath externalStep hT hτ f hfr hfm hu k z t).val ≤ M + E := by
  have hv := (exactTwistedOne hT hu t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have he0 := (errorPath externalStep hT hτ f hfr hfm hu k t).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hvM : hNorm 0 (exactTwistedOne hT hu t).val ≤ M := by
    simpa only [sobolev_norm, exactL2Path, exactTwistedOne, inclusionMap_val] using
      exactL2Path_bound hT hγ hγ2 hu huM t
  have hn := hNorm_sub_le hv (he0.smul z)
  rw [hNorm_smul he0] at hn
  exact hn.trans (add_le_add hvM (calc
    _ ≤ 1 * E := mul_le_mul hz he (hNorm_nonneg _ _) (by norm_num)
    _ = _ := one_mul _))

theorem pathCubic_error_first (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (a b : ℝ) :
    pathCubic a b (errorCubicInputs externalStep hT hτ f hfr hfm hu k 0 ![0,1/2,1]) =
      CIntegral a b (fun t => (errorPath externalStep hT hτ f hfr hfm hu k t).val)
        (fun t => (errorMidpoint externalStep hT hτ f hfr hfm hu k t).val)
        (fun t => (globalInterpolation externalStep τ hτ f hfr hfm k t).val) := by
  simp only [pathCubic, errorCubicInputs]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [ite_true, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, ite_false]
  simp only [affineErrorPath_half, affineErrorPath_one]

theorem pathCubic_error_last (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (a b : ℝ) :
    pathCubic a b (errorCubicInputs externalStep hT hτ f hfr hfm hu k 2 (fun _ => 0)) =
      CIntegral a b (fun t => (exactTwistedOne hT hu t).val) (fun t => (exactTwistedOne hT hu t).val)
        (fun t => (errorPath externalStep hT hτ f hfr hfm hu k t).val) := by
  simp only [pathCubic, errorCubicInputs]
  simp [affineErrorPath]

theorem combine_stability_scalar {h τ x E N l j c r wt wp : ℝ}
    (hh : 0 ≤ h) (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hE : 0 ≤ E) (hN : 1 ≤ N)
    (hl : 0 ≤ l) (hj : 0 ≤ j) (hc : 0 ≤ c) (hr : 0 ≤ r) (hwt : 0 ≤ wt) (hwp : 0 ≤ wp) :
    N * l * E * h + wt * (2 * j * E) + 2 * c * (h * x + (h + wp) * E) + r * (h + τ) * (x + E) ≤
      (1 + l + 2 * j + 2 * c + r) * ((h + τ) * x + (N * h + τ + wt + wp) * E) := by
  apply sub_nonneg.mp
  have hNm : 0 ≤ N - 1 := sub_nonneg.mpr hN
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  calc
    _ = (1 + l + 2 * j) * h * x + (1 + l + 2 * j + 2 * c) * τ * x +
        (N * (1 + 2 * j) + (N - 1) * (2 * c + r)) * h * E +
        (1 + l + 2 * j + 2 * c) * τ * E +
        (1 + l + 2 * c + r) * wt * E + (1 + l + 2 * j + r) * wp * E := by ring
    _ ≥ 0 := by positivity

/-- Bound on the nonlinear integral in the actual error equation, before
 choosing the proof frequency threshold and the restarted interval length. -/
theorem restarted_error_integral_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          b - (j0 : ℝ) * τ ≤ 1 → 0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          ∀ m : ℕ,
          let e := errorPath externalStep hT.le hτ f hfr hfm hu k
          let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
          let I := fun l => ∫ t : ℝ in (j0 : ℝ) * τ..b, B t (e t).val (g t).val l
          InSobolev 0 I ∧ hNorm 0 I ≤ C * ((b - (j0 : ℝ) * τ + τ) * τ ^ γ +
            ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - (j0 : ℝ) * τ) + τ +
              weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E) := by
  obtain ⟨Cc, hCc, hCubic⟩ := restarted_cubic_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cf, hCf, hForcing⟩ := restarted_forcing_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  let Kl := negativeProductConstant 1 (by norm_num)
  let Kj := 4 * h1EmbeddingConstant
  have hKl : 0 ≤ Kl := norm_nonneg _
  have hKj : 0 ≤ Kj := by dsimp [Kj]; have h := h1EmbeddingConstant_ge_one; positivity
  let G := M + 1
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let C := 1 + Kl * G + 2 * Kj * G + 2 * Cc + Cf
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  let v := exactTwistedOne hT.le hu
  let V := globalInterpolation externalStep τ hτ f hfr hfm k
  let FI := fun l => ∫ t : ℝ in a..b, B t (e t).val (g t).val l
  let C₁ := CIntegral a b (fun t => (e t).val) (fun t => (g t).val) (fun t => (V t).val)
  let C₂ := CIntegral a b (fun t => (v t).val) (fun t => (v t).val) (fun t => (e t).val)
  let RI := fun l => ∫ t : ℝ in a..b,
    J t (concatenate τ (numericalResidualDerivativeFamily externalStep τ hτ f hfr hfm) k t).val (V t).val l
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
  have heC : Continuous e := continuous_errorPath externalStep hT.le hτ f hfr hfm hu k
  have hgC : Continuous g := continuous_errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  have hgB : ∀ t ∈ Set.Icc a b, hNorm 0 (g t).val ≤ G := by
    intro t ht
    exact (affine_error_pointwise_bound externalStep hT.le hτ hγ.le (by linarith : γ ≤ 2) hE f hfr hfm hu huM k t (he t ht)
      (1 / 2) (by norm_num)).trans (by dsimp [G]; linarith)
  have hFI : InSobolev 0 FI := by
    have hi : IntervalIntegrable (fun t => BOneBundled t (e t) (g t)) volume a b :=
      (continuous_BOneBundled continuous_id heC hgC).intervalIntegrable a b
    rw [show FI = (∫ t : ℝ in a..b, BOneBundled t (e t) (g t)).val from (sobolev_integral_val hi).symm]
    exact (∫ t : ℝ in a..b, BOneBundled t (e t) (g t)).property
  have hLow := (integrated_B_low_bound hab hE hG e g heC hgC he hgB (3 * m)).2
  obtain ⟨hC₁, hC₁n⟩ := hCubic τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m 0 ![0,1/2,1]
    (by intro j; fin_cases j <;> norm_num)
  rw [pathCubic_error_first] at hC₁ hC₁n
  obtain ⟨hC₂, hC₂n⟩ := hCubic τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m 2 (fun _ => 0)
    (by intro j; norm_num)
  rw [pathCubic_error_last] at hC₂ hC₂n
  obtain ⟨hRI, hRIn⟩ := hForcing τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he
  have hNF : FI = (1 / 3 : ℂ) • (J b (e b).val (g b).val - J a (e a).val (g a).val) -
      (1 / 3 : ℂ) • C₁ - (1 / 6 : ℂ) • C₂ + (1 / 3 : ℂ) • RI := by
    funext l
    exact actual_error_normal_form externalStep hT.le hτ k hTotal f hfr hfm hu ha hab hb l
  obtain ⟨hJb, hJbn⟩ := J_h1_bound ((e b).property.of_le (by norm_num)) ((g b).property.of_le (by norm_num)) b
  obtain ⟨hJa, hJan⟩ := J_h1_bound ((e a).property.of_le (by norm_num)) ((g a).property.of_le (by norm_num)) a
  have hEnd : hNorm 1 (J b (e b).val (g b).val) + hNorm 1 (J a (e a).val (g a).val) ≤ 2 * Kj * E * G := by
    have hbE := he b ⟨hab, le_rfl⟩
    have haE := he a ⟨le_rfl, hab⟩
    have hbG := hgB b ⟨hab, le_rfl⟩
    have haG := hgB a ⟨le_rfl, hab⟩
    have hbj : hNorm 1 (J b (e b).val (g b).val) ≤ Kj * E * G := hJbn.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hbE hKj) hbG (hNorm_nonneg _ _) (mul_nonneg hKj hE))
    have haj : hNorm 1 (J a (e a).val (g a).val) ≤ Kj * E * G := hJan.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left haE hKj) haG (hNorm_nonneg _ _) (mul_nonneg hKj hE))
    linarith
  have hHigh := (normal_form_high_bound (3 * m) hJb hJa hC₁ hC₂ hRI hNF).2
  refine ⟨hFI, (hNorm_low_high_le hFI (3 * m)).trans ?_⟩
  have hwt : 0 ≤ weight (-1) (3 * m : ℤ) := (weight_pos _ _).le
  have hwp : 0 ≤ weight (-pStar) (m : ℤ) := (weight_pos _ _).le
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hHigh' : hNorm 0 (highCutoff (3 * m) FI) ≤ weight (-1) (3 * m : ℤ) * (2 * Kj * E * G) +
      2 * Cc * ((b - a) * τ ^ γ + (b - a + weight (-pStar) (m : ℤ)) * E) +
      Cf * (b - a + τ) * (τ ^ γ + E) := by
    have hh := hHigh.trans (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hEnd (weight_pos _ _).le) hC₁n) hC₂n) hRIn)
    convert! hh using 1; (try simp only [Nat.cast_mul, Nat.cast_ofNat]); (try dsimp only [a]); ring
  calc
    _ ≤ (1 + ((3 * m : ℕ) : ℝ) ^ 2) * Kl * E * G * (b - a) +
      (weight (-1) (3 * m : ℤ) * (2 * Kj * E * G) +
      2 * Cc * ((b - a) * τ ^ γ + (b - a + weight (-pStar) (m : ℤ)) * E) +
      Cf * (b - a + τ) * (τ ^ γ + E)) := add_le_add hLow hHigh'
    _ ≤ C * ((b - a + τ) * τ ^ γ +
      ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - a) + τ + weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E) := by
      have hs := combine_stability_scalar (h := b - a) (τ := τ) (x := τ ^ γ) (E := E)
        (N := 1 + ((3 * m : ℕ) : ℝ) ^ 2) (l := Kl * G) (j := Kj * G) (c := Cc) (r := Cf)
        (wt := weight (-1) (3 * m : ℤ)) (wp := weight (-pStar) (m : ℤ))
        hlen0 hτ.le hτγ hE (by nlinarith [sq_nonneg (((3 * m : ℕ) : ℝ))])
        (mul_nonneg hKl hG) (mul_nonneg hKj hG) hCc.le hCf.le hwt hwp
      dsimp only [C]
      convert! hs using 1 <;> ring



end

section
set_option maxHeartbeats 800000

/-- The pointwise restarted inequality before choosing proof parameters or
 discharging the temporary bootstrap hypothesis. -/
theorem restarted_error_inequality (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          b - (j0 : ℝ) * τ ≤ 1 → 0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          ∀ m : ℕ,
          let e := errorPath externalStep hT.le hτ f hfr hfm hu k
          hNorm 0 (e b).val ≤ hNorm 0 (e ((j0 : ℝ) * τ)).val +
            C * ((b - (j0 : ℝ) * τ + τ) * τ ^ γ +
            ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - (j0 : ℝ) * τ) + τ +
              weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E) := by
  obtain ⟨Ci, hCi, hInt⟩ := restarted_error_integral_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cr, hCr, hRes⟩ := restarted_residual_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  refine ⟨Ci + Cr, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let g := errorMidpoint externalStep hT.le hτ f hfr hfm hu k
  let R := globalResidual externalStep τ hτ f hfr hfm k
  let FI := fun l => ∫ t : ℝ in a..b, B t (e t).val (g t).val l
  let Z : ℝ := (b - a + τ) * τ ^ γ +
    ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - a) + τ + weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) * E
  obtain ⟨hFI, hFIn⟩ := hInt τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m
  have hRn := hRes τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he b ⟨hab, le_rfl⟩
  have hRI : InSobolev 0 ((R b).val - (R a).val) := (R b).property.sub (R a).property
  have hRnorm : hNorm 0 ((R b).val - (R a).val) ≤ Cr * (b - a + τ) * (τ ^ γ + E) := by
    simpa only [sobolev_norm, sobolev_val_sub] using hRn
  have hCoeff : b - a + τ ≤ (1 + ((3 * m : ℕ) : ℝ) ^ 2) * (b - a) + τ +
      weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ) := by
    have hh : 0 ≤ b - a := sub_nonneg.mpr hab
    have h1 := (weight_pos (-1) (3 * m : ℤ)).le
    have h2 := (weight_pos (-pStar) (m : ℤ)).le
    nlinarith [mul_nonneg (sq_nonneg (((3 * m : ℕ) : ℝ))) hh]
  have hRZ : hNorm 0 ((R b).val - (R a).val) ≤ Cr * Z := hRnorm.trans (calc
    _ = Cr * ((b - a + τ) * τ ^ γ + (b - a + τ) * E) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCoeff hE)) hCr.le)
  have hEq : (e b).val = (e a).val + FI - ((R b).val - (R a).val) :=
    actual_error_integral_identity externalStep hT.le hτ k hTotal f hfr hfm hu
      (mul_nonneg (Nat.cast_nonneg _) hτ.le) hab hb
  rw [hEq]
  have hea := (e a).property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ ≤ hNorm 0 ((e a).val + FI) + hNorm 0 ((R b).val - (R a).val) := hNorm_sub_le (hea.add hFI) hRI
    _ ≤ (hNorm 0 (e a).val + hNorm 0 FI) + hNorm 0 ((R b).val - (R a).val) :=
      add_le_add (hNorm_add_le hea hFI) le_rfl
    _ ≤ (hNorm 0 (e a).val + Ci * Z) + Cr * Z := add_le_add (add_le_add le_rfl hFIn) hRZ
    _ = _ := by dsimp [Z]; ring


end

section

theorem weight_negative_le_inverse_index {p : ℝ} (hp : 1 ≤ p) {m : ℕ} (hm : 0 < m) :
    weight (-p) (m : ℤ) ≤ (m : ℝ)⁻¹ := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    _ ≤ weight (-1) (m : ℤ) := weight_mono (by linarith) _
    _ = (weight 1 (m : ℤ))⁻¹ := weight_neg 1 _
    _ ≤ _ := inv_anti₀ hmR (by simpa only [Int.cast_natCast, abs_of_pos hmR] using weight_one_ge_abs (m : ℤ))

/-- The proof frequency threshold and restarted interval length are chosen
 before the numerical data, grid and bootstrap interval. -/
theorem absorption_parameters {C : ℝ} (hC : 0 < C) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ h τ : ℝ, 0 ≤ h → h ≤ δ → 0 ≤ τ → τ ≤ δ →
        C * ((1 + ((3 * m : ℕ) : ℝ) ^ 2) * h + τ +
          weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) ≤ 1 / 4 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 : ℝ) (16 * C))
  have hm1 : 1 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmC : 16 * C < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hmR : 0 < (m : ℝ) := by positivity
  let N : ℝ := 1 + ((3 * m : ℕ) : ℝ) ^ 2
  have hN : 1 ≤ N := by dsimp [N]; nlinarith [sq_nonneg (((3 * m : ℕ) : ℝ))]
  have hN0 : 0 ≤ N := by linarith
  let δ : ℝ := min 1 (1 / (8 * C * (N + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδn : δ ≤ 1 / (8 * C * (N + 1)) := min_le_right _ _
  have hw1 : weight (-1) (3 * m : ℤ) ≤ (m : ℝ)⁻¹ := by
    have hwm := weight_negative_le_inverse_index (p := 1) le_rfl (m := 3 * m) (by omega)
    have hc : (3 * m : ℤ) = ((3 * m : ℕ) : ℤ) := by push_cast; rfl
    rw [hc]
    exact hwm.trans (inv_anti₀ hmR (by push_cast; nlinarith))
  have hwp : weight (-pStar) (m : ℤ) ≤ (m : ℝ)⁻¹ := weight_negative_le_inverse_index (by norm_num [pStar]) hm0
  have hwC : C * (weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) ≤ 1 / 8 := by
    calc
      _ ≤ C * (2 * (m : ℝ)⁻¹) := mul_le_mul_of_nonneg_left (by linarith) hC.le
      _ = (2 * C) / (m : ℝ) := by ring
      _ ≤ 1 / 8 := (div_le_iff₀ hmR).mpr (by nlinarith)
  refine ⟨m, hm0, δ, hδ, hδ1, ?_⟩
  intro h τ hh hhδ hτ hτδ
  have hδC : C * (N + 1) * δ ≤ 1 / 8 := by
    have hd : 0 < 8 * C * (N + 1) := by positivity
    have hx := (le_div_iff₀ hd).mp hδn
    nlinarith
  have hhτ : C * (N * h + τ) ≤ 1 / 8 := by
    calc
      _ ≤ C * ((N + 1) * δ) := mul_le_mul_of_nonneg_left (by nlinarith) hC.le
      _ = C * (N + 1) * δ := by ring
      _ ≤ _ := hδC
  change C * (N * h + τ + weight (-1) (3 * m : ℤ) + weight (-pStar) (m : ℤ)) ≤ _
  linarith


end

section
set_option maxHeartbeats 800000

theorem exists_hNorm_maximum {a b : ℝ} (hab : a ≤ b) (f : ℝ → Sobolev 1) (hf : Continuous f) :
    ∃ E : ℝ, 0 ≤ E ∧ (∀ t ∈ Set.Icc a b, hNorm 0 (f t).val ≤ E) ∧
      ∃ t ∈ Set.Icc a b, hNorm 0 (f t).val = E := by
  have hc : Continuous (fun t => ‖inclusionMap 0 1 (by norm_num) (f t)‖) :=
    ((inclusionMap 0 1 (by norm_num)).continuous.comp hf).norm
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab⟩ hc.continuousOn
  refine ⟨hNorm 0 (f t).val, hNorm_nonneg _ _, ?_, t, ht, rfl⟩
  intro r hr
  have hh := hmax hr
  change ‖inclusionMap 0 1 (by norm_num) (f r)‖ ≤ ‖inclusionMap 0 1 (by norm_num) (f t)‖ at hh
  simpa only [sobolev_norm, inclusionMap_val] using hh

/-- The restarted stability estimate (35), after an internal maximum and
 absorption argument. The remaining unit bootstrap is explicit and will be
 discharged by continuity in the global estimate. -/
theorem restarted_stability_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧
      ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ δ → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          b - (j0 : ℝ) * τ ≤ δ →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ 1) →
          ∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤
              2 * hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k ((j0 : ℝ) * τ)).val + K * τ ^ γ := by
  obtain ⟨C, hC, hEst⟩ := restarted_error_inequality externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨m, _, δ, hδ, hδ1, hAbs⟩ := absorption_parameters hC
  refine ⟨δ, 4 * C * δ, hδ, hδ1, by positivity, ?_⟩
  intro τ hτ hτδ k hTotal f hfr hfm u hu huM j0 hj0 b hab hb hlen hUnit t ht
  let a : ℝ := (j0 : ℝ) * τ
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  obtain ⟨E, hE, hEbound, s, hs, hsE⟩ := exists_hNorm_maximum hab e
    (continuous_errorPath externalStep hT.le hτ f hfr hfm hu k)
  have hE1 : E ≤ 1 := hsE ▸ hUnit s hs
  have hSub : Set.Icc a s ⊆ Set.Icc a b := fun r hr => ⟨hr.1, hr.2.trans hs.2⟩
  have hslen : s - a ≤ δ := by linarith [hs.2]
  have hI := hEst τ hτ (hτδ.trans hδ1) k hTotal f hfr hfm u hu huM j0 hj0 s E hs.1
    (hs.2.trans hb) (hslen.trans hδ1) hE hE1 (fun r hr => hEbound r (hSub hr)) m
  change hNorm 0 (e s).val ≤ hNorm 0 (e a).val + _ at hI
  rw [hsE] at hI
  have hCoeff := hAbs (s - a) τ (sub_nonneg.mpr hs.1) hslen hτ.le hτδ
  have hStep : s - a + τ ≤ 2 * δ := by linarith
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hTime := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hStep hτγ) hC.le
  have hCoefE := mul_le_mul_of_nonneg_right hCoeff hE
  have hA : 0 ≤ hNorm 0 (e a).val := hNorm_nonneg _ _
  have hEB : E ≤ 2 * hNorm 0 (e a).val + (4 * C * δ) * τ ^ γ := by nlinarith
  exact (hEbound t ht).trans hEB


end


section

/-- A genuine first-crossing argument discharges a temporary unit bound.
 The conclusion on each prefix is an actual hypothesis to be instantiated
 by the internally proved restarted stability estimate. -/
theorem continuity_unit_bootstrap {a b D : ℝ} (_hab : a ≤ b)
    (q : ℝ → ℝ) (hq : Continuous q) (hqa : q a < 1) (hD : D < 1)
    (hLocal : ∀ c ∈ Set.Icc a b, (∀ r ∈ Set.Icc a c, q r ≤ 1) → q c ≤ D) :
    ∀ t ∈ Set.Icc a b, q t ≤ D := by
  have hUnit : ∀ t ∈ Set.Icc a b, q t ≤ 1 := by
    by_contra hbad
    push Not at hbad
    obtain ⟨r, hr, hqr⟩ := hbad
    obtain ⟨s, hs, hqs⟩ := intermediate_value_Icc hr.1 hq.continuousOn ⟨hqa.le, hqr.le⟩
    let S : Set ℝ := Set.Icc a b ∩ {t | q t = 1}
    have hScompact : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hq continuous_const)
    have hSnonempty : S.Nonempty := ⟨s, ⟨hs.1, hs.2.trans hr.2⟩, hqs⟩
    obtain ⟨c, hc, hmin⟩ := hScompact.exists_isMinOn hSnonempty continuous_id.continuousOn
    have hcI : c ∈ Set.Icc a b := hc.1
    have hqc : q c = 1 := hc.2
    have hPrefix : ∀ x ∈ Set.Icc a c, q x ≤ 1 := by
      intro x hx
      by_contra hqx
      have hqx' : 1 < q x := lt_of_not_ge hqx
      obtain ⟨y, hy, hqy⟩ := intermediate_value_Icc hx.1 hq.continuousOn ⟨hqa.le, hqx'.le⟩
      have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans (hx.2.trans hcI.2)⟩, hqy⟩
      have hcy : c ≤ y := hmin hyS
      have hyx : y < x := lt_of_le_of_ne hy.2 (by intro h; rw [h] at hqy; linarith)
      linarith [hx.2]
    have hcD := hLocal c hcI hPrefix
    linarith
  intro t ht
  exact hLocal t ht (fun r hr => hUnit r ⟨hr.1, hr.2.trans ht.2⟩)


end

section

/-- Quantitative induction on a fixed number of blocks. The local hypothesis
 is an internal scalar interface, instantiated later by restarted stability. -/
theorem grid_block_bootstrap {τ δ K x : ℝ} {N B J : ℕ}
    (hτ : 0 < τ) (hStep : (J : ℝ) * τ ≤ δ) (hK : 0 ≤ K) (hx : 0 ≤ x)
    (hCover : N ≤ B * J) (hSmall : K * ((2 : ℝ) ^ B - 1) * x < 1)
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hLocal : ∀ j : ℕ, j < N → ∀ c : ℝ,
      (j : ℝ) * τ ≤ c → c ≤ (N : ℝ) * τ → c - (j : ℝ) * τ ≤ δ →
      (∀ r ∈ Set.Icc ((j : ℝ) * τ) c, q r ≤ 1) →
        q c ≤ 2 * q ((j : ℝ) * τ) + K * x) :
    ∀ t ∈ Set.Icc 0 ((N : ℝ) * τ), q t ≤ K * ((2 : ℝ) ^ B - 1) * x := by
  let D : ℕ → ℝ := fun n => K * ((2 : ℝ) ^ n - 1) * x
  have hD0 (n : ℕ) : 0 ≤ D n := by
    have hp : 0 ≤ (2 : ℝ) ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact mul_nonneg (mul_nonneg hK hp) hx
  have hDmono : Monotone D := by
    intro n m hnm
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnm) 1) hK) hx
  have hDsucc (n : ℕ) : D (n + 1) = 2 * D n + K * x := by dsimp [D]; rw [pow_succ]; ring
  have hAll : ∀ n : ℕ, n ≤ B → ∀ t ∈ Set.Icc 0 (((min (n * J) N : ℕ) : ℝ) * τ), q t ≤ D n := by
    intro n
    induction n with
    | zero =>
      intro _ t ht
      simp only [Nat.zero_min, Nat.cast_zero, zero_mul] at ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simpa only [hq0, D, pow_zero, sub_self, mul_zero, zero_mul] using (le_refl (0 : ℝ))
    | succ n ih =>
      intro hn t ht
      have hnB : n ≤ B := (Nat.le_succ n).trans hn
      have hdn : D n ≤ D (n + 1) := hDmono (Nat.le_succ _)
      by_cases hdone : N ≤ n * J
      · have hdone' : N ≤ (n + 1) * J := hdone.trans (Nat.mul_le_mul_right J (Nat.le_succ n))
        rw [Nat.min_eq_right hdone'] at ht
        exact (ih hnB t (by rwa [Nat.min_eq_right hdone])).trans hdn
      · have hj : n * J < N := lt_of_not_ge hdone
        let a : ℝ := ((n * J : ℕ) : ℝ) * τ
        let b : ℝ := ((min ((n + 1) * J) N : ℕ) : ℝ) * τ
        have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
        have hab : a ≤ b := mul_le_mul_of_nonneg_right (by
          exact_mod_cast (le_min (Nat.mul_le_mul_right J (Nat.le_succ n)) hj.le)) hτ.le
        have hbN : b ≤ (N : ℝ) * τ := mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right ((n + 1) * J) N) hτ.le
        have hbStep : b - a ≤ δ := by
          have hbJ : b ≤ (((n + 1) * J : ℕ) : ℝ) * τ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left ((n + 1) * J) N) hτ.le
          have heq : (((n + 1) * J : ℕ) : ℝ) * τ = a + (J : ℝ) * τ := by dsimp [a]; push_cast; ring
          rw [heq] at hbJ
          linarith
        have hStart : q a ≤ D n := ih hnB a (by rw [Nat.min_eq_left hj.le]; exact ⟨ha0, le_rfl⟩)
        have hqa : q a < 1 := hStart.trans_lt ((hDmono hnB).trans_lt hSmall)
        have hNext : D (n + 1) < 1 := (hDmono hn).trans_lt hSmall
        have hBlock : ∀ r ∈ Set.Icc a b, q r ≤ D (n + 1) := by
          apply continuity_unit_bootstrap hab q hq hqa hNext
          intro c hc hUnit
          have hcStep : c - a ≤ δ := by linarith [hc.2]
          have h := hLocal (n * J) hj c hc.1 (hc.2.trans hbN) hcStep hUnit
          rw [hDsucc]
          linarith
        by_cases hta : t ≤ a
        · exact (ih hnB t (by rw [Nat.min_eq_left hj.le]; exact ⟨ht.1, hta⟩)).trans hdn
        · exact hBlock t ⟨le_of_not_ge hta, ht.2⟩
  have hFinal := hAll B le_rfl
  rw [Nat.min_eq_right hCover] at hFinal
  exact hFinal


end

section

theorem small_rpow_threshold {γ C A : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hA : 0 < A) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ τ0 ≤ A ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → C * τ ^ γ ≤ 1 / 2 := by
  let r : ℝ := (1 / (2 * C)) ^ γ⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min A r, lt_min hA hr, min_le_left _ _, ?_⟩
  intro τ hτ hτ0
  have hτr : τ ≤ r := hτ0.trans (min_le_right _ _)
  have hp : τ ^ γ ≤ 1 / (2 * C) := by
    have h := Real.rpow_le_rpow hτ.le hτr hγ.le
    rwa [Real.rpow_inv_rpow (by positivity : 0 ≤ 1 / (2 * C)) hγ.ne'] at h
  calc
    _ ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hp hC.le
    _ = _ := by field_simp

/-- A fixed number of blocks covers every grid. Integer division chooses
 only the block length; no cutoff or modification of the method is involved. -/
theorem uniform_grid_blocks {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ L : ℕ, 0 < L → ∀ τ : ℝ, τ = T / (L : ℝ) → τ ≤ δ / 2 →
      L ≤ B * (L / B + 1) ∧ ((L / B + 1 : ℕ) : ℝ) * τ ≤ δ := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (1 : ℝ) (2 * T / δ))
  have hB1 : 1 < (B : ℝ) := (le_max_left _ _).trans_lt hB
  have hBR : 0 < (B : ℝ) := by linarith
  have hBN : 0 < B := by exact_mod_cast hBR
  have hBT : 2 * T / δ < (B : ℝ) := (le_max_right _ _).trans_lt hB
  have hTdivB : T / (B : ℝ) ≤ δ / 2 := by
    apply (div_le_iff₀ hBR).mpr
    have h := (div_lt_iff₀ hδ).mp hBT
    nlinarith
  refine ⟨B, hBN, ?_⟩
  intro L hL τ hτ hτδ
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hτpos : 0 < τ := hτ ▸ div_pos hT hLR
  have hCover : L ≤ B * (L / B + 1) := by
    have hrem := Nat.mod_lt L hBN
    have heq := Nat.div_add_mod L B
    nlinarith
  have hfloor : ((L / B : ℕ) : ℝ) ≤ (L : ℝ) / (B : ℝ) := by
    apply (le_div_iff₀ hBR).mpr
    exact_mod_cast Nat.div_mul_le_self L B
  refine ⟨hCover, ?_⟩
  calc
    _ = ((L / B : ℕ) : ℝ) * τ + τ := by push_cast; ring
    _ ≤ ((L : ℝ) / (B : ℝ)) * τ + τ := add_le_add (mul_le_mul_of_nonneg_right hfloor hτpos.le) le_rfl
    _ = T / (B : ℝ) + τ := by rw [hτ]; field_simp
    _ ≤ δ := by linarith


end

section
set_option maxHeartbeats 800000

/-- Uniform convergence for auxiliary `H²` flows. Its constants use only the
 common `H^γ` bound; the `H²` norm is absent. This is the input to density. -/
theorem uniform_h2_convergence (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ u : ℝ → Fourier, KdVSolution 2 T f.val u →
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ L : ℕ, 0 < L → T / (L : ℝ) ≤ τ0 →
          maximumError T L f.val u ≤ C * (T / (L : ℝ)) ^ γ := by
  obtain ⟨δ, K, hδ, _, hK, hStab⟩ := restarted_stability_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨B, _, hBlocks⟩ := uniform_grid_blocks hT hδ
  let C : ℝ := 1 + K * (2 : ℝ) ^ B
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨τ0, hτ0, hτ0δ, hSmall⟩ := small_rpow_threshold hγ hC (half_pos hδ)
  refine ⟨C, hC, τ0, hτ0, ?_⟩
  intro f hfr hfm u hu huM L hL hτsmall
  let τ : ℝ := T / (L : ℝ)
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hτ : 0 < τ := div_pos hT hLR
  have hτδ2 : τ ≤ δ / 2 := hτsmall.trans hτ0δ
  have hτδ : τ ≤ δ := hτδ2.trans (by linarith)
  have hLT : (L : ℝ) * τ = T := by dsimp [τ]; field_simp
  let k := L - 1
  have hKL : k + 1 = L := by dsimp [k]; omega
  have hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T := by rw [hKL, hLT]
  let J := L / B + 1
  obtain ⟨hCover, hStep⟩ := hBlocks L hL τ rfl hτδ2
  let e := errorPath externalStep hT.le hτ f hfr hfm hu k
  let q : ℝ → ℝ := fun t => hNorm 0 (e t).val
  have hqC : Continuous q := by
    have h := (((inclusionMap 0 1 (by norm_num)).continuous.comp
      (continuous_errorPath externalStep hT.le hτ f hfr hfm hu k)).norm)
    simpa only [sobolev_norm, inclusionMap_val, Function.comp_def] using h
  have hq0 : q 0 = 0 := by
    simp only [q, e, errorPath, sobolev_val_sub, exactTwistedOne, inclusionMap_val,
      extendedTwistedPath_zero, globalInterpolation_zero, sub_self, hNorm_zero]
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hCoeff : K * ((2 : ℝ) ^ B - 1) ≤ C := by dsimp [C]; nlinarith
  have hSmall' : K * ((2 : ℝ) ^ B - 1) * τ ^ γ < 1 := by
    calc
      _ ≤ C * τ ^ γ := mul_le_mul_of_nonneg_right hCoeff hτγ
      _ ≤ 1 / 2 := hSmall τ hτ hτsmall
      _ < _ := by norm_num
  have hLocal : ∀ j : ℕ, j < L → ∀ c : ℝ,
      (j : ℝ) * τ ≤ c → c ≤ (L : ℝ) * τ → c - (j : ℝ) * τ ≤ δ →
      (∀ r ∈ Set.Icc ((j : ℝ) * τ) c, q r ≤ 1) → q c ≤ 2 * q ((j : ℝ) * τ) + K * τ ^ γ := by
    intro j hj c hac hc hlen hUnit
    have hjk : j ≤ k := by dsimp [k]; omega
    have hcT : c ≤ ((k + 1 : ℕ) : ℝ) * τ := by rwa [hKL]
    exact hStab τ hτ hτδ k hTotal f hfr hfm u hu huM j hjk c hac hcT hlen hUnit c ⟨hac, le_rfl⟩
  have hGlobal := grid_block_bootstrap (N := L) (B := B) (J := J) hτ hStep hK.le hτγ hCover hSmall' q hqC hq0 hLocal
  unfold maximumError
  apply Finset.sup'_le
  intro j hj
  have hjL : j ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have ht : (j : ℝ) * τ ∈ Set.Icc 0 ((L : ℝ) * τ) :=
    ⟨mul_nonneg (Nat.cast_nonneg _) hτ.le, mul_le_mul_of_nonneg_right (by exact_mod_cast hjL) hτ.le⟩
  have hjk : j ≤ k + 1 := by rwa [hKL]
  have hGrid := actual_error_grid_norm externalStep hT.le hτ k hTotal f hfr hfm hu hjk
  change hNorm 0 (e ((j : ℝ) * τ)).val = _ at hGrid
  rw [← hGrid]
  exact (hGlobal _ ht).trans (mul_le_mul_of_nonneg_right hCoeff hτγ)


end


section

theorem positive_kdv_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    {f : Fourier} (hf : InSobolev s f) (hfr : RealValued f) (hfm : MeanZero f) :
    ∃ u : ℝ → Fourier, KdVSolution s T f u := by
  obtain ⟨A, _, hExists⟩ := uniform_source_flow_exists externalGalerkin externalLimit externalHigh externalLow
    hs hT (show 0 < hNorm s f + 1 by linarith [hNorm_nonneg s f])
  have hfh := homogeneous_reflectSign (hf.to_homogeneous hs.le hfm)
  have hfn : homogeneousNorm s (reflectSign f) ≤ hNorm s f + 1 := by
    rw [homogeneousNorm_reflectSign]
    exact (homogeneousNorm_le_hNorm hs.le hf hfm).trans (by linarith)
  obtain ⟨v, _, hw, hc, _⟩ := hExists (reflectSign f) (reflectSign_real hfr) hfh hfn
  have hu := source_solution_to_kdv hs.le hfh hw.1 hc (fun t ht => (hw.2.1 t ht).1)
  rw [reflectSign_involutive] at hu
  exact ⟨_, hu⟩


end

section
set_option maxHeartbeats 1000000

theorem numerical_cutoff_converges {f : Fourier} (hf : InSobolev 0 f) (τ : ℝ) (n : ℕ) :
    Filter.Tendsto (fun m : ℕ => hNorm 0 (numerical τ (cutoff m f) n - numerical τ f n))
      Filter.atTop (nhds 0) := by
  let F : Sobolev 0 := ⟨f, hf⟩
  have h := ((continuous_numericalBundled τ n).continuousAt.tendsto.comp (approximation_converges F))
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [sobolev_norm, sobolev_val_sub, numericalBundled_val, approximation, Function.comp_def] using h

/-- Density is performed at each fixed positive timestep, using the proved
 full-method `L²` continuity and the source flow's uniform `L²` dependence.
 The constants are selected before the rough datum and the number of steps. -/
theorem uniform_rough_convergence (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    (externalGalerkin : BITGalerkinEstimate) (externalLimit : BITExistenceLimit)
    (externalHigh : BITHigherRegularity) (externalLow : BITLowRegularity)
    (externalLipschitz : BITWeakerLipschitz)
    {T γ R : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ f : Fourier, InSobolev γ f → RealValued f → MeanZero f → hNorm γ f ≤ R →
      ∀ u : ℝ → Fourier, KdVSolution γ T f u →
        ∀ L : ℕ, 0 < L → T / (L : ℝ) ≤ τ0 →
          maximumError T L f u ≤ C * (T / (L : ℝ)) ^ γ := by
  obtain ⟨M, hM, hFlow⟩ := uniform_kdv_flow_bound externalGalerkin externalLimit externalHigh externalLow hγ hT hR
  obtain ⟨C, hC, τ0, hτ0, hConv⟩ := uniform_h2_convergence externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM.le
  obtain ⟨Cd, hCd, hDep⟩ := kdv_flow_l2_lipschitz externalLipschitz (show 0 ≤ 2 * R by positivity) hT
  refine ⟨C, hC, τ0, hτ0, ?_⟩
  intro f hf hfr hfm hfR u hu L hL hτ0bound
  let τ : ℝ := T / (L : ℝ)
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hτ : 0 < τ := div_pos hT hLR
  have hLT : (L : ℝ) * τ = T := by dsimp [τ]; field_simp
  have hf0 := hf.of_le hγ.le
  have hf0R : hNorm 0 f ≤ R := (hNorm_mono hf hγ.le).trans hfR
  let fm : ℕ → Sobolev 2 := fun m => ⟨cutoff m f, cutoff_inSobolev_all 2 m f⟩
  have hfmR (m : ℕ) : RealValued (fm m).val := cutoff_real hfr m
  have hfmM (m : ℕ) : MeanZero (fm m).val := cutoff_meanZero hfm m
  have hfmγ (m : ℕ) : InSobolev γ (fm m).val := cutoff_inSobolev hf m
  have hfmBound (m : ℕ) : hNorm γ (fm m).val ≤ R := (cutoff_hNorm_le hf m).trans hfR
  have hex (m : ℕ) : ∃ v : ℝ → Fourier, KdVSolution 2 T (fm m).val v :=
    positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow (by norm_num) hT
      (fm m).property (hfmR m) (hfmM m)
  choose vm hvm using hex
  have hvmγ (m : ℕ) : KdVSolution γ T (fm m).val (vm m) :=
    ⟨(hvm m).1.of_le (by linarith : γ ≤ 2), (hvm m).2⟩
  have hvmBound (m : ℕ) : ∀ t ∈ Set.Icc 0 T, hNorm γ (vm m t) ≤ M :=
    hFlow (fm m).val (hfmR m) (hfmM m) (hfmγ m) (hfmBound m) (vm m) (hvmγ m)
  have hConvM (m : ℕ) := hConv (fm m) (hfmR m) (hfmM m) (vm m) (hvm m) (hvmBound m) L hL hτ0bound
  have hData := cutoff_converges hf0
  unfold maximumError
  apply Finset.sup'_le
  intro n hn
  have hnL : n ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have ht : (n : ℝ) * τ ∈ Set.Icc 0 T := ⟨mul_nonneg (Nat.cast_nonneg _) hτ.le,
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hnL) hτ.le).trans_eq hLT⟩
  have hNum := numerical_cutoff_converges hf0 τ n
  have hLimit : Filter.Tendsto (fun m : ℕ => Cd * hNorm 0 (cutoff m f - f) + C * τ ^ γ +
      hNorm 0 (numerical τ (cutoff m f) n - numerical τ f n)) Filter.atTop (nhds (C * τ ^ γ)) := by
    have h := (((tendsto_const_nhds (x := Cd)).mul hData).add_const (C * τ ^ γ)).add hNum
    simpa only [mul_zero, zero_add, add_zero] using h
  apply ge_of_tendsto hLimit
  apply Filter.Eventually.of_forall
  intro m
  have hL2 : hNorm 0 (fm m).val + hNorm 0 f ≤ 2 * R := by
    have hb := (cutoff_hNorm_le hf0 m).trans hf0R
    change hNorm 0 (cutoff m f) + hNorm 0 f ≤ _
    linarith
  have hExact := hDep 2 γ (by norm_num) hγ.le (fm m).val f (hfmR m) (hfmM m) (fm m).property
    hfr hfm hf hL2 (vm m) u (hvm m) hu _ ht
  have hErr : hNorm 0 (vm m ((n : ℝ) * τ) - numerical τ (fm m).val n) ≤ C * τ ^ γ := by
    have h := Finset.le_sup' (fun j : ℕ => hNorm 0 (vm m ((j : ℝ) * τ) - numerical τ (fm m).val j)) hn
    exact h.trans (hConvM m)
  have hu0 := (hu.1.1 _ ht).of_le hγ.le
  have hm0 := ((hvm m).1.1 _ ht).of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hn0 := numerical_inSobolev (γ := 0) le_rfl (by norm_num) τ ((fm m).property.of_le (by norm_num)) n
  have hnf0 := numerical_inSobolev (γ := 0) le_rfl (by norm_num) τ hf0 n
  have hSplit : u ((n : ℝ) * τ) - numerical τ f n =
      (u ((n : ℝ) * τ) - vm m ((n : ℝ) * τ)) +
      (vm m ((n : ℝ) * τ) - numerical τ (fm m).val n) +
      (numerical τ (fm m).val n - numerical τ f n) := by abel
  have hSymm : hNorm 0 (u ((n : ℝ) * τ) - vm m ((n : ℝ) * τ)) ≤ Cd * hNorm 0 (cutoff m f - f) := by
    rw [hNorm_sub_symm]
    exact hExact
  rw [hSplit]
  exact (hNorm_add_le ((hu0.sub hm0).add (hm0.sub hn0)) (hn0.sub hnf0)).trans
    ((add_le_add (hNorm_add_le (hu0.sub hm0) (hm0.sub hn0)) le_rfl).trans
      (add_le_add (add_le_add hSymm hErr) le_rfl))


end

section

theorem kdv_solution_unique (externalLipschitz : BITWeakerLipschitz)
    {s r T : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hT : 0 < T)
    {f : Fourier} (hf : InSobolev s f) (hfr : RealValued f) (hfm : MeanZero f)
    {u v : ℝ → Fourier} (hu : KdVSolution s T f u) (hv : KdVSolution r T f v) :
    ∀ t ∈ Set.Icc 0 T, u t = v t := by
  have hf0 := hf.of_le hs
  have hfr0 : InSobolev r f := by
    have hh := hv.1.1 0 ⟨le_rfl, hT.le⟩
    rwa [hv.2.1.1] at hh
  obtain ⟨C, _, hDep⟩ := kdv_flow_l2_lipschitz externalLipschitz
    (show 0 ≤ 2 * hNorm 0 f by exact mul_nonneg (by norm_num) (hNorm_nonneg _ _)) hT
  intro t ht
  have hn := hDep s r hs hr f f hfr hfm hf hfr hfm hfr0 (by linarith) u v hu hv t ht
  rw [sub_self, hNorm_zero, mul_zero] at hn
  have hmem := ((hu.1.1 t ht).of_le hs).sub ((hv.1.1 t ht).of_le hr)
  funext k
  have hk := weighted_coeff_bound hmem k
  rw [weighted_zero] at hk
  have hkn : ‖(u t - v t) k‖ = 0 := le_antisymm (hk.trans hn) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hkn)

theorem SobolevContinuousOn.congr_on {s T : ℝ} {u v : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) (heq : ∀ t ∈ Set.Icc 0 T, u t = v t) :
    SobolevContinuousOn s T v := by
  refine ⟨fun t ht => heq t ht ▸ hu.1 t ht, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  simpa only [← heq r hr, ← heq t ht] using hb r hr hrt

/-- The cited positive-regularity flow, with smooth data, has every spatial
 Sobolev regularity. No higher regularity is imposed as an external premise. -/
theorem all_sobolev_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {T : ℝ} (hT : 0 < T) {f : Fourier} (hf : ∀ s : ℝ, InSobolev s f)
    (hfr : RealValued f) (hfm : MeanZero f) :
    ∃ u : ℝ → Fourier, Duhamel T f u ∧ (∀ s : ℝ, SobolevContinuousOn s T u) ∧
      ∀ t ∈ Set.Icc 0 T, RealValued (u t) ∧ MeanZero (u t) := by
  obtain ⟨u, hu⟩ := positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow
    (s := 2) (by norm_num) hT (hf 2) hfr hfm
  refine ⟨u, hu.2.1, ?_, hu.2.2⟩
  intro s
  let q : ℝ := max 2 (s + 1)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hsq : s ≤ q := (by linarith : s ≤ s + 1).trans (le_max_right _ _)
  obtain ⟨v, hv⟩ := positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow hq hT (hf q) hfr hfm
  have heq := kdv_solution_unique externalLipschitz hq.le (by norm_num : (0 : ℝ) ≤ 2) hT (hf q) hfr hfm hv hu
  exact (hv.1.of_le hsq).congr_on heq


end

section
set_option maxHeartbeats 800000

theorem integer_product_bound (n : ℕ) {f g : Fourier}
    (hf : InSobolev ((n + 1 : ℕ) : ℝ) f) (hg : InSobolev ((n + 1 : ℕ) : ℝ) g) :
    hNorm ((n + 1 : ℕ) : ℝ) (product f g) ≤
      ((3 : ℝ) ^ n * (2 * h1EmbeddingConstant)) * hNorm ((n + 1 : ℕ) : ℝ) f * hNorm ((n + 1 : ℕ) : ℝ) g := by
  induction n generalizing f g with
  | zero => simpa using (h1_product_bound (by simpa using hf) (by simpa using hg)).2
  | succ n ih =>
    let s : ℝ := ((n + 1 : ℕ) : ℝ)
    let K : ℝ := (3 : ℝ) ^ n * (2 * h1EmbeddingConstant)
    have hK : 0 ≤ K := by dsimp [K]; have hh := h1EmbeddingConstant_ge_one; positivity
    have hs1 : 1 ≤ s := by dsimp [s]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hfp : InSobolev (s + 1) f := by simpa only [s, Nat.cast_add, Nat.cast_one] using hf
    have hgp : InSobolev (s + 1) g := by simpa only [s, Nat.cast_add, Nat.cast_one] using hg
    obtain ⟨hfl, hfd⟩ := inSobolev_succ_iff.mp hfp
    obtain ⟨hgl, hgd⟩ := inSobolev_succ_iff.mp hgp
    have hf1 := hfl.of_le hs1
    have hg1 := hgl.of_le hs1
    have hp := integer_product_inSobolev n hfl hgl
    have hd1 := integer_product_inSobolev n hfd hgl
    have hd2 := integer_product_inSobolev n hfl hgd
    have hdp : InSobolev s (derivative (product f g)) := by
      rw [derivative_product hf1 hg1]
      exact hd1.add hd2
    have hl := ih hfl hgl
    have hd1n := ih hfd hgl
    have hd2n := ih hfl hgd
    have hfpn := derivative_hNorm hfp
    have hgpn := derivative_hNorm hgp
    have hfln := hNorm_mono hfp (by linarith : s ≤ s + 1)
    have hgln := hNorm_mono hgp (by linarith : s ≤ s + 1)
    have hfnon := hNorm_nonneg (s + 1) f
    have hgnon := hNorm_nonneg (s + 1) g
    have hln : hNorm s (product f g) ≤ K * hNorm (s + 1) f * hNorm (s + 1) g := hl.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hfln hK) hgln (hNorm_nonneg _ _) (mul_nonneg hK hfnon))
    have hd1n' : hNorm s (product (derivative f) g) ≤ K * hNorm (s + 1) f * hNorm (s + 1) g := hd1n.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hfpn hK) hgln (hNorm_nonneg _ _) (mul_nonneg hK hfnon))
    have hd2n' : hNorm s (product f (derivative g)) ≤ K * hNorm (s + 1) f * hNorm (s + 1) g := hd2n.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hfln hK) hgpn (hNorm_nonneg _ _) (mul_nonneg hK hfnon))
    have hd : hNorm s (derivative (product f g)) ≤ 2 * K * hNorm (s + 1) f * hNorm (s + 1) g := by
      rw [derivative_product hf1 hg1]
      exact (hNorm_add_le hd1 hd2).trans (by linarith)
    have hn := (sobolev_succ_bound hp hdp).2
    have hsBound : hNorm (s + 1) (product f g) ≤ 3 * K * hNorm (s + 1) f * hNorm (s + 1) g := by linarith
    simpa only [s, K, Nat.cast_add, Nat.cast_one, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hsBound


end

section

def productIntegerBilinear (n : ℕ) : Sobolev ((n + 1 : ℕ) : ℝ) →ₗ[ℂ]
    Sobolev ((n + 1 : ℕ) : ℝ) →ₗ[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) where
  toFun f := {
    toFun g := ⟨product f.val g.val, integer_product_inSobolev n f.property g.property⟩
    map_add' g h := by
      apply Sobolev.ext
      exact product_add_right (f.property.of_le (by positivity)) (g.property.of_le (by positivity)) (h.property.of_le (by positivity))
    map_smul' z g := by apply Sobolev.ext; exact product_smul_right z f.val g.val }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Sobolev.ext
    exact product_add_left (f.property.of_le (by positivity)) (g.property.of_le (by positivity)) (h.property.of_le (by positivity))
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply Sobolev.ext
    exact product_smul_left z f.val g.val

def productIntegerMap (n : ℕ) : Sobolev ((n + 1 : ℕ) : ℝ) →L[ℂ]
    Sobolev ((n + 1 : ℕ) : ℝ) →L[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) :=
  (productIntegerBilinear n).mkContinuous₂ ((3 : ℝ) ^ n * (2 * h1EmbeddingConstant))
    (fun f g => by simp only [sobolev_norm]; exact integer_product_bound n f.property g.property)

theorem productIntegerMap_val (n : ℕ) (f g : Sobolev ((n + 1 : ℕ) : ℝ)) :
    (productIntegerMap n f g).val = product f.val g.val := rfl

theorem continuous_productIntegerMap {X : Type*} [TopologicalSpace X] (n : ℕ)
    {f g : X → Sobolev ((n + 1 : ℕ) : ℝ)} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => productIntegerMap n (f t) (g t)) := by
  exact ((productIntegerMap n).continuous.comp hf).clm_apply hg


end

section

def physicalRHS (f : Fourier) : Fourier :=
  -derivative (derivative (derivative f)) + (1 / 2 : ℂ) • derivative (product f f)

theorem nat_order_succ (n : ℕ) : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring

def derivativeNatLinear (n : ℕ) : Sobolev ((n + 2 : ℕ) : ℝ) →ₗ[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := ((n + 1 : ℕ) : ℝ)) (by
    rw [nat_order_succ]
    exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeNatMap (n : ℕ) : Sobolev ((n + 2 : ℕ) : ℝ) →L[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) :=
  (derivativeNatLinear n).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    have hf : InSobolev (((n + 1 : ℕ) : ℝ) + 1) f.val := by
      rw [nat_order_succ]
      exact f.property
    have hn := derivative_hNorm hf
    rw [nat_order_succ] at hn
    exact hn)

theorem derivativeNatMap_val (n : ℕ) (f : Sobolev ((n + 2 : ℕ) : ℝ)) :
    (derivativeNatMap n f).val = derivative f.val := rfl

def thirdDerivativeNatMap (n : ℕ) : Sobolev ((n + 4 : ℕ) : ℝ) →L[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) :=
  (derivativeNatMap n).comp ((derivativeNatMap (n + 1)).comp (derivativeNatMap (n + 2)))

def physicalVectorField (n : ℕ) (f : Sobolev ((n + 4 : ℕ) : ℝ)) : Sobolev ((n + 1 : ℕ) : ℝ) :=
  -thirdDerivativeNatMap n f + (1 / 2 : ℂ) • derivativeNatMap n
    (productIntegerMap (n + 1)
      (inclusionMap ((n + 2 : ℕ) : ℝ) ((n + 4 : ℕ) : ℝ) (by push_cast; linarith) f)
      (inclusionMap ((n + 2 : ℕ) : ℝ) ((n + 4 : ℕ) : ℝ) (by push_cast; linarith) f))

theorem physicalVectorField_val (n : ℕ) (f : Sobolev ((n + 4 : ℕ) : ℝ)) :
    (physicalVectorField n f).val = physicalRHS f.val := rfl

theorem continuous_physicalVectorField (n : ℕ) : Continuous (physicalVectorField n) := by
  unfold physicalVectorField
  exact (thirdDerivativeNatMap n).continuous.neg.add
    ((continuous_const (y := (1 / 2 : ℂ))).smul ((derivativeNatMap n).continuous.comp
      (continuous_productIntegerMap (n + 1) (inclusionMap _ _ _).continuous (inclusionMap _ _ _).continuous)))


end

section

theorem contDiff_physicalVectorField (n m : ℕ) : ContDiff ℝ m (physicalVectorField n) := by
  let A := inclusionMap ((n + 2 : ℕ) : ℝ) ((n + 4 : ℕ) : ℝ) (by push_cast; linarith)
  have hA : ContDiff ℝ m A := (A.restrictScalars ℝ).contDiff
  have hP : ContDiff ℝ m (fun f => productIntegerMap (n + 1) (A f) (A f)) :=
    (((productIntegerMap (n + 1)).bilinearRestrictScalars ℝ).contDiff.comp hA).clm_apply hA
  have hD := ((derivativeNatMap n).restrictScalars ℝ).contDiff.comp hP
  have hL : ContDiff ℝ m (thirdDerivativeNatMap n) := ((thirdDerivativeNatMap n).restrictScalars ℝ).contDiff
  exact hL.neg.add ((contDiff_const (c := (1 / 2 : ℂ))).smul hD)


end

section

/-- Actual differentiation of the physical (untwisted) equation, derived
 from Duhamel rather than assumed as regularity of the exact solution. -/
theorem physical_coefficient_hasDerivAt {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T f u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => u r k)
      (Complex.I * (k : ℂ) ^ 3 * u t k + (1 / 2 : ℂ) * (Complex.I * (k : ℂ)) * product (u t) (u t) k) t := by
  let v := extendedTwistedPath hT hu
  let E := fun r : ℝ => Complex.exp (Complex.I * (r : ℂ) * (k : ℂ) ^ 3)
  have hdv := extendedTwistedPath_hasDerivAt hT hu ht k
  have hdE : HasDerivAt E ((Complex.I * (k : ℂ) ^ 3) * E t) t := by
    have h := ((((hasDerivAt_id t).ofReal_comp).const_mul Complex.I).mul_const ((k : ℂ) ^ 3)).cexp
    simpa only [E, id_eq, Complex.ofReal_one, mul_one, mul_comm] using h
  have hd := hdE.mul hdv
  have hEq : (fun r : ℝ => E r * (v r).val k) =ᶠ[nhds t] (fun r : ℝ => u r k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    change airy r (v r).val k = u r k
    rw [extendedTwistedPath_val_on hT hu hr, airy_inverse_neg]
  have hB : E t * B t (v t).val (v t).val k = (Complex.I * (k : ℂ)) * product (u t) (u t) k := by
    change airy t (B t (v t).val (v t).val) k = _
    rw [B, airy_inverse_neg, extendedTwistedPath_val_on hT hu ⟨ht.1.le, ht.2.le⟩, airy_inverse_neg]
    rfl
  have hU : E t * (v t).val k = u t k := hEq.self_of_nhds
  have hD : (exactTwistedDerivative hT hu t).val k = (1 / 2 : ℂ) * B t (v t).val (v t).val k := by
    rw [exactTwistedDerivative_equation]
    rfl
  apply (hd.congr_of_eventuallyEq hEq.symm).congr_deriv
  rw [hD]
  linear_combination (Complex.I * (k : ℂ) ^ 3) * hU + (1 / 2 : ℂ) * hB


end

section
set_option maxHeartbeats 800000

theorem sobolev_val_add {s : ℝ} (f g : Sobolev s) : (f + g).val = f.val + g.val := rfl

theorem physicalRHS_coefficient (f : Fourier) (k : ℤ) :
    physicalRHS f k = Complex.I * (k : ℂ) ^ 3 * f k +
      (1 / 2 : ℂ) * (Complex.I * (k : ℂ)) * product f f k := by
  simp only [physicalRHS, derivative, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_pow_three]
  ring

def spatialPath {T : ℝ} {u : ℝ → Fourier} (hT : 0 ≤ T)
    (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) (n : ℕ) : ℝ → Sobolev ((n + 1 : ℕ) : ℝ) :=
  sobolevExtension hT u (hAll ((n + 1 : ℕ) : ℝ))

theorem continuous_spatialPath {T : ℝ} {u : ℝ → Fourier} (hT : 0 ≤ T)
    (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) (n : ℕ) : Continuous (spatialPath hT hAll n) :=
  continuous_sobolevExtension hT _

theorem spatialPath_val_on {T : ℝ} {u : ℝ → Fourier} (hT : 0 ≤ T)
    (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (spatialPath hT hAll n t).val = u t := sobolevExtension_val_on hT _ ht

/-- The coefficient Duhamel equation is an actual Bochner integral equation
 in every positive integer Sobolev space for an all-regularity flow. -/
theorem spatial_physical_integral {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    spatialPath hT hAll n t = spatialPath hT hAll n 0 +
      ∫ r : ℝ in (0 : ℝ)..t, physicalVectorField n (spatialPath hT hAll (n + 3) r) := by
  let U := spatialPath hT hAll n
  let F := fun r => physicalVectorField n (spatialPath hT hAll (n + 3) r)
  have hUC : Continuous U := continuous_spatialPath hT hAll n
  have hFC : Continuous F := (continuous_physicalVectorField n).comp (continuous_spatialPath hT hAll (n + 3))
  have hi : IntervalIntegrable F volume 0 t := hFC.intervalIntegrable 0 t
  apply Sobolev.ext
  rw [sobolev_val_add, sobolev_integral_val hi]
  funext k
  have hcU : ContinuousOn (fun r : ℝ => u r k) (Set.Icc 0 t) := by
    apply (((coefficientMap ((n + 1 : ℕ) : ℝ) k).continuous.comp hUC).continuousOn).congr
    intro r hr
    change u r k = (U r).val k
    rw [spatialPath_val_on hT hAll n ⟨hr.1, hr.2.trans ht.2⟩]
  have hcF : Continuous (fun r : ℝ => (F r).val k) :=
    (coefficientMap ((n + 1 : ℕ) : ℝ) k).continuous.comp hFC
  have hd : ∀ r ∈ Set.Ioo 0 t, HasDerivAt (fun s : ℝ => u s k) ((F r).val k) r := by
    intro r hr
    have hrT : r ∈ Set.Ioo 0 T := ⟨hr.1, hr.2.trans_le ht.2⟩
    have h := physical_coefficient_hasDerivAt hT hu hrT k
    have hfVal : (F r).val = physicalRHS (u r) := by
      rw [physicalVectorField_val, spatialPath_val_on hT hAll (n + 3) ⟨hrT.1.le, hrT.2.le⟩]
    rwa [hfVal, physicalRHS_coefficient]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcU hd (hcF.intervalIntegrable 0 t)
  change (spatialPath hT hAll n t).val k = (spatialPath hT hAll n 0).val k + ∫ r : ℝ in (0 : ℝ)..t, (F r).val k
  rw [spatialPath_val_on hT hAll n ht, spatialPath_val_on hT hAll n ⟨le_rfl, hT⟩, hFTC]
  ring


end

section
set_option maxHeartbeats 800000

theorem spatial_hasDerivWithinAt {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (spatialPath hT hAll n)
      (physicalVectorField n (spatialPath hT hAll (n + 3) t)) (Set.Icc 0 T) t := by
  let F := fun r => physicalVectorField n (spatialPath hT hAll (n + 3) r)
  have hc : Continuous F := (continuous_physicalVectorField n).comp (continuous_spatialPath hT hAll (n + 3))
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hG := (hasDerivAt_const t (spatialPath hT hAll n 0)).add hd
  simp only [zero_add] at hG
  exact hG.hasDerivWithinAt.congr_of_mem (fun r hr => spatial_physical_integral hT hu hAll n hr) ht

/-- Infinite spatial Sobolev regularity and the actual autonomous KdV equation
 imply all time derivatives, including one-sided boundary regularity. -/
theorem all_regular_coefficient_contDiffOn {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 < T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) :
    ∀ k : ℤ, ∀ m : ℕ, ContDiffOn ℝ m (fun t => u t k) (Set.Icc 0 T) := by
  have hD (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) := spatial_hasDerivWithinAt hT.le hu hAll n ht
  have hSmooth : ∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ m (spatialPath hT.le hAll n) (Set.Icc 0 T) := by
    intro m
    induction m with
    | zero =>
      intro n
      exact contDiffOn_zero.mpr (continuous_spatialPath hT.le hAll n).continuousOn
    | succ m ih =>
      intro n
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
      refine ⟨fun t ht => (hD n t ht).differentiableWithinAt, by simp, ?_⟩
      have hF := (contDiff_physicalVectorField n m).comp_contDiffOn (ih (n + 3))
      apply hF.congr
      intro t ht
      exact (hD n t ht).derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
  intro k m
  have h := ((coefficientMap (((0 + 1 : ℕ) : ℝ)) k).restrictScalars ℝ).contDiff.comp_contDiffOn (hSmooth m 0)
  apply h.congr
  intro t ht
  change u t k = (spatialPath hT.le hAll 0 t).val k
  rw [spatialPath_val_on hT.le hAll 0 ht]

theorem all_regular_is_smooth {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 < T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) :
    SmoothSolution T f u :=
  ⟨hu.2.1, hAll, all_regular_coefficient_contDiffOn hT hu hAll, hu.2.2⟩


end

section

theorem smooth_kdv_flow_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {T : ℝ} (hT : 0 < T) {f : Fourier} (hf : ∀ s : ℝ, InSobolev s f)
    (hfr : RealValued f) (hfm : MeanZero f) :
    ∃ u : ℝ → Fourier, SmoothSolution T f u := by
  obtain ⟨u, hd, hc, hr⟩ := all_sobolev_flow_exists externalGalerkin externalLimit externalHigh externalLow externalLipschitz hT hf hfr hfm
  exact ⟨u, all_regular_is_smooth hT ⟨hc 2, hd, hr⟩ hc⟩

/-- Every positive Sobolev Duhamel solution is the limit of actual smooth
 KdV solutions, in precisely the topology specified in the supplied paper. -/
theorem kdv_solution_smooth_approximation (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier} (hf : InSobolev γ f)
    (hfr : RealValued f) (hfm : MeanZero f) {u : ℝ → Fourier} (hu : KdVSolution γ T f u) :
    ObtainedBySmoothApproximation γ T f u := by
  have hf0 := hf.of_le hγ.le
  have hex (m : ℕ) : ∃ v : ℝ → Fourier, SmoothSolution T (cutoff m f) v :=
    smooth_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow externalLipschitz hT
      (fun s => cutoff_inSobolev_all s m f) (cutoff_real hfr m) (cutoff_meanZero hfm m)
  choose v hv using hex
  refine ⟨fun m => cutoff m f, v, hv, cutoff_converges hf, ?_⟩
  obtain ⟨C, hC, hDep⟩ := kdv_flow_l2_lipschitz externalLipschitz
    (show 0 ≤ 2 * hNorm 0 f from mul_nonneg (by norm_num) (hNorm_nonneg _ _)) hT
  have hData : Filter.Tendsto (fun m : ℕ => C * hNorm 0 (cutoff m f - f)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul (cutoff_converges hf0)
  intro ε hε
  have hEvent : ∀ᶠ m : ℕ in Filter.atTop, C * hNorm 0 (cutoff m f - f) < ε := hData.eventually (gt_mem_nhds hε)
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp hEvent
  refine ⟨m0, ?_⟩
  intro m hmm0 t ht
  have hvm : KdVSolution 2 T (cutoff m f) (v m) := ⟨(hv m).2.1 2, (hv m).1, (hv m).2.2.2⟩
  have hInput : hNorm 0 (cutoff m f) + hNorm 0 f ≤ 2 * hNorm 0 f := by linarith [cutoff_hNorm_le hf0 m]
  have h := hDep 2 γ (by norm_num) hγ.le (cutoff m f) f (cutoff_real hfr m) (cutoff_meanZero hfm m)
    (cutoff_inSobolev_all 2 m f) hfr hfm hf hInput (v m) u hvm hu t ht
  exact h.trans_lt (hm0 m hmm0)

/-- The explicit approximation condition does not restrict the continuous
 positive Sobolev solution class. -/
theorem exactSolution_iff_kdvSolution (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier} (hf : InSobolev γ f)
    (hfr : RealValued f) (hfm : MeanZero f) (u : ℝ → Fourier) :
    ExactSolution γ T f u ↔ KdVSolution γ T f u := by
  exact ⟨And.left, fun hu => ⟨hu, kdv_solution_smooth_approximation externalGalerkin externalLimit externalHigh externalLow externalLipschitz hγ hT hf hfr hfm hu⟩⟩

theorem exact_solution_exists (externalGalerkin : BITGalerkinEstimate)
    (externalLimit : BITExistenceLimit) (externalHigh : BITHigherRegularity)
    (externalLow : BITLowRegularity) (externalLipschitz : BITWeakerLipschitz)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier} (hf : InSobolev γ f)
    (hfr : RealValued f) (hfm : MeanZero f) : ∃ u : ℝ → Fourier, ExactSolution γ T f u := by
  obtain ⟨u, hu⟩ := positive_kdv_flow_exists externalGalerkin externalLimit externalHigh externalLow hγ hT hf hfr hfm
  exact ⟨u, (exactSolution_iff_kdvSolution externalGalerkin externalLimit externalHigh externalLow externalLipschitz hγ hT hf hfr hfm u).mpr hu⟩


end

section

def productCoefficientBilinear (k : ℤ) : Sobolev 0 →ₗ[ℂ] Sobolev 0 →ₗ[ℂ] ℂ where
  toFun f := {
    toFun g := product f.val g.val k
    map_add' g h := congrFun (product_add_right f.property g.property h.property) k
    map_smul' z g := congrFun (product_smul_right z f.val g.val) k }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    exact congrFun (product_add_left f.property g.property h.property) k
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    exact congrFun (product_smul_left z f.val g.val) k

def productCoefficientMap (k : ℤ) : Sobolev 0 →L[ℂ] Sobolev 0 →L[ℂ] ℂ :=
  (productCoefficientBilinear k).mkContinuous₂ 1 (fun f g => by
    simp only [sobolev_norm, one_mul]
    exact product_coeff_bound f.property g.property k)

theorem productCoefficientMap_apply (k : ℤ) (f g : Sobolev 0) :
    productCoefficientMap k f g = product f.val g.val k := rfl

theorem continuous_productCoefficientMap {X : Type*} [TopologicalSpace X] (k : ℤ)
    {f g : X → Sobolev 0} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => product (f x).val (g x).val k) :=
  ((productCoefficientMap k).continuous.comp hf).clm_apply hg

theorem continuous_BCoefficient {f g : ℝ → Sobolev 0} (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    Continuous (fun t : ℝ => B t (f t).val (g t).val k) := by
  have hp := continuous_productCoefficientMap k (continuous_airy_apply 0 continuous_id hf)
    (continuous_airy_apply 0 continuous_id hg)
  change Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3) *
    ((Complex.I * (k : ℂ)) * product (airy t (f t).val) (airy t (g t).val) k))
  have hE : Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3)) := by fun_prop
  exact hE.mul (continuous_const.mul hp)


end

section

def roughTwistedPath {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : ℝ → Sobolev 0 :=
  sobolevExtension hT (fun t => airy (-t) (u t))
    ((hu.1.of_le hγ).airy_path (fun t : ℝ => -t) continuous_neg)

theorem roughTwistedPath_val_on {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (roughTwistedPath hT hγ hu t).val = airy (-t) (u t) := sobolevExtension_val_on hT _ ht

theorem continuous_roughTwistedPath {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : Continuous (roughTwistedPath hT hγ hu) :=
  continuous_sobolevExtension hT _

theorem roughTwistedPath_equation {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (k : ℤ) :
    (roughTwistedPath hT hγ hu t).val k = f k + (1 / 2 : ℂ) *
      ∫ r : ℝ in (0 : ℝ)..t, B r (roughTwistedPath hT hγ hu r).val (roughTwistedPath hT hγ hu r).val k := by
  have h := (twist_Duhamel hu.2.1).2 t ht k
  rw [roughTwistedPath_val_on hT hγ hu ht]
  convert h using 1
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le ht.1] at hr
  dsimp only
  rw [roughTwistedPath_val_on hT hγ hu ⟨hr.1, hr.2.trans ht.2⟩]

theorem roughTwistedPath_hasDerivAt {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => (roughTwistedPath hT hγ hu r).val k)
      ((1 / 2 : ℂ) * B t (roughTwistedPath hT hγ hu t).val (roughTwistedPath hT hγ hu t).val k) t := by
  let v := roughTwistedPath hT hγ hu
  have hc := continuous_BCoefficient (continuous_roughTwistedPath hT hγ hu) (continuous_roughTwistedPath hT hγ hu) k
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := (hasDerivAt_const t (f k)).add (hi.const_mul (1 / 2 : ℂ))
  have hEq : (fun r : ℝ => (v r).val k) =ᶠ[nhds t]
      (fun r : ℝ => f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..r, B s (v s).val (v s).val k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    exact roughTwistedPath_equation hT hγ hu hr k
  simpa only [zero_add] using! hd.congr_of_eventuallyEq hEq

theorem rough_physical_coefficient_hasDerivAt {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℤ) :
    HasDerivAt (fun r : ℝ => u r k)
      (Complex.I * (k : ℂ) ^ 3 * u t k + (1 / 2 : ℂ) * (Complex.I * (k : ℂ)) * product (u t) (u t) k) t := by
  let v := roughTwistedPath hT hγ hu
  let E := fun r : ℝ => Complex.exp (Complex.I * (r : ℂ) * (k : ℂ) ^ 3)
  have hdv := roughTwistedPath_hasDerivAt hT hγ hu ht k
  have hdE : HasDerivAt E ((Complex.I * (k : ℂ) ^ 3) * E t) t := by
    have h := ((((hasDerivAt_id t).ofReal_comp).const_mul Complex.I).mul_const ((k : ℂ) ^ 3)).cexp
    simpa only [E, id_eq, Complex.ofReal_one, mul_one, mul_comm] using h
  have hd := hdE.mul hdv
  have hEq : (fun r : ℝ => E r * (v r).val k) =ᶠ[nhds t] (fun r : ℝ => u r k) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    change airy r (v r).val k = u r k
    rw [roughTwistedPath_val_on hT hγ hu hr, airy_inverse_neg]
  have hB : E t * B t (v t).val (v t).val k = (Complex.I * (k : ℂ)) * product (u t) (u t) k := by
    change airy t (B t (v t).val (v t).val) k = _
    rw [B, airy_inverse_neg, roughTwistedPath_val_on hT hγ hu ⟨ht.1.le, ht.2.le⟩, airy_inverse_neg]
    rfl
  have hU : E t * (v t).val k = u t k := hEq.self_of_nhds
  apply (hd.congr_of_eventuallyEq hEq.symm).congr_deriv
  linear_combination (Complex.I * (k : ℂ) ^ 3) * hU + (1 / 2 : ℂ) * hB


end

section

/-- The time-distributional identity for every integer spatial Fourier mode.
 The negative Sobolev realization below supplies its vector-valued form. -/
def DistributionalKdV (T : ℝ) (u : ℝ → Fourier) : Prop :=
  WeakTimeDerivative 0 T u (fun t => physicalRHS (u t))

theorem weakTimeDerivative_of_coefficient_calculus {a b : ℝ} (hab : a ≤ b)
    {f df : ℝ → Fourier}
    (hc : ∀ k : ℤ, ContinuousOn (fun t => f t k) (Set.Icc a b))
    (hdc : ∀ k : ℤ, ContinuousOn (fun t => df t k) (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ, HasDerivAt (fun r => f r k) (df t k) t) :
    WeakTimeDerivative a b f df := by
  intro k φ hφ _ hsupp
  have ha : φ a = 0 := by
    by_contra h
    exact (lt_irrefl a) (hsupp h).1
  have hb : φ b = 0 := by
    by_contra h
    exact (lt_irrefl b) (hsupp h).2
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hφdiff := hφ.differentiable (by simp)
  have hprod := hcφ.continuousOn.mul (hc k)
  have hi1 : IntervalIntegrable (fun t => ((deriv φ t : ℝ) : ℂ) * f t k) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hcDφ.continuousOn.mul (hc k))
  have hi2 : IntervalIntegrable (fun t => (φ t : ℂ) * df t k) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hcφ.continuousOn.mul (hdc k))
  have hder (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun r => (φ r : ℂ) * f r k)
        (((deriv φ t : ℝ) : ℂ) * f t k + (φ t : ℂ) * df t k) t :=
    ((hφdiff t).hasDerivAt.ofReal_comp).mul (hd t ht k)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hprod hder (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  change (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) * f t k) +
    (∫ t : ℝ in a..b, (φ t : ℂ) * df t k) = (φ b : ℂ) * f b k - (φ a : ℂ) * f a k at hFTC
  simp only [ha, hb, Complex.ofReal_zero, zero_mul, sub_self] at hFTC
  linear_combination hFTC

theorem kdv_solution_distributional {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : DistributionalKdV T u := by
  let U := sobolevExtension hT u (hu.1.of_le hγ)
  have hUC : Continuous U := continuous_sobolevExtension hT _
  have hUv (t : ℝ) (ht : t ∈ Set.Icc 0 T) : (U t).val = u t := sobolevExtension_val_on hT _ ht
  apply weakTimeDerivative_of_coefficient_calculus hT
  · intro k
    have h := (coefficientMap 0 k).continuous.comp hUC
    apply h.continuousOn.congr
    intro t ht
    change u t k = (U t).val k
    rw [hUv t ht]
  · intro k
    have hP := continuous_productCoefficientMap k hUC hUC
    have hC := ((continuous_const (y := Complex.I * (k : ℂ) ^ 3)).mul ((coefficientMap 0 k).continuous.comp hUC)).add
      ((continuous_const (y := (1 / 2 : ℂ) * (Complex.I * (k : ℂ)))).mul hP)
    have hR : Continuous (fun t : ℝ => physicalRHS (U t).val k) := by
      simp only [physicalRHS_coefficient]
      exact hC
    apply hR.continuousOn.congr
    intro t ht
    dsimp only
    rw [hUv t ht]
  · intro t ht k
    rw [physicalRHS_coefficient]
    exact rough_physical_coefficient_hasDerivAt hT hγ hu ht k


end

section

def negativeProductBilinear : Sobolev 0 →ₗ[ℂ] Sobolev 0 →ₗ[ℂ] Sobolev (-1) where
  toFun f := {
    toFun g := ⟨product f.val g.val, (negative_product_bound (q := 1) (by norm_num) f.property g.property).1⟩
    map_add' g h := by apply Sobolev.ext; exact product_add_right f.property g.property h.property
    map_smul' z g := by apply Sobolev.ext; exact product_smul_right z f.val g.val }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Sobolev.ext
    exact product_add_left f.property g.property h.property
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply Sobolev.ext
    exact product_smul_left z f.val g.val

def negativeProductMap : Sobolev 0 →L[ℂ] Sobolev 0 →L[ℂ] Sobolev (-1) :=
  negativeProductBilinear.mkContinuous₂ (negativeProductConstant 1 (by norm_num))
    (fun f g => by simp only [sobolev_norm]; exact (negative_product_bound (q := 1) (by norm_num) f.property g.property).2)

def derivativeBetweenLinear (s r : ℝ) (h : r = s + 1) : Sobolev r →ₗ[ℂ] Sobolev s where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := s) (by rw [← h]; exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeBetweenMap (s r : ℝ) (h : r = s + 1) : Sobolev r →L[ℂ] Sobolev s :=
  (derivativeBetweenLinear s r h).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    have hf : InSobolev (s + 1) f.val := by rw [← h]; exact f.property
    have hn := derivative_hNorm hf
    rw [← h] at hn
    exact hn)

/-- Every term of the rough KdV equation lives in the actual complete H^-3
 space. This is a continuous polynomial map, with no additional regularity. -/
def physicalRoughField (f : Sobolev 0) : Sobolev (-3) :=
  -derivativeBetweenMap (-3) (-2) (by norm_num)
    (derivativeBetweenMap (-2) (-1) (by norm_num) (derivativeBetweenMap (-1) 0 (by norm_num) f)) +
    (1 / 2 : ℂ) • inclusionMap (-3) (-2) (by norm_num)
      (derivativeBetweenMap (-2) (-1) (by norm_num) (negativeProductMap f f))

theorem physicalRoughField_val (f : Sobolev 0) : (physicalRoughField f).val = physicalRHS f.val := rfl

theorem continuous_physicalRoughField : Continuous physicalRoughField := by
  unfold physicalRoughField
  have hp : Continuous (fun f : Sobolev 0 => negativeProductMap f f) :=
    (negativeProductMap.continuous.comp continuous_id).clm_apply continuous_id
  exact ((derivativeBetweenMap (-3) (-2) (by norm_num)).continuous.comp
    ((derivativeBetweenMap (-2) (-1) (by norm_num)).continuous.comp
      (derivativeBetweenMap (-1) 0 (by norm_num)).continuous)).neg.add
    ((continuous_const (y := (1 / 2 : ℂ))).smul ((inclusionMap (-3) (-2) (by norm_num)).continuous.comp
      ((derivativeBetweenMap (-2) (-1) (by norm_num)).continuous.comp hp)))


end

section

theorem sobolev_val_neg {s : ℝ} (f : Sobolev s) : (-f).val = -f.val := rfl

/-- The equation as a time distribution with values in H^-3(T), not merely
 a list of assigned derivative values. All terms use the full Fourier product. -/
def SobolevDistributionalKdV (T : ℝ) (u : ℝ → Fourier) : Prop :=
  ∃ U : ℝ → Sobolev 0, ∃ F : ℝ → Sobolev (-3), Continuous U ∧ Continuous F ∧
    (∀ t ∈ Set.Icc 0 T, (U t).val = u t ∧ (F t).val = physicalRHS (u t)) ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
      Function.support φ ⊆ Set.Ioo 0 T →
        (∫ t : ℝ in (0 : ℝ)..T, (((deriv φ t : ℝ) : ℂ)) • inclusionMap (-3) 0 (by norm_num) (U t)) =
          -(∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) • F t)

theorem kdv_solution_sobolev_distributional {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : SobolevDistributionalKdV T u := by
  let U := sobolevExtension hT u (hu.1.of_le hγ)
  let F := fun t => physicalRoughField (U t)
  have hUC : Continuous U := continuous_sobolevExtension hT _
  have hFC : Continuous F := continuous_physicalRoughField.comp hUC
  have hUv (t : ℝ) (ht : t ∈ Set.Icc 0 T) : (U t).val = u t := sobolevExtension_val_on hT _ ht
  have hFv (t : ℝ) (ht : t ∈ Set.Icc 0 T) : (F t).val = physicalRHS (u t) := by
    rw [physicalRoughField_val, hUv t ht]
  refine ⟨U, F, hUC, hFC, fun t ht => ⟨hUv t ht, hFv t ht⟩, ?_⟩
  intro φ hφ hsupp hsupport
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hi1 : IntervalIntegrable (fun t => ((deriv φ t : ℝ) : ℂ) • inclusionMap (-3) 0 (by norm_num) (U t)) volume 0 T :=
    (hcDφ.smul ((inclusionMap (-3) 0 (by norm_num)).continuous.comp hUC)).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t => (φ t : ℂ) • F t) volume 0 T :=
    (hcφ.smul hFC).intervalIntegrable 0 T
  apply Sobolev.ext
  rw [sobolev_integral_val hi1, sobolev_val_neg, sobolev_integral_val hi2]
  funext k
  change (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * (U t).val k) =
    -(∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * (F t).val k)
  have hI1 : (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * (U t).val k) =
      ∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * u t k := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [hUv t ht]
  have hI2 : (∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * (F t).val k) =
      ∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * physicalRHS (u t) k := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [hFv t ht]
  rw [hI1, hI2]
  exact kdv_solution_distributional hT hγ hu k φ hφ hsupp hsupport


end

section

def sobolevWeightedZero (s : ℝ) : Sobolev s ≃ₗᵢ[ℂ] Sobolev 0 :=
  (sobolevIsometry s).trans (sobolevIsometry 0).symm

theorem sobolevWeightedZero_val (s : ℝ) (f : Sobolev s) :
    (sobolevWeightedZero s f).val = weighted s f.val := by
  funext k
  change (weight 0 k : ℂ)⁻¹ * weighted s f.val k = weighted s f.val k
  simp [weight]

theorem weight_neg_index (s : ℝ) (k : ℤ) : weight s (-k) = weight s k := by simp [weight]

/-- The bilinear distribution/test-function pairing, on H^-s × H^s.
 The missing conjugation is intentional: distributions act on test functions,
 rather than using the sesquilinear Hilbert inner product. -/
def distributionTest (s : ℝ) (φ : Sobolev s) : Sobolev (-s) →L[ℂ] ℂ :=
  ((productCoefficientMap 0).flip (sobolevWeightedZero s φ)).comp
    (sobolevWeightedZero (-s)).toContinuousLinearEquiv.toContinuousLinearMap

theorem distributionTest_apply (s : ℝ) (φ : Sobolev s) (f : Sobolev (-s)) :
    distributionTest s φ f = ∑' k : ℤ, f.val k * φ.val (-k) := by
  change product (sobolevWeightedZero (-s) f).val (sobolevWeightedZero s φ).val 0 = _
  rw [sobolevWeightedZero_val, sobolevWeightedZero_val]
  unfold product
  apply tsum_congr
  intro k
  simp only [zero_sub, weighted, weight_neg_index, weight_neg, Complex.ofReal_inv]
  calc
    _ = (((weight s k : ℂ)⁻¹) * (weight s k : ℂ)) * (f.val k * φ.val (-k)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos s k).ne'), one_mul]

theorem distributionTest_bound (s : ℝ) (φ : Sobolev s) (f : Sobolev (-s)) :
    ‖distributionTest s φ f‖ ≤ ‖f‖ * ‖φ‖ := by
  have h := product_coeff_bound (sobolevWeightedZero (-s) f).property (sobolevWeightedZero s φ).property 0
  rw [← sobolev_norm, ← sobolev_norm, (sobolevWeightedZero (-s)).norm_map, (sobolevWeightedZero s).norm_map] at h
  exact h

/-- On functions this pairing is the same full convolution coefficient whose
 equality with normalized physical L² multiplication was proved earlier. -/
theorem distributionTest_function (s : ℝ) (hs : 0 ≤ s) (φ : Sobolev s) (f : Sobolev 0) :
    distributionTest s φ (inclusionMap (-s) 0 (by linarith) f) = product f.val φ.val 0 := by
  rw [distributionTest_apply]
  unfold product
  simp only [zero_sub, inclusionMap_val]


end

section

/-- The H^-3-valued distribution identity can be tested against every H³
 spatial test function, in particular every smooth periodic test function. -/
theorem kdv_solution_distributional_spatial_tests {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) :
    ∃ U : ℝ → Sobolev 0, ∃ F : ℝ → Sobolev (-3), Continuous U ∧ Continuous F ∧
      (∀ t ∈ Set.Icc 0 T, (U t).val = u t ∧ (F t).val = physicalRHS (u t)) ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
        Function.support φ ⊆ Set.Ioo 0 T → ∀ ψ : Sobolev 3,
        (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) *
          distributionTest 3 ψ (inclusionMap (-3) 0 (by norm_num) (U t))) =
          -(∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * distributionTest 3 ψ (F t)) := by
  obtain ⟨U, F, hUC, hFC, hval, hWeak⟩ := kdv_solution_sobolev_distributional hT hγ hu
  refine ⟨U, F, hUC, hFC, hval, ?_⟩
  intro φ hφ hsupp hsupport ψ
  let L := distributionTest 3 ψ
  have hcφ : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hcDφ : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hi1 : IntervalIntegrable (fun t => ((deriv φ t : ℝ) : ℂ) • inclusionMap (-3) 0 (by norm_num) (U t)) volume 0 T :=
    (hcDφ.smul ((inclusionMap (-3) 0 (by norm_num)).continuous.comp hUC)).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun t => (φ t : ℂ) • F t) volume 0 T := (hcφ.smul hFC).intervalIntegrable 0 T
  have h := congrArg L (hWeak φ hφ hsupp hsupport)
  rw [L.map_neg, ← L.intervalIntegral_comp_comm hi1, ← L.intervalIntegral_comp_comm hi2] at h
  simpa only [map_smul, smul_eq_mul] using h


end

end KdV

open KdV

/-- Theorem 1, conditional only on the explicitly typed cited source results.
 The stronger companion `uniform_rough_convergence` proves the same conclusion
 for every continuous Sobolev Duhamel solution, before selecting the solution
 obtained by smooth approximation. -/
theorem theorem_1 (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    (externalGalerkin : BITGalerkinEstimate) (externalLimit : BITExistenceLimit)
    (externalHigh : BITHigherRegularity) (externalLow : BITLowRegularity)
    (externalLipschitz : BITWeakerLipschitz) : TheoremOne := by
  intro T hT γ hγ hγ1 R hR
  obtain ⟨C, hC, τ0, hτ0, hConv⟩ := uniform_rough_convergence externalStep externalStage externalProduct
    externalTrilinear externalGalerkin externalLimit externalHigh externalLow externalLipschitz hT hγ hγ1 hR
  refine ⟨C, hC, τ0, hτ0, ?_⟩
  intro f hf hfr hfm hfR u hu
  exact hConv f hf hfr hfm hfR u hu.1

