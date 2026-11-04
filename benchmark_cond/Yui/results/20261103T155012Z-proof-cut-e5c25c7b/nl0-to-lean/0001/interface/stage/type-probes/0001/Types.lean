import Mathlib
open scoped BigOperators ENNReal
open MeasureTheory Filter Set
noncomputable section
namespace KdV
abbrev Coeff := ℤ → ℂ
abbrev Curve := ℝ → Coeff
def weight (s : ℝ) (k : ℤ) : ℝ := (1 + (k : ℝ)^2) ^ s
def H (s : ℝ) (f : Coeff) : Prop := Summable (fun k => weight s k * ‖f k‖^2)
def hn (s : ℝ) (f : Coeff) : ℝ := Real.sqrt (∑' k, weight s k * ‖f k‖^2)
def dh (s : ℝ) (f : Coeff) : Prop :=
  f 0 = 0 ∧ Summable (fun k : ℤ => if k = 0 then 0 else |(k : ℝ)|^(2*s) * ‖f k‖^2)
def dn (s : ℝ) (f : Coeff) : ℝ :=
  Real.sqrt (∑' k : ℤ, if k = 0 then 0 else |(k : ℝ)|^(2*s) * ‖f k‖^2)
def realCoeff (f : Coeff) : Prop := ∀ k, f (-k) = star (f k)
def mz (f : Coeff) : Prop := f 0 = 0
def data (s : ℝ) (f : Coeff) : Prop := H s f ∧ mz f
def rd (s : ℝ) (f : Coeff) : Prop := data s f ∧ realCoeff f
def smooth (f : Coeff) : Prop := ∀ m : ℕ, H (m : ℝ) f
def poly (f : Coeff) : Prop := Set.Finite (Function.support f)
def ik (k : ℤ) : ℂ := Complex.I * (k : ℂ)
def air (t : ℝ) (f : Coeff) : Coeff :=
  fun k => Complex.exp (Complex.I * (t : ℂ) * (k : ℂ)^3) * f k
def proj (f : Coeff) : Coeff := fun k => if k = 0 then 0 else f k
def mean (f : Coeff) : Coeff := fun k => if k = 0 then f 0 else 0
def invD (f : Coeff) : Coeff := fun k => if k = 0 then 0 else (ik k)⁻¹ * f k
def invD2 (f : Coeff) : Coeff := invD (invD f)
def dx (f : Coeff) : Coeff := fun k => ik k * f k
def mul (f g : Coeff) : Coeff := fun k => ∑' a : ℤ, f a * g (k-a)
def cube (f : Coeff) : Coeff := mul (mul f f) f
def low (N : ℝ) (f : Coeff) : Coeff := fun k => if |(k : ℝ)| ≤ N then f k else 0
def high (N : ℝ) (f : Coeff) : Coeff := f - low N f
def eval (f : Coeff) (x : ℝ) : ℂ := ∑' k : ℤ, Complex.exp (Complex.I * (k : ℂ) * (x : ℂ)) * f k
def linfty (f : Coeff) : ℝ := sSup ((fun x => ‖eval f x‖) '' Icc 0 (2*Real.pi))
def bn (t : ℝ) (f g : Coeff) : Coeff := air (-t) (dx (mul (air t f) (air t g)))
def jn (t : ℝ) (f g : Coeff) : Coeff := air (-t) (proj (mul (air t (invD f)) (air t (invD g))))
def cint (a b : ℝ) (f g h : Curve) : Coeff :=
  fun k => ∫ t in a..b, (air (-t) (proj (mul (proj (mul (air t (f t)) (air t (g t)))) (air t (invD (h t)))))) k
def intC (a b : ℝ) (f : Curve) : Coeff := fun k => ∫ t in a..b, f t k
def stage (n : ℕ) (τ t : ℝ) (f g : Coeff) : Coeff :=
  (1/2 : ℂ) • intC ((n : ℝ)*τ) t (fun r => bn r f g)
def favg (τ α : ℝ) : ℂ := (τ : ℂ)⁻¹ * ∫ t in (0 : ℝ)..τ, Complex.exp (-Complex.I * (t : ℂ) * (α : ℂ))
def eta (τ α β : ℝ) : ℂ := favg τ (α+β) - favg τ α * favg τ β
def phase1 (a b : ℤ) : ℝ := 3*(a:ℝ)*(b:ℝ)*((a+b):ℤ)
def phase2 (k c p : ℤ) : ℝ := 3*(k:ℝ)*(c:ℝ)*(p:ℝ)
abbrev Mult := ℤ → ℤ → ℤ → ℤ → ℂ
def unitMult : Mult := fun _ _ _ _ => 1
def rterm (μ : Mult) (n : ℕ) (τ : ℝ) (f g h : Coeff) (k : ℤ) (v : ℤ × ℤ) : ℂ :=
  let a := v.1
  let b := v.2
  let c := k-a-b
  let α := phase1 a b
  let β := phase2 k c (a+b)
  if k = 0 ∨ a+b = 0 then 0 else
    -(τ : ℂ)/(18*ik k) * μ k a b c *
      Complex.exp (-Complex.I * ((n:ℝ)*τ : ℝ) * ((α+β : ℝ) : ℂ)) *
      eta τ α β * f a * g b * h c
def rem (μ : Mult) (n : ℕ) (τ : ℝ) (f g h : Coeff) : Coeff :=
  fun k => ∑' v : ℤ × ℤ, rterm μ n τ f g h k v
def quad (τ : ℝ) (f : Coeff) : Coeff :=
  (1/6 : ℂ) • proj (mul (air τ (invD f)) (air τ (invD f))) -
  (1/6 : ℂ) • air τ (proj (mul (invD f) (invD f)))
def cubic (τ : ℝ) (f : Coeff) : Coeff :=
  let F := quad τ f
  let E := fun s => air (τ-s) (invD (cube (air s (invD f))))
  let G := fun s => air (τ-s) (invD2 (mul (air (s-τ) (invD2 F)) (air s (invD f))))
  (1/3 : ℂ) • proj (mul (air τ (invD f)) (invD F)) +
  ((τ/9 : ℝ) : ℂ) • mul (air τ (invD f)) (mean (mul f f)) -
  (1/54 : ℂ) • (E τ - E 0) - ((1/(27*τ) : ℝ) : ℂ) • (G τ - G 0)
def step (τ : ℝ) (f : Coeff) : Coeff := air τ f + quad τ f + cubic τ f
def iter (τ : ℝ) (q : Coeff) : ℕ → Coeff
  | 0 => q
  | n+1 => step τ (iter τ q n)
def pstar : ℝ := 23/14
def aux (γ : ℝ) : ℝ := if γ < 1/2 then 1/2-γ else if γ = 1/2 then 1/8 else 0
def sourceAux (s ε : ℝ) : ℝ := if s = 0 then 1/2+ε else if s < 1/2 then 1/2-s else if s = 1/2 then ε else 0
def beta0 (s ε : ℝ) : ℝ := if s < 1/2 then 2*s-3/2 else if s = 1/2 then -1/2-ε else s-1
def k3 (a b c d : ℤ) : ℝ :=
  max (min |(a:ℝ)| (min |(b:ℝ)| |(c:ℝ)|))
    (max (min |(a:ℝ)| (min |(b:ℝ)| |(d:ℝ)|))
      (max (min |(a:ℝ)| (min |(c:ℝ)| |(d:ℝ)|)) (min |(b:ℝ)| (min |(c:ℝ)| |(d:ℝ)|))))
def contH (s a b : ℝ) (f : Curve) : Prop :=
  (∀ t ∈ Icc a b, H s (f t)) ∧
  ∀ t ∈ Icc a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ r ∈ Icc a b, |r-t| < δ → hn s (f r - f t) < ε
def convH (s : ℝ) (f : ℕ → Coeff) (g : Coeff) : Prop :=
  (∀ n, H s (f n)) ∧ H s g ∧ Tendsto (fun n => hn s (f n-g)) atTop (nhds 0)
def supH (s a b : ℝ) (f : Curve) : ℝ := sSup ((fun t => hn s (f t)) '' Icc a b)
def boundedH (s a b : ℝ) (f : Curve) : Prop :=
  (∀ t ∈ Icc a b, H s (f t)) ∧ ∃ C : ℝ, ∀ t ∈ Icc a b, hn s (f t) ≤ C
def aeH (s a b : ℝ) (f : Curve) : Prop :=
  (∀ k : ℤ, AEStronglyMeasurable (fun t => f t k) (volume.restrict (Icc a b))) ∧
  (∀ᵐ t ∂(volume.restrict (Icc a b)), H s (f t)) ∧
  ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Icc a b)), hn s (f t) ≤ C
def essH (s a b : ℝ) (f : Curve) : ℝ :=
  (essSup (fun t => ENNReal.ofReal (hn s (f t))) (volume.restrict (Icc a b))).toReal
def weakD (a b : ℝ) (f df : Curve) : Prop :=
  (∀ k : ℤ, IntervalIntegrable (fun t => df t k) volume a b) ∧
  ∀ t ∈ Icc a b, ∀ k : ℤ, f t k = f a k + ∫ r in a..t, df r k
def admissible (s a b : ℝ) (f df : Curve) : Prop :=
  aeH s a b f ∧ aeH (-pstar) a b df ∧ weakD a b f df
def xn (a b : ℝ) (f df : Curve) : ℝ := essH 0 a b f + essH (-pstar) a b df
def normDeriv (s a b t : ℝ) (f : Curve) (d : Coeff) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc a b,
    0 < |r-t| → |r-t| < δ →
      hn s (f r - f t - ((r-t : ℝ) : ℂ) • d) ≤ ε * |r-t|
def smoothPair (a b : ℝ) (f df : Curve) : Prop :=
  ∀ m : ℕ, contH (m:ℝ) a b f ∧ contH (m:ℝ) a b df ∧
    ∀ t ∈ Icc a b, normDeriv (m:ℝ) a b t f (df t)
def piecewise (a b : ℝ) (f df : Curve) : Prop :=
  (∀ m : ℕ, contH (m:ℝ) a b f) ∧
  ∃ N : ℕ, ∃ r : ℕ → ℝ, ∃ d : ℕ → Curve,
    r 0 = a ∧ r N = b ∧
    (∀ j < N, r j ≤ r (j+1) ∧ smoothPair (r j) (r (j+1)) f (d j) ∧
      (∀ᵐ t ∂(volume.restrict (Icc (r j) (r (j+1)))), df t = d j t))
def twisted (sign : ℝ) (u : Curve) : Curve := fun t => air (-sign*t) (u t)
def rhs (sign : ℝ) (f : Coeff) : Coeff :=
  fun k => Complex.I * (sign : ℂ) * (k : ℂ)^3 * f k + (1/2 : ℂ) * ik k * mul f f k
def solution (sign s A : ℝ) (q : Coeff) (u : Curve) : Prop :=
  contH s 0 A u ∧ u 0 = q ∧
  (∀ t ∈ Icc 0 A, realCoeff (u t) ∧ mz (u t)) ∧
  (∀ k : ℤ, IntervalIntegrable (fun t => rhs sign (u t) k) volume 0 A) ∧
  ∀ t ∈ Icc 0 A, ∀ k : ℤ, u t k = q k + ∫ r in (0:ℝ)..t, rhs sign (u r) k
def smoothCurve (a b : ℝ) (u : Curve) : Prop := ∀ m : ℕ, contH (m:ℝ) a b u
def exact (sign s A : ℝ) (q : Coeff) (u : Curve) : Prop :=
  solution sign s A q u ∧ ∃ us : ℕ → Curve,
    (∀ m, solution sign 0 A (low (m:ℝ) q) (us m) ∧ smoothCurve 0 A (us m)) ∧
    Tendsto (fun m => supH 0 0 A (fun t => us m t-u t)) atTop (nhds 0)
end KdV

set_option autoImplicit false
def __probe_0 :=
  (KdV.exact 1 (1/2) 1 (0 : KdV.Coeff) (0 : KdV.Curve))
def __probe_1 :=
  (KdV.admissible 0 0 1 (0 : KdV.Curve) (0 : KdV.Curve))
