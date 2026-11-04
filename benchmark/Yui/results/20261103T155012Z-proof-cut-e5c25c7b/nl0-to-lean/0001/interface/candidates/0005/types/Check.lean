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
    (∀ m : ℕ, solution sign 0 A (low (m:ℝ) q) (us m) ∧ smoothCurve 0 A (us m)) ∧
    Tendsto (fun m => supH 0 0 A (fun t => us m t-u t)) atTop (nhds 0)
end KdV

namespace KdV
def srcScale : ℝ := Real.sqrt (2*Real.pi)
def pairing (f g : Coeff) : ℂ := ∑' k : ℤ, f k * star (g k)
def L1dual (s A : ℝ) (g : Curve) : Prop :=
  (∀ k : ℤ, AEStronglyMeasurable (fun t => g t k) (volume.restrict (Icc 0 A))) ∧
  (∀ᵐ t ∂(volume.restrict (Icc 0 A)), dh (-s) (g t)) ∧
  IntegrableOn (fun t => dn (-s) (g t)) (Icc 0 A) volume
def gal (A : ℝ) (q : Coeff) (m : ℕ) (u : Curve) : Prop :=
  u 0 = low (m:ℝ) q ∧ smoothCurve 0 A u ∧
  (∀ t ∈ Icc 0 A, rd 0 (u t) ∧ low (m:ℝ) (u t) = u t) ∧
  weakD 0 A u (fun t => low (m:ℝ) (rhs (-1) (u t)))
def galBounds : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ A : ℝ, 0 < A → ∀ B Q : ℝ, 0 ≤ B → 0 ≤ Q →
  ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Coeff, dh s q → realCoeff q → hn 0 q ≤ B → dn s q ≤ Q →
    ∀ m : ℕ, ∀ u : Curve, gal A q m u → ∀ t ∈ Icc 0 A, dn s (u t) ≤ M
def sourceCompactness : Prop :=
  ∀ s : ℝ, 0 < s → ∀ A : ℝ, 0 < A → ∀ q : Coeff, dh s q → realCoeff q →
  ∀ σ : ℝ, 0 < σ → σ < s →
  ∃ us : ℕ → Curve, ∃ u : Curve, ∃ κ : ℕ → ℕ,
    (∀ m, gal A q m (us m)) ∧ StrictMono κ ∧ exact (-1) s A q u ∧
    (∃ M : ℝ, (∀ m t, t ∈ Icc 0 A → dn s (us m t) ≤ M) ∧
      ∀ t ∈ Icc 0 A, dn s (u t) ≤ M) ∧
    (∀ p : ℝ, 1 < p →
      Tendsto (fun j => ∫ t in (0:ℝ)..A, hn σ (us (κ j) t-u t)^p) atTop (nhds 0)) ∧
    (∀ g : Curve, L1dual s A g →
      Tendsto (fun j => ∫ t in (0:ℝ)..A, pairing (us (κ j) t) (g t)) atTop
        (nhds (∫ t in (0:ℝ)..A, pairing (u t) (g t))))
def sourceFlow : Prop :=
  (∀ s : ℝ, 0 ≤ s → ∀ A : ℝ, 0 < A → ∀ q : Coeff, dh s q → realCoeff q →
    ∃ u : Curve, exact (-1) s A q u ∧
      (∀ v : Curve, solution (-1) s A q v → EqOn u v (Icc 0 A)) ∧
      ∀ t ∈ Icc 0 A, hn 0 (u t) = hn 0 q) ∧
  (∀ s : ℝ, 0 ≤ s → ∀ A : ℝ, 0 < A → ∀ B : ℝ, 0 ≤ B →
    ∃ C : ℝ, 0 < C ∧ ∀ q r : Coeff,
      dh s q → dh s r → realCoeff q → realCoeff r → dn s q + dn s r ≤ B →
      ∀ u v : Curve, exact (-1) s A q u → exact (-1) s A r v →
        ∀ t ∈ Icc 0 A, dn s (u t-v t) ≤ C*dn s (q-r)) ∧
  (∀ θ B : ℝ, -1 < θ → θ ≤ 0 → 0 ≤ B →
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ A : ℝ, 0 < A → ∀ q r : Coeff,
        rd 0 q → rd 0 r → hn 0 q+hn 0 r ≤ B →
        ∀ u v : Curve, exact (-1) 0 A q u → exact (-1) 0 A r v →
          ∀ t ∈ Icc 0 A,
            dn θ (twisted (-1) u t-twisted (-1) v t) ≤ C*D^A*dn θ (q-r))
def sourceUniform : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ A : ℝ, 0 < A → ∀ B Q : ℝ, 0 ≤ B → 0 ≤ Q →
  ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Coeff, dh s q → realCoeff q → hn 0 q ≤ B → dn s q ≤ Q →
    ∀ u : Curve, exact (-1) s A q u → ∀ t ∈ Icc 0 A, dn s (u t) ≤ M
def bit : Prop := galBounds ∧ sourceCompactness ∧ sourceFlow ∧ sourceUniform
def cubicBounds (K : ℝ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ α a b : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ a → a ≤ b → b-a ≤ 1 →
    ∀ f df : Fin 3 → Curve, (∀ j, admissible α a b (f j) (df j)) →
      H 0 (cint a b (f 0) (f 1) (f 2)) ∧ ∀ i : Fin 3,
      K*hn 0 (cint a b (f 0) (f 1) (f 2)) ≤
        C*(b-a)*(∏ j : Fin 3, K*xn a b (f j) (df j)) +
        C*(K*essH (-pstar) a b (f i))*
          (∏ j ∈ (Finset.univ.erase i), K*essH 0 a b (f j))) ∧
  (∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∃ C : ℝ, 0 < C ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b-a ≤ 1 →
    ∀ f : Fin 3 → Coeff, (∀ j, H s (f j)) →
      H 0 (cint a b (fun _ => f 0) (fun _ => f 1) (fun _ => f 2)) ∧
      K*hn 0 (cint a b (fun _ => f 0) (fun _ => f 1) (fun _ => f 2)) ≤
        C*(b-a)^s*(∏ j : Fin 3, K*hn s (f j)))
def productBounds (K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ f g : Coeff, H s f → H (sourceAux s ε) g →
    H 0 (mul f g) ∧ K*hn 0 (mul f g) ≤ C*(K*hn s f)*(K*hn (sourceAux s ε) g)
def stageBoundAt (K s ε : ℝ) : Prop :=
  ∀ β : ℝ, beta0 s ε ≤ β → β ≤ 1+s →
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ τ t : ℝ, 0 < τ →
  t ∈ Icc ((n:ℝ)*τ) (((n:ℝ)+1)*τ) →
  ∀ f g : Coeff, data s f → data s g →
    H β (stage n τ t f g) ∧
    K*hn β (stage n τ t f g) ≤
      C*τ^((1+s-β)/(1+s-beta0 s ε))*(K*hn s f)*(K*hn s g)
def stageBounds (K : ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → s ≤ 1 → s ≠ 1/2 → stageBoundAt K s 0) ∧
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → stageBoundAt K (1/2) ε
def schemeIdentity : Prop :=
  ∀ n : ℕ, ∀ τ : ℝ, 0 < τ → ∀ f : Coeff, smooth f → mz f →
    air (-((n:ℝ)*τ)-τ) (step τ (air ((n:ℝ)*τ) f)) =
      f + stage n τ (((n:ℝ)+1)*τ) f f +
      intC ((n:ℝ)*τ) (((n:ℝ)+1)*τ) (fun t => bn t f (stage n τ t f f)) -
      rem unitMult n τ f f f
def fn (n : ℕ) (τ : ℝ) (f : Coeff) : Curve := fun t => stage n τ t f f
def zn (n : ℕ) (τ : ℝ) (f : Coeff) : Curve := fun t => f + fn n τ f t
def dz (f : Coeff) : Curve := fun t => (1/2 : ℂ) • bn t f f
def cn (n : ℕ) (τ : ℝ) (f : Coeff) : Curve :=
  fun t => intC ((n:ℝ)*τ) t (fun r => bn r f (fn n τ f r))
def qn (n : ℕ) (τ : ℝ) (f : Coeff) : Curve :=
  fun t => (1/2 : ℂ) • intC ((n:ℝ)*τ) t (fun r => bn r (fn n τ f r) (fn n τ f r))
def wn (n : ℕ) (τ : ℝ) (f : Coeff) : Coeff :=
  qn n τ f (((n:ℝ)+1)*τ) + rem unitMult n τ f f f
def vn (n : ℕ) (τ : ℝ) (f : Coeff) : Curve :=
  fun t => f + fn n τ f t + cn n τ f t + qn n τ f t -
    (((t-(n:ℝ)*τ)/τ : ℝ) : ℂ) • wn n τ f
def yn (n : ℕ) (τ : ℝ) (f : Coeff) : Curve := vn n τ f - zn n τ f
def dy (n : ℕ) (τ : ℝ) (f : Coeff) : Curve :=
  fun t => bn t f (fn n τ f t) + (1/2 : ℂ) • bn t (fn n τ f t) (fn n τ f t) -
    ((τ⁻¹ : ℝ) : ℂ) • wn n τ f
def drho (n : ℕ) (τ : ℝ) (f : Coeff) : Curve :=
  fun t => -bn t (yn n τ f t) (zn n τ f t) -
    (1/2 : ℂ) • bn t (yn n τ f t) (yn n τ f t) -
    ((τ⁻¹ : ℝ) : ℂ) • wn n τ f
def rho (n : ℕ) (τ : ℝ) (f : Coeff) : Curve :=
  fun t => -intC ((n:ℝ)*τ) t (fun r => bn r (yn n τ f r) (zn n τ f r)) -
    (1/2 : ℂ) • intC ((n:ℝ)*τ) t (fun r => bn r (yn n τ f r) (yn n τ f r)) -
    (((t-(n:ℝ)*τ)/τ : ℝ) : ℂ) • wn n τ f
def idx (τ t : ℝ) : ℕ := (Int.floor (t/τ)).toNat
def datum (τ : ℝ) (q : Coeff) (n : ℕ) : Coeff := air (-((n:ℝ)*τ)) (iter τ q n)
def interp (τ : ℝ) (q : Coeff) : Curve := fun t => vn (idx τ t) τ (datum τ q (idx τ t)) t
def residual (τ : ℝ) (q : Coeff) : Curve := fun t =>
  (∑ j ∈ Finset.range (idx τ t), rho j τ (datum τ q j) (((j:ℝ)+1)*τ)) +
    rho (idx τ t) τ (datum τ q (idx τ t)) t
def dres (τ : ℝ) (q : Coeff) : Curve := fun t => drho (idx τ t) τ (datum τ q (idx τ t)) t
def dvnum (τ : ℝ) (q : Coeff) : Curve := fun t =>
  let n := idx τ t
  let f := datum τ q n
  (1/2 : ℂ) • bn t (zn n τ f t) (zn n τ f t) - ((τ⁻¹ : ℝ) : ℂ) • wn n τ f
end KdV

namespace KdV
def phaseEst : Prop :=
  ∀ τ α β : ℝ, 0 < τ →
    ((α = 0 ∨ β = 0) → eta τ α β = 0) ∧
    (α ≠ 0 → β ≠ 0 →
      ‖eta τ α β‖ ≤ 2*min |α/β| |β/α| ∧
      ‖eta τ α β‖ ≤ τ*min |α| |β|)
def freqEst : Prop :=
  ∀ a b c d : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → a+b+c+d = 0 →
  ∀ N1 N2 N3 N4 : ℝ,
    List.Perm [|(a:ℝ)|, |(b:ℝ)|, |(c:ℝ)|, |(d:ℝ)|] [N1,N2,N3,N4] →
    N4 ≤ N3 → N3 ≤ N2 → N2 ≤ N1 →
    N1 ≤ 3*N2 ∧
    |(d:ℝ)|⁻¹ * min (|(a:ℝ)*(b:ℝ)|/|(c:ℝ)*(d:ℝ)|)
      (|(c:ℝ)*(d:ℝ)|/|(a:ℝ)*(b:ℝ)|) ≤ 3/N3 ∧
    |((a+b:ℤ):ℝ)| / max |(a:ℝ)*(b:ℝ)| |(c:ℝ)*(d:ℝ)| ≤ 6/N3
def phaseAndGeometry : Prop := phaseEst ∧ freqEst
def quadTerm (x : Fin 4 → ℤ → ℝ) (Ω : Set (ℤ × ℤ × ℤ)) (v : ℤ × ℤ × ℤ) : ℝ :=
  let a := v.1
  let b := v.2.1
  let c := v.2.2
  let d := -(a+b+c)
  @ite ℝ (v ∈ Ω ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0)
    (Classical.propDecidable (v ∈ Ω ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0))
    (x 0 a * x 1 b * x 2 c * x 3 d / k3 a b c d) 0
def fourLinear : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : Fin 4 → ℤ → ℝ,
    (∀ j, x j 0 = 0 ∧ (∀ k, 0 ≤ x j k) ∧ Summable (fun k => (x j k)^2)) →
    ∀ Ω : Set (ℤ × ℤ × ℤ),
      Summable (quadTerm x Ω) ∧
      (∑' v, quadTerm x Ω v) ≤ C*(∏ j : Fin 4, Real.sqrt (∑' k, (x j k)^2))
def triOn (s : ℝ) (G : (Fin 3 → Coeff) → Coeff) : Prop :=
  ∀ f : Fin 3 → Coeff, (∀ j, data s (f j)) → ∀ i : Fin 3,
    (∀ u v : Coeff, data s u → data s v →
      G (Function.update f i (u+v)) = G (Function.update f i u) + G (Function.update f i v)) ∧
    (∀ u : Coeff, data s u → ∀ c : ℂ,
      G (Function.update f i (c • u)) = c • G (Function.update f i u))
def triBound (s τ C : ℝ) (G : (Fin 3 → Coeff) → Coeff) : Prop :=
  ∀ f : Fin 3 → Coeff, (∀ j, data s (f j)) →
    H 0 (G f) ∧ hn 0 (G f) ≤ C*τ^(1+s)*(∏ j : Fin 3, hn s (f j))
def remainderCore : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∃ C : ℝ, 0 < C ∧
  ∀ μ : Mult, (∀ k a b c, ‖μ k a b c‖ ≤ 1) →
  ∀ n : ℕ, ∀ τ : ℝ, 0 < τ →
    let G := fun f : Fin 3 → Coeff => rem μ n τ (f 0) (f 1) (f 2)
    triOn s G ∧ triBound s τ C G ∧
    (∀ f : Fin 3 → Coeff, (∀ j, data s (f j)) →
      ∀ k : ℤ, Summable (rterm μ n τ (f 0) (f 1) (f 2) k)) ∧
    (∀ F : (Fin 3 → Coeff) → Coeff, triOn s F →
      (∃ D : ℝ, 0 < D ∧ triBound s τ D F) →
      (∀ f : Fin 3 → Coeff, (∀ j, data s (f j) ∧ poly (f j)) → F f = G f) →
      ∀ f : Fin 3 → Coeff, (∀ j, data s (f j)) → F f = G f)
def numericalRemainder (γ : ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  ∀ f w : Coeff, data 0 f → data γ w → hn γ w ≤ M → hn 0 (f-w) ≤ 1 →
    H 0 (rem unitMult n τ f f f) ∧
    hn 0 (rem unitMult n τ f f f) ≤ C*τ*(τ^γ+hn 0 (f-w))
def remainderBounds (γ : ℝ) : Prop := remainderCore ∧ numericalRemainder γ
def linearBounds : Prop :=
  (∀ s t : ℝ, ∀ f : Coeff, H s f → H s (air t f) ∧ hn s (air t f) = hn s f) ∧
  (∀ t : ℝ, ∀ f : Coeff, (realCoeff f → realCoeff (air t f)) ∧ (mz f → mz (air t f))) ∧
  ∃ C : ℝ, 0 < C ∧
    (∀ f : Coeff, data 0 f → H 1 (invD f) ∧ hn 1 (invD f)+linfty (invD f) ≤ C*hn 0 f) ∧
    (∀ t : ℝ, ∀ f g : Coeff, data 0 f → data 0 g →
      H (-pstar) (bn t f g) ∧ hn (-pstar) (bn t f g) ≤ C*hn 0 f*hn 0 g ∧
      H 1 (jn t f g) ∧ hn 1 (jn t f g) ≤ C*hn 0 f*hn 0 g) ∧
    (∀ f : Coeff, H 1 f → linfty f ≤ C*hn 1 f) ∧
    (∀ f g : Coeff, H 1 f → H 1 g →
      H 1 (mul f g) ∧ hn 1 (mul f g) ≤ C*hn 1 f*hn 1 g) ∧
    (∀ f g : Coeff, H 0 f → H 0 g →
      H 0 (invD (proj (mul f g))) ∧ hn 0 (invD (proj (mul f g))) ≤ C*hn 0 f*hn 0 g) ∧
    (∀ f : Coeff, mz f → H 0 (invD f) →
      H (-pstar) f ∧ hn (-pstar) f ≤ hn 0 (invD f)) ∧
    (∀ t : ℝ, ∀ f g : Coeff, mz f → H 0 (invD f) → H 0 g →
      H 0 (jn t f g) ∧ hn 0 (jn t f g) ≤ C*hn 0 (invD f)*hn 0 g)
def normalForms : Prop :=
  (∀ t : ℝ, ∀ f g : Coeff, data 0 f → data 0 g → jn t f g = jn t g f) ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ f df g dg : Curve,
    piecewise a b f df → piecewise a b g dg →
    (∀ t ∈ Icc a b, mz (f t) ∧ mz (g t)) →
    intC a b (fun t => bn t (f t) (g t)) =
      (1/3 : ℂ) • (jn b (f b) (g b)-jn a (f a) (g a)) -
      (1/3 : ℂ) • intC a b (fun t => jn t (df t) (g t)+jn t (f t) (dg t))) ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ f g h : Curve,
    smoothCurve a b f → smoothCurve a b g → smoothCurve a b h →
    (∀ t ∈ Icc a b, mz (f t) ∧ mz (g t) ∧ mz (h t)) →
    intC a b (fun t => jn t (bn t (f t) (g t)) (h t)) = cint a b f g h) ∧
  (∀ n : ℕ, ∀ τ t : ℝ, 0 < τ →
    t ∈ Icc ((n:ℝ)*τ) (((n:ℝ)+1)*τ) → ∀ f : Coeff, data 0 f →
    stage n τ t f f = (1/6 : ℂ) • (jn t f f - jn ((n:ℝ)*τ) f f))
def basic : Prop := linearBounds ∧ normalForms
def normalizedProduct (γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f g : Coeff, H γ f → H (aux γ) g →
    H 0 (mul f g) ∧ hn 0 (mul f g) ≤ C*hn γ f*hn (aux γ) g
def normalizedStages (γ : ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ C : ℝ, 0 < C ∧
  ∀ w : Coeff, data γ w → hn γ w ≤ M → ∀ n : ℕ, ∀ τ t : ℝ, 0 < τ → τ ≤ 1 →
  t ∈ Icc ((n:ℝ)*τ) (((n:ℝ)+1)*τ) →
    H (aux γ) (stage n τ t w w) ∧ hn (aux γ) (stage n τ t w w) ≤ C*τ^γ ∧
    H (1+γ) (stage n τ t w w) ∧ hn (1+γ) (stage n τ t w w) ≤ C
def continuousBounds (γ : ℝ) : Prop :=
  0 ≤ aux γ ∧ aux γ < 1 ∧ cubicBounds 1 ∧ normalizedProduct γ ∧ normalizedStages γ
def flow (T γ R : ℝ) : Prop :=
  (∃ A : ℝ, 0 ≤ A ∧ ∀ q : Coeff, rd γ q → hn γ q ≤ R →
    (∃ u : Curve, exact 1 γ T q u) ∧
    (∀ u : Curve, exact 1 γ T q u →
      (∀ v : Curve, solution 1 γ T q v → EqOn u v (Icc 0 T)) ∧
      (smooth q → smoothCurve 0 T u) ∧
      (∀ t ∈ Icc 0 T, hn γ (u t) ≤ A) ∧
      supH γ 0 T (twisted 1 u) ≤ A ∧
      (∀ s t : ℝ, t ∈ Icc 0 T → H s (u t) →
        H s (twisted 1 u t) ∧ hn s (twisted 1 u t) = hn s (u t)) ∧
      (smooth q → weakD 0 T (twisted 1 u)
        (fun t => (1/2 : ℂ) • bn t (twisted 1 u t) (twisted 1 u t))))) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 < C ∧ ∀ q r : Coeff,
    rd 0 q → rd 0 r → hn 0 q+hn 0 r ≤ B →
    ∀ u v : Curve, exact 1 0 T q u → exact 1 0 T r v →
      supH 0 0 T (u-v) ≤ C*hn 0 (q-r))
def interpolation : Prop :=
  ∀ q : Coeff, smooth q → realCoeff q → mz q → ∀ τ : ℝ, 0 < τ →
    (∀ n : ℕ, smooth (iter τ q n) ∧ realCoeff (iter τ q n) ∧ mz (iter τ q n)) ∧
    (∀ n : ℕ, interp τ q ((n:ℝ)*τ) = datum τ q n) ∧
    (∀ n : ℕ, yn n τ (datum τ q n) ((n:ℝ)*τ) = 0) ∧
    (∀ L : ℕ, piecewise 0 ((L:ℝ)*τ) (interp τ q) (dvnum τ q) ∧
      weakD 0 ((L:ℝ)*τ) (interp τ q) (dvnum τ q) ∧
      weakD 0 ((L:ℝ)*τ) (residual τ q) (dres τ q)) ∧
    residual τ q 0 = 0 ∧
    (∀ t : ℝ, 0 ≤ t →
      dvnum τ q t = (1/2 : ℂ) • bn t (interp τ q t) (interp τ q t) + dres τ q t) ∧
    (∀ n : ℕ, ∀ t ∈ Icc ((n:ℝ)*τ) (((n:ℝ)+1)*τ),
      residual τ q t-residual τ q ((n:ℝ)*τ) = rho n τ (datum τ q n) t)
end KdV

namespace KdV
def stepHyp (γ M τ : ℝ) (f w : Coeff) : Prop :=
  smooth f ∧ smooth w ∧ mz f ∧ mz w ∧ H γ w ∧ hn γ w ≤ M ∧ hn 0 (f-w) ≤ 1 ∧ 0 < τ ∧ τ ≤ 1
def stepControlsAt (γ C : ℝ) (n : ℕ) (τ : ℝ) (f w : Coeff) : Prop :=
  let a := (n:ℝ)*τ
  let b := ((n:ℝ)+1)*τ
  let δ := hn 0 (f-w)
  let q := τ^γ+δ
  admissible 0 a b (zn n τ f) (dz f) ∧
  admissible 0 a b (yn n τ f) (dy n τ f) ∧
  xn a b (zn n τ f) (dz f) ≤ C ∧
  xn a b (yn n τ f) (dy n τ f) ≤ C*q ∧
  H 0 (wn n τ f) ∧ hn 0 (wn n τ f) ≤ C*τ*q ∧
  ∀ t ∈ Icc a b,
    H 1 (fn n τ f t) ∧ hn 1 (fn n τ f t) ≤ C ∧
    H 1 (fn n τ f t-stage n τ t w w) ∧ hn 1 (fn n τ f t-stage n τ t w w) ≤ C*δ ∧
    H (aux γ) (fn n τ f t) ∧ hn (aux γ) (fn n τ f t)+hn 0 (fn n τ f t) ≤ C*q ∧
    H 0 (bn t (fn n τ f t) (fn n τ f t)) ∧ hn 0 (bn t (fn n τ f t) (fn n τ f t)) ≤ C*q ∧
    H 0 (qn n τ f t) ∧ hn 0 (qn n τ f t)+hn 0 (wn n τ f) ≤ C*τ*q ∧
    H 0 (invD (yn n τ f t)) ∧ hn 0 (invD (yn n τ f t)) ≤ C*τ*q ∧
    H 0 (invD (dy n τ f t)) ∧ hn 0 (invD (dy n τ f t)) ≤ C*q ∧
    H 0 (yn n τ f t) ∧ hn 0 (yn n τ f t) ≤ C*q ∧
    H (-pstar) (yn n τ f t) ∧ hn (-pstar) (yn n τ f t) ≤ C*τ*q
def stepControls (γ : ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ τ : ℝ,
    ∀ f w : Coeff, stepHyp γ M τ f w → stepControlsAt γ C n τ f w
def residualControls (γ : ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ τ : ℝ,
  ∀ f w : Coeff, stepHyp γ M τ f w →
    let a := (n:ℝ)*τ
    let b := ((n:ℝ)+1)*τ
    let q := τ^γ+hn 0 (f-w)
    boundedH 0 a b (rho n τ f) ∧ supH 0 a b (rho n τ f) ≤ C*τ*q ∧
    aeH (-pstar) a b (drho n τ f) ∧ essH (-pstar) a b (drho n τ f) ≤ C*q
def stability (T γ : ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧
  ∀ q : Coeff, ∀ u : Curve, solution 1 γ T q u → smoothCurve 0 T u →
    1+supH γ 0 T (twisted 1 u) ≤ M →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → b-a ≤ 1 →
    (∃ n : ℕ, a = (n:ℝ)*τ) →
    let e := twisted 1 u - interp τ q
    let E := supH 0 a b e
    E ≤ 1 → ∀ N : ℝ, 2 ≤ N →
      E ≤ hn 0 (e a)+C*(b-a+τ)*τ^γ+
        C*(N^2*(b-a)+(b-a)+τ+N⁻¹+N^(-pstar))*E
def gridRate (T γ C τ0 : ℝ) (q : Coeff) (u : Curve) : Prop :=
  ∀ L : ℕ, 0 < L →
    let τ := T/(L:ℝ)
    τ ≤ τ0 → ∀ n : ℕ, n ≤ L →
      H 0 (iter τ q n) ∧
      hn 0 (u ((n:ℝ)*τ)-iter τ q n) ≤ C*τ^γ
def smoothRate (T γ R : ℝ) : Prop :=
  ∃ C τ0 : ℝ, 0 < C ∧ 0 < τ0 ∧
    ∀ q : Coeff, rd γ q → smooth q → hn γ q ≤ R →
    (∃ u : Curve, exact 1 γ T q u) ∧
    (∀ u : Curve, exact 1 γ T q u →
      gridRate T γ C τ0 q u ∧
      ∀ L : ℕ, 0 < L →
        let τ := T/(L:ℝ)
        τ ≤ τ0 → supH 0 0 T (twisted 1 u - interp τ q) ≤ C*τ^γ)
def rate (T γ R : ℝ) : Prop :=
  ∃ C τ0 : ℝ, 0 < C ∧ 0 < τ0 ∧
    ∀ q : Coeff, rd γ q → hn γ q ≤ R →
    (∃ u : Curve, exact 1 γ T q u ∧
      ∀ v : Curve, exact 1 γ T q v → EqOn u v (Icc 0 T)) ∧
    (∀ u : Curve, exact 1 γ T q u → gridRate T γ C τ0 q u)
end KdV

namespace Translation
set_option autoImplicit false

def __signature_T001 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdV.bit), (KdV.flow T gamma R))
def __signature_T005 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ), (KdV.basic))
def __signature_T007 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E005 : KdV.schemeIdentity), (KdV.interpolation))
def __signature_T006 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_E002 : KdV.cubicBounds KdV.srcScale) (h_E003 : KdV.productBounds KdV.srcScale) (h_E004 : KdV.stageBounds KdV.srcScale), (KdV.continuousBounds gamma))
def __signature_T002 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ), (KdV.phaseAndGeometry))
def __signature_T003 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ), (KdV.fourLinear))
def __signature_T004 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T002 : KdV.phaseAndGeometry) (h_T003 : KdV.fourLinear), (KdV.remainderBounds gamma))
def __signature_T008 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdV.remainderBounds gamma) (h_T005 : KdV.basic) (h_T006 : KdV.continuousBounds gamma), (KdV.stepControls gamma))
def __signature_T009 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdV.basic) (h_T006 : KdV.continuousBounds gamma) (h_T008 : KdV.stepControls gamma), (KdV.residualControls gamma))
def __signature_T010 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdV.basic) (h_T006 : KdV.continuousBounds gamma) (h_T007 : KdV.interpolation) (h_T008 : KdV.stepControls gamma) (h_T009 : KdV.residualControls gamma), (KdV.stability T gamma))
def __signature_T011 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdV.flow T gamma R) (h_T007 : KdV.interpolation) (h_T010 : KdV.stability T gamma), (KdV.smoothRate T gamma R))
def __signature_T012 : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdV.flow T gamma R) (h_T005 : KdV.basic) (h_T011 : KdV.smoothRate T gamma R), (KdV.rate T gamma R))
def __signature_P : Prop :=
  (∀ (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdV.bit) (h_E002 : KdV.cubicBounds KdV.srcScale) (h_E003 : KdV.productBounds KdV.srcScale) (h_E004 : KdV.stageBounds KdV.srcScale) (h_E005 : KdV.schemeIdentity), (KdV.rate T gamma R))

end Translation
