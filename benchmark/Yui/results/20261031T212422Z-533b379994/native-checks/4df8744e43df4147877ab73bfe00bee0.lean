import Mathlib
noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter MeasureTheory Set
namespace KdVPlan
abbrev Coeff := ℤ → ℂ
abbrev Path := ℝ → Coeff
def weight (s : ℝ) (k : ℤ) : ℝ := (1 + (k : ℝ)^2) ^ s
def MemH (s : ℝ) (f : Coeff) : Prop := Summable (fun k => weight s k * ‖f k‖^2)
def hn (s : ℝ) (f : Coeff) : ℝ := Real.sqrt (∑' k, weight s k * ‖f k‖^2)
def HB (s : ℝ) (f : Coeff) (C : ℝ) : Prop := MemH s f ∧ hn s f ≤ C
def ZeroMean (f : Coeff) : Prop := f 0 = 0
def RealField (f : Coeff) : Prop := ∀ k, f (-k) = star (f k)
def Data (s : ℝ) (f : Coeff) : Prop := MemH s f ∧ ZeroMean f ∧ RealField f
def Smooth (f : Coeff) : Prop := ∀ m : ℕ, MemH (m : ℝ) f
def dn (s : ℝ) (f : Coeff) : ℝ :=
  Real.sqrt (∑' k : ℤ, if k = 0 then 0 else |(k : ℝ)| ^ (2*s) * ‖f k‖^2)
def MemDot (s : ℝ) (f : Coeff) : Prop :=
  ZeroMean f ∧ Summable (fun k : ℤ => if k = 0 then 0 else |(k : ℝ)| ^ (2*s) * ‖f k‖^2)
def scale (c : ℂ) (f : Coeff) : Coeff := fun k => c * f k
def P (f : Coeff) : Coeff := fun k => if k = 0 then 0 else f k
def cutoff (N : ℝ) (f : Coeff) : Coeff := fun k => if |(k : ℝ)| ≤ N then f k else 0
def high (N : ℝ) (f : Coeff) : Coeff := f - cutoff N f
def S (t : ℝ) (f : Coeff) : Coeff := fun k => Complex.exp (Complex.I * (t * (k : ℝ)^3 : ℝ)) * f k
def invD (f : Coeff) : Coeff := fun k => if k = 0 then 0 else (Complex.I * (k : ℂ))⁻¹ * f k
def invD2 (f : Coeff) : Coeff := invD (invD f)
def dx (f : Coeff) : Coeff := fun k => Complex.I * (k : ℂ) * f k
def mul (f g : Coeff) : Coeff := fun k => ∑' j : ℤ, f j * g (k-j)
def cube (f : Coeff) : Coeff := mul (mul f f) f
def timeInt (a b : ℝ) (f : Path) : Coeff := fun k => ∫ t in a..b, f t k
def B (t : ℝ) (f g : Coeff) : Coeff := S (-t) (dx (mul (S t f) (S t g)))
def J (t : ℝ) (f g : Coeff) : Coeff := S (-t) (P (mul (S t (invD f)) (S t (invD g))))
def tri (a b : ℝ) (f g h : Path) : Coeff :=
  timeInt a b (fun t => S (-t) (P (mul (P (mul (S t (f t)) (S t (g t)))) (S t (invD (h t))))))
def stage (a b : ℝ) (f g : Coeff) : Coeff := scale (1/2) (timeInt a b (fun t => B t f g))
def avg (τ : ℝ) (f : ℝ → ℂ) : ℂ := (τ : ℂ)⁻¹ * ∫ t in (0 : ℝ)..τ, f t
def phase (α t : ℝ) : ℂ := Complex.exp (-Complex.I * (t*α : ℝ))
def eta (τ α β : ℝ) : ℂ := avg τ (phase (α+β)) - avg τ (phase α) * avg τ (phase β)
def remWith (χ : ℤ → ℤ → ℤ → ℂ) (a τ : ℝ) (f g h : Coeff) : Coeff :=
  fun k => if k = 0 then 0 else
    -(τ : ℂ) / (18 * Complex.I * (k : ℂ)) *
      ∑' z : ℤ × ℤ, if z.1 + z.2 = 0 then 0 else
        let c := k-z.1-z.2
        let α : ℝ := 3*(z.1 : ℝ)*(z.2 : ℝ)*(z.1+z.2 : ℤ)
        let β : ℝ := 3*(k : ℝ)*(c : ℝ)*(z.1+z.2 : ℤ)
        χ z.1 z.2 c * phase (α+β) a * eta τ α β * f z.1 * g z.2 * h c
def rem (a τ : ℝ) (f g h : Coeff) : Coeff := remWith (fun _ _ _ => 1) a τ f g h
def Ftau (τ : ℝ) (f : Coeff) : Coeff :=
  scale (1/6) (P (mul (S τ (invD f)) (S τ (invD f)))) -
  scale (1/6) (S τ (P (mul (invD f) (invD f))))
def Htau (τ : ℝ) (f : Coeff) : Coeff :=
  scale (1/3) (P (mul (S τ (invD f)) (invD (Ftau τ f)))) +
  scale ((τ : ℂ)/9 * mul f f 0) (S τ (invD f)) -
  scale (1/54) (S (τ-τ) (invD (cube (S τ (invD f)))) - S (τ-0) (invD (cube (S 0 (invD f))))) -
  scale (1/(27*(τ : ℂ)))
    (S (τ-τ) (invD2 (mul (S (τ-τ) (invD2 (Ftau τ f))) (S τ (invD f)))) -
     S (τ-0) (invD2 (mul (S (0-τ) (invD2 (Ftau τ f))) (S 0 (invD f)))))
def psi (τ : ℝ) (f : Coeff) : Coeff := S τ f + Ftau τ f + Htau τ f
def numerical (τ : ℝ) (f : Coeff) (n : ℕ) : Coeff := (psi τ)^[n] f
def twistedNum (τ : ℝ) (f : Coeff) (n : ℕ) : Coeff := S (-(n : ℝ)*τ) (numerical τ f n)
def pstar : ℝ := 23/14
def ag (γ : ℝ) : ℝ := if γ < 1/2 then 1/2-γ else if γ = 1/2 then 1/8 else 0
def ContH (s a b : ℝ) (f : Path) : Prop :=
  (∀ t ∈ Icc a b, MemH s (f t)) ∧
  ∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ r ∈ Icc a b, |r-t| < δ → hn s (f r-f t) < ε
def SupH (s a b : ℝ) (f : Path) : ℝ := sSup {x | ∃ t ∈ Icc a b, x = hn s (f t)}
def UB (s a b : ℝ) (f : Path) (C : ℝ) : Prop := ∀ t ∈ Icc a b, HB s (f t) C
def UniformConv (s a b : ℝ) (f : ℕ → Path) (g : Path) : Prop :=
  ∀ ε > 0, ∃ m : ℕ, ∀ n ≥ m, ∀ t ∈ Icc a b, HB s (f n t-g t) ε
def dt (f : Path) : Path := fun t k => deriv (fun r => f r k) t
def Weak (a b : ℝ) (f d : Path) : Prop :=
  (∀ k, IntegrableOn (fun t => f t k) (Icc a b) ∧ IntegrableOn (fun t => d t k) (Icc a b)) ∧
  ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → Function.support φ ⊆ Ioo a b →
    ∀ k, (∫ t in a..b, f t k * ((deriv φ t : ℝ) : ℂ)) = -(∫ t in a..b, d t k * (φ t : ℂ))
def EssH (s a b : ℝ) (f : Path) : ℝ :=
  (essSup (fun t => ENNReal.ofReal (hn s (f t))) (volume.restrict (Icc a b))).toReal
def EssBound (s a b : ℝ) (f : Path) : Prop :=
  (∀ k, AEStronglyMeasurable (fun t => f t k) (volume.restrict (Icc a b))) ∧
  (∀ᵐ t ∂(volume.restrict (Icc a b)), MemH s (f t)) ∧
  essSup (fun t => ENNReal.ofReal (hn s (f t))) (volume.restrict (Icc a b)) < (⊤ : ℝ≥0∞)
def Xnorm (a b : ℝ) (f d : Path) : ℝ := EssH 0 a b f + EssH (-pstar) a b d
def XPath (s a b : ℝ) (f d : Path) : Prop := Weak a b f d ∧ EssBound s a b f ∧ EssBound (-pstar) a b d
def SmoothOn (a b : ℝ) (f : Path) : Prop :=
  (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => f t k) (Icc a b)) ∧
  ∀ m j : ℕ, ContH (m : ℝ) a b (fun t k => iteratedDerivWithin j (fun r => f r k) (Icc a b) t)
def Piecewise (a b : ℝ) (f : Path) : Prop :=
  (∀ m : ℕ, ContH (m : ℝ) a b f) ∧
  ∃ p : Finset ℝ, ∀ l r, a ≤ l → l < r → r ≤ b →
    (∀ x ∈ p, x ∉ Ioo l r) → SmoothOn l r f
def RealPath (a b : ℝ) (f : Path) : Prop := ∀ t ∈ Icc a b, ZeroMean (f t) ∧ RealField (f t)
def F (a : ℝ) (f : Coeff) : Path := fun t => stage a t f f
def z (a : ℝ) (f : Coeff) : Path := fun t => f + F a f t
def Cst (a : ℝ) (f : Coeff) : Path := fun t => timeInt a t (fun s => B s f (F a f s))
def Qst (a : ℝ) (f : Coeff) : Path := fun t => scale (1/2) (timeInt a t (fun s => B s (F a f s) (F a f s)))
def Wst (a τ : ℝ) (f : Coeff) : Coeff := Qst a f (a+τ) + rem a τ f f f
def Vst (a τ : ℝ) (f : Coeff) : Path :=
  fun t => f + F a f t + Cst a f t + Qst a f t - scale (((t-a)/τ : ℝ) : ℂ) (Wst a τ f)
def Yst (a τ : ℝ) (f : Coeff) : Path := fun t => Vst a τ f t-z a f t
def rho (a τ : ℝ) (f : Coeff) : Path :=
  fun t => -timeInt a t (fun s => B s (Yst a τ f s) (z a f s)) -
    scale (1/2) (timeInt a t (fun s => B s (Yst a τ f s) (Yst a τ f s))) -
    scale (((t-a)/τ : ℝ) : ℂ) (Wst a τ f)
def gridIndex (τ t : ℝ) : ℕ := ⌊t/τ⌋₊
def interp (τ : ℝ) (f : Coeff) : Path :=
  fun t => let n := gridIndex τ t; Vst ((n : ℝ)*τ) τ (twistedNum τ f n) t
def residual (τ : ℝ) (f : Coeff) : Path :=
  fun t => let n := gridIndex τ t
           (∑ j ∈ Finset.range n, rho ((j : ℝ)*τ) τ (twistedNum τ f j) (((j : ℝ)+1)*τ)) +
           rho ((n : ℝ)*τ) τ (twistedNum τ f n) t
def Twist (u : Path) : Path := fun t => S (-t) (u t)
def SourceTwist (u : Path) : Path := fun t => S t (u t)
def sourceB (t : ℝ) (f g : Coeff) : Coeff := S t (dx (mul (S (-t) f) (S (-t) g)))
def IntegralEq (op : ℝ → Coeff → Coeff → Coeff) (a b : ℝ) (f : Coeff) (v : Path) : Prop :=
  v a = f ∧ ∀ t ∈ Icc a b, v t = f + scale (1/2) (timeInt a t (fun s => op s (v s) (v s)))
def SourceSol (s T : ℝ) (f : Coeff) (u : Path) : Prop :=
  ContH s 0 T u ∧ RealPath 0 T u ∧ IntegralEq sourceB 0 T f (SourceTwist u)
def KSol (s T : ℝ) (f : Coeff) (u : Path) : Prop :=
  ContH s 0 T u ∧ RealPath 0 T u ∧ IntegralEq B 0 T f (Twist u)
def SameOn (a b : ℝ) (u v : Path) : Prop := ∀ t ∈ Icc a b, u t = v t
def SmoothApprox (s T : ℝ) (f : Coeff) (u : Path) : Prop :=
  ∃ v : ℕ → Path, (∀ n : ℕ, KSol s T (cutoff (n : ℝ) f) (v n) ∧ SmoothOn 0 T (v n)) ∧ UniformConv s 0 T v u
def Exact (s T : ℝ) (f : Coeff) (u : Path) : Prop :=
  KSol s T f u ∧ SmoothApprox s T f u ∧
  ∀ v, KSol s T f v → SameOn 0 T u v
def linfty (f : Coeff) : ℝ := sSup {x | ∃ t : ℝ, x = ‖∑' k : ℤ, f k * Complex.exp (Complex.I * ((k : ℝ)*t : ℝ))‖}
def LinftyBound (f : Coeff) (C : ℝ) : Prop :=
  BddAbove {x | ∃ t : ℝ, x = ‖∑' k : ℤ, f k * Complex.exp (Complex.I * ((k : ℝ)*t : ℝ))‖} ∧ linfty f ≤ C
end KdVPlan

namespace KdVPlan
def SourceClass (T : ℝ) (f : Coeff) (u : Path) : Prop :=
  RealPath 0 T u ∧ EssBound 0 0 T u ∧ IntegralEq sourceB 0 T f (SourceTwist u)
def DotCont (s a b : ℝ) (u : Path) : Prop :=
  (∀ t ∈ Icc a b, MemDot s (u t)) ∧
  ∀ t ∈ Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ r ∈ Icc a b, |r-t| < δ → dn s (u r-u t) < ε
def DotUB (s a b : ℝ) (u : Path) (C : ℝ) : Prop := ∀ t ∈ Icc a b, MemDot s (u t) ∧ dn s (u t) ≤ C
def SourceApprox (s T : ℝ) (f : Coeff) (u : Path) : Prop :=
  ∃ v : ℕ → Path, (∀ n : ℕ, SourceSol s T (cutoff (n : ℝ) f) (v n) ∧ SmoothOn 0 T (v n)) ∧
    ∀ ε > 0, ∃ m : ℕ, ∀ n ≥ m, DotUB s 0 T (fun t => v n t-u t) ε
def galOp (m : ℕ) (t : ℝ) (f g : Coeff) : Coeff :=
  cutoff (m : ℝ) (sourceB t (cutoff (m : ℝ) f) (cutoff (m : ℝ) g))
def Galerkin (m : ℕ) (T : ℝ) (f : Coeff) (z : Path) : Prop :=
  DotCont 0 0 T z ∧ RealPath 0 T z ∧ IntegralEq (galOp m) 0 T f z
def dotPair (s : ℝ) (f g : Coeff) : ℂ :=
  ∑' k : ℤ, if k = 0 then 0 else (|(k : ℝ)| ^ (2*s) : ℝ) * f k * star (g k)
def StrongTime (s q T : ℝ) (v : ℕ → Path) (u : Path) : Prop :=
  (∀ n : ℕ, IntegrableOn (fun t => dn s (v n t-u t)^q) (Icc 0 T)) ∧
  Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..T, dn s (v n t-u t)^q) atTop (nhds 0)
def WeakStarDot (s T : ℝ) (v : ℕ → Path) (u : Path) : Prop :=
  ∀ φ : Path, (∀ k, AEStronglyMeasurable (fun t => φ t k) (volume.restrict (Icc 0 T))) →
    (∀ᵐ t ∂(volume.restrict (Icc 0 T)), MemDot s (φ t)) →
    IntegrableOn (fun t => dn s (φ t)) (Icc 0 T) →
    Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..T, dotPair s (v n t) (φ t))
      atTop (nhds (∫ t in (0 : ℝ)..T, dotPair s (u t) (φ t)))
def EFlow : Prop :=
  (∀ s T : ℝ, 0 ≤ s → 0 < T →
    (∀ f : Coeff, MemDot s f → RealField f → ∃ u : Path,
      SourceSol s T f u ∧ DotCont s 0 T u ∧
      (∀ v, SourceClass T f v → SameOn 0 T u v) ∧
      (∀ t ∈ Icc 0 T, dn 0 (u t) = dn 0 f) ∧ SourceApprox s T f u) ∧
    (∀ B₀ Bₛ : ℝ, 0 ≤ B₀ → 0 ≤ Bₛ → ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      (∀ f u, MemDot s f → RealField f → dn 0 f ≤ B₀ → dn s f ≤ Bₛ →
        SourceSol s T f u → DotUB s 0 T u A) ∧
      (∀ f g u v, MemDot s f → MemDot s g → RealField f → RealField g →
        dn 0 f ≤ B₀ → dn 0 g ≤ B₀ → dn s f ≤ Bₛ → dn s g ≤ Bₛ →
        SourceSol s T f u → SourceSol s T g v →
        DotUB s 0 T (fun t => u t-v t) (K*dn s (f-g))) ∧
      (∀ f : Coeff, MemDot s f → RealField f → dn 0 f ≤ B₀ → dn s f ≤ Bₛ →
        (∀ m : ℕ, ∃ z : Path, Galerkin m T f z) ∧
        (∀ m z, Galerkin m T f z → DotUB s 0 T z A)) )) ∧
  (∀ s T : ℝ, 0 < s → 0 < T → ∀ f : Coeff, MemDot s f → RealField f →
    ∀ v : ℕ → Path, (∀ m : ℕ, Galerkin m T f (v m)) →
    ∃ l : ℕ → ℕ, StrictMono l ∧ ∃ u : Path, SourceSol s T f u ∧
      WeakStarDot s T (fun n => v (l n)) (SourceTwist u) ∧
      ∀ σ q : ℝ, 0 < σ → σ < s → 1 < q → StrongTime σ q T (fun n => v (l n)) (SourceTwist u))
def EDependence : Prop :=
  ∀ B₀ θ : ℝ, 0 ≤ B₀ → -1 < θ → θ ≤ 0 → ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
    ∀ T : ℝ, 0 < T → ∀ f g u v, Data 0 f → Data 0 g →
      dn 0 f + dn 0 g ≤ B₀ → SourceSol 0 T f u → SourceSol 0 T g v →
      DotUB θ 0 T (fun t => SourceTwist u t-SourceTwist v t) (C * D^T * dn θ (f-g)) ∧
      DotUB θ 0 T (fun t => u t-v t) (C * D^T * dn θ (f-g))
def csrc : ℝ := Real.sqrt (2*Real.pi)
def srcN (s : ℝ) (f : Coeff) : ℝ := csrc * hn s f
def srcX (a b : ℝ) (f d : Path) : ℝ := csrc * Xnorm a b f d
def TriBound (c a b : ℝ) (f g h df dg dh : Path) : Prop :=
  HB 0 (tri a b f g h) (c*(b-a)*Xnorm a b f df*Xnorm a b g dg*Xnorm a b h dh +
    c*EssH (-pstar) a b f*EssH 0 a b g*EssH 0 a b h) ∧
  HB 0 (tri a b f g h) (c*(b-a)*Xnorm a b f df*Xnorm a b g dg*Xnorm a b h dh +
    c*EssH (-pstar) a b g*EssH 0 a b f*EssH 0 a b h) ∧
  HB 0 (tri a b f g h) (c*(b-a)*Xnorm a b f df*Xnorm a b g dg*Xnorm a b h dh +
    c*EssH (-pstar) a b h*EssH 0 a b f*EssH 0 a b g)
def SrcTriBound (c a b : ℝ) (f g h df dg dh : Path) : Prop :=
  MemH 0 (tri a b f g h) ∧
  (∀ i : Fin 3, let fs : Fin 3 → Path := ![f,g,h]
                srcN 0 (tri a b f g h) ≤
                  c*(b-a)*srcX a b f df*srcX a b g dg*srcX a b h dh +
                  c*(csrc*EssH (-pstar) a b (fs i)) *
                    ∏ j ∈ Finset.univ.erase i, csrc*EssH 0 a b (fs j))
def ETri : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ α a b : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ a → a ≤ b → b-a ≤ 1 →
      ∀ f g h df dg dh : Path, XPath α a b f df → XPath α a b g dg → XPath α a b h dh →
      SrcTriBound c a b f g h df dg dh) ∧
    (∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b-a ≤ 1 →
      ∀ f g h : Coeff, MemH σ f → MemH σ g → MemH σ h →
      MemH 0 (tri a b (fun _ => f) (fun _ => g) (fun _ => h)) ∧
      srcN 0 (tri a b (fun _ => f) (fun _ => g) (fun _ => h)) ≤
        C*(b-a)^σ*srcN σ f*srcN σ g*srcN σ h)
def beta0 (σ ε : ℝ) : ℝ := if σ < 1/2 then 2*σ-3/2 else if σ = 1/2 then -1/2-ε else σ-1
def aprod (σ ε : ℝ) : ℝ := if σ = 0 then 1/2+ε else if σ < 1/2 then 1/2-σ else if σ = 1/2 then ε else 0
def EStage : Prop :=
  ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β : ℝ, beta0 σ ε ≤ β → β ≤ 1+σ →
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → ∀ n : ℕ, ∀ t : ℝ,
    (n : ℝ)*τ ≤ t → t ≤ (n : ℝ)*τ+τ →
    ∀ f g : Coeff, MemH σ f → MemH σ g → ZeroMean f → ZeroMean g →
    MemH β (stage ((n : ℝ)*τ) t f g) ∧
    srcN β (stage ((n : ℝ)*τ) t f g) ≤ C*τ^((1+σ-β)/(1+σ-beta0 σ ε))*srcN σ f*srcN σ g
def EProduct : Prop :=
  ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ C : ℝ, 0 < C ∧
    ∀ f g : Coeff, MemH σ f → MemH (aprod σ ε) g →
    MemH 0 (mul f g) ∧ srcN 0 (mul f g) ≤ C*srcN σ f*srcN (aprod σ ε) g
def Endpoint : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ n : ℕ, ∀ f : Coeff, Data 0 f → Smooth f →
    S (-((n : ℝ)+1)*τ) (psi τ (S ((n : ℝ)*τ) f)) =
      f + stage ((n : ℝ)*τ) (((n : ℝ)+1)*τ) f f +
      Cst ((n : ℝ)*τ) f (((n : ℝ)+1)*τ) - rem ((n : ℝ)*τ) τ f f f
end KdVPlan

namespace KdVPlan
def FromLP (s : ℝ) (x : lp (fun _ : ℤ => ℂ) 2) : Coeff := fun k => (weight (-s/2) k : ℂ)*x k
def SeqConv (s : ℝ) (f : ℕ → Coeff) (g : Coeff) : Prop :=
  MemH s g ∧ ∀ ε > 0, ∃ m : ℕ, ∀ n ≥ m, HB s (f n-g) ε
def SobolevInfrastructure : Prop :=
  (∀ s f, MemH s f ↔ ∃ x : lp (fun _ : ℤ => ℂ) 2, f = FromLP s x) ∧
  (∀ s (x : lp (fun _ : ℤ => ℂ) 2), hn s (FromLP s x) = ‖x‖) ∧
  (∀ s f, MemH s f → SeqConv s (fun n : ℕ => cutoff (n : ℝ) f) f) ∧
  (∀ q r f, q ≤ r → MemH r f → HB q f (hn r f)) ∧
  (∀ s (f : ℕ → Coeff), (∀ n, MemH s (f n)) →
    (∀ ε > 0, ∃ m : ℕ, ∀ n ≥ m, ∀ j ≥ m, HB s (f n-f j) ε) →
    ∃ g, SeqConv s f g)
def MOf (T γ : ℝ) (u : Path) : ℝ := 1+SupH γ 0 T (Twist u)
def FlowOutput (T γ R : ℝ) : Prop :=
  (∃ A : ℝ, 0 ≤ A ∧ ∀ f : Coeff, Data γ f → hn γ f ≤ R →
    ∃ u : Path, Exact γ T f u ∧ UB γ 0 T u A ∧ UB γ 0 T (Twist u) A ∧ MOf T γ u ≤ 1+A ∧
      (Smooth f → SmoothOn 0 T u ∧ SmoothOn 0 T (Twist u) ∧
        ∀ t ∈ Ioo 0 T, dt (Twist u) t = scale (1/2) (B t (Twist u t) (Twist u t)))) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ f g : Coeff, Data 0 f → Data 0 g → hn 0 f+hn 0 g ≤ 2*R →
    ∃ u v : Path, Exact 0 T f u ∧ Exact 0 T g v ∧
      UB 0 0 T (fun t => u t-v t) (K*hn 0 (f-g)) ∧
      UB 0 0 T (fun t => Twist u t-Twist v t) (K*hn 0 (f-g)))
def CovarianceBounds : Prop :=
  ∀ τ α β : ℝ, 0 < τ →
    (α*β = 0 → eta τ α β = 0) ∧
    (α*β ≠ 0 → ‖eta τ α β‖ ≤ 2*min |α/β| |β/α| ∧
      ‖eta τ α β‖ ≤ τ*min |α| |β|)
def n1 (a b c d : ℤ) : ℝ := max (max |(a : ℝ)| |(b : ℝ)|) (max |(c : ℝ)| |(d : ℝ)|)
def n2 (a b c d : ℤ) : ℝ :=
  max (min |(a : ℝ)| |(b : ℝ)|)
    (max (min |(a : ℝ)| |(c : ℝ)|)
      (max (min |(a : ℝ)| |(d : ℝ)|)
        (max (min |(b : ℝ)| |(c : ℝ)|) (max (min |(b : ℝ)| |(d : ℝ)|) (min |(c : ℝ)| |(d : ℝ)|)))))
def n3 (a b c d : ℤ) : ℝ :=
  min (max |(a : ℝ)| |(b : ℝ)|)
    (min (max |(a : ℝ)| |(c : ℝ)|)
      (min (max |(a : ℝ)| |(d : ℝ)|)
        (min (max |(b : ℝ)| |(c : ℝ)|) (min (max |(b : ℝ)| |(d : ℝ)|) (max |(c : ℝ)| |(d : ℝ)|)))))
def Interaction (a b c d : ℤ) : Prop := a+b+c+d = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0
def NonnegL2 (x : ℤ → ℝ) : Prop := x 0 = 0 ∧ (∀ k, 0 ≤ x k) ∧ Summable (fun k => x k ^ 2)
def seqN (x : ℤ → ℝ) : ℝ := Real.sqrt (∑' k, x k^2)
def quadTerm (A : Set (ℤ × ℤ × ℤ)) (x₁ x₂ x₃ x₄ : ℤ → ℝ) (z : ℤ × ℤ × ℤ) : ℝ :=
  let a := z.1; let b := z.2.1; let c := z.2.2; let d := -a-b-c
  @ite ℝ (z ∈ A ∧ Interaction a b c d) (Classical.propDecidable _) (x₁ a*x₂ b*x₃ c*x₄ d/n3 a b c d) 0
def FourFrequency : Prop :=
  (∀ a b c d : ℤ, Interaction a b c d →
    n1 a b c d ≤ 3*n2 a b c d ∧
    (1/|(d : ℝ)|)*min (|(a : ℝ)*(b : ℝ)|/|(c : ℝ)*(d : ℝ)| : ℝ) (|(c : ℝ)*(d : ℝ)|/|(a : ℝ)*(b : ℝ)| : ℝ) ≤ 3/n3 a b c d ∧
    |(a : ℝ)+(b : ℝ)| / max (|(a : ℝ)*(b : ℝ)| : ℝ) (|(c : ℝ)*(d : ℝ)| : ℝ) ≤ 6/n3 a b c d) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ x₁ x₂ x₃ x₄ : ℤ → ℝ,
    NonnegL2 x₁ → NonnegL2 x₂ → NonnegL2 x₃ → NonnegL2 x₄ →
    ∀ A : Set (ℤ × ℤ × ℤ), Summable (quadTerm A x₁ x₂ x₃ x₄) ∧
      (∑' z, quadTerm A x₁ x₂ x₃ x₄ z) ≤ C*seqN x₁*seqN x₂*seqN x₃*seqN x₄ ∧
      (∑' z, quadTerm A x₁ x₂ x₃ x₄ z) =
        sSup {r | ∃ F : Finset (ℤ × ℤ × ℤ), r = ∑ z ∈ F, quadTerm A x₁ x₂ x₃ x₄ z}
def Poly (f : Coeff) : Prop := (Function.support f).Finite
def TriLinearOn (s : ℝ) (A : Coeff → Coeff → Coeff → Coeff) : Prop :=
  ∀ f f' g g' h h' : Coeff,
    MemH s f → MemH s f' → MemH s g → MemH s g' → MemH s h → MemH s h' →
    ZeroMean f → ZeroMean f' → ZeroMean g → ZeroMean g' → ZeroMean h → ZeroMean h' →
    A (f+f') g h = A f g h + A f' g h ∧
    A f (g+g') h = A f g h + A f g' h ∧
    A f g (h+h') = A f g h + A f g h' ∧
    ∀ z : ℂ, A (scale z f) g h = scale z (A f g h) ∧
      A f (scale z g) h = scale z (A f g h) ∧ A f g (scale z h) = scale z (A f g h)
def BoundedTri (s : ℝ) (A : Coeff → Coeff → Coeff → Coeff) : Prop :=
  TriLinearOn s A ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h,
    MemH s f → MemH s g → MemH s h → ZeroMean f → ZeroMean g → ZeroMean h →
    HB 0 (A f g h) (C*hn s f*hn s g*hn s h)
def RemainderBound : Prop :=
  (∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∃ C : ℝ, 0 < C ∧
    ∀ χ : ℤ → ℤ → ℤ → ℂ, (∀ a b c, ‖χ a b c‖ ≤ 1) →
    ∀ a τ : ℝ, 0 ≤ a → 0 < τ →
      BoundedTri σ (remWith χ a τ) ∧
      (∀ f g h, MemH σ f → MemH σ g → MemH σ h → ZeroMean f → ZeroMean g → ZeroMean h →
        HB 0 (remWith χ a τ f g h) (C*τ^(1+σ)*hn σ f*hn σ g*hn σ h)) ∧
      (∀ A : Coeff → Coeff → Coeff → Coeff, BoundedTri σ A →
        (∀ f g h, Poly f → Poly g → Poly h → ZeroMean f → ZeroMean g → ZeroMean h →
          A f g h = remWith χ a τ f g h) →
        ∀ f g h, MemH σ f → MemH σ g → MemH σ h → ZeroMean f → ZeroMean g → ZeroMean h →
          A f g h = remWith χ a τ f g h))
def MultiplierBound : Prop :=
  (∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 → 0 < τ →
    ∀ a b c : ℤ, let k := a+b+c
    Interaction a b c (-k) → a+b ≠ 0 →
      ‖eta τ (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ)) (3*(k : ℝ)*(c : ℝ)*(a+b : ℤ))‖ /
        (|(k : ℝ)| * |(a : ℝ)*(b : ℝ)*(c : ℝ)|^σ) ≤ 6^(1-σ)*18^σ*τ^σ/n3 a b c (-k))
def MixedRemainderBound : Prop :=
  (∀ σ M : ℝ, 0 < σ → σ ≤ 1 → 0 ≤ M → ∃ C : ℝ, 0 < C ∧
    ∀ a τ : ℝ, 0 ≤ a → 0 < τ → τ ≤ 1 → ∀ f w : Coeff,
    MemH 0 f → ZeroMean f → MemH σ w → ZeroMean w → hn σ w ≤ M → hn 0 (f-w) ≤ 1 →
    HB 0 (rem a τ f f f) (C*τ*(τ^σ+hn 0 (f-w))))
def RemOutput : Prop := RemainderBound ∧ MultiplierBound ∧ MixedRemainderBound
def ContinuousMapH (s r : ℝ) (A : Coeff → Coeff) (guard : Coeff → Prop) : Prop :=
  ∀ f, MemH s f → guard f → MemH r (A f) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ g, MemH s g → guard g → hn s (g-f) < δ → hn r (A g-A f) < ε
def NormalForm : Prop :=
  (∀ t f g, MemH 0 f → MemH 0 g → ZeroMean f → ZeroMean g → J t f g = J t g f) ∧
  (∀ a b f g, a ≤ b → Piecewise a b f → Piecewise a b g →
    (∀ t ∈ Icc a b, ZeroMean (f t)) → (∀ t ∈ Icc a b, ZeroMean (g t)) →
    timeInt a b (fun t => B t (f t) (g t)) =
      scale (1/3) (J b (f b) (g b)-J a (f a) (g a)) -
      scale (1/3) (timeInt a b (fun t => J t (dt f t) (g t)+J t (f t) (dt g t)))) ∧
  (∀ a b f g h, a ≤ b → Piecewise a b f → Piecewise a b g → Piecewise a b h →
    (∀ t ∈ Icc a b, ZeroMean (f t) ∧ ZeroMean (g t) ∧ ZeroMean (h t)) →
    timeInt a b (fun t => J t (B t (f t) (g t)) (h t)) = tri a b f g h) ∧
  (∀ a t f g, a ≤ t → MemH 0 f → MemH 0 g → ZeroMean f → ZeroMean g →
    stage a t f g = scale (1/6) (J t f g-J a f g))
def FourierApprox2 (s r q : ℝ) (A : Coeff → Coeff → Coeff) : Prop :=
  ∀ f g, MemH s f → MemH r g →
    SeqConv q (fun n : ℕ => A (cutoff (n : ℝ) f) (cutoff (n : ℝ) g)) (A f g)
def BilinearExtensions : Prop :=
  (∀ f, MemH 0 f → SeqConv 1 (fun n : ℕ => invD (cutoff (n : ℝ) f)) (invD f)) ∧
  FourierApprox2 1 1 1 mul ∧
  (∀ t : ℝ, FourierApprox2 0 0 (-pstar) (B t) ∧ FourierApprox2 0 0 1 (J t)) ∧
  FourierApprox2 0 0 0 (fun f g => invD (P (mul f g)))
def BasicBilinearBounds : Prop :=
  (∃ C : ℝ, 0 < C ∧
    (∀ f, MemH 0 f → ZeroMean f → HB 1 (invD f) (C*hn 0 f) ∧ LinftyBound (invD f) (C*hn 0 f)) ∧
    (∀ f g, MemH 1 f → MemH 1 g → HB 1 (mul f g) (C*hn 1 f*hn 1 g)) ∧
    (∀ t f g, MemH 0 f → MemH 0 g →
      HB (-pstar) (B t f g) (C*hn 0 f*hn 0 g) ∧ HB 1 (J t f g) (C*hn 0 f*hn 0 g) ∧
      HB 0 (invD (P (mul f g))) (C*hn 0 f*hn 0 g)) ∧
    (∀ t A g, ZeroMean A → MemH 0 (invD A) → MemH 0 g →
      HB (-pstar) A (hn 0 (invD A)) ∧ HB 0 (J t A g) (C*hn 0 (invD A)*hn 0 g))) ∧ BilinearExtensions
def BilinearOutput : Prop := BasicBilinearBounds ∧ NormalForm
def FourierApprox3 (s : ℝ) (A : Coeff → Coeff → Coeff → Coeff) : Prop :=
  ∀ f g h, MemH s f → MemH s g → MemH s h → ZeroMean f → ZeroMean g → ZeroMean h →
    SeqConv 0 (fun n : ℕ => A (cutoff (n : ℝ) f) (cutoff (n : ℝ) g) (cutoff (n : ℝ) h)) (A f g h)
def XConvergence (a b : ℝ) (v : ℕ → Path) (u du : Path) : Prop :=
  XPath 0 a b u du ∧
  (∀ n : ℕ, Piecewise a b (v n) ∧ XPath 0 a b (fun t => v n t-u t) (fun t => dt (v n) t-du t)) ∧
  ∀ ε > 0, ∃ m : ℕ, ∀ n ≥ m,
    Xnorm a b (fun t => v n t-u t) (fun t => dt (v n) t-du t) < ε
def TriExtensions : Prop :=
  (∀ σ a b : ℝ, 0 ≤ σ → σ ≤ 1 → 0 ≤ a → a ≤ b → b-a ≤ 1 →
    FourierApprox3 σ (fun f g h => tri a b (fun _ => f) (fun _ => g) (fun _ => h))) ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ b → b-a ≤ 1 →
    ∀ (fn gn hn : ℕ → Path) (f g h df dg dh : Path),
    XConvergence a b fn f df → XConvergence a b gn g dg → XConvergence a b hn h dh →
    (∀ n : ℕ, ∀ t ∈ Icc a b, ZeroMean (fn n t) ∧ ZeroMean (gn n t) ∧ ZeroMean (hn n t)) →
    SeqConv 0 (fun n : ℕ => tri a b (fn n) (gn n) (hn n)) (tri a b f g h))
def StageExtensions (γ : ℝ) : Prop :=
  ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ a+1 →
    ∀ w, MemH γ w → ZeroMean w →
      SeqConv (ag γ) (fun n : ℕ => stage a t (cutoff (n : ℝ) w) (cutoff (n : ℝ) w)) (stage a t w w) ∧
      SeqConv (1+γ) (fun n : ℕ => stage a t (cutoff (n : ℝ) w) (cutoff (n : ℝ) w)) (stage a t w w)
def NormalizedTri : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b-a ≤ 1 →
    ∀ f g h : Path, Piecewise a b f → Piecewise a b g → Piecewise a b h →
    (∀ t ∈ Icc a b, ZeroMean (f t) ∧ ZeroMean (g t) ∧ ZeroMean (h t)) →
    TriBound C a b f g h (dt f) (dt g) (dt h)) ∧
  (∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∃ C : ℝ, 0 < C ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b-a ≤ 1 → ∀ f g h,
    MemH σ f → MemH σ g → MemH σ h → ZeroMean f → ZeroMean g → ZeroMean h →
    HB 0 (tri a b (fun _ => f) (fun _ => g) (fun _ => h)) (C*(b-a)^σ*hn σ f*hn σ g*hn σ h)) ∧ TriExtensions
def ProductOutput (γ : ℝ) : Prop :=
  (0 ≤ ag γ ∧ ag γ < 1) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ f g, MemH γ f → MemH (ag γ) g → HB 0 (mul f g) (C*hn γ f*hn (ag γ) g))
def StageEstimates (γ : ℝ) : Prop :=
  (∀ M : ℝ, 0 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ a τ t : ℝ,
    0 ≤ a → 0 < τ → τ ≤ 1 → a ≤ t → t ≤ a+τ →
    ∀ w, MemH γ w → ZeroMean w → hn γ w ≤ M →
    HB (ag γ) (stage a t w w) (C*τ^γ) ∧ HB (1+γ) (stage a t w w) C) ∧ StageExtensions γ
def ContinuousOutput (γ : ℝ) : Prop := NormalizedTri ∧ ProductOutput γ ∧ StageEstimates γ
def SchemeOutput : Prop :=
  (∀ τ : ℝ, 0 < τ →
    ContinuousMapH 0 0 (psi τ) (fun f => ZeroMean f ∧ RealField f) ∧
    ContinuousMapH 0 1 (Ftau τ) ZeroMean ∧
    (∀ f, Data 0 f → Data 0 (psi τ f) ∧ (Smooth f → Smooth (psi τ f))) ∧
    (∀ n : ℕ, ContinuousMapH 0 0 (fun f => numerical τ f n) (fun f => ZeroMean f ∧ RealField f))) ∧
  Endpoint ∧
  (∀ (τ : ℝ) (f : Coeff) (n : ℕ), 0 < τ → Data 0 f → Smooth f →
    Vst ((n : ℝ)*τ) τ (twistedNum τ f n) ((n : ℝ)*τ) = twistedNum τ f n ∧
    Vst ((n : ℝ)*τ) τ (twistedNum τ f n) (((n : ℝ)+1)*τ) = twistedNum τ f (n+1)) ∧
  (∀ (τ : ℝ) (f : Coeff) (L : ℕ), 0 < τ → Data 0 f → Smooth f →
    Piecewise 0 ((L : ℝ)*τ) (interp τ f) ∧ RealPath 0 ((L : ℝ)*τ) (interp τ f) ∧
    ∀ n : ℕ, n ≤ L → interp τ f ((n : ℝ)*τ) = twistedNum τ f n)
end KdVPlan

namespace KdVPlan
def localQ (γ τ : ℝ) (f w : Coeff) : ℝ := τ^γ+hn 0 (f-w)
def StepData (γ M a τ : ℝ) (f w : Coeff) : Prop :=
  1 ≤ M ∧ 0 ≤ a ∧ 0 < τ ∧ τ ≤ 1 ∧ Data 0 f ∧ Data γ w ∧ Smooth f ∧ Smooth w ∧
  hn γ w ≤ M ∧ hn 0 (f-w) ≤ 1
def LocalBounds (C γ M a τ : ℝ) (f w : Coeff) : Prop :=
  let q := localQ γ τ f w
  hn 0 f ≤ M+1 ∧ q ≤ 2 ∧
  UB 1 a (a+τ) (F a f) C ∧
  UB 1 a (a+τ) (fun t => F a f t-stage a t w w) (C*hn 0 (f-w)) ∧
  (∀ t ∈ Icc a (a+τ), hn (ag γ) (F a f t)+hn 0 (F a f t) ≤ C*q ∧ MemH (ag γ) (F a f t)) ∧
  XPath 0 a (a+τ) (z a f) (dt (z a f)) ∧ Xnorm a (a+τ) (z a f) (dt (z a f)) ≤ C ∧
  UB 0 a (a+τ) (fun t => B t (F a f t) (F a f t)) (C*q) ∧
  (∀ t ∈ Icc a (a+τ), MemH 0 (Qst a f t) ∧ MemH 0 (Wst a τ f) ∧
    hn 0 (Qst a f t)+hn 0 (Wst a τ f) ≤ C*τ*q) ∧
  UB 0 a (a+τ) (fun t => invD (B t f (F a f t))) (C*q) ∧
  (∀ t ∈ Ioo a (a+τ), dt (Yst a τ f) t = B t f (F a f t)+
    scale (1/2) (B t (F a f t) (F a f t))-scale ((τ : ℂ)⁻¹) (Wst a τ f)) ∧
  UB 0 a (a+τ) (fun t => invD (Yst a τ f t)) (C*τ*q) ∧
  (∀ᵐ t ∂(volume.restrict (Icc a (a+τ))), HB 0 (invD (dt (Yst a τ f) t)) (C*q)) ∧
  (∀ t ∈ Icc a (a+τ), Cst a f t = scale (1/3) (J t f (F a f t)) -
    scale (1/6) (tri a t (fun _ => f) (fun _ => f) (fun _ => f))) ∧
  UB 0 a (a+τ) (Yst a τ f) (C*q) ∧
  XPath 0 a (a+τ) (Yst a τ f) (dt (Yst a τ f)) ∧
  Xnorm a (a+τ) (Yst a τ f) (dt (Yst a τ f)) ≤ C*q ∧
  UB (-pstar) a (a+τ) (Yst a τ f) (C*τ*q)
def StageOutput (γ : ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ a τ f w, StepData γ M a τ f w → LocalBounds C γ M a τ f w
def TwistedExact (γ M H : ℝ) (v : Path) : Prop :=
  SmoothOn 0 H v ∧ RealPath 0 H v ∧ UB γ 0 H v M ∧
  ∀ t ∈ Ioo 0 H, dt v t = scale (1/2) (B t (v t) (v t))
def Traj (γ M τ : ℝ) (L : ℕ) (f : Coeff) (v : Path) : Prop :=
  Data 0 f ∧ Smooth f ∧ TwistedExact γ M ((L : ℝ)*τ) v
def GridInterval (τ : ℝ) (L : ℕ) (a b : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ b ≤ (L : ℝ)*τ ∧ ∃ n : ℕ, n ≤ L ∧ a = (n : ℝ)*τ
def err (τ : ℝ) (f : Coeff) (v : Path) : Path := fun t => v t-interp τ f t
def enorm (a b τ : ℝ) (f : Coeff) (v : Path) : ℝ := SupH 0 a b (err τ f v)
def StepResidual (C γ a τ : ℝ) (f w : Coeff) : Prop :=
  let q := localQ γ τ f w
  (∀ t ∈ Ioo a (a+τ),
    dt (Vst a τ f) t = scale (1/2) (B t (Vst a τ f t) (Vst a τ f t))+dt (rho a τ f) t ∧
    dt (rho a τ f) t = -B t (Yst a τ f t) (z a f t) -
      scale (1/2) (B t (Yst a τ f t) (Yst a τ f t))-scale ((τ : ℂ)⁻¹) (Wst a τ f)) ∧
  UB 0 a (a+τ) (rho a τ f) (C*τ*q) ∧
  EssBound (-pstar) a (a+τ) (dt (rho a τ f)) ∧ EssH (-pstar) a (a+τ) (dt (rho a τ f)) ≤ C*q
def AccResidual (C γ τ : ℝ) (L : ℕ) (f : Coeff) (v : Path) : Prop :=
  Piecewise 0 ((L : ℝ)*τ) (interp τ f) ∧ RealPath 0 ((L : ℝ)*τ) (interp τ f) ∧
  Weak 0 ((L : ℝ)*τ) (interp τ f)
    (fun t => scale (1/2) (B t (interp τ f t) (interp τ f t))+dt (residual τ f) t) ∧
  residual τ f 0 = 0 ∧
  (∀ n : ℕ, n ≤ L → interp τ f ((n : ℝ)*τ) = twistedNum τ f n) ∧
  ∀ a b : ℝ, GridInterval τ L a b → b-a ≤ 1 → enorm a b τ f v ≤ 1 →
    UB 0 a b (fun t => residual τ f t-residual τ f a)
      (C*(b-a+τ)*(τ^γ+enorm a b τ f v)) ∧
    EssBound (-pstar) a b (dt (residual τ f)) ∧
    EssH (-pstar) a b (dt (residual τ f)) ≤ C*(τ^γ+enorm a b τ f v) ∧
    XPath 0 a b (err τ f v) (dt (err τ f v)) ∧
    Xnorm a b (err τ f v) (dt (err τ f v)) ≤ C*(τ^γ+enorm a b τ f v) ∧
    XPath 0 a b v (dt v) ∧ XPath 0 a b (interp τ f) (dt (interp τ f)) ∧
    Xnorm a b v (dt v)+Xnorm a b (interp τ f) (dt (interp τ f)) ≤ C
def ResidualOutput (γ : ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧
    (∀ a τ f w, StepData γ M a τ f w → StepResidual C γ a τ f w) ∧
    (∀ (τ : ℝ) (L : ℕ) (f : Coeff) (v : Path), 0 < τ → τ ≤ 1 →
      Traj γ M τ L f v → AccResidual C γ τ L f v)
def errorF (a τ : ℝ) (f : Coeff) (v : Path) : Path :=
  fun t => timeInt a t (fun s => B s (err τ f v s) (v s-scale (1/2) (err τ f v s)))
def StabilityEstimates (C γ τ a b : ℝ) (f : Coeff) (v : Path) : Prop :=
  let e := err τ f v
  let g : Path := fun t => v t-scale (1/2) (e t)
  let E := enorm a b τ f v
  let h := b-a
  (∀ t ∈ Icc a b, e t = e a + errorF a τ f v t-(residual τ f t-residual τ f a)) ∧
  (∀ N : ℝ, 2 ≤ N →
    UB 0 a b (fun t => cutoff N (errorF a τ f v t)) (C*N^2*h*E) ∧
    (∀ t ∈ Icc a b, errorF a τ f v t =
      scale (1/3) (J t (e t) (g t)-J a (e a) (g a)) -
      scale (1/3) (tri a t e g (interp τ f)) -
      scale (1/6) (tri a t v v e) +
      scale (1/3) (timeInt a t (fun s => J s (dt (residual τ f) s) (interp τ f s)))) ∧
    UB 0 a b (fun t => high N (errorF a τ f v t))
      (C*(h+τ)*τ^γ+C*(h+τ+N⁻¹+N^(-pstar))*E) ∧
    E ≤ hn 0 (e a)+C*(h+τ)*τ^γ+C*(N^2*h+h+τ+N⁻¹+N^(-pstar))*E)
def StabilityOutput (γ : ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M →
    (∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (L : ℕ) (f : Coeff) (v : Path) (a b : ℝ),
      0 < τ → τ ≤ 1 → Traj γ M τ L f v → GridInterval τ L a b →
      b-a ≤ 1 → enorm a b τ f v ≤ 1 → StabilityEstimates C γ τ a b f v) ∧
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧
      ∀ (τ : ℝ) (L : ℕ) (f : Coeff) (v : Path) (a b : ℝ),
      0 < τ → τ ≤ δ/2 → Traj γ M τ L f v → GridInterval τ L a b →
      b-a ≤ δ → enorm a b τ f v ≤ 1 →
      enorm a b τ f v ≤ 2*hn 0 (err τ f v a)+K*δ*τ^γ
def GridError (C γ τ : ℝ) (L : ℕ) (f : Coeff) (u : Path) : Prop :=
  ∀ n : ℕ, n ≤ L →
    Data 0 (numerical τ f n) ∧ HB 0 (u ((n : ℝ)*τ)-numerical τ f n) (C*τ^γ)
def SmoothOutput (T γ R : ℝ) : Prop :=
  ∃ C τ₀ : ℝ, 0 < C ∧ 0 < τ₀ ∧ ∀ f : Coeff, Data γ f → Smooth f → hn γ f ≤ R →
    ∀ L : ℕ, 0 < L → T/(L : ℝ) ≤ τ₀ → ∃ u : Path, Exact γ T f u ∧
      UB 0 0 T (fun t => Twist u t-interp (T/(L : ℝ)) f t) (C*(T/(L : ℝ))^γ) ∧
      GridError C γ (T/(L : ℝ)) L f u
def Target (T γ R : ℝ) : Prop :=
  ∃ C τ₀ : ℝ, 0 < C ∧ 0 < τ₀ ∧ ∀ f : Coeff, Data γ f → hn γ f ≤ R →
    ∀ L : ℕ, 0 < L → T/(L : ℝ) ≤ τ₀ → ∃ u : Path, Exact γ T f u ∧ GridError C γ (T/(L : ℝ)) L f u
end KdVPlan

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), KdVPlan.rho a τ f a = 0" := by
  intro a τ f
  ext k
  simp [KdVPlan.rho, KdVPlan.timeInt, KdVPlan.scale]

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ a τ f w, KdVPlan.StepData gamma M a τ f w → (∀ t ∈ Set.Ioo a (a+τ), KdVPlan.dt (KdVPlan.Yst a τ f) t = KdVPlan.B t f (KdVPlan.F a f t) + KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.F a f t) (KdVPlan.F a f t)) - KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst a τ f))" := by
  intro M hM
  obtain ⟨C, hC, h⟩ := h_T008 M hM
  refine ⟨C, hC, ?_⟩
  intro a τ f w hs
  have hb := h a τ f w hs
  exact hb.2.2.2.2.2.2.2.2.2.2.1

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.MemH s (f+g) ∧ KdVPlan.hn s (f+g) ≤ KdVPlan.hn s f+KdVPlan.hn s g" := by
  intro s f g hf hg
  obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
  obtain ⟨y, rfl⟩ := (h_T013.1 s g).mp hg
  have he : KdVPlan.FromLP s x + KdVPlan.FromLP s y = KdVPlan.FromLP s (x+y) := by
    funext k
    simp [KdVPlan.FromLP, mul_add]
  rw [he]
  constructor
  · exact (h_T013.1 s _).mpr ⟨x+y, rfl⟩
  · simpa only [h_T013.2.1 s] using norm_add_le x y

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ), Function.Injective (KdVPlan.FromLP s)" := by
  intro s x y h
  apply Subtype.ext
  funext k
  have hk := congrFun h k
  have hw : (KdVPlan.weight (-s/2) k : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold KdVPlan.weight
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  exact mul_left_cancel₀ hw hk

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (c : ℂ), KdVPlan.MemH s f → KdVPlan.MemH s (KdVPlan.scale c f) ∧ KdVPlan.hn s (KdVPlan.scale c f) = ‖c‖*KdVPlan.hn s f" := by
  intro s f c hf
  obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
  have he : KdVPlan.scale c (KdVPlan.FromLP s x) = KdVPlan.FromLP s (c • x) := by
    funext k
    simp [KdVPlan.FromLP, KdVPlan.scale, mul_left_comm]
  rw [he]
  constructor
  · exact (h_T013.1 s _).mpr ⟨c • x, rfl⟩
  · simpa only [h_T013.2.1 s] using norm_smul c x

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.MemH s (f-g) ∧ KdVPlan.hn s (f-g) ≤ KdVPlan.hn s f+KdVPlan.hn s g" := by
  intro s f g hf hg
  have hng := @yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s g (-1) hg
  have he : KdVPlan.scale (-1) g = -g := by funext k; simp [KdVPlan.scale]
  rw [he] at hng
  have hh := @yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f (-g) hf hng.1
  simpa [sub_eq_add_neg, hng.2] using hh

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (x y : lp (fun _ : ℤ => ℂ) 2), KdVPlan.FromLP s (x-y) = KdVPlan.FromLP s x-KdVPlan.FromLP s y" := by
  intro s x y
  funext k
  simp [KdVPlan.FromLP, mul_sub]

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, ∃ L : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2, (∀ f, KdVPlan.MemH s f → KdVPlan.FromLP s (L f) = f ∧ ‖L f‖ = KdVPlan.hn s f) ∧ (∀ f g, KdVPlan.MemH s f → KdVPlan.MemH s g → ‖L f-L g‖ = KdVPlan.hn s (f-g))" := by
  classical
  intro s
  let L : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2 := fun f => if hf : KdVPlan.MemH s f then Classical.choose ((h_T013.1 s f).mp hf) else 0
  have hL : ∀ f, KdVPlan.MemH s f → KdVPlan.FromLP s (L f) = f := by
    intro f hf
    dsimp [L]
    rw [dif_pos hf]
    exact (Classical.choose_spec ((h_T013.1 s f).mp hf)).symm
  refine ⟨L, ?_, ?_⟩
  · intro f hf
    refine ⟨hL f hf, ?_⟩
    rw [← h_T013.2.1 s, hL f hf]
  · intro f g hf hg
    have he : KdVPlan.FromLP s (L f-L g) = f-g := by
      rw [@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, hL f hf, hL g hg]
    rw [← h_T013.2.1 s, he]

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (L : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2), (∀ f g, KdVPlan.MemH s f → KdVPlan.MemH s g → ‖L f-L g‖ = KdVPlan.hn s (f-g)) → ∀ u : KdVPlan.Path, KdVPlan.ContH s a b u → ContinuousOn (fun t => L (u t)) (Set.Icc a b)" := by
  intro s a b L hL u hu
  apply Metric.continuousOn_iff.mpr
  intro t ht ε hε
  obtain ⟨δ, hδ, hd⟩ := hu.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [dist_eq_norm, hL _ _ (hu.1 r hr) (hu.1 t ht)]
  exact hd r hr (by simpa only [Real.dist_eq] using hrt)

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path) (U : ℝ → lp (fun _ : ℤ => ℂ) 2), a ≤ b → IntervalIntegrable U MeasureTheory.volume a b → (∀ t ∈ Set.Icc a b, KdVPlan.FromLP s (U t) = u t) → KdVPlan.FromLP s (∫ t in a..b, U t) = KdVPlan.timeInt a b u" := by
  intro s a b u U hab hU he
  funext k
  let A : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ := (KdVPlan.weight (-s/2) k : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k
  change A (∫ t in a..b, U t) = ∫ t in a..b, u t k
  rw [← A.intervalIntegral_comp_comm hU]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using ht
  exact congrFun (he t ht') k

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ a b t : ℝ, a ≤ b → t ∈ Set.uIoc a b → t ∈ Set.Icc a b" := by
  intro a b t hab ht
  have hh : a < t ∧ t ≤ b := by simpa only [Set.uIoc, Set.mem_Ioc, min_eq_left hab, max_eq_right hab] using ht
  exact ⟨hh.1.le, hh.2⟩

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (u : KdVPlan.Path), a ≤ b → KdVPlan.ContH s a b u → KdVPlan.UB s a b u C → KdVPlan.HB s (KdVPlan.timeInt a b u) ((b-a)*C)" := by
  intro s a b C u hab hc hb
  obtain ⟨L, hL, hD⟩ := @yui_aux_0008 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s
  have hcont := @yui_aux_0009 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b L hD u hc
  have hint := hcont.intervalIntegrable_of_Icc hab (μ := MeasureTheory.volume)
  have he := @yui_aux_0010 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b u (fun t => L (u t)) hab hint (fun t ht => (hL (u t) (hc.1 t ht)).1)
  constructor
  · exact (h_T013.1 s _).mpr ⟨∫ t in a..b, L (u t), he.symm⟩
  · rw [← he, h_T013.2.1 s]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := fun t => L (u t)) (C := C) (by
      intro t ht
      have ht' : t ∈ Set.Icc a b := @yui_aux_0011 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b t hab ht
      rw [(hL (u t) (hc.1 t ht')).2]
      exact (hb t ht').2)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm C] using hnorm

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (u : KdVPlan.Path), 0 ≤ C → (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)), KdVPlan.HB s (u t) C) → (essSup (fun t => ENNReal.ofReal (KdVPlan.hn s (u t))) (MeasureTheory.volume.restrict (Set.Icc a b)) < (⊤ : ℝ≥0∞)) ∧ KdVPlan.EssH s a b u ≤ C" := by
  intro s a b C u hC hu
  have hb : essSup (fun t => ENNReal.ofReal (KdVPlan.hn s (u t))) (MeasureTheory.volume.restrict (Set.Icc a b)) ≤ ENNReal.ofReal C := by
    refine essSup_le_of_ae_le (ENNReal.ofReal C) ?_
    filter_upwards [hu] with t ht
    exact ENNReal.ofReal_le_ofReal ht.2
  refine ⟨hb.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  unfold KdVPlan.EssH
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal hC] using hr

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → ∀ k : ℤ, Summable (fun j : ℤ => f j*g (k-j))" := by
  intro f g hf hg k
  have hf' : Summable (fun j : ℤ => ‖f j‖^2) := by simpa [KdVPlan.MemH, KdVPlan.weight] using hf
  have hg' : Summable (fun j : ℤ => ‖g j‖^2) := by simpa [KdVPlan.MemH, KdVPlan.weight] using hg
  let e : ℤ ≃ ℤ := ⟨fun j => k-j, fun j => k-j, by intro j; dsimp; omega, by intro j; dsimp; omega⟩
  have hge : Summable (fun j : ℤ => ‖g (k-j)‖^2) := e.summable_iff.mpr hg'
  apply (hf'.add hge).of_norm_bounded
  intro j
  rw [norm_mul]
  nlinarith [sq_nonneg (‖f j‖-‖g (k-j)‖)]

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (k : ℤ), ‖Complex.exp (Complex.I * (t*(k : ℝ)^3 : ℝ))‖ = 1" := by
  intro t k
  exact Complex.norm_exp_I_mul_ofReal (t*(k : ℝ)^3)

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s t : ℝ) (f : KdVPlan.Coeff), (KdVPlan.MemH s (KdVPlan.S t f) ↔ KdVPlan.MemH s f) ∧ KdVPlan.hn s (KdVPlan.S t f) = KdVPlan.hn s f" := by
  intro s t f
  have hnorm : ∀ k, ‖KdVPlan.S t f k‖ = ‖f k‖ := by
    intro k
    change ‖Complex.exp (Complex.I * (t*(k : ℝ)^3 : ℝ)) * f k‖ = ‖f k‖
    rw [norm_mul, @yui_aux_0015 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, one_mul]
  constructor
  · simp only [KdVPlan.MemH, hnorm]
  · simp only [KdVPlan.hn, hnorm]

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (M : ℝ), 0 < τ → KdVPlan.Traj gamma M τ L f v → KdVPlan.Piecewise 0 ((L : ℝ)*τ) (KdVPlan.interp τ f) ∧ KdVPlan.RealPath 0 ((L : ℝ)*τ) (KdVPlan.interp τ f) ∧ KdVPlan.residual τ f 0 = 0 ∧ ∀ n : ℕ, n ≤ L → KdVPlan.interp τ f ((n : ℝ)*τ) = KdVPlan.twistedNum τ f n" := by
  intro τ L f v M hτ ht
  obtain ⟨hp, hr, hg⟩ := h_T007.2.2.2 τ f L hτ ht.1 ht.2.1
  refine ⟨hp, hr, ?_, hg⟩
  have hzero : KdVPlan.gridIndex τ 0 = 0 := by simp [KdVPlan.gridIndex]
  simp only [KdVPlan.residual, hzero, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, zero_add]
  exact @yui_aux_0001 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 τ (KdVPlan.twistedNum τ f 0)

theorem yui_aux_0018 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.ContH s a b (fun _ => f)" := by
  intro s a b f hf
  refine ⟨fun _ _ => hf, ?_⟩
  intro t ht ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro r hr hrt
  simpa [KdVPlan.hn] using hε

theorem yui_aux_0019 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s a b g → KdVPlan.ContH s a b (fun t => f t+g t)" := by
  intro s a b f g hf hg
  refine ⟨fun t ht => (@yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ _ (hf.1 t ht) (hg.1 t ht)).1, ?_⟩
  intro t ht ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf.2 t ht (ε/2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg.2 t ht (ε/2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro r hr hrt
  have hfr := (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ _ (hf.1 r hr) (hf.1 t ht)).1
  have hgr := (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ _ (hg.1 r hr) (hg.1 t ht)).1
  have hh := (@yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ _ hfr hgr).2
  have he : f r+g r-(f t+g t) = (f r-f t)+(g r-g t) := by abel
  rw [he]
  have h1 := h₁ r hr (hrt.trans_le (min_le_left _ _))
  have h2 := h₂ r hr (hrt.trans_le (min_le_right _ _))
  linarith

theorem yui_aux_0020 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), KdVPlan.ContH s a b f → (∀ t ∈ Set.Icc a b, f t = g t) → KdVPlan.ContH s a b g" := by
  intro s a b f g hf he
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [← he t ht]
    exact hf.1 t ht
  · intro t ht ε hε
    obtain ⟨δ, hδ, hd⟩ := hf.2 t ht ε hε
    refine ⟨δ, hδ, ?_⟩
    intro r hr hrt
    rw [← he r hr, ← he t ht]
    exact hd r hr hrt

theorem yui_aux_0021 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (c : ℂ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s a b (fun t => KdVPlan.scale c (f t))" := by
  intro s a b c f hf
  refine ⟨fun t ht => (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ c (hf.1 t ht)).1, ?_⟩
  intro t ht ε hε
  have hden : 0 < ‖c‖+1 := by positivity
  obtain ⟨δ, hδ, hd⟩ := hf.2 t ht (ε/(‖c‖+1)) (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  have hmem := (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ _ (hf.1 r hr) (hf.1 t ht)).1
  have he : KdVPlan.scale c (f r)-KdVPlan.scale c (f t) = KdVPlan.scale c (f r-f t) := by
    funext k
    simp [KdVPlan.scale, mul_sub]
  rw [he, (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ c hmem).2]
  have hh := (lt_div_iff₀ hden).mp (hd r hr hrt)
  have hn : 0 ≤ KdVPlan.hn s (f r-f t) := Real.sqrt_nonneg _
  nlinarith

theorem yui_aux_0022 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (c : ℂ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b (fun t => KdVPlan.scale c (f t))" := by
  intro a b c f hf
  constructor
  · intro k
    exact contDiffOn_const.mul (hf.1 k)
  · intro m j
    have hc := @yui_aux_0021 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b c _ (hf.2 m j)
    convert hc using 1
    funext t k
    exact iteratedDerivWithin_const_mul_field c (fun r => f r k)

theorem yui_aux_0023 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ j : ℕ, (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)" := by
  intro j
  exact WithTop.coe_le_coe.mpr le_top

theorem yui_aux_0024 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), a < b → KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b g → KdVPlan.SmoothOn a b (fun t => f t+g t)" := by
  intro a b f g hab hf hg
  constructor
  · intro k
    exact (hf.1 k).add (hg.1 k)
  · intro m j
    have hc := @yui_aux_0019 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b _ _ (hf.2 m j) (hg.2 m j)
    apply @yui_aux_0020 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b _ _ hc
    intro t ht
    funext k
    exact (iteratedDerivWithin_fun_add ht (uniqueDiffOn_Icc hab) ((hf.1 k t ht).of_le (@yui_aux_0023 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 j)) ((hg.1 k t ht).of_le (@yui_aux_0023 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 j))).symm

theorem yui_aux_0025 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b (fun t => f t+g t)" := by
  classical
  intro a b f g hf hg
  refine ⟨fun m => @yui_aux_0019 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b f g (hf.1 m) (hg.1 m), ?_⟩
  obtain ⟨p, hp⟩ := hf.2
  obtain ⟨q, hq⟩ := hg.2
  refine ⟨p∪q, ?_⟩
  intro l r hal hlr hrb hbreak
  apply @yui_aux_0024 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 l r f g hlr
  · exact hp l r hal hlr hrb (fun x hx => hbreak x (Finset.mem_union_left q hx))
  · exact hq l r hal hlr hrb (fun x hx => hbreak x (Finset.mem_union_right p hx))

theorem yui_aux_0026 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (c : ℂ) (f : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b (fun t => KdVPlan.scale c (f t))" := by
  intro a b c f hf
  refine ⟨fun m => @yui_aux_0021 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b c f (hf.1 m), ?_⟩
  obtain ⟨p, hp⟩ := hf.2
  refine ⟨p, ?_⟩
  intro l r hal hlr hrb hbreak
  exact @yui_aux_0022 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 l r c f (hp l r hal hlr hrb hbreak)

theorem yui_aux_0027 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), KdVPlan.SmoothOn a b f → (∀ t ∈ Set.Icc a b, f t=g t) → KdVPlan.SmoothOn a b g" := by
  intro a b f g hf he
  constructor
  · intro k
    exact (hf.1 k).congr (fun t ht => (congrFun (he t ht) k).symm)
  · intro m j
    apply @yui_aux_0020 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b _ _ (hf.2 m j)
    intro t ht
    funext k
    exact iteratedDerivWithin_congr (fun r hr => congrFun (he r hr) k) ht

theorem yui_aux_0028 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), KdVPlan.Piecewise a b f → (∀ t ∈ Set.Icc a b, f t=g t) → KdVPlan.Piecewise a b g" := by
  intro a b f g hf he
  refine ⟨fun m => @yui_aux_0020 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b f g (hf.1 m) he, ?_⟩
  obtain ⟨p, hp⟩ := hf.2
  refine ⟨p, ?_⟩
  intro l r hal hlr hrb hbreak
  apply @yui_aux_0027 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 l r f g (hp l r hal hlr hrb hbreak)
  intro t ht
  exact he t ⟨hal.trans ht.1, ht.2.trans hrb⟩

theorem yui_aux_0029 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → KdVPlan.Piecewise 0 τ (KdVPlan.Vst 0 τ f)" := by
  intro τ f hτ hf hs
  have hnum : KdVPlan.twistedNum τ f 0=f := by
    funext k
    simp [KdVPlan.twistedNum, KdVPlan.numerical, KdVPlan.S]
  have hstruct := h_T007.2.2.2 τ f 1 hτ hf hs
  have hp : KdVPlan.Piecewise 0 τ (KdVPlan.interp τ f) := by simpa using hstruct.1
  apply @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 τ _ _ hp
  intro t ht
  rcases ht.2.eq_or_lt with heq | hlt
  · subst t
    have hg := hstruct.2.2 1 le_rfl
    have hend := (h_T007.2.2.1 τ f 0 hτ hf hs).2
    simpa only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_add, one_mul, hnum] using hg.trans hend.symm
  · have hi : KdVPlan.gridIndex τ t = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hτ).mpr hlt)
    simp only [KdVPlan.interp, hi, Nat.cast_zero, zero_mul, hnum]

theorem yui_aux_0030 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s t : ℝ) (f : KdVPlan.Coeff), KdVPlan.S s (KdVPlan.S t f) = KdVPlan.S (s+t) f" := by
  intro s t f
  funext k
  unfold KdVPlan.S
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem yui_aux_0031 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.B (a+t) f g = KdVPlan.S (-a) (KdVPlan.B t (KdVPlan.S a f) (KdVPlan.S a g))" := by
  intro a t f g
  simp only [KdVPlan.B, @yui_aux_0030 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013]
  simp only [neg_add, add_comm t a]

theorem yui_aux_0032 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a t : ℝ) (u : KdVPlan.Path), KdVPlan.timeInt a (a+t) u = KdVPlan.timeInt 0 t (fun r => u (a+r))" := by
  intro a t u
  funext k
  simpa only [KdVPlan.timeInt, add_zero] using (intervalIntegral.integral_comp_add_left (fun r => u r k) (a := 0) (b := t) a).symm

theorem yui_aux_0033 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (a t : ℝ) (u : KdVPlan.Path), KdVPlan.timeInt a (a+t) u = KdVPlan.timeInt 0 t (fun r => u (a+r))) ∧ (∀ (s a b : ℝ) (u : KdVPlan.Path), KdVPlan.S s (KdVPlan.timeInt a b u) = KdVPlan.timeInt a b (fun r => KdVPlan.S s (u r))) ∧ (∀ (s : ℝ) (c : ℂ) (f : KdVPlan.Coeff), KdVPlan.S s (KdVPlan.scale c f) = KdVPlan.scale c (KdVPlan.S s f))" := by
  refine ⟨?_, ?_, ?_⟩
  · exact @yui_aux_0032 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013
  · intro s a b u
    funext k
    simp only [KdVPlan.S, KdVPlan.timeInt, intervalIntegral.integral_const_mul]
  · intro s c f
    funext k
    simp only [KdVPlan.S, KdVPlan.scale]
    ring

theorem yui_aux_0034 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.stage a (a+t) f g = KdVPlan.S (-a) (KdVPlan.stage 0 t (KdVPlan.S a f) (KdVPlan.S a g))" := by
  intro a t f g
  unfold KdVPlan.stage
  rw [@yui_aux_0032 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013]
  rw [(@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2, (@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1]
  simp only [@yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013]

theorem yui_aux_0035 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a t : ℝ) (f : KdVPlan.Coeff), KdVPlan.Cst a f (a+t) = KdVPlan.S (-a) (KdVPlan.Cst 0 (KdVPlan.S a f) t) ∧ KdVPlan.Qst a f (a+t) = KdVPlan.S (-a) (KdVPlan.Qst 0 (KdVPlan.S a f) t)" := by
  intro a t f
  have hz : ∀ u : KdVPlan.Coeff, KdVPlan.S 0 u=u := by
    intro u
    funext k
    simp [KdVPlan.S]
  constructor
  · unfold KdVPlan.Cst
    rw [@yui_aux_0032 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, (@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1]
    simp only [KdVPlan.F, @yui_aux_0034 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, @yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, @yui_aux_0030 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, add_neg_cancel, hz]
  · unfold KdVPlan.Qst
    rw [@yui_aux_0032 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, (@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2, (@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1]
    simp only [KdVPlan.F, @yui_aux_0034 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, @yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, @yui_aux_0030 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, add_neg_cancel, hz]

theorem yui_aux_0036 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a : ℝ) (k x y : ℤ), KdVPlan.phase (3*(x : ℝ)*(y : ℝ)*(x+y : ℤ)+3*(k : ℝ)*(k-x-y : ℤ)*(x+y : ℤ)) a = Complex.exp (Complex.I * ((-a)*(k : ℝ)^3 : ℝ)) * Complex.exp (Complex.I * (a*(x : ℝ)^3 : ℝ)) * Complex.exp (Complex.I * (a*(y : ℝ)^3 : ℝ)) * Complex.exp (Complex.I * (a*(k-x-y : ℤ)^3 : ℝ))" := by
  intro a k x y
  unfold KdVPlan.phase
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem yui_aux_0037 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (χ : ℤ → ℤ → ℤ → ℂ) (a τ : ℝ) (f g h : KdVPlan.Coeff), KdVPlan.remWith χ a τ f g h = KdVPlan.S (-a) (KdVPlan.remWith χ 0 τ (KdVPlan.S a f) (KdVPlan.S a g) (KdVPlan.S a h))" := by
  intro χ a τ f g h
  funext k
  by_cases hk : k=0
  · simp [hk, KdVPlan.remWith, KdVPlan.S]
  · simp only [KdVPlan.remWith, KdVPlan.S, if_neg hk]
    rw [mul_left_comm (Complex.exp _) (-(τ : ℂ)/(18*Complex.I*(k : ℂ)))]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    by_cases hz : z.1+z.2=0
    · simp only [if_pos hz, mul_zero]
    · simp only [if_neg hz]
      have hp0 : ∀ A : ℝ, KdVPlan.phase A 0 = 1 := by intro A; simp [KdVPlan.phase]
      simp only [hp0, mul_one]
      rw [@yui_aux_0036 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013]
      ring

theorem yui_aux_0038 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.S s (f+g)=KdVPlan.S s f+KdVPlan.S s g ∧ KdVPlan.S s (f-g)=KdVPlan.S s f-KdVPlan.S s g" := by
  intro s f g
  constructor <;> funext k <;> simp [KdVPlan.S, mul_add, mul_sub]

theorem yui_aux_0039 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), KdVPlan.Wst a τ f = KdVPlan.S (-a) (KdVPlan.Wst 0 τ (KdVPlan.S a f))" := by
  intro a τ f
  unfold KdVPlan.Wst KdVPlan.rem
  rw [(@yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f).2, @yui_aux_0037 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (fun _ _ _ => 1) a τ f f f]
  simp only [zero_add, (@yui_aux_0038 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ _ _).1]

theorem yui_aux_0040 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ t : ℝ) (f : KdVPlan.Coeff), KdVPlan.Vst a τ f (a+t) = KdVPlan.S (-a) (KdVPlan.Vst 0 τ (KdVPlan.S a f) t)" := by
  intro a τ t f
  have hS0 : ∀ u : KdVPlan.Coeff, KdVPlan.S 0 u=u := by intro u; funext k; simp [KdVPlan.S]
  have hAdd : ∀ s f g, KdVPlan.S s (f+g)=KdVPlan.S s f+KdVPlan.S s g := fun s f g => (@yui_aux_0038 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f g).1
  have hSub : ∀ s f g, KdVPlan.S s (f-g)=KdVPlan.S s f-KdVPlan.S s g := fun s f g => (@yui_aux_0038 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f g).2
  have hC := fun a t f => (@yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a t f).1
  have hQ := fun a t f => (@yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a t f).2
  unfold KdVPlan.Vst KdVPlan.F
  rw [@yui_aux_0034 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a t f f, hC a t f, hQ a t f, @yui_aux_0039 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f]
  simp only [hAdd, hSub, (@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2, @yui_aux_0030 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, neg_add_cancel, hS0, add_sub_cancel_left, sub_zero]

theorem yui_aux_0041 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (s a b t : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s a b (fun r => KdVPlan.S t (f r))) ∧ (∀ (a b t : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b (fun r => KdVPlan.S t (f r))) ∧ (∀ (a b t : ℝ) (f : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b (fun r => KdVPlan.S t (f r)))" := by
  have hc : ∀ (s a b t : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s a b (fun r => KdVPlan.S t (f r)) := by
    intro s a b t f hf
    refine ⟨fun r hr => (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s t _).1.mpr (hf.1 r hr), ?_⟩
    intro r hr ε hε
    obtain ⟨δ, hδ, hd⟩ := hf.2 r hr ε hε
    refine ⟨δ, hδ, ?_⟩
    intro v hv hvr
    rw [← (@yui_aux_0038 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t _ _).2, (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s t _).2]
    exact hd v hv hvr
  have hs : ∀ (a b t : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b (fun r => KdVPlan.S t (f r)) := by
    intro a b t f hf
    constructor
    · intro k
      exact contDiffOn_const.mul (hf.1 k)
    · intro m j
      have hh := hc (m : ℝ) a b t _ (hf.2 m j)
      convert hh using 1
      funext r k
      exact iteratedDerivWithin_const_mul_field _ _
  refine ⟨hc, hs, ?_⟩
  intro a b t f hf
  refine ⟨fun m => hc (m : ℝ) a b t f (hf.1 m), ?_⟩
  obtain ⟨p, hp⟩ := hf.2
  refine ⟨p, ?_⟩
  intro l r hal hlr hrb hbreak
  exact hs l r t f (hp l r hal hlr hrb hbreak)

theorem yui_aux_0042 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (s a b c : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s (a+c) (b+c) (fun t => f (t-c))) ∧ (∀ (a b c : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn (a+c) (b+c) (fun t => f (t-c))) ∧ (∀ (a b c : ℝ) (f : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise (a+c) (b+c) (fun t => f (t-c)))" := by
  classical
  have hc : ∀ (s a b c : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s (a+c) (b+c) (fun t => f (t-c)) := by
    intro s a b c f hf
    have hm : ∀ t ∈ Set.Icc (a+c) (b+c), t-c ∈ Set.Icc a b := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    refine ⟨fun t ht => hf.1 _ (hm t ht), ?_⟩
    intro t ht ε hε
    obtain ⟨δ, hδ, hd⟩ := hf.2 _ (hm t ht) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro r hr hrt
    apply hd _ (hm r hr)
    convert hrt using 1
    congr 1
    ring
  have hs : ∀ (a b c : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn (a+c) (b+c) (fun t => f (t-c)) := by
    intro a b c f hf
    letI : VAdd ℝ (Set ℝ) := Set.vaddSet
    have hset : (-c) +ᵥ Set.Icc (a+c) (b+c) = Set.Icc a b := by
      change (fun x : ℝ => -c+x) '' Set.Icc (a+c) (b+c) = _
      rw [Set.image_const_add_Icc]
      congr 1 <;> ring
    constructor
    · intro k
      apply (hf.1 k).comp (contDiffOn_id.sub contDiffOn_const)
      intro t ht
      change t-c ∈ Set.Icc a b
      constructor <;> linarith [ht.1, ht.2]
    · intro m j
      have hh := hc (m : ℝ) a b c _ (hf.2 m j)
      convert hh using 1
      funext r k
      simpa only [sub_eq_add_neg, hset] using congrFun (iteratedDerivWithin_comp_add_const (n := j) (s := Set.Icc (a+c) (b+c)) (f := fun t => f t k) (-c)) r
  refine ⟨hc, hs, ?_⟩
  intro a b c f hf
  refine ⟨fun m => hc (m : ℝ) a b c f (hf.1 m), ?_⟩
  obtain ⟨p, hp⟩ := hf.2
  refine ⟨p.image (fun x => x+c), ?_⟩
  intro l r hal hlr hrb hbreak
  have hpiece : KdVPlan.SmoothOn (l-c) (r-c) f := by
    apply hp (l-c) (r-c) (by linarith) (by linarith) (by linarith)
    intro x hx hxint
    have hnot := hbreak (x+c) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    apply hnot
    constructor <;> linarith [hxint.1, hxint.2]
  have hshift := hs (l-c) (r-c) c f hpiece
  simpa only [sub_add_cancel] using hshift

theorem yui_aux_0043 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (k : ℤ), Complex.exp (Complex.I * (t*((-k : ℤ) : ℝ)^3 : ℝ)) = star (Complex.exp (Complex.I * (t*(k : ℝ)^3 : ℝ)))" := by
  intro t k
  change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Int.cast_neg]
  push_cast
  ring

theorem yui_aux_0044 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s t : ℝ) (f : KdVPlan.Coeff), KdVPlan.Data s f → KdVPlan.Data s (KdVPlan.S t f) ∧ (KdVPlan.Smooth f → KdVPlan.Smooth (KdVPlan.S t f))" := by
  intro s t f hf
  refine ⟨⟨(@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s t f).1.mpr hf.1, ?_, ?_⟩, ?_⟩
  · simpa [KdVPlan.ZeroMean, KdVPlan.S] using hf.2.1
  · intro k
    change Complex.exp (Complex.I * (t*((-k : ℤ) : ℝ)^3 : ℝ)) * f (-k) = star (Complex.exp (Complex.I * (t*(k : ℝ)^3 : ℝ)) * f k)
    rw [hf.2.2 k, @yui_aux_0043 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013]
    simp [star_mul, mul_comm]
  · intro hs m
    exact (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) t f).1.mpr (hs m)

theorem yui_aux_0045 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → KdVPlan.Piecewise a (a+τ) (KdVPlan.Vst a τ f)" := by
  intro a τ f hτ hf hs
  have hsf := @yui_aux_0044 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a f hf
  have hp0 := @yui_aux_0029 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ (KdVPlan.S a f) hτ hsf.1 (hsf.2 hs)
  have hp1 := (@yui_aux_0042 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2 0 τ a _ hp0
  have hp2 := (@yui_aux_0041 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2 (0+a) (τ+a) (-a) _ hp1
  have hp3 : KdVPlan.Piecewise a (a+τ) (fun t => KdVPlan.S (-a) (KdVPlan.Vst 0 τ (KdVPlan.S a f) (t-a))) := by simpa only [zero_add, add_comm τ a] using hp2
  apply @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ hp3
  intro t ht
  simpa only [add_sub_cancel] using (@yui_aux_0040 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ (t-a) f).symm

theorem yui_aux_0046 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (c d : ℂ) (f g : KdVPlan.Coeff), KdVPlan.mul (KdVPlan.scale c f) (KdVPlan.scale d g) = KdVPlan.scale (c*d) (KdVPlan.mul f g)) ∧ (∀ (c : ℂ) (a b : ℝ) (u : KdVPlan.Path), KdVPlan.timeInt a b (fun r => KdVPlan.scale c (u r)) = KdVPlan.scale c (KdVPlan.timeInt a b u)) ∧ (∀ (c d : ℂ) (f : KdVPlan.Coeff), KdVPlan.scale c (KdVPlan.scale d f) = KdVPlan.scale (c*d) f)" := by
  refine ⟨?_, ?_, ?_⟩
  · intro c d f g
    funext k
    unfold KdVPlan.mul KdVPlan.scale
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    ring
  · intro c a b u
    funext k
    simp only [KdVPlan.timeInt, KdVPlan.scale, intervalIntegral.integral_const_mul]
  · intro c d f
    funext k
    simp only [KdVPlan.scale, mul_assoc]

theorem yui_aux_0047 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (c d : ℂ) (f g : KdVPlan.Coeff), KdVPlan.B t (KdVPlan.scale c f) (KdVPlan.scale d g) = KdVPlan.scale (c*d) (KdVPlan.B t f g)" := by
  intro t c d f g
  have hdx : ∀ (z : ℂ) (u : KdVPlan.Coeff), KdVPlan.dx (KdVPlan.scale z u)=KdVPlan.scale z (KdVPlan.dx u) := by
    intro z u
    funext k
    simp only [KdVPlan.dx, KdVPlan.scale]
    ring
  simp only [KdVPlan.B, (@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2, (@yui_aux_0046 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1, hdx]

theorem yui_aux_0048 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (a t : ℝ) (c d : ℂ) (f g : KdVPlan.Coeff), KdVPlan.stage a t (KdVPlan.scale c f) (KdVPlan.scale d g) = KdVPlan.scale (c*d) (KdVPlan.stage a t f g)) ∧ (∀ (a t : ℝ) (c : ℂ) (f : KdVPlan.Coeff), KdVPlan.Cst a (KdVPlan.scale c f) t = KdVPlan.scale (c^3) (KdVPlan.Cst a f t) ∧ KdVPlan.Qst a (KdVPlan.scale c f) t = KdVPlan.scale (c^4) (KdVPlan.Qst a f t))" := by
  have hst : ∀ (a t : ℝ) (c d : ℂ) (f g : KdVPlan.Coeff), KdVPlan.stage a t (KdVPlan.scale c f) (KdVPlan.scale d g) = KdVPlan.scale (c*d) (KdVPlan.stage a t f g) := by
    intro a t c d f g
    simp only [KdVPlan.stage, @yui_aux_0047 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, (@yui_aux_0046 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1]
    funext k
    simp only [KdVPlan.scale]
    ring
  refine ⟨hst, ?_⟩
  intro a t c f
  constructor
  · simp only [KdVPlan.Cst, KdVPlan.F, hst, @yui_aux_0047 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, (@yui_aux_0046 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1]
    funext k
    simp only [KdVPlan.scale]
    ring
  · simp only [KdVPlan.Qst, KdVPlan.F, hst, @yui_aux_0047 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, (@yui_aux_0046 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1]
    funext k
    simp only [KdVPlan.scale]
    ring

theorem yui_aux_0049 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (χ : ℤ → ℤ → ℤ → ℂ) (a τ : ℝ) (c : ℂ) (f : KdVPlan.Coeff), KdVPlan.remWith χ a τ (KdVPlan.scale c f) (KdVPlan.scale c f) (KdVPlan.scale c f) = KdVPlan.scale (c^3) (KdVPlan.remWith χ a τ f f f)" := by
  intro χ a τ c f
  funext k
  by_cases hk : k=0
  · simp [hk, KdVPlan.remWith, KdVPlan.scale]
  · simp only [KdVPlan.remWith, KdVPlan.scale, if_neg hk]
    rw [mul_left_comm (c^3) (-(τ : ℂ)/(18*Complex.I*(k : ℂ)))]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    by_cases hz : z.1+z.2=0
    · simp only [if_pos hz, mul_zero]
    · simp only [if_neg hz]
      ring

theorem yui_aux_0050 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ t : ℝ) (f : KdVPlan.Coeff), KdVPlan.F a f t = KdVPlan.scale (1/24) (KdVPlan.scale 16 (KdVPlan.Vst a τ f t+KdVPlan.Vst a τ (KdVPlan.scale (-1) f) t) - (KdVPlan.Vst a τ (KdVPlan.scale 2 f) t+KdVPlan.Vst a τ (KdVPlan.scale (-2) f) t))" := by
  intro a τ t f
  have hC := fun a t c f => ((@yui_aux_0048 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2 a t c f).1
  have hQ := fun a t c f => ((@yui_aux_0048 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2 a t c f).2
  simp only [KdVPlan.Vst, KdVPlan.F, KdVPlan.Wst, KdVPlan.rem, (@yui_aux_0048 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1, hC, hQ, @yui_aux_0049 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013]
  funext k
  simp only [KdVPlan.scale, Pi.add_apply, Pi.sub_apply]
  ring

theorem yui_aux_0051 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s r : ℝ) (f : KdVPlan.Coeff), KdVPlan.Data s f → KdVPlan.Data s (KdVPlan.scale (r : ℂ) f) ∧ (KdVPlan.Smooth f → KdVPlan.Smooth (KdVPlan.scale (r : ℂ) f))" := by
  intro s r f hf
  refine ⟨⟨(@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f (r : ℂ) hf.1).1, ?_, ?_⟩, ?_⟩
  · change (r : ℂ)*f 0=0
    rw [hf.2.1, mul_zero]
  · intro k
    change (r : ℂ)*f (-k)=star ((r : ℂ)*f k)
    rw [hf.2.2 k, star_mul]
    simp [mul_comm]
  · intro hs m
    exact (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) f (r : ℂ) (hs m)).1

theorem yui_aux_0052 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b (fun t => f t-g t)" := by
  intro a b f g hf hg
  have hn := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b (-1) g hg
  have ha := @yui_aux_0025 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b f _ hf hn
  apply @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b _ _ ha
  intro t ht
  funext k
  simp [KdVPlan.scale, sub_eq_add_neg]

theorem yui_aux_0053 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → KdVPlan.Piecewise a (a+τ) (KdVPlan.F a f)" := by
  intro a τ f hτ hf hs
  have hp : ∀ r : ℝ, KdVPlan.Piecewise a (a+τ) (KdVPlan.Vst a τ (KdVPlan.scale (r : ℂ) f)) := by
    intro r
    have hh := @yui_aux_0051 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 r f hf
    exact @yui_aux_0045 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ _ hτ hh.1 (hh.2 hs)
  have hm : KdVPlan.Piecewise a (a+τ) (KdVPlan.Vst a τ (KdVPlan.scale (-1) f)) := by simpa using hp (-1)
  have h2 : KdVPlan.Piecewise a (a+τ) (KdVPlan.Vst a τ (KdVPlan.scale 2 f)) := by simpa using hp 2
  have hm2 : KdVPlan.Piecewise a (a+τ) (KdVPlan.Vst a τ (KdVPlan.scale (-2) f)) := by simpa using hp (-2)
  have hb := @yui_aux_0045 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs
  have hleft := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) 16 _ (@yui_aux_0025 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ hb hm)
  have hright := @yui_aux_0025 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ h2 hm2
  have hall := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) (1/24) _ (@yui_aux_0052 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ hleft hright)
  apply @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ hall
  intro t ht
  exact (@yui_aux_0050 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ t f).symm

theorem yui_aux_0054 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Coeff), KdVPlan.Smooth f → KdVPlan.Piecewise a b (fun _ => f)" := by
  intro a b f hf
  refine ⟨fun m => @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) a b f (hf m), ⟨∅, ?_⟩⟩
  intro l r hal hlr hrb hbreak
  constructor
  · intro k
    exact contDiffOn_const
  · intro m j
    by_cases hj : j=0
    · subst j
      simpa only [iteratedDerivWithin_zero] using @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) l r f (hf m)
    · simp only [iteratedDerivWithin_const, if_neg hj]
      apply @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (m : ℝ) l r 0
      simp [KdVPlan.MemH]

theorem yui_aux_0055 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → KdVPlan.Piecewise a (a+τ) (KdVPlan.z a f) ∧ KdVPlan.Piecewise a (a+τ) (KdVPlan.Yst a τ f)" := by
  intro a τ f hτ hf hs
  have hF := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs
  have hc := @yui_aux_0054 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) f hs
  have hz : KdVPlan.Piecewise a (a+τ) (KdVPlan.z a f) := @yui_aux_0025 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ hc hF
  refine ⟨hz, ?_⟩
  exact @yui_aux_0052 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ (@yui_aux_0045 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs) hz

theorem yui_aux_0056 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ f g : KdVPlan.Coeff, KdVPlan.mul f g = KdVPlan.mul g f) ∧ (∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.B t f g=KdVPlan.B t g f ∧ KdVPlan.J t f g=KdVPlan.J t g f) ∧ (∀ (a τ : ℝ) (f : KdVPlan.Coeff), KdVPlan.ZeroMean f → (∀ t : ℝ, KdVPlan.ZeroMean (KdVPlan.z a f t) ∧ KdVPlan.ZeroMean (KdVPlan.Yst a τ f t)))" := by
  have hm : ∀ f g : KdVPlan.Coeff, KdVPlan.mul f g = KdVPlan.mul g f := by
    intro f g
    funext k
    let e : ℤ ≃ ℤ := ⟨fun j => k-j, fun j => k-j, by intro j; dsimp; omega, by intro j; dsimp; omega⟩
    unfold KdVPlan.mul
    rw [← e.tsum_eq (fun j => f j*g (k-j))]
    apply tsum_congr
    intro j
    change f (k-j)*g (k-(k-j))=g j*f (k-j)
    rw [sub_sub_cancel]
    exact mul_comm _ _
  refine ⟨hm, ?_, ?_⟩
  · intro t f g
    constructor
    · unfold KdVPlan.B
      rw [hm]
    · unfold KdVPlan.J
      rw [hm]
  · intro a τ f hf t
    have hB : ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.B t f g 0=0 := by
      intro t f g
      simp [KdVPlan.B, KdVPlan.S, KdVPlan.dx]
    change f 0=0 at hf
    constructor <;> unfold KdVPlan.ZeroMean <;> simp [KdVPlan.z, KdVPlan.Yst, KdVPlan.Vst, KdVPlan.F, KdVPlan.stage, KdVPlan.Cst, KdVPlan.Qst, KdVPlan.Wst, KdVPlan.rem, KdVPlan.remWith, KdVPlan.timeInt, KdVPlan.scale, hB, hf]

theorem yui_aux_0057 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f f' g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.mul (f+f') g=KdVPlan.mul f g+KdVPlan.mul f' g" := by
  intro f f' g hf hf' hg
  funext k
  simp only [KdVPlan.mul, Pi.add_apply, add_mul]
  exact (@yui_aux_0014 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 f g hf hg k).tsum_add (@yui_aux_0014 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 f' g hf' hg k)

theorem yui_aux_0058 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → ∀ k : ℤ, Continuous (fun t : ℝ => KdVPlan.B t f g k)" := by
  intro f g hf hg k
  have hn : Summable (fun j : ℤ => ‖f j‖*‖g (k-j)‖) := by
    simpa only [norm_mul] using summable_norm_iff.mpr (@yui_aux_0014 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 f g hf hg k)
  have hS : ∀ (u : KdVPlan.Coeff) (j : ℤ), Continuous (fun t : ℝ => KdVPlan.S t u j) := by
    intro u j
    unfold KdVPlan.S
    fun_prop
  have hm : Continuous (fun t : ℝ => ∑' j : ℤ, KdVPlan.S t f j*KdVPlan.S t g (k-j)) := by
    apply continuous_tsum (fun j => (hS f j).mul (hS g (k-j))) hn
    intro j t
    change ‖KdVPlan.S t f j*KdVPlan.S t g (k-j)‖ ≤ ‖f j‖*‖g (k-j)‖
    simp only [KdVPlan.S, norm_mul, @yui_aux_0015 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013, one_mul]
    exact le_rfl
  change Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t)*(k : ℝ)^3 : ℝ)) * (Complex.I*(k : ℂ)*(∑' j : ℤ, KdVPlan.S t f j*KdVPlan.S t g (k-j))))
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t)*(k : ℝ)^3 : ℝ)))).mul (continuous_const.mul hm)

theorem yui_aux_0059 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH 0 f → (∀ (t : ℝ) (k : ℤ), HasDerivAt (fun r => KdVPlan.z a f r k) (KdVPlan.scale (1/2) (KdVPlan.B t f f) k) t) ∧ (∀ t : ℝ, KdVPlan.dt (KdVPlan.z a f) t=KdVPlan.scale (1/2) (KdVPlan.B t f f))" := by
  intro a f hf
  have hd : ∀ (t : ℝ) (k : ℤ), HasDerivAt (fun r => KdVPlan.z a f r k) (KdVPlan.scale (1/2) (KdVPlan.B t f f) k) t := by
    intro t k
    have hc := @yui_aux_0058 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 f f hf hf k
    have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t) (hc.stronglyMeasurableAtFilter MeasureTheory.volume (nhds t)) hc.continuousAt
    exact (hi.const_mul (1/2 : ℂ)).const_add (f k)
  refine ⟨hd, ?_⟩
  intro t
  funext k
  exact (hd t k).deriv

theorem yui_aux_0060 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → ∀ k : ℤ, ‖f k‖ ≤ KdVPlan.weight (-s/2) k * KdVPlan.hn s f" := by
  intro s f hf k
  obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
  have hw : 0 < KdVPlan.weight (-s/2) k := by
    unfold KdVPlan.weight
    exact Real.rpow_pos_of_pos (by positivity) _
  change ‖(KdVPlan.weight (-s/2) k : ℂ)*x k‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, h_T013.2.1 s]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x k) hw.le

theorem yui_aux_0061 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (F : Finset ℤ) (v : ℤ → ℝ), (∑ k : F, v k) = ∑ k ∈ F, v k" := by
  intro F v
  exact Finset.sum_coe_sort F v

theorem yui_aux_0062 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (F : Finset ℤ), ‖(WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*f k) : PiLp 2 (fun _ : F => ℂ))‖^2 = ∑ k ∈ F, KdVPlan.weight s k * ‖f k‖^2" := by
  intro s f F
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ k : F, ‖(Real.sqrt (KdVPlan.weight s k) : ℂ)*f k‖^2) = ∑ k : F, KdVPlan.weight s k*‖f k‖^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
      unfold KdVPlan.weight
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    _ = _ := @yui_aux_0061 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 F (fun k : ℤ => KdVPlan.weight s k*‖f k‖^2)

theorem yui_aux_0063 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), 0 ≤ KdVPlan.hn s f ∧ (KdVPlan.hn s f)^2 = ∑' k : ℤ, KdVPlan.weight s k*‖f k‖^2" := by
  intro s f
  constructor
  · exact Real.sqrt_nonneg _
  · apply Real.sq_sqrt
    apply tsum_nonneg
    intro k
    apply mul_nonneg
    · unfold KdVPlan.weight
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    · exact sq_nonneg _

theorem yui_aux_0064 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (v : ℤ → ℝ) (F : Finset ℤ), Summable v → (∀ k, 0 ≤ v k) → (∑ k ∈ F, v k) ≤ ∑' k, v k" := by
  intro v F hv hn
  exact Summable.sum_le_tsum F (fun k hk => hn k) hv

theorem yui_aux_0065 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s C : ℝ) (f : KdVPlan.Coeff) (F : Finset ℤ), KdVPlan.HB s f C → ‖(WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*f k) : PiLp 2 (fun _ : F => ℂ))‖ ≤ C" := by
  intro s C f F hf
  have hn := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f
  have hnon : ∀ k : ℤ, 0 ≤ KdVPlan.weight s k*‖f k‖^2 := by
    intro k
    apply mul_nonneg
    · unfold KdVPlan.weight
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    · exact sq_nonneg _
  have hsum : (∑ k ∈ F, KdVPlan.weight s k*‖f k‖^2) ≤ ∑' k : ℤ, KdVPlan.weight s k*‖f k‖^2 := @yui_aux_0064 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ F hf.1 hnon
  have hsquare := @yui_aux_0062 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f F
  rw [← hn.2, ← hsquare] at hsum
  have hle : ‖(WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*f k) : PiLp 2 (fun _ : F => ℂ))‖ ≤ KdVPlan.hn s f := by nlinarith [norm_nonneg (WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*f k) : PiLp 2 (fun _ : F => ℂ))]
  exact hle.trans hf.2

theorem yui_aux_0066 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path) (F : Finset ℤ), (∀ k, IntervalIntegrable (fun t => u t k) MeasureTheory.volume a b) → (∫ t in a..b, (WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*u t k) : PiLp 2 (fun _ : F => ℂ))) = WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*KdVPlan.timeInt a b u k)" := by
  intro s a b u F hu
  let U : ℝ → PiLp 2 (fun _ : F => ℂ) := fun t => WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*u t k)
  have hUi : ∀ k : F, IntervalIntegrable (fun t => U t k) MeasureTheory.volume a b := by
    intro k
    exact (hu k).const_mul (Real.sqrt (KdVPlan.weight s k) : ℂ)
  have hU : IntervalIntegrable U MeasureTheory.volume a b := ⟨MeasureTheory.Integrable.of_eval_piLp (fun k => (hUi k).1), MeasureTheory.Integrable.of_eval_piLp (fun k => (hUi k).2)⟩
  change (∫ t in a..b, U t) = _
  ext k
  have he := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : F => ℂ) k).intervalIntegral_comp_comm hU
  change (∫ t in a..b, U t k) = (∫ t in a..b, U t) k at he
  rw [← he]
  exact intervalIntegral.integral_const_mul _ _

theorem yui_aux_0067 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (u : KdVPlan.Path), a ≤ b → 0 ≤ C → (∀ k, IntervalIntegrable (fun t => u t k) MeasureTheory.volume a b) → (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioc a b → KdVPlan.HB s (u t) C) → KdVPlan.HB s (KdVPlan.timeInt a b u) ((b-a)*C)" := by
  intro s a b C u hab hC hi hb
  have hnon : ∀ k : ℤ, 0 ≤ KdVPlan.weight s k*‖KdVPlan.timeInt a b u k‖^2 := by
    intro k
    apply mul_nonneg
    · unfold KdVPlan.weight
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    · exact sq_nonneg _
  have hboundnon : 0 ≤ (b-a)*C := mul_nonneg (sub_nonneg.mpr hab) hC
  have hfinite : ∀ F : Finset ℤ, (∑ k ∈ F, KdVPlan.weight s k*‖KdVPlan.timeInt a b u k‖^2) ≤ ((b-a)*C)^2 := by
    intro F
    let U : ℝ → PiLp 2 (fun _ : F => ℂ) := fun t => WithLp.toLp 2 (fun k : F => (Real.sqrt (KdVPlan.weight s k) : ℂ)*u t k)
    have hB : ‖∫ t in a..b, U t‖ ≤ C*|b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      filter_upwards [hb] with t ht
      intro htI
      have hI : t ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using htI
      exact @yui_aux_0065 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s C (u t) F (ht hI)
    rw [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm C] at hB
    have he := @yui_aux_0066 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b u F hi
    change (∫ t in a..b, U t) = _ at he
    rw [he] at hB
    have hsq := @yui_aux_0062 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s (KdVPlan.timeInt a b u) F
    rw [← hsq]
    exact pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hs : KdVPlan.MemH s (KdVPlan.timeInt a b u) := summable_of_sum_le hnon hfinite
  refine ⟨hs, ?_⟩
  have htsum := hs.tsum_le_of_sum_le hfinite
  have hn := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s (KdVPlan.timeInt a b u)
  rw [← hn.2] at htsum
  nlinarith

theorem yui_aux_0068 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (s A B : ℝ) (f g : KdVPlan.Coeff), KdVPlan.HB s f A → KdVPlan.HB s g B → KdVPlan.HB s (f+g) (A+B) ∧ KdVPlan.HB s (f-g) (A+B)) ∧ (∀ (s A : ℝ) (c : ℂ) (f : KdVPlan.Coeff), KdVPlan.HB s f A → KdVPlan.HB s (KdVPlan.scale c f) (‖c‖*A)) ∧ (∀ (s A B : ℝ) (f : KdVPlan.Coeff), KdVPlan.HB s f A → A ≤ B → KdVPlan.HB s f B)" := by
  refine ⟨?_, ?_, ?_⟩
  · intro s A B f g hf hg
    have ha := @yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f g hf.1 hg.1
    have hs := @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f g hf.1 hg.1
    exact ⟨⟨ha.1, ha.2.trans (add_le_add hf.2 hg.2)⟩, ⟨hs.1, hs.2.trans (add_le_add hf.2 hg.2)⟩⟩
  · intro s A c f hf
    have hh := @yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f c hf.1
    exact ⟨hh.1, hh.2.le.trans (mul_le_mul_of_nonneg_left hf.2 (norm_nonneg _))⟩
  · intro s A B f hf hAB
    exact ⟨hf.1, hf.2.trans hAB⟩

theorem yui_aux_0069 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f f' g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.B t (f+f') g=KdVPlan.B t f g+KdVPlan.B t f' g" := by
  intro t f f' g hf hf' hg
  have hsf := (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 t f).1.mpr hf
  have hsf' := (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 t f').1.mpr hf'
  have hsg := (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 t g).1.mpr hg
  have hdx : ∀ u v : KdVPlan.Coeff, KdVPlan.dx (u+v)=KdVPlan.dx u+KdVPlan.dx v := by intro u v; funext k; simp [KdVPlan.dx, mul_add]
  unfold KdVPlan.B
  rw [(@yui_aux_0038 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t f f').1, @yui_aux_0057 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ _ _ hsf hsf' hsg, hdx, (@yui_aux_0038 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ _ _).1]

theorem yui_aux_0070 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g h : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → KdVPlan.MemH 0 h → KdVPlan.B t (f-g) h=KdVPlan.B t f h-KdVPlan.B t g h ∧ KdVPlan.B t h (f-g)=KdVPlan.B t h f-KdVPlan.B t h g" := by
  have hd : ∀ (t : ℝ) (f g h : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → KdVPlan.MemH 0 h → KdVPlan.B t (f-g) h=KdVPlan.B t f h-KdVPlan.B t g h := by
    intro t f g h hf hg hh
    have hs := (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 f g hf hg).1
    have ha := @yui_aux_0069 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t (f-g) g h hs hg hh
    rw [sub_add_cancel] at ha
    exact eq_sub_iff_add_eq.mpr ha.symm
  intro t f g h hf hg hh
  refine ⟨hd t f g h hf hg hh, ?_⟩
  have hm := fun t f g => ((@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 t f g).1
  rw [hm t h (f-g), hd t f g h hf hg hh, hm t f h, hm t g h]

theorem yui_aux_0071 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ k : ℤ, ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → ‖KdVPlan.B t f g k‖ ≤ C*KdVPlan.hn 0 f*KdVPlan.hn 0 g" := by
  intro k
  obtain ⟨C, hC, hi, hm, hB, hasym⟩ := h_T005.1.1
  have hw : 0 < KdVPlan.weight (KdVPlan.pstar/2) k := by
    unfold KdVPlan.weight
    exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨KdVPlan.weight (KdVPlan.pstar/2) k*C, mul_pos hw hC, ?_⟩
  intro t f g hf hg
  have hb := (hB t f g hf hg).1
  have he := @yui_aux_0060 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (-KdVPlan.pstar) (KdVPlan.B t f g) hb.1 k
  simp only [neg_neg] at he
  calc
    ‖KdVPlan.B t f g k‖ ≤ KdVPlan.weight (KdVPlan.pstar/2) k*KdVPlan.hn (-KdVPlan.pstar) (KdVPlan.B t f g) := he
    _ ≤ KdVPlan.weight (KdVPlan.pstar/2) k*(C*KdVPlan.hn 0 f*KdVPlan.hn 0 g) := mul_le_mul_of_nonneg_left hb.2 hw.le
    _ = _ := by ring

theorem yui_aux_0072 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ k : ℤ, ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f₁ f₀ g₁ g₀ : KdVPlan.Coeff), KdVPlan.MemH 0 f₁ → KdVPlan.MemH 0 f₀ → KdVPlan.MemH 0 g₁ → KdVPlan.MemH 0 g₀ → ‖KdVPlan.B t f₁ g₁ k-KdVPlan.B t f₀ g₀ k‖ ≤ C*KdVPlan.hn 0 (f₁-f₀)*KdVPlan.hn 0 g₁+C*KdVPlan.hn 0 f₀*KdVPlan.hn 0 (g₁-g₀)" := by
  intro k
  obtain ⟨C,hC,hB⟩ := @yui_aux_0071 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 k
  refine ⟨C,hC,?_⟩
  intro t f₁ f₀ g₁ g₀ hf₁ hf₀ hg₁ hg₀
  have hdf := (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 _ _ hf₁ hf₀).1
  have hdg := (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 _ _ hg₁ hg₀).1
  have he : KdVPlan.B t f₁ g₁-KdVPlan.B t f₀ g₀=KdVPlan.B t (f₁-f₀) g₁+KdVPlan.B t f₀ (g₁-g₀) := by
    rw [(@yui_aux_0070 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t f₁ f₀ g₁ hf₁ hf₀ hg₁).1, (@yui_aux_0070 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t g₁ g₀ f₀ hg₁ hg₀ hf₀).2]
    abel
  change ‖(KdVPlan.B t f₁ g₁-KdVPlan.B t f₀ g₀) k‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hB t _ _ hdf hg₁) (hB t _ _ hf₀ hdg))

theorem yui_aux_0073 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ x y z : ℂ, ‖x-z‖ ≤ ‖x-y‖+‖y-z‖" := by
  exact fun x y z => norm_sub_le_norm_sub_add_norm_sub x y z

theorem yui_aux_0074 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), KdVPlan.ContH 0 a b f → KdVPlan.ContH 0 a b g → ∀ k : ℤ, ContinuousOn (fun t => KdVPlan.B t (f t) (g t) k) (Set.Icc a b)" := by
  intro a b f g hf hg k
  obtain ⟨C,hC,hB⟩ := @yui_aux_0072 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 k
  apply Metric.continuousOn_iff.mpr
  intro t ht ε hε
  have hft := hf.1 t ht
  have hgt := hg.1 t ht
  have hnF := (@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (f t)).1
  have hnG := (@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (g t)).1
  let A := C*(KdVPlan.hn 0 (g t)+1)+C*KdVPlan.hn 0 (f t)+1
  have hA : 0 < A := by dsimp [A]; positivity
  let η := min 1 (ε/(2*A))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε (mul_pos (by norm_num) hA))
  obtain ⟨δf,hδf,hdf⟩ := hf.2 t ht η hη
  obtain ⟨δg,hδg,hdg⟩ := hg.2 t ht η hη
  have hfixed := @yui_aux_0058 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (f t) (g t) hft hgt k
  obtain ⟨δ₀,hδ₀,hd₀⟩ := Metric.continuousAt_iff.mp hfixed.continuousAt (ε/2) (half_pos hε)
  refine ⟨min δ₀ (min δf δg), lt_min hδ₀ (lt_min hδf hδg), ?_⟩
  intro r hr hrt
  have hdfr := hdf r hr (by simpa only [Real.dist_eq] using hrt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hdgr := hdg r hr (by simpa only [Real.dist_eq] using hrt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hgr : KdVPlan.hn 0 (g r) ≤ KdVPlan.hn 0 (g t)+1 := by
    have hh := (@yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (g r-g t) (g t) (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 _ _ (hg.1 r hr) hgt).1 hgt).2
    rw [sub_add_cancel] at hh
    have he : η ≤ 1 := min_le_left _ _
    linarith
  have hngr := (@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (g r)).1
  have hvar := hB r (f r) (f t) (g r) (g t) (hf.1 r hr) hft (hg.1 r hr) hgt
  have hprod := mul_le_mul hdfr.le hgr hngr hη.le
  have hprodC := mul_le_mul_of_nonneg_left hprod hC.le
  have hprodG := mul_le_mul_of_nonneg_left hdgr.le (mul_nonneg hC.le hnF)
  have hηA : η*A ≤ ε/2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hA)).mp (show η ≤ ε/(2*A) from min_le_right _ _)
    nlinarith
  have hvar' : ‖KdVPlan.B r (f r) (g r) k-KdVPlan.B r (f t) (g t) k‖ ≤ ε/2 := by
    dsimp [A] at hηA
    nlinarith
  have hfix := hd₀ (hrt.trans_le (min_le_left _ _))
  change dist (KdVPlan.B r (f t) (g t) k) (KdVPlan.B t (f t) (g t) k) < ε/2 at hfix
  rw [dist_eq_norm] at hfix ⊢
  exact (@yui_aux_0073 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (KdVPlan.B r (f r) (g r) k) (KdVPlan.B r (f t) (g t) k) (KdVPlan.B t (f t) (g t) k)).trans_lt (by linarith)

theorem yui_aux_0075 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (u : KdVPlan.Path), (∀ k, ContinuousOn (fun t => u t k) (Set.Icc a b)) → ∀ t ∈ Set.Ioo a b, ∀ k, HasDerivAt (fun r => KdVPlan.timeInt a r u k) (u t k) t" := by
  intro a b u hu t ht k
  have hc := hu k
  have hn : Set.Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hct : ContinuousAt (fun r => u r k) t := hc.continuousAt hn
  have hi : IntervalIntegrable (fun r => u r k) volume a t :=
    (hc.mono (Set.Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hm : StronglyMeasurableAtFilter (fun r => u r k) (nhds t) volume :=
    ⟨Set.Icc a b, hn, hc.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivAt_right hi hm hct

theorem yui_aux_0076 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ t : ℝ) (w : ℂ), HasDerivAt (fun r : ℝ => (((r-a)/τ : ℝ) : ℂ)*w) ((τ : ℂ)⁻¹*w) t" := by
  intro a τ t w
  have h := (((hasDerivAt_id t).sub_const a).div_const τ).ofReal_comp.mul_const w
  simpa [one_div] using h

theorem yui_aux_0077 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → ∀ t ∈ Set.Ioo a (a+τ), ∀ k : ℤ, HasDerivAt (fun r => KdVPlan.Cst a f r k) (KdVPlan.B t f (KdVPlan.F a f t) k) t ∧ HasDerivAt (fun r => KdVPlan.Qst a f r k) (KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.F a f t) (KdVPlan.F a f t)) k) t" := by
  intro a τ f hτ hf hs t ht k
  have hF := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs
  have hF0 : KdVPlan.ContH 0 a (a+τ) (KdVPlan.F a f) := by simpa using hF.1 0
  have hc := @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a (a+τ) f hf.1
  have h1 := @yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) (fun _ => f) (KdVPlan.F a f) hc hF0
  have h2 := @yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) (KdVPlan.F a f) (KdVPlan.F a f) hF0 hF0
  have d1 := @yui_aux_0075 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) (fun r => KdVPlan.B r f (KdVPlan.F a f r)) h1 t ht k
  have d2 := @yui_aux_0075 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) (fun r => KdVPlan.B r (KdVPlan.F a f r) (KdVPlan.F a f r)) h2 t ht k
  exact ⟨d1, d2.const_mul (1/2)⟩

theorem yui_aux_0078 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → ∀ t ∈ Set.Ioo a (a+τ), ∀ k : ℤ, HasDerivAt (fun r => KdVPlan.Vst a τ f r k) ((KdVPlan.scale (1/2) (KdVPlan.B t f f)+KdVPlan.B t f (KdVPlan.F a f t)+KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.F a f t) (KdVPlan.F a f t))-KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst a τ f)) k) t ∧ HasDerivAt (fun r => KdVPlan.rho a τ f r k) ((-KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.z a f t)-KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.Yst a τ f t))-KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst a τ f)) k) t" := by
  intro a τ f hτ hf hs t ht k
  have hzy := @yui_aux_0055 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs
  have hz : KdVPlan.ContH 0 a (a+τ) (KdVPlan.z a f) := by simpa using hzy.1.1 0
  have hy : KdVPlan.ContH 0 a (a+τ) (KdVPlan.Yst a τ f) := by simpa using hzy.2.1 0
  have d1 := @yui_aux_0075 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) (fun r => KdVPlan.B r (KdVPlan.Yst a τ f r) (KdVPlan.z a f r)) (@yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ hy hz) t ht k
  have d2 := @yui_aux_0075 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) (fun r => KdVPlan.B r (KdVPlan.Yst a τ f r) (KdVPlan.Yst a τ f r)) (@yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a (a+τ) _ _ hy hy) t ht k
  have da := @yui_aux_0076 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ t (KdVPlan.Wst a τ f k)
  have dz := (@yui_aux_0059 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a f hf.1).1 t k
  have dcq := @yui_aux_0077 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs t ht k
  constructor
  · simpa only [KdVPlan.z, KdVPlan.Vst, KdVPlan.scale, Pi.add_apply, Pi.sub_apply, Pi.add_def, Pi.sub_def, Pi.neg_def] using ((dz.add dcq.1).add dcq.2).sub da
  · simpa only [KdVPlan.rho, KdVPlan.scale, Pi.neg_apply, Pi.sub_apply, Pi.add_def, Pi.sub_def, Pi.neg_def] using ((d1.neg).sub (d2.const_mul (1/2))).sub da

theorem yui_aux_0079 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → KdVPlan.B t (f+g) (f+g) = KdVPlan.B t f f + KdVPlan.scale 2 (KdVPlan.B t f g) + KdVPlan.B t g g" := by
  intro t f g hf hg
  have hadd := @yui_aux_0069 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013
  have hs := (@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1
  have hm := (@yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 f g hf hg).1
  rw [hadd t f g (f+g) hf hg hm, (hs t f (f+g)).1, (hs t g (f+g)).1,
    hadd t f g f hf hg hf, hadd t f g g hf hg hg, (hs t g f).1]
  ext k
  simp only [Pi.add_apply, KdVPlan.scale]
  ring

theorem yui_aux_0080 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → ∀ t ∈ Set.Ioo a (a+τ),\nKdVPlan.dt (KdVPlan.Vst a τ f) t = KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.Vst a τ f t) (KdVPlan.Vst a τ f t))+KdVPlan.dt (KdVPlan.rho a τ f) t ∧\nKdVPlan.dt (KdVPlan.rho a τ f) t = -KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.z a f t)-KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.Yst a τ f t))-KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst a τ f)" := by
  intro a τ f hτ hf hs t ht
  have hd := @yui_aux_0078 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs t ht
  have hr : KdVPlan.dt (KdVPlan.rho a τ f) t =
    -KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.z a f t) -
    KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.Yst a τ f t)) -
    KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst a τ f) := by
    ext k
    exact (hd k).2.deriv
  refine ⟨?_, hr⟩
  have hzy := @yui_aux_0055 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs
  have hmz : KdVPlan.MemH 0 (KdVPlan.z a f t) := by simpa using (hzy.1.1 0).1 t ⟨ht.1.le,ht.2.le⟩
  have hmy : KdVPlan.MemH 0 (KdVPlan.Yst a τ f t) := by simpa using (hzy.2.1 0).1 t ⟨ht.1.le,ht.2.le⟩
  have hmF : KdVPlan.MemH 0 (KdVPlan.F a f t) := by
    simpa using ((@yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hs).1 0).1 t ⟨ht.1.le,ht.2.le⟩
  have hv : KdVPlan.Vst a τ f t = KdVPlan.z a f t+KdVPlan.Yst a τ f t := by
    dsimp [KdVPlan.Yst]
    abel
  have hBv := @yui_aux_0079 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t (KdVPlan.z a f t) (KdVPlan.Yst a τ f t) hmz hmy
  have hBz := @yui_aux_0079 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t f (KdVPlan.F a f t) hf.1 hmF
  have hsym := ((@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 t (KdVPlan.z a f t) (KdVPlan.Yst a τ f t)).1
  rw [hr, hv, hBv, hsym]
  change _ = KdVPlan.scale (1/2) (_ + _ + _) + _
  rw [show KdVPlan.B t (KdVPlan.z a f t) (KdVPlan.z a f t) = _ from hBz]
  ext k
  rw [show KdVPlan.dt (KdVPlan.Vst a τ f) t k = _ from (hd k).1.deriv]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, KdVPlan.scale]
  ring

theorem yui_aux_0081 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (u : KdVPlan.Path), 0 ≤ C → (∀ t ∈ Set.Ioo a b, KdVPlan.HB s (KdVPlan.dt u t) C) → KdVPlan.EssBound s a b (KdVPlan.dt u) ∧ KdVPlan.EssH s a b (KdVPlan.dt u) ≤ C" := by
  intro s a b C u hC hu
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB s (KdVPlan.dt u t) C := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_of_forall_mem measurableSet_Ioo hu
  have hb := @yui_aux_0013 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b C (KdVPlan.dt u) hC hae
  refine ⟨⟨?_, hae.mono (fun _ h => h.1), hb.1⟩, hb.2⟩
  intro k
  exact (stronglyMeasurable_deriv (fun t => u t k)).aestronglyMeasurable

theorem yui_aux_0082 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (C M a τ : ℝ) (f w : KdVPlan.Coeff), 0 ≤ C →\nKdVPlan.StepData gamma M a τ f w → KdVPlan.LocalBounds C gamma M a τ f w →\nKdVPlan.UB 0 a (a+τ) (KdVPlan.z a f) (M+1+C) ∧\nKdVPlan.HB 0 (KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst a τ f)) (C*KdVPlan.localQ gamma τ f w)" := by
  intro C M a τ f w hC hd hl
  rcases hd with ⟨hM,ha,hτ,hτ1,hf,hw,hsf,hsw,hwM,hdist⟩
  rcases hl with ⟨hfn,hq,hF,hFd,hFag,hzX,hzN,hBFF,hQW,hinvB,hYd,hinvY,hYdae,hCst,hY,hYX,hYN,hYneg⟩
  have hq0 : 0 ≤ KdVPlan.localQ gamma τ f w :=
    add_nonneg (Real.rpow_nonneg hτ.le _) (Real.sqrt_nonneg _)
  have hinc := h_T013.2.2.2.1
  have hnorm := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013
  constructor
  · intro t ht
    have hFt := hF t ht
    have hF0 := hinc 0 1 (KdVPlan.F a f t) (by norm_num) hFt.1
    have hbF : KdVPlan.HB 0 (KdVPlan.F a f t) C := ⟨hF0.1, hF0.2.trans hFt.2⟩
    have hb := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1 0 (M+1) C f (KdVPlan.F a f t) ⟨hf.1,hfn⟩ hbF
    exact hb.1
  · have hab : a ∈ Set.Icc a (a+τ) := ⟨le_rfl,by linarith⟩
    have hw := hQW a hab
    have hbW : KdVPlan.HB 0 (KdVPlan.Wst a τ f) (C*τ*KdVPlan.localQ gamma τ f w) :=
      ⟨hw.2.1, by linarith [ (hnorm 0 (KdVPlan.Qst a f a)).1 ]⟩
    have hb := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 0 _ ((τ : ℂ)⁻¹) _ hbW
    have hc : ‖(τ : ℂ)⁻¹‖*(C*τ*KdVPlan.localQ gamma τ f w) = C*KdVPlan.localQ gamma τ f w := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      field_simp
    rw [hc] at hb
    exact hb

theorem yui_aux_0083 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ D : ℝ, 0 < D ∧ ∀ a τ f w,\nKdVPlan.StepData gamma M a τ f w →\n(KdVPlan.EssBound (-KdVPlan.pstar) a (a+τ) (KdVPlan.dt (KdVPlan.rho a τ f)) ∧\nKdVPlan.EssH (-KdVPlan.pstar) a (a+τ) (KdVPlan.dt (KdVPlan.rho a τ f)) ≤ D*KdVPlan.localQ gamma τ f w)" := by
  intro M hM
  rcases h_T008 M hM with ⟨C,hC,hCl⟩
  rcases h_T005.1.1 with ⟨B,hB,hBi,hBm,hBB,hBas⟩
  let D : ℝ := B*C*(M+1+C)+B*C^2+C
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro a τ f w hd
  have hl := hCl a τ f w hd
  have hzW := @yui_aux_0082 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 C M a τ f w hC.le hd hl
  have hq0 : 0 ≤ KdVPlan.localQ gamma τ f w :=
    add_nonneg (Real.rpow_nonneg hd.2.2.1.le _) (Real.sqrt_nonneg _)
  rcases hl with ⟨hfn,hq,hF,hFd,hFag,hzX,hzN,hBFF,hQW,hinvB,hYd,hinvY,hYdae,hCst,hY,hYX,hYN,hYneg⟩
  apply @yui_aux_0081 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (-KdVPlan.pstar) a (a+τ) (D*KdVPlan.localQ gamma τ f w) (KdVPlan.rho a τ f) (mul_nonneg hD.le hq0)
  intro t ht
  have htc : t ∈ Set.Icc a (a+τ) := ⟨ht.1.le,ht.2.le⟩
  have hy := hY t htc
  have hz := hzW.1 t htc
  have h1 := (hBB t _ _ hy.1 hz.1).1
  have h2 := (hBB t _ _ hy.1 hy.1).1
  have h3 := h_T013.2.2.2.1 (-KdVPlan.pstar) 0 _ (by norm_num [KdVPlan.pstar]) hzW.2.1
  have h3' : KdVPlan.HB (-KdVPlan.pstar) (KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst a τ f)) (C*KdVPlan.localQ gamma τ f w) :=
    ⟨h3.1,h3.2.trans hzW.2.2⟩
  have h1' := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 _ _ (-1) _ h1
  have h2' := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 _ _ (1/2) _ h2
  have hsum := ((@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1 _ _ _ _ _ (((@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1 _ _ _ _ _ h1' h2').2) h3').2
  have hr := (@yui_aux_0080 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hd.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.2.1 t ht).2
  rw [hr]
  have hn : KdVPlan.scale (-1) (KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.z a f t)) = -KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.z a f t) := by ext k; simp [KdVPlan.scale]
  rw [hn] at hsum
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  simp only [norm_neg, norm_one, one_mul, hhalf]
  have hzN0 := (@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (KdVPlan.z a f t)).1
  have hyN0 := (@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (KdVPlan.Yst a τ f t)).1
  have hmul1 : B*KdVPlan.hn 0 (KdVPlan.Yst a τ f t)*KdVPlan.hn 0 (KdVPlan.z a f t) ≤ B*(C*KdVPlan.localQ gamma τ f w)*(M+1+C) := by gcongr; exact hy.2; exact hz.2
  have hmul2 : B*KdVPlan.hn 0 (KdVPlan.Yst a τ f t)*KdVPlan.hn 0 (KdVPlan.Yst a τ f t) ≤ B*(C*KdVPlan.localQ gamma τ f w)*(C*KdVPlan.localQ gamma τ f w) := by gcongr; exact hy.2; exact hy.2
  have hq2 : (KdVPlan.localQ gamma τ f w)^2 ≤ 2*KdVPlan.localQ gamma τ f w := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hq2 (mul_nonneg hB.le (sq_nonneg C))
  dsimp [D]
  nlinarith

theorem yui_aux_0084 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (u : ℤ → ℝ → ℂ), (∀ k, Measurable (u k)) → Measurable (fun t => ∑' k, u k t)" := by
  intro u hu
  exact Measurable.tsum hu

theorem yui_aux_0085 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (μ : MeasureTheory.Measure ℝ) (u v : KdVPlan.Path), (∀ k, AEStronglyMeasurable (fun t => u t k) μ) → (∀ k, AEStronglyMeasurable (fun t => v t k) μ) →\n∀ k, AEStronglyMeasurable (fun t => KdVPlan.J t (u t) (v t) k) μ" := by
  intro μ u v hu hv k
  unfold KdVPlan.J KdVPlan.S KdVPlan.P
  split_ifs with hk
  · simp only [mul_zero]
    exact aestronglyMeasurable_const
  · apply AEStronglyMeasurable.mul
    · fun_prop
    · apply AEMeasurable.aestronglyMeasurable
      unfold KdVPlan.mul
      apply AEMeasurable.tsum
      intro j
      apply AEMeasurable.mul
      · apply AEMeasurable.mul
        · fun_prop
        · simp only [KdVPlan.invD]
          split_ifs
          · exact aemeasurable_const
          · exact aemeasurable_const.mul (hu j).aemeasurable
      · apply AEMeasurable.mul
        · fun_prop
        · simp only [KdVPlan.invD]
          split_ifs
          · exact aemeasurable_const
          · exact aemeasurable_const.mul (hv (k-j)).aemeasurable

theorem yui_aux_0086 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path), KdVPlan.ContH s a b u → ∀ k, ContinuousOn (fun t => u t k) (Set.Icc a b)" := by
  intro s a b u hu k
  apply Metric.continuousOn_iff.mpr
  intro t ht ε hε
  let A := |KdVPlan.weight (-s/2) k|+1
  have hA : 0 < A := by dsimp [A]; positivity
  rcases hu.2 t ht (ε/A) (div_pos hε hA) with ⟨δ,hδ,hd⟩
  refine ⟨δ,hδ,?_⟩
  intro r hr hrt
  have hn := hd r hr (by simpa only [Real.dist_eq] using hrt)
  have hb := @yui_aux_0060 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s (u r-u t) (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s _ _ (hu.1 r hr) (hu.1 t ht)).1 k
  rw [dist_eq_norm]
  change ‖(u r-u t) k‖ < ε
  have hN := (@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s (u r-u t)).1
  have hw : KdVPlan.weight (-s/2) k ≤ A := by dsimp [A]; linarith [le_abs_self (KdVPlan.weight (-s/2) k)]
  have hbound := mul_le_mul_of_nonneg_right hw hN
  have hlt := (mul_lt_mul_of_pos_left hn hA)
  have heq : A*(ε/A)=ε := by field_simp
  rw [heq] at hlt
  exact hb.trans_lt (hbound.trans_lt hlt)

theorem yui_aux_0087 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (u : KdVPlan.Path), a ≤ b → (∀ k, AEStronglyMeasurable (fun t => u t k) (volume.restrict (Set.Icc a b))) → (∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB s (u t) C) → ∀ k, IntervalIntegrable (fun t => u t k) volume a b" := by
  intro s a b C u hab hm hb k
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply IntegrableOn.of_bound (by simp) (hm k) (|KdVPlan.weight (-s/2) k| *C)
  filter_upwards [hb] with t ht
  have he := @yui_aux_0060 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s (u t) ht.1 k
  have hn := (@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s (u t)).1
  calc
    ‖u t k‖ ≤ KdVPlan.weight (-s/2) k*KdVPlan.hn s (u t) := he
    _ ≤ |KdVPlan.weight (-s/2) k| *KdVPlan.hn s (u t) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hn
    _ ≤ |KdVPlan.weight (-s/2) k| *C := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)

theorem yui_aux_0088 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b l r : ℝ) (u : KdVPlan.Path), a ≤ l → r ≤ b → KdVPlan.EssBound s a b u →\nKdVPlan.EssBound s l r u ∧ KdVPlan.EssH s l r u ≤ KdVPlan.EssH s a b u" := by
  intro s a b l r u hal hrb hu
  have hsub : Set.Icc l r ⊆ Set.Icc a b := Set.Icc_subset_Icc hal hrb
  have hm : volume.restrict (Set.Icc l r) ≤ volume.restrict (Set.Icc a b) := Measure.restrict_mono hsub le_rfl
  have he : essSup (fun t => ENNReal.ofReal (KdVPlan.hn s (u t))) (volume.restrict (Set.Icc l r)) ≤
    essSup (fun t => ENNReal.ofReal (KdVPlan.hn s (u t))) (volume.restrict (Set.Icc a b)) :=
    essSup_mono_measure' hm
  refine ⟨⟨fun k => (hu.1 k).mono_measure hm, ?_, he.trans_lt hu.2.2⟩, ?_⟩
  · exact ae_mono hm hu.2.1
  · exact ENNReal.toReal_mono (ne_of_lt hu.2.2) he

theorem yui_aux_0089 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (s a b l r : ℝ) (u : KdVPlan.Path), a ≤ l → r ≤ b → KdVPlan.ContH s a b u → KdVPlan.ContH s l r u) ∧\n(∀ (a b l r : ℝ) (u : KdVPlan.Path), a ≤ l → r ≤ b → KdVPlan.Piecewise a b u → KdVPlan.Piecewise l r u) ∧\n(∀ (a b l r : ℝ) (u du : KdVPlan.Path), a ≤ l → r ≤ b →\n KdVPlan.EssBound 0 a b u → KdVPlan.EssBound (-KdVPlan.pstar) a b du →\n KdVPlan.Xnorm l r u du ≤ KdVPlan.Xnorm a b u du)" := by
  have hc : ∀ (s a b l r : ℝ) (u : KdVPlan.Path), a ≤ l → r ≤ b → KdVPlan.ContH s a b u → KdVPlan.ContH s l r u := by
    intro s a b l r u hal hrb hu
    have hs := Set.Icc_subset_Icc hal hrb
    refine ⟨fun t ht => hu.1 t (hs ht),?_⟩
    intro t ht ε hε
    rcases hu.2 t (hs ht) ε hε with ⟨δ,hδ,hd⟩
    exact ⟨δ,hδ,fun x hx hxt => hd x (hs hx) hxt⟩
  refine ⟨hc,?_,?_⟩
  · intro a b l r u hal hrb hu
    refine ⟨fun m => hc _ _ _ _ _ _ hal hrb (hu.1 m),?_⟩
    rcases hu.2 with ⟨p,hp⟩
    exact ⟨p,fun x y hx hxy hy hpxy => hp x y (hal.trans hx) hxy (hy.trans hrb) hpxy⟩
  · intro a b l r u du hal hrb hu hdu
    exact add_le_add (@yui_aux_0088 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b l r u hal hrb hu).2
      (@yui_aux_0088 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (-KdVPlan.pstar) a b l r du hal hrb hdu).2

theorem yui_aux_0090 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (u : KdVPlan.Path), 0 ≤ C → KdVPlan.ContH s a b u → KdVPlan.UB s a b u C →\nKdVPlan.EssBound s a b u ∧ KdVPlan.EssH s a b u ≤ C" := by
  intro s a b C u hC hc hb
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB s (u t) C :=
    ae_restrict_of_forall_mem measurableSet_Icc hb
  have he := @yui_aux_0013 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b C u hC hae
  refine ⟨⟨?_,hae.mono (fun _ h => h.1),he.1⟩,he.2⟩
  intro k
  exact (@yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b u hc k).aestronglyMeasurable measurableSet_Icc

theorem yui_aux_0091 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s r a b : ℝ) (u : KdVPlan.Path), s ≤ r → KdVPlan.ContH r a b u → KdVPlan.ContH s a b u" := by
  intro s r a b u hsr hu
  have hi := h_T013.2.2.2.1
  refine ⟨fun t ht => (hi s r (u t) hsr (hu.1 t ht)).1,?_⟩
  intro t ht ε hε
  rcases hu.2 t ht ε hε with ⟨δ,hδ,hd⟩
  refine ⟨δ,hδ,?_⟩
  intro x hx hxt
  have hm := (@yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 r (u x) (u t) (hu.1 x hx) (hu.1 t ht)).1
  exact (hi s r _ hsr hm).2.trans_lt (hd x hx hxt)

theorem yui_aux_0092 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ s : ℝ, KdVPlan.HB s 0 0) ∧\n(∀ (a b : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH 0 f →\nKdVPlan.Xnorm a b (fun _ => f) (KdVPlan.dt (fun _ => f)) ≤ KdVPlan.hn 0 f)" := by
  have hz : ∀ s : ℝ, KdVPlan.HB s 0 0 := by
    intro s
    simp [KdVPlan.HB,KdVPlan.MemH,KdVPlan.hn]
  refine ⟨hz,?_⟩
  intro a b f hf
  have hc := @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b f hf
  have h1 := @yui_aux_0090 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b (KdVPlan.hn 0 f) (fun _ => f) (Real.sqrt_nonneg _) hc (fun _ _ => ⟨hf,le_rfl⟩)
  have hd : KdVPlan.dt (fun _ : ℝ => f) = fun _ => 0 := by
    ext t k
    simp [KdVPlan.dt]
  have h2 := @yui_aux_0081 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (-KdVPlan.pstar) a b 0 (fun _ => f) le_rfl (by
    intro t ht
    rw [hd]
    exact hz _)
  dsimp [KdVPlan.Xnorm]
  linarith [ENNReal.toReal_nonneg (a := essSup (fun t => ENNReal.ofReal (KdVPlan.hn 0 f)) (volume.restrict (Set.Icc a b)))]

theorem yui_aux_0093 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (c d : ℂ) (f g : KdVPlan.Coeff), KdVPlan.J t (KdVPlan.scale c f) (KdVPlan.scale d g) = KdVPlan.scale (c*d) (KdVPlan.J t f g)" := by
  intro t c d f g
  have hi : ∀ (z : ℂ) (u : KdVPlan.Coeff), KdVPlan.invD (KdVPlan.scale z u) = KdVPlan.scale z (KdVPlan.invD u) := by
    intro z u
    ext k
    simp only [KdVPlan.invD,KdVPlan.scale]
    split_ifs <;> ring
  have hs := (@yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2
  unfold KdVPlan.J
  rw [hi, hi, hs, hs, (@yui_aux_0046 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1]
  have hp : ∀ (z : ℂ) (u : KdVPlan.Coeff), KdVPlan.P (KdVPlan.scale z u) = KdVPlan.scale z (KdVPlan.P u) := by
    intro z u
    ext k
    simp only [KdVPlan.P,KdVPlan.scale]
    split_ifs <;> simp
  rw [hp,hs]

theorem yui_aux_0094 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.HB s (KdVPlan.P f) (KdVPlan.hn s f)" := by
  intro s f hf
  have hn : ∀ k, 0 ≤ KdVPlan.weight s k*‖KdVPlan.P f k‖^2 := by
    intro k
    unfold KdVPlan.weight
    positivity
  have hle : ∀ k, KdVPlan.weight s k*‖KdVPlan.P f k‖^2 ≤ KdVPlan.weight s k*‖f k‖^2 := by
    intro k
    unfold KdVPlan.P
    split_ifs
    · simp only [norm_zero,zero_pow (by decide : 2≠0),mul_zero]
      unfold KdVPlan.weight
      positivity
    · exact le_rfl
  have hs : KdVPlan.MemH s (KdVPlan.P f) := Summable.of_nonneg_of_le hn hle hf
  refine ⟨hs,?_⟩
  have hsum := hs.tsum_le_tsum hle hf
  have hp := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s (KdVPlan.P f)
  have hf' := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s f
  rw [← hp.2,← hf'.2] at hsum
  nlinarith [hp.1,hf'.1]

theorem yui_aux_0095 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b A C E : ℝ) (u v : KdVPlan.Path), a ≤ b → 0 ≤ C →\nKdVPlan.Piecewise a b u → KdVPlan.Piecewise a b v →\n(∀ t ∈ Set.Icc a b, KdVPlan.ZeroMean (u t)) → (∀ t ∈ Set.Icc a b, KdVPlan.ZeroMean (v t)) →\nKdVPlan.HB 0 (KdVPlan.J b (u b) (v b)) A → KdVPlan.HB 0 (KdVPlan.J a (u a) (v a)) A →\n(∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB 0 (KdVPlan.J t (KdVPlan.dt u t) (v t)) C) →\n(∀ k, IntervalIntegrable (fun t => KdVPlan.J t (u t) (KdVPlan.dt v t) k) volume a b) →\nKdVPlan.HB 0 (KdVPlan.timeInt a b (fun t => KdVPlan.J t (u t) (KdVPlan.dt v t))) E →\nKdVPlan.HB 0 (KdVPlan.timeInt a b (fun t => KdVPlan.B t (u t) (v t))) ((2*A+(b-a)*C+E)/3)" := by
  intro a b A C E u v hab hC hu hv hzu hzv hJb hJa hJdu hInt hJdv
  have hvm : ∀ k, AEStronglyMeasurable (fun t => v t k) (volume.restrict (Set.Icc a b)) := by
    intro k
    exact (@yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b v (by simpa using hv.1 0) k).aestronglyMeasurable measurableSet_Icc
  have hdm : ∀ k, AEStronglyMeasurable (fun t => KdVPlan.dt u t k) (volume.restrict (Set.Icc a b)) :=
    fun k => (stronglyMeasurable_deriv (fun t => u t k)).aestronglyMeasurable
  have hmeas := @yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (volume.restrict (Set.Icc a b)) (KdVPlan.dt u) v hdm hvm
  have hintdu := @yui_aux_0087 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b C _ hab hmeas hJdu
  have hJdu' : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → KdVPlan.HB 0 (KdVPlan.J t (KdVPlan.dt u t) (v t)) C := by
    rw [ae_restrict_iff' measurableSet_Icc] at hJdu
    exact hJdu.mono (fun _ h ht => h ⟨ht.1.le,ht.2⟩)
  have hdu := @yui_aux_0067 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b C _ hab hC hintdu hJdu'
  have hadd : KdVPlan.timeInt a b (fun t => KdVPlan.J t (KdVPlan.dt u t) (v t)+KdVPlan.J t (u t) (KdVPlan.dt v t)) =
   KdVPlan.timeInt a b (fun t => KdVPlan.J t (KdVPlan.dt u t) (v t)) + KdVPlan.timeInt a b (fun t => KdVPlan.J t (u t) (KdVPlan.dt v t)) := by
    ext k
    exact intervalIntegral.integral_add (hintdu k) (hInt k)
  rw [h_T005.2.2.1 a b u v hab hu hv hzu hzv,hadd]
  have hbounds := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1
  have hs := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1
  have hb := (hbounds 0 A A _ _ hJb hJa).2
  have hi := (hbounds 0 _ E _ _ hdu hJdv).1
  have ht := (hbounds 0 _ _ _ _ (hs 0 _ (1/3) _ hb) (hs 0 _ (1/3) _ hi)).2
  convert ht using 1 <;> norm_num <;> ring

theorem yui_aux_0096 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ u : KdVPlan.Path, (∀ t, KdVPlan.ZeroMean (u t)) → ∀ t, KdVPlan.ZeroMean (KdVPlan.dt u t)" := by
  intro u hu t
  have he : (fun r => u r 0) = fun _ => (0 : ℂ) := funext hu
  change deriv (fun r => u r 0) t=0
  rw [he]
  simp

theorem yui_aux_0097 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ K : ℝ, 0 < K ∧ ∀ (a b A B C : ℝ) (u : KdVPlan.Path), a ≤ b → 0 ≤ A → 0 ≤ B → 0 ≤ C →\nKdVPlan.Piecewise a b u → (∀ t, KdVPlan.ZeroMean (u t)) →\nKdVPlan.UB 0 a b u B → KdVPlan.UB 0 a b (fun t => KdVPlan.invD (u t)) A →\n(∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB 0 (KdVPlan.invD (KdVPlan.dt u t)) C) →\nKdVPlan.HB 0 (KdVPlan.timeInt a b (fun t => KdVPlan.B t (u t) (u t))) ((2*K*A*B+2*(b-a)*K*C*B)/3)" := by
  rcases h_T005.1.1 with ⟨K,hK,hi,hm,hB,hJ⟩
  refine ⟨K,hK,?_⟩
  intro a b A B C u hab hA hB0 hC hu hzu hub hui hud
  have hzd := @yui_aux_0096 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 u hzu
  have hboundary : ∀ t ∈ Set.Icc a b, KdVPlan.HB 0 (KdVPlan.J t (u t) (u t)) (K*A*B) := by
    intro t ht
    have hb := (hJ t (u t) (u t) (hzu t) (hui t ht).1 (hub t ht).1).2
    refine ⟨hb.1,hb.2.trans ?_⟩
    have hN : 0 ≤ KdVPlan.hn 0 (u t) := Real.sqrt_nonneg _
    gcongr
    · exact (hui t ht).2
    · exact (hub t ht).2
  have hdJ : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB 0 (KdVPlan.J t (KdVPlan.dt u t) (u t)) (K*C*B) := by
    filter_upwards [hud,ae_restrict_mem measurableSet_Icc] with t ht hti
    have hb := (hJ t _ _ (hzd t) ht.1 (hub t hti).1).2
    refine ⟨hb.1,hb.2.trans ?_⟩
    have hN : 0 ≤ KdVPlan.hn 0 (u t) := Real.sqrt_nonneg _
    gcongr
    · exact ht.2
    · exact (hub t hti).2
  have hum : ∀ k, AEStronglyMeasurable (fun t => u t k) (volume.restrict (Set.Icc a b)) :=
    fun k => (@yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b u (by simpa using hu.1 0) k).aestronglyMeasurable measurableSet_Icc
  have hdm : ∀ k, AEStronglyMeasurable (fun t => KdVPlan.dt u t k) (volume.restrict (Set.Icc a b)) :=
    fun k => (stronglyMeasurable_deriv (fun t => u t k)).aestronglyMeasurable
  have hsym : (fun t => KdVPlan.J t (u t) (KdVPlan.dt u t)) = (fun t => KdVPlan.J t (KdVPlan.dt u t) (u t)) := by
    funext t
    exact ((@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 t _ _).2
  have hdJ' : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB 0 (KdVPlan.J t (u t) (KdVPlan.dt u t)) (K*C*B) := by
    filter_upwards [hdJ] with t ht
    rw [((@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 t _ _).2]
    exact ht
  have hint := @yui_aux_0087 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b (K*C*B) _ hab (@yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ u (KdVPlan.dt u) hum hdm) hdJ'
  have hbint := @yui_aux_0067 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b (K*C*B) _ hab (by positivity) hint (by
    rw [ae_restrict_iff' measurableSet_Icc] at hdJ'
    exact hdJ'.mono (fun t h ht => h ⟨ht.1.le,ht.2⟩))
  have hb := @yui_aux_0095 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b (K*A*B) (K*C*B) ((b-a)*(K*C*B)) u u hab (by positivity) hu hu (fun t _ => hzu t) (fun t _ => hzu t)
    (hboundary b ⟨hab,le_rfl⟩) (hboundary a ⟨le_rfl,hab⟩) hdJ hint hbint
  convert hb using 1 <;> ring

theorem yui_aux_0098 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (C M : ℝ), 0 ≤ C → ∃ D : ℝ, 0 < D ∧ ∀ a τ f w, KdVPlan.StepData gamma M a τ f w → KdVPlan.LocalBounds C gamma M a τ f w →\nKdVPlan.UB 0 a (a+τ) (fun t => KdVPlan.timeInt a t (fun s => KdVPlan.B s (KdVPlan.Yst a τ f s) (KdVPlan.Yst a τ f s))) (D*τ*KdVPlan.localQ gamma τ f w)" := by
  intro C M hC
  rcases @yui_aux_0097 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 with ⟨K,hK,hKK⟩
  refine ⟨1+4*K*C^2,by positivity,?_⟩
  intro a τ f w hd hl t ht
  have hτ : 0 < τ := hd.2.2.1
  rcases hl with ⟨hfn,hq,hF,hFd,hFag,hzX,hzN,hBFF,hQW,hinvB,hYd,hinvY,hYdae,hCst,hY,hYX,hYN,hYneg⟩
  have hq0 : 0 ≤ KdVPlan.localQ gamma τ f w :=
    add_nonneg (Real.rpow_nonneg hd.2.2.1.le _) (Real.sqrt_nonneg _)
  have hy := (@yui_aux_0055 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hd.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.2.1).2
  have hy' := (@yui_aux_0089 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 a (a+τ) a t _ le_rfl ht.2 hy
  have hb := hKK a t (C*τ*KdVPlan.localQ gamma τ f w) (C*KdVPlan.localQ gamma τ f w) (C*KdVPlan.localQ gamma τ f w)
    (KdVPlan.Yst a τ f) ht.1 (by positivity) (by positivity) (by positivity) hy'
    (fun r => ((@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2 a τ f hd.2.2.2.2.1.2.1 r).2)
    (fun r hr => hY r ⟨hr.1,hr.2.trans ht.2⟩)
    (fun r hr => hinvY r ⟨hr.1,hr.2.trans ht.2⟩)
    (ae_mono (Measure.restrict_mono (Set.Icc_subset_Icc le_rfl ht.2) le_rfl) hYdae)
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hq2 : (KdVPlan.localQ gamma τ f w)^2 ≤ 2*KdVPlan.localQ gamma τ f w := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hq2 (mul_nonneg (mul_nonneg hK.le (sq_nonneg C)) hd.2.2.1.le)
  have htime := mul_le_mul_of_nonneg_right (show t-a ≤ τ by linarith only [ht.2]) (mul_nonneg (mul_nonneg hK.le (sq_nonneg C)) (sq_nonneg (KdVPlan.localQ gamma τ f w)))
  have hτq := mul_nonneg hτ.le hq0
  have hnon : 0 ≤ K*C^2*τ*KdVPlan.localQ gamma τ f w := by positivity
  nlinarith only [hmul,htime,hτq,hnon]

theorem yui_aux_0099 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (C M : ℝ), 0 ≤ C → ∃ D : ℝ, 0 < D ∧ ∀ a τ f w, KdVPlan.StepData gamma M a τ f w → KdVPlan.LocalBounds C gamma M a τ f w →\nKdVPlan.UB 0 a (a+τ) (fun t => KdVPlan.tri a t (fun _ => f) (fun _ => f) (KdVPlan.Yst a τ f)) (D*τ*KdVPlan.localQ gamma τ f w)" := by
  intro C M hC
  rcases h_T006.1.1 with ⟨K,hK,hKt⟩
  refine ⟨1+2*K*C*(M+1)^2,by positivity,?_⟩
  intro a τ f w hd hl t ht
  have hτ : 0 < τ := hd.2.2.1
  have hMpos : 0 ≤ M+1 := by linarith only [hd.1]
  have hf := hd.2.2.2.2.1
  have hsf := hd.2.2.2.2.2.2.1
  rcases hl with ⟨hfn,hq,hF,hFd,hFag,hzX,hzN,hBFF,hQW,hinvB,hYd,hinvY,hYdae,hCst,hY,hYX,hYN,hYneg⟩
  have hq0 : 0 ≤ KdVPlan.localQ gamma τ f w :=
    add_nonneg (Real.rpow_nonneg hτ.le _) (Real.sqrt_nonneg _)
  have hy := (@yui_aux_0055 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hsf).2
  have hy' := (@yui_aux_0089 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 a (a+τ) a t _ le_rfl ht.2 hy
  have hc := @yui_aux_0054 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a t f hsf
  have hz := (@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2 a τ f hf.2.1
  have hb := (hKt a t hd.2.1 ht.1 (by linarith only [ht.2,hd.2.2.2.1]) (fun _ => f) (fun _ => f) (KdVPlan.Yst a τ f) hc hc hy' (fun r _ => ⟨hf.2.1,hf.2.1,(hz r).2⟩)).2.2
  have hxY := ((@yui_aux_0089 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2 a (a+τ) a t (KdVPlan.Yst a τ f) (KdVPlan.dt (KdVPlan.Yst a τ f)) le_rfl ht.2 hYX.2.1 hYX.2.2).trans hYN
  have hxF := ((@yui_aux_0092 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2 a t f hf.1).trans hfn
  have heF := (@yui_aux_0090 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a t (KdVPlan.hn 0 f) (fun _ => f) (Real.sqrt_nonneg _) (@yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a t f hf.1) (fun _ _ => ⟨hf.1,le_rfl⟩)).2.trans hfn
  have hycont : KdVPlan.ContH (-KdVPlan.pstar) a t (KdVPlan.Yst a τ f) :=
    @yui_aux_0091 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (-KdVPlan.pstar) 0 a t _ (by norm_num [KdVPlan.pstar]) (by simpa using hy'.1 0)
  have heY := (@yui_aux_0090 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (-KdVPlan.pstar) a t (C*τ*KdVPlan.localQ gamma τ f w) _ (by positivity) hycont (fun r hr => hYneg r ⟨hr.1,hr.2.trans ht.2⟩)).2
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hEss : ∀ s (u : KdVPlan.Path), 0 ≤ KdVPlan.EssH s a t u := fun _ _ => ENNReal.toReal_nonneg
  have hX0 : 0 ≤ KdVPlan.Xnorm a t (fun _ => f) (KdVPlan.dt (fun _ => f)) := add_nonneg (hEss _ _) (hEss _ _)
  have hXY0 : 0 ≤ KdVPlan.Xnorm a t (KdVPlan.Yst a τ f) (KdVPlan.dt (KdVPlan.Yst a τ f)) := add_nonneg (hEss _ _) (hEss _ _)
  have htime : 0 ≤ t-a := sub_nonneg.mpr ht.1
  have h1 : K*(t-a)*KdVPlan.Xnorm a t (fun _ => f) (KdVPlan.dt (fun _ => f))*KdVPlan.Xnorm a t (fun _ => f) (KdVPlan.dt (fun _ => f))*KdVPlan.Xnorm a t (KdVPlan.Yst a τ f) (KdVPlan.dt (KdVPlan.Yst a τ f)) ≤ K*(t-a)*(M+1)*(M+1)*(C*KdVPlan.localQ gamma τ f w) := by
    gcongr <;> first | assumption | positivity
  have h2 : K*KdVPlan.EssH (-KdVPlan.pstar) a t (KdVPlan.Yst a τ f)*KdVPlan.EssH 0 a t (fun _ => f)*KdVPlan.EssH 0 a t (fun _ => f) ≤ K*(C*τ*KdVPlan.localQ gamma τ f w)*(M+1)*(M+1) := by
    gcongr <;> first | assumption | exact hEss _ _ | positivity
  have htime2 := mul_le_mul_of_nonneg_right (show t-a ≤ τ by linarith only [ht.2]) (show 0 ≤ K*(M+1)^2*C*KdVPlan.localQ gamma τ f w by positivity)
  have hτq := mul_nonneg hτ.le hq0
  nlinarith only [h1,h2,htime2,hτq]

theorem yui_aux_0100 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH 1 f →\nKdVPlan.HB 0 (KdVPlan.invD (KdVPlan.B t f f)) (K*KdVPlan.hn 1 f*KdVPlan.hn 1 f)" := by
  rcases h_T005.1.1 with ⟨K,hK,hi,hm,hB,hJ⟩
  refine ⟨K,hK,?_⟩
  intro t f hf
  have hSf := (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 1 t f).1.mpr hf
  have hmul := hm (KdVPlan.S t f) (KdVPlan.S t f) hSf hSf
  have hP := @yui_aux_0094 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 1 _ hmul.1
  have hP0 := h_T013.2.2.2.1 0 1 _ (by norm_num) hP.1
  have he : KdVPlan.invD (KdVPlan.B t f f) = KdVPlan.S (-t) (KdVPlan.P (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t f))) := by
    ext k
    simp only [KdVPlan.invD,KdVPlan.B,KdVPlan.S,KdVPlan.dx,KdVPlan.P]
    split_ifs with hk
    · simp
    · have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hiC : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hkC
      field_simp
      <;> ring
  rw [he]
  have hS := @yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (-t) (KdVPlan.P (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t f)))
  refine ⟨hS.1.mpr hP0.1,?_⟩
  rw [hS.2]
  calc
    _ ≤ KdVPlan.hn 1 (KdVPlan.P (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t f))) := hP0.2
    _ ≤ KdVPlan.hn 1 (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t f)) := hP.2
    _ ≤ K*KdVPlan.hn 1 (KdVPlan.S t f)*KdVPlan.hn 1 (KdVPlan.S t f) := hmul.2
    _ = _ := by rw [(@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 1 t f).2]

theorem yui_aux_0101 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Coeff) (u : KdVPlan.Path), a ≤ b → KdVPlan.Data 0 f → KdVPlan.Smooth f → KdVPlan.Piecewise a b u → (∀ t ∈ Set.Icc a b, KdVPlan.ZeroMean (u t)) →\nKdVPlan.timeInt a b (fun t => KdVPlan.J t (u t) (KdVPlan.dt (KdVPlan.z a f) t)) =\nKdVPlan.scale (1/2) (KdVPlan.tri a b (fun _ => f) (fun _ => f) u)" := by
  intro a b f u hab hf hs hu hzu
  have h1 : ∀ g : KdVPlan.Coeff, KdVPlan.scale 1 g=g := by intro g; ext k; simp [KdVPlan.scale]
  have he : (fun t => KdVPlan.J t (u t) (KdVPlan.dt (KdVPlan.z a f) t)) =
    fun t => KdVPlan.scale (1/2) (KdVPlan.J t (KdVPlan.B t f f) (u t)) := by
    funext t
    rw [(@yui_aux_0059 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a f hf.1).2 t, ((@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 t _ _).2]
    have hj := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t (1/2) 1 (KdVPlan.B t f f) (u t)
    simpa only [h1,mul_one] using hj
  rw [he,(@yui_aux_0046 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1]
  have hc := @yui_aux_0054 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b f hs
  rw [h_T005.2.2.2.1 a b (fun _ => f) (fun _ => f) u hab hc hc hu (fun t ht => ⟨hf.2.1,hf.2.1,hzu t ht⟩)]

theorem yui_aux_0102 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b B : ℝ) (f : KdVPlan.Coeff) (u : KdVPlan.Path), a ≤ b → KdVPlan.Data 0 f → KdVPlan.Smooth f → KdVPlan.ContH 0 a b u → KdVPlan.UB 0 a b u B →\n∀ k, IntervalIntegrable (fun t => KdVPlan.J t (u t) (KdVPlan.dt (KdVPlan.z a f) t) k) volume a b" := by
  intro a b B f u hab hf hs hu hub
  rcases @yui_aux_0100 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 with ⟨K0,hK0,hKf⟩
  rcases h_T005.1.1 with ⟨K,hK,hi,hm,hB,hJ⟩
  have hf1 : KdVPlan.MemH 1 f := by simpa using hs 1
  have hn1 : 0 ≤ KdVPlan.hn 1 f := Real.sqrt_nonneg _
  have hum : ∀ k, AEStronglyMeasurable (fun t => u t k) (volume.restrict (Set.Icc a b)) :=
    fun k => (@yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b u hu k).aestronglyMeasurable measurableSet_Icc
  have hdm : ∀ k, AEStronglyMeasurable (fun t => KdVPlan.dt (KdVPlan.z a f) t k) (volume.restrict (Set.Icc a b)) :=
    fun k => (stronglyMeasurable_deriv (fun t => KdVPlan.z a f t k)).aestronglyMeasurable
  apply @yui_aux_0087 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b ((1/2)*(K*(K0*KdVPlan.hn 1 f*KdVPlan.hn 1 f)*B)) _ hab (@yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ u _ hum hdm)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro t ht
  have hbF := hKf t f hf1
  have hzB : KdVPlan.ZeroMean (KdVPlan.B t f f) := by simp [KdVPlan.ZeroMean,KdVPlan.B,KdVPlan.S,KdVPlan.dx]
  have hb := (hJ t _ _ hzB hbF.1 (hub t ht).1).2
  have hb' : KdVPlan.HB 0 (KdVPlan.J t (KdVPlan.B t f f) (u t)) (K*(K0*KdVPlan.hn 1 f*KdVPlan.hn 1 f)*B) := by
    refine ⟨hb.1,hb.2.trans ?_⟩
    have hnu : 0 ≤ KdVPlan.hn 0 (u t) := Real.sqrt_nonneg _
    gcongr
    · exact hbF.2
    · exact (hub t ht).2
  have h1 : KdVPlan.scale 1 (u t)=u t := by ext k; simp [KdVPlan.scale]
  have he : KdVPlan.J t (u t) (KdVPlan.dt (KdVPlan.z a f) t) = KdVPlan.scale (1/2) (KdVPlan.J t (KdVPlan.B t f f) (u t)) := by
    rw [(@yui_aux_0059 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a f hf.1).2 t,((@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 t _ _).2]
    simpa only [h1,mul_one] using @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 t (1/2) 1 (KdVPlan.B t f f) (u t)
  rw [he]
  convert (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 0 _ (1/2) _ hb' using 1 <;> norm_num

theorem yui_aux_0103 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (C M : ℝ), 0 ≤ C → 1 ≤ M → ∃ D : ℝ, 0 < D ∧ ∀ a τ f w, KdVPlan.StepData gamma M a τ f w → KdVPlan.LocalBounds C gamma M a τ f w →\nKdVPlan.UB 0 a (a+τ) (fun t => KdVPlan.timeInt a t (fun s => KdVPlan.B s (KdVPlan.Yst a τ f s) (KdVPlan.z a f s))) (D*τ*KdVPlan.localQ gamma τ f w)" := by
  intro C M hC hM
  rcases @yui_aux_0099 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 C M hC with ⟨Dtri,hDtri,htri⟩
  rcases h_T005.1.1 with ⟨K,hK,hi,hm,hB,hJ⟩
  have hMpos : 0 ≤ M+1+C := by linarith
  refine ⟨1+K*C*(M+1+C)+Dtri,by positivity,?_⟩
  intro a τ f w hd hl t ht
  have hτ : 0 < τ := hd.2.2.1
  have hf := hd.2.2.2.2.1
  have hsf := hd.2.2.2.2.2.2.1
  have hzW := @yui_aux_0082 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 C M a τ f w hC hd hl
  have htrit := htri a τ f w hd hl t ht
  rcases hl with ⟨hfn,hq,hF,hFd,hFag,hzX,hzN,hBFF,hQW,hinvB,hYd,hinvY,hYdae,hCst,hY,hYX,hYN,hYneg⟩
  have hq0 : 0 ≤ KdVPlan.localQ gamma τ f w :=
    add_nonneg (Real.rpow_nonneg hτ.le _) (Real.sqrt_nonneg _)
  have hzy := @yui_aux_0055 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hf hsf
  have hy' := (@yui_aux_0089 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 a (a+τ) a t _ le_rfl ht.2 hzy.2
  have hz' := (@yui_aux_0089 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 a (a+τ) a t _ le_rfl ht.2 hzy.1
  have hzero := (@yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.2 a τ f hf.2.1
  have hzeroD := @yui_aux_0096 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 (KdVPlan.Yst a τ f) (fun r => (hzero r).2)
  have hbound : ∀ r ∈ Set.Icc a t, KdVPlan.HB 0 (KdVPlan.J r (KdVPlan.Yst a τ f r) (KdVPlan.z a f r)) (K*(C*τ*KdVPlan.localQ gamma τ f w)*(M+1+C)) := by
    intro r hr
    have hr' : r ∈ Set.Icc a (a+τ) := ⟨hr.1,hr.2.trans ht.2⟩
    have hb := (hJ r _ _ (hzero r).2 (hinvY r hr').1 (hzW.1 r hr').1).2
    refine ⟨hb.1,hb.2.trans ?_⟩
    have hn : 0 ≤ KdVPlan.hn 0 (KdVPlan.z a f r) := Real.sqrt_nonneg _
    gcongr
    · exact (hinvY r hr').2
    · exact (hzW.1 r hr').2
  have hderiv : ∀ᵐ r ∂(volume.restrict (Set.Icc a t)), KdVPlan.HB 0 (KdVPlan.J r (KdVPlan.dt (KdVPlan.Yst a τ f) r) (KdVPlan.z a f r)) (K*(C*KdVPlan.localQ gamma τ f w)*(M+1+C)) := by
    have hdae := ae_mono (Measure.restrict_mono (Set.Icc_subset_Icc le_rfl ht.2) le_rfl) hYdae
    filter_upwards [hdae,ae_restrict_mem measurableSet_Icc] with r hr hri
    have hr' : r ∈ Set.Icc a (a+τ) := ⟨hri.1,hri.2.trans ht.2⟩
    have hb := (hJ r _ _ (hzeroD r) hr.1 (hzW.1 r hr').1).2
    refine ⟨hb.1,hb.2.trans ?_⟩
    have hn : 0 ≤ KdVPlan.hn 0 (KdVPlan.z a f r) := Real.sqrt_nonneg _
    gcongr
    · exact hr.2
    · exact (hzW.1 r hr').2
  have hcubic : KdVPlan.HB 0 (KdVPlan.timeInt a t (fun r => KdVPlan.J r (KdVPlan.Yst a τ f r) (KdVPlan.dt (KdVPlan.z a f) r))) ((1/2)*(Dtri*τ*KdVPlan.localQ gamma τ f w)) := by
    rw [@yui_aux_0101 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a t f _ ht.1 hf hsf hy' (fun r _ => (hzero r).2)]
    convert (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1 0 _ (1/2) _ htrit using 1 <;> norm_num
  have hint := @yui_aux_0102 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a t (C*KdVPlan.localQ gamma τ f w) f (KdVPlan.Yst a τ f) ht.1 hf hsf (by simpa using hy'.1 0) (fun r hr => hY r ⟨hr.1,hr.2.trans ht.2⟩)
  have hb := @yui_aux_0095 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a t (K*(C*τ*KdVPlan.localQ gamma τ f w)*(M+1+C)) (K*(C*KdVPlan.localQ gamma τ f w)*(M+1+C)) ((1/2)*(Dtri*τ*KdVPlan.localQ gamma τ f w)) _ _ ht.1 (by positivity) hy' hz' (fun r _ => (hzero r).2) (fun r _ => (hzero r).1)
    (hbound t ⟨ht.1,le_rfl⟩) (hbound a ⟨le_rfl,ht.1⟩) hderiv hint hcubic
  refine ⟨hb.1,hb.2.trans ?_⟩
  have htime := mul_le_mul_of_nonneg_right (show t-a ≤ τ by linarith only [ht.2]) (show 0 ≤ K*C*(M+1+C)*KdVPlan.localQ gamma τ f w by positivity)
  have hτq := mul_nonneg hτ.le hq0
  have hDτq : 0 ≤ Dtri*τ*KdVPlan.localQ gamma τ f w := by positivity
  nlinarith only [htime,hτq,hDτq]

theorem yui_aux_0104 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ a τ f w, KdVPlan.StepData gamma M a τ f w → KdVPlan.StepResidual C gamma a τ f w" := by
  intro M hM
  rcases h_T008 M hM with ⟨A,hA,hAl⟩
  rcases @yui_aux_0083 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 M hM with ⟨D,hD,hDl⟩
  rcases @yui_aux_0098 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 A M hA.le with ⟨Kyy,hKyy,hyy⟩
  rcases @yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 A M hA.le hM with ⟨Kyz,hKyz,hyz⟩
  let C := Kyz+Kyy+A+D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro a τ f w hd
  have hl := hAl a τ f w hd
  have hτ : 0 < τ := hd.2.2.1
  have hq0 : 0 ≤ KdVPlan.localQ gamma τ f w :=
    add_nonneg (Real.rpow_nonneg hτ.le _) (Real.sqrt_nonneg _)
  have hτq : 0 ≤ τ*KdVPlan.localQ gamma τ f w := mul_nonneg hτ.le hq0
  have hdiff := @yui_aux_0080 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a τ f hτ hd.2.2.2.2.1 hd.2.2.2.2.2.2.1
  have hder := hDl a τ f w hd
  refine ⟨hdiff,?_,hder.1,?_⟩
  · intro t ht
    have h1 := hyz a τ f w hd hl t ht
    have h2 := hyy a τ f w hd hl t ht
    rcases hl with ⟨hfn,hq,hF,hFd,hFag,hzX,hzN,hBFF,hQW,hinvB,hYd,hinvY,hYdae,hCst,hY,hYX,hYN,hYneg⟩
    have hW := hQW t ht
    have hWb : KdVPlan.HB 0 (KdVPlan.Wst a τ f) (A*τ*KdVPlan.localQ gamma τ f w) :=
      ⟨hW.2.1,by linarith only [hW.2.2,(@yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (KdVPlan.Qst a f t)).1]⟩
    have hc : ‖((((t-a)/τ : ℝ) : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sub_nonneg.mpr ht.1) hτ.le)]
      apply (div_le_one hτ).mpr
      linarith only [ht.2]
    have hs := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).2.1
    have haff := hs 0 _ ((((t-a)/τ : ℝ) : ℂ)) _ hWb
    have haff' : KdVPlan.HB 0 (KdVPlan.scale ((((t-a)/τ : ℝ) : ℂ)) (KdVPlan.Wst a τ f)) (A*τ*KdVPlan.localQ gamma τ f w) := by
      refine ⟨haff.1,haff.2.trans ?_⟩
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (one_mul _)
    have hneg : KdVPlan.HB 0 (-KdVPlan.timeInt a t (fun s => KdVPlan.B s (KdVPlan.Yst a τ f s) (KdVPlan.z a f s))) (Kyz*τ*KdVPlan.localQ gamma τ f w) := by
      have hb := hs 0 _ (-1) _ h1
      have he : KdVPlan.scale (-1) (KdVPlan.timeInt a t (fun s => KdVPlan.B s (KdVPlan.Yst a τ f s) (KdVPlan.z a f s))) = -KdVPlan.timeInt a t (fun s => KdVPlan.B s (KdVPlan.Yst a τ f s) (KdVPlan.z a f s)) := by ext k; simp [KdVPlan.scale]
      rw [he] at hb
      simpa only [norm_neg,norm_one,one_mul] using hb
    have hh := hs 0 _ (1/2) _ h2
    have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hhalf] at hh
    have hadd := (@yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013).1
    have hb := (hadd 0 _ _ _ _ ((hadd 0 _ _ _ _ hneg hh).2) haff').2
    change KdVPlan.HB 0 (_ - _ - _) _
    refine ⟨hb.1,hb.2.trans ?_⟩
    dsimp [C]
    have hnon : 0 ≤ Kyy*τ*KdVPlan.localQ gamma τ f w := by positivity
    have hDnon : 0 ≤ D*τ*KdVPlan.localQ gamma τ f w := by positivity
    nlinarith only [hnon,hDnon]
  · exact hder.2.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hq0)

theorem yui_aux_0105 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (p : Finset ℝ) (a b : ℝ) (f d : ℝ → ℂ), a ≤ b → ContinuousOn f (Set.Icc a b) →\n(∀ x ∈ Set.Ioo a b, x ∉ p → HasDerivAt f (d x) x) →\nIntervalIntegrable d volume a b → (∫ x in a..b, d x) = f b-f a" := by
  classical
  intro p
  induction p using Finset.induction_on with
  | empty =>
    intro a b f d hab hc hd hi
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc (fun x hx => hd x hx (by simp)) hi
  | @insert c p hcp ih =>
    intro a b f d hab hc hd hi
    by_cases hci : c ∈ Set.Ioo a b
    · have hil : IntervalIntegrable d volume a c :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hci.1.le).mpr
          (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi).mono_set (Set.Icc_subset_Icc le_rfl hci.2.le))
      have hir : IntervalIntegrable d volume c b :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hci.2.le).mpr
          (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi).mono_set (Set.Icc_subset_Icc hci.1.le le_rfl))
      have hl := ih a c f d hci.1.le (hc.mono (Set.Icc_subset_Icc le_rfl hci.2.le))
        (by
          intro x hx hxp
          apply hd x ⟨hx.1,hx.2.trans hci.2⟩
          simp only [Finset.mem_insert,not_or]
          exact ⟨ne_of_lt hx.2,hxp⟩) hil
      have hr := ih c b f d hci.2.le (hc.mono (Set.Icc_subset_Icc hci.1.le le_rfl))
        (by
          intro x hx hxp
          apply hd x ⟨hci.1.trans hx.1,hx.2⟩
          simp only [Finset.mem_insert,not_or]
          exact ⟨ne_of_gt hx.1,hxp⟩) hir
      rw [← intervalIntegral.integral_add_adjacent_intervals hil hir,hl,hr]
      ring
    · apply ih a b f d hab hc _ hi
      intro x hx hxp
      apply hd x hx
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun h => hci (h ▸ hx),hxp⟩

theorem yui_aux_0106 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (u d : KdVPlan.Path), a ≤ b →\n(∀ k, ContinuousOn (fun t => u t k) (Set.Icc a b)) →\n(∃ p : Finset ℝ, ∀ t ∈ Set.Ioo a b, t ∉ p → ∀ k, HasDerivAt (fun r => u r k) (d t k) t) →\n(∀ k, IntegrableOn (fun t => d t k) (Set.Icc a b)) → KdVPlan.Weak a b u d" := by
  intro a b u d hab hc hd hi
  refine ⟨fun k => ⟨(hc k).integrableOn_Icc,hi k⟩,?_⟩
  intro φ hφ hφc hφs k
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simpa using @yui_aux_0023 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 1
  have hφ1 := hφ.of_le h1
  have hφd := hφ1.differentiable_one
  have hφcont : Continuous (fun t => (φ t : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hφder : Continuous (fun t => ((deriv φ t : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hφ1.continuous_deriv_one
  have hid : IntervalIntegrable (fun t => d t k) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hi k)
  have hidφ := hid.mul_continuousOn hφcont.continuousOn
  have hiuφ : IntervalIntegrable (fun t => u t k*((deriv φ t : ℝ) : ℂ)) volume a b := ((hc k).mul hφder.continuousOn).intervalIntegrable_of_Icc hab
  rcases hd with ⟨p,hp⟩
  have hFTC := @yui_aux_0105 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 p a b (fun t => u t k*(φ t : ℂ)) (fun t => d t k*(φ t : ℂ)+u t k*((deriv φ t : ℝ) : ℂ)) hab
    ((hc k).mul hφcont.continuousOn)
    (fun t ht htp => (hp t ht htp k).mul (hφd t).hasDerivAt.ofReal_comp)
    (hidφ.add hiuφ)
  have hφa : φ a=0 := Function.notMem_support.mp (fun h => (lt_irrefl a) (hφs h).1)
  have hφb : φ b=0 := Function.notMem_support.mp (fun h => (lt_irrefl b) (hφs h).2)
  rw [intervalIntegral.integral_add hidφ hiuφ,hφa,hφb] at hFTC
  simp only [Complex.ofReal_zero,mul_zero,sub_zero] at hFTC
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hFTC)

theorem yui_aux_0107 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (u : KdVPlan.Path), KdVPlan.Piecewise a b u → ∃ p : Finset ℝ, ∀ t ∈ Set.Ioo a b, t ∉ p → ∀ k, HasDerivAt (fun r => u r k) (KdVPlan.dt u t k) t" := by
  classical
  intro a b u hu
  rcases hu.2 with ⟨p,hp⟩
  refine ⟨p,?_⟩
  intro t ht htp k
  have hopen : IsOpen (Set.Ioo a b \ (p : Set ℝ)) := isOpen_Ioo.sdiff p.finite_toSet.isClosed
  have hnh : Set.Ioo a b \ (p : Set ℝ) ∈ nhds t := hopen.mem_nhds ⟨ht,htp⟩
  rcases exists_Icc_mem_subset_of_mem_nhds hnh with ⟨l,r,htri,hnhlr,hlrsub⟩
  have hti : t ∈ Set.Ioo l r := Icc_mem_nhds_iff.mp hnhlr
  have hlr : l < r := hti.1.trans hti.2
  have hal : a ≤ l := (hlrsub ⟨le_rfl,hlr.le⟩).1.1.le
  have hrb : r ≤ b := (hlrsub ⟨hlr.le,le_rfl⟩).1.2.le
  have hs := hp l r hal hlr hrb (by
    intro x hx hxi
    exact (hlrsub ⟨hxi.1.le,hxi.2.le⟩).2 hx)
  have hn0 : (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by simp
  have hdiff := ((hs.1 k).differentiableOn hn0 t htri).differentiableAt hnhlr
  exact hdiff.hasDerivAt

theorem yui_aux_0108 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path), KdVPlan.EssBound s a b u →\n∀ᵐ t ∂(volume.restrict (Set.Icc a b)), KdVPlan.HB s (u t) (KdVPlan.EssH s a b u)" := by
  intro s a b u hu
  filter_upwards [hu.2.1,ENNReal.ae_le_essSup (μ := volume.restrict (Set.Icc a b)) (fun t => ENNReal.ofReal (KdVPlan.hn s (u t)))] with t ht hle
  refine ⟨ht,?_⟩
  have hreal := ENNReal.toReal_mono (ne_of_lt hu.2.2) hle
  rw [ENNReal.toReal_ofReal (show 0 ≤ KdVPlan.hn s (u t) from Real.sqrt_nonneg _)] at hreal
  exact hreal

theorem yui_aux_0109 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path), a ≤ b → KdVPlan.Piecewise a b u → KdVPlan.EssBound s a b (KdVPlan.dt u) → KdVPlan.Weak a b u (KdVPlan.dt u)" := by
  intro s a b u hab hu hd
  have hi := @yui_aux_0087 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b (KdVPlan.EssH s a b (KdVPlan.dt u)) _ hab hd.1 (@yui_aux_0108 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 s a b (KdVPlan.dt u) hd)
  exact @yui_aux_0106 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b u (KdVPlan.dt u) hab
    (@yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 a b u (by simpa using hu.1 0))
    (@yui_aux_0107 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 a b u hu)
    (fun k => (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (hi k))

theorem yui_aux_0110 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ τ : ℝ, 0 < τ →\n(∀ t : ℝ, 0 ≤ t → (KdVPlan.gridIndex τ t : ℝ)*τ ≤ t ∧ t < ((KdVPlan.gridIndex τ t : ℝ)+1)*τ) ∧\n(∀ n : ℕ, KdVPlan.gridIndex τ ((n : ℝ)*τ)=n) ∧\n(∀ (n : ℕ) (t : ℝ), t ∈ Set.Ico ((n : ℝ)*τ) (((n : ℝ)+1)*τ) → KdVPlan.gridIndex τ t=n) ∧\n(∀ (L : ℕ) (t : ℝ), t ∈ Set.Icc 0 ((L : ℝ)*τ) → KdVPlan.gridIndex τ t ≤ L)" := by
  intro τ hτ
  have h0 : ∀ n : ℕ, KdVPlan.gridIndex τ ((n : ℝ)*τ)=n := by
    intro n
    simp [KdVPlan.gridIndex,hτ.ne']
  refine ⟨?_,h0,?_,?_⟩
  · intro t ht
    have hlo := Nat.floor_le (div_nonneg ht hτ.le)
    have hhi := Nat.lt_floor_add_one (t/τ)
    exact ⟨(le_div_iff₀ hτ).mp hlo,(div_lt_iff₀ hτ).mp hhi⟩
  · intro n t ht
    unfold KdVPlan.gridIndex
    apply Nat.floor_eq_on_Ico n
    exact ⟨(le_div_iff₀ hτ).mpr ht.1,(div_lt_iff₀ hτ).mpr ht.2⟩
  · intro L t ht
    have hm := Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hτ.le)
    simpa [KdVPlan.gridIndex,hτ.ne'] using hm

theorem yui_aux_0111 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f → ∀ n : ℕ, KdVPlan.Data 0 (KdVPlan.twistedNum τ f n) ∧ KdVPlan.Smooth (KdVPlan.twistedNum τ f n)" := by
  intro τ f hτ hf hs
  have hn : ∀ n : ℕ, KdVPlan.Data 0 (KdVPlan.numerical τ f n) ∧ KdVPlan.Smooth (KdVPlan.numerical τ f n) := by
    intro n
    induction n with
    | zero => exact ⟨hf,hs⟩
    | succ n ih =>
      have hh := (h_T007.1 τ hτ).2.2.1 _ ih.1
      simpa only [KdVPlan.numerical,Function.iterate_succ_apply'] using ⟨hh.1,hh.2 ih.2⟩
  intro n
  have hh := @yui_aux_0044 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 (-((n : ℝ))*τ) (KdVPlan.numerical τ f n) (hn n).1
  exact ⟨hh.1,hh.2 (hn n).2⟩

theorem yui_aux_0112 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (n : ℕ) (t : ℝ), 0 < τ → t ∈ Set.Ioo ((n : ℝ)*τ) (((n : ℝ)+1)*τ) → ∀ᶠ r in nhds t, KdVPlan.gridIndex τ r=n" := by
  intro τ n t hτ ht
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact (@yui_aux_0110 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ hτ).2.2.1 n r ⟨hr.1.le,hr.2⟩

theorem yui_aux_0113 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f →\n∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioo ((n : ℝ)*τ) (((n : ℝ)+1)*τ) →\nKdVPlan.dt (KdVPlan.residual τ f) t = KdVPlan.dt (KdVPlan.rho ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t ∧\n∀ k, HasDerivAt (fun r => KdVPlan.interp τ f r k) ((KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.interp τ f t) (KdVPlan.interp τ f t))+KdVPlan.dt (KdVPlan.residual τ f) t) k) t" := by
  intro τ f hτ hf hs n t ht
  have hcell : t ∈ Set.Ioo ((n : ℝ)*τ) ((n : ℝ)*τ+τ) := by constructor <;> nlinarith only [ht.1,ht.2]
  have hnum := @yui_aux_0111 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ f hτ hf hs n
  have hd := @yui_aux_0078 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n) hτ hnum.1 hnum.2 t hcell
  have he := @yui_aux_0112 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ n t hτ ht
  have hflo := (@yui_aux_0110 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ hτ).2.2.1 n t ⟨ht.1.le,ht.2⟩
  have hR : KdVPlan.dt (KdVPlan.residual τ f) t = KdVPlan.dt (KdVPlan.rho ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t := by
    ext k
    have hρ := (hd k).2.differentiableAt.hasDerivAt
    have h := (hasDerivAt_const t ((∑ j ∈ Finset.range n, KdVPlan.rho ((j : ℝ)*τ) τ (KdVPlan.twistedNum τ f j) (((j : ℝ)+1)*τ)) k)).add hρ
    have h' : HasDerivAt (fun r => KdVPlan.residual τ f r k) (KdVPlan.dt (KdVPlan.rho ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t k) t := by
      simp only [zero_add] at h
      apply h.congr_of_eventuallyEq
      filter_upwards [he] with r hr
      simp only [KdVPlan.residual,hr,Pi.add_apply]
    exact h'.deriv
  refine ⟨hR,?_⟩
  intro k
  have hV := (hd k).1.differentiableAt.hasDerivAt
  have hvrel := (@yui_aux_0080 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n) hτ hnum.1 hnum.2 t hcell).1
  change HasDerivAt (fun r => KdVPlan.Vst ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n) r k) (KdVPlan.dt (KdVPlan.Vst ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t k) t at hV
  rw [hvrel] at hV
  have hV' : HasDerivAt (fun r => KdVPlan.interp τ f r k) ((KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.Vst ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n) t) (KdVPlan.Vst ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n) t))+KdVPlan.dt (KdVPlan.rho ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t) k) t := by
    apply hV.congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [KdVPlan.interp,hr]
  simpa only [KdVPlan.interp,hflo,hR] using hV'

theorem yui_aux_0114 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (L : ℕ), 0 < τ → ∃ p : Finset ℝ, ∀ t ∈ Set.Icc 0 ((L : ℝ)*τ), t ∉ p →\nKdVPlan.gridIndex τ t < L ∧ t ∈ Set.Ioo ((KdVPlan.gridIndex τ t : ℝ)*τ) (((KdVPlan.gridIndex τ t : ℝ)+1)*τ)" := by
  classical
  intro τ L hτ
  let p := (Finset.range (L+1)).image (fun n : ℕ => (n : ℝ)*τ)
  refine ⟨p,?_⟩
  intro t ht htp
  have hidx := (@yui_aux_0110 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ hτ).2.2.2 L t ht
  have hb := (@yui_aux_0110 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ hτ).1 t ht.1
  have hne : (KdVPlan.gridIndex τ t : ℝ)*τ ≠ t := by
    intro he
    apply htp
    exact Finset.mem_image.mpr ⟨KdVPlan.gridIndex τ t,Finset.mem_range.mpr (by omega),he⟩
  have hlo : (KdVPlan.gridIndex τ t : ℝ)*τ < t := lt_of_le_of_ne hb.1 hne
  refine ⟨?_,hlo,hb.2⟩
  by_contra hn
  have he : KdVPlan.gridIndex τ t=L := by omega
  rw [he] at hlo
  linarith only [hlo,ht.2]

theorem yui_aux_0115 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (L : ℕ) (d : ℝ → ℂ) (D : ℕ → ℝ → ℂ), 0 < τ →\nAEStronglyMeasurable d (volume.restrict (Set.Icc 0 ((L : ℝ)*τ))) →\n(∀ n, ContinuousOn (D n) (Set.Icc ((n : ℝ)*τ) (((n : ℝ)+1)*τ))) →\n(∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioo ((n : ℝ)*τ) (((n : ℝ)+1)*τ) → d t = D n t) →\nIntegrableOn d (Set.Icc 0 ((L : ℝ)*τ))" := by
  classical
  intro τ L d D hτ hd hD he
  have hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc ((n : ℝ)*τ) (((n : ℝ)+1)*τ), ‖D n t‖ ≤ C := by
    intro n
    rcases isCompact_Icc.exists_bound_of_continuousOn (hD n) with ⟨C,hC⟩
    exact ⟨max 0 C,le_max_left _ _,fun t ht => (hC t ht).trans (le_max_right _ _)⟩
  choose C hC0 hC using hb
  rcases @yui_aux_0114 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ L hτ with ⟨p,hp⟩
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hd (∑ n ∈ Finset.range L, C n)
  have hpn : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 ((L : ℝ)*τ))), t ∉ (p : Set ℝ) :=
    ae_mono Measure.restrict_le_self (p.finite_toSet.countable.ae_notMem volume)
  filter_upwards [hpn,ae_restrict_mem measurableSet_Icc] with t htp ht
  have hcell := hp t ht htp
  rw [he _ _ hcell.2]
  exact (hC _ t ⟨hcell.2.1.le,hcell.2.2.le⟩).trans
    (Finset.single_le_sum (fun n _ => hC0 n) (Finset.mem_range.mpr hcell.1))

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T007 : KdVPlan.SchemeOutput) (h_T008 : KdVPlan.StageOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f → KdVPlan.Smooth f →\n∃ D : ℕ → KdVPlan.Path,\n(∀ (n : ℕ) (k : ℤ), ContinuousOn (fun t => D n t k) (Set.Icc ((n : ℝ)*τ) (((n : ℝ)+1)*τ))) ∧\n∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioo ((n : ℝ)*τ) (((n : ℝ)+1)*τ) →\nKdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.interp τ f t) (KdVPlan.interp τ f t))+KdVPlan.dt (KdVPlan.residual τ f) t = D n t" := by
  intro τ f hτ hf hs
  let D : ℕ → KdVPlan.Path := fun n t =>
   KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.twistedNum τ f n) (KdVPlan.twistedNum τ f n))+
   KdVPlan.B t (KdVPlan.twistedNum τ f n) (KdVPlan.F ((n : ℝ)*τ) (KdVPlan.twistedNum τ f n) t)+
   KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.F ((n : ℝ)*τ) (KdVPlan.twistedNum τ f n) t) (KdVPlan.F ((n : ℝ)*τ) (KdVPlan.twistedNum τ f n) t))-
   KdVPlan.scale ((τ : ℂ)⁻¹) (KdVPlan.Wst ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n))
  refine ⟨D,?_,?_⟩
  · intro n k
    have hn := @yui_aux_0111 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ f hτ hf hs n
    have hF : KdVPlan.ContH 0 ((n : ℝ)*τ) (((n : ℝ)+1)*τ) (KdVPlan.F ((n : ℝ)*τ) (KdVPlan.twistedNum τ f n)) := by
      have h := (@yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 ((n : ℝ)*τ) τ _ hτ hn.1 hn.2).1 0
      convert h using 1 <;> push_cast <;> ring
    have hc := @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 0 ((n : ℝ)*τ) (((n : ℝ)+1)*τ) (KdVPlan.twistedNum τ f n) hn.1.1
    have h1 := @yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ _ _ _ hc hc k
    have h2 := @yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ _ _ _ hc hF k
    have h3 := @yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 _ _ _ _ hF hF k
    exact (((h1.const_mul (1/2)).add h2).add (h3.const_mul (1/2))).sub continuousOn_const
  · intro n t ht
    have hn := @yui_aux_0111 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ f hτ hf hs n
    have hcell : t ∈ Set.Ioo ((n : ℝ)*τ) ((n : ℝ)*τ+τ) := by constructor <;> nlinarith only [ht.1,ht.2]
    have hd := @yui_aux_0078 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 ((n : ℝ)*τ) τ _ hτ hn.1 hn.2 t hcell
    have hR := (@yui_aux_0113 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ f hτ hf hs n t ht).1
    have hV := (@yui_aux_0080 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 ((n : ℝ)*τ) τ _ hτ hn.1 hn.2 t hcell).1
    have hflo := (@yui_aux_0110 T gamma R h_H002 h_T005 h_T006 h_T007 h_T008 h_T013 τ hτ).2.2.1 n t ⟨ht.1.le,ht.2⟩
    rw [hR]
    have hipt : KdVPlan.interp τ f t = KdVPlan.Vst ((n : ℝ)*τ) τ (KdVPlan.twistedNum τ f n) t := by simp only [KdVPlan.interp,hflo]
    rw [hipt,← hV]
    ext k
    exact (hd k).1.deriv
#check @checked
#print axioms checked
end YuiAuxiliary
