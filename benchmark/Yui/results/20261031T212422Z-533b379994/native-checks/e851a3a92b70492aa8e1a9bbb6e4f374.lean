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
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ w u v : ℝ, 0 < w → w*u ≤ w*v → u ≤ v" := by
  intro w u v hw h
  exact (mul_le_mul_iff_right₀ hw).mp h

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ w m u : ℝ, 0 < w → 0 < m → u*m ≤ 3*w → 1/w*u ≤ 3/m" := by
  intro w m u hw hm h
  calc
    1/w*u = u/w := by ring
    _ ≤ 3/m := (div_le_div_iff₀ hw hm).2 h

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ x y z w : ℝ, 0 < x → 0 < y → 0 < z → 0 < w → x ≤ y+z+w → y ≤ x+z+w → z ≤ x+y+w → w ≤ x+y+z → let m := min (max x y) (min (max x z) (min (max x w) (min (max y z) (min (max y w) (max z w))))) ; (1/w)*min (x*y/(z*w)) (z*w/(x*y)) ≤ 3/m" := by
  intro x y z w hx hy hz hw hx' hy' hz' hw'
  dsimp only
  have hxy : 0 < x*y := mul_pos hx hy
  have hzw : 0 < z*w := mul_pos hz hw
  have hmin := min_le_left (x*y/(z*w)) (z*w/(x*y))
  have hmin' := min_le_right (x*y/(z*w)) (z*w/(x*y))
  have hone : min (x*y/(z*w)) (z*w/(x*y)) ≤ 1 := by
    by_cases h : x*y ≤ z*w
    · exact hmin.trans ((div_le_one hzw).2 h)
    · exact hmin'.trans ((div_le_one hxy).2 (le_of_not_ge h))
  have hm1 := (le_div_iff₀ hzw).mp hmin
  have hm2 := (le_div_iff₀ hxy).mp hmin'
  have hnonneg : 0 ≤ min (x*y/(z*w)) (z*w/(x*y)) := le_min (by positivity) (by positivity)
  apply @yui_aux_0002 T gamma R w _ _ hw (by positivity)
  rcases le_total x y with hxyO | hyxO <;>
  rcases le_total x z with hxzO | hzxO <;>
  rcases le_total x w with hxwO | hwxO <;>
  rcases le_total y z with hyzO | hzyO <;>
  rcases le_total y w with hywO | hwyO <;>
  rcases le_total z w with hzwO | hwzO
  all_goals
    simp_all only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, min_self, max_self]
  all_goals try nlinarith

  all_goals
    have hprod : z*z ≤ x*y := mul_le_mul hzxO hzyO hz.le hx.le
    have hmul := mul_le_mul_of_nonneg_left hprod hnonneg
    nlinarith

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ x y z w t : ℝ, 0 < x → 0 < y → 0 < z → 0 < w →\nx ≤ y+z+w → y ≤ x+z+w → z ≤ x+y+w → w ≤ x+y+z →\nt ≤ x+y → t ≤ z+w →\nlet m := min (max x y) (min (max x z) (min (max x w) (min (max y z) (min (max y w) (max z w)))));\nmax (max x y) (max z w) ≤ 3 * max (min x y) (max (min x z) (max (min x w) (max (min y z) (max (min y w) (min z w))))) ∧\nt / max (x*y) (z*w) ≤ 6/m" := by
  intro x y z w t hx hy hz hw hx' hy' hz' hw' ht ht'
  dsimp only
  have hm : 0 < min (max x y) (min (max x z) (min (max x w) (min (max y z) (min (max y w) (max z w))))) := by positivity
  have hmax : 0 < max (x*y) (z*w) := lt_max_of_lt_left (mul_pos hx hy)
  have h1 : x*y ≤ max (x*y) (z*w) := le_max_left _ _
  have h2 : z*w ≤ max (x*y) (z*w) := le_max_right _ _
  constructor
  · rcases le_total x y with hxyO | hyxO <;>
    rcases le_total x z with hxzO | hzxO <;>
    rcases le_total x w with hxwO | hwxO <;>
    rcases le_total y z with hyzO | hzyO <;>
    rcases le_total y w with hywO | hwyO <;>
    rcases le_total z w with hzwO | hwzO <;>
    simp_all only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, min_self, max_self] <;> linarith
  · apply (div_le_div_iff₀ hmax hm).2
    rcases le_total x y with hxyO | hyxO <;>
    rcases le_total x z with hxzO | hzxO <;>
    rcases le_total x w with hxwO | hwxO <;>
    rcases le_total y z with hyzO | hzyO <;>
    rcases le_total y w with hywO | hwyO <;>
    rcases le_total z w with hzwO | hwzO
    all_goals
      simp_all only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, min_self, max_self]
    all_goals nlinarith

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ x y : ℝ, |x+y| ≤ |x|+|y|" := by
  intro x y
  exact abs_add_le x y

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (x y z : ℝ), x ≤ y → x+z ≤ y+z" := by
  intro x y z h
  exact add_le_add h le_rfl

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ a b c d : ℤ, KdVPlan.Interaction a b c d → KdVPlan.n1 a b c d ≤ 3*KdVPlan.n2 a b c d ∧ (1/|(d : ℝ)|)*min (|(a : ℝ)*(b : ℝ)|/|(c : ℝ)*(d : ℝ)|) (|(c : ℝ)*(d : ℝ)|/|(a : ℝ)*(b : ℝ)|) ≤ 3/KdVPlan.n3 a b c d ∧ |(a : ℝ)+(b : ℝ)| / max |(a : ℝ)*(b : ℝ)| |(c : ℝ)*(d : ℝ)| ≤ 6/KdVPlan.n3 a b c d" := by
  intro a b c d h
  rcases h with ⟨hs, ha, hb, hc, hd⟩
  have hs' : (a : ℝ)+(b : ℝ)+(c : ℝ)+(d : ℝ)=0 := by exact_mod_cast hs
  have hp : ∀ k : ℤ, k ≠ 0 → 0 < |(k : ℝ)| := by
    intro k hk
    exact abs_pos.mpr (by exact_mod_cast hk)
  have hsum : ∀ x y z w : ℝ, x+y+z+w=0 → |x| ≤ |y|+|z|+|w| := by
    intro x y z w he
    have he' : x = -(y+z+w) := by linarith
    rw [he', abs_neg]
    exact ((@yui_aux_0005 T gamma R) (y+z) w).trans (@yui_aux_0006 T gamma R _ _ _ ((@yui_aux_0005 T gamma R) y z))
  have h1 := hsum a b c d hs'
  have h2 := hsum b a c d (by linarith)
  have h3 := hsum c a b d (by linarith)
  have h4 := hsum d a b c (by linarith)
  have hab : |(a : ℝ)+(b : ℝ)| ≤ |(c : ℝ)|+|(d : ℝ)| := by
    have he : (a : ℝ)+(b : ℝ) = -((c : ℝ)+(d : ℝ)) := by linarith
    rw [he, abs_neg]
    exact (@yui_aux_0005 T gamma R) _ _
  have hfirst := @yui_aux_0003 T gamma R |(a : ℝ)| |(b : ℝ)| |(c : ℝ)| |(d : ℝ)| (hp a ha) (hp b hb) (hp c hc) (hp d hd) h1 h2 h3 h4
  have hrest := @yui_aux_0004 T gamma R |(a : ℝ)| |(b : ℝ)| |(c : ℝ)| |(d : ℝ)| |(a : ℝ)+(b : ℝ)| (hp a ha) (hp b hb) (hp c hc) (hp d hd) h1 h2 h3 h4 ((@yui_aux_0005 T gamma R) _ _) hab
  exact ⟨hrest.1, by simpa only [KdVPlan.n3, abs_mul] using hfirst, by simpa only [KdVPlan.n3, abs_mul] using hrest.2⟩

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ {ι κ : Type} (s : Finset ι) (t : Finset κ) (K : ι → κ → ℝ) (u : ι → ℝ) (v : κ → ℝ) (C : ℝ),\n0 ≤ C → (∀ i ∈ s, ∀ j ∈ t, 0 ≤ K i j) →\n(∀ i ∈ s, ∑ j ∈ t, K i j ≤ C) →\n(∀ j ∈ t, ∑ i ∈ s, K i j ≤ C) →\n(∑ i ∈ s, ∑ j ∈ t, K i j * u i * v j) ≤\nC * Real.sqrt (∑ i ∈ s, (u i)^2) * Real.sqrt (∑ j ∈ t, (v j)^2)" := by
  intro ι κ s t K u v C hC hK hrow hcol
  classical
  have hsq : ∀ i ∈ s, ∀ j ∈ t, (Real.sqrt (K i j))^2 = K i j := by
    intro i hi j hj
    exact Real.sq_sqrt (hK i hi j hj)
  have ha : (∑ z ∈ s ×ˢ t, (Real.sqrt (K z.1 z.2) * u z.1)^2) ≤ C * ∑ i ∈ s, (u i)^2 := by
    rw [Finset.sum_product]
    calc
      _ = ∑ i ∈ s, (∑ j ∈ t, K i j) * (u i)^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_pow, hsq i hi j hj]
      _ ≤ ∑ i ∈ s, C * (u i)^2 := Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hb : (∑ z ∈ s ×ˢ t, (Real.sqrt (K z.1 z.2) * v z.2)^2) ≤ C * ∑ j ∈ t, (v j)^2 := by
    rw [Finset.sum_product, Finset.sum_comm]
    calc
      _ = ∑ j ∈ t, (∑ i ∈ s, K i j) * (v j)^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow, hsq i hi j hj]
      _ ≤ ∑ j ∈ t, C * (v j)^2 := Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (s ×ˢ t) (fun z => Real.sqrt (K z.1 z.2)*u z.1) (fun z => Real.sqrt (K z.1 z.2)*v z.2)
  have heq : (∑ z ∈ s ×ˢ t, (Real.sqrt (K z.1 z.2) * u z.1) * (Real.sqrt (K z.1 z.2) * v z.2)) =
      ∑ i ∈ s, ∑ j ∈ t, K i j * u i * v j := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    calc
      _ = (Real.sqrt (K i j))^2 * u i * v j := by ring
      _ = _ := by rw [hsq i hi j hj]
  rw [heq] at hcs
  calc
    _ ≤ Real.sqrt (∑ z ∈ s ×ˢ t, (Real.sqrt (K z.1 z.2) * u z.1)^2) *
        Real.sqrt (∑ z ∈ s ×ˢ t, (Real.sqrt (K z.1 z.2) * v z.2)^2) := hcs
    _ ≤ Real.sqrt (C * ∑ i ∈ s, (u i)^2) * Real.sqrt (C * ∑ j ∈ t, (v j)^2) :=
      mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hC, Real.sqrt_mul hC]
      calc
        _ = (Real.sqrt C)^2 * Real.sqrt (∑ i ∈ s, (u i)^2) * Real.sqrt (∑ j ∈ t, (v j)^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hC]

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (s t : Finset ℕ) (ρ : ℝ) (u v : ℕ → ℝ), 0 ≤ ρ → ρ < 1 →\n(∑ i ∈ s, ∑ j ∈ t, (if j ≤ i then ρ^(i-j) else 0) * u i * v j) ≤\n(1-ρ)⁻¹ * Real.sqrt (∑ i ∈ s, (u i)^2) * Real.sqrt (∑ j ∈ t, (v j)^2)" := by
  intro s t ρ u v hρ hρ'
  classical
  have hg : Summable (fun n : ℕ => ρ^n) := summable_geometric_of_lt_one hρ hρ'
  have hgeom : ∑' n : ℕ, ρ^n = (1-ρ)⁻¹ := tsum_geometric_of_lt_one hρ hρ'
  apply @yui_aux_0008 T gamma R ℕ ℕ s t (fun i j => if j ≤ i then ρ^(i-j) else 0) u v ((1-ρ)⁻¹) (by positivity)
  · intro i hi j hj
    split_ifs <;> positivity
  · intro i hi
    rw [← Finset.sum_filter]
    calc
      _ = ∑ r ∈ (t.filter (fun j => j ≤ i)).image (fun j => i-j), ρ^r := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        dsimp only at hab ha' hb'
        omega
      _ ≤ ∑' n : ℕ, ρ^n := hg.sum_le_tsum _ (fun _ _ => by positivity)
      _ = _ := hgeom
  · intro j hj
    rw [← Finset.sum_filter]
    calc
      _ = ∑ r ∈ (s.filter (fun i => j ≤ i)).image (fun i => i-j), ρ^r := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        dsimp only at hab ha' hb'
        omega
      _ ≤ ∑' n : ℕ, ρ^n := hg.sum_le_tsum _ (fun _ _ => by positivity)
      _ = _ := hgeom

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (s t : Finset ℕ) (u v : ℕ → ℝ),\n(∑ i ∈ s, ∑ j ∈ t, (if j ≤ i ∧ i ≤ j+2 then (1:ℝ) else 0) * u i * v j) ≤\n3 * Real.sqrt (∑ i ∈ s, (u i)^2) * Real.sqrt (∑ j ∈ t, (v j)^2)" := by
  intro s t u v
  classical
  have hsingle : ∀ (s : Finset ℕ) (i q : ℕ), (∑ j ∈ s, if i = j+q then (1:ℝ) else 0) ≤ 1 := by
    intro s i q
    by_cases h : q ≤ i
    · have he : ∀ j, i = j+q ↔ j=i-q := by intro j; omega
      simp_rw [he]
      simp only [Finset.sum_ite_eq', Finset.sum_const_zero]
      split_ifs <;> norm_num
    · have he : ∀ j, i ≠ j+q := by intro j; omega
      simp [he]
  have hsingle' : ∀ (s : Finset ℕ) (j q : ℕ), (∑ i ∈ s, if i = j+q then (1:ℝ) else 0) ≤ 1 := by
    intro s j q
    simp only [Finset.sum_ite_eq', Finset.sum_const_zero]
    split_ifs <;> norm_num
  have he : ∀ i j : ℕ, (if j ≤ i ∧ i ≤ j+2 then (1:ℝ) else 0) =
      (if i=j then 1 else 0)+(if i=j+1 then 1 else 0)+(if i=j+2 then 1 else 0) := by
    intro i j
    split_ifs <;> first | omega | norm_num
  apply @yui_aux_0008 T gamma R ℕ ℕ s t _ u v 3 (by norm_num)
  · intro i hi j hj
    split_ifs <;> norm_num
  · intro i hi
    simp_rw [he, Finset.sum_add_distrib]
    have h0 := hsingle t i 0
    have h1 := hsingle t i 1
    have h2 := hsingle t i 2
    simp only [Nat.add_zero] at h0
    linarith
  · intro j hj
    simp_rw [he, Finset.sum_add_distrib]
    have h0 := hsingle' s j 0
    have h1 := hsingle' s j 1
    have h2 := hsingle' s j 2
    simp only [Nat.add_zero] at h0
    linarith

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ {α : Type} [Fintype α] (H : (Fin 4 → α) → ℝ),\n(∑ k : Fin 4 → α, H k) = ∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α, H ![a,b,c,d]" := by
  intro α inst H
  classical
  let e : (Fin 4 → α) ≃ (α × α × α × α) :=
    { toFun := fun k => (k 0, k 1, k 2, k 3)
      invFun := fun z => ![z.1,z.2.1,z.2.2.1,z.2.2.2]
      left_inv := by intro k; funext i; fin_cases i <;> rfl
      right_inv := by intro z; rfl }
  calc
    _ = ∑ z : α × α × α × α, H ![z.1,z.2.1,z.2.2.1,z.2.2.2] := by
      apply Fintype.sum_equiv e
      intro k
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = _ := by simp only [Fintype.sum_prod_type]

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (n : ℕ) (f : ℕ → ℝ), (∑ i ∈ Finset.range n, f i) = ∑ i : Fin n, f i" := by
  intro n f
  exact (Fin.sum_univ_eq_sum_range f n).symm

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (n : ℕ) (ρ : ℝ) (X : Fin 4 → ℕ → ℝ),\n0 ≤ ρ → ρ < 1 → (∀ i j, 0 ≤ X i j) →\n(∑ j : Fin 4 → Fin n,\n ((if (j 1 : ℕ) ≤ j 0 ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)+2 then (1:ℝ) else 0) *\n  (if (j 3 : ℕ) ≤ j 2 then ρ^((j 2 : ℕ)-(j 3 : ℕ)) else 0)) *\n ∏ i : Fin 4, X i (j i)) ≤\n(3/(1-ρ)) * ∏ i : Fin 4, Real.sqrt (∑ j : Fin n, (X i j)^2)" := by
  intro n ρ X hρ hρ' hX
  classical
  let L : ℝ := ∑ a : Fin n, ∑ b : Fin n, (if (b:ℕ) ≤ a ∧ (a:ℕ) ≤ (b:ℕ)+2 then (1:ℝ) else 0)*X 0 a*X 1 b
  let U : ℝ := ∑ c : Fin n, ∑ d : Fin n, (if (d:ℕ) ≤ c then ρ^((c:ℕ)-(d:ℕ)) else 0)*X 2 c*X 3 d
  have hL : L ≤ 3 * Real.sqrt (∑ a : Fin n, (X 0 a)^2) * Real.sqrt (∑ b : Fin n, (X 1 b)^2) := by
    dsimp [L]
    simpa only [@yui_aux_0012 T gamma R n] using @yui_aux_0010 T gamma R (Finset.range n) (Finset.range n) (X 0) (X 1)
  have hU : U ≤ (1-ρ)⁻¹ * Real.sqrt (∑ c : Fin n, (X 2 c)^2) * Real.sqrt (∑ d : Fin n, (X 3 d)^2) := by
    dsimp [U]
    simpa only [@yui_aux_0012 T gamma R n] using @yui_aux_0009 T gamma R (Finset.range n) (Finset.range n) ρ (X 2) (X 3) hρ hρ'
  have he : (∑ j : Fin 4 → Fin n,
   ((if (j 1 : ℕ) ≤ j 0 ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)+2 then (1:ℝ) else 0) *
    (if (j 3 : ℕ) ≤ j 2 then ρ^((j 2 : ℕ)-(j 3 : ℕ)) else 0)) *
   ∏ i : Fin 4, X i (j i)) = L*U := by
    rw [@yui_aux_0011 T gamma R (Fin n)]
    dsimp [L, U]
    simp [Fin.prod_univ_succ]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> ring
  rw [he]
  have hU0 : 0 ≤ U := by
    dsimp [U]
    apply Finset.sum_nonneg
    intro c hc
    apply Finset.sum_nonneg
    intro d hd
    have hc' := hX 2 c
    have hd' := hX 3 d
    split_ifs <;> positivity
  calc
    L*U ≤ (3 * Real.sqrt (∑ a : Fin n, (X 0 a)^2) * Real.sqrt (∑ b : Fin n, (X 1 b)^2)) *
      ((1-ρ)⁻¹ * Real.sqrt (∑ c : Fin n, (X 2 c)^2) * Real.sqrt (∑ d : Fin n, (X 3 d)^2)) :=
        mul_le_mul hL hU hU0 (by positivity)
    _ = _ := by simp [Fin.prod_univ_succ]; ring

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (p : Equiv.Perm (Fin 4)) (Y : Fin 4 → ℝ), (∏ i, Y (p i)) = ∏ i, Y i" := by
  intro p Y
  exact Equiv.prod_comp p Y

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (n : ℕ) (K H : (Fin 4 → Fin n) → ℝ) (X : Fin 4 → ℕ → ℝ) (D B : ℝ),\n(∀ j, 0 ≤ K j) → 0 ≤ D → (∀ i j, 0 ≤ X i j) →\n(∀ Y : Fin 4 → ℕ → ℝ, (∀ i j, 0 ≤ Y i j) →\n (∑ j : Fin 4 → Fin n, K j * ∏ i : Fin 4, Y i (j i)) ≤\n B * ∏ i : Fin 4, Real.sqrt (∑ j : Fin n, (Y i j)^2)) →\n(∀ j, ∃ p : Equiv.Perm (Fin 4), H j ≤ D * K (fun i => j (p i)) * ∏ i : Fin 4, X i (j i)) →\n(∑ j, H j) ≤ 24 * D * B * ∏ i : Fin 4, Real.sqrt (∑ j : Fin n, (X i j)^2)" := by
  intro n K H X D B hK hD hX hkernel hcover
  classical
  let P : ℝ := ∏ i : Fin 4, Real.sqrt (∑ j : Fin n, (X i j)^2)
  have hp : ∀ p : Equiv.Perm (Fin 4),
    (∑ j : Fin 4 → Fin n, K (fun i => j (p i)) * ∏ i : Fin 4, X i (j i)) ≤ B*P := by
    intro p
    let e : (Fin 4 → Fin n) ≃ (Fin 4 → Fin n) :=
      { toFun := fun j i => j (p i)
        invFun := fun j i => j (p.symm i)
        left_inv := by intro j; funext i; simp
        right_inv := by intro j; funext i; simp }
    have he : (∑ j : Fin 4 → Fin n, K (fun i => j (p i)) * ∏ i : Fin 4, X i (j i)) =
        ∑ j : Fin 4 → Fin n, K j * ∏ i : Fin 4, X (p i) (j i) := by
      apply Fintype.sum_equiv e
      intro j
      dsimp [e]
      rw [(@yui_aux_0014 T gamma R p) (fun i => X i (j i))]
    rw [he]
    have h := hkernel (fun i => X (p i)) (fun i j => hX (p i) j)
    simpa only [P, (@yui_aux_0014 T gamma R p) (fun i => Real.sqrt (∑ j : Fin n, (X i j)^2))] using h
  have hterm : ∀ j, H j ≤ ∑ p : Equiv.Perm (Fin 4), D * K (fun i => j (p i)) * ∏ i : Fin 4, X i (j i) := by
    intro j
    obtain ⟨p, hp'⟩ := hcover j
    apply hp'.trans
    apply Finset.single_le_sum _ (Finset.mem_univ p)
    intro p' hp'
    exact mul_nonneg (mul_nonneg hD (hK _)) (Finset.prod_nonneg fun i hi => hX _ _)
  calc
    (∑ j, H j) ≤ ∑ j : Fin 4 → Fin n, ∑ p : Equiv.Perm (Fin 4), D*K (fun i => j (p i))*∏ i : Fin 4, X i (j i) := Finset.sum_le_sum fun j hj => hterm j
    _ = ∑ p : Equiv.Perm (Fin 4), D * ∑ j : Fin 4 → Fin n, K (fun i => j (p i))*∏ i : Fin 4, X i (j i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ p : Equiv.Perm (Fin 4), D*(B*P) := Finset.sum_le_sum fun p hp' => mul_le_mul_of_nonneg_left (hp p) hD
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      norm_num [P, Nat.factorial]
      <;> ring

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ {α : Type} [Fintype α] (k : α → ℤ), Function.Injective k →\n∀ (u v : α → ℝ) (r : ℤ),\n(∑ a : α, ∑ b : α, if k a+k b=r then u a*v b else 0) ≤\nReal.sqrt (∑ a : α, (u a)^2) * Real.sqrt (∑ b : α, (v b)^2)" := by
  intro α inst k hk u v r
  classical
  have hone : ∀ r : ℤ, (∑ a : α, if k a=r then (1:ℝ) else 0) ≤ 1 := by
    intro r
    by_cases he : ∃ a, k a=r
    · obtain ⟨a₀, ha₀⟩ := he
      have hiff : ∀ a, k a=r ↔ a=a₀ := by
        intro a
        constructor
        · intro ha
          apply hk
          exact ha.trans ha₀.symm
        · rintro rfl
          exact ha₀
      simp [hiff]
    · have hne : ∀ a, k a ≠ r := by simpa only [not_exists] using he
      simp [hne]
  have h := @yui_aux_0008 T gamma R α α Finset.univ Finset.univ (fun a b => if k a+k b=r then (1:ℝ) else 0) u v 1 (by norm_num) (by intro a ha b hb; split_ifs <;> norm_num) ?_ ?_
  · simpa only [ite_mul, one_mul, zero_mul] using h
  · intro a ha
    have he : ∀ b, k a+k b=r ↔ k b=r-k a := by intro b; omega
    simpa only [he] using hone (r-k a)
  · intro b hb
    have he : ∀ a, k a+k b=r ↔ k a=r-k b := by intro a; omega
    simpa only [he] using hone (r-k b)

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (k : Fin 4 → ℤ) (r : ℝ),\nr ≤ KdVPlan.n3 (k 0) (k 1) (k 2) (k 3) ↔\n∀ i j : Fin 4, i ≠ j → r ≤ max |(k i : ℝ)| |(k j : ℝ)|" := by
  intro k r
  constructor
  · intro h i j hij
    rcases (show r ≤ max |(k 0 : ℝ)| |(k 1 : ℝ)| ∧
      r ≤ max |(k 0 : ℝ)| |(k 2 : ℝ)| ∧
      r ≤ max |(k 0 : ℝ)| |(k 3 : ℝ)| ∧
      r ≤ max |(k 1 : ℝ)| |(k 2 : ℝ)| ∧
      r ≤ max |(k 1 : ℝ)| |(k 3 : ℝ)| ∧
      r ≤ max |(k 2 : ℝ)| |(k 3 : ℝ)| from by
        simpa only [KdVPlan.n3, le_min_iff] using h) with ⟨h01,h02,h03,h12,h13,h23⟩
    fin_cases i <;> fin_cases j <;> simp_all [max_comm] <;> tauto
  · intro h
    unfold KdVPlan.n3
    exact le_min (h 0 1 (by decide)) (le_min (h 0 2 (by decide)) (le_min (h 0 3 (by decide)) (le_min (h 1 2 (by decide)) (le_min (h 1 3 (by decide)) (h 2 3 (by decide))))))

theorem yui_aux_0018 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ {α : Type} [Fintype α] (k : α → ℤ), Function.Injective k →\n∀ W : Fin 4 → α → ℝ, (∀ i a, 0 ≤ W i a) →\n(∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0 then ∏ i : Fin 4, W i (a i) else 0) ≤\nReal.sqrt (∑ a : α, (W 0 a)^2) * Real.sqrt (∑ a : α, (W 1 a)^2) * (∑ a : α, W 2 a) * (∑ a : α, W 3 a)" := by
  intro α inst k hk W hW
  classical
  let P : ℝ := Real.sqrt (∑ a : α, (W 0 a)^2) * Real.sqrt (∑ a : α, (W 1 a)^2)
  let f : α → α → α → α → ℝ := fun a b c d =>
    if k a+k b+k c+k d=0 then W 0 a*W 1 b*W 2 c*W 3 d else 0
  have he : (∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0 then ∏ i : Fin 4, W i (a i) else 0) =
    ∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α, f a b c d := by
    rw [@yui_aux_0011 T gamma R α]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    simp [f, Fin.sum_univ_succ, Fin.prod_univ_succ, add_assoc, mul_assoc]
  have hrotate : (∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α, f a b c d) =
      ∑ c : α, ∑ d : α, ∑ a : α, ∑ b : α, f a b c d := by
    calc
      _ = ∑ ab : α × α, ∑ cd : α × α, f ab.1 ab.2 cd.1 cd.2 := by simp only [Fintype.sum_prod_type]
      _ = ∑ cd : α × α, ∑ ab : α × α, f ab.1 ab.2 cd.1 cd.2 := Finset.sum_comm
      _ = _ := by simp only [Fintype.sum_prod_type]
  have hcell : ∀ c d : α, (∑ a : α, ∑ b : α, f a b c d) ≤ P * W 2 c * W 3 d := by
    intro c d
    have he' : (∑ a : α, ∑ b : α, f a b c d) =
        (∑ a : α, ∑ b : α, if k a+k b= -(k c+k d) then W 0 a*W 1 b else 0) * W 2 c * W 3 d := by
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp [f]
      have hiff : k a+k b+k c+k d=0 ↔ k a+k b= -(k c+k d) := by omega
      simp only [hiff]
      split_ifs <;> ring
    rw [he']
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (@yui_aux_0016 T gamma R α inst k hk (W 0) (W 1) (-(k c+k d))) (hW 2 c)) (hW 3 d)
  rw [he, hrotate]
  calc
    _ ≤ ∑ c : α, ∑ d : α, P*W 2 c*W 3 d := Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun d hd => hcell c d
    _ = _ := by
      dsimp [P]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem yui_aux_0019 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ k : ℤ, (k.natAbs : ℝ) = |(k:ℝ)| ∧ (k ≠ 0 → k.natAbs ≠ 0)" := by
  intro k
  constructor
  · rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  · exact Int.natAbs_ne_zero.mpr

theorem yui_aux_0020 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "(∀ k : ℤ, k ≠ 0 →\n (2:ℝ)^(Nat.log 2 k.natAbs) ≤ |(k:ℝ)| ∧ |(k:ℝ)| < (2:ℝ)^(Nat.log 2 k.natAbs+1)) ∧\n(∀ (B : Finset ℤ) (j : ℕ), (B.filter (fun k => Nat.log 2 k.natAbs=j)).card ≤ 4*2^j)" := by
  classical
  constructor
  · intro k hk
    have heq : (k.natAbs : ℝ) = |(k:ℝ)| := (@yui_aux_0019 T gamma R k).1
    have hk' : k.natAbs ≠ 0 := (@yui_aux_0019 T gamma R k).2 hk
    have hl : ((2^(Nat.log 2 k.natAbs) : ℕ):ℝ) ≤ (k.natAbs:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hk'
    have hu : (k.natAbs:ℝ) < ((2^(Nat.log 2 k.natAbs+1) : ℕ):ℝ) := by exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<2) k.natAbs
    constructor
    · simpa only [Nat.cast_pow, Nat.cast_ofNat, heq] using hl
    · simpa only [Nat.cast_pow, Nat.cast_ofNat, heq] using hu
  · intro B j
    let U : ℕ := 2^(j+1)
    have hsub : B.filter (fun k => Nat.log 2 k.natAbs=j) ⊆ Finset.Ico (-(U:ℤ)) (U:ℤ) := by
      intro k hk
      have hlog := (Finset.mem_filter.mp hk).2
      have hknat : k.natAbs < U := by
        dsimp [U]
        simpa only [hlog, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by decide : 1<2) k.natAbs
      have hkint : |k| < (U:ℤ) := by
        have hh : (k.natAbs:ℤ) < (U:ℤ) := by exact_mod_cast hknat
        simpa only [Int.natCast_natAbs] using hh
      exact Finset.mem_Ico.mpr ⟨(abs_lt.mp hkint).1.le, (abs_lt.mp hkint).2⟩
    have hcard := Finset.card_le_card hsub
    have hc : (Finset.Ico (-(U:ℤ)) (U:ℤ)).card = 2*U := by
      rw [Int.card_Ico]
      omega
    rw [hc] at hcard
    have he : 2*U = 4*2^j := by dsimp [U]; ring
    exact hcard.trans_eq he

theorem yui_aux_0021 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (k : Fin 4 → ℤ) (j : Fin 4 → ℕ) (p : Equiv.Perm (Fin 4)),\nAntitone (fun i => j (p i)) →\n(∀ i, (2:ℝ)^(j i) ≤ |(k i:ℝ)| ∧ |(k i:ℝ)| < (2:ℝ)^(j i+1)) →\n(∑ i : Fin 4, k i)=0 →\nj (p 0) ≤ j (p 1)+2 ∧ (2:ℝ)^(j (p 2)) ≤ KdVPlan.n3 (k 0) (k 1) (k 2) (k 3)" := by
  intro k j p hj hb hs
  have h12 : j (p 2) ≤ j (p 1) := hj (by decide)
  have h13 : j (p 3) ≤ j (p 1) := hj (by decide)
  have hs' : (∑ i : Fin 4, k (p i))=0 := (Equiv.sum_comp p k).trans hs
  have hsR : (k (p 0):ℝ)+(k (p 1):ℝ)+(k (p 2):ℝ)+(k (p 3):ℝ)=0 := by
    have hz : k (p 0)+k (p 1)+k (p 2)+k (p 3)=0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hs'
    exact_mod_cast hz
  have htri : |(k (p 0):ℝ)| ≤ |(k (p 1):ℝ)|+|(k (p 2):ℝ)|+|(k (p 3):ℝ)| := by
    have he : (k (p 0):ℝ) = -((k (p 1):ℝ)+(k (p 2):ℝ)+(k (p 3):ℝ)) := by linarith
    rw [he, abs_neg]
    exact (@yui_aux_0005 T gamma R ((k (p 1):ℝ)+(k (p 2):ℝ)) (k (p 3))).trans
      (@yui_aux_0006 T gamma R _ _ _ (@yui_aux_0005 T gamma R (k (p 1)) (k (p 2))))
  have hu1 := (hb (p 1)).2
  have hu2 := ((hb (p 2)).2).trans_le (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j (p 2)+1 ≤ j (p 1)+1 by omega))
  have hu3 := ((hb (p 3)).2).trans_le (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j (p 3)+1 ≤ j (p 1)+1 by omega))
  constructor
  · by_contra h
    have hgap : j (p 1)+3 ≤ j (p 0) := by omega
    have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hgap
    rw [pow_add] at hpow
    norm_num only [pow_succ, pow_zero, mul_one, OfNat.ofNat] at hpow
    rw [pow_succ] at hu1 hu2 hu3
    have hlo := (hb (p 0)).1
    have hpos : (0:ℝ) < 2^(j (p 1)) := by positivity
    nlinarith
  · apply (@yui_aux_0017 T gamma R k _).mpr
    intro i l hil
    have hbig : ∀ i : Fin 4, p.symm i ≤ 2 → (2:ℝ)^(j (p 2)) ≤ |(k i:ℝ)| := by
      intro i hi
      have hji : j (p 2) ≤ j i := by simpa only [p.apply_symm_apply] using hj hi
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji).trans (hb i).1
    by_cases hi : p.symm i ≤ 2
    · exact (hbig i hi).trans (le_max_left _ _)
    · have hne : p.symm i ≠ p.symm l := fun h => hil (p.symm.injective h)
      have hl : p.symm l ≤ 2 := by omega
      exact (hbig l hl).trans (le_max_right _ _)

theorem yui_aux_0022 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "(0 < (Real.sqrt 2)⁻¹ ∧ (Real.sqrt 2)⁻¹ < 1) ∧\n(∀ m n : ℕ, n ≤ m → (Real.sqrt 2)^m * (Real.sqrt 2)^n / (2:ℝ)^m = ((Real.sqrt 2)⁻¹)^(m-n)) ∧\n(∀ {α : Type} [Fintype α] (q : α → ℕ) (x : α → ℝ) (j : ℕ),\n(Finset.univ.filter (fun a => q a=j)).card ≤ 4*2^j →\n(∑ a : α, if q a=j then x a else 0) ≤\n2*(Real.sqrt 2)^j * Real.sqrt (∑ a : α, if q a=j then (x a)^2 else 0))" := by
  have hb : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hb2 : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hpow : ∀ j : ℕ, ((Real.sqrt 2)^j)^2 = (2:ℝ)^j := by
    intro j
    rw [← pow_mul, mul_comm j 2, pow_mul, hb2]
  constructor
  · constructor
    · positivity
    · have hg : (1:ℝ) < Real.sqrt 2 := by
        have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
        simpa only [Real.sqrt_one] using h
      simpa only [one_div] using (div_lt_one hb).2 hg
  constructor
  · intro m n hnm
    have hm := hpow m
    have he : (Real.sqrt 2)^m = (Real.sqrt 2)^(m-n)*(Real.sqrt 2)^n := by
      rw [← pow_add, Nat.sub_add_cancel hnm]
    calc
      _ = (Real.sqrt 2)^n / (Real.sqrt 2)^m := by
        rw [← hm]
        field_simp [ne_of_gt hb]
        <;> ring
      _ = _ := by
        rw [he, inv_pow]
        field_simp [ne_of_gt hb]
        <;> ring
  · intro α inst q x j hcard
    classical
    let s : Finset α := Finset.univ.filter (fun a => q a=j)
    have hc : (s.card:ℝ) ≤ 4*(2:ℝ)^j := by exact_mod_cast hcard
    have hs : Real.sqrt (s.card:ℝ) ≤ 2*(Real.sqrt 2)^j := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have he : (2*(Real.sqrt 2)^j)^2 = 4*(2:ℝ)^j := by rw [mul_pow, hpow]; norm_num
        simpa only [he] using hc
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1:ℝ)) x
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    calc
      _ = ∑ a ∈ s, x a := by simp only [s, Finset.sum_filter]
      _ ≤ Real.sqrt (s.card:ℝ)*Real.sqrt (∑ a ∈ s, (x a)^2) := hcs
      _ ≤ (2*(Real.sqrt 2)^j)*Real.sqrt (∑ a ∈ s, (x a)^2) :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
      _ = _ := by simp only [s, Finset.sum_filter]

theorem yui_aux_0023 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ {α : Type} [Fintype α] (k : α → ℤ) (q : α → ℕ) (x : Fin 4 → α → ℝ),\nFunction.Injective k → (∀ i a, 0 ≤ x i a) →\n(∀ a, (2:ℝ)^(q a) ≤ |(k a:ℝ)| ∧ |(k a:ℝ)| < (2:ℝ)^(q a+1)) →\n(∀ l : ℕ, (Finset.univ.filter (fun a => q a=l)).card ≤ 4*2^l) →\n∀ (j : Fin 4 → ℕ) (p : Equiv.Perm (Fin 4)), Antitone (fun i => j (p i)) →\n(∑ a : Fin 4 → α, if (∀ i, q (a i)=j i) ∧ (∑ i : Fin 4, k (a i))=0\n  then (∏ i : Fin 4, x i (a i))/KdVPlan.n3 (k (a 0)) (k (a 1)) (k (a 2)) (k (a 3)) else 0) ≤\n4 * ((Real.sqrt 2)⁻¹)^(j (p 2)-j (p 3)) *\n∏ i : Fin 4, Real.sqrt (∑ a : α, if q a=j i then (x i a)^2 else 0)" := by
  intro α inst k q x hk hx hb hc j p hj
  classical
  let W : Fin 4 → α → ℝ := fun i a => if q a=j i then x i a else 0
  let X : Fin 4 → ℝ := fun i => Real.sqrt (∑ a : α, if q a=j i then (x i a)^2 else 0)
  let A : ℝ := (2:ℝ)^(j (p 2))
  have hA : 0 < A := by dsimp [A]; positivity
  have hW : ∀ i a, 0 ≤ W i a := by intro i a; dsimp [W]; split_ifs <;> first | exact hx i a | positivity
  have hX : ∀ i, 0 ≤ X i := fun i => Real.sqrt_nonneg _
  have hn : ∀ i, Real.sqrt (∑ a : α, (W i a)^2) = X i := by
    intro i
    simp only [W, X, ite_pow, zero_pow (by decide : (2:ℕ) ≠ 0)]
  have hL : ∀ i, (∑ a : α, W i a) ≤ 2*(Real.sqrt 2)^(j i)*X i := by
    intro i
    exact (@yui_aux_0022 T gamma R).2.2 q (x i) (j i) (hc (j i))
  have hmaj : (∑ a : Fin 4 → α, if (∀ i, q (a i)=j i) ∧ (∑ i : Fin 4, k (a i))=0
      then (∏ i : Fin 4, x i (a i))/KdVPlan.n3 (k (a 0)) (k (a 1)) (k (a 2)) (k (a 3)) else 0) ≤
    A⁻¹ * (∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0 then ∏ i : Fin 4, W i (a i) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    by_cases hz : (∑ i : Fin 4, k (a i))=0
    · by_cases hs : ∀ i, q (a i)=j i
      · rw [if_pos ⟨hs,hz⟩, if_pos hz]
        have hprod : (∏ i : Fin 4, W i (a i)) = ∏ i : Fin 4, x i (a i) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp only [W, hs i, ite_true]
        rw [hprod]
        have hfreq : ∀ i, (2:ℝ)^(j i) ≤ |(k (a i):ℝ)| ∧ |(k (a i):ℝ)| < (2:ℝ)^(j i+1) := by
          intro i
          simpa only [hs i] using hb (a i)
        have hm := (@yui_aux_0021 T gamma R (fun i => k (a i)) j p hj hfreq hz).2
        have hnpos : 0 < KdVPlan.n3 (k (a 0)) (k (a 1)) (k (a 2)) (k (a 3)) := lt_of_lt_of_le hA hm
        have hp0 : 0 ≤ ∏ i : Fin 4, x i (a i) := Finset.prod_nonneg fun i hi => hx i (a i)
        calc
          _ ≤ (∏ i : Fin 4, x i (a i))/A := (div_le_div_iff₀ hnpos hA).2 (mul_le_mul_of_nonneg_left hm hp0)
          _ = _ := by ring
      · rw [if_neg (by intro h; exact hs h.1), if_pos hz]
        exact mul_nonneg (inv_nonneg.mpr hA.le) (Finset.prod_nonneg fun i hi => hW i (a i))
    · simp only [hz, and_false, if_false, mul_zero, le_refl]
  have hperm : (∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0 then ∏ i : Fin 4, W i (a i) else 0) =
      ∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0 then ∏ i : Fin 4, W (p i) (a i) else 0 := by
    let e : (Fin 4 → α) ≃ (Fin 4 → α) :=
      { toFun := fun a i => a (p i)
        invFun := fun a i => a (p.symm i)
        left_inv := by intro a; funext i; simp
        right_inv := by intro a; funext i; simp }
    apply Fintype.sum_equiv e
    intro a
    dsimp [e]
    simp only [Equiv.sum_comp p (fun i => k (a i)), @yui_aux_0014 T gamma R p (fun i => W i (a i))]
  have hconv : (∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0 then ∏ i : Fin 4, W i (a i) else 0) ≤
      X (p 0)*X (p 1)*(∑ a : α, W (p 2) a)*(∑ a : α, W (p 3) a) := by
    rw [hperm]
    simpa only [hn] using @yui_aux_0018 T gamma R α inst k hk (fun i => W (p i)) (fun i a => hW (p i) a)
  have hbound : X (p 0)*X (p 1)*(∑ a : α, W (p 2) a)*(∑ a : α, W (p 3) a) ≤
    X (p 0)*X (p 1)*(2*(Real.sqrt 2)^(j (p 2))*X (p 2))*(2*(Real.sqrt 2)^(j (p 3))*X (p 3)) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hL (p 2)) (mul_nonneg (hX _) (hX _))
    · exact hL (p 3)
    · exact Finset.sum_nonneg fun a ha => hW (p 3) a
    · positivity
  have h23 : j (p 3) ≤ j (p 2) := hj (by decide)
  calc
    _ ≤ A⁻¹ * (∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0 then ∏ i : Fin 4, W i (a i) else 0) := hmaj
    _ ≤ A⁻¹*(X (p 0)*X (p 1)*(2*(Real.sqrt 2)^(j (p 2))*X (p 2))*(2*(Real.sqrt 2)^(j (p 3))*X (p 3))) :=
      mul_le_mul_of_nonneg_left (hconv.trans hbound) (inv_nonneg.mpr hA.le)
    _ = 4*((Real.sqrt 2)^(j (p 2))*(Real.sqrt 2)^(j (p 3))/(2:ℝ)^(j (p 2)))*(∏ i : Fin 4, X (p i)) := by
      dsimp [A]
      simp [Fin.prod_univ_succ]
      <;> ring
    _ = _ := by
      rw [(@yui_aux_0022 T gamma R).2.1 _ _ h23, @yui_aux_0014 T gamma R p X]

theorem yui_aux_0024 (T : ℝ) (gamma : ℝ) (R : ℝ) : yui_aux_type% "∀ (n : ℕ) (K : (Fin 4 → Fin n) → ℝ) (j : Fin 4 → Fin n) (p : Equiv.Perm (Fin 4)), (∀ j, 0 ≤ K j) → 0 ≤ 4*K (fun i => j (p i))" := by
  intro n K j p hK
  exact mul_nonneg (by norm_num) (hK (fun i => j (p i)))

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ)  : yui_aux_type% "∀ {α : Type} [Fintype α] (n : ℕ) (k : α → ℤ) (q : α → Fin n) (x : Fin 4 → α → ℝ),\nFunction.Injective k → (∀ i a, 0 ≤ x i a) →\n(∀ a, (2:ℝ)^((q a:ℕ)) ≤ |(k a:ℝ)| ∧ |(k a:ℝ)| < (2:ℝ)^((q a:ℕ)+1)) →\n(∀ l : ℕ, (Finset.univ.filter (fun a => (q a:ℕ)=l)).card ≤ 4*2^l) →\n(∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0\n  then (∏ i : Fin 4, x i (a i))/KdVPlan.n3 (k (a 0)) (k (a 1)) (k (a 2)) (k (a 3)) else 0) ≤\n(24*4*(3/(1-(Real.sqrt 2)⁻¹))) * ∏ i : Fin 4, Real.sqrt (∑ a : α, (x i a)^2)" := by
  intro α inst n k q x hk hx hb hc
  classical
  let ρ : ℝ := (Real.sqrt 2)⁻¹
  have hρ : 0 ≤ ρ := (@yui_aux_0022 T gamma R).1.1.le
  have hρ' : ρ < 1 := (@yui_aux_0022 T gamma R).1.2
  let X : Fin 4 → ℕ → ℝ := fun i l => Real.sqrt (∑ a : α, if (q a:ℕ)=l then (x i a)^2 else 0)
  let H : (Fin 4 → Fin n) → ℝ := fun j =>
    ∑ a : Fin 4 → α, if (fun i => q (a i))=j ∧ (∑ i : Fin 4, k (a i))=0
      then (∏ i : Fin 4, x i (a i))/KdVPlan.n3 (k (a 0)) (k (a 1)) (k (a 2)) (k (a 3)) else 0
  let K : (Fin 4 → Fin n) → ℝ := fun j =>
    (if (j 1:ℕ) ≤ j 0 ∧ (j 0:ℕ) ≤ (j 1:ℕ)+2 then (1:ℝ) else 0) *
    (if (j 3:ℕ) ≤ j 2 then ρ^((j 2:ℕ)-(j 3:ℕ)) else 0)
  have hX : ∀ i l, 0 ≤ X i l := fun i l => Real.sqrt_nonneg _
  have hK : ∀ j, 0 ≤ K j := by intro j; dsimp [K]; split_ifs <;> positivity
  have hkernel : ∀ Y : Fin 4 → ℕ → ℝ, (∀ i l, 0 ≤ Y i l) →
      (∑ j : Fin 4 → Fin n, K j * ∏ i : Fin 4, Y i (j i)) ≤
      (3/(1-ρ)) * ∏ i : Fin 4, Real.sqrt (∑ j : Fin n, (Y i j)^2) := by
    intro Y hY
    exact @yui_aux_0013 T gamma R n ρ Y hρ hρ' hY
  have hcover : ∀ j : Fin 4 → Fin n, ∃ p : Equiv.Perm (Fin 4),
      H j ≤ 4*K (fun i => j (p i))*∏ i : Fin 4, X i (j i) := by
    intro j
    let f : Fin 4 → ℕ := fun i => (j i:ℕ)
    let p : Equiv.Perm (Fin 4) := Fin.revPerm.trans (Tuple.sort f)
    have hj : Antitone (fun i => f (p i)) := by
      intro i l hil
      change f (Tuple.sort f (Fin.rev l)) ≤ f (Tuple.sort f (Fin.rev i))
      apply Tuple.monotone_sort f
      simp only [Fin.le_def, Fin.val_rev]
      omega
    refine ⟨p, ?_⟩
    have h01 : (j (p 1):ℕ) ≤ j (p 0) := hj (by decide)
    have h23 : (j (p 3):ℕ) ≤ j (p 2) := hj (by decide)
    have heq : ∀ a : Fin 4 → α, ((fun i => q (a i))=j) ↔ (∀ i, (q (a i):ℕ)=(j i:ℕ)) := by
      intro a
      constructor
      · intro he i
        exact congrArg Fin.val (congrFun he i)
      · intro he
        funext i
        exact Fin.ext (he i)
    by_cases hgap : (j (p 0):ℕ) ≤ (j (p 1):ℕ)+2
    · have hcell := @yui_aux_0023 T gamma R α inst k (fun a => (q a:ℕ)) x hk hx hb hc f p hj
      simpa only [H, heq, X, K, f, h01, hgap, h23, and_self, ite_true, one_mul, mul_one, ρ] using hcell
    · have hz : H j=0 := by
        dsimp [H]
        apply Finset.sum_eq_zero
        intro a ha
        split_ifs with he
        · have hm : ∀ i, (2:ℝ)^(f i) ≤ |(k (a i):ℝ)| ∧ |(k (a i):ℝ)| < (2:ℝ)^(f i+1) := by
            intro i
            have hqi : q (a i)=j i := congrFun he.1 i
            simpa only [hqi, f] using hb (a i)
          have hg := (@yui_aux_0021 T gamma R (fun i => k (a i)) f p hj hm he.2).1
          exact (hgap hg).elim
        · rfl
      rw [hz]
      exact mul_nonneg (@yui_aux_0024 T gamma R n K j p hK) (Finset.prod_nonneg fun i hi => hX i (j i))
  have hsum := @yui_aux_0015 T gamma R n K H X 4 (3/(1-ρ)) hK (by norm_num) hX hkernel hcover
  have hpartition : (∑ j : Fin 4 → Fin n, H j) =
      ∑ a : Fin 4 → α, if (∑ i : Fin 4, k (a i))=0
        then (∏ i : Fin 4, x i (a i))/KdVPlan.n3 (k (a 0)) (k (a 1)) (k (a 2)) (k (a 3)) else 0 := by
    dsimp [H]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hz : (∑ i : Fin 4, k (a i))=0
    · simp only [hz, and_true, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    · simp only [hz, and_false, ite_false, Finset.sum_const_zero]
  have hnorm : ∀ i : Fin 4, (∑ j : Fin n, (X i j)^2) = ∑ a : α, (x i a)^2 := by
    intro i
    calc
      _ = ∑ j : Fin n, ∑ a : α, if (q a:ℕ)=(j:ℕ) then (x i a)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Real.sq_sqrt (Finset.sum_nonneg fun a ha => by split_ifs <;> positivity)
      _ = ∑ a : α, ∑ j : Fin n, if (q a:ℕ)=(j:ℕ) then (x i a)^2 else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hpartition] at hsum
  simpa only [hnorm, ρ] using hsum
#check @checked
#print axioms checked
end YuiAuxiliary
