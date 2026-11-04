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
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (k : ℤ), (KdVPlan.weight s k : ℂ) ≠ 0" := by
  intro s k
  have h : KdVPlan.weight s k ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity : 0 < 1 + (k : ℝ)^2) s)
  exact_mod_cast h

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, Function.Injective (KdVPlan.FromLP s)" := by
  intro s x y h
  apply Subtype.ext
  funext k
  exact mul_left_cancel₀ (yui_aux_0001 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 (-s / 2) k) (congrFun h k)

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.HB s (f+g) (KdVPlan.hn s f+KdVPlan.hn s g)) ∧ (∀ (s : ℝ) (f : KdVPlan.Coeff) (z : ℂ), KdVPlan.MemH s f → KdVPlan.MemH s (KdVPlan.scale z f) ∧ KdVPlan.hn s (KdVPlan.scale z f) = ‖z‖*KdVPlan.hn s f) ∧ (∀ (s : ℝ) (f : KdVPlan.Coeff), 0 ≤ KdVPlan.hn s f)" := by
  rcases h_T013 with ⟨hmem, hnorm, hrest⟩
  constructor
  · intro s f g hf hg
    obtain ⟨x, rfl⟩ := (hmem s f).mp hf
    obtain ⟨y, rfl⟩ := (hmem s g).mp hg
    have hadd : KdVPlan.FromLP s x + KdVPlan.FromLP s y = KdVPlan.FromLP s (x+y) := by
      funext k
      simp [KdVPlan.FromLP, mul_add]
    rw [hadd]
    exact ⟨(hmem _ _).mpr ⟨x+y, rfl⟩, by simpa only [hnorm] using norm_add_le x y⟩
  constructor
  · intro s f z hf
    obtain ⟨x, rfl⟩ := (hmem s f).mp hf
    have hscale : KdVPlan.scale z (KdVPlan.FromLP s x) = KdVPlan.FromLP s (z • x) := by
      funext k
      simp [KdVPlan.scale, KdVPlan.FromLP, mul_left_comm]
    rw [hscale]
    exact ⟨(hmem _ _).mpr ⟨z • x, rfl⟩, by simp only [hnorm, norm_smul]⟩
  · intro s f
    exact Real.sqrt_nonneg _

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → ∀ k : ℤ, Summable (fun j : ℤ => f j * g (k-j))" := by
  intro f g hf hg k
  have hf' : Summable (fun j : ℤ => ‖f j‖^2) := by simpa [KdVPlan.MemH, KdVPlan.weight] using hf
  have hg' : Summable (fun j : ℤ => ‖g j‖^2) := by simpa [KdVPlan.MemH, KdVPlan.weight] using hg
  have he : Function.Injective (fun j : ℤ => k-j) := by
    intro i j h
    change k-i=k-j at h
    omega
  have hkg : Summable (fun j : ℤ => ‖g (k-j)‖^2) := hg'.comp_injective he
  apply Summable.of_norm
  apply ((hf'.add hkg).div_const 2).of_nonneg_of_le
  · intro j; positivity
  · intro j
    change ‖f j * g (k-j)‖ ≤ (‖f j‖^2+‖g (k-j)‖^2)/2
    rw [norm_mul]
    nlinarith [sq_nonneg (‖f j‖-‖g (k-j)‖)]

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.HB s (f-g) (KdVPlan.hn s f+KdVPlan.hn s g)) ∧ (∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.hn s (-f) = KdVPlan.hn s f) ∧ ∀ (M a τ : ℝ) (f w : KdVPlan.Coeff), KdVPlan.StepData gamma M a τ f w → KdVPlan.hn 0 f ≤ M+1 ∧ KdVPlan.localQ gamma τ f w ≤ 2" := by
  have h := yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hneg : ∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.hn s (-f) = KdVPlan.hn s f := by
    intro s f
    simp [KdVPlan.hn]
  refine ⟨?_, hneg, ?_⟩
  · intro s f g hf hg
    have heq : KdVPlan.scale (-1) g = -g := by funext k; simp [KdVPlan.scale]
    have hg' := (h.2.1 s g (-1) hg).1
    rw [heq] at hg'
    simpa only [sub_eq_add_neg, hneg] using h.1 s f (-g) hf hg'
  · intro M a τ f w hd
    rcases hd with ⟨hM, ha, ht, ht1, hf, hw, hfs, hws, hwM, hd1⟩
    have hw0 : KdVPlan.HB 0 w (KdVPlan.hn gamma w) := h_T013.2.2.2.1 0 gamma w (le_of_lt h_H002.1) hw.1
    have hdiff := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.1 0 w (-1) hw0.1
    have hnmem : KdVPlan.MemH 0 (f-w) := by
      have hnw : KdVPlan.MemH 0 (-w) := by
        have heq : KdVPlan.scale (-1) w = -w := by funext k; simp [KdVPlan.scale]
        exact heq ▸ hdiff.1
      exact (h.1 0 f (-w) hf.1 hnw).1
    have heq : f-w+w=f := sub_add_cancel f w
    have hfbound := (h.1 0 (f-w) w hnmem hw0.1).2
    rw [heq] at hfbound
    constructor
    · linarith [hw0.2]
    · have hp : τ^gamma ≤ 1 := Real.rpow_le_one ht.le ht1 h_H002.1.le
      dsimp [KdVPlan.localQ]
      linarith

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s r C : ℝ) (m : ℤ → ℂ) (f : KdVPlan.Coeff), 0 ≤ C → KdVPlan.MemH s f → (∀ k, KdVPlan.weight r k * ‖m k‖^2 ≤ C^2*KdVPlan.weight s k) → KdVPlan.HB r (fun k => m k*f k) (C*KdVPlan.hn s f)" := by
  intro s r C m f hC hf hm
  have hw : ∀ (s : ℝ) (k : ℤ), 0 ≤ KdVPlan.weight s k := by
    intro s k
    exact (Real.rpow_pos_of_pos (by positivity : 0 < 1+(k:ℝ)^2) s).le
  have hn : ∀ k, 0 ≤ KdVPlan.weight r k*‖m k*f k‖^2 := by intro k; exact mul_nonneg (hw r k) (sq_nonneg _)
  have hb : ∀ k, KdVPlan.weight r k*‖m k*f k‖^2 ≤ C^2*(KdVPlan.weight s k*‖f k‖^2) := by
    intro k
    rw [norm_mul, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right (hm k) (sq_nonneg ‖f k‖)]
  have hsum : Summable (fun k => KdVPlan.weight r k*‖m k*f k‖^2) := (hf.mul_left (C^2)).of_nonneg_of_le hn hb
  refine ⟨hsum, ?_⟩
  unfold KdVPlan.hn
  calc
    _ ≤ Real.sqrt (∑' k, C^2*(KdVPlan.weight s k*‖f k‖^2)) := Real.sqrt_le_sqrt (hsum.tsum_le_tsum hb (hf.mul_left (C^2)))
    _ = C*Real.sqrt (∑' k, KdVPlan.weight s k*‖f k‖^2) := by rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (k : ℤ), ‖Complex.exp (Complex.I * ((t*(k:ℝ)^3 : ℝ):ℂ))‖ = 1" := by
  intro t k
  exact Complex.norm_exp_I_mul_ofReal (t*(k:ℝ)^3)

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s t : ℝ) (f : KdVPlan.Coeff), (KdVPlan.MemH s (KdVPlan.S t f) ↔ KdVPlan.MemH s f) ∧ KdVPlan.hn s (KdVPlan.S t f) = KdVPlan.hn s f" := by
  intro s t f
  have he : (fun k => KdVPlan.weight s k*‖KdVPlan.S t f k‖^2) = (fun k => KdVPlan.weight s k*‖f k‖^2) := by
    funext k
    change KdVPlan.weight s k*‖Complex.exp (Complex.I * ((t*(k:ℝ)^3 : ℝ):ℂ))*f k‖^2 = _
    rw [norm_mul, yui_aux_0007 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013, one_mul]
  constructor
  · change Summable _ ↔ Summable _
    rw [he]
  · unfold KdVPlan.hn
    rw [he]

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.HB s (KdVPlan.P f) (KdVPlan.hn s f)) ∧ (∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.HB s (KdVPlan.invD f) (KdVPlan.hn s f)) ∧ ∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH (s+1) f → KdVPlan.HB s (KdVPlan.dx f) (KdVPlan.hn (s+1) f)" := by
  have hmult := yui_aux_0006 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hw : ∀ (s : ℝ) (k : ℤ), 0 ≤ KdVPlan.weight s k := by intro s k; exact (Real.rpow_pos_of_pos (by positivity : 0<1+(k:ℝ)^2) s).le
  refine ⟨?_, ?_, ?_⟩
  · intro s f hf
    have heq : KdVPlan.P f = fun k : ℤ => (if k=0 then (0:ℂ) else 1)*f k := by funext k; by_cases h:k=0 <;> simp [KdVPlan.P,h]
    rw [heq]
    simpa only [one_mul] using hmult s s 1 (fun k : ℤ => if k=0 then (0:ℂ) else 1) f (by norm_num) hf (by
      intro k
      by_cases h:k=0 <;> simp [h, hw])
  · intro s f hf
    have heq : KdVPlan.invD f = fun k : ℤ => (if k=0 then (0:ℂ) else (Complex.I*(k:ℂ))⁻¹)*f k := by funext k; by_cases h:k=0 <;> simp [KdVPlan.invD,h]
    rw [heq]
    have hb : ∀ k : ℤ, KdVPlan.weight s k * ‖if k=0 then (0:ℂ) else (Complex.I*(k:ℂ))⁻¹‖^2 ≤ 1^2*KdVPlan.weight s k := by
      intro k
      by_cases hk:k=0
      · simp [hk, hw]
      · simp only [if_neg hk, norm_inv, norm_mul, Complex.norm_I, one_mul, one_pow]
        have hk1 : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
        have habs : ‖(k:ℂ)‖ = |(k:ℝ)| := by simp
        rw [habs]
        have hi : (|(k:ℝ)|⁻¹)^2 ≤ 1 := by
          have hi1 : |(k:ℝ)|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk1
          have hi0 : 0 ≤ |(k:ℝ)|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hi (hw s k)]
    simpa only [one_mul] using hmult s s 1 _ f (by norm_num) hf hb
  · intro s f hf
    have hb : ∀ k : ℤ, KdVPlan.weight s k*‖Complex.I*(k:ℂ)‖^2 ≤ 1^2*KdVPlan.weight (s+1) k := by
      intro k
      simp only [norm_mul, Complex.norm_I, one_mul, one_pow]
      have he : ‖(k:ℂ)‖^2 = (k:ℝ)^2 := by simp
      rw [he]
      unfold KdVPlan.weight
      rw [Real.rpow_add (by positivity : 0<1+(k:ℝ)^2), Real.rpow_one]
      have hpos : 0 ≤ (1+(k:ℝ)^2)^s := (Real.rpow_pos_of_pos (by positivity) s).le
      nlinarith
    change KdVPlan.HB s (fun k : ℤ => Complex.I*(k:ℂ)*f k) _
    simpa only [one_mul] using hmult (s+1) s 1 (fun k : ℤ => Complex.I*(k:ℂ)) f (by norm_num) hf hb

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (f f' g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.mul (f+f') g = KdVPlan.mul f g + KdVPlan.mul f' g) ∧ (∀ (f g g' : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → KdVPlan.MemH 0 g' → KdVPlan.mul f (g+g') = KdVPlan.mul f g + KdVPlan.mul f g') ∧ ∀ (f g : KdVPlan.Coeff) (z : ℂ), KdVPlan.mul (KdVPlan.scale z f) g = KdVPlan.scale z (KdVPlan.mul f g) ∧ KdVPlan.mul f (KdVPlan.scale z g) = KdVPlan.scale z (KdVPlan.mul f g)" := by
  have hs := yui_aux_0004 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  refine ⟨?_, ?_, ?_⟩
  · intro f f' g hf hf' hg
    funext k
    change (∑' j : ℤ, (f j+f' j)*g (k-j)) = (∑' j : ℤ, f j*g (k-j))+(∑' j : ℤ, f' j*g (k-j))
    simp only [add_mul]
    exact (hs f g hf hg k).tsum_add (hs f' g hf' hg k)
  · intro f g g' hf hg hg'
    funext k
    change (∑' j : ℤ, f j*(g (k-j)+g' (k-j))) = (∑' j : ℤ, f j*g (k-j))+(∑' j : ℤ, f j*g' (k-j))
    simp only [mul_add]
    exact (hs f g hf hg k).tsum_add (hs f g' hf hg' k)
  · intro f g z
    constructor
    · funext k
      change (∑' j : ℤ, (z*f j)*g (k-j)) = z*(∑' j : ℤ, f j*g (k-j))
      simp_rw [mul_assoc]
      exact tsum_mul_left
    · funext k
      change (∑' j : ℤ, f j*(z*g (k-j))) = z*(∑' j : ℤ, f j*g (k-j))
      simp_rw [mul_left_comm (f _) z]
      exact tsum_mul_left

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f f' g g' : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.MemH 0 g' → KdVPlan.J t (f+f') g = KdVPlan.J t f g+KdVPlan.J t f' g ∧ KdVPlan.J t f (g+g') = KdVPlan.J t f g+KdVPlan.J t f g'" := by
  intro t f f' g g' hf hf' hg hg'
  have hm := yui_aux_0010 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hi := (yui_aux_0009 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.1
  have hs := yui_aux_0008 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hin : ∀ x y : KdVPlan.Coeff, KdVPlan.S t (KdVPlan.invD (x+y)) = KdVPlan.S t (KdVPlan.invD x)+KdVPlan.S t (KdVPlan.invD y) := by
    intro x y
    funext k
    by_cases hk:k=0 <;> simp [KdVPlan.S, KdVPlan.invD, hk, mul_add]
  have hout : ∀ x y : KdVPlan.Coeff, KdVPlan.S (-t) (KdVPlan.P (x+y)) = KdVPlan.S (-t) (KdVPlan.P x)+KdVPlan.S (-t) (KdVPlan.P y) := by
    intro x y
    funext k
    by_cases hk:k=0 <;> simp [KdVPlan.S, KdVPlan.P, hk, mul_add]
  have hmem : ∀ x : KdVPlan.Coeff, KdVPlan.MemH 0 x → KdVPlan.MemH 0 (KdVPlan.S t (KdVPlan.invD x)) := by
    intro x hx
    exact (hs 0 t _).1.mpr (hi 0 x hx).1
  constructor
  · unfold KdVPlan.J
    rw [hin, hm.1 _ _ _ (hmem f hf) (hmem f' hf') (hmem g hg), hout]
  · unfold KdVPlan.J
    rw [hin, hm.2.1 _ _ _ (hmem f hf) (hmem g hg) (hmem g' hg'), hout]

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ C : ℝ, 0 < C ∧ ∀ (a t : ℝ) (f g : KdVPlan.Coeff), a ≤ t → KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → KdVPlan.ZeroMean f → KdVPlan.ZeroMean g → KdVPlan.HB 1 (KdVPlan.stage a t f g) (C*KdVPlan.hn 0 f*KdVPlan.hn 0 g)" := by
  rcases h_T005.1.1 with ⟨Cb, hCb, hb⟩
  refine ⟨Cb, hCb, ?_⟩
  intro a t f g hat hf hg hzf hzg
  have hJt := (hb.2.2.1 t f g hf hg).2.1
  have hJa := (hb.2.2.1 a f g hf hg).2.1
  have hdiff := (yui_aux_0005 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 1 _ _ hJt.1 hJa.1
  have hsc := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.1 1 _ (1/6) hdiff.1
  rw [h_T005.2.2.2.2 a t f g hat hf hg hzf hzg]
  refine ⟨hsc.1, ?_⟩
  rcases hdiff with ⟨_, hd⟩
  change KdVPlan.hn 1 (KdVPlan.scale (1/6) _) ≤ _
  rw [hsc.2]
  have hc : ‖(1/6:ℂ)‖ = (1/6:ℝ) := by norm_num
  rw [hc]
  have hn1 := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2 0 f
  have hn2 := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2 0 g
  nlinarith [hJt.2, hJa.2, mul_nonneg (hCb.le) (mul_nonneg hn1 hn2)]

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a t : ℝ) (f w : KdVPlan.Coeff), a ≤ t → KdVPlan.MemH 0 f → KdVPlan.MemH 0 w → KdVPlan.ZeroMean f → KdVPlan.ZeroMean w → KdVPlan.stage a t f f-KdVPlan.stage a t w w = KdVPlan.stage a t (f-w) f+KdVPlan.stage a t w (f-w)" := by
  intro a t f w hat hf hw hzf hzw
  have hd := (yui_aux_0005 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 0 f w hf hw
  have hzd : KdVPlan.ZeroMean (f-w) := by change f 0-w 0=0; rw [hzf,hzw]; ring
  have hlin := yui_aux_0011 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hJ : ∀ r, KdVPlan.J r f f-KdVPlan.J r w w = KdVPlan.J r (f-w) f+KdVPlan.J r w (f-w) := by
    intro r
    have h1 := (hlin r (f-w) w f w hd.1 hw hf hw).1
    rw [sub_add_cancel] at h1
    have h2 := (hlin r w w (f-w) w hw hw hd.1 hw).2
    rw [sub_add_cancel] at h2
    rw [h1,h2]
    abel
  have hs := h_T005.2.2.2.2
  rw [hs a t f f hat hf hf hzf hzf, hs a t w w hat hw hw hzw hzw, hs a t (f-w) f hat hd.1 hf hzd hzf, hs a t w (f-w) hat hw hd.1 hzw hzd]
  funext k
  have ht := congrFun (hJ t) k
  have ha := congrFun (hJ a) k
  simp only [Pi.sub_apply, Pi.add_apply] at ht ha
  simp only [KdVPlan.scale, Pi.sub_apply, Pi.add_apply]
  linear_combination (1/6:ℂ) * ht - (1/6:ℂ) * ha

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ (a τ : ℝ) (f w : KdVPlan.Coeff), KdVPlan.StepData gamma M a τ f w → KdVPlan.UB 1 a (a+τ) (KdVPlan.F a f) C ∧ KdVPlan.UB 1 a (a+τ) (fun t => KdVPlan.F a f t-KdVPlan.stage a t w w) (C*KdVPlan.hn 0 (f-w))" := by
  intro M hM
  rcases yui_aux_0012 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 with ⟨Cs,hCs,hs⟩
  let C := Cs*(M+1)^2+2*Cs*(M+1)
  have hM0 : 0 ≤ M := by linarith
  have hMp : 0 < M+1 := by linarith
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro a τ f w hd
  have hff := (yui_aux_0005 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2 M a τ f w hd
  rcases hd with ⟨_,ha,hτ,hτ1,hf,hw,hfs,hws,hwM,hd1⟩
  have hw0 := h_T013.2.2.2.1 0 gamma w h_H002.1.le hw.1
  have hdmem := (yui_aux_0005 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 0 f w hf.1 hw0.1
  have hzd : KdVPlan.ZeroMean (f-w) := by change f 0-w 0=0; rw [hf.2.1,hw.2.1]; ring
  have hnon := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2
  have hnf0 := hnon 0 f
  have hnw0 := hnon 0 w
  have hnd0 := hnon 0 (f-w)
  constructor
  · intro t ht
    have hb := hs a t f f ht.1 hf.1 hf.1 hf.2.1 hf.2.1
    refine ⟨hb.1, hb.2.trans ?_⟩
    change Cs*KdVPlan.hn 0 f*KdVPlan.hn 0 f ≤ C
    calc
      _ ≤ Cs*(M+1)*(M+1) := by gcongr <;> exact hff.1
      _ ≤ C := by dsimp [C]; nlinarith
  · intro t ht
    change KdVPlan.HB 1 (KdVPlan.stage a t f f-KdVPlan.stage a t w w) _
    rw [yui_aux_0013 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 a t f w ht.1 hf.1 hw0.1 hf.2.1 hw.2.1]
    have hb1 := hs a t (f-w) f ht.1 hdmem.1 hf.1 hzd hf.2.1
    have hb2 := hs a t w (f-w) ht.1 hw0.1 hdmem.1 hw.2.1 hzd
    have hb := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 1 _ _ hb1.1 hb2.1
    refine ⟨hb.1, hb.2.trans ?_⟩
    have he1 : KdVPlan.hn 1 (KdVPlan.stage a t (f-w) f) ≤ Cs*KdVPlan.hn 0 (f-w)*(M+1) := hb1.2.trans (by gcongr; exact hff.1)
    have he2 : KdVPlan.hn 1 (KdVPlan.stage a t w (f-w)) ≤ Cs*(M+1)*KdVPlan.hn 0 (f-w) := hb2.2.trans (by gcongr; linarith [hw0.2])
    have hc : 2*Cs*(M+1) ≤ C := by dsimp [C]; nlinarith [sq_nonneg (M+1)]
    calc
      _ ≤ (2*Cs*(M+1))*KdVPlan.hn 0 (f-w) := by nlinarith
      _ ≤ C*KdVPlan.hn 0 (f-w) := mul_le_mul_of_nonneg_right hc (hnon 0 (f-w))

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ (a τ : ℝ) (f w : KdVPlan.Coeff), KdVPlan.StepData gamma M a τ f w → KdVPlan.hn 0 f ≤ M+1 ∧ KdVPlan.localQ gamma τ f w ≤ 2 ∧ KdVPlan.UB 1 a (a+τ) (KdVPlan.F a f) C ∧ KdVPlan.UB 1 a (a+τ) (fun t => KdVPlan.F a f t-KdVPlan.stage a t w w) (C*KdVPlan.hn 0 (f-w)) ∧ (∀ t ∈ Icc a (a+τ), KdVPlan.hn (KdVPlan.ag gamma) (KdVPlan.F a f t)+KdVPlan.hn 0 (KdVPlan.F a f t) ≤ C*KdVPlan.localQ gamma τ f w ∧ KdVPlan.MemH (KdVPlan.ag gamma) (KdVPlan.F a f t))" := by
  intro M hM
  rcases yui_aux_0014 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 M hM with ⟨Cf,hCf,hF⟩
  rcases h_T006.2.2.1 M (by linarith) with ⟨Cs,hCs,hs⟩
  let C := 3*Cf+2*Cs
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro a τ f w hd
  have hinit := (yui_aux_0005 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2 M a τ f w hd
  have hfs := hF a τ f w hd
  rcases hd with ⟨_,ha,hτ,hτ1,hf,hw,hfS,hwS,hwM,hd1⟩
  have hCcf : Cf ≤ C := by dsimp [C]; linarith
  have hn := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2
  have hδ := hn 0 (f-w)
  have hpow : 0 ≤ τ^gamma := Real.rpow_nonneg hτ.le _
  refine ⟨hinit.1,hinit.2,?_,?_,?_⟩
  · intro t ht
    exact ⟨(hfs.1 t ht).1,(hfs.1 t ht).2.trans hCcf⟩
  · intro t ht
    exact ⟨(hfs.2 t ht).1,(hfs.2 t ht).2.trans (mul_le_mul_of_nonneg_right hCcf hδ)⟩
  · intro t ht
    have hA := (hs a τ t ha hτ hτ1 ht.1 ht.2 w hw.1 hw.2.1 hwM).1
    have hD := hfs.2 t ht
    have hD' := h_T013.2.2.2.1 (KdVPlan.ag gamma) 1 _ h_T006.2.1.1.2.le hD.1
    have hF' := h_T013.2.2.2.1 (KdVPlan.ag gamma) 1 _ h_T006.2.1.1.2.le (hfs.1 t ht).1
    have hb := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 (KdVPlan.ag gamma) _ _ hD'.1 hA.1
    have heq : KdVPlan.F a f t-KdVPlan.stage a t w w+KdVPlan.stage a t w w=KdVPlan.F a f t := sub_add_cancel _ _
    rw [heq] at hb
    have h0 := h_T013.2.2.2.1 0 (KdVPlan.ag gamma) _ h_T006.2.1.1.1 hF'.1
    refine ⟨?_,hF'.1⟩
    have hfsmall : KdVPlan.hn (KdVPlan.ag gamma) (KdVPlan.F a f t) ≤ Cf*KdVPlan.hn 0 (f-w)+Cs*τ^gamma := by linarith [hb.2,hD'.2,hD.2,hA.2]
    dsimp [C,KdVPlan.localQ]
    nlinarith [h0.2, mul_nonneg hCf.le hδ, mul_nonneg hCf.le hpow, mul_nonneg hCs.le hδ]

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (k : ℤ) (f : ℤ → ℂ), (∑' j : ℤ, f (k-j)) = ∑' j : ℤ, f j" := by
  intro k f
  exact (Equiv.subLeft k).tsum_eq f

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ f g : KdVPlan.Coeff, KdVPlan.mul f g = KdVPlan.mul g f) ∧ ∀ f g : KdVPlan.Coeff, KdVPlan.MemH 1 f → KdVPlan.MemH 1 g → KdVPlan.dx (KdVPlan.mul f g) = KdVPlan.mul (KdVPlan.dx f) g+KdVPlan.mul f (KdVPlan.dx g)" := by
  constructor
  · intro f g
    funext k
    change (∑' j : ℤ, f j*g (k-j)) = ∑' j : ℤ, g j*f (k-j)
    rw [← yui_aux_0016 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 k (fun j : ℤ => g j*f (k-j))]
    apply tsum_congr
    intro j
    simp [mul_comm]
  · intro f g hf hg
    have hi := h_T013.2.2.2.1
    have hdx := (yui_aux_0009 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2
    have hdf := hdx 0 f (by simpa using hf)
    have hdg := hdx 0 g (by simpa using hg)
    have hf0 := hi 0 1 f (by norm_num) hf
    have hg0 := hi 0 1 g (by norm_num) hg
    have hsum := yui_aux_0004 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
    funext k
    change Complex.I*(k:ℂ)*(∑' j : ℤ, f j*g (k-j)) = (∑' j : ℤ, KdVPlan.dx f j*g (k-j))+(∑' j : ℤ, f j*KdVPlan.dx g (k-j))
    rw [← (hsum (KdVPlan.dx f) g hdf.1 hg0.1 k).tsum_add (hsum f (KdVPlan.dx g) hf0.1 hdg.1 k), ← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [KdVPlan.dx, Int.cast_sub]
    ring

theorem yui_aux_0018 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f f' g g' : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.MemH 0 g' → KdVPlan.B t (f+f') g = KdVPlan.B t f g+KdVPlan.B t f' g ∧ KdVPlan.B t f (g+g') = KdVPlan.B t f g+KdVPlan.B t f g'" := by
  intro t f f' g g' hf hf' hg hg'
  have hm := yui_aux_0010 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hs := yui_aux_0008 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hin : ∀ x y : KdVPlan.Coeff, KdVPlan.S t (x+y) = KdVPlan.S t x+KdVPlan.S t y := by
    intro x y
    funext k
    simp [KdVPlan.S, mul_add]
  have hout : ∀ x y : KdVPlan.Coeff, KdVPlan.S (-t) (KdVPlan.dx (x+y)) = KdVPlan.S (-t) (KdVPlan.dx x)+KdVPlan.S (-t) (KdVPlan.dx y) := by
    intro x y
    funext k
    simp [KdVPlan.S, KdVPlan.dx, mul_add]
  have hmem : ∀ x : KdVPlan.Coeff, KdVPlan.MemH 0 x → KdVPlan.MemH 0 (KdVPlan.S t x) := by
    intro x hx
    exact (hs 0 t _).1.mpr hx
  constructor
  · unfold KdVPlan.B
    rw [hin, hm.1 _ _ _ (hmem f hf) (hmem f' hf') (hmem g hg), hout]
  · unfold KdVPlan.B
    rw [hin, hm.2.1 _ _ _ (hmem f hf) (hmem g hg) (hmem g' hg'), hout]

theorem yui_aux_0019 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.ZeroMean (KdVPlan.B t f g)) ∧ (∀ (a t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.ZeroMean (KdVPlan.stage a t f g)) ∧ (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH 1 f → KdVPlan.MemH 1 g → KdVPlan.HB 0 (KdVPlan.B t f g) (C*KdVPlan.hn 1 f*KdVPlan.hn 1 g)) ∧ (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH (1+gamma) f → KdVPlan.MemH (KdVPlan.ag gamma) f → KdVPlan.HB 0 (KdVPlan.B t f f) (C*KdVPlan.hn (1+gamma) f*KdVPlan.hn (KdVPlan.ag gamma) f))" := by
  have hS := yui_aux_0008 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hdx := (yui_aux_0009 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro t f g
    simp [KdVPlan.ZeroMean,KdVPlan.B,KdVPlan.S,KdVPlan.dx]
  · intro a t f g
    simp [KdVPlan.ZeroMean,KdVPlan.stage,KdVPlan.scale,KdVPlan.timeInt,KdVPlan.B,KdVPlan.S,KdVPlan.dx]
  · rcases h_T005.1.1 with ⟨C,hC,hb⟩
    refine ⟨C,hC,?_⟩
    intro t f g hf hg
    have hm := hb.2.1 (KdVPlan.S t f) (KdVPlan.S t g) ((hS 1 t f).1.mpr hf) ((hS 1 t g).1.mpr hg)
    have hd := hdx 0 _ (by simpa using hm.1)
    have hh := (hS 0 (-t) (KdVPlan.dx (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t g))))
    refine ⟨hh.1.mpr hd.1,?_⟩
    change KdVPlan.hn 0 (KdVPlan.S (-t) _) ≤ _
    rw [hh.2]
    have hm' : KdVPlan.hn 1 (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t g)) ≤ C*KdVPlan.hn 1 f*KdVPlan.hn 1 g := by simpa only [(hS 1 t f).2,(hS 1 t g).2] using hm.2
    exact (by simpa only [zero_add] using hd.2 : KdVPlan.hn 0 (KdVPlan.dx _) ≤ KdVPlan.hn 1 _).trans hm'
  · rcases h_T006.2.1.2 with ⟨C,hC,hb⟩
    refine ⟨2*C,by positivity,?_⟩
    intro t f hf hfa
    have hf1 := h_T013.2.2.2.1 1 (1+gamma) f (by linarith [h_H002.1]) hf
    have hsf1 := (hS 1 t f).1.mpr hf1.1
    have hd := hdx gamma f (by simpa [add_comm] using hf)
    have hm := hb (KdVPlan.S t (KdVPlan.dx f)) (KdVPlan.S t f) ((hS gamma t _).1.mpr hd.1) ((hS (KdVPlan.ag gamma) t f).1.mpr hfa)
    have heq : KdVPlan.B t f f = KdVPlan.scale 2 (KdVPlan.S (-t) (KdVPlan.mul (KdVPlan.S t (KdVPlan.dx f)) (KdVPlan.S t f))) := by
      unfold KdVPlan.B
      rw [(yui_aux_0017 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2 _ _ hsf1 hsf1]
      rw [(yui_aux_0017 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 (KdVPlan.S t f) (KdVPlan.dx (KdVPlan.S t f))]
      have hcomm : KdVPlan.dx (KdVPlan.S t f) = KdVPlan.S t (KdVPlan.dx f) := by funext k; simp [KdVPlan.dx,KdVPlan.S]; ring
      rw [hcomm]
      funext k
      simp [KdVPlan.scale,KdVPlan.S,mul_add]
      ring
    rw [heq]
    have hmS := (hS 0 (-t) _).1.mpr hm.1
    have hsc := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.1 0 _ 2 hmS
    refine ⟨hsc.1,?_⟩
    rw [hsc.2,(hS 0 (-t) _).2]
    have hh : KdVPlan.hn 0 (KdVPlan.mul (KdVPlan.S t (KdVPlan.dx f)) (KdVPlan.S t f)) ≤ C*KdVPlan.hn gamma (KdVPlan.dx f)*KdVPlan.hn (KdVPlan.ag gamma) f := by simpa only [(hS gamma t _).2,(hS (KdVPlan.ag gamma) t _).2] using hm.2
    have hnfa := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2 (KdVPlan.ag gamma) f
    have hbound : C*KdVPlan.hn gamma (KdVPlan.dx f)*KdVPlan.hn (KdVPlan.ag gamma) f ≤ C*KdVPlan.hn (1+gamma) f*KdVPlan.hn (KdVPlan.ag gamma) f := by gcongr; simpa [add_comm] using hd.2
    norm_num
    nlinarith [hh.trans hbound]

theorem yui_aux_0020 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ (a τ : ℝ) (f w : KdVPlan.Coeff), KdVPlan.StepData gamma M a τ f w → KdVPlan.UB 0 a (a+τ) (fun t => KdVPlan.B t (KdVPlan.F a f t) (KdVPlan.F a f t)) (C*KdVPlan.localQ gamma τ f w)" := by
  intro M hM
  rcases yui_aux_0015 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 M hM with ⟨Cf,hCf,hF⟩
  rcases h_T006.2.2.1 M (by linarith) with ⟨Cs,hCs,hs⟩
  rcases (yui_aux_0019 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2.1 with ⟨Cb,hCb,hb⟩
  rcases (yui_aux_0019 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2.2 with ⟨Ca,hCa,ha⟩
  let E := Cb*Cf*Cf+Cb*Cs*Cf
  let D := Ca*Cs*Cs
  let C := 1+E+D
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro a τ f w hd t ht
  have hf := hF a τ f w hd
  rcases hd with ⟨_,ha0,hτ,hτ1,hfd,hwd,hfs,hws,hwM,hd1⟩
  let A := KdVPlan.stage a t w w
  let V := KdVPlan.F a f t
  let U := V-A
  have hA := hs a τ t ha0 hτ hτ1 ht.1 ht.2 w hwd.1 hwd.2.1 hwM
  have hA1 := h_T013.2.2.2.1 1 (1+gamma) A (by linarith [h_H002.1]) hA.2.1
  have hV1 := hf.2.2.1 t ht
  have hU1 := hf.2.2.2.1 t ht
  have hU0 := h_T013.2.2.2.1 0 1 U (by norm_num) hU1.1
  have hV0 := h_T013.2.2.2.1 0 1 V (by norm_num) hV1.1
  have hA0 := h_T013.2.2.2.1 0 1 A (by norm_num) hA1.1
  have hlin := yui_aux_0018 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have heq : U+A=V := sub_add_cancel _ _
  have hl := (hlin t U A V A hU0.1 hA0.1 hV0.1 hA0.1).1
  have hr := (hlin t A A U A hA0.1 hA0.1 hU0.1 hA0.1).2
  rw [heq] at hl hr
  have hsum : KdVPlan.B t V V = (KdVPlan.B t U V+KdVPlan.B t A U)+KdVPlan.B t A A := by rw [hl,hr]; abel
  have hb1 := hb t U V hU1.1 hV1.1
  have hb2 := hb t A U hA1.1 hU1.1
  have hb3 := ha t A hA.2.1 hA.1.1
  have hn := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2
  have hδ := hn 0 (f-w)
  have hp : 0 ≤ τ^gamma := Real.rpow_nonneg hτ.le _
  have h1 : KdVPlan.hn 0 (KdVPlan.B t U V) ≤ Cb*(Cf*KdVPlan.hn 0 (f-w))*Cf := hb1.2.trans (by gcongr <;> first | exact hU1.2 | exact hV1.2 | exact hn _ _)
  have h2 : KdVPlan.hn 0 (KdVPlan.B t A U) ≤ Cb*Cs*(Cf*KdVPlan.hn 0 (f-w)) := hb2.2.trans (by gcongr <;> first | exact hU1.2 | exact hA1.2.trans hA.2.2 | exact hn _ _)
  have h3 : KdVPlan.hn 0 (KdVPlan.B t A A) ≤ Ca*Cs*(Cs*τ^gamma) := hb3.2.trans (by gcongr <;> first | exact hA.2.2 | exact hA.1.2 | exact hn _ _)
  have hadd := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1
  have h12 := hadd 0 _ _ hb1.1 hb2.1
  have h123 := hadd 0 _ _ h12.1 hb3.1
  change KdVPlan.HB 0 (KdVPlan.B t V V) _
  rw [hsum]
  refine ⟨h123.1,?_⟩
  have hbound : KdVPlan.hn 0 ((KdVPlan.B t U V+KdVPlan.B t A U)+KdVPlan.B t A A) ≤ E*KdVPlan.hn 0 (f-w)+D*τ^gamma := by dsimp [E,D]; nlinarith [h123.2,h12.2]
  refine hbound.trans ?_
  dsimp [C,KdVPlan.localQ]
  nlinarith [mul_nonneg hE hp,mul_nonneg hD hδ]

theorem yui_aux_0021 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ f : KdVPlan.Coeff, KdVPlan.invD (KdVPlan.dx f) = KdVPlan.P f) ∧ (∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.invD (KdVPlan.B t f g) = KdVPlan.S (-t) (KdVPlan.P (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t g)))) ∧ (∀ f : KdVPlan.Coeff, KdVPlan.ZeroMean f → KdVPlan.P f=f) ∧ ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.ZeroMean f → KdVPlan.ZeroMean g → KdVPlan.J t (KdVPlan.dx f) (KdVPlan.dx g) = KdVPlan.invD (KdVPlan.B t f g)" := by
  have hid : ∀ f : KdVPlan.Coeff, KdVPlan.invD (KdVPlan.dx f) = KdVPlan.P f := by
    intro f
    funext k
    by_cases hk:k=0
    · simp [KdVPlan.invD,KdVPlan.dx,KdVPlan.P,hk]
    · have hkC : (k:ℂ) ≠ 0 := by exact_mod_cast hk
      simp only [KdVPlan.invD,KdVPlan.dx,KdVPlan.P,if_neg hk]
      rw [←mul_assoc,inv_mul_cancel₀ (mul_ne_zero Complex.I_ne_zero hkC),one_mul]
  have hb : ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.invD (KdVPlan.B t f g) = KdVPlan.S (-t) (KdVPlan.P (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t g))) := by
    intro t f g
    funext k
    by_cases hk:k=0
    · simp [KdVPlan.invD,KdVPlan.B,KdVPlan.dx,KdVPlan.S,KdVPlan.P,hk]
    · have hkC : (k:ℂ) ≠ 0 := by exact_mod_cast hk
      simp only [KdVPlan.invD,KdVPlan.B,KdVPlan.dx,KdVPlan.S,KdVPlan.P,if_neg hk]
      field_simp
  have hp : ∀ f : KdVPlan.Coeff, KdVPlan.ZeroMean f → KdVPlan.P f=f := by
    intro f hf
    funext k
    change f 0=0 at hf
    by_cases hk:k=0 <;> simp [KdVPlan.P,hk,hf]
  refine ⟨hid,hb,hp,?_⟩
  intro t f g hf hg
  unfold KdVPlan.J
  rw [hid,hid,hp f hf,hp g hg,hb]

theorem yui_aux_0022 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 1 g → KdVPlan.ZeroMean f → KdVPlan.ZeroMean g → KdVPlan.HB 0 (KdVPlan.invD (KdVPlan.B t f g)) (C*KdVPlan.hn 0 f*KdVPlan.hn 1 g)) ∧ (∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH gamma f → KdVPlan.MemH (KdVPlan.ag gamma) g → KdVPlan.HB 0 (KdVPlan.invD (KdVPlan.B t f g)) (C*KdVPlan.hn gamma f*KdVPlan.hn (KdVPlan.ag gamma) g))" := by
  have hid := yui_aux_0021 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  have hS := yui_aux_0008 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013
  constructor
  · rcases h_T005.1.1 with ⟨C,hC,hb⟩
    refine ⟨C,hC,?_⟩
    intro t f g hf hg hzf hzg
    have hdx := (yui_aux_0009 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2 0 g (by simpa using hg)
    have hidf : KdVPlan.invD (KdVPlan.dx f) = f := (hid.1 f).trans (hid.2.2.1 f hzf)
    have hzd : KdVPlan.ZeroMean (KdVPlan.dx f) := by simp [KdVPlan.ZeroMean,KdVPlan.dx]
    have hx := (hb.2.2.2 t (KdVPlan.dx f) (KdVPlan.dx g) hzd (hidf.symm ▸ hf) hdx.1).2
    rw [hid.2.2.2 t f g hzf hzg] at hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    rw [hidf]
    have hn0 := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2 0 f
    gcongr
    simpa only [zero_add] using hdx.2
  · rcases h_T006.2.1.2 with ⟨C,hC,hb⟩
    refine ⟨C,hC,?_⟩
    intro t f g hf hg
    have hm := hb (KdVPlan.S t f) (KdVPlan.S t g) ((hS gamma t f).1.mpr hf) ((hS (KdVPlan.ag gamma) t g).1.mpr hg)
    have hp := (yui_aux_0009 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 0 _ hm.1
    rw [hid.2.1 t f g]
    refine ⟨(hS 0 (-t) _).1.mpr hp.1,?_⟩
    rw [(hS 0 (-t) _).2]
    exact hp.2.trans (by simpa only [(hS gamma t f).2,(hS (KdVPlan.ag gamma) t g).2] using hm.2)

theorem yui_aux_0023 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ (a τ : ℝ) (f w : KdVPlan.Coeff), KdVPlan.StepData gamma M a τ f w → KdVPlan.UB 0 a (a+τ) (fun t => KdVPlan.invD (KdVPlan.B t f (KdVPlan.F a f t))) (C*KdVPlan.localQ gamma τ f w)" := by
  intro M hM
  rcases yui_aux_0015 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 M hM with ⟨Cf,hCf,hF⟩
  rcases (yui_aux_0022 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 with ⟨Cb,hCb,hb⟩
  rcases (yui_aux_0022 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2 with ⟨Cp,hCp,hp⟩
  let C := Cb*Cf+Cp*M*Cf
  have hM0 : 0 ≤ M := by linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro a τ f w hd t ht
  have hFdata := hF a τ f w hd
  rcases hd with ⟨_,ha,hτ,hτ1,hfd,hwd,hfs,hws,hwM,hd1⟩
  let V := KdVPlan.F a f t
  have hV1 := hFdata.2.2.1 t ht
  have hVa := hFdata.2.2.2.2 t ht
  have hV0 := h_T013.2.2.2.1 0 1 V (by norm_num) hV1.1
  have hw0 := h_T013.2.2.2.1 0 gamma w h_H002.1.le hwd.1
  have hd0 := (yui_aux_0005 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 0 f w hfd.1 hw0.1
  have hzd : KdVPlan.ZeroMean (f-w) := by change f 0-w 0=0; rw [hfd.2.1,hwd.2.1]; ring
  have hzV : KdVPlan.ZeroMean V := (yui_aux_0019 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.1 a t f f
  have hb1 := hb t (f-w) V hd0.1 hV1.1 hzd hzV
  have hb2 := hp t w V hwd.1 hVa.2
  have hl := (yui_aux_0018 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 t (f-w) w V V hd0.1 hw0.1 hV0.1 hV0.1).1
  rw [sub_add_cancel] at hl
  have heq : KdVPlan.invD (KdVPlan.B t f V) = KdVPlan.invD (KdVPlan.B t (f-w) V)+KdVPlan.invD (KdVPlan.B t w V) := by
    rw [hl]
    funext k
    by_cases hk:k=0 <;> simp [KdVPlan.invD,hk,mul_add]
  change KdVPlan.HB 0 (KdVPlan.invD (KdVPlan.B t f V)) _
  rw [heq]
  have hadd := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).1 0 _ _ hb1.1 hb2.1
  refine ⟨hadd.1,?_⟩
  have hn := (yui_aux_0003 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013).2.2
  have hδ := hn 0 (f-w)
  have hVag := hn (KdVPlan.ag gamma) V
  have hVzero := hn 0 V
  have hq : 0 ≤ KdVPlan.localQ gamma τ f w := by dsimp [KdVPlan.localQ]; positivity
  have h1 : KdVPlan.hn 0 (KdVPlan.invD (KdVPlan.B t (f-w) V)) ≤ Cb*KdVPlan.hn 0 (f-w)*Cf := hb1.2.trans (by gcongr; exact hV1.2)
  have h2 : KdVPlan.hn 0 (KdVPlan.invD (KdVPlan.B t w V)) ≤ Cp*M*(Cf*KdVPlan.localQ gamma τ f w) := hb2.2.trans (by gcongr <;> first | exact hwM | linarith [hVa.1])
  have hδq : KdVPlan.hn 0 (f-w) ≤ KdVPlan.localQ gamma τ f w := by
    exact le_add_of_nonneg_left (Real.rpow_nonneg hτ.le gamma)
  have h3 : Cb*KdVPlan.hn 0 (f-w)*Cf ≤ Cb*KdVPlan.localQ gamma τ f w*Cf := by gcongr
  refine hadd.2.trans ?_
  dsimp [C]
  nlinarith

theorem yui_aux_0024 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, ∃ (L : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] KdVPlan.Coeff) (K : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2), (∀ x, L x=KdVPlan.FromLP s x) ∧ (∀ f, KdVPlan.MemH s f → L (K f)=f ∧ ‖K f‖=KdVPlan.hn s f) ∧ (∀ f g, KdVPlan.MemH s f → KdVPlan.MemH s g → ‖K f-K g‖=KdVPlan.hn s (f-g))" := by
  intro s
  classical
  let L : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] KdVPlan.Coeff := ContinuousLinearMap.pi (fun k : ℤ => (KdVPlan.weight (-s/2) k : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k)
  have hL : ∀ x, L x=KdVPlan.FromLP s x := by intro x; rfl
  let K : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2 := fun f => if h : KdVPlan.MemH s f then Classical.choose ((h_T013.1 s f).mp h) else 0
  have hK : ∀ f, KdVPlan.MemH s f → L (K f)=f := by
    intro f hf
    dsimp [K]
    rw [dif_pos hf,hL]
    exact (Classical.choose_spec ((h_T013.1 s f).mp hf)).symm
  have hnorm : ∀ x, KdVPlan.hn s (L x) = ‖x‖ := by intro x; rw [hL]; exact h_T013.2.1 s x
  refine ⟨L,K,hL,?_,?_⟩
  · intro f hf
    exact ⟨hK f hf, by rw [←hnorm,hK f hf]⟩
  · intro f g hf hg
    rw [←hnorm, map_sub,hK f hf,hK g hg]

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T004 : KdVPlan.RemOutput) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f ↔ ∃ G : ℝ → lp (fun _ : ℤ => ℂ) 2, ContinuousOn G (Icc a b) ∧ ∀ t ∈ Icc a b, KdVPlan.FromLP s (G t)=f t" := by
  intro s a b f
  rcases yui_aux_0024 T gamma R h_H002 h_T004 h_T005 h_T006 h_T013 s with ⟨L,K,hL,hK,hD⟩
  constructor
  · intro hf
    refine ⟨fun t => K (f t),?_,?_⟩
    · rw [Metric.continuousOn_iff]
      intro t ht ε hε
      rcases hf.2 t ht ε hε with ⟨δ,hδ,hd⟩
      refine ⟨δ,hδ,?_⟩
      intro r hr hrt
      rw [dist_eq_norm,hD (f r) (f t) (hf.1 r hr) (hf.1 t ht)]
      simpa only [dist_eq_norm] using hd r hr (by simpa only [Real.dist_eq] using hrt)
    · intro t ht
      rw [←hL]
      exact (hK (f t) (hf.1 t ht)).1
  · rintro ⟨G,hG,hGf⟩
    constructor
    · intro t ht
      rw [←hGf t ht]
      exact (h_T013.1 s _).mpr ⟨G t,rfl⟩
    · intro t ht ε hε
      rcases (Metric.continuousOn_iff.mp hG) t ht ε hε with ⟨δ,hδ,hd⟩
      refine ⟨δ,hδ,?_⟩
      intro r hr hrt
      have hn : KdVPlan.hn s (f r-f t)=‖G r-G t‖ := by
        rw [←hGf r hr,←hGf t ht,←hL,←hL,←map_sub,hL,h_T013.2.1]
      rw [hn]
      exact hd r hr (by simpa only [Real.dist_eq] using hrt)
#check @checked
#print axioms checked
end YuiAuxiliary
