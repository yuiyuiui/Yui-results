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
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f : KdVPlan.Coeff, KdVPlan.Smooth f → ∀ m : ℕ, KdVPlan.MemH (m : ℝ) f" := by
  intro f hf m
  exact hf m

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), (∀ k, ‖f k‖ = ‖g k‖) → (KdVPlan.MemH s f ↔ KdVPlan.MemH s g) ∧ KdVPlan.hn s f = KdVPlan.hn s g" := by
  intro s f g h
  have he : (fun k => KdVPlan.weight s k * ‖f k‖^2) = (fun k => KdVPlan.weight s k * ‖g k‖^2) := by funext k; rw [h k]
  constructor
  · unfold KdVPlan.MemH; rw [he]
  · unfold KdVPlan.hn; rw [he]

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ F : ℤ → ℝ, (Summable (fun k => F (-k)) ↔ Summable F) ∧ (∑' k, F (-k)) = ∑' k, F k" := by
  intro F
  constructor
  · exact (Equiv.neg ℤ).summable_iff (f := F)
  · exact (Equiv.neg ℤ).tsum_eq F

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), (KdVPlan.MemH s (fun k => -f (-k)) ↔ KdVPlan.MemH s f) ∧ KdVPlan.hn s (fun k => -f (-k)) = KdVPlan.hn s f" := by
  intro s f
  have he : ∀ k : ℤ, KdVPlan.weight s k * ‖-f (-k)‖^2 = KdVPlan.weight s (-k) * ‖f (-k)‖^2 := by intro k; simp [KdVPlan.weight]
  have hh := @yui_aux_0003 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 (fun k => KdVPlan.weight s k * ‖f k‖^2)
  constructor
  · unfold KdVPlan.MemH; simp_rw [he]; exact hh.1
  · unfold KdVPlan.hn; simp_rw [he]; rw [hh.2]

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.MemH s (f-g) ∧ KdVPlan.hn s (f-g) ≤ KdVPlan.hn s f + KdVPlan.hn s g" := by
  intro s f g hf hg
  obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
  obtain ⟨y, rfl⟩ := (h_T013.1 s g).mp hg
  have he : KdVPlan.FromLP s x - KdVPlan.FromLP s y = KdVPlan.FromLP s (x-y) := by
    funext k
    simp [KdVPlan.FromLP, mul_sub]
  rw [he]
  constructor
  · exact (h_T013.1 s _).mpr ⟨x-y,rfl⟩
  · rw [h_T013.2.1, h_T013.2.1, h_T013.2.1]
    exact norm_sub_le x y

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ t : ℝ, ∀ k : ℤ, ‖Complex.exp (Complex.I * (t * (k : ℝ)^3 : ℝ))‖ = 1" := by
  intro t k
  exact Complex.norm_exp_I_mul_ofReal (t*(k : ℝ)^3)

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s t : ℝ, ∀ f : KdVPlan.Coeff, (KdVPlan.MemH s (KdVPlan.S t f) ↔ KdVPlan.MemH s f) ∧ KdVPlan.hn s (KdVPlan.S t f) = KdVPlan.hn s f" := by
  intro s t f
  apply @yui_aux_0002 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s (KdVPlan.S t f) f
  intro k
  change ‖Complex.exp (Complex.I * (t * (k : ℝ)^3 : ℝ)) * f k‖ = ‖f k‖
  rw [norm_mul, @yui_aux_0006 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013, one_mul]

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ t : ℝ, ∀ k : ℤ, Complex.exp (Complex.I * ((-t) * ((-k : ℤ) : ℝ)^3 : ℝ)) = Complex.exp (Complex.I * (t * (k : ℝ)^3 : ℝ))" := by
  intro t k
  congr 2
  push_cast
  ring

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (k : ℤ), |(k : ℝ)| ^ (2*s) = ((k : ℝ)^2)^s" := by
  intro s k
  rw [Real.rpow_mul (abs_nonneg _) 2 s, Real.rpow_two, sq_abs]

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ t : ℝ, ∀ f : KdVPlan.Coeff, KdVPlan.S t (fun k => -f (-k)) = fun k => -(KdVPlan.S (-t) f (-k))" := by
  intro t f
  funext k
  change Complex.exp (Complex.I * (t * (k : ℝ)^3 : ℝ)) * -f (-k) = -(Complex.exp (Complex.I * ((-t) * ((-k : ℤ) : ℝ)^3 : ℝ)) * f (-k))
  rw [@yui_aux_0008 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 t k, mul_neg]

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), 0 ≤ s → KdVPlan.MemH s f → KdVPlan.ZeroMean f → KdVPlan.MemDot s f ∧ KdVPlan.dn s f ≤ KdVPlan.hn s f" := by
  intro s f hs hf hz
  have hp : ∀ k : ℤ, 0 ≤ (if k = 0 then 0 else |(k : ℝ)| ^ (2*s) * ‖f k‖^2 : ℝ) := by intro k; split_ifs <;> positivity
  have hl : ∀ k : ℤ, (if k = 0 then 0 else |(k : ℝ)| ^ (2*s) * ‖f k‖^2 : ℝ) ≤ KdVPlan.weight s k * ‖f k‖^2 := by
    intro k
    split_ifs
    · unfold KdVPlan.weight; positivity
    · rw [@yui_aux_0009 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (sq_nonneg _) (by linarith) hs) (sq_nonneg _)
  have hd : Summable (fun k : ℤ => if k = 0 then 0 else |(k : ℝ)| ^ (2*s) * ‖f k‖^2) := Summable.of_nonneg_of_le hp hl hf
  refine ⟨⟨hz,hd⟩,Real.sqrt_le_sqrt ?_⟩
  exact hd.tsum_le_tsum hl hf

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f g : KdVPlan.Coeff, KdVPlan.mul (fun k => -f (-k)) (fun k => -g (-k)) = fun k => KdVPlan.mul f g (-k)" := by
  intro f g
  funext k
  unfold KdVPlan.mul
  have he := (Equiv.neg ℤ).tsum_eq (fun j : ℤ => f j * g (-k-j))
  change (∑' j : ℤ, -f (-j) * -g (-(k-j))) = ∑' j : ℤ, f j * g (-k-j)
  calc
    _ = ∑' j : ℤ, f (-j) * g (-k-(-j)) := by
      apply tsum_congr
      intro j
      simp only [neg_mul_neg]
      congr 2
      omega
    _ = _ := he

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f : KdVPlan.Coeff) (u : KdVPlan.Path), (∀ m : ℕ, KdVPlan.SourceSol (m : ℝ) T f u) → ∀ m : ℕ, KdVPlan.ContH (m : ℝ) 0 T (fun t k => iteratedDerivWithin 0 (fun r => u r k) (Set.Icc 0 T) t)" := by
  intro f u hu m
  simpa only [iteratedDerivWithin_zero] using (hu m).1

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path), KdVPlan.ContH s a b u → KdVPlan.ContH s a b (fun t k => -u t (-k))" := by
  intro s a b u hu
  refine ⟨fun t ht => (@yui_aux_0004 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s (u t)).1.mpr (hu.1 t ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δ,hδ,hd⟩ := hu.2 t ht ε hε
  refine ⟨δ,hδ,?_⟩
  intro r hr hrt
  have he : (fun k => -u r (-k)) - (fun k => -u t (-k)) = (fun k => -(u r-u t) (-k)) := by funext k; simp only [Pi.sub_apply, neg_sub_neg, neg_sub]
  rw [he, (@yui_aux_0004 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s (u r-u t)).2]
  exact hd r hr hrt

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.Data s f → KdVPlan.Data s (fun k => -f (-k))" := by
  intro s f hf
  refine ⟨(@yui_aux_0004 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s f).1.mpr hf.1, ?_, ?_⟩
  · change -f (-0) = 0
    have hz : f 0 = 0 := hf.2.1
    simp only [neg_zero, hz]
  · intro k
    simpa only [star_neg] using congrArg Neg.neg (hf.2.2 (-k))

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ A : ℝ, 0 ≤ A ∧ ∀ f : KdVPlan.Coeff, KdVPlan.Data gamma f → KdVPlan.hn gamma f ≤ R → ∃ U : KdVPlan.Path, KdVPlan.SourceSol gamma T (fun k => -f (-k)) U ∧ KdVPlan.DotCont gamma 0 T U ∧ (∀ V, KdVPlan.SourceClass T (fun k => -f (-k)) V → KdVPlan.SameOn 0 T U V) ∧ KdVPlan.SourceApprox gamma T (fun k => -f (-k)) U ∧ KdVPlan.DotUB gamma 0 T U A" := by
  obtain ⟨A,K,hA,hK,hbound,hrest⟩ := (h_E001.1 gamma T h_H002.1.le h_H001).2 R R h_H003.le h_H003.le
  refine ⟨A,hA,?_⟩
  intro f hf hR
  have hr := @yui_aux_0015 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 gamma f hf
  have hdot := @yui_aux_0011 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 gamma (fun k => -f (-k)) h_H002.1.le hr.1 hr.2.1
  have hg : KdVPlan.dn gamma (fun k => -f (-k)) ≤ R := hdot.2.trans (by rw [(@yui_aux_0004 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 gamma f).2]; exact hR)
  have h0 : KdVPlan.dn 0 (fun k => -f (-k)) ≤ R := by
    have hinc := h_T013.2.2.2.1 0 gamma (fun k => -f (-k)) h_H002.1.le hr.1
    have hd0 := @yui_aux_0011 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 0 (fun k => -f (-k)) (le_refl 0) hinc.1 hr.2.1
    exact hd0.2.trans (hinc.2.trans (by rw [(@yui_aux_0004 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 gamma f).2]; exact hR))
  obtain ⟨U,hU,hcont,huniq,hcons,happrox⟩ := (h_E001.1 gamma T h_H002.1.le h_H001).1 (fun k => -f (-k)) hdot.1 hr.2.2
  exact ⟨U,hU,hcont,huniq,happrox,hbound _ _ hdot.1 hr.2.2 h0 hg hU⟩

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.B t (fun k => -f (-k)) (fun k => -g (-k)) = (fun k => -KdVPlan.sourceB t f g (-k))" := by
  intro t f g
  let j : KdVPlan.Coeff → KdVPlan.Coeff := fun p k => -p (-k)
  have hS (r : ℝ) (p : KdVPlan.Coeff) : KdVPlan.S r (j p) = j (KdVPlan.S (-r) p) := @yui_aux_0010 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 r p
  have hD (p : KdVPlan.Coeff) : KdVPlan.dx (fun k => p (-k)) = j (KdVPlan.dx p) := by
    funext k
    dsimp [KdVPlan.dx,j]
    push_cast
    ring
  change KdVPlan.S (-t) (KdVPlan.dx (KdVPlan.mul (KdVPlan.S t (j f)) (KdVPlan.S t (j g)))) = j (KdVPlan.sourceB t f g)
  rw [hS,hS]
  change KdVPlan.S (-t) (KdVPlan.dx (KdVPlan.mul (fun k => -(KdVPlan.S (-t) f) (-k)) (fun k => -(KdVPlan.S (-t) g) (-k)))) = j (KdVPlan.sourceB t f g)
  rw [@yui_aux_0012 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013]
  rw [hD,hS]
  simp only [neg_neg]
  rfl

theorem yui_aux_0018 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (U : KdVPlan.Path), KdVPlan.SourceSol s T f U → KdVPlan.KSol s T (fun k => -f (-k)) (fun t k => -U t (-k))" := by
  intro s f U hU
  let j : KdVPlan.Coeff → KdVPlan.Coeff := fun p k => -p (-k)
  let u : KdVPlan.Path := fun t => j (U t)
  have htw (t : ℝ) : KdVPlan.Twist u t = j (KdVPlan.SourceTwist U t) := by
    change KdVPlan.S (-t) (j (U t)) = j (KdVPlan.S t (U t))
    simpa only [neg_neg] using (@yui_aux_0010 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 (-t) (U t))
  refine ⟨@yui_aux_0014 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s 0 T U hU.1, ?_, ?_⟩
  · intro t ht
    obtain ⟨hz,hr⟩ := hU.2.1 t ht
    constructor
    · change -U t (-0) = 0
      have hz' : U t 0 = 0 := hz
      simp only [neg_zero,hz']
    · intro k
      simpa only [star_neg] using congrArg Neg.neg (hr (-k))
  · change KdVPlan.IntegralEq KdVPlan.B 0 T (j f) (KdVPlan.Twist u)
    constructor
    · rw [htw]
      exact congrArg j hU.2.2.1
    · intro t ht
      rw [htw]
      simp_rw [htw]
      change j (KdVPlan.SourceTwist U t) = j f + KdVPlan.scale (1/2) (KdVPlan.timeInt 0 t (fun r => KdVPlan.B r (fun k => -(KdVPlan.SourceTwist U r) (-k)) (fun k => -(KdVPlan.SourceTwist U r) (-k))))
      simp_rw [@yui_aux_0017 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013]
      have he := congrArg j (hU.2.2.2 t ht)
      funext k
      have hek := congrFun he k
      simpa only [j, KdVPlan.scale, KdVPlan.timeInt, Pi.add_apply, intervalIntegral.integral_neg, mul_neg, neg_add_rev, add_comm] using hek

theorem yui_aux_0019 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path), KdVPlan.ContH s a b u → ∃ x : ℝ → lp (fun _ : ℤ => ℂ) 2, (∀ t ∈ Set.Icc a b, u t = KdVPlan.FromLP s (x t)) ∧ ContinuousOn x (Set.Icc a b)" := by
  intro s a b u hu
  classical
  have hh : ∀ t : ℝ, ∃ y : lp (fun _ : ℤ => ℂ) 2, t ∈ Set.Icc a b → u t = KdVPlan.FromLP s y := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · obtain ⟨y,hy⟩ := (h_T013.1 s (u t)).mp (hu.1 t ht)
      exact ⟨y,fun _ => hy⟩
    · exact ⟨0,fun ht' => False.elim (ht ht')⟩
  choose x hx using hh
  refine ⟨x,hx,?_⟩
  apply Metric.continuousOn_iff.mpr
  intro t ht ε hε
  obtain ⟨δ,hδ,hd⟩ := hu.2 t ht ε hε
  refine ⟨δ,hδ,?_⟩
  intro r hr hrt
  have he : u r-u t = KdVPlan.FromLP s (x r-x t) := by
    rw [hx r hr, hx t ht]
    funext k
    simp [KdVPlan.FromLP, mul_sub]
  have hh := hd r hr (by simpa only [Real.dist_eq] using hrt)
  rw [he,h_T013.2.1] at hh
  simpa only [dist_eq_norm] using hh

theorem yui_aux_0020 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (x : lp (fun _ : ℤ => ℂ) 2), f = KdVPlan.FromLP s x → KdVPlan.hn s f = ‖x‖ ∧ ∀ k, f k = (KdVPlan.weight (-s/2) k : ℂ) * x k" := by
  intro s f x hx
  subst f
  exact ⟨h_T013.2.1 s x,fun _ => rfl⟩

theorem yui_aux_0021 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path), KdVPlan.ContH s a b u → ContinuousOn (fun t => KdVPlan.hn s (u t)) (Set.Icc a b) ∧ ∀ k, ContinuousOn (fun t => u t k) (Set.Icc a b)" := by
  intro s a b u hu
  obtain ⟨x,hx,hc⟩ := @yui_aux_0019 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s a b u hu
  have hconv (t : ℝ) (ht : t ∈ Set.Icc a b) := @yui_aux_0020 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s (u t) (x t) (hx t ht)
  constructor
  · apply hc.norm.congr
    intro t ht
    exact (hconv t ht).1
  · intro k
    have heval : Continuous (fun y : lp (fun _ : ℤ => ℂ) 2 => y k) := (lp.lipschitzWith_one_eval 2 k).continuous
    have hh : ContinuousOn (fun t => (KdVPlan.weight (-s/2) k : ℂ) * x t k) (Set.Icc a b) := continuousOn_const.mul (heval.comp_continuousOn hc)
    apply hh.congr
    intro t ht
    exact (hconv t ht).2 k

theorem yui_aux_0022 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (q r a b : ℝ) (u : KdVPlan.Path), q ≤ r → KdVPlan.ContH r a b u → KdVPlan.ContH q a b u" := by
  intro q r a b u hqr hu
  refine ⟨fun t ht => (h_T013.2.2.2.1 q r (u t) hqr (hu.1 t ht)).1, ?_⟩
  intro t ht ε hε
  obtain ⟨δ,hδ,hd⟩ := hu.2 t ht ε hε
  refine ⟨δ,hδ,?_⟩
  intro v hv hvd
  have hmem := (@yui_aux_0005 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 r (u v) (u t) (hu.1 v hv) (hu.1 t ht)).1
  exact (h_T013.2.2.2.1 q r (u v-u t) hqr hmem).2.trans_lt (hd v hv hvd)

theorem yui_aux_0023 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (u : KdVPlan.Path), KdVPlan.ContH s a b u → KdVPlan.EssBound s a b u" := by
  intro s a b u hu
  obtain ⟨hn,hcoeff⟩ := @yui_aux_0021 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s a b u hu
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hn
  refine ⟨fun k => (hcoeff k).aestronglyMeasurable measurableSet_Icc, ?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact hu.1 t ht
  · apply lt_of_le_of_lt (essSup_le_of_ae_le (ENNReal.ofReal C) ?_) ENNReal.ofReal_lt_top
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact ENNReal.ofReal_le_ofReal (hC ⟨t,ht,rfl⟩)

theorem yui_aux_0024 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, s ≤ 1 → (2 : ℝ)^s ≤ 4" := by
  intro s hs
  have hp : (2 : ℝ)^s ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hs
  norm_num at hp
  linarith

theorem yui_aux_0025 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (k : ℤ), 0 ≤ s → s ≤ 1 → k ≠ 0 → KdVPlan.weight s k ≤ 4 * |(k : ℝ)| ^ (2*s)" := by
  intro s k hs hs1 hk
  have hx : 1 ≤ (k : ℝ)^2 := by
    have ha : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    nlinarith [sq_abs (k : ℝ)]
  rw [@yui_aux_0009 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013]
  unfold KdVPlan.weight
  calc
    (1+(k : ℝ)^2)^s ≤ (2*(k : ℝ)^2)^s := Real.rpow_le_rpow (by positivity) (by linarith) hs
    _ = (2 : ℝ)^s * ((k : ℝ)^2)^s := Real.mul_rpow (by norm_num) (sq_nonneg _)
    _ ≤ 4 * ((k : ℝ)^2)^s := mul_le_mul_of_nonneg_right (@yui_aux_0024 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s hs1) (Real.rpow_nonneg (sq_nonneg _) _)

theorem yui_aux_0026 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), 0 ≤ s → s ≤ 1 → KdVPlan.MemDot s f → KdVPlan.MemH s f ∧ KdVPlan.hn s f ≤ 2*KdVPlan.dn s f" := by
  intro s f hs hs1 hf
  let d : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^(2*s)*‖f k‖^2
  have hz : f 0 = 0 := hf.1
  have hp : ∀ k, 0 ≤ KdVPlan.weight s k * ‖f k‖^2 := by intro k; unfold KdVPlan.weight; positivity
  have hl : ∀ k, KdVPlan.weight s k * ‖f k‖^2 ≤ 4*d k := by
    intro k
    by_cases hk : k = 0
    · subst k; simp [d,hz]
    · dsimp [d]
      rw [if_neg hk]
      have h := mul_le_mul_of_nonneg_right (@yui_aux_0025 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s k hs hs1 hk) (sq_nonneg ‖f k‖)
      nlinarith
  have hd : Summable d := hf.2
  have h4 : Summable (fun k => 4*d k) := hd.mul_left 4
  have hmem : KdVPlan.MemH s f := Summable.of_nonneg_of_le hp hl h4
  refine ⟨hmem,?_⟩
  change Real.sqrt (∑' k, KdVPlan.weight s k * ‖f k‖^2) ≤ 2*Real.sqrt (∑' k, d k)
  calc
    _ ≤ Real.sqrt (∑' k, 4*d k) := Real.sqrt_le_sqrt (hmem.tsum_le_tsum hl h4)
    _ = 2*Real.sqrt (∑' k, d k) := by rw [tsum_mul_left,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num

theorem yui_aux_0027 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (U : KdVPlan.Path), KdVPlan.SmoothOn a b U → KdVPlan.SmoothOn a b (fun t k => -U t (-k))" := by
  intro a b U hU
  constructor
  · intro k; exact (hU.1 (-k)).neg
  · intro m j
    simp_rw [iteratedDerivWithin_fun_neg]
    exact @yui_aux_0014 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 (m : ℝ) a b (fun t k => iteratedDerivWithin j (fun r => U r k) (Set.Icc a b) t) (hU.2 m j)

theorem yui_aux_0028 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.sourceB t (fun k => -f (-k)) (fun k => -g (-k)) = (fun k => -KdVPlan.B t f g (-k))" := by
  intro t f g
  have he := @yui_aux_0017 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 t (fun k => -f (-k)) (fun k => -g (-k))
  funext k
  have hk := congrFun he (-k)
  simp only [neg_neg] at hk
  exact (neg_eq_iff_eq_neg.mpr hk).symm

theorem yui_aux_0029 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (u : KdVPlan.Path), KdVPlan.KSol s T f u → KdVPlan.SourceSol s T (fun k => -f (-k)) (fun t k => -u t (-k))" := by
  intro s f u hu
  let j : KdVPlan.Coeff → KdVPlan.Coeff := fun p k => -p (-k)
  let U : KdVPlan.Path := fun t => j (u t)
  have htw (t : ℝ) : KdVPlan.SourceTwist U t = j (KdVPlan.Twist u t) := by
    exact @yui_aux_0010 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 t (u t)
  refine ⟨@yui_aux_0014 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 s 0 T u hu.1, ?_, ?_⟩
  · intro t ht
    obtain ⟨hz,hr⟩ := hu.2.1 t ht
    constructor
    · change -u t (-0) = 0
      have hz' : u t 0 = 0 := hz
      simp only [neg_zero,hz']
    · intro k
      simpa only [star_neg] using congrArg Neg.neg (hr (-k))
  · change KdVPlan.IntegralEq KdVPlan.sourceB 0 T (j f) (KdVPlan.SourceTwist U)
    constructor
    · rw [htw]
      exact congrArg j hu.2.2.1
    · intro t ht
      rw [htw]
      simp_rw [htw]
      change j (KdVPlan.Twist u t) = j f + KdVPlan.scale (1/2) (KdVPlan.timeInt 0 t (fun r => KdVPlan.sourceB r (fun k => -(KdVPlan.Twist u r) (-k)) (fun k => -(KdVPlan.Twist u r) (-k))))
      simp_rw [@yui_aux_0028 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013]
      have he := congrArg j (hu.2.2.2 t ht)
      funext k
      have hek := congrFun he k
      simpa only [j, KdVPlan.scale, KdVPlan.timeInt, Pi.add_apply, intervalIntegral.integral_neg, mul_neg, neg_add_rev, add_comm] using hek

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_E001 : KdVPlan.EFlow) (h_E002 : KdVPlan.EDependence) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (u : KdVPlan.Path), 0 ≤ s → KdVPlan.SourceSol s T f u → KdVPlan.SourceClass T f u" := by
  intro s f u hs hu
  exact ⟨hu.2.1, @yui_aux_0023 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 0 0 T u (@yui_aux_0022 T gamma R h_H001 h_H002 h_H003 h_E001 h_E002 h_T013 0 s 0 T u hs hu.1), hu.2.2⟩
#check @checked
#print axioms checked
end YuiAuxiliary
