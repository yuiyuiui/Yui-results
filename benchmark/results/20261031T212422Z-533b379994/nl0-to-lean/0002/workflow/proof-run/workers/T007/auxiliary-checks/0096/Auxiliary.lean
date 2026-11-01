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
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, KdVPlan.MemH s (0 : KdVPlan.Coeff) ∧ KdVPlan.hn s (0 : KdVPlan.Coeff) = 0" := by
  intro s
  simp [KdVPlan.MemH, KdVPlan.hn]

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s : ℝ, ∀ f g : Coeff, MemH s f → MemH s g → MemH s (f+g) ∧ hn s (f+g) ≤ hn s f + hn s g" := by
  exact (open KdVPlan in by
    intro s f g hf hg
    obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
    obtain ⟨y, rfl⟩ := (h_T013.1 s g).mp hg
    have hxy : FromLP s (x+y) = FromLP s x + FromLP s y := by
      funext k
      simp [FromLP, lp.coeFn_add, mul_add]
    constructor
    · exact (h_T013.1 s _).mpr ⟨x+y, hxy.symm⟩
    · rw [← hxy, h_T013.2.1, h_T013.2.1, h_T013.2.1]
      exact norm_add_le x y)

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s : ℝ, (∀ f : Coeff, 0 ≤ hn s f) ∧ (∀ f : Coeff, MemH s f → MemH s (-f) ∧ hn s (-f) = hn s f) ∧ (∀ f g : Coeff, MemH s f → MemH s g → MemH s (f-g) ∧ hn s (f-g) ≤ hn s f+hn s g) ∧ (∀ c : ℂ, ∀ f : Coeff, MemH s f → MemH s (scale c f) ∧ hn s (scale c f) = ‖c‖*hn s f)" := by
  exact (open KdVPlan in by
    intro s
    have hnneg : ∀ f : Coeff, MemH s f → MemH s (-f) ∧ hn s (-f) = hn s f := by
      intro f hf
      constructor
      · simpa [MemH, Pi.neg_apply, norm_neg] using hf
      · simp [hn, Pi.neg_apply, norm_neg]
    refine ⟨fun f => Real.sqrt_nonneg _, hnneg, ?_, ?_⟩
    · intro f g hf hg
      simpa [sub_eq_add_neg, (hnneg g hg).2] using (@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 s f (-g) hf (hnneg g hg).1)
    · intro c f hf
      obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
      have heq : FromLP s (c • x) = scale c (FromLP s x) := by
        funext k
        simp [FromLP, scale, mul_left_comm]
      constructor
      · exact (h_T013.1 s _).mpr ⟨c • x, heq.symm⟩
      · rw [← heq, h_T013.2.1, norm_smul, h_T013.2.1])

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f g : ℤ → ℝ, Summable f → Summable g → (∀ k, f k ≤ g k) → (∑' k, f k) ≤ ∑' k, g k" := by
  intro f g hf hg h
  exact hf.tsum_le_tsum h hg

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ x : ℤ → ℝ, (∀ k, 0 ≤ x k) → (Real.sqrt (∑' k, x k))^2 = ∑' k, x k" := by
  intro x hx
  apply Real.sq_sqrt
  exact tsum_nonneg hx

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s : ℝ, ∀ m : ℤ → ℂ, ∀ C : ℝ, 0 ≤ C → (∀ k, ‖m k‖ ≤ C) → ∀ f : Coeff, MemH s f → HB s (fun k => m k*f k) (C*hn s f)" := by
  exact (open KdVPlan in by
    intro s m C hC hm f hf
    have hw : ∀ k : ℤ, 0 ≤ weight s k := fun k => Real.rpow_nonneg (by positivity) _
    have hb : ∀ k : ℤ, weight s k * ‖m k*f k‖^2 ≤ C^2*(weight s k*‖f k‖^2) := by
      intro k
      rw [norm_mul, mul_pow]
      have hx : ‖m k‖^2 ≤ C^2 := sq_le_sq₀ (norm_nonneg _) hC |>.mpr (hm k)
      nlinarith [mul_le_mul_of_nonneg_right hx (mul_nonneg (hw k) (sq_nonneg ‖f k‖))]
    have hs : Summable (fun k => C^2*(weight s k*‖f k‖^2)) := hf.mul_left _
    have ht : MemH s (fun k => m k*f k) := Summable.of_nonneg_of_le (fun k => mul_nonneg (hw k) (sq_nonneg _)) hb hs
    refine ⟨ht, ?_⟩
    have hb' := @yui_aux_0004 T gamma R h_E006 h_T005 h_T013 _ _ ht hs hb
    rw [tsum_mul_left] at hb'
    have h1 := @yui_aux_0005 T gamma R h_E006 h_T005 h_T013 (fun k => weight s k * ‖m k*f k‖^2) (fun k => mul_nonneg (hw k) (sq_nonneg _))
    have h2 := @yui_aux_0005 T gamma R h_E006 h_T005 h_T013 (fun k => weight s k * ‖f k‖^2) (fun k => mul_nonneg (hw k) (sq_nonneg _))
    change hn s (fun k => m k*f k)^2 = _ at h1
    change hn s f^2 = _ at h2
    have hn1 : 0 ≤ hn s (fun k => m k*f k) := Real.sqrt_nonneg _
    have hn2 : 0 ≤ C*hn s f := mul_nonneg hC (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (hn s (fun k => m k*f k) - C*hn s f)])

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ t : ℝ, ∀ k : ℤ, ‖Complex.exp (Complex.I * (t*(k:ℝ)^3 : ℝ))‖=1" := by
  intro t k
  exact Complex.norm_exp_I_mul_ofReal _

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ s t : ℝ, ∀ f : Coeff, MemH s f → MemH s (S t f) ∧ hn s (S t f) = hn s f) ∧ (∀ s : ℝ, ∀ f : Coeff, MemH s f → HB s (P f) (hn s f)) ∧ (∀ t r : ℝ, ∀ f : Coeff, S t (S r f) = S (t+r) f) ∧ (∀ f : Coeff, S 0 f=f)" := by
  exact (open KdVPlan in by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s t f hf
      have he : (fun k => weight s k*‖S t f k‖^2) = (fun k => weight s k*‖f k‖^2) := by
        funext k
        simp only [S, norm_mul, @yui_aux_0007 T gamma R h_E006 h_T005 h_T013, one_mul]
      exact ⟨by simpa only [MemH, he] using hf, by simp only [hn, he]⟩
    · intro s f hf
      have he : P f = fun k => (if k=0 then (0:ℂ) else 1)*f k := by funext k; by_cases hk:k=0 <;> simp [P,hk]
      rw [he]
      simpa using (@yui_aux_0006 T gamma R h_E006 h_T005 h_T013 s (fun k => if k=0 then (0:ℂ) else 1) 1 (by norm_num) (fun k => by split_ifs <;> simp) f hf)
    · intro t r f
      funext k
      simp only [S, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · intro f
      funext k
      simp [S])

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s r : ℝ, ∀ A : Coeff → Coeff, ∀ guard : Coeff → Prop, (∀ f, MemH s f → guard f → MemH r (A f)) → (∀ f, MemH s f → guard f → ∃ C : ℝ, 0 ≤ C ∧ ∀ g, MemH s g → guard g → hn s (g-f) ≤ 1 → hn r (A g-A f) ≤ C*hn s (g-f)) → ContinuousMapH s r A guard" := by
  exact (open KdVPlan in by
    intro s r A guard hmem hbound f hf hgf
    refine ⟨hmem f hf hgf, ?_⟩
    intro ε hε
    obtain ⟨C, hC, hb⟩ := hbound f hf hgf
    refine ⟨min 1 (ε/(C+1)), lt_min zero_lt_one (div_pos hε (by linarith)), ?_⟩
    intro g hg hgg hd
    have hd1 : hn s (g-f) ≤ 1 := (lt_of_lt_of_le hd (min_le_left _ _)).le
    have hd2 := lt_of_lt_of_le hd (min_le_right 1 (ε/(C+1)))
    have hd3 : (C+1)*hn s (g-f) < ε := by
      have h := (lt_div_iff₀ (by linarith : 0<C+1)).mp hd2
      simpa [mul_comm] using h
    have hn0 : 0 ≤ hn s (g-f) := Real.sqrt_nonneg _
    have := hb g hg hgg hd1
    nlinarith)

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ a τ : ℝ, ∀ f : Coeff, Vst a τ f a=f) ∧ (∀ a τ : ℝ, τ≠0 → ∀ f : Coeff, Vst a τ f (a+τ)=f+stage a (a+τ) f f+Cst a f (a+τ)-rem a τ f f f)" := by
  exact (open KdVPlan in by
    constructor
    · intro a τ f
      funext k
      simp [Vst, F, stage, timeInt, Cst, Qst, scale]
    · intro a τ hτ f
      have hc : (((a+τ-a)/τ:ℝ):ℂ)=1 := by simp [hτ]
      rw [Vst, hc]
      have hs : scale 1 (Wst a τ f) = Wst a τ f := by funext k; simp [scale]
      rw [hs, Wst]
      change f+stage a (a+τ) f f+Cst a f (a+τ)+Qst a f (a+τ)-(Qst a f (a+τ)+rem a τ f f f) = _
      abel)

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ τ : ℝ, 0<τ → ∀ n : ℕ, gridIndex τ ((n:ℝ)*τ)=n) ∧ (∀ τ : ℝ, 0<τ → ∀ f : Coeff, ∀ n : ℕ, interp τ f ((n:ℝ)*τ) = twistedNum τ f n) ∧ (∀ τ : ℝ, ∀ f : Coeff, ∀ n : ℕ, numerical τ f (n+1)=psi τ (numerical τ f n))" := by
  exact (open KdVPlan in by
    have hfloor : ∀ τ : ℝ, 0<τ → ∀ n : ℕ, gridIndex τ ((n:ℝ)*τ)=n := by
      intro τ hτ n
      simp [gridIndex, hτ.ne']
    refine ⟨hfloor, ?_, ?_⟩
    · intro τ hτ f n
      simp only [interp, hfloor τ hτ n]
      exact (@yui_aux_0010 T gamma R h_E006 h_T005 h_T013).1 _ _ _
    · intro τ f n
      exact Function.iterate_succ_apply' _ _ _)

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ τ : ℝ, 0<τ → ∀ n : ℕ, ∀ f : Coeff, Data 0 f → Smooth f → Vst ((n:ℝ)*τ) τ f (((n:ℝ)+1)*τ)=S (-((n:ℝ)+1)*τ) (psi τ (S ((n:ℝ)*τ) f))" := by
  exact (open KdVPlan in by
    intro τ hτ n f hf hsm
    have he := h_E006 τ hτ n f hf hsm
    have hp := (@yui_aux_0010 T gamma R h_E006 h_T005 h_T013).2 ((n:ℝ)*τ) τ hτ.ne' f
    have ht : (n:ℝ)*τ+τ=((n:ℝ)+1)*τ := by ring
    rw [ht] at hp
    exact hp.trans he.symm)

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ k : ℤ, Function.Injective (fun j : ℤ => k-j)" := by
  intro k a b h
  change k-a=k-b at h
  omega

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f g : Coeff, MemH 0 f → MemH 0 g → ∀ k : ℤ, Summable (fun j : ℤ => f j*g (k-j))" := by
  exact (open KdVPlan in by
    intro f g hf hg k
    have hf' : Summable (fun j => ‖f j‖^2) := by simpa [MemH, weight] using hf
    have hg' : Summable (fun j => ‖g j‖^2) := by simpa [MemH, weight] using hg
    have hi : Function.Injective (fun j : ℤ => k-j) := @yui_aux_0013 T gamma R h_E006 h_T005 h_T013 k
    have hs : Summable (fun j : ℤ => ‖g (k-j)‖^2) := hg'.comp_injective hi
    apply (hf'.add hs).of_norm_bounded
    intro j
    rw [norm_mul]
    nlinarith [sq_nonneg (‖f j‖-‖g (k-j)‖)])

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f : Coeff, invD f = fun k : ℤ => (if k=0 then (0:ℂ) else (Complex.I*(k:ℂ))⁻¹)*f k" := by
  exact (open KdVPlan in by
    intro f
    funext k
    by_cases hk:k=0 <;> simp [invD,hk])

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ s : ℝ, ∀ f : Coeff, MemH s f → HB s (invD f) (hn s f)) ∧ (∀ f g : Coeff, invD (f-g)=invD f-invD g) ∧ (∀ t : ℝ, ∀ f g : Coeff, S t (f-g)=S t f-S t g) ∧ (∀ f g : Coeff, P (f-g)=P f-P g)" := by
  exact (open KdVPlan in by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s f hf
      rw [@yui_aux_0015 T gamma R h_E006 h_T005 h_T013 f]
      have hm : ∀ k : ℤ, ‖(if k=0 then (0:ℂ) else (Complex.I*(k:ℂ))⁻¹)‖ ≤ 1 := by
        intro k
        split_ifs with hk
        · simp
        · have hh : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
          rw [norm_inv, norm_mul, Complex.norm_I, one_mul]
          have hn : ‖(k:ℂ)‖ = |(k:ℝ)| := by simpa using Complex.norm_real (k:ℝ)
          rw [hn]
          exact inv_le_one_of_one_le₀ hh
      simpa using (@yui_aux_0006 T gamma R h_E006 h_T005 h_T013 s _ 1 (by norm_num) hm f hf)
    · intro f g; funext k; by_cases hk:k=0 <;> simp [invD,hk,mul_sub]
    · intro t f g; funext k; simp [S,mul_sub]
    · intro f g; funext k; by_cases hk:k=0 <;> simp [P,hk])

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∃ C : ℝ, 0<C ∧ (∀ f : Coeff, MemH 0 f → HB 1 (invD f) (C*hn 0 f)) ∧ (∀ f g : Coeff, MemH 1 f → MemH 1 g → HB 1 (mul f g) (C*hn 1 f*hn 1 g))" := by
  exact (open KdVPlan in by
    obtain ⟨C,hC,hi,hm,hrest⟩ := h_T005.1.1
    refine ⟨C,hC,?_,hm⟩
    intro f hf
    have hp := (@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).2.1 0 f hf
    have hz : ZeroMean (P f) := by simp [ZeroMean,P]
    have he : invD (P f)=invD f := by funext k; by_cases hk:k=0 <;> simp [invD,P,hk]
    have hb := (hi (P f) hp.1 hz).1
    rw [he] at hb
    exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left hp.2 hC.le)⟩)

theorem yui_aux_0018 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s r : ℝ, ∀ A : Coeff → Coeff, ∀ C : ℝ, 0≤C → (∀ f, MemH s f → HB r (A f) (C*hn s f)) → (∀ f g, A (g-f)=A g-A f) → ContinuousMapH s r A (fun _ => True)" := by
  exact (open KdVPlan in by
    intro s r A C hC hb he
    apply @yui_aux_0009 T gamma R h_E006 h_T005 h_T013 s r A (fun _=>True)
    · intro f hf _; exact (hb f hf).1
    · intro f hf _
      refine ⟨C,hC,?_⟩
      intro g hg _ _
      rw [← he]
      exact (hb (g-f) ((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 s).2.2.1 g f hg hf).1).2)

theorem yui_aux_0019 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ s r q : ℝ, ∀ A B : Coeff → Coeff, ∀ G H : Coeff → Prop, ContinuousMapH s r A G → ContinuousMapH r q B H → (∀ f, MemH s f → G f → H (A f)) → ContinuousMapH s q (fun f => B (A f)) G) ∧ (∀ s r : ℝ, ∀ A : Coeff → Coeff, ∀ G H : Coeff → Prop, ContinuousMapH s r A G → (∀ f, H f → G f) → ContinuousMapH s r A H)" := by
  exact (open KdVPlan in by
    constructor
    · intro s r q A B G H hA hB hguard f hf hgf
      have hAf := hA f hf hgf
      have hBf := hB (A f) hAf.1 (hguard f hf hgf)
      refine ⟨hBf.1, ?_⟩
      intro ε hε
      obtain ⟨δ,hδ,hδspec⟩ := hBf.2 ε hε
      obtain ⟨η,hη,hηspec⟩ := hAf.2 δ hδ
      refine ⟨η,hη,?_⟩
      intro g hg hgg hdist
      exact hδspec (A g) (hA g hg hgg).1 (hguard g hg hgg) (hηspec g hg hgg hdist)
    · intro s r A G H hA hguard f hf hgf
      have hf' := hA f hf (hguard f hgf)
      refine ⟨hf'.1, ?_⟩
      intro ε hε
      obtain ⟨δ,hδ,hspec⟩ := hf'.2 ε hε
      exact ⟨δ,hδ,fun g hg hgg hd=>hspec g hg (hguard g hgg) hd⟩)

theorem yui_aux_0020 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s r : ℝ, ∀ A B : Coeff → Coeff, ∀ G : Coeff → Prop, ContinuousMapH s r A G → ContinuousMapH s r B G → ContinuousMapH s r (fun f => A f+B f) G ∧ ContinuousMapH s r (fun f => A f-B f) G" := by
  exact (open KdVPlan in by
    intro s r A B G hA hB
    have hcore : ∀ D : Coeff → Coeff, ContinuousMapH s r D G → ContinuousMapH s r (fun f => A f+D f) G := by
      intro D hD f hf hgf
      have hAf:=hA f hf hgf
      have hDf:=hD f hf hgf
      refine ⟨(@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 r _ _ hAf.1 hDf.1).1, ?_⟩
      intro ε hε
      obtain ⟨δ,hδ,hδspec⟩ := hAf.2 (ε/2) (by positivity)
      obtain ⟨η,hη,hηspec⟩ := hDf.2 (ε/2) (by positivity)
      refine ⟨min δ η, lt_min hδ hη, ?_⟩
      intro g hg hgg hd
      have h1 := hδspec g hg hgg (lt_of_lt_of_le hd (min_le_left _ _))
      have h2 := hηspec g hg hgg (lt_of_lt_of_le hd (min_le_right _ _))
      have hmA := (@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 r).2.2.1 _ _ (hA g hg hgg).1 hAf.1
      have hmD := (@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 r).2.2.1 _ _ (hD g hg hgg).1 hDf.1
      have he : A g+D g-(A f+D f)=(A g-A f)+(D g-D f) := by abel
      rw [he]
      exact lt_of_le_of_lt (@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 r _ _ hmA.1 hmD.1).2 (by linarith)
    refine ⟨hcore B hB, ?_⟩
    have hnB : ContinuousMapH s r (fun f=> -B f) G := by
      intro f hf hgf
      have hf' := hB f hf hgf
      refine ⟨((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 r).2.1 _ hf'.1).1, ?_⟩
      intro ε hε
      obtain ⟨δ,hδ,hspec⟩ := hf'.2 ε hε
      refine ⟨δ,hδ,?_⟩
      intro g hg hgg hd
      have he : -B g- -B f= -(B g-B f) := by abel
      rw [he, ((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 r).2.1 _ ((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 r).2.2.1 _ _ (hB g hg hgg).1 hf'.1).1).2]
      exact hspec g hg hgg hd
    simpa only [sub_eq_add_neg] using hcore (fun f=> -B f) hnB)

theorem yui_aux_0021 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ s : ℝ, ContinuousMapH s s id (fun _=>True)) ∧ (∀ q r : ℝ, q≤r → ContinuousMapH r q id (fun _=>True)) ∧ (∀ s t : ℝ, ContinuousMapH s s (S t) (fun _=>True)) ∧ (∀ s : ℝ, ContinuousMapH s s P (fun _=>True)) ∧ (∀ s : ℝ, ∀ c : ℂ, ContinuousMapH s s (scale c) (fun _=>True)) ∧ (∀ s : ℝ, ContinuousMapH s s invD (fun _=>True)) ∧ ContinuousMapH 0 1 invD (fun _=>True)" := by
  exact (open KdVPlan in by
    have lin := @yui_aux_0018 T gamma R h_E006 h_T005 h_T013
    have ops := @yui_aux_0008 T gamma R h_E006 h_T005 h_T013
    have inv := @yui_aux_0016 T gamma R h_E006 h_T005 h_T013
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · intro s
      apply lin s s id 1 (by norm_num)
      · intro f hf; exact ⟨hf,by simp⟩
      · intro f g; rfl
    · intro q r hqr
      apply lin r q id 1 (by norm_num)
      · intro f hf; simpa using h_T013.2.2.2.1 q r f hqr hf
      · intro f g; rfl
    · intro s t
      apply lin s s (S t) 1 (by norm_num)
      · intro f hf; exact ⟨(ops.1 s t f hf).1,by simp [(ops.1 s t f hf).2]⟩
      · intro f g; exact inv.2.2.1 t g f
    · intro s
      apply lin s s P 1 (by norm_num)
      · intro f hf; simpa using ops.2.1 s f hf
      · intro f g; exact inv.2.2.2 g f
    · intro s c
      apply lin s s (scale c) ‖c‖ (norm_nonneg _)
      · intro f hf; exact ⟨((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 s).2.2.2 c f hf).1, le_of_eq ((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 s).2.2.2 c f hf).2⟩
      · intro f g; funext k; simp [scale,mul_sub]
    · intro s
      apply lin s s invD 1 (by norm_num)
      · intro f hf; simpa using inv.1 s f hf
      · intro f g; exact inv.2.1 g f
    · obtain ⟨C,hC,hi,hm⟩ := @yui_aux_0017 T gamma R h_E006 h_T005 h_T013
      exact lin 0 1 invD C hC.le hi (fun f g=>inv.2.1 g f))

theorem yui_aux_0022 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f f' g g' : Coeff, MemH 0 f → MemH 0 f' → MemH 0 g → MemH 0 g' → mul f g - mul f' g' = mul (f-f') g + mul f' (g-g')" := by
  exact (open KdVPlan in by
    intro f f' g g' hf hf' hg hg'
    have hsum := @yui_aux_0014 T gamma R h_E006 h_T005 h_T013
    have hsub := (@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 0).2.2.1
    funext k
    change (∑' j : ℤ, f j*g (k-j))-(∑' j : ℤ, f' j*g' (k-j)) = (∑' j : ℤ, (f-f') j*g (k-j))+(∑' j : ℤ, f' j*(g-g') (k-j))
    rw [← (hsum _ _ (hsub _ _ hf hf').1 hg k).tsum_add (hsum _ _ hf' (hsub _ _ hg hg').1 k), ← (hsum _ _ hf hg k).tsum_sub (hsum _ _ hf' hg' k)]
    apply tsum_congr
    intro j
    simp only [Pi.sub_apply]
    ring)

theorem yui_aux_0023 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ C u v ε : ℝ, 0≤C → 0≤u → 0≤v → 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ x y z : ℝ, 0≤x → 0≤y → 0≤z → x<δ → y<δ → z≤v+y → C*x*z+C*u*y<ε" := by
  intro C u v ε hC hu hv hε
  let A:=C*(u+v+1)+1
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨min 1 (ε/(2*A)), lt_min zero_lt_one (div_pos hε (by positivity)), ?_⟩
  intro x y z hx hy hz hxd hyd hzle
  have hx1 : x<ε/(2*A) := lt_of_lt_of_le hxd (min_le_right _ _)
  have hy1 : y<ε/(2*A) := lt_of_lt_of_le hyd (min_le_right _ _)
  have hy2 : y<1 := lt_of_lt_of_le hyd (min_le_left _ _)
  have hax : A*x<ε/2 := by have h:= (lt_div_iff₀ (by positivity : 0<2*A)).mp hx1; nlinarith
  have hay : A*y<ε/2 := by have h:= (lt_div_iff₀ (by positivity : 0<2*A)).mp hy1; nlinarith
  have hcu : C*u≤A := by dsimp [A]; nlinarith [mul_nonneg hC hv]
  have hcv : C*(v+1)≤A := by dsimp [A]; nlinarith [mul_nonneg hC hu]
  have hcz : C*x*z≤C*x*(v+1) := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hx)
  have hcx : C*x*(v+1)≤A*x := by nlinarith [mul_le_mul_of_nonneg_right hcv hx]
  have hcy : C*u*y≤A*y := mul_le_mul_of_nonneg_right hcu hy
  linarith

theorem yui_aux_0024 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s : ℝ, ∀ U V : Coeff → Coeff, ∀ G : Coeff → Prop, ContinuousMapH s 1 U G → ContinuousMapH s 1 V G → ContinuousMapH s 1 (fun f => mul (U f) (V f)) G" := by
  exact (open KdVPlan in by
    intro s U V G hU hV
    obtain ⟨C,hC,hi,hm⟩ := @yui_aux_0017 T gamma R h_E006 h_T005 h_T013
    have h00 : ∀ f, MemH 1 f → MemH 0 f := fun f hf => (h_T013.2.2.2.1 0 1 f (by norm_num) hf).1
    have hadd := @yui_aux_0002 T gamma R h_E006 h_T005 h_T013 1
    have hsub := (@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 1).2.2.1
    have hnonneg : ∀ f, 0≤hn 1 f := (@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 1).1
    intro f hf hgf
    have hUf:=hU f hf hgf
    have hVf:=hV f hf hgf
    refine ⟨(hm _ _ hUf.1 hVf.1).1, ?_⟩
    intro ε hε
    obtain ⟨δ,hδ,hδspec⟩ := @yui_aux_0023 T gamma R h_E006 h_T005 h_T013 C (hn 1 (U f)) (hn 1 (V f)) ε hC.le (hnonneg _) (hnonneg _) hε
    obtain ⟨ηU,hηU,hηUspec⟩ := hUf.2 δ hδ
    obtain ⟨ηV,hηV,hηVspec⟩ := hVf.2 δ hδ
    refine ⟨min ηU ηV, lt_min hηU hηV, ?_⟩
    intro g hg hgg hd
    have hUg:=(hU g hg hgg).1
    have hVg:=(hV g hg hgg).1
    have hUd:=(hsub _ _ hUg hUf.1).1
    have hVd:=(hsub _ _ hVg hVf.1).1
    have h1:=hm _ _ hUd hVg
    have h2:=hm _ _ hUf.1 hVd
    have ht:=(hadd _ _ h1.1 h2.1).2
    rw [@yui_aux_0022 T gamma R h_E006 h_T005 h_T013 _ _ _ _ (h00 _ hUg) (h00 _ hUf.1) (h00 _ hVg) (h00 _ hVf.1)]
    apply lt_of_le_of_lt ht
    apply lt_of_le_of_lt (add_le_add h1.2 h2.2)
    apply hδspec _ _ _ (hnonneg _) (hnonneg _) (hnonneg _) (hηUspec g hg hgg (lt_of_lt_of_le hd (min_le_left _ _))) (hηVspec g hg hgg (lt_of_lt_of_le hd (min_le_right _ _)))
    have hb := (hadd (V f) (V g-V f) hVf.1 hVd).2
    simpa only [add_sub_cancel] using hb)

theorem yui_aux_0025 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ τ : ℝ, ContinuousMapH 0 1 (Ftau τ) (fun _=>True)" := by
  exact (open KdVPlan in by
    intro τ
    have ops := @yui_aux_0021 T gamma R h_E006 h_T005 h_T013
    have comp := (@yui_aux_0019 T gamma R h_E006 h_T005 h_T013).1
    have post : ∀ A B : Coeff → Coeff, ContinuousMapH 0 1 A (fun _=>True) → ContinuousMapH 1 1 B (fun _=>True) → ContinuousMapH 0 1 (fun f=>B (A f)) (fun _=>True) := by
      intro A B hA hB
      exact comp 0 1 1 A B _ _ hA hB (by intros; trivial)
    have hd := ops.2.2.2.2.2.2
    have hsd := post invD (S τ) hd (ops.2.2.1 1 τ)
    have hp := @yui_aux_0024 T gamma R h_E006 h_T005 h_T013 0 _ _ (fun _=>True) hsd hsd
    have hq := @yui_aux_0024 T gamma R h_E006 h_T005 h_T013 0 _ _ (fun _=>True) hd hd
    have h1 := post _ (scale (1/6)) (post _ P hp (ops.2.2.2.1 1)) (ops.2.2.2.2.1 1 (1/6))
    have h2 := post _ (scale (1/6)) (post _ (S τ) (post _ P hq (ops.2.2.2.1 1)) (ops.2.2.1 1 τ)) (ops.2.2.2.2.1 1 (1/6))
    exact (@yui_aux_0020 T gamma R h_E006 h_T005 h_T013 0 1 _ _ (fun _=>True) h1 h2).2)

theorem yui_aux_0026 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ g : ℤ → ℂ, Summable (fun j => ‖g j‖^2) → Summable (fun j : ℤ => ‖g (-j)‖^2)" := by
  intro g hg
  have hi : Function.Injective (fun j : ℤ=> -j) := neg_injective
  exact hg.comp_injective hi

theorem yui_aux_0027 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ g : Coeff, MemH 0 g → MemH 0 (fun k : ℤ => g (-k)) ∧ hn 0 (fun k : ℤ => g (-k)) = hn 0 g" := by
  exact (open KdVPlan in by
    intro g hg
    have hg' : Summable (fun j => ‖g j‖^2) := by simpa [MemH,weight] using hg
    constructor
    · simpa [MemH,weight] using (@yui_aux_0026 T gamma R h_E006 h_T005 h_T013 g hg')
    · simp only [hn,weight,Real.rpow_zero,one_mul]
      congr 1
      exact (Equiv.neg ℤ).tsum_eq (fun j=>‖g j‖^2))

theorem yui_aux_0028 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f g : Coeff, MemH 0 f → MemH 0 g → ‖mul f g 0‖ ≤ hn 0 f*hn 0 g" := by
  exact (open KdVPlan in by
    intro f g hf hg
    have hgr := @yui_aux_0027 T gamma R h_E006 h_T005 h_T013 g hg
    obtain ⟨x,hx⟩ := (h_T013.1 0 f).mp hf
    obtain ⟨y,hy⟩ := (h_T013.1 0 (fun k : ℤ=>g (-k))).mp hgr.1
    have hxf : ∀ j : ℤ, f j=x j := by intro j; rw [hx]; simp [FromLP,weight]
    have hyg : ∀ j : ℤ, g (-j)=y j := by intro j; have h:=congrFun hy j; simpa [FromLP,weight] using h
    have hnx : hn 0 f=‖x‖ := hx ▸ h_T013.2.1 0 x
    have hny : hn 0 g=‖y‖ := hgr.2 ▸ (hy ▸ h_T013.2.1 0 y)
    have hpq : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := by rw [Real.holderConjugate_iff]; norm_num
    have hs : Summable (fun j : ℤ=>‖f j*g (-j)‖) := by
      simpa only [norm_mul,hxf,hyg] using lp.summable_mul hpq x y
    calc
      ‖mul f g 0‖ = ‖∑' j : ℤ, f j*g (-j)‖ := by simp [mul]
      _ ≤ ∑' j : ℤ, ‖f j*g (-j)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ hn 0 f*hn 0 g := by
        simpa only [norm_mul,hxf,hyg,hnx,hny] using lp.tsum_mul_le_mul_norm' hpq x y)

theorem yui_aux_0029 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f : Coeff, MemH 0 f → ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ g : Coeff, MemH 0 g → hn 0 (g-f)<δ → ‖mul g g 0-mul f f 0‖<ε" := by
  exact (open KdVPlan in by
    intro f hf ε hε
    have hn0 : ∀ f : Coeff, 0≤hn 0 f := fun f=>Real.sqrt_nonneg _
    obtain ⟨δ,hδ,hspec⟩ := @yui_aux_0023 T gamma R h_E006 h_T005 h_T013 1 (hn 0 f) (hn 0 f) ε (by norm_num) (hn0 _) (hn0 _) hε
    refine ⟨δ,hδ,?_⟩
    intro g hg hd
    have hsub := (@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 0).2.2.1
    have hgd := (hsub _ _ hg hf).1
    have h1 := @yui_aux_0028 T gamma R h_E006 h_T005 h_T013 (g-f) g hgd hg
    have h2 := @yui_aux_0028 T gamma R h_E006 h_T005 h_T013 f (g-f) hf hgd
    have he := congrFun (@yui_aux_0022 T gamma R h_E006 h_T005 h_T013 g f g f hg hf hg hf) 0
    change mul g g 0-mul f f 0=mul (g-f) g 0+mul f (g-f) 0 at he
    rw [he]
    apply lt_of_le_of_lt (norm_add_le _ _)
    apply lt_of_le_of_lt (add_le_add h1 h2)
    have hb := (@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 0 f (g-f) hf hgd).2
    have hb' : hn 0 g ≤ hn 0 f+hn 0 (g-f) := by simpa only [add_sub_cancel] using hb
    simpa only [one_mul] using hspec _ _ _ (hn0 _) (hn0 _) (hn0 _) hd hd hb')

theorem yui_aux_0030 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s r : ℝ, ∀ c : Coeff → ℂ, ∀ U : Coeff → Coeff, ∀ G : Coeff → Prop, (∀ f, MemH s f → G f → ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ g, MemH s g → G g → hn s (g-f)<δ → ‖c g-c f‖<ε) → ContinuousMapH s r U G → ContinuousMapH s r (fun f=>scale (c f) (U f)) G" := by
  exact (open KdVPlan in by
    intro s r c U G hc hU f hf hgf
    have hUf:=hU f hf hgf
    have hscale:=(@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 r).2.2.2
    have hsub:=(@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 r).2.2.1
    have hadd:=@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 r
    have hn0 : ∀ f : Coeff, 0≤hn r f := fun f=>Real.sqrt_nonneg _
    refine ⟨(hscale (c f) (U f) hUf.1).1, ?_⟩
    intro ε hε
    obtain ⟨δ,hδ,hspec⟩ := @yui_aux_0023 T gamma R h_E006 h_T005 h_T013 1 ‖c f‖ (hn r (U f)) ε (by norm_num) (norm_nonneg _) (hn0 _) hε
    obtain ⟨η,hη,hηspec⟩:=hc f hf hgf δ hδ
    obtain ⟨ζ,hζ,hζspec⟩:=hUf.2 δ hδ
    refine ⟨min η ζ,lt_min hη hζ,?_⟩
    intro g hg hgg hd
    have hUg:=(hU g hg hgg).1
    have hUd:=(hsub _ _ hUg hUf.1).1
    have hc':=hηspec g hg hgg (lt_of_lt_of_le hd (min_le_left _ _))
    have hu':=hζspec g hg hgg (lt_of_lt_of_le hd (min_le_right _ _))
    have he : scale (c g) (U g)-scale (c f) (U f)=scale (c g-c f) (U g)+scale (c f) (U g-U f) := by funext k; simp only [scale,Pi.sub_apply,Pi.add_apply]; ring
    rw [he]
    have hsum:=(hadd _ _ (hscale (c g-c f) _ hUg).1 (hscale (c f) _ hUd).1).2
    rw [(hscale (c g-c f) _ hUg).2,(hscale (c f) _ hUd).2] at hsum
    apply lt_of_le_of_lt hsum
    have hb:=(hadd (U f) (U g-U f) hUf.1 hUd).2
    have hb' : hn r (U g)≤hn r (U f)+hn r (U g-U f) := by simpa only [add_sub_cancel] using hb
    simpa only [one_mul] using hspec _ _ _ (norm_nonneg _) (hn0 _) (hn0 _) hc' hu' hb')

theorem yui_aux_0031 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ τ : ℝ, ContinuousMapH 0 1 (Htau τ) (fun _=>True)" := by
  exact (open KdVPlan in by
    intro τ
    have ops := @yui_aux_0021 T gamma R h_E006 h_T005 h_T013
    have comp := (@yui_aux_0019 T gamma R h_E006 h_T005 h_T013).1
    have post : ∀ A B : Coeff → Coeff, ContinuousMapH 0 1 A (fun _=>True) → ContinuousMapH 1 1 B (fun _=>True) → ContinuousMapH 0 1 (fun f=>B (A f)) (fun _=>True) := by
      intro A B hA hB
      exact comp 0 1 1 A B _ _ hA hB (by intros; trivial)
    have pr := @yui_aux_0024 T gamma R h_E006 h_T005 h_T013 0
    have addsub := @yui_aux_0020 T gamma R h_E006 h_T005 h_T013 0 1
    have hd := ops.2.2.2.2.2.2
    have hf := @yui_aux_0025 T gamma R h_E006 h_T005 h_T013 τ
    have inv1 := ops.2.2.2.2.2.1 1
    have sD : ∀ t : ℝ, ContinuousMapH 0 1 (fun f=>S t (invD f)) (fun _=>True) := fun t=>post _ _ hd (ops.2.2.1 1 t)
    have dF := post _ invD hf inv1
    have h1 := post _ (scale (1/3)) (post _ P (pr _ _ _ (sD τ) dF) (ops.2.2.2.1 1)) (ops.2.2.2.2.1 1 (1/3))
    have hmean : ∀ f, MemH 0 f → True → ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ g, MemH 0 g → True → hn 0 (g-f)<δ → ‖mul g g 0-mul f f 0‖<ε := by
      intro f hfm _ ε hε
      obtain ⟨δ,hδ,hδspec⟩:=@yui_aux_0029 T gamma R h_E006 h_T005 h_T013 f hfm ε hε
      exact ⟨δ,hδ,fun g hg _ hd=>hδspec g hg hd⟩
    have hm := @yui_aux_0030 T gamma R h_E006 h_T005 h_T013 0 1 (fun f=>mul f f 0) (fun f=>S τ (invD f)) (fun _=>True) hmean (sD τ)
    have h2raw:=post _ (scale ((τ:ℂ)/9)) hm (ops.2.2.2.2.1 1 ((τ:ℂ)/9))
    have h2 : ContinuousMapH 0 1 (fun f=>scale ((τ:ℂ)/9*mul f f 0) (S τ (invD f))) (fun _=>True) := by
      have he : (fun f=>scale ((τ:ℂ)/9) (scale (mul f f 0) (S τ (invD f)))) = (fun f=>scale ((τ:ℂ)/9*mul f f 0) (S τ (invD f))) := by funext f k; simp [scale,mul_assoc]
      rw [he] at h2raw
      exact h2raw
    have cu : ∀ t : ℝ, ContinuousMapH 0 1 (fun f=>invD (cube (S t (invD f)))) (fun _=>True) := by
      intro t
      exact post _ invD (pr _ _ _ (pr _ _ _ (sD t) (sD t)) (sD t)) inv1
    have h3 := post _ (scale (1/54)) (addsub _ _ _ (post _ (S (τ-τ)) (cu τ) (ops.2.2.1 1 (τ-τ))) (post _ (S (τ-0)) (cu 0) (ops.2.2.1 1 (τ-0)))).2 (ops.2.2.2.2.1 1 (1/54))
    have d2F := post _ invD dF inv1
    have d2 : ContinuousMapH 1 1 invD2 (fun _=>True) := comp 1 1 1 invD invD _ _ inv1 inv1 (by intros; trivial)
    have inn : ∀ t : ℝ, ContinuousMapH 0 1 (fun f=>S (τ-t) (invD2 (mul (S (t-τ) (invD2 (Ftau τ f))) (S t (invD f))))) (fun _=>True) := by
      intro t
      exact post _ (S (τ-t)) (post _ invD2 (pr _ _ _ (post _ (S (t-τ)) d2F (ops.2.2.1 1 (t-τ))) (sD t)) d2) (ops.2.2.1 1 (τ-t))
    have h4 := post _ (scale (1/(27*(τ:ℂ)))) (addsub _ _ _ (inn τ) (inn 0)).2 (ops.2.2.2.2.1 1 (1/(27*(τ:ℂ))))
    exact (addsub _ _ _ (addsub _ _ _ (addsub _ _ _ h1 h2).1 h3).2 h4).2)

theorem yui_aux_0032 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ τ : ℝ, ContinuousMapH 0 0 (psi τ) (fun _=>True)) ∧ (∀ τ : ℝ, ∀ n : ℕ, ContinuousMapH 0 0 (fun f=>numerical τ f n) (fun _=>True))" := by
  exact (open KdVPlan in by
    have ops:=@yui_aux_0021 T gamma R h_E006 h_T005 h_T013
    have comp:=(@yui_aux_0019 T gamma R h_E006 h_T005 h_T013).1
    have add:=@yui_aux_0020 T gamma R h_E006 h_T005 h_T013 0 0
    have hpsi : ∀ τ : ℝ, ContinuousMapH 0 0 (psi τ) (fun _=>True) := by
      intro τ
      have hF:=comp 0 1 0 (Ftau τ) id _ _ (@yui_aux_0025 T gamma R h_E006 h_T005 h_T013 τ) (ops.2.1 0 1 (by norm_num)) (by intros; trivial)
      have hH:=comp 0 1 0 (Htau τ) id _ _ (@yui_aux_0031 T gamma R h_E006 h_T005 h_T013 τ) (ops.2.1 0 1 (by norm_num)) (by intros; trivial)
      exact (add _ _ _ (add _ _ _ (ops.2.2.1 0 τ) hF).1 hH).1
    refine ⟨hpsi,?_⟩
    intro τ n
    induction n with
    | zero => exact ops.1 0
    | succ n ih =>
      have h:=comp 0 0 0 (fun f=>numerical τ f n) (psi τ) _ _ ih (hpsi τ) (by intros; trivial)
      simpa only [numerical,Function.iterate_succ_apply'] using h)

theorem yui_aux_0033 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ t : ℝ, ∀ k : ℤ, Complex.exp (Complex.I*(t*((-k:ℤ):ℝ)^3:ℝ))=star (Complex.exp (Complex.I*(t*(k:ℝ)^3:ℝ)))" := by
  intro t k
  change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp
  ring

theorem yui_aux_0034 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ t : ℝ, ∀ f : Coeff, RealField f → RealField (S t f)) ∧ (∀ f : Coeff, RealField f → RealField (invD f)) ∧ (∀ f : Coeff, RealField f → RealField (P f)) ∧ (∀ f g : Coeff, RealField f → RealField g → RealField (f+g) ∧ RealField (f-g)) ∧ (∀ c : ℂ, star c=c → ∀ f : Coeff, RealField f → RealField (scale c f))" := by
  exact (open KdVPlan in by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro t f hf k
      simp only [S,hf k,star_mul,@yui_aux_0033 T gamma R h_E006 h_T005 h_T013]
      exact mul_comm _ _
    · intro f hf k
      by_cases hk:k=0
      · simp [invD,hk]
      · simp [invD,hk,hf k,star_mul,Complex.star_def]
        ring
    · intro f hf k
      by_cases hk:k=0 <;> simp [P,hk,hf k]
    · intro f g hf hg
      constructor <;> intro k <;> simp only [Pi.add_apply,Pi.sub_apply,hf k,hg k,star_add,star_sub]
    · intro c hc f hf k
      simp only [scale,hf k,star_mul,hc]
      exact mul_comm _ _)

theorem yui_aux_0035 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f g : Coeff, RealField f → RealField g → RealField (mul f g)" := by
  exact (open KdVPlan in by
    intro f g hf hg k
    change (∑' j : ℤ, f j*g (-k-j)) = star (∑' j : ℤ,f j*g (k-j))
    rw [tsum_star,← (Equiv.neg ℤ).tsum_eq (fun j : ℤ=> f j*g (-k-j))]
    apply tsum_congr
    intro j
    change f (-j)*g (-k- -j)=star (f j*g (k-j))
    have he : -k- -j= -(k-j) := by omega
    rw [he,hf j,hg (k-j),star_mul]
    ring)

theorem yui_aux_0036 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ τ : ℝ, ∀ f : Coeff, RealField f → RealField (Ftau τ f) ∧ RealField (Htau τ f) ∧ RealField (psi τ f)) ∧ (∀ τ : ℝ, ∀ f : Coeff, ZeroMean (Ftau τ f) ∧ ZeroMean (Htau τ f) ∧ (ZeroMean f → ZeroMean (psi τ f)))" := by
  exact (open KdVPlan in by
    have ops:=@yui_aux_0034 T gamma R h_E006 h_T005 h_T013
    have hS:=ops.1
    have hI:=ops.2.1
    have hP:=ops.2.2.1
    have hA : ∀ f g, RealField f → RealField g → RealField (f+g) := fun f g hf hg=>(ops.2.2.2.1 f g hf hg).1
    have hSub : ∀ f g, RealField f → RealField g → RealField (f-g) := fun f g hf hg=>(ops.2.2.2.1 f g hf hg).2
    have hscale:=ops.2.2.2.2
    have hm:=@yui_aux_0035 T gamma R h_E006 h_T005 h_T013
    constructor
    · intro τ f hf
      have hr : star (mul f f 0)=mul f f 0 := by have hh:=hm f f hf hf 0; simpa using hh.symm
      have hF : RealField (Ftau τ f) := by
        unfold Ftau
        apply hSub
        · apply hscale _ (by simp); apply hP; apply hm <;> apply hS <;> apply hI <;> exact hf
        · apply hscale _ (by simp); apply hS; apply hP; apply hm <;> apply hI <;> exact hf
      have hH : RealField (Htau τ f) := by
        unfold Htau
        apply hSub
        · apply hSub
          · apply hA
            · apply hscale _ (by simp); apply hP; apply hm
              · exact hS τ _ (hI f hf)
              · exact hI _ hF
            · apply hscale _ (by simp [hr]); exact hS τ _ (hI f hf)
          · apply hscale _ (by simp); apply hSub
            · apply hS; apply hI; unfold cube; apply hm
              · apply hm <;> exact hS τ _ (hI f hf)
              · exact hS τ _ (hI f hf)
            · apply hS; apply hI; unfold cube; apply hm
              · apply hm <;> exact hS 0 _ (hI f hf)
              · exact hS 0 _ (hI f hf)
        · apply hscale _ (by simp); apply hSub
          · apply hS; unfold invD2; apply hI; apply hI; apply hm
            · apply hS; apply hI; apply hI; exact hF
            · exact hS τ _ (hI f hf)
          · apply hS; unfold invD2; apply hI; apply hI; apply hm
            · apply hS; apply hI; apply hI; exact hF
            · exact hS 0 _ (hI f hf)
      exact ⟨hF,hH,hA _ _ (hA _ _ (hS τ f hf) hF) hH⟩
    · intro τ f
      constructor
      · simp [ZeroMean,Ftau,scale,P,S]
      constructor
      · simp [ZeroMean,Htau,scale,P,S,invD,invD2]
      · intro hf
        simpa [ZeroMean,psi,Ftau,Htau,scale,P,S,invD,invD2] using hf)

theorem yui_aux_0037 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ s t : ℝ, ∀ f : Coeff, Data s f → Data s (S t f)) ∧ (∀ t : ℝ, ∀ f : Coeff, Smooth f → Smooth (S t f)) ∧ (∀ τ : ℝ, ∀ f : Coeff, Data 0 f → Data 0 (psi τ f)) ∧ (∀ τ : ℝ, ∀ f : Coeff, Data 0 f → ∀ n : ℕ, Data 0 (numerical τ f n) ∧ Data 0 (twistedNum τ f n))" := by
  exact (open KdVPlan in by
    have hS : ∀ s t : ℝ, ∀ f : Coeff, Data s f → Data s (S t f) := by
      intro s t f hf
      refine ⟨((@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).1 s t f hf.1).1,?_,(@yui_aux_0034 T gamma R h_E006 h_T005 h_T013).1 t f hf.2.2⟩
      simpa [ZeroMean,S] using hf.2.1
    have hpsi : ∀ τ : ℝ, ∀ f : Coeff, Data 0 f → Data 0 (psi τ f) := by
      intro τ f hf
      refine ⟨((@yui_aux_0032 T gamma R h_E006 h_T005 h_T013).1 τ f hf.1 trivial).1,((@yui_aux_0036 T gamma R h_E006 h_T005 h_T013).2 τ f).2.2 hf.2.1,((@yui_aux_0036 T gamma R h_E006 h_T005 h_T013).1 τ f hf.2.2).2.2⟩
    refine ⟨hS,?_,hpsi,?_⟩
    · intro t f hf m
      exact ((@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).1 (m:ℝ) t f (hf m)).1
    · intro τ f hf n
      have hn : ∀ n : ℕ, Data 0 (numerical τ f n) := by
        intro n
        induction n with
        | zero => exact hf
        | succ n ih => rw [(@yui_aux_0011 T gamma R h_E006 h_T005 h_T013).2.2]; exact hpsi τ _ ih
      exact ⟨hn n,hS 0 _ _ (hn n)⟩)

theorem yui_aux_0038 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ m : ℕ, ∀ f : Coeff, (MemH (m:ℝ) f ∧ MemH (m:ℝ) (fun k : ℤ=>(k:ℂ)*f k)) ↔ MemH ((m:ℝ)+1) f" := by
  exact (open KdVPlan in by
    intro m f
    have he : (fun k : ℤ=>weight ((m:ℝ)+1) k*‖f k‖^2)=(fun k : ℤ=>weight (m:ℝ) k*‖f k‖^2)+(fun k : ℤ=>weight (m:ℝ) k*‖(k:ℂ)*f k‖^2) := by
      funext k
      simp only [weight,Real.rpow_add (by positivity : (0:ℝ)<1+(k:ℝ)^2),Real.rpow_one,norm_mul,mul_pow,Pi.add_apply]
      have hn : ‖(k:ℂ)‖^2=(k:ℝ)^2 := by simp [Complex.norm_intCast,Int.cast_abs,sq_abs]
      rw [hn]
      ring
    constructor
    · rintro ⟨hf,hg⟩
      change Summable _
      rw [he]
      exact hf.add hg
    · intro hf
      have hw : ∀ k : ℤ, 0≤weight (m:ℝ) k := fun k=>Real.rpow_nonneg (by positivity) _
      change Summable _ at hf
      rw [he] at hf
      have hf' : Summable (fun k : ℤ=>weight (m:ℝ) k*‖f k‖^2) := Summable.of_nonneg_of_le (fun k=>mul_nonneg (hw k) (sq_nonneg _)) (fun k=>by dsimp only [Pi.add_apply]; exact le_add_of_nonneg_right (mul_nonneg (hw k) (sq_nonneg _))) hf
      have hg' : Summable (fun k : ℤ=>weight (m:ℝ) k*‖(k:ℂ)*f k‖^2) := Summable.of_nonneg_of_le (fun k=>mul_nonneg (hw k) (sq_nonneg _)) (fun k=>by dsimp only [Pi.add_apply]; exact le_add_of_nonneg_left (mul_nonneg (hw k) (sq_nonneg _))) hf
      exact ⟨hf',hg'⟩)

theorem yui_aux_0039 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ f : Coeff, Smooth f → Smooth (fun k : ℤ=>(k:ℂ)*f k)) ∧ (∀ f : Coeff, Smooth f → ∀ n : ℕ, Smooth (fun k : ℤ=>(k:ℂ)^n*f k)) ∧ (∀ f : Coeff, (∀ n : ℕ, MemH 0 (fun k : ℤ=>(k:ℂ)^n*f k)) → Smooth f)" := by
  exact (open KdVPlan in by
    have shift : ∀ f : Coeff, Smooth f → Smooth (fun k : ℤ=>(k:ℂ)*f k) := by
      intro f hf m
      have hm : MemH ((m:ℝ)+1) f := by simpa only [Nat.cast_add,Nat.cast_one] using hf (m+1)
      exact (((@yui_aux_0038 T gamma R h_E006 h_T005 h_T013) m f).mpr hm).2
    refine ⟨shift,?_,?_⟩
    · intro f hf n
      induction n with
      | zero => simpa using hf
      | succ n ih =>
        have h:=shift _ ih
        have he : (fun k : ℤ=>(k:ℂ)*((k:ℂ)^n*f k))=(fun k : ℤ=>(k:ℂ)^(n+1)*f k) := by funext k; ring
        rw [he] at h
        exact h
    · intro f hf m
      induction m generalizing f with
      | zero => simpa using hf 0
      | succ m ih =>
        have hg : ∀ n : ℕ, MemH 0 (fun k : ℤ=>(k:ℂ)^n*((k:ℂ)*f k)) := by
          intro n
          have he : (fun k : ℤ=>(k:ℂ)^n*((k:ℂ)*f k))=(fun k : ℤ=>(k:ℂ)^(n+1)*f k) := by funext k; ring
          rw [he]
          exact hf (n+1)
        have h := ((@yui_aux_0038 T gamma R h_E006 h_T005 h_T013) m f).mp ⟨ih f hf,ih (fun k : ℤ=>(k:ℂ)*f k) hg⟩
        simpa only [Nat.cast_add,Nat.cast_one] using h)

theorem yui_aux_0040 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f : Coeff, Smooth f → MemH 0 f ∧ MemH 1 f" := by
  exact (open KdVPlan in by
    intro f hf
    constructor
    · simpa using hf 0
    · simpa using hf 1)

theorem yui_aux_0041 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f g : Coeff, Smooth f → Smooth g → (fun k : ℤ=>(k:ℂ)*mul f g k)=mul (fun k : ℤ=>(k:ℂ)*f k) g+mul f (fun k : ℤ=>(k:ℂ)*g k)" := by
  exact (open KdVPlan in by
    intro f g hf hg
    have hs:=@yui_aux_0014 T gamma R h_E006 h_T005 h_T013
    have sh:=(@yui_aux_0039 T gamma R h_E006 h_T005 h_T013).1
    have h00 := @yui_aux_0040 T gamma R h_E006 h_T005 h_T013
    have hfs : MemH 0 (fun k : ℤ=>(k:ℂ)*f k) := (h00 _ (sh f hf)).1
    have hgs : MemH 0 (fun k : ℤ=>(k:ℂ)*g k) := (h00 _ (sh g hg)).1
    have hf0 : MemH 0 f := (h00 f hf).1
    have hg0 : MemH 0 g := (h00 g hg).1
    funext k
    change (k:ℂ)*(∑' j : ℤ,f j*g (k-j))=(∑' j : ℤ,((j:ℂ)*f j)*g (k-j))+(∑' j : ℤ,f j*(((k-j:ℤ):ℂ)*g (k-j)))
    rw [← tsum_mul_left,← (hs (fun k : ℤ=>(k:ℂ)*f k) g hfs hg0 k).tsum_add (hs f (fun k : ℤ=>(k:ℂ)*g k) hf0 hgs k)]
    apply tsum_congr
    intro j
    push_cast
    ring)

theorem yui_aux_0042 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f g : Coeff, Smooth f → Smooth g → Smooth (mul f g)" := by
  exact (open KdVPlan in by
    obtain ⟨C,hC,hi,hm⟩ := @yui_aux_0017 T gamma R h_E006 h_T005 h_T013
    have h00:=@yui_aux_0040 T gamma R h_E006 h_T005 h_T013
    have sh:=(@yui_aux_0039 T gamma R h_E006 h_T005 h_T013).1
    have hmoment : ∀ n : ℕ, ∀ f g : Coeff, Smooth f → Smooth g → MemH 1 (fun k : ℤ=>(k:ℂ)^n*mul f g k) := by
      intro n
      induction n with
      | zero =>
        intro f g hf hg
        simpa using (hm f g (h00 f hf).2 (h00 g hg).2).1
      | succ n ih =>
        intro f g hf hg
        have h1:=ih (fun k : ℤ=>(k:ℂ)*f k) g (sh f hf) hg
        have h2:=ih f (fun k : ℤ=>(k:ℂ)*g k) hf (sh g hg)
        have hsum:=(@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 1 _ _ h1 h2).1
        have he : (fun k : ℤ=>(k:ℂ)^(n+1)*mul f g k)=(fun k : ℤ=>(k:ℂ)^n*mul (fun k : ℤ=>(k:ℂ)*f k) g k)+(fun k : ℤ=>(k:ℂ)^n*mul f (fun k : ℤ=>(k:ℂ)*g k) k) := by
          funext k
          have hk:=congrFun (@yui_aux_0041 T gamma R h_E006 h_T005 h_T013 f g hf hg) k
          change (k:ℂ)*mul f g k=mul (fun k : ℤ=>(k:ℂ)*f k) g k+mul f (fun k : ℤ=>(k:ℂ)*g k) k at hk
          change (k:ℂ)^(n+1)*mul f g k=(k:ℂ)^n*mul (fun k : ℤ=>(k:ℂ)*f k) g k+(k:ℂ)^n*mul f (fun k : ℤ=>(k:ℂ)*g k) k
          calc
            _ = (k:ℂ)^n*((k:ℂ)*mul f g k) := by ring
            _ = _ := by rw [hk]; ring
        rw [he]
        exact hsum
    intro f g hf hg
    apply (@yui_aux_0039 T gamma R h_E006 h_T005 h_T013).2.2
    intro n
    exact (h_T013.2.2.2.1 0 1 _ (by norm_num) (hmoment n f g hf hg)).1)

theorem yui_aux_0043 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ f : Coeff, Smooth f → Smooth (invD f)) ∧ (∀ f : Coeff, Smooth f → Smooth (P f)) ∧ (∀ c : ℂ, ∀ f : Coeff, Smooth f → Smooth (scale c f)) ∧ (∀ f g : Coeff, Smooth f → Smooth g → Smooth (f+g) ∧ Smooth (f-g))" := by
  exact (open KdVPlan in by
    refine ⟨?_,?_,?_,?_⟩
    · intro f hf m
      exact ((@yui_aux_0016 T gamma R h_E006 h_T005 h_T013).1 (m:ℝ) f (hf m)).1
    · intro f hf m
      exact ((@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).2.1 (m:ℝ) f (hf m)).1
    · intro c f hf m
      exact ((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 (m:ℝ)).2.2.2 c f (hf m)).1
    · intro f g hf hg
      constructor
      · intro m; exact (@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 (m:ℝ) f g (hf m) (hg m)).1
      · intro m; exact ((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 (m:ℝ)).2.2.1 f g (hf m) (hg m)).1)

theorem yui_aux_0044 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ τ : ℝ, ∀ f : Coeff, Smooth f → Smooth (Ftau τ f) ∧ Smooth (Htau τ f) ∧ Smooth (psi τ f)) ∧ (∀ τ : ℝ, ∀ f : Coeff, Smooth f → ∀ n : ℕ, Smooth (numerical τ f n) ∧ Smooth (twistedNum τ f n))" := by
  exact (open KdVPlan in by
    have ops:=@yui_aux_0043 T gamma R h_E006 h_T005 h_T013
    have hS:=(@yui_aux_0037 T gamma R h_E006 h_T005 h_T013).2.1
    have hI:=ops.1
    have hP:=ops.2.1
    have hScale:=ops.2.2.1
    have hA : ∀ f g, Smooth f → Smooth g → Smooth (f+g) := fun f g hf hg=>(ops.2.2.2 f g hf hg).1
    have hSub : ∀ f g, Smooth f → Smooth g → Smooth (f-g) := fun f g hf hg=>(ops.2.2.2 f g hf hg).2
    have hm:=@yui_aux_0042 T gamma R h_E006 h_T005 h_T013
    have hup : ∀ τ : ℝ, ∀ f : Coeff, Smooth f → Smooth (Ftau τ f) ∧ Smooth (Htau τ f) ∧ Smooth (psi τ f) := by
      intro τ f hf
      have hF : Smooth (Ftau τ f) := by
        unfold Ftau
        apply hSub
        · apply hScale; apply hP; apply hm <;> apply hS <;> apply hI <;> exact hf
        · apply hScale; apply hS; apply hP; apply hm <;> apply hI <;> exact hf
      have hH : Smooth (Htau τ f) := by
        unfold Htau
        apply hSub
        · apply hSub
          · apply hA
            · apply hScale; apply hP; apply hm
              · exact hS τ _ (hI f hf)
              · exact hI _ hF
            · apply hScale; exact hS τ _ (hI f hf)
          · apply hScale; apply hSub
            · apply hS; apply hI; unfold cube; apply hm
              · apply hm <;> exact hS τ _ (hI f hf)
              · exact hS τ _ (hI f hf)
            · apply hS; apply hI; unfold cube; apply hm
              · apply hm <;> exact hS 0 _ (hI f hf)
              · exact hS 0 _ (hI f hf)
        · apply hScale; apply hSub
          · apply hS; unfold invD2; apply hI; apply hI; apply hm
            · apply hS; apply hI; apply hI; exact hF
            · exact hS τ _ (hI f hf)
          · apply hS; unfold invD2; apply hI; apply hI; apply hm
            · apply hS; apply hI; apply hI; exact hF
            · exact hS 0 _ (hI f hf)
      exact ⟨hF,hH,hA _ _ (hA _ _ (hS τ f hf) hF) hH⟩
    refine ⟨hup,?_⟩
    intro τ f hf n
    have hn : ∀ n : ℕ, Smooth (numerical τ f n) := by
      intro n
      induction n with
      | zero => exact hf
      | succ n ih => rw [(@yui_aux_0011 T gamma R h_E006 h_T005 h_T013).2.2]; exact (hup τ _ ih).2.2
    exact ⟨hn n,hS _ _ (hn n)⟩)

theorem yui_aux_0045 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ τ : ℝ, ∀ f : Coeff, ∀ n : ℕ, 0<τ → Data 0 f → Smooth f → Vst ((n:ℝ)*τ) τ (twistedNum τ f n) ((n:ℝ)*τ)=twistedNum τ f n ∧ Vst ((n:ℝ)*τ) τ (twistedNum τ f n) (((n:ℝ)+1)*τ)=twistedNum τ f (n+1)" := by
  exact (open KdVPlan in by
    intro τ f n hτ hf hsm
    refine ⟨(@yui_aux_0010 T gamma R h_E006 h_T005 h_T013).1 _ _ _, ?_⟩
    have hdata:=((@yui_aux_0037 T gamma R h_E006 h_T005 h_T013).2.2.2 τ f hf n).2
    have hsmooth:=((@yui_aux_0044 T gamma R h_E006 h_T005 h_T013).2 τ f hsm n).2
    rw [@yui_aux_0012 T gamma R h_E006 h_T005 h_T013 τ hτ n _ hdata hsmooth]
    have he : S ((n:ℝ)*τ) (twistedNum τ f n)=numerical τ f n := by
      unfold twistedNum
      rw [(@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).2.2.1]
      have ht : (n:ℝ)*τ+ -(n:ℝ)*τ=0 := by ring
      rw [ht,(@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).2.2.2]
    rw [he]
    simp only [twistedNum,(@yui_aux_0011 T gamma R h_E006 h_T005 h_T013).2.2,Nat.cast_add,Nat.cast_one,neg_add_rev,neg_mul])

theorem yui_aux_0046 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ s : ℝ, Function.Injective (FromLP s)) ∧ (∀ s : ℝ, ∀ x y : lp (fun _ : ℤ=>ℂ) 2, FromLP s (x+y)=FromLP s x+FromLP s y ∧ FromLP s (x-y)=FromLP s x-FromLP s y) ∧ (∀ s : ℝ, ∀ c : ℂ, ∀ x : lp (fun _ : ℤ=>ℂ) 2, FromLP s (c•x)=scale c (FromLP s x)) ∧ ∃ Q : Coeff → lp (fun _ : ℤ=>ℂ) 2, ∀ f : Coeff, MemH 1 f → FromLP 1 (Q f)=f" := by
  exact (open KdVPlan in by
    have hadd : ∀ s : ℝ, ∀ x y : lp (fun _ : ℤ=>ℂ) 2, FromLP s (x+y)=FromLP s x+FromLP s y := by intro s x y; funext k; simp [FromLP,mul_add]
    have hsub : ∀ s : ℝ, ∀ x y : lp (fun _ : ℤ=>ℂ) 2, FromLP s (x-y)=FromLP s x-FromLP s y := by intro s x y; funext k; simp [FromLP,mul_sub]
    refine ⟨?_,fun s x y=>⟨hadd s x y,hsub s x y⟩,?_,?_⟩
    · intro s x y hxy
      have he : FromLP s (x-y)=0 := by rw [hsub,hxy,sub_self]
      have hn := h_T013.2.1 s (x-y)
      rw [he,(@yui_aux_0001 T gamma R h_E006 h_T005 h_T013 s).2] at hn
      exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)
    · intro s c x; funext k; simp [FromLP,scale,mul_left_comm]
    · classical
      let Q : Coeff → lp (fun _ : ℤ=>ℂ) 2 := fun f=>if hf:MemH 1 f then Classical.choose ((h_T013.1 1 f).mp hf) else 0
      refine ⟨Q,?_⟩
      intro f hf
      dsimp only [Q]
      rw [dif_pos hf]
      exact (Classical.choose_spec ((h_T013.1 1 f).mp hf)).symm)

theorem yui_aux_0047 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ a b : ℝ, ∀ f : ℝ → ℂ, (∫ t in a..b, star (f t))=star (∫ t in a..b, f t)" := by
  intro a b f
  simp only [intervalIntegral,star_sub]
  change (∫ t in Set.Ioc a b, (starRingEnd ℂ) (f t))-(∫ t in Set.Ioc b a, (starRingEnd ℂ) (f t))=(starRingEnd ℂ) (∫ t in Set.Ioc a b,f t)-(starRingEnd ℂ) (∫ t in Set.Ioc b a,f t)
  rw [integral_conj,integral_conj]

theorem yui_aux_0048 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ f : Coeff, RealField f → RealField (dx f)) ∧ (∀ t : ℝ, ∀ f g : Coeff, RealField f → RealField g → RealField (B t f g) ∧ ZeroMean (B t f g)) ∧ (∀ a b : ℝ, ∀ f : Path, (∀ t, RealField (f t)) → RealField (timeInt a b f)) ∧ (∀ a b : ℝ, ∀ f : Path, (∀ t, ZeroMean (f t)) → ZeroMean (timeInt a b f))" := by
  exact (open KdVPlan in by
    have hdx : ∀ f : Coeff, RealField f → RealField (dx f) := by
      intro f hf k
      simp [dx,hf k,star_mul]
      ring
    have hS:=(@yui_aux_0034 T gamma R h_E006 h_T005 h_T013).1
    refine ⟨hdx,?_,?_,?_⟩
    · intro t f g hf hg
      constructor
      · exact hS (-t) _ (hdx _ (@yui_aux_0035 T gamma R h_E006 h_T005 h_T013 _ _ (hS t f hf) (hS t g hg)))
      · simp [ZeroMean,B,S,dx]
    · intro a b f hf k
      change (∫ t in a..b,f t (-k))=star (∫ t in a..b,f t k)
      have he : (fun t=>f t (-k))=(fun t=>star (f t k)) := funext (fun t=>hf t k)
      rw [he,@yui_aux_0047 T gamma R h_E006 h_T005 h_T013]
    · intro a b f hf
      have he : (fun t=>f t 0)=(fun _=>0) := funext (fun t=>hf t)
      change (∫ t in a..b,f t 0)=0
      rw [he]
      simp)

theorem yui_aux_0049 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ a : ℝ, ∀ f : Coeff, RealField f → ∀ t : ℝ, (ZeroMean (F a f t) ∧ RealField (F a f t)) ∧ (ZeroMean (Cst a f t) ∧ RealField (Cst a f t)) ∧ (ZeroMean (Qst a f t) ∧ RealField (Qst a f t))" := by
  exact (open KdVPlan in by
    intro a f hf
    have ops:=@yui_aux_0048 T gamma R h_E006 h_T005 h_T013
    have rscale:=(@yui_aux_0034 T gamma R h_E006 h_T005 h_T013).2.2.2.2
    have hF : ∀ t, ZeroMean (F a f t) ∧ RealField (F a f t) := by
      intro t
      constructor
      · simp [ZeroMean,F,stage,timeInt,scale,B,S,dx]
      · apply rscale _ (by simp)
        apply ops.2.2.1
        intro r
        exact (ops.2.1 r f f hf hf).1
    intro t
    refine ⟨hF t,⟨?_,?_⟩,⟨?_,?_⟩⟩
    · simp [ZeroMean,Cst,timeInt,B,S,dx]
    · apply ops.2.2.1
      intro r
      exact (ops.2.1 r f (F a f r) hf (hF r).2).1
    · simp [ZeroMean,Qst,timeInt,scale,B,S,dx]
    · apply rscale _ (by simp)
      apply ops.2.2.1
      intro r
      exact (ops.2.1 r _ _ (hF r).2 (hF r).2).1)

theorem yui_aux_0050 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ τ : ℝ, 0<τ → ∀ n : ℕ, ∀ f : Coeff, Data 0 f → Smooth f → ∀ t : ℝ, ZeroMean (Vst ((n:ℝ)*τ) τ f t) ∧ RealField (Vst ((n:ℝ)*τ) τ f t)) ∧ (∀ τ : ℝ, 0<τ → ∀ f : Coeff, Data 0 f → Smooth f → ∀ H : ℝ, RealPath 0 H (interp τ f))" := by
  exact (open KdVPlan in by
    have ops:=@yui_aux_0034 T gamma R h_E006 h_T005 h_T013
    have hA : ∀ f g, RealField f → RealField g → RealField (f+g) := fun f g hf hg=>(ops.2.2.2.1 f g hf hg).1
    have hSub : ∀ f g, RealField f → RealField g → RealField (f-g) := fun f g hf hg=>(ops.2.2.2.1 f g hf hg).2
    have hp : ∀ τ : ℝ, 0<τ → ∀ n : ℕ, ∀ f : Coeff, Data 0 f → Smooth f → ∀ t : ℝ, ZeroMean (Vst ((n:ℝ)*τ) τ f t) ∧ RealField (Vst ((n:ℝ)*τ) τ f t) := by
      intro τ hτ n f hf hsm t
      let a : ℝ:=(n:ℝ)*τ
      have hst:=@yui_aux_0049 T gamma R h_E006 h_T005 h_T013 a f hf.2.2
      have hr : RealField (rem a τ f f f) := by
        have he:=h_E006 τ hτ n f hf hsm
        have hre : rem a τ f f f=f+F a f (((n:ℝ)+1)*τ)+Cst a f (((n:ℝ)+1)*τ)-S (-((n:ℝ)+1)*τ) (psi τ (S a f)) := by rw [he]; change rem a τ f f f = f+F a f (((n:ℝ)+1)*τ)+Cst a f (((n:ℝ)+1)*τ)-(f+F a f (((n:ℝ)+1)*τ)+Cst a f (((n:ℝ)+1)*τ)-rem a τ f f f); abel
        rw [hre]
        apply hSub
        · exact hA _ _ (hA _ _ hf.2.2 (hst _).1.2) (hst _).2.1.2
        · apply ops.1
          exact ((@yui_aux_0036 T gamma R h_E006 h_T005 h_T013).1 τ _ (ops.1 a f hf.2.2)).2.2
      have hw : RealField (Wst a τ f) := hA _ _ (hst (a+τ)).2.2.2 hr
      constructor
      · change ZeroMean (Vst a τ f t)
        have hf0:=hf.2.1
        simp only [ZeroMean] at hf0 ⊢
        simp [Vst,scale,Wst,F,stage,Cst,Qst,timeInt,B,S,dx,rem,remWith,hf0]
      · change RealField (Vst a τ f t)
        unfold Vst
        apply hSub
        · exact hA _ _ (hA _ _ (hA _ _ hf.2.2 (hst t).1.2) (hst t).2.1.2) (hst t).2.2.2
        · exact ops.2.2.2.2 _ (by simp) _ hw
    refine ⟨hp,?_⟩
    intro τ hτ f hf hsm H t ht
    exact hp τ hτ (gridIndex τ t) (twistedNum τ f (gridIndex τ t)) (((@yui_aux_0037 T gamma R h_E006 h_T005 h_T013).2.2.2 τ f hf _).2) (((@yui_aux_0044 T gamma R h_E006 h_T005 h_T013).2 τ f hsm _).2) t)

theorem yui_aux_0051 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E], ∀ (ι : Type) (ev : ι → E →L[ℝ] ℂ), (∀ x y : E, (∀ i, ev i x=ev i y) → x=y) → ∀ u du : ℝ → E, Continuous du → (∀ i t, HasDerivAt (fun r=>ev i (u r)) (ev i (du t)) t) → ∀ t, HasDerivAt u (du t) t" := by
  intro E _ _ _ ι ev hsep u du hdu hd
  have he : u=(fun r=>u 0+∫ x in (0:ℝ)..r, du x) := by
    funext r
    apply hsep
    intro i
    have hint : IntervalIntegrable du volume 0 r := hdu.intervalIntegrable _ _
    have hscalar : IntervalIntegrable (fun x=>ev i (du x)) volume 0 r := ((ev i).continuous.comp hdu).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>hd i x) hscalar
    rw [map_add,← (ev i).intervalIntegral_comp_comm hint,hftc]
    abel
  intro t
  rw [he]
  have hint : IntervalIntegrable du volume 0 t := hdu.intervalIntegrable _ _
  exact (intervalIntegral.integral_hasDerivAt_right hint (hdu.stronglyMeasurableAtFilter _ _) hdu.continuousAt).const_add (u 0)

theorem yui_aux_0052 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ j : ℕ, (j:WithTop ℕ∞) < ((⊤:ℕ∞):WithTop ℕ∞)" := by
  intro j
  exact_mod_cast ENat.coe_lt_top j

theorem yui_aux_0053 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E], ∀ (ι : Type) (ev : ι → E →L[ℝ] ℂ), (∀ x y : E, (∀ i, ev i x=ev i y) → x=y) → ∀ φ : ι → ℝ → ℂ, (∀ i, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (φ i)) → ∀ u : ℕ → ℝ → E, (∀ j, Continuous (u j)) → (∀ j i t, ev i (u j t)=iteratedDeriv j (φ i) t) → ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (u 0)" := by
  intro E _ _ _ ι ev hsep φ hφ u hu he
  have hstep : ∀ j t, HasDerivAt (u j) (u (j+1) t) t := by
    intro j
    apply @yui_aux_0051 T gamma R h_E006 h_T005 h_T013 E _ _ _ ι ev hsep (u j) (u (j+1)) (hu (j+1))
    intro i t
    have hi := ((hφ i).differentiable_iteratedDeriv j (@yui_aux_0052 T gamma R h_E006 h_T005 h_T013 j)).differentiableAt.hasDerivAt (x:=t)
    have h0 : (fun r=>ev i (u j r))=iteratedDeriv j (φ i) := funext (he j i)
    rw [h0,he (j+1) i t,iteratedDeriv_succ]
    exact hi
  have hiter : ∀ j, iteratedDeriv j (u 0)=u j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iteratedDeriv_succ,ih]
      exact funext (fun t=>(hstep j t).deriv)
  apply contDiff_of_differentiable_iteratedDeriv (n:=(⊤:ℕ∞))
  intro j hj
  rw [hiter j]
  exact fun t=>(hstep j t).differentiableAt

theorem yui_aux_0054 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∃ ev : ℤ → (lp (fun _ : ℤ=>ℂ) 2) →L[ℝ] ℂ, (∀ k x, ev k x=FromLP 1 x k) ∧ (∀ x y, (∀ k, ev k x=ev k y) → x=y)" := by
  exact (open KdVPlan in by
    let ev : ℤ → (lp (fun _ : ℤ=>ℂ) 2) →L[ℝ] ℂ := fun k=>(((weight (-1/2) k:ℂ) • lp.evalCLM ℂ (fun _ : ℤ=>ℂ) 2 k).restrictScalars ℝ)
    have hev : ∀ k x, ev k x=FromLP 1 x k := by intro k x; rfl
    refine ⟨ev,hev,?_⟩
    intro x y hxy
    apply (@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).1 1
    funext k
    rw [← hev,← hev]
    exact hxy k)

theorem yui_aux_0055 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s : ℝ, ∀ x y : lp (fun _ : ℤ=>ℂ) 2, MemH s (FromLP s x) ∧ hn s (FromLP s x-FromLP s y)=‖x-y‖" := by
  exact (open KdVPlan in by
    intro s x y
    refine ⟨(h_T013.1 s _).mpr ⟨x,rfl⟩,?_⟩
    rw [← ((@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.1 s x y).2]
    exact h_T013.2.1 s (x-y))

theorem yui_aux_0056 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ Q : Coeff → lp (fun _ : ℤ=>ℂ) 2, (∀ f : Coeff, MemH 1 f → FromLP 1 (Q f)=f) → ∀ f g : Coeff, MemH 1 f → MemH 1 g → hn 1 (f-g)=‖Q f-Q g‖" := by
  exact (open KdVPlan in by
    intro Q hQ f g hf hg
    calc
      hn 1 (f-g)=hn 1 (FromLP 1 (Q f)-FromLP 1 (Q g)) := by rw [hQ f hf,hQ g hg]
      _ = ‖Q f-Q g‖ := (@yui_aux_0055 T gamma R h_E006 h_T005 h_T013 1 _ _).2)

theorem yui_aux_0057 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f : Path, (∃ u : ℝ → lp (fun _ : ℤ=>ℂ) 2, Continuous u ∧ ∀ t, FromLP 1 (u t)=f t) ↔ (∀ t, MemH 1 (f t)) ∧ ∀ t ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ r : ℝ, |r-t|<δ → hn 1 (f r-f t)<ε" := by
  exact (open KdVPlan in by
    intro f
    have normdiff:=@yui_aux_0055 T gamma R h_E006 h_T005 h_T013 1
    constructor
    · rintro ⟨u,hu,he⟩
      refine ⟨fun t=>he t ▸ (normdiff (u t) (u t)).1,?_⟩
      intro t ε hε
      obtain ⟨δ,hδ,hspec⟩:=(Metric.continuousAt_iff.mp hu.continuousAt) ε hε
      refine ⟨δ,hδ,?_⟩
      intro r hdr
      rw [← he r,← he t,(normdiff (u r) (u t)).2]
      simpa only [dist_eq_norm,Real.norm_eq_abs] using hspec (by simpa only [Real.dist_eq] using hdr)
    · rintro ⟨hm,hc⟩
      obtain ⟨Q,hQ⟩:=(@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.2.2
      refine ⟨fun t=>Q (f t),?_,fun t=>hQ (f t) (hm t)⟩
      apply continuous_iff_continuousAt.mpr
      intro t
      apply Metric.continuousAt_iff.mpr
      intro ε hε
      obtain ⟨δ,hδ,hspec⟩:=hc t ε hε
      refine ⟨δ,hδ,?_⟩
      intro r hdr
      have hd : hn 1 (f r-f t)=‖Q (f r)-Q (f t)‖ := @yui_aux_0056 T gamma R h_E006 h_T005 h_T013 Q hQ (f r) (f t) (hm r) (hm t)
      rw [dist_eq_norm,← hd]
      exact hspec r (by simpa only [Real.dist_eq] using hdr))

theorem yui_aux_0058 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ s t : ℝ, ∀ f : Coeff, MemH s f → Continuous (fun r : ℝ=>hn s (S r f-S t f))" := by
  exact (open KdVPlan in by
    intro s t f hf
    have hw : ∀ k : ℤ, 0≤weight s k := fun k=>Real.rpow_nonneg (by positivity) _
    have hcoef : ∀ r : ℝ, ∀ k : ℤ, ‖S r f k‖=‖f k‖ := by intro r k; simp only [S,norm_mul,@yui_aux_0007 T gamma R h_E006 h_T005 h_T013,one_mul]
    have hc : ∀ k : ℤ, Continuous (fun r : ℝ=>weight s k*‖S r f k-S t f k‖^2) := by
      intro k
      unfold S
      fun_prop
    have hs : Summable (fun k : ℤ=>4*(weight s k*‖f k‖^2)) := hf.mul_left _
    have hb : ∀ k : ℤ, ∀ r : ℝ, ‖weight s k*‖S r f k-S t f k‖^2‖ ≤4*(weight s k*‖f k‖^2) := by
      intro k r
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw k) (sq_nonneg _))]
      have hn : ‖S r f k-S t f k‖ ≤ 2*‖f k‖ := by simpa [hcoef,two_mul] using norm_sub_le (S r f k) (S t f k)
      have hn2 : ‖S r f k-S t f k‖^2≤4*‖f k‖^2 := by nlinarith [norm_nonneg (S r f k-S t f k)]
      nlinarith [mul_le_mul_of_nonneg_left hn2 (hw k)]
    have hsum : Continuous (fun r : ℝ=>∑' k : ℤ,weight s k*‖S r f k-S t f k‖^2) := continuous_tsum hc hs hb
    exact Real.continuous_sqrt.comp hsum)

theorem yui_aux_0059 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in (∀ f f' g : Coeff, MemH 0 f → MemH 0 f' → MemH 0 g → mul (f+f') g=mul f g+mul f' g) ∧ (∀ f g g' : Coeff, MemH 0 f → MemH 0 g → MemH 0 g' → mul f (g+g')=mul f g+mul f g') ∧ (∀ c : ℂ, ∀ f g : Coeff, mul (scale c f) g=scale c (mul f g) ∧ mul f (scale c g)=scale c (mul f g))" := by
  exact (open KdVPlan in by
    have hs:=@yui_aux_0014 T gamma R h_E006 h_T005 h_T013
    refine ⟨?_,?_,?_⟩
    · intro f f' g hf hf' hg
      funext k
      change (∑' j : ℤ, (f j+f' j)*g (k-j))=(∑' j : ℤ,f j*g (k-j))+(∑' j : ℤ,f' j*g (k-j))
      simp only [add_mul]
      exact (hs f g hf hg k).tsum_add (hs f' g hf' hg k)
    · intro f g g' hf hg hg'
      funext k
      change (∑' j : ℤ, f j*(g (k-j)+g' (k-j)))=(∑' j : ℤ,f j*g (k-j))+(∑' j : ℤ,f j*g' (k-j))
      simp only [mul_add]
      exact (hs f g hf hg k).tsum_add (hs f g' hf hg' k)
    · intro c f g
      constructor
      · funext k
        change (∑' j : ℤ,(c*f j)*g (k-j))=c*(∑' j : ℤ,f j*g (k-j))
        simp only [mul_assoc,tsum_mul_left]
      · funext k
        change (∑' j : ℤ,f j*(c*g (k-j)))=c*(∑' j : ℤ,f j*g (k-j))
        simp only [mul_left_comm (f _ ) c,tsum_mul_left])

theorem yui_aux_0060 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∃ B : (lp (fun _ : ℤ=>ℂ) 2) →L[ℝ] (lp (fun _ : ℤ=>ℂ) 2) →L[ℝ] (lp (fun _ : ℤ=>ℂ) 2), ∀ x y, FromLP 1 (B x y)=mul (FromLP 1 x) (FromLP 1 y)" := by
  exact (open KdVPlan in by
    obtain ⟨C,hC,hi,hm⟩:=@yui_aux_0017 T gamma R h_E006 h_T005 h_T013
    have rep:=@yui_aux_0046 T gamma R h_E006 h_T005 h_T013
    obtain ⟨Q,hQ⟩:=rep.2.2.2
    have linj:=rep.1 1
    have ladd : ∀ x y : lp (fun _ : ℤ=>ℂ) 2, FromLP 1 (x+y)=FromLP 1 x+FromLP 1 y := fun x y=>(rep.2.1 1 x y).1
    have lsmul:=rep.2.2.1 1
    have mem1 : ∀ x : lp (fun _ : ℤ=>ℂ) 2, MemH 1 (FromLP 1 x) := fun x=>(h_T013.1 1 _).mpr ⟨x,rfl⟩
    have mem0 : ∀ x : lp (fun _ : ℤ=>ℂ) 2, MemH 0 (FromLP 1 x) := fun x=>(h_T013.2.2.2.1 0 1 _ (by norm_num) (mem1 x)).1
    let B : (lp (fun _ : ℤ=>ℂ) 2) → (lp (fun _ : ℤ=>ℂ) 2) → (lp (fun _ : ℤ=>ℂ) 2) := fun x y=>Q (mul (FromLP 1 x) (FromLP 1 y))
    have hB : ∀ x y, FromLP 1 (B x y)=mul (FromLP 1 x) (FromLP 1 y) := by intro x y; exact hQ _ (hm _ _ (mem1 x) (mem1 y)).1
    have hadd1 : ∀ x x' y, B (x+x') y=B x y+B x' y := by
      intro x x' y
      apply linj
      simp only [hB,ladd]
      exact (@yui_aux_0059 T gamma R h_E006 h_T005 h_T013).1 _ _ _ (mem0 x) (mem0 x') (mem0 y)
    have hsmul1 : ∀ (c : ℂ) x y, B (c•x) y=c•B x y := by
      intro c x y
      apply linj
      simp only [hB,lsmul]
      exact ((@yui_aux_0059 T gamma R h_E006 h_T005 h_T013).2.2 c _ _).1
    have hadd2 : ∀ x y y', B x (y+y')=B x y+B x y' := by
      intro x y y'
      apply linj
      simp only [hB,ladd]
      exact (@yui_aux_0059 T gamma R h_E006 h_T005 h_T013).2.1 _ _ _ (mem0 x) (mem0 y) (mem0 y')
    have hsmul2 : ∀ (c : ℂ) x y, B x (c•y)=c•B x y := by
      intro c x y
      apply linj
      simp only [hB,lsmul]
      exact ((@yui_aux_0059 T gamma R h_E006 h_T005 h_T013).2.2 c _ _).2
    let b : (lp (fun _ : ℤ=>ℂ) 2) →ₗ[ℂ] (lp (fun _ : ℤ=>ℂ) 2) →ₗ[ℂ] (lp (fun _ : ℤ=>ℂ) 2) := LinearMap.mk₂ ℂ B hadd1 hsmul1 hadd2 hsmul2
    have hb : ∀ x y, ‖b x y‖≤C*‖x‖*‖y‖ := by
      intro x y
      change ‖B x y‖≤C*‖x‖*‖y‖
      rw [← h_T013.2.1 1 (B x y),hB]
      simpa only [h_T013.2.1] using (hm _ _ (mem1 x) (mem1 y)).2
    refine ⟨(b.mkContinuous₂ C hb).bilinearRestrictScalars ℝ,?_⟩
    intro x y
    exact hB x y)

theorem yui_aux_0061 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ f : Path,\n (∃ u : ℝ → lp (fun _ : ℤ=>ℂ) 2, Continuous u ∧ ∀ t, FromLP 1 (u t)=f t) →\n ∃ u : ℝ → lp (fun _ : ℤ=>ℂ) 2, Continuous u ∧ ∀ t, FromLP 1 (u t)=S t (f t)" := by
  exact (open KdVPlan in by
    intro f hf
    have hc:=(@yui_aux_0057 T gamma R h_E006 h_T005 h_T013 f).mp hf
    apply (@yui_aux_0057 T gamma R h_E006 h_T005 h_T013 _).mpr
    refine ⟨fun t=>(@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).1 1 t (f t) (hc.1 t) |>.1,?_⟩
    intro t ε hε
    obtain ⟨δ,hδ,hd⟩:=hc.2 t (ε/2) (by linarith)
    have hs:=@yui_aux_0058 T gamma R h_E006 h_T005 h_T013 1 t (f t) (hc.1 t)
    obtain ⟨η,hη,he⟩:=(Metric.continuousAt_iff.mp hs.continuousAt) (ε/2) (by linarith)
    refine ⟨min δ η,lt_min hδ hη,?_⟩
    intro r hr
    have h1:=hd r (lt_of_lt_of_le hr (min_le_left _ _))
    have h2:=he (x:=r) (by simpa only [Real.dist_eq] using lt_of_lt_of_le hr (min_le_right _ _))
    have hz: hn 1 (S t (f t)-S t (f t))=0:=by
      simpa using (@yui_aux_0001 T gamma R h_E006 h_T005 h_T013 1).2
    rw [hz,dist_eq_norm,sub_zero,Real.norm_eq_abs,abs_of_nonneg ((@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 1).1 _)] at h2
    have hm:=(@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 1).2.2.1 (f r) (f t) (hc.1 r) (hc.1 t)
    have hsm:=(@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).1 1 r (f r-f t) hm.1
    have ht:=(@yui_aux_0003 T gamma R h_E006 h_T005 h_T013 1).2.2.1
      (S r (f t)) (S t (f t))
      ((@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).1 1 r (f t) (hc.1 t)).1
      ((@yui_aux_0008 T gamma R h_E006 h_T005 h_T013).1 1 t (f t) (hc.1 t)).1
    have ha:=(@yui_aux_0002 T gamma R h_E006 h_T005 h_T013 1 _ _ hsm.1 ht.1).2
    rw [(@yui_aux_0016 T gamma R h_E006 h_T005 h_T013).2.2.1] at ha
    have eqn : S r (f r)-S r (f t)+(S r (f t)-S t (f t))=S r (f r)-S t (f t):=by abel
    rw [eqn,← (@yui_aux_0016 T gamma R h_E006 h_T005 h_T013).2.2.1,hsm.2] at ha
    linarith)

theorem yui_aux_0062 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in ∀ M : ℤ → ℂ, ∀ C : ℝ, 0≤C → (∀ k, ‖M k‖≤C) →\n ∃ A : (lp (fun _ : ℤ=>ℂ) 2) →L[ℂ] (lp (fun _ : ℤ=>ℂ) 2),\n ∀ x k, FromLP 1 (A x) k=M k*FromLP 1 x k" := by
  exact (open KdVPlan in by
    intro M C hC hM
    obtain ⟨Q,hQ⟩:=(@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.2.2
    let A : lp (fun _ : ℤ=>ℂ) 2 → lp (fun _ : ℤ=>ℂ) 2 :=
      fun x=>Q (fun k=>M k*FromLP 1 x k)
    have hA : ∀ x, FromLP 1 (A x)=(fun k=>M k*FromLP 1 x k):=by
      intro x
      exact hQ _ (@yui_aux_0006 T gamma R h_E006 h_T005 h_T013 1 M C hC hM _ ((@yui_aux_0055 T gamma R h_E006 h_T005 h_T013 1 x x).1)).1
    let L : (lp (fun _ : ℤ=>ℂ) 2) →ₗ[ℂ] (lp (fun _ : ℤ=>ℂ) 2) := {
      toFun:=A
      map_add':=by
        intro x y
        apply (@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).1 1
        simp only [hA, (@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.1 1 x y |>.1,
          (@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.1 1 (A x) (A y) |>.1]
        funext k
        exact mul_add _ _ _
      map_smul':=by
        intro c x
        apply (@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).1 1
        change FromLP 1 (A (c • x))=FromLP 1 (c • A x)
        simp only [hA, (@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.2.1]
        funext k
        simp only [scale]
        ring }
    refine ⟨L.mkContinuous C ?_,?_⟩
    · intro x
      have h:=(@yui_aux_0006 T gamma R h_E006 h_T005 h_T013 1 M C hC hM _ ((@yui_aux_0055 T gamma R h_E006 h_T005 h_T013 1 x x).1)).2
      rw [← hA x,h_T013.2.1,h_T013.2.1] at h
      exact h
    · intro x k
      exact congrFun (hA x) k)

theorem yui_aux_0063 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],\n ∀ (L : E →L[ℝ] ℂ) (u : ℝ → E), ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) u →\n ∀ j t, L (iteratedDeriv j u t)=iteratedDeriv j (fun r=>L (u r)) t" := by
  intro E _ _ L u hu j
  induction j with
  | zero => intro t; rfl
  | succ j hj =>
    intro t
    have hd : Differentiable ℝ (iteratedDeriv j u):=
      hu.differentiable_iteratedDeriv j (@yui_aux_0052 T gamma R h_E006 h_T005 h_T013 j)
    have eqn : (fun r=>L (iteratedDeriv j u r))=iteratedDeriv j (fun r=>L (u r)):=funext hj
    rw [iteratedDeriv_succ,iteratedDeriv_succ,← eqn]
    exact (L.hasFDerivAt.comp_hasDerivAt t (hd t).hasDerivAt).deriv.symm

theorem yui_aux_0064 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in let Reg := fun f : Path => ∀ n : ℕ, ∃ u : ℝ → lp (fun _ : ℤ=>ℂ) 2, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) u ∧ ∀ t k, FromLP 1 (u t) k=(k:ℂ)^n*f t k;\n (∀ f, Smooth f → Reg (fun _=>f)) ∧\n (∀ f g, Reg f → Reg g → Reg (fun t=>f t+g t) ∧ Reg (fun t=>f t-g t)) ∧\n (∀ c : ℝ → ℂ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) c →\n   ∀ f, Reg f → Reg (fun t=>scale (c t) (f t))) ∧\n (∀ f, Reg f → Reg (fun t (k : ℤ)=>(k:ℂ)*f t k)) ∧\n (∀ f, Reg f → ∀ t, Smooth (f t))" := by
  exact (open KdVPlan in by
    dsimp only
    let Reg := fun f : Path => ∀ n : ℕ, ∃ u : ℝ → lp (fun _ : ℤ=>ℂ) 2, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) u ∧ ∀ t k, FromLP 1 (u t) k=(k:ℂ)^n*f t k
    have hc : ∀ f, Smooth f → Reg (fun _=>f):=by
      intro f hf n
      have hm:=(@yui_aux_0040 T gamma R h_E006 h_T005 h_T013 _ ((@yui_aux_0039 T gamma R h_E006 h_T005 h_T013).2.1 f hf n)).2
      obtain ⟨u,hu⟩:= (h_T013.1 1 _).mp hm
      refine ⟨fun _=>u,contDiff_const,?_⟩
      intro t k
      exact congrFun hu.symm k
    have ha : ∀ f g, Reg f → Reg g →
        Reg (fun t=>f t+g t) ∧ Reg (fun t=>f t-g t):=by
      intro f g hf hg
      constructor
      · intro n
        obtain ⟨u,hu,he⟩:=hf n
        obtain ⟨v,hv,hvE⟩:=hg n
        refine ⟨fun t=>u t+v t,hu.add hv,?_⟩
        intro t k
        rw [(@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.1 1 _ _ |>.1]
        change FromLP 1 (u t) k+FromLP 1 (v t) k=_
        rw [he,hvE]
        exact (mul_add _ _ _).symm
      · intro n
        obtain ⟨u,hu,he⟩:=hf n
        obtain ⟨v,hv,hvE⟩:=hg n
        refine ⟨fun t=>u t-v t,hu.sub hv,?_⟩
        intro t k
        rw [(@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.1 1 _ _ |>.2]
        change FromLP 1 (u t) k-FromLP 1 (v t) k=_
        rw [he,hvE]
        exact (mul_sub _ _ _).symm
    have hs : ∀ c : ℝ → ℂ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) c →
        ∀ f, Reg f → Reg (fun t=>scale (c t) (f t)):=by
      intro c hc f hf n
      obtain ⟨u,hu,he⟩:=hf n
      refine ⟨fun t=>c t • u t,hc.smul hu,?_⟩
      intro t k
      rw [(@yui_aux_0046 T gamma R h_E006 h_T005 h_T013).2.2.1]
      change c t*FromLP 1 (u t) k=_
      rw [he]
      simp only [scale]
      ring
    have hd : ∀ f, Reg f → Reg (fun t (k : ℤ)=>(k:ℂ)*f t k):=by
      intro f hf n
      obtain ⟨u,hu,he⟩:=hf (n+1)
      refine ⟨u,hu,?_⟩
      intro t k
      rw [he,pow_succ]
      ring
    have hm : ∀ f, Reg f → ∀ t, Smooth (f t):=by
      intro f hf t
      apply (@yui_aux_0039 T gamma R h_E006 h_T005 h_T013).2.2
      intro n
      obtain ⟨u,hu,he⟩:=hf n
      have heq : FromLP 1 (u t)=(fun k : ℤ=>(k:ℂ)^n*f t k):=funext (he t)
      have hh := (h_T013.1 1 _).mpr ⟨u t,rfl⟩
      rw [heq] at hh
      exact (h_T013.2.2.2.1 0 1 _ (by norm_num) hh).1
    exact ⟨hc,ha,hs,hd,hm⟩)

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_E006 : KdVPlan.Endpoint) (h_T005 : KdVPlan.BilinearOutput) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "open KdVPlan in let Reg := fun f : Path => ∀ n : ℕ, ∃ u : ℝ → lp (fun _ : ℤ=>ℂ) 2,  ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) u ∧ ∀ t k, FromLP 1 (u t) k=(k:ℂ)^n*f t k;\n (∀ f, Reg f → ∀ k, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun t=>f t k)) ∧\n (∀ f, Reg f → ∀ j : ℕ, Reg (fun t k=>iteratedDeriv j (fun r=>f r k) t))" := by
  exact (open KdVPlan in by
    dsimp only
    let Reg := fun f : Path => ∀ n : ℕ, ∃ u : ℝ → lp (fun _ : ℤ=>ℂ) 2,  ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) u ∧ ∀ t k, FromLP 1 (u t) k=(k:ℂ)^n*f t k
    obtain ⟨ev,he,hsep⟩:=@yui_aux_0054 T gamma R h_E006 h_T005 h_T013
    have hh : ∀ f, Reg f → ∀ k, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun t=>f t k):=by
      intro f hf k
      obtain ⟨u,hu,heq⟩:=hf 0
      have eqn : (fun t=>ev k (u t))=(fun t=>f t k):=by
        funext t
        rw [he,heq]
        simp
      rw [← eqn]
      exact (ev k).contDiff.comp hu
    refine ⟨hh,?_⟩
    intro f hf j n
    obtain ⟨u,hu,heq⟩:=hf n
    have hud : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (iteratedDeriv j u):=by
      exact hu.iteratedDeriv (by simpa using le_rfl : ((⊤:ℕ∞):WithTop ℕ∞)+j≤((⊤:ℕ∞):WithTop ℕ∞))
    refine ⟨iteratedDeriv j u,hud,?_⟩
    intro t k
    rw [← he]
    rw [@yui_aux_0063 T gamma R h_E006 h_T005 h_T013 _ _ _ (ev k) u hu j t]
    have eqn : (fun r=>ev k (u r))=(fun r=>(k:ℂ)^n*f r k):=by
      funext r
      rw [he,heq]
    rw [eqn,iteratedDeriv_const_mul_field])
#check @checked
#print axioms checked
end YuiAuxiliary
