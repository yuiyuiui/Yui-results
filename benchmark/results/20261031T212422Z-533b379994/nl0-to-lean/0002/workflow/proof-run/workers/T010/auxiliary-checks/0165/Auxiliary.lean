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
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ C : ℝ, Tendsto (fun N : ℝ => C*(N⁻¹+N^(-KdVPlan.pstar))) atTop (nhds 0)" := by
  intro C
  have hp : 0 < KdVPlan.pstar := by norm_num [KdVPlan.pstar]
  have hi : Tendsto (fun N : ℝ => N⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hr : Tendsto (fun N : ℝ => N^(-KdVPlan.pstar)) atTop (nhds 0) := tendsto_rpow_neg_atTop hp
  simpa using (hi.add hr).const_mul C

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ C : ℝ, 0 < C → ∃ N δ K : ℝ, 2 ≤ N ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧ ∀ h τ E A : ℝ, 0 ≤ h → h ≤ δ → 0 < τ → τ ≤ δ/2 → 0 ≤ E → E ≤ A + C*(h+τ)*τ^gamma + C*(N^2*h+h+τ+N⁻¹+N^(-KdVPlan.pstar))*E → E ≤ 2*A+K*δ*τ^gamma" := by
  intro C hC
  have ht := @yui_aux_0001 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 C
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)))
  let N : ℝ := max 2 B
  have hN : 2 ≤ N := le_max_left _ _
  have htail : C*(N⁻¹+N^(-KdVPlan.pstar)) ≤ 1/8 := (hB N (le_max_right _ _)).le
  let δ : ℝ := min 1 (1/(8*C*(N^2+3)))
  have hdpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hdle : δ ≤ 1 := min_le_left _ _
  have hdsmall : δ*(8*C*(N^2+3)) ≤ 1 := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨N, δ, 4*C, hN, hdpos, hdle, by positivity, ?_⟩
  intro h τ E A hh hhd htpos htd hE hpre
  have hcoef : C*(N^2*h+h+τ+N⁻¹+N^(-KdVPlan.pstar)) ≤ 1/2 := by
    have hnh : N^2*h ≤ N^2*δ := mul_le_mul_of_nonneg_left hhd (sq_nonneg N)
    have hτ : τ ≤ δ := le_trans htd (by linarith)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoef hE
  have hsum : h+τ ≤ 2*δ := by linarith
  have hpow : 0 ≤ τ^gamma := Real.rpow_nonneg htpos.le _
  have hforce := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hC.le) hpow
  nlinarith

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.MemH s (f+g) ∧ KdVPlan.hn s (f+g) ≤ KdVPlan.hn s f+KdVPlan.hn s g" := by
  intro s f g hf hg
  obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
  obtain ⟨y, rfl⟩ := (h_T013.1 s g).mp hg
  have hadd : KdVPlan.FromLP s (x+y) = KdVPlan.FromLP s x+KdVPlan.FromLP s y := by
    funext k
    simp [KdVPlan.FromLP, mul_add]
  rw [← hadd]
  constructor
  · exact (h_T013.1 s _).mpr ⟨x+y,rfl⟩
  · simpa only [h_T013.2.1] using norm_add_le x y

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (c : ℂ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s (KdVPlan.scale c f) ∧ KdVPlan.hn s (KdVPlan.scale c f) = ‖c‖*KdVPlan.hn s f" := by
  intro s c f hf
  obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
  have hscale : KdVPlan.FromLP s (c • x) = KdVPlan.scale c (KdVPlan.FromLP s x) := by
    funext k
    simp [KdVPlan.FromLP, KdVPlan.scale, mul_left_comm]
  rw [← hscale]
  constructor
  · exact (h_T013.1 s _).mpr ⟨c • x,rfl⟩
  · simp only [h_T013.2.1, norm_smul]

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.MemH s (f-g) ∧ KdVPlan.hn s (f-g) ≤ KdVPlan.hn s f+KdVPlan.hn s g" := by
  intro s f g hf hg
  have hn := @yui_aux_0004 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s (-1) g hg
  have heq : KdVPlan.scale (-1) g = -g := by funext k; simp [KdVPlan.scale]
  rw [heq] at hn
  have hh := @yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s f (-g) hf hn.1
  simpa [sub_eq_add_neg, hn.2] using hh

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s r C : ℝ) (f g : KdVPlan.Coeff), 0 ≤ C → KdVPlan.MemH r g → (∀ k, KdVPlan.weight s k*‖f k‖^2 ≤ C^2*(KdVPlan.weight r k*‖g k‖^2)) → KdVPlan.HB s f (C*KdVPlan.hn r g)" := by
  intro s r C f g hC hg hfg
  have hw (q : ℝ) (k : ℤ) : 0 ≤ KdVPlan.weight q k := Real.rpow_nonneg (by positivity) _
  have hf : KdVPlan.MemH s f := (hg.mul_left (C^2)).of_nonneg_of_le (fun k => mul_nonneg (hw s k) (sq_nonneg _)) hfg
  refine ⟨hf, ?_⟩
  have hsum : (∑' k, KdVPlan.weight s k*‖f k‖^2) ≤ C^2*(∑' k, KdVPlan.weight r k*‖g k‖^2) := by
    rw [← tsum_mul_left]
    exact hf.tsum_le_tsum hfg (hg.mul_left (C^2))
  have hsqrt := Real.sqrt_le_sqrt hsum
  simpa only [KdVPlan.hn, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] using hsqrt

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s N : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.HB s (KdVPlan.cutoff N f) (KdVPlan.hn s f) ∧ KdVPlan.HB s (KdVPlan.high N f) (KdVPlan.hn s f)" := by
  intro s N f hf
  have hw (k : ℤ) : 0 ≤ KdVPlan.weight s k*‖f k‖^2 := mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  constructor
  · simpa using @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s s 1 (KdVPlan.cutoff N f) f (by norm_num) hf (by
      intro k
      by_cases hk : |(k:ℝ)| ≤ N <;> simp [KdVPlan.cutoff, hk, hw])
  · simpa using @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s s 1 (KdVPlan.high N f) f (by norm_num) hf (by
      intro k
      by_cases hk : |(k:ℝ)| ≤ N <;> simp [KdVPlan.high, KdVPlan.cutoff, hk, hw])

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ N x : ℝ, 0 < N → N^2 ≤ 1+x^2 → 1 ≤ (N⁻¹)^2*(1+x^2)" := by
  intro N x hN hsq
  have heq : (N⁻¹)^2*(1+x^2) = (1+x^2)/N^2 := by ring
  rw [heq]
  exact (le_div_iff₀ (sq_pos_of_pos hN)).mpr (by simpa using hsq)

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N : ℝ) (f : KdVPlan.Coeff), 0 < N → KdVPlan.MemH 1 f → KdVPlan.HB 0 (KdVPlan.high N f) (N⁻¹*KdVPlan.hn 1 f)" := by
  intro N f hN hf
  apply @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 1 N⁻¹ (KdVPlan.high N f) f (inv_nonneg.mpr hN.le) hf
  intro k
  by_cases hk : |(k:ℝ)| ≤ N
  · simp [KdVPlan.high, KdVPlan.cutoff, hk, KdVPlan.weight]
    positivity
  · have ha : N < |(k:ℝ)| := lt_of_not_ge hk
    have hsq : N^2 ≤ 1+(k:ℝ)^2 := by nlinarith [sq_abs (k:ℝ)]
    have hi := @yui_aux_0008 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N (k:ℝ) hN hsq
    simpa [KdVPlan.high, KdVPlan.cutoff, hk, KdVPlan.weight, mul_assoc] using mul_le_mul_of_nonneg_right hi (sq_nonneg ‖f k‖)

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, Function.Injective (KdVPlan.FromLP s)" := by
  intro s x y hxy
  apply lp.ext
  funext k
  have hw : (KdVPlan.weight (-s/2) k : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  exact mul_left_cancel₀ hw (congrFun hxy k)

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, ∃ W : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2, (∀ f, KdVPlan.MemH s f → KdVPlan.FromLP s (W f) = f) ∧ (∀ x, W (KdVPlan.FromLP s x) = x)" := by
  classical
  intro s
  let W : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2 := fun f => if hf : KdVPlan.MemH s f then Classical.choose ((h_T013.1 s f).mp hf) else 0
  have hw (f : KdVPlan.Coeff) (hf : KdVPlan.MemH s f) : KdVPlan.FromLP s (W f) = f := by
    dsimp [W]
    rw [dif_pos hf]
    exact (Classical.choose_spec ((h_T013.1 s f).mp hf)).symm
  refine ⟨W, hw, ?_⟩
  intro x
  apply @yui_aux_0010 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s
  exact hw _ ((h_T013.1 s _).mpr ⟨x,rfl⟩)

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Path) (W : KdVPlan.Coeff → lp (fun _ : ℤ => ℂ) 2), (∀ g, KdVPlan.MemH s g → KdVPlan.FromLP s (W g) = g) → KdVPlan.ContH s a b f → ContinuousOn (fun t => W (f t)) (Icc a b)" := by
  intro s a b f W hW hf
  apply Metric.continuousOn_iff.mpr
  intro t ht ε hε
  obtain ⟨δ,hδ,hd⟩ := hf.2 t ht ε hε
  refine ⟨δ,hδ,?_⟩
  intro r hr hrt
  have heq : KdVPlan.FromLP s (W (f r)-W (f t)) = f r-f t := by
    funext k
    simp only [KdVPlan.FromLP, lp.coeFn_sub, Pi.sub_apply, mul_sub]
    exact congrArg₂ (fun x y : ℂ => x-y) (congrFun (hW _ (hf.1 r hr)) k) (congrFun (hW _ (hf.1 t ht)) k)
  rw [dist_eq_norm]
  rw [← h_T013.2.1 s (W (f r)-W (f t)), heq]
  exact hd r hr (by simpa [Real.dist_eq] using hrt)

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (f : KdVPlan.Path), a ≤ b → KdVPlan.ContH s a b f → KdVPlan.UB s a b f C → KdVPlan.HB s (KdVPlan.timeInt a b f) (C*(b-a))" := by
  intro s a b C f hab hf hb
  obtain ⟨W,hW,_⟩ := @yui_aux_0011 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s
  have hc := @yui_aux_0012 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f W hW hf
  have hi : IntervalIntegrable (fun t => W (f t)) volume a b := hc.intervalIntegrable_of_Icc hab
  have heq : KdVPlan.FromLP s (∫ t in a..b, W (f t)) = KdVPlan.timeInt a b f := by
    funext k
    let L : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ := (KdVPlan.weight (-s/2) k : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k
    change L (∫ t in a..b, W (f t)) = ∫ t in a..b, f t k
    rw [← L.intervalIntegral_comp_comm hi]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
    exact congrFun (hW _ (hf.1 t ht')) k
  rw [← heq]
  refine ⟨(h_T013.1 s _).mpr ⟨_,rfl⟩, ?_⟩
  rw [h_T013.2.1]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq (by rw [abs_of_nonneg (sub_nonneg.mpr hab)])
  intro t ht
  have ht0 : t ∈ Ioc a b := by simpa [uIoc_of_le hab] using ht
  have ht' : t ∈ Icc a b := ⟨ht0.1.le,ht0.2⟩
  rw [← h_T013.2.1 s (W (f t)), hW _ (hf.1 t ht')]
  exact (hb t ht').2

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s a b g → KdVPlan.ContH s a b (fun t => f t+g t)" := by
  intro s a b f g hf hg
  let addH := @yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  let subH := @yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  refine ⟨fun t ht => (addH s (f t) (g t) (hf.1 t ht) (hg.1 t ht)).1, ?_⟩
  intro t ht ε hε
  obtain ⟨δf,hδf,hfδ⟩ := hf.2 t ht (ε/2) (by linarith)
  obtain ⟨δg,hδg,hgδ⟩ := hg.2 t ht (ε/2) (by linarith)
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro r hr hrt
  have hfr := hfδ r hr (lt_of_lt_of_le hrt (min_le_left _ _))
  have hgr := hgδ r hr (lt_of_lt_of_le hrt (min_le_right _ _))
  have heq : f r+g r-(f t+g t) = (f r-f t)+(g r-g t) := by abel
  rw [heq]
  have ha := (addH s (f r-f t) (g r-g t) (subH s _ _ (hf.1 r hr) (hf.1 t ht)).1 (subH s _ _ (hg.1 r hr) (hg.1 t ht)).1).2
  linarith

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (c : ℂ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s a b (fun t => KdVPlan.scale c (f t))" := by
  intro s a b c f hf
  let scaleH := @yui_aux_0004 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  let subH := @yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  refine ⟨fun t ht => (scaleH s c (f t) (hf.1 t ht)).1, ?_⟩
  intro t ht ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf.2 t ht (ε/(‖c‖+1)) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro r hr hrt
  have heq : KdVPlan.scale c (f r)-KdVPlan.scale c (f t) = KdVPlan.scale c (f r-f t) := by funext k; simp [KdVPlan.scale,mul_sub]
  rw [heq, (scaleH s c (f r-f t) (subH s _ _ (hf.1 r hr) (hf.1 t ht)).1).2]
  have hh := (lt_div_iff₀ (by positivity : 0 < ‖c‖+1)).mp (hfδ r hr hrt)
  have hn : 0 ≤ KdVPlan.hn s (f r-f t) := Real.sqrt_nonneg _
  nlinarith [norm_nonneg c]

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → BddAbove {x : ℝ | ∃ t ∈ Icc a b, x = KdVPlan.hn s (f t)} ∧ ∀ t ∈ Icc a b, KdVPlan.HB s (f t) (KdVPlan.SupH s a b f)" := by
  intro s a b f hf
  obtain ⟨W,hW,_⟩ := @yui_aux_0011 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s
  have hc := @yui_aux_0012 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f W hW hf
  have hn : ContinuousOn (fun t => KdVPlan.hn s (f t)) (Icc a b) := hc.norm.congr (by
    intro t ht
    change KdVPlan.hn s (f t) = ‖W (f t)‖
    rw [← h_T013.2.1 s (W (f t)), hW _ (hf.1 t ht)])
  have hs : {x : ℝ | ∃ t ∈ Icc a b, x = KdVPlan.hn s (f t)} = (fun t => KdVPlan.hn s (f t)) '' Icc a b := by
    ext x
    simp only [mem_setOf_eq, mem_image]
    constructor <;> rintro ⟨t,ht,hx⟩ <;> exact ⟨t,ht,hx.symm⟩
  have hb : BddAbove {x : ℝ | ∃ t ∈ Icc a b, x = KdVPlan.hn s (f t)} := by
    rw [hs]
    exact (isCompact_Icc.image_of_continuousOn hn).bddAbove
  refine ⟨hb, ?_⟩
  intro t ht
  exact ⟨hf.1 t ht, le_csSup hb ⟨t,ht,rfl⟩⟩

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → (∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → b-a ≤ 1 → KdVPlan.enorm a b τ f v ≤ 1 → KdVPlan.StabilityEstimates C gamma τ a b f v) → ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧ ∀ (τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 0 < τ → τ ≤ δ/2 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → b-a ≤ δ → KdVPlan.enorm a b τ f v ≤ 1 → KdVPlan.enorm a b τ f v ≤ 2*KdVPlan.hn 0 (KdVPlan.err τ f v a)+K*δ*τ^gamma" := by
  intro M hM hbase
  obtain ⟨C,hC,hs⟩ := hbase
  obtain ⟨N,δ,K,hN,hδ,hd1,hK,ha⟩ := @yui_aux_0002 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 C hC
  refine ⟨δ,K,hδ,hd1,hK,?_⟩
  intro τ L f v a b ht htδ htraj hg hlen he
  have ht1 : τ ≤ 1 := by linarith
  have hp := (hs τ L f v a b ht ht1 htraj hg (hlen.trans hd1) he).2 N hN
  apply ha (b-a) τ (KdVPlan.enorm a b τ f v) (KdVPlan.hn 0 (KdVPlan.err τ f v a)) (sub_nonneg.mpr hg.2.1) hlen ht htδ
  · apply Real.sSup_nonneg
    rintro x ⟨t,ht,rfl⟩
    exact Real.sqrt_nonneg _
  · exact hp.2.2.2

theorem yui_aux_0018 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), (∀ t ∈ Icc a b, f t = g t) → KdVPlan.ContH s a b f → KdVPlan.ContH s a b g" := by
  intro s a b f g heq hf
  constructor
  · intro t ht
    rw [← heq t ht]
    exact hf.1 t ht
  · intro t ht ε hε
    obtain ⟨δ,hδ,hd⟩ := hf.2 t ht ε hε
    refine ⟨δ,hδ,?_⟩
    intro r hr hrt
    rw [← heq r hr, ← heq t ht]
    exact hd r hr hrt

theorem yui_aux_0019 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ j : ℕ, (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)" := by
  intro j
  change ((j : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

theorem yui_aux_0020 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), a < b → KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b g → KdVPlan.SmoothOn a b (fun t => f t+g t)" := by
  intro a b f g hab hf hg
  constructor
  · intro k
    exact (hf.1 k).add (hg.1 k)
  · intro m j
    have hs := @yui_aux_0014 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b _ _ (hf.2 m j) (hg.2 m j)
    apply @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b _ _ ?_ hs
    intro t ht
    funext k
    symm
    exact iteratedDerivWithin_fun_add ht (uniqueDiffOn_Icc hab) ((hf.1 k t ht).of_le (@yui_aux_0019 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 j)) ((hg.1 k t ht).of_le (@yui_aux_0019 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 j))

theorem yui_aux_0021 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b (fun t => f t+g t)" := by
  classical
  intro a b f g hf hg
  constructor
  · intro m
    exact @yui_aux_0014 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 _ _ _ _ _ (hf.1 m) (hg.1 m)
  · obtain ⟨p,hp⟩ := hf.2
    obtain ⟨q,hq⟩ := hg.2
    refine ⟨p∪q,?_⟩
    intro l r hal hlr hrb hn
    apply @yui_aux_0020 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l r f g hlr
    · exact hp l r hal hlr hrb (fun x hx => hn x (Finset.mem_union_left q hx))
    · exact hq l r hal hlr hrb (fun x hx => hn x (Finset.mem_union_right p hx))

theorem yui_aux_0022 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (c : ℂ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b (fun t => KdVPlan.scale c (f t))" := by
  intro a b c f hf
  constructor
  · intro k
    exact contDiffOn_const.mul (hf.1 k)
  · intro m j
    have hs : KdVPlan.ContH (m:ℝ) a b (fun t k => c*iteratedDerivWithin j (fun r => f r k) (Icc a b) t) := @yui_aux_0015 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b c _ (hf.2 m j)
    simpa only [KdVPlan.scale, iteratedDerivWithin_const_mul_field] using hs

theorem yui_aux_0023 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (c : ℂ) (f : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b (fun t => KdVPlan.scale c (f t))" := by
  intro a b c f hf
  constructor
  · intro m
    exact @yui_aux_0015 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 _ _ _ c _ (hf.1 m)
  · obtain ⟨p,hp⟩ := hf.2
    refine ⟨p,?_⟩
    intro l r hal hlr hrb hn
    exact @yui_aux_0022 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l r c f (hp l r hal hlr hrb hn)

theorem yui_aux_0024 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b l r : ℝ) (f : KdVPlan.Path), a ≤ l → r ≤ b → KdVPlan.ContH s a b f → KdVPlan.ContH s l r f" := by
  intro s a b l r f hal hrb hf
  have hs : Icc l r ⊆ Icc a b := Icc_subset_Icc hal hrb
  refine ⟨fun t ht => hf.1 t (hs ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δ,hδ,hd⟩ := hf.2 t (hs ht) ε hε
  exact ⟨δ,hδ,fun x hx => hd x (hs hx)⟩

theorem yui_aux_0025 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b l r : ℝ) (f : KdVPlan.Path), a ≤ l → l < r → r ≤ b → KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn l r f" := by
  intro a b l r f hal hlr hrb hf
  have hab : a < b := hal.trans_lt (hlr.trans_le hrb)
  have hsub : Icc l r ⊆ Icc a b := Icc_subset_Icc hal hrb
  constructor
  · intro k
    exact (hf.1 k).mono hsub
  · intro m j
    have hc := @yui_aux_0024 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b l r _ hal hrb (hf.2 m j)
    apply @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) l r _ _ ?_ hc
    intro t ht
    funext k
    have heq := iteratedFDerivWithin_subset hsub (uniqueDiffOn_Icc hlr) (uniqueDiffOn_Icc hab) ((hf.1 k).of_le (@yui_aux_0019 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 j)) ht
    exact (congrArg (fun A => A (fun _ => (1:ℝ))) heq).symm

theorem yui_aux_0026 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.Piecewise a b f" := by
  intro a b f hf
  constructor
  · intro m
    simpa only [iteratedDerivWithin_zero] using hf.2 m 0
  · refine ⟨∅,?_⟩
    intro l r hal hlr hrb _
    exact @yui_aux_0025 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b l r f hal hlr hrb hf

theorem yui_aux_0027 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b (fun t => f t-g t)" := by
  intro a b f g hf hg
  have hn := @yui_aux_0023 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (-1) g hg
  have heq : (fun t => KdVPlan.scale (-1) (g t)) = (fun t => -g t) := by
    funext t k
    simp [KdVPlan.scale]
  rw [heq] at hn
  simpa only [sub_eq_add_neg] using @yui_aux_0021 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b f (fun t => -g t) hf hn

theorem yui_aux_0028 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b l r : ℝ) (f : KdVPlan.Path), a ≤ l → r ≤ b → KdVPlan.Piecewise a b f → KdVPlan.Piecewise l r f" := by
  intro a b l r f hal hrb hf
  constructor
  · intro m
    exact @yui_aux_0024 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 _ a b l r f hal hrb (hf.1 m)
  · obtain ⟨p,hp⟩ := hf.2
    refine ⟨p,?_⟩
    intro x y hlx hxy hyr hn
    exact hp x y (hal.trans hlx) hxy (hyr.trans hrb) hn

theorem yui_aux_0029 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → ∀ t ∈ Icc a b, let e := KdVPlan.err τ f v; let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s); KdVPlan.errorF a τ f v t = KdVPlan.scale (1/3) (KdVPlan.J t (e t) (g t)-KdVPlan.J a (e a) (g a)) - KdVPlan.scale (1/3) (KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt e s) (g s)+KdVPlan.J s (e s) (KdVPlan.dt g s)))" := by
  intro M τ L f v a b hM ht ht1 hv hg t htt
  let e := KdVPlan.err τ f v
  let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s)
  obtain ⟨C,hC,_,hacc⟩ := h_T009 M hM
  have ha := hacc τ L f v ht ht1 hv
  have pv := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v hv.2.2.1
  have pe : KdVPlan.Piecewise 0 ((L:ℝ)*τ) e := @yui_aux_0027 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v (KdVPlan.interp τ f) pv ha.1
  have pg : KdVPlan.Piecewise 0 ((L:ℝ)*τ) g := @yui_aux_0027 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v (fun s => KdVPlan.scale (1/2) (e s)) pv (@yui_aux_0023 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) (1/2) e pe)
  have htH : t ≤ (L:ℝ)*τ := htt.2.trans hg.2.2.1
  have e0 : ∀ s ∈ Icc a t, KdVPlan.ZeroMean (e s) := by
    intro s hs
    have hsH : s ∈ Icc 0 ((L:ℝ)*τ) := ⟨hg.1.trans hs.1,hs.2.trans htH⟩
    change v s 0-KdVPlan.interp τ f s 0 = 0
    rw [(hv.2.2.2.1 s hsH).1, (ha.2.1 s hsH).1]
    simp
  have g0 : ∀ s ∈ Icc a t, KdVPlan.ZeroMean (g s) := by
    intro s hs
    have hsH : s ∈ Icc 0 ((L:ℝ)*τ) := ⟨hg.1.trans hs.1,hs.2.trans htH⟩
    change v s 0-(1/2:ℂ)*e s 0 = 0
    rw [(hv.2.2.2.1 s hsH).1, e0 s hs]
    simp
  exact h_T005.2.2.1 a t e g htt.1 (@yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) a t e hg.1 htH pe) (@yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) a t g hg.1 htH pg) e0 g0

theorem yui_aux_0030 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ n : ℕ, n ≤ L → (n:ℝ)*τ ∈ Icc a b → KdVPlan.StepData gamma M ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) (v ((n:ℝ)*τ))" := by
  intro M τ L f v a b hM ht ht1 hv hg hE n hn hni
  obtain ⟨C,hC,_,hacc⟩ := h_T009 M hM
  have ha := hacc τ L f v ht ht1 hv
  have hnH : (n:ℝ)*τ ∈ Icc 0 ((L:ℝ)*τ) := ⟨hg.1.trans hni.1,hni.2.trans hg.2.2.1⟩
  have hgrid := ha.2.2.2.2.1 n hn
  have hmem (m : ℕ) : KdVPlan.MemH (m:ℝ) (KdVPlan.twistedNum τ f n) := by
    rw [← hgrid]
    exact (ha.1.1 m).1 _ hnH
  have hreal := ha.2.1 _ hnH
  rw [hgrid] at hreal
  have hdata : KdVPlan.Data 0 (KdVPlan.twistedNum τ f n) := ⟨by simpa using hmem 0,hreal⟩
  have hw := hv.2.2.2.2.1 _ hnH
  have hwreal := hv.2.2.2.1 _ hnH
  have hwdata : KdVPlan.Data gamma (v ((n:ℝ)*τ)) := ⟨hw.1,hwreal⟩
  have hwsmooth : KdVPlan.Smooth (v ((n:ℝ)*τ)) := by
    intro m
    simpa only [iteratedDerivWithin_zero] using (hv.2.2.1.2 m 0).1 _ hnH
  have pv := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v hv.2.2.1
  have pe : KdVPlan.Piecewise 0 ((L:ℝ)*τ) (KdVPlan.err τ f v) := @yui_aux_0027 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v (KdVPlan.interp τ f) pv ha.1
  have hecont : KdVPlan.ContH 0 a b (KdVPlan.err τ f v) := @yui_aux_0024 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 0 ((L:ℝ)*τ) a b _ hg.1 hg.2.2.1 (by simpa using pe.1 0)
  have hen := (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b _ hecont).2 _ hni
  have heq : KdVPlan.hn 0 (KdVPlan.twistedNum τ f n-v ((n:ℝ)*τ)) = KdVPlan.hn 0 (KdVPlan.err τ f v ((n:ℝ)*τ)) := by
    unfold KdVPlan.err
    rw [hgrid]
    unfold KdVPlan.hn
    congr 1
    apply tsum_congr
    intro k
    simp only [Pi.sub_apply, norm_sub_rev]
  refine ⟨hM,hnH.1,ht,ht1,hdata,hwdata,hmem,hwsmooth,hw.2,?_⟩
  rw [heq]
  exact hen.2.trans hE

theorem yui_aux_0031 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.Piecewise a b (KdVPlan.err τ f v) ∧ KdVPlan.UB 0 a b (KdVPlan.err τ f v) (KdVPlan.enorm a b τ f v)" := by
  intro M τ L f v a b hM ht ht1 hv hg
  obtain ⟨C,hC,_,hacc⟩ := h_T009 M hM
  have ha := hacc τ L f v ht ht1 hv
  have pv := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v hv.2.2.1
  have pe : KdVPlan.Piecewise 0 ((L:ℝ)*τ) (KdVPlan.err τ f v) := @yui_aux_0027 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v (KdVPlan.interp τ f) pv ha.1
  have pel := @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) a b _ hg.1 hg.2.2.1 pe
  refine ⟨pel,?_⟩
  exact (@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b _ (by simpa using pel.1 0)).2

theorem yui_aux_0032 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.hn s (f-g) = KdVPlan.hn s (g-f)" := by
  intro s f g
  unfold KdVPlan.hn
  congr 1
  apply tsum_congr
  intro k
  simp only [Pi.sub_apply, norm_sub_rev]

theorem yui_aux_0033 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (r : ℝ), ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1" := by
  intro r
  rw [Complex.norm_exp, Complex.mul_re]
  simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

theorem yui_aux_0034 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f : KdVPlan.Coeff) (k : ℤ), ‖KdVPlan.S t f k‖ = ‖f k‖" := by
  intro t f k
  change ‖Complex.exp (Complex.I * ((t*(k:ℝ)^3 : ℝ):ℂ)) * f k‖ = ‖f k‖
  rw [norm_mul, @yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (t*(k:ℝ)^3),one_mul]

theorem yui_aux_0035 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s t : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s (KdVPlan.S t f) ∧ KdVPlan.hn s (KdVPlan.S t f) = KdVPlan.hn s f" := by
  intro s t f hf
  have heq : (fun k => KdVPlan.weight s k*‖KdVPlan.S t f k‖^2) = (fun k => KdVPlan.weight s k*‖f k‖^2) := by
    funext k
    rw [@yui_aux_0034 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t f k]
  constructor
  · change Summable _
    rw [heq]
    exact hf
  · change Real.sqrt (∑' k, _) = _
    rw [heq]
    rfl

theorem yui_aux_0036 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.B t f g = KdVPlan.S (-t) (KdVPlan.dx (KdVPlan.dx (KdVPlan.invD (KdVPlan.P (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t g))))))" := by
  intro t f g
  unfold KdVPlan.B
  congr 1
  funext k
  by_cases hk : k = 0
  · subst k
    simp [KdVPlan.dx, KdVPlan.invD, KdVPlan.P]
  · have hi : Complex.I*(k:ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
    simp only [KdVPlan.dx, KdVPlan.invD, KdVPlan.P, if_neg hk]
    rw [mul_inv_cancel_left₀ hi]

theorem yui_aux_0037 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f : KdVPlan.Coeff) (k : ℤ), ‖KdVPlan.dx f k‖ = |(k : ℝ)| * ‖f k‖" := by
  intro f k
  simp only [KdVPlan.dx, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]

theorem yui_aux_0038 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N t : ℝ) (A : KdVPlan.Coeff), 0 ≤ N → KdVPlan.MemH 0 A → KdVPlan.HB 0 (KdVPlan.cutoff N (KdVPlan.S t (KdVPlan.dx (KdVPlan.dx A)))) (N^2 * KdVPlan.hn 0 A)" := by
  intro N t A hN hA
  apply @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 0 (N^2) _ A (sq_nonneg N) hA
  intro k
  by_cases hk : |(k:ℝ)| ≤ N
  · simp only [KdVPlan.cutoff, if_pos hk, @yui_aux_0034 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013, @yui_aux_0037 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013, KdVPlan.weight, Real.rpow_zero, one_mul]
    calc
      (|(k:ℝ)| * (|(k:ℝ)| * ‖A k‖))^2 ≤ (N*(N*‖A k‖))^2 := by gcongr
      _ = (N^2)^2*‖A k‖^2 := by ring
  · simp only [KdVPlan.cutoff, if_neg hk, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, KdVPlan.weight, Real.rpow_zero, one_mul]
    positivity

theorem yui_aux_0039 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ C : ℝ, 0 < C ∧ ∀ (N t : ℝ) (f g : KdVPlan.Coeff), 0 ≤ N → KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → KdVPlan.HB 0 (KdVPlan.cutoff N (KdVPlan.B t f g)) (C*N^2*KdVPlan.hn 0 f*KdVPlan.hn 0 g)" := by
  obtain ⟨C,hC,hi,hm,hBG,hA⟩ := h_T005.1.1
  refine ⟨C,hC,?_⟩
  intro N t f g hN hf hg
  have hfs := @yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 t f hf
  have hgs := @yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 t g hg
  let A := KdVPlan.invD (KdVPlan.P (KdVPlan.mul (KdVPlan.S t f) (KdVPlan.S t g)))
  have hprod : KdVPlan.HB 0 A (C*KdVPlan.hn 0 f*KdVPlan.hn 0 g) := by
    simpa only [hfs.2,hgs.2] using (hBG 0 (KdVPlan.S t f) (KdVPlan.S t g) hfs.1 hgs.1).2.2
  have hlow := @yui_aux_0038 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N (-t) A hN hprod.1
  have heq := @yui_aux_0036 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t f g
  change KdVPlan.B t f g = KdVPlan.S (-t) (KdVPlan.dx (KdVPlan.dx A)) at heq
  rw [← heq] at hlow
  refine ⟨hlow.1,?_⟩
  calc
    KdVPlan.hn 0 (KdVPlan.cutoff N (KdVPlan.B t f g)) ≤ N^2*KdVPlan.hn 0 A := hlow.2
    _ ≤ N^2*(C*KdVPlan.hn 0 f*KdVPlan.hn 0 g) := mul_le_mul_of_nonneg_left hprod.2 (sq_nonneg N)
    _ = C*N^2*KdVPlan.hn 0 f*KdVPlan.hn 0 g := by ring

theorem yui_aux_0040 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → KdVPlan.UB 0 a b v M ∧ KdVPlan.UB 0 a b (KdVPlan.interp τ f) (M+1) ∧ KdVPlan.UB 0 a b (fun t => v t-KdVPlan.scale (1/2) (KdVPlan.err τ f v t)) (M+1)" := by
  intro M τ L f v a b hM ht ht1 hv hg hE
  have he := (@yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg).2
  have hv0 : KdVPlan.UB 0 a b v M := by
    intro t htt
    have hvγ := hv.2.2.2.2.1 t ⟨hg.1.trans htt.1,htt.2.trans hg.2.2.1⟩
    have hh := h_T013.2.2.2.1 0 gamma (v t) h_H002.1.le hvγ.1
    exact ⟨hh.1,hh.2.trans hvγ.2⟩
  refine ⟨hv0,?_,?_⟩
  · intro t htt
    have hsub := @yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (v t) (KdVPlan.err τ f v t) (hv0 t htt).1 (he t htt).1
    have heq : v t-KdVPlan.err τ f v t = KdVPlan.interp τ f t := by unfold KdVPlan.err; abel
    rw [heq] at hsub
    refine ⟨hsub.1,?_⟩
    linarith [(hv0 t htt).2,(he t htt).2]
  · intro t htt
    have hscale := @yui_aux_0004 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (1/2) (KdVPlan.err τ f v t) (he t htt).1
    have hsub := @yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (v t) (KdVPlan.scale (1/2) (KdVPlan.err τ f v t)) (hv0 t htt).1 hscale.1
    have hc : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
    rw [hc] at hscale
    refine ⟨hsub.1,?_⟩
    linarith [(hv0 t htt).2,(he t htt).2, hsub.2, hscale.2]

theorem yui_aux_0041 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (F : Finset ℤ) (f : KdVPlan.Coeff), (∑ i : F, ‖f i‖^2) = ∑ k ∈ F, ‖f k‖^2" := by
  intro F f
  exact Finset.sum_coe_sort F (fun k : ℤ => ‖f k‖^2)

theorem yui_aux_0042 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (F : Finset ℤ) (f : KdVPlan.Coeff), KdVPlan.MemH 0 f → ‖(WithLp.toLp 2 (fun i : F => f i) : PiLp 2 (fun _ : F => ℂ))‖ ≤ KdVPlan.hn 0 f" := by
  intro F f hf
  have hs : Summable (fun k => ‖f k‖^2) := by simpa only [KdVPlan.MemH,KdVPlan.weight,Real.rpow_zero,one_mul] using hf
  rw [PiLp.norm_eq_of_L2]
  change Real.sqrt (∑ i : F, ‖f i‖^2) ≤ KdVPlan.hn 0 f
  have hb : (∑ i : F, ‖f i‖^2) ≤ ∑' k, ‖f k‖^2 := by
    rw [@yui_aux_0041 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 F f]
    exact hs.sum_le_tsum F (fun k _ => sq_nonneg _)
  simpa only [KdVPlan.hn,KdVPlan.weight,Real.rpow_zero,one_mul] using Real.sqrt_le_sqrt hb

theorem yui_aux_0043 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b C : ℝ) (f : KdVPlan.Path) (F : Finset ℤ), a ≤ b → 0 ≤ C → KdVPlan.UB 0 a b f C → (∀ k ∈ F, IntervalIntegrable (fun t => f t k) volume a b) → (∑ k ∈ F, ‖KdVPlan.timeInt a b f k‖^2) ≤ (C*(b-a))^2" := by
  intro a b C f F hab hC hf hint
  let X : ℝ → PiLp 2 (fun _ : F => ℂ) := fun t => WithLp.toLp 2 (fun i : F => f t i)
  have hi : IntervalIntegrable X volume a b := ⟨Integrable.of_eval_piLp (fun i => (hint i i.property).1), Integrable.of_eval_piLp (fun i => (hint i i.property).2)⟩
  have heval (i : F) : (∫ t in a..b, X t) i = KdVPlan.timeInt a b f i := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : F => ℂ) i).intervalIntegral_comp_comm hi).symm
  have hn : ‖∫ t in a..b, X t‖ ≤ C*(b-a) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq (by rw [abs_of_nonneg (sub_nonneg.mpr hab)])
    intro t ht
    have ht0 : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
    have htt : t ∈ Icc a b := ⟨ht0.1.le,ht0.2⟩
    exact (@yui_aux_0042 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 F (f t) (hf t htt).1).trans (hf t htt).2
  have heq : ‖∫ t in a..b, X t‖^2 = ∑ k ∈ F, ‖KdVPlan.timeInt a b f k‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp_rw [heval]
    exact @yui_aux_0041 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 F (KdVPlan.timeInt a b f)
  rw [← heq]
  have hc : 0 ≤ C*(b-a) := mul_nonneg hC (sub_nonneg.mpr hab)
  nlinarith [norm_nonneg (∫ t in a..b, X t)]

theorem yui_aux_0044 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b C : ℝ) (f : KdVPlan.Path), a ≤ b → 0 ≤ C → KdVPlan.UB 0 a b f C → KdVPlan.HB 0 (KdVPlan.timeInt a b f) (C*(b-a))" := by
  classical
  intro a b C f hab hC hf
  have hfin (F : Finset ℤ) : (∑ k ∈ F, ‖KdVPlan.timeInt a b f k‖^2) ≤ (C*(b-a))^2 := by
    let G := F.filter (fun k => IntervalIntegrable (fun t => f t k) volume a b)
    have hi : ∀ k ∈ G, IntervalIntegrable (fun t => f t k) volume a b := fun k hk => (Finset.mem_filter.mp hk).2
    have heq : (∑ k ∈ F, ‖KdVPlan.timeInt a b f k‖^2) = ∑ k ∈ G, ‖KdVPlan.timeInt a b f k‖^2 := by
      dsimp only [G]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hi : IntervalIntegrable (fun t => f t k) volume a b
      · simp only [if_pos hi]
      · simp only [if_neg hi, KdVPlan.timeInt, intervalIntegral.integral_undef hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    rw [heq]
    exact @yui_aux_0043 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b C f G hab hC hf hi
  have hs : Summable (fun k => ‖KdVPlan.timeInt a b f k‖^2) := summable_of_sum_le (fun k => sq_nonneg _) hfin
  have hb : (∑' k, ‖KdVPlan.timeInt a b f k‖^2) ≤ (C*(b-a))^2 := Real.tsum_le_of_sum_le (fun k => sq_nonneg _) hfin
  refine ⟨by simpa only [KdVPlan.MemH,KdVPlan.weight,Real.rpow_zero,one_mul] using hs, ?_⟩
  calc
    KdVPlan.hn 0 (KdVPlan.timeInt a b f) = Real.sqrt (∑' k, ‖KdVPlan.timeInt a b f k‖^2) := by simp only [KdVPlan.hn,KdVPlan.weight,Real.rpow_zero,one_mul]
    _ ≤ Real.sqrt ((C*(b-a))^2) := Real.sqrt_le_sqrt hb
    _ = C*(b-a) := Real.sqrt_sq (mul_nonneg hC (sub_nonneg.mpr hab))

theorem yui_aux_0045 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N a b : ℝ) (f : KdVPlan.Path), KdVPlan.cutoff N (KdVPlan.timeInt a b f) = KdVPlan.timeInt a b (fun t => KdVPlan.cutoff N (f t)) ∧ KdVPlan.high N (KdVPlan.timeInt a b f) = KdVPlan.timeInt a b (fun t => KdVPlan.high N (f t))" := by
  intro N a b f
  constructor <;> funext k <;> by_cases hk : |(k:ℝ)| ≤ N
  all_goals simp [KdVPlan.cutoff,KdVPlan.high,KdVPlan.timeInt,hk]

theorem yui_aux_0046 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ N : ℝ, 2 ≤ N → KdVPlan.UB 0 a b (fun t => KdVPlan.cutoff N (KdVPlan.errorF a τ f v t)) (C*N^2*(b-a)*KdVPlan.enorm a b τ f v)" := by
  intro M hM
  obtain ⟨C,hC,hB⟩ := @yui_aux_0039 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  refine ⟨C*(M+1),by positivity,?_⟩
  intro τ L f v a b ht ht1 hv hg hE N hN
  let e := KdVPlan.err τ f v
  let g : KdVPlan.Path := fun t => v t-KdVPlan.scale (1/2) (e t)
  let E := KdVPlan.enorm a b τ f v
  have hE0 : 0 ≤ E := by
    apply Real.sSup_nonneg
    rintro x ⟨t,htt,rfl⟩
    exact Real.sqrt_nonneg _
  have he := (@yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg).2
  have hgb := (@yui_aux_0040 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE).2.2
  intro t htt
  change KdVPlan.HB 0 (KdVPlan.cutoff N (KdVPlan.timeInt a t (fun s => KdVPlan.B s (e s) (g s)))) _
  rw [(@yui_aux_0045 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N a t (fun s => KdVPlan.B s (e s) (g s))).1]
  have hint : KdVPlan.UB 0 a t (fun s => KdVPlan.cutoff N (KdVPlan.B s (e s) (g s))) (C*N^2*E*(M+1)) := by
    intro s hst
    have hsb : s ∈ Icc a b := ⟨hst.1,hst.2.trans htt.2⟩
    have hb := hB N s (e s) (g s) (by linarith) (he s hsb).1 (hgb s hsb).1
    refine ⟨hb.1,hb.2.trans ?_⟩
    gcongr
    · exact Real.sqrt_nonneg _
    · exact (he s hsb).2
    · exact (hgb s hsb).2
  have hi := @yui_aux_0044 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a t (C*N^2*E*(M+1)) _ htt.1 (by positivity) hint
  refine ⟨hi.1,hi.2.trans ?_⟩
  calc
    C*N^2*E*(M+1)*(t-a) ≤ C*N^2*E*(M+1)*(b-a) := mul_le_mul_of_nonneg_left (sub_le_sub_right htt.2 a) (by positivity)
    _ = C*(M+1)*N^2*(b-a)*E := by ring

theorem yui_aux_0047 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (p : Finset ℝ) (a b : ℝ) (u d : ℝ → ℂ), a ≤ b → (∀ l r : ℝ, a ≤ l → l ≤ r → r ≤ b → (∀ x ∈ p, x ∉ Ioo l r) → IntervalIntegrable d volume l r ∧ (∫ t in l..r, d t) = u r-u l) → IntervalIntegrable d volume a b ∧ (∫ t in a..b, d t) = u b-u a" := by
  classical
  intro p
  induction p using Finset.induction_on with
  | empty =>
    intro a b u d hab hlocal
    exact hlocal a b le_rfl hab le_rfl (by simp)
  | @insert x p hx ih =>
    intro a b u d hab hlocal
    by_cases hxab : x ∈ Ioo a b
    · have hl := ih a x u d hxab.1.le (by
        intro l r hal hlr hrx hfree
        apply hlocal l r hal hlr (hrx.trans hxab.2.le)
        intro y hy hyint
        rcases Finset.mem_insert.mp hy with rfl | hyp
        · exact (not_lt_of_ge hrx) hyint.2
        · exact hfree y hyp hyint)
      have hr := ih x b u d hxab.2.le (by
        intro l r hxl hlr hrb hfree
        apply hlocal l r (hxab.1.le.trans hxl) hlr hrb
        intro y hy hyint
        rcases Finset.mem_insert.mp hy with rfl | hyp
        · exact (not_lt_of_ge hxl) hyint.1
        · exact hfree y hyp hyint)
      refine ⟨hl.1.trans hr.1,?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hl.1 hr.1,hl.2,hr.2]
      abel
    · apply ih a b u d hab
      intro l r hal hlr hrb hfree
      apply hlocal l r hal hlr hrb
      intro y hy hyint
      rcases Finset.mem_insert.mp hy with rfl | hyp
      · exact hxab ⟨hal.trans_lt hyint.1,hyint.2.trans_le hrb⟩
      · exact hfree y hyp hyint

theorem yui_aux_0048 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (u : ℝ → ℂ), a ≤ b → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (Icc a b) → IntervalIntegrable (deriv u) volume a b ∧ (∫ t in a..b, deriv u t) = u b-u a" := by
  intro a b u hab hu
  have ho : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simpa using @yui_aux_0019 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 1
  have h1 : ContDiffOn ℝ 1 u (Icc a b) := hu.of_le ho
  refine ⟨?_,intervalIntegral.integral_deriv_of_contDiffOn_Icc h1 hab⟩
  rcases hab.eq_or_lt with rfl | hlt
  · exact IntervalIntegrable.refl
  · have hc := (h1.derivWithin (m := 0) (uniqueDiffOn_Icc hlt) (by simp)).continuousOn
    apply (hc.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
    simp only [uIoc_of_le hab]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

theorem yui_aux_0049 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Path), a ≤ b → KdVPlan.Piecewise a b f → (∀ k, IntervalIntegrable (fun t => KdVPlan.dt f t k) volume a b) ∧ KdVPlan.timeInt a b (KdVPlan.dt f) = f b-f a" := by
  intro a b f hab hf
  obtain ⟨p,hp⟩ := hf.2
  have hcalc (k : ℤ) : IntervalIntegrable (fun t => KdVPlan.dt f t k) volume a b ∧ (∫ t in a..b, KdVPlan.dt f t k) = f b k-f a k := by
    apply @yui_aux_0047 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 p a b (fun t => f t k) (fun t => KdVPlan.dt f t k) hab
    intro l r hal hlr hrb hfree
    rcases hlr.eq_or_lt with rfl | hlt
    · simp only [intervalIntegral.integral_same,sub_self,and_true]
      exact IntervalIntegrable.refl
    · exact @yui_aux_0048 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l r (fun t => f t k) hlr ((hp l r hal hlt hrb hfree).1 k)
  refine ⟨fun k => (hcalc k).1,?_⟩
  funext k
  exact (hcalc k).2

theorem yui_aux_0050 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f g : KdVPlan.Coeff) (k : ℤ), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → Summable (fun j : ℤ => f j*g (k-j))" := by
  intro f g k hf hg
  have hf2 : Summable (fun j => ‖f j‖^2) := by simpa only [KdVPlan.MemH,KdVPlan.weight,Real.rpow_zero,one_mul] using hf
  have hg2 : Summable (fun j => ‖g j‖^2) := by simpa only [KdVPlan.MemH,KdVPlan.weight,Real.rpow_zero,one_mul] using hg
  have hg2' : Summable (fun j : ℤ => ‖g (k-j)‖^2) := (Equiv.subLeft k).summable_iff.mpr hg2
  apply Summable.of_norm
  apply ((hf2.add hg2').div_const 2).of_nonneg_of_le (fun j => norm_nonneg _)
  intro j
  rw [norm_mul]
  nlinarith [sq_nonneg (‖f j‖-‖g (k-j)‖)]

theorem yui_aux_0051 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f g : KdVPlan.Coeff, KdVPlan.mul f g = KdVPlan.mul g f ∧ ∀ c : ℂ, KdVPlan.mul (KdVPlan.scale c f) g = KdVPlan.scale c (KdVPlan.mul f g) ∧ KdVPlan.mul f (KdVPlan.scale c g) = KdVPlan.scale c (KdVPlan.mul f g)" := by
  intro f g
  have hcomm (u w : KdVPlan.Coeff) : KdVPlan.mul u w = KdVPlan.mul w u := by
    funext k
    unfold KdVPlan.mul
    rw [← (Equiv.subLeft k).tsum_eq (fun j : ℤ => w j*u (k-j))]
    simp only [Equiv.subLeft_apply,sub_sub_cancel,mul_comm]
  refine ⟨hcomm f g,?_⟩
  intro c
  have hl (u w : KdVPlan.Coeff) : KdVPlan.mul (KdVPlan.scale c u) w = KdVPlan.scale c (KdVPlan.mul u w) := by
    funext k
    simp only [KdVPlan.mul,KdVPlan.scale,mul_assoc,tsum_mul_left]
  refine ⟨hl f g,?_⟩
  rw [hcomm f (KdVPlan.scale c g),hl g f,hcomm g f]

theorem yui_aux_0052 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f f' g : KdVPlan.Coeff, KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.mul (f+f') g = KdVPlan.mul f g+KdVPlan.mul f' g ∧ KdVPlan.mul (f-f') g = KdVPlan.mul f g-KdVPlan.mul f' g" := by
  intro f f' g hf hf' hg
  constructor <;> funext k
  · simp only [KdVPlan.mul,Pi.add_apply,add_mul]
    exact ( (@yui_aux_0050 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 f g k hf hg).tsum_add (@yui_aux_0050 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 f' g k hf' hg))
  · simp only [KdVPlan.mul,Pi.sub_apply,sub_mul]
    exact ( (@yui_aux_0050 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 f g k hf hg).tsum_sub (@yui_aux_0050 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 f' g k hf' hg))

theorem yui_aux_0053 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ t : ℝ, ∃ LS LD LI LP : KdVPlan.Coeff →ₗ[ℂ] KdVPlan.Coeff, (∀ f, LS f = KdVPlan.S t f) ∧ (∀ f, LD f = KdVPlan.dx f) ∧ (∀ f, LI f = KdVPlan.invD f) ∧ (∀ f, LP f = KdVPlan.P f)" := by
  intro t
  let LS : KdVPlan.Coeff →ₗ[ℂ] KdVPlan.Coeff :=
    { toFun := KdVPlan.S t
      map_add' := by intro f g; funext k; simp [KdVPlan.S,mul_add]
      map_smul' := by intro c f; funext k; simp [KdVPlan.S,mul_left_comm] }
  let LD : KdVPlan.Coeff →ₗ[ℂ] KdVPlan.Coeff :=
    { toFun := KdVPlan.dx
      map_add' := by intro f g; funext k; simp [KdVPlan.dx,mul_add]
      map_smul' := by intro c f; funext k; simp [KdVPlan.dx,mul_left_comm] }
  let LI : KdVPlan.Coeff →ₗ[ℂ] KdVPlan.Coeff :=
    { toFun := KdVPlan.invD
      map_add' := by intro f g; funext k; by_cases hk : k=0 <;> simp [KdVPlan.invD,hk,mul_add]
      map_smul' := by intro c f; funext k; by_cases hk : k=0 <;> simp [KdVPlan.invD,hk,mul_left_comm] }
  let LP : KdVPlan.Coeff →ₗ[ℂ] KdVPlan.Coeff :=
    { toFun := KdVPlan.P
      map_add' := by intro f g; funext k; by_cases hk : k=0 <;> simp [KdVPlan.P,hk]
      map_smul' := by intro c f; funext k; by_cases hk : k=0 <;> simp [KdVPlan.P,hk] }
  exact ⟨LS,LD,LI,LP,fun f=>rfl,fun f=>rfl,fun f=>rfl,fun f=>rfl⟩

theorem yui_aux_0054 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f f' g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.B t (f+f') g = KdVPlan.B t f g+KdVPlan.B t f' g ∧ KdVPlan.B t (f-f') g = KdVPlan.B t f g-KdVPlan.B t f' g" := by
  intro t f f' g hf hf' hg
  obtain ⟨Sp,Dp,Ip,Pp,hSp,_,_,_⟩ := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t
  obtain ⟨Sm,Dm,Im,Pm,hSm,hD,_,_⟩ := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-t)
  let A := Sm.comp Dm
  have hA (u : KdVPlan.Coeff) : A u = KdVPlan.S (-t) (KdVPlan.dx u) := by change Sm (Dm u) = _; rw [hD,hSm]
  have hB (u w : KdVPlan.Coeff) : KdVPlan.B t u w = A (KdVPlan.mul (Sp u) (Sp w)) := by rw [hA,hSp,hSp]; rfl
  have hfp : KdVPlan.MemH 0 (Sp f) := by rw [hSp]; exact (@yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 t f hf).1
  have hfp' : KdVPlan.MemH 0 (Sp f') := by rw [hSp]; exact (@yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 t f' hf').1
  have hgp : KdVPlan.MemH 0 (Sp g) := by rw [hSp]; exact (@yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 t g hg).1
  have hm := @yui_aux_0052 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (Sp f) (Sp f') (Sp g) hfp hfp' hgp
  constructor
  · rw [hB,Sp.map_add,hm.1,A.map_add,← hB,← hB]
  · rw [hB,Sp.map_sub,hm.2,A.map_sub,← hB,← hB]

theorem yui_aux_0055 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.B t f g = KdVPlan.B t g f ∧ ∀ c : ℂ, KdVPlan.B t (KdVPlan.scale c f) g = KdVPlan.scale c (KdVPlan.B t f g) ∧ KdVPlan.B t f (KdVPlan.scale c g) = KdVPlan.scale c (KdVPlan.B t f g)" := by
  intro t f g
  have hc (u w : KdVPlan.Coeff) : KdVPlan.B t u w = KdVPlan.B t w u := by
    unfold KdVPlan.B
    rw [(@yui_aux_0051 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (KdVPlan.S t u) (KdVPlan.S t w)).1]
  obtain ⟨Sp,Dp,Ip,Pp,hSp,_,_,_⟩ := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t
  obtain ⟨Sm,Dm,Im,Pm,hSm,hD,_,_⟩ := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-t)
  let A := Sm.comp Dm
  have hA (u : KdVPlan.Coeff) : A u = KdVPlan.S (-t) (KdVPlan.dx u) := by change Sm (Dm u) = _; rw [hD,hSm]
  have hB (u w : KdVPlan.Coeff) : KdVPlan.B t u w = A (KdVPlan.mul (Sp u) (Sp w)) := by rw [hA,hSp,hSp]; rfl
  have hs (c : ℂ) (u w : KdVPlan.Coeff) : KdVPlan.B t (KdVPlan.scale c u) w = KdVPlan.scale c (KdVPlan.B t u w) := by
    change KdVPlan.B t (c • u) w = c • KdVPlan.B t u w
    rw [hB,Sp.map_smul,hB]
    change A (KdVPlan.mul (KdVPlan.scale c (Sp u)) (Sp w)) = c • A (KdVPlan.mul (Sp u) (Sp w))
    rw [(@yui_aux_0051 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (Sp u) (Sp w)).2 c |>.1]
    exact A.map_smul c _
  refine ⟨hc f g,?_⟩
  intro c
  refine ⟨hs c f g,?_⟩
  rw [hc f (KdVPlan.scale c g),hs c g f,hc g f]

theorem yui_aux_0056 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (u w : KdVPlan.Coeff), KdVPlan.MemH 0 u → KdVPlan.MemH 0 w → KdVPlan.B t (u-w) (u-KdVPlan.scale (1/2) (u-w)) = KdVPlan.scale (1/2) (KdVPlan.B t u u)-KdVPlan.scale (1/2) (KdVPlan.B t w w)" := by
  intro t u w hu hw
  let addB := @yui_aux_0054 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  let symB := @yui_aux_0055 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have he := (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 u w hu hw).1
  have hg : u-KdVPlan.scale (1/2) (u-w) = KdVPlan.scale (1/2) (u+w) := by
    funext k
    simp only [KdVPlan.scale,Pi.add_apply,Pi.sub_apply]
    ring
  rw [hg,(symB t (u-w) (u+w)).2 (1/2) |>.2]
  rw [(symB t (u-w) (u+w)).1,(addB t u w (u-w) hu hw he).1]
  rw [(symB t u (u-w)).1,(symB t w (u-w)).1]
  rw [(addB t u w u hu hw hu).2,(addB t u w w hu hw hw).2]
  rw [(symB t w u).1]
  funext k
  simp only [KdVPlan.scale,Pi.add_apply,Pi.sub_apply]
  ring

theorem yui_aux_0057 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (μ : Measure ℝ) (c : ℝ) (f : KdVPlan.Path) (k : ℤ), AEStronglyMeasurable (fun t => f t k) μ → AEStronglyMeasurable (fun t => KdVPlan.S (c*t) (f t) k) μ" := by
  intro μ c f k hf
  have hp : AEStronglyMeasurable (fun t : ℝ => Complex.exp (Complex.I*(((c*t)*(k:ℝ)^3 : ℝ):ℂ))) μ := (by fun_prop : Continuous (fun t : ℝ => Complex.exp (Complex.I*(((c*t)*(k:ℝ)^3 : ℝ):ℂ)))).aestronglyMeasurable
  have hh := hp.mul hf
  change AEStronglyMeasurable (fun t : ℝ => Complex.exp (Complex.I*(((c*t)*(k:ℝ)^3 : ℝ):ℂ))*f t k) μ at hh
  change AEStronglyMeasurable (fun t : ℝ => Complex.exp (Complex.I*(((c*t)*(k:ℝ)^3 : ℝ):ℂ))*f t k) μ
  exact hh

theorem yui_aux_0058 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (μ : Measure ℝ) (f g : KdVPlan.Path), (∀ k, AEStronglyMeasurable (fun t => f t k) μ) → (∀ k, AEStronglyMeasurable (fun t => g t k) μ) → ∀ k, AEStronglyMeasurable (fun t => KdVPlan.B t (f t) (g t) k) μ" := by
  intro μ f g hf hg
  have hsf (k : ℤ) : AEStronglyMeasurable (fun t => KdVPlan.S t (f t) k) μ := by
    have hh := @yui_aux_0057 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 μ 1 f k (hf k)
    simpa only [one_mul] using hh
  have hsg (k : ℤ) : AEStronglyMeasurable (fun t => KdVPlan.S t (g t) k) μ := by
    have hh := @yui_aux_0057 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 μ 1 g k (hg k)
    simpa only [one_mul] using hh
  have hmul (k : ℤ) : AEStronglyMeasurable (fun t => KdVPlan.mul (KdVPlan.S t (f t)) (KdVPlan.S t (g t)) k) μ := AEStronglyMeasurable.tsum (fun j : ℤ => (hsf j).mul (hsg (k-j)))
  let h : KdVPlan.Path := fun t => KdVPlan.dx (KdVPlan.mul (KdVPlan.S t (f t)) (KdVPlan.S t (g t)))
  have hmeas (k : ℤ) : AEStronglyMeasurable (fun t => h t k) μ := by
    change AEStronglyMeasurable (fun t => Complex.I*(k:ℂ)*KdVPlan.mul (KdVPlan.S t (f t)) (KdVPlan.S t (g t)) k) μ
    exact (hmul k).const_mul (Complex.I*(k:ℂ))
  intro k
  have hh := @yui_aux_0057 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 μ (-1) h k (hmeas k)
  change AEStronglyMeasurable (fun t => KdVPlan.S (-t) (h t) k) μ
  simpa only [neg_one_mul] using hh

theorem yui_aux_0059 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (k : ℤ), KdVPlan.MemH s f → ‖f k‖ ≤ KdVPlan.weight (-s/2) k * KdVPlan.hn s f" := by
  intro s f k hf
  obtain ⟨x,rfl⟩ := (h_T013.1 s f).mp hf
  rw [h_T013.2.1]
  change ‖(KdVPlan.weight (-s/2) k : ℂ)*x k‖ ≤ KdVPlan.weight (-s/2) k*‖x‖
  have hw : 0 < KdVPlan.weight (-s/2) k := Real.rpow_pos_of_pos (by positivity) _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) x k) hw.le

theorem yui_aux_0060 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (f : KdVPlan.Path), a ≤ b → (∀ k, AEStronglyMeasurable (fun t => f t k) (volume.restrict (Icc a b))) → KdVPlan.UB s a b f C → ∀ k, IntervalIntegrable (fun t => f t k) volume a b" := by
  intro s a b C f hab hm hf k
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply Integrable.of_bound (hm k) (KdVPlan.weight (-s/2) k*C)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hw : 0 ≤ KdVPlan.weight (-s/2) k := Real.rpow_nonneg (by positivity) _
  exact (@yui_aux_0059 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s (f t) k (hf t ht).1).trans (mul_le_mul_of_nonneg_left (hf t ht).2 hw)

theorem yui_aux_0061 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b C D : ℝ) (f g : KdVPlan.Path), a ≤ b → 0 ≤ C → 0 ≤ D → (∀ k, AEStronglyMeasurable (fun t => f t k) (volume.restrict (Icc a b))) → (∀ k, AEStronglyMeasurable (fun t => g t k) (volume.restrict (Icc a b))) → KdVPlan.UB 0 a b f C → KdVPlan.UB 0 a b g D → ∀ k, IntervalIntegrable (fun t => KdVPlan.B t (f t) (g t) k) volume a b" := by
  intro a b C D f g hab hC hD hm hn hf hg
  obtain ⟨Cb,hCb,_,_,hB,_⟩ := h_T005.1.1
  have hmeas := @yui_aux_0058 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (volume.restrict (Icc a b)) f g hm hn
  apply @yui_aux_0060 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-KdVPlan.pstar) a b (Cb*C*D) (fun t => KdVPlan.B t (f t) (g t)) hab hmeas
  intro t ht
  have hh := (hB t (f t) (g t) (hf t ht).1 (hg t ht).1).1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hprod := mul_le_mul (hf t ht).2 (hg t ht).2 (Real.sqrt_nonneg _) hC
  nlinarith [mul_le_mul_of_nonneg_left hprod hCb.le]

theorem yui_aux_0062 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → ∀ k, ContinuousOn (fun t => f t k) (Icc a b)" := by
  intro s a b f hf k
  obtain ⟨W,hW,_⟩ := @yui_aux_0011 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s
  have hc := @yui_aux_0012 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f W hW hf
  have hp : ContinuousOn (fun t => (W (f t)) k) (Icc a b) := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous.comp_continuousOn hc
  have hcp : ContinuousOn (fun t => (KdVPlan.weight (-s/2) k : ℂ)*(W (f t)) k) (Icc a b) := continuousOn_const.mul hp
  apply hcp.congr
  intro t ht
  exact (congrFun (hW _ (hf.1 t ht)) k).symm

theorem yui_aux_0063 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (n : ℕ) (t : ℝ), 0 < τ → (n:ℝ)*τ ≤ t → t < ((n:ℝ)+1)*τ → KdVPlan.gridIndex τ t = n" := by
  intro τ n t ht hlow hupp
  have hn : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg n) ht.le).trans hlow
  apply (Nat.floor_eq_iff (div_nonneg hn ht.le)).mpr
  exact ⟨(le_div_iff₀ ht).mpr hlow,(div_lt_iff₀ ht).mpr hupp⟩

theorem yui_aux_0064 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff) (n : ℕ) (t : ℝ), 0 < τ → t ∈ Ioo ((n:ℝ)*τ) (((n:ℝ)+1)*τ) → KdVPlan.interp τ f t = KdVPlan.Vst ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) t ∧ KdVPlan.dt (KdVPlan.interp τ f) t = KdVPlan.dt (KdVPlan.Vst ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t ∧ KdVPlan.dt (KdVPlan.residual τ f) t = KdVPlan.dt (KdVPlan.rho ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t" := by
  intro τ f n t ht htt
  have hloc : ∀ᶠ r in nhds t, KdVPlan.gridIndex τ r = n := by
    filter_upwards [Ioo_mem_nhds htt.1 htt.2] with r hr
    exact @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ n r ht hr.1.le hr.2
  have hidx := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ n t ht htt.1.le htt.2
  refine ⟨by simp only [KdVPlan.interp,hidx],?_,?_⟩
  · funext k
    change deriv (fun r => KdVPlan.interp τ f r k) t = _
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hloc] with r hr
    simp only [KdVPlan.interp,hr]
  · funext k
    let c : ℂ := (∑ j ∈ Finset.range n, KdVPlan.rho ((j:ℝ)*τ) τ (KdVPlan.twistedNum τ f j) (((j:ℝ)+1)*τ)) k
    have he : (fun r => KdVPlan.residual τ f r k) =ᶠ[nhds t] (fun r => c+KdVPlan.rho ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) r k) := by
      filter_upwards [hloc] with r hr
      simp only [KdVPlan.residual,hr,Pi.add_apply]
      rfl
    change deriv (fun r => KdVPlan.residual τ f r k) t = _
    rw [he.deriv_eq,deriv_const_add]
    rfl

theorem yui_aux_0065 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (L : ℕ) (a b t : ℝ), 0 < τ → KdVPlan.GridInterval τ L a b → t ∈ Icc a b → let n := KdVPlan.gridIndex τ t; n ≤ L ∧ (n:ℝ)*τ ∈ Icc a b ∧ t ∈ Ico ((n:ℝ)*τ) (((n:ℝ)+1)*τ)" := by
  intro τ L a b t ht hg htt
  let n := KdVPlan.gridIndex τ t
  have ht0 : 0 ≤ t := hg.1.trans htt.1
  have hlo : (n:ℝ)*τ ≤ t := (le_div_iff₀ ht).mp (Nat.floor_le (div_nonneg ht0 ht.le))
  have hhi : t < ((n:ℝ)+1)*τ := (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (t/τ))
  have hnL : n ≤ L := by
    have hdiv : t/τ ≤ (L:ℝ) := (div_le_iff₀ ht).mpr (htt.2.trans hg.2.2.1)
    have hh := Nat.floor_mono hdiv
    change ⌊t/τ⌋₊ ≤ L
    simpa only [Nat.floor_natCast] using hh
  obtain ⟨m,hmL,ham⟩ := hg.2.2.2
  have hma : KdVPlan.gridIndex τ a = m := by
    apply @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ m a ht
    · exact ham.ge
    · rw [ham]
      nlinarith
  have hmn : m ≤ n := by
    rw [← hma]
    exact Nat.floor_mono (div_le_div_of_nonneg_right htt.1 ht.le)
  have hcast : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have has : a ≤ (n:ℝ)*τ := by rw [ham]; exact mul_le_mul_of_nonneg_right hcast ht.le
  exact ⟨hnL,⟨has,hlo.trans htt.2⟩,⟨hlo,hhi⟩⟩

theorem yui_aux_0066 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ᵐ t ∂(volume.restrict (Icc a b)), let n := KdVPlan.gridIndex τ t; let fn := KdVPlan.twistedNum τ f n; KdVPlan.dt (KdVPlan.interp τ f) t = KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.interp τ f t) (KdVPlan.interp τ f t))+KdVPlan.dt (KdVPlan.residual τ f) t ∧ KdVPlan.dt (KdVPlan.residual τ f) t = -KdVPlan.B t (KdVPlan.Yst ((n:ℝ)*τ) τ fn t) (KdVPlan.z ((n:ℝ)*τ) fn t)-KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.Yst ((n:ℝ)*τ) τ fn t) (KdVPlan.Yst ((n:ℝ)*τ) τ fn t))-KdVPlan.scale ((τ:ℂ)⁻¹) (KdVPlan.Wst ((n:ℝ)*τ) τ fn)" := by
  intro M τ L f v a b hM ht ht1 hv hg hE
  obtain ⟨C,hC,hstep,_⟩ := h_T009 M hM
  have hnot : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∉ Set.range (fun n : ℕ => (n:ℝ)*τ) := (Set.countable_range _).ae_notMem _
  filter_upwards [ae_restrict_mem measurableSet_Icc,hnot] with t htt hnt
  let n := KdVPlan.gridIndex τ t
  have hn := @yui_aux_0065 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ L a b t ht hg htt
  have hs := @yui_aux_0030 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE n hn.1 hn.2.1
  have hstrict : (n:ℝ)*τ < t := lt_of_le_of_ne hn.2.2.1 (by intro he; exact hnt ⟨n,he⟩)
  have hlocal := @yui_aux_0064 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ f n t ht ⟨hstrict,hn.2.2.2⟩
  have hcell : t ∈ Ioo ((n:ℝ)*τ) ((n:ℝ)*τ+τ) := ⟨hstrict,by nlinarith [hn.2.2.2]⟩
  have heq := (hstep ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) (v ((n:ℝ)*τ)) hs).1 t hcell
  constructor
  · rw [hlocal.2.1,hlocal.1,hlocal.2.2]
    exact heq.1
  · rw [hlocal.2.2]
    exact heq.2

theorem yui_aux_0067 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Path), KdVPlan.Piecewise a b f → ∀ᵐ t ∂(volume.restrict (Icc a b)), (∀ k, DifferentiableAt ℝ (fun r => f r k) t) ∧ KdVPlan.Smooth (KdVPlan.dt f t)" := by
  intro a b f hf
  obtain ⟨p,hp⟩ := hf.2
  have hIoo : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ Ioo a b := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hnot : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∉ (p : Set ℝ) := p.countable_toSet.ae_notMem _
  filter_upwards [hIoo,hnot] with t htt hnt
  have hnbhd : Ioo a b ∩ (p : Set ℝ)ᶜ ∈ nhds t := inter_mem (Ioo_mem_nhds htt.1 htt.2) (p.finite_toSet.isClosed.isOpen_compl.mem_nhds hnt)
  obtain ⟨l,r,hlt,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnbhd
  let l' := (l+t)/2
  let r' := (t+r)/2
  have hll : l < l' := by dsimp [l']; linarith [hlt.1]
  have hlt' : l' < t := by dsimp [l']; linarith [hlt.1]
  have htr' : t < r' := by dsimp [r']; linarith [hlt.2]
  have hrr : r' < r := by dsimp [r']; linarith [hlt.2]
  have hlmem : l' ∈ Ioo a b := (hs ⟨hll,hlt'.trans hlt.2⟩).1
  have hrmem : r' ∈ Ioo a b := (hs ⟨hlt.1.trans htr',hrr⟩).1
  have hfree : ∀ x ∈ p, x ∉ Ioo l' r' := by
    intro x hxp hx
    exact (hs ⟨hll.trans hx.1,hx.2.trans hrr⟩).2 hxp
  have hsm := hp l' r' hlmem.1.le (hlt'.trans htr') hrmem.2.le hfree
  have htn : t ∈ Icc l' r' := ⟨hlt'.le,htr'.le⟩
  refine ⟨?_,?_⟩
  · intro k
    have h1 : ContDiffWithinAt ℝ 1 (fun r => f r k) (Icc l' r') t := (hsm.1 k t htn).of_le (by simpa using @yui_aux_0019 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 1)
    exact (h1.differentiableWithinAt one_ne_zero).differentiableAt (Icc_mem_nhds hlt' htr')
  · intro m
    have heq : (fun k => iteratedDerivWithin 1 (fun r => f r k) (Icc l' r') t) = KdVPlan.dt f t := by
      funext k
      rw [iteratedDerivWithin_one,derivWithin_of_mem_nhds (Icc_mem_nhds hlt' htr')]
      rfl
    rw [← heq]
    exact (hsm.2 m 1).1 t htn

theorem yui_aux_0068 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ᵐ t ∂(volume.restrict (Icc a b)), let e := KdVPlan.err τ f v; let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s); KdVPlan.dt e t = KdVPlan.B t (e t) (g t)-KdVPlan.dt (KdVPlan.residual τ f) t ∧ KdVPlan.dt g t = KdVPlan.scale (1/2) (KdVPlan.B t (v t) (v t))-KdVPlan.scale (1/2) (KdVPlan.B t (e t) (g t))+KdVPlan.scale (1/2) (KdVPlan.dt (KdVPlan.residual τ f) t)" := by
  intro M τ L f v a b hM ht ht1 hv hg hE
  obtain ⟨C,hC,_,hacc⟩ := h_T009 M hM
  have ha := hacc τ L f v ht ht1 hv
  have pv := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v hv.2.2.1
  have pvl := @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) a b v hg.1 hg.2.2.1 pv
  have pil := @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) a b (KdVPlan.interp τ f) hg.1 hg.2.2.1 ha.1
  have hdv := @yui_aux_0067 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b v pvl
  have hdi := @yui_aux_0067 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (KdVPlan.interp τ f) pil
  have hlocal := @yui_aux_0066 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE
  have hbounds := @yui_aux_0040 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE
  have hIoo : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ Ioo a b := by rw [← restrict_Ioo_eq_restrict_Icc]; exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hdv,hdi,hlocal,hIoo] with t hdv hdi hlocal htt
  let e := KdVPlan.err τ f v
  let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s)
  have httc : t ∈ Icc a b := ⟨htt.1.le,htt.2.le⟩
  have hvt := hv.2.2.2.2.2 t ⟨hg.1.trans_lt htt.1,htt.2.trans_le hg.2.2.1⟩
  have hde (k : ℤ) : DifferentiableAt ℝ (fun r => e r k) t := (hdv.1 k).sub (hdi.1 k)
  have hdt : KdVPlan.dt e t = KdVPlan.dt v t-KdVPlan.dt (KdVPlan.interp τ f) t := by
    funext k
    exact deriv_sub (hdv.1 k) (hdi.1 k)
  have hpol : KdVPlan.B t (e t) (g t) = KdVPlan.scale (1/2) (KdVPlan.B t (v t) (v t))-KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.interp τ f t) (KdVPlan.interp τ f t)) := @yui_aux_0056 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t (v t) (KdVPlan.interp τ f t) (hbounds.1 t httc).1 (hbounds.2.1 t httc).1
  have he : KdVPlan.dt e t = KdVPlan.B t (e t) (g t)-KdVPlan.dt (KdVPlan.residual τ f) t := by
    rw [hdt,hvt,hlocal.1,hpol]
    abel
  refine ⟨he,?_⟩
  have hdg : KdVPlan.dt g t = KdVPlan.dt v t-KdVPlan.scale (1/2) (KdVPlan.dt e t) := by
    funext k
    exact ((hdv.1 k).hasDerivAt.sub ((hde k).hasDerivAt.const_mul (1/2:ℂ))).deriv
  rw [hdg,hvt,he]
  funext k
  simp only [KdVPlan.scale,Pi.add_apply,Pi.sub_apply]
  ring

theorem yui_aux_0069 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ x y z : ℝ, x ≤ y → z+x ≤ z+y" := by
  intro x y z hxy
  exact add_le_add le_rfl hxy

theorem yui_aux_0070 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → ∀ n : ℕ, n ≤ L → (n:ℝ)*τ ∈ Icc a b → KdVPlan.localQ gamma τ (KdVPlan.twistedNum τ f n) (v ((n:ℝ)*τ)) ≤ τ^gamma+KdVPlan.enorm a b τ f v" := by
  intro M τ L f v a b hM ht ht1 hv hg n hn hni
  obtain ⟨C,hC,_,hacc⟩ := h_T009 M hM
  have ha := hacc τ L f v ht ht1 hv
  have hgrid := ha.2.2.2.2.1 n hn
  have he := (@yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg).2 _ hni
  change τ^gamma+KdVPlan.hn 0 (KdVPlan.twistedNum τ f n-v ((n:ℝ)*τ)) ≤ _
  apply @yui_aux_0069 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 _ _ (τ^gamma)
  rw [@yui_aux_0032 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (KdVPlan.twistedNum τ f n) (v ((n:ℝ)*τ))]
  have heq : KdVPlan.err τ f v ((n:ℝ)*τ) = v ((n:ℝ)*τ)-KdVPlan.twistedNum τ f n := by unfold KdVPlan.err; rw [hgrid]
  rw [← heq]
  exact he.2

theorem yui_aux_0071 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M a τ : ℝ) (f w : KdVPlan.Coeff), KdVPlan.StepData gamma M a τ f w → ∀ k, IntervalIntegrable (fun t => KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.z a f t) k) volume a (a+τ) ∧ IntervalIntegrable (fun t => KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.Yst a τ f t) k) volume a (a+τ)" := by
  intro M a τ f w hs
  obtain ⟨C,hC,hlocal⟩ := h_T008 M hs.1
  have hl := hlocal a τ f w hs
  rcases hs with ⟨hM,ha,ht,ht1,hf,hw,hsf,hsw,hwn,hen⟩
  rcases hl with ⟨hfn,hq,hF,hFd,hag,hz,hzx,hFF,hQW,hiBF,hdY,hiY,hidY,hCst,hY,hYX,hYnorm,hYneg⟩
  let q := KdVPlan.localQ gamma τ f w
  have hq0 : 0 ≤ q := add_nonneg (Real.rpow_nonneg ht.le _) (Real.sqrt_nonneg _)
  have hzUB : KdVPlan.UB 0 a (a+τ) (KdVPlan.z a f) (M+1+C) := by
    intro t htt
    have hFt := hF t htt
    have hF0 := h_T013.2.2.2.1 0 1 (KdVPlan.F a f t) (by norm_num) hFt.1
    have hsum := @yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 f (KdVPlan.F a f t) hf.1 hF0.1
    refine ⟨hsum.1,?_⟩
    change KdVPlan.hn 0 (f+KdVPlan.F a f t) ≤ M+1+C
    linarith [hsum.2,hF0.2,hFt.2]
  have hi1 := @yui_aux_0061 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a (a+τ) (C*q) (M+1+C) (KdVPlan.Yst a τ f) (KdVPlan.z a f) (by linarith) (by positivity) (by positivity) hYX.2.1.1 hz.2.1.1 hY hzUB
  have hi2 := @yui_aux_0061 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a (a+τ) (C*q) (C*q) (KdVPlan.Yst a τ f) (KdVPlan.Yst a τ f) (by linarith) (by positivity) (by positivity) hYX.2.1.1 hYX.2.1.1 hY hY
  exact fun k => ⟨hi1 k,hi2 k⟩

theorem yui_aux_0072 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (l r : ℝ) (p q : ℝ → ℂ) (c W : ℂ), IntervalIntegrable p volume l r → IntervalIntegrable q volume l r → IntervalIntegrable (fun t => -p t-c*q t-W) volume l r ∧ (∫ t in l..r, -p t-c*q t-W) = -(∫ t in l..r, p t)-c*(∫ t in l..r, q t)-(r-l) • W" := by
  intro l r p q c W hp hq
  have hneg : IntervalIntegrable (fun t => -p t) volume l r := hp.neg
  have hhalf : IntervalIntegrable (fun t => c*q t) volume l r := hq.const_mul c
  have hpq : IntervalIntegrable (fun t => -p t-c*q t) volume l r := hneg.sub hhalf
  have hc : IntervalIntegrable (fun _ : ℝ => W) volume l r := intervalIntegrable_const
  refine ⟨hpq.sub hc,?_⟩
  rw [intervalIntegral.integral_sub hpq hc,intervalIntegral.integral_sub hneg hhalf,intervalIntegral.integral_neg,intervalIntegral.integral_const_mul,intervalIntegral.integral_const]

theorem yui_aux_0073 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ r a τ : ℝ, (((r-a)/τ : ℝ) : ℂ) = ((r:ℂ)-(a:ℂ))*(τ:ℂ)⁻¹" := by
  intro r a τ
  push_cast
  rfl

theorem yui_aux_0074 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a l r τ : ℝ) (p q : ℝ → ℂ) (W : ℂ), IntervalIntegrable p volume a l → IntervalIntegrable p volume l r → IntervalIntegrable q volume a l → IntervalIntegrable q volume l r → let d : ℝ → ℂ := fun t => -p t-(1/2:ℂ)*q t-(τ:ℂ)⁻¹*W; IntervalIntegrable d volume l r ∧ (∫ t in l..r, d t) = (-(∫ t in a..r, p t)-(1/2:ℂ)*(∫ t in a..r, q t)-(((r-a)/τ:ℝ):ℂ)*W)-(-(∫ t in a..l, p t)-(1/2:ℂ)*(∫ t in a..l, q t)-(((l-a)/τ:ℝ):ℂ)*W)" := by
  intro a l r τ p q W hpal hplr hqal hqlr
  have hi := @yui_aux_0072 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l r p q (1/2) ((τ:ℂ)⁻¹*W) hplr hqlr
  refine ⟨hi.1,hi.2.trans ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpal hplr,← intervalIntegral.integral_add_adjacent_intervals hqal hqlr]
  rw [@yui_aux_0073 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 r a τ,@yui_aux_0073 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l a τ]
  simp only [Complex.real_smul,Complex.ofReal_sub]
  ring

theorem yui_aux_0075 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M a τ : ℝ) (f w : KdVPlan.Coeff), KdVPlan.StepData gamma M a τ f w → ∀ l r : ℝ, a ≤ l → l ≤ r → r ≤ a+τ → ∀ k, IntervalIntegrable (fun t => KdVPlan.dt (KdVPlan.rho a τ f) t k) volume l r ∧ (∫ t in l..r, KdVPlan.dt (KdVPlan.rho a τ f) t k) = KdVPlan.rho a τ f r k-KdVPlan.rho a τ f l k" := by
  intro M a τ f w hs l r hal hlr hrb k
  obtain ⟨C,hC,hstep,_⟩ := h_T009 M hs.1
  have hres := hstep a τ f w hs
  have hint := @yui_aux_0071 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M a τ f w hs k
  have hab : a ≤ a+τ := by linarith [hs.2.2.1]
  have hsubal : uIcc a l ⊆ uIcc a (a+τ) := by
    rw [uIcc_of_le hal,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl (hlr.trans hrb)
  have hsublr : uIcc l r ⊆ uIcc a (a+τ) := by
    rw [uIcc_of_le hlr,uIcc_of_le hab]
    exact Icc_subset_Icc hal hrb
  let p : ℝ → ℂ := fun t => KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.z a f t) k
  let q : ℝ → ℂ := fun t => KdVPlan.B t (KdVPlan.Yst a τ f t) (KdVPlan.Yst a τ f t) k
  let W := KdVPlan.Wst a τ f k
  let d : ℝ → ℂ := fun t => -p t-(1/2:ℂ)*q t-(τ:ℂ)⁻¹*W
  have hi := @yui_aux_0074 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a l r τ p q W (hint.1.mono_set hsubal) (hint.1.mono_set hsublr) (hint.2.mono_set hsubal) (hint.2.mono_set hsublr)
  have heq : d =ᵐ[volume.restrict (uIoc l r)] (fun t => KdVPlan.dt (KdVPlan.rho a τ f) t k) := by
    rw [uIoc_of_le hlr,← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htt
    have htt' : t ∈ Ioo a (a+τ) := ⟨hal.trans_lt htt.1,htt.2.trans_le hrb⟩
    exact (congrFun ((hres.1 t htt').2) k).symm
  have hprim : (∫ t in l..r, d t) = KdVPlan.rho a τ f r k-KdVPlan.rho a τ f l k := hi.2
  exact ⟨hi.1.congr_ae heq,(intervalIntegral.integral_congr_ae_restrict heq.symm).trans hprim⟩

theorem yui_aux_0076 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a τ : ℝ) (f : KdVPlan.Coeff), KdVPlan.rho a τ f a = 0" := by
  intro a τ f
  funext k
  simp [KdVPlan.rho,KdVPlan.timeInt,KdVPlan.scale]

theorem yui_aux_0077 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff) (n : ℕ), 0 < τ → KdVPlan.residual τ f ((n:ℝ)*τ) = ∑ j ∈ Finset.range n, KdVPlan.rho ((j:ℝ)*τ) τ (KdVPlan.twistedNum τ f j) (((j:ℝ)+1)*τ)" := by
  intro τ f n ht
  have hidx : KdVPlan.gridIndex τ ((n:ℝ)*τ) = n := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ n ((n:ℝ)*τ) ht le_rfl (by nlinarith)
  simp only [KdVPlan.residual,hidx,@yui_aux_0076 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013,add_zero]

theorem yui_aux_0078 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff) (n : ℕ) (t : ℝ), 0 < τ → t ∈ Icc ((n:ℝ)*τ) (((n:ℝ)+1)*τ) → KdVPlan.residual τ f t = (∑ j ∈ Finset.range n, KdVPlan.rho ((j:ℝ)*τ) τ (KdVPlan.twistedNum τ f j) (((j:ℝ)+1)*τ))+KdVPlan.rho ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) t" := by
  intro τ f n t ht htt
  by_cases hlt : t < ((n:ℝ)+1)*τ
  · have hi := @yui_aux_0063 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ n t ht htt.1 hlt
    simp only [KdVPlan.residual,hi]
  · have heq : t = ((n:ℝ)+1)*τ := le_antisymm htt.2 (le_of_not_gt hlt)
    rw [heq]
    have hend : ((n+1:ℕ):ℝ)*τ = ((n:ℝ)+1)*τ := by simp only [Nat.cast_add,Nat.cast_one]
    rw [← hend,@yui_aux_0077 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ f (n+1) ht,Finset.sum_range_succ]
    rw [hend]

theorem yui_aux_0079 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ n : ℕ, n ≤ L → (n:ℝ)*τ ∈ Icc a b → ∀ l r : ℝ, (n:ℝ)*τ ≤ l → l ≤ r → r ≤ ((n:ℝ)+1)*τ → ∀ k, IntervalIntegrable (fun t => KdVPlan.dt (KdVPlan.residual τ f) t k) volume l r ∧ (∫ t in l..r, KdVPlan.dt (KdVPlan.residual τ f) t k) = KdVPlan.residual τ f r k-KdVPlan.residual τ f l k" := by
  intro M τ L f v a b hM ht ht1 hv hg hE n hn hni l r hal hlr hrb k
  have hs := @yui_aux_0030 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE n hn hni
  have hrb' : r ≤ (n:ℝ)*τ+τ := by nlinarith
  have hi := @yui_aux_0075 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) (v ((n:ℝ)*τ)) hs l r hal hlr hrb' k
  have heq : (fun t => KdVPlan.dt (KdVPlan.rho ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t k) =ᵐ[volume.restrict (uIoc l r)] (fun t => KdVPlan.dt (KdVPlan.residual τ f) t k) := by
    rw [uIoc_of_le hlr,← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htt
    have htcell : t ∈ Ioo ((n:ℝ)*τ) (((n:ℝ)+1)*τ) := ⟨hal.trans_lt htt.1,htt.2.trans_le hrb⟩
    exact (congrFun (@yui_aux_0064 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ f n t ht htcell).2.2 k).symm
  have hleft := @yui_aux_0078 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ f n l ht ⟨hal,hlr.trans hrb⟩
  have hright := @yui_aux_0078 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ f n r ht ⟨hal.trans hlr,hrb⟩
  refine ⟨hi.1.congr_ae heq,?_⟩
  calc
    (∫ t in l..r, KdVPlan.dt (KdVPlan.residual τ f) t k) = ∫ t in l..r, KdVPlan.dt (KdVPlan.rho ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n)) t k := intervalIntegral.integral_congr_ae_restrict heq.symm
    _ = KdVPlan.rho ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) r k-KdVPlan.rho ((n:ℝ)*τ) τ (KdVPlan.twistedNum τ f n) l k := hi.2
    _ = KdVPlan.residual τ f r k-KdVPlan.residual τ f l k := by rw [hright,hleft]; simp only [Pi.add_apply]; abel

theorem yui_aux_0080 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ t ∈ Icc a b, (∀ k, IntervalIntegrable (fun s => KdVPlan.dt (KdVPlan.residual τ f) s k) volume a t) ∧ KdVPlan.timeInt a t (KdVPlan.dt (KdVPlan.residual τ f)) = KdVPlan.residual τ f t-KdVPlan.residual τ f a" := by
  classical
  intro M τ L f v a b hM ht ht1 hv hg hE t htt
  let p : Finset ℝ := (Finset.range (L+1)).image (fun n : ℕ => (n:ℝ)*τ)
  have hcalc (k : ℤ) : IntervalIntegrable (fun s => KdVPlan.dt (KdVPlan.residual τ f) s k) volume a t ∧ (∫ s in a..t, KdVPlan.dt (KdVPlan.residual τ f) s k) = KdVPlan.residual τ f t k-KdVPlan.residual τ f a k := by
    apply @yui_aux_0047 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 p a t (fun s => KdVPlan.residual τ f s k) (fun s => KdVPlan.dt (KdVPlan.residual τ f) s k) htt.1
    intro l r hal hlr hrt hfree
    have hli : l ∈ Icc a b := ⟨hal,hlr.trans (hrt.trans htt.2)⟩
    let n := KdVPlan.gridIndex τ l
    have hn := @yui_aux_0065 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 τ L a b l ht hg hli
    have hrend : r ≤ ((n:ℝ)+1)*τ := by
      by_contra hno
      have hbad : ((n:ℝ)+1)*τ < r := lt_of_not_ge hno
      have hprod : ((n:ℝ)+1)*τ < (L:ℝ)*τ := hbad.trans_le (hrt.trans (htt.2.trans hg.2.2.1))
      have hreal : (n:ℝ)+1 < (L:ℝ) := by
        by_contra hh
        have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hh) ht.le
        linarith
      have hnplus : n+1 ≤ L := Nat.le_of_lt (by exact_mod_cast hreal)
      have hp : ((n:ℝ)+1)*τ ∈ p := by
        apply Finset.mem_image.mpr
        refine ⟨n+1,Finset.mem_range.mpr (by omega),?_⟩
        simp only [Nat.cast_add,Nat.cast_one]
      exact hfree _ hp ⟨hn.2.2.2,hbad⟩
    exact @yui_aux_0079 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE n hn.1 hn.2.1 l r hn.2.2.1 hlr hrend k
  refine ⟨fun k => (hcalc k).1,?_⟩
  funext k
  exact (hcalc k).2

theorem yui_aux_0081 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ t ∈ Icc a b, KdVPlan.err τ f v t = KdVPlan.err τ f v a+KdVPlan.errorF a τ f v t-(KdVPlan.residual τ f t-KdVPlan.residual τ f a)" := by
  intro M τ L f v a b hM ht ht1 hv hg hE t htt
  let e := KdVPlan.err τ f v
  let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s)
  have pe := (@yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg).1
  have pet := @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b a t e le_rfl htt.2 pe
  have heFTC := @yui_aux_0049 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a t e htt.1 pet
  have hRFTC := @yui_aux_0080 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE t htt
  have hdyn := @yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE
  have hsub : Ioc a t ⊆ Icc a b := fun s hs => ⟨hs.1.le,hs.2.trans htt.2⟩
  have hdyn' := ae_restrict_of_ae_restrict_of_subset hsub hdyn
  have hi : KdVPlan.errorF a τ f v t = KdVPlan.timeInt a t (KdVPlan.dt e)+KdVPlan.timeInt a t (KdVPlan.dt (KdVPlan.residual τ f)) := by
    funext k
    have heq : (fun s => KdVPlan.B s (e s) (g s) k) =ᵐ[volume.restrict (uIoc a t)] (fun s => KdVPlan.dt e s k+KdVPlan.dt (KdVPlan.residual τ f) s k) := by
      rw [uIoc_of_le htt.1]
      filter_upwards [hdyn'] with s hs
      exact sub_eq_iff_eq_add.mp (congrFun hs.1 k).symm
    change (∫ s in a..t, KdVPlan.B s (e s) (g s) k) = (∫ s in a..t, KdVPlan.dt e s k)+(∫ s in a..t, KdVPlan.dt (KdVPlan.residual τ f) s k)
    exact (intervalIntegral.integral_congr_ae_restrict heq).trans (intervalIntegral.integral_add (heFTC.1 k) (hRFTC.1 k))
  rw [heFTC.2,hRFTC.2] at hi
  rw [hi]
  change e t = e a+(e t-e a+(KdVPlan.residual τ f t-KdVPlan.residual τ f a))-(KdVPlan.residual τ f t-KdVPlan.residual τ f a)
  abel

theorem yui_aux_0082 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f : KdVPlan.Coeff, KdVPlan.MemH 0 f → KdVPlan.HB 0 (KdVPlan.invD f) (KdVPlan.hn 0 f)" := by
  intro f hf
  have hnorm (k : ℤ) : ‖KdVPlan.invD f k‖ ≤ ‖f k‖ := by
    by_cases hk : k=0
    · simp only [KdVPlan.invD,if_pos hk,norm_zero]
      exact norm_nonneg _
    · have hki : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
      have hinv : |(k:ℝ)|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hki
      simp only [KdVPlan.invD,if_neg hk,norm_mul,norm_inv,Complex.norm_I,Complex.norm_intCast,one_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv (norm_nonneg (f k))
  have hh := @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 0 1 (KdVPlan.invD f) f (by norm_num) hf (by
    intro k
    simp only [KdVPlan.weight,Real.rpow_zero,one_mul,one_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2)
  simpa only [one_mul] using hh

theorem yui_aux_0083 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f f' g : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 f' → KdVPlan.MemH 0 g → KdVPlan.J t (f+f') g = KdVPlan.J t f g+KdVPlan.J t f' g ∧ KdVPlan.J t (f-f') g = KdVPlan.J t f g-KdVPlan.J t f' g ∧ KdVPlan.J t f g = KdVPlan.J t g f ∧ ∀ c : ℂ, KdVPlan.J t (KdVPlan.scale c f) g = KdVPlan.scale c (KdVPlan.J t f g) ∧ KdVPlan.J t f (KdVPlan.scale c g) = KdVPlan.scale c (KdVPlan.J t f g)" := by
  intro t f f' g hf hf' hg
  obtain ⟨Sp,Dp,Ip,Pp,hSp,_,hI,_⟩ := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t
  obtain ⟨Sm,Dm,Im,Pm,hSm,_,_,hP⟩ := @yui_aux_0053 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-t)
  let U := Sp.comp Ip
  let A := Sm.comp Pm
  have hU (u : KdVPlan.Coeff) : U u = KdVPlan.S t (KdVPlan.invD u) := by change Sp (Ip u) = _; rw [hI,hSp]
  have hA (u : KdVPlan.Coeff) : A u = KdVPlan.S (-t) (KdVPlan.P u) := by change Sm (Pm u) = _; rw [hP,hSm]
  have hJ (u w : KdVPlan.Coeff) : KdVPlan.J t u w = A (KdVPlan.mul (U u) (U w)) := by rw [hA,hU,hU]; rfl
  have hmem (u : KdVPlan.Coeff) (hu : KdVPlan.MemH 0 u) : KdVPlan.MemH 0 (U u) := by
    rw [hU]
    exact (@yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 t (KdVPlan.invD u) (@yui_aux_0082 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 u hu).1).1
  have hm := @yui_aux_0052 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (U f) (U f') (U g) (hmem f hf) (hmem f' hf') (hmem g hg)
  have hc (u w : KdVPlan.Coeff) : KdVPlan.J t u w = KdVPlan.J t w u := by
    rw [hJ,hJ,(@yui_aux_0051 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (U u) (U w)).1]
  refine ⟨?_,?_,hc f g,?_⟩
  · rw [hJ,U.map_add,hm.1,A.map_add,← hJ,← hJ]
  · rw [hJ,U.map_sub,hm.2,A.map_sub,← hJ,← hJ]
  · intro c
    have hs (u w : KdVPlan.Coeff) : KdVPlan.J t (KdVPlan.scale c u) w = KdVPlan.scale c (KdVPlan.J t u w) := by
      change KdVPlan.J t (c • u) w = c • KdVPlan.J t u w
      rw [hJ,U.map_smul,hJ]
      change A (KdVPlan.mul (KdVPlan.scale c (U u)) (U w)) = c • A (KdVPlan.mul (U u) (U w))
      rw [(@yui_aux_0051 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (U u) (U w)).2 c |>.1]
      exact A.map_smul c _
    refine ⟨hs f g,?_⟩
    rw [hc f (KdVPlan.scale c g),hs g f,hc g f]

theorem yui_aux_0084 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f : KdVPlan.Coeff, KdVPlan.MemH 1 f → KdVPlan.HB 0 (KdVPlan.dx f) (KdVPlan.hn 1 f)" := by
  intro f hf
  have hh := @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 1 1 (KdVPlan.dx f) f (by norm_num) hf (by
    intro k
    rw [@yui_aux_0037 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 f k]
    simp only [KdVPlan.weight,Real.rpow_zero,Real.rpow_one,one_mul,one_pow,mul_pow,sq_abs]
    nlinarith [sq_nonneg ‖f k‖])
  simpa only [one_mul] using hh

theorem yui_aux_0085 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH 1 f → KdVPlan.MemH 1 g → KdVPlan.HB 0 (KdVPlan.B t f g) (C*KdVPlan.hn 1 f*KdVPlan.hn 1 g)" := by
  obtain ⟨C,hC,_,hprod,_,_⟩ := h_T005.1.1
  refine ⟨C,hC,?_⟩
  intro t f g hf hg
  have hfs := @yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 1 t f hf
  have hgs := @yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 1 t g hg
  have hp := hprod (KdVPlan.S t f) (KdVPlan.S t g) hfs.1 hgs.1
  rw [hfs.2,hgs.2] at hp
  have hd := @yui_aux_0084 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 _ hp.1
  have hs := @yui_aux_0035 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (-t) _ hd.1
  refine ⟨hs.1,?_⟩
  change KdVPlan.hn 0 (KdVPlan.S (-t) _) ≤ _
  rw [hs.2]
  exact hd.2.trans hp.2

theorem yui_aux_0086 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → let e := KdVPlan.err τ f v; let V := KdVPlan.interp τ f; let g : KdVPlan.Path := fun t => v t-KdVPlan.scale (1/2) (e t); KdVPlan.Piecewise a b v ∧ KdVPlan.Piecewise a b V ∧ KdVPlan.Piecewise a b e ∧ KdVPlan.Piecewise a b g ∧ ∀ t ∈ Icc a b, KdVPlan.ZeroMean (v t) ∧ KdVPlan.ZeroMean (V t) ∧ KdVPlan.ZeroMean (e t) ∧ KdVPlan.ZeroMean (g t)" := by
  intro M τ L f v a b hM ht ht1 hv hg
  let e := KdVPlan.err τ f v
  let V := KdVPlan.interp τ f
  let g : KdVPlan.Path := fun t => v t-KdVPlan.scale (1/2) (e t)
  obtain ⟨C,hC,_,hacc⟩ := h_T009 M hM
  have ha := hacc τ L f v ht ht1 hv
  have pv0 := @yui_aux_0026 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) v hv.2.2.1
  have pv := @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) a b v hg.1 hg.2.2.1 pv0
  have pV : KdVPlan.Piecewise a b V := @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 ((L:ℝ)*τ) a b V hg.1 hg.2.2.1 ha.1
  have pe := (@yui_aux_0031 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg).1
  have pg : KdVPlan.Piecewise a b g := @yui_aux_0027 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b v (fun t => KdVPlan.scale (1/2) (e t)) pv (@yui_aux_0023 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (1/2) e pe)
  refine ⟨pv,pV,pe,pg,?_⟩
  intro t htt
  have htH : t ∈ Icc 0 ((L:ℝ)*τ) := ⟨hg.1.trans htt.1,htt.2.trans hg.2.2.1⟩
  have v0 := (hv.2.2.2.1 t htH).1
  have V0 : KdVPlan.ZeroMean (V t) := (ha.2.1 t htH).1
  have e0 : KdVPlan.ZeroMean (e t) := by change v t 0-V t 0=0; rw [v0,V0]; simp
  have g0 : KdVPlan.ZeroMean (g t) := by change v t 0-(1/2:ℂ)*e t 0=0; rw [v0,e0]; simp
  exact ⟨v0,V0,e0,g0⟩

theorem yui_aux_0087 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.MemH 0 (KdVPlan.dt (KdVPlan.residual τ f) t)" := by
  intro M τ L f v a b hM ht ht1 hv hg hE
  have hpaths := @yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg
  have hdi := @yui_aux_0067 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (KdVPlan.interp τ f) hpaths.2.1
  have hlocal := @yui_aux_0066 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE
  obtain ⟨Cb,hCb,hB⟩ := @yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  filter_upwards [hdi,hlocal,ae_restrict_mem measurableSet_Icc] with t hdi hlocal htt
  have hI1 : KdVPlan.MemH 1 (KdVPlan.interp τ f t) := by simpa using (hpaths.2.1.1 1).1 t htt
  have hB0 := (hB t (KdVPlan.interp τ f t) (KdVPlan.interp τ f t) hI1 hI1).1
  have hscale := (@yui_aux_0004 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (1/2) _ hB0).1
  have hdtI : KdVPlan.MemH 0 (KdVPlan.dt (KdVPlan.interp τ f) t) := by simpa using hdi.2 0
  have heq : KdVPlan.dt (KdVPlan.residual τ f) t = KdVPlan.dt (KdVPlan.interp τ f) t-KdVPlan.scale (1/2) (KdVPlan.B t (KdVPlan.interp τ f t) (KdVPlan.interp τ f t)) := by rw [hlocal.1]; abel
  rw [heq]
  exact (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 _ _ hdtI hscale).1

theorem yui_aux_0088 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g g' : KdVPlan.Coeff), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → KdVPlan.MemH 0 g' → KdVPlan.J t f (g+g') = KdVPlan.J t f g+KdVPlan.J t f g' ∧ KdVPlan.J t f (g-g') = KdVPlan.J t f g-KdVPlan.J t f g'" := by
  intro t f g g' hf hg hg'
  let j := @yui_aux_0083 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have ha := (@yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 g g' hg hg').1
  have hs := (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 g g' hg hg').1
  constructor
  · rw [(j t f f (g+g') hf hf ha).2.2.1,(j t g g' f hg hg' hf).1,(j t g g f hg hg hf).2.2.1,(j t g' g' f hg' hg' hf).2.2.1]
  · rw [(j t f f (g-g') hf hf hs).2.2.1,(j t g g' f hg hg' hf).2.1,(j t g g f hg hg hf).2.2.1,(j t g' g' f hg' hg' hf).2.2.1]

theorem yui_aux_0089 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (A B r e g : KdVPlan.Coeff), KdVPlan.MemH 0 A → KdVPlan.MemH 0 B → KdVPlan.MemH 0 r → KdVPlan.MemH 0 e → KdVPlan.MemH 0 g → KdVPlan.J t (A-r) g+KdVPlan.J t e (KdVPlan.scale (1/2) B-KdVPlan.scale (1/2) A+KdVPlan.scale (1/2) r) = KdVPlan.J t A (g-KdVPlan.scale (1/2) e)+KdVPlan.scale (1/2) (KdVPlan.J t B e)-KdVPlan.J t r (g-KdVPlan.scale (1/2) e)" := by
  intro t A B r e g hA hB hr he hg
  let j := @yui_aux_0083 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  let jr := @yui_aux_0088 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  let sc := @yui_aux_0004 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have hAh := (sc 0 (1/2) A hA).1
  have hBh := (sc 0 (1/2) B hB).1
  have hrh := (sc 0 (1/2) r hr).1
  have heh := (sc 0 (1/2) e he).1
  have hBA := (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 _ _ hBh hAh).1
  rw [(j t A r g hA hr hg).2.1,(jr t e (KdVPlan.scale (1/2) B-KdVPlan.scale (1/2) A) (KdVPlan.scale (1/2) r) he hBA hrh).1]
  rw [(jr t e (KdVPlan.scale (1/2) B) (KdVPlan.scale (1/2) A) he hBh hAh).2]
  rw [(jr t A g (KdVPlan.scale (1/2) e) hA hg heh).2,(jr t r g (KdVPlan.scale (1/2) e) hr hg heh).2]
  rw [(j t e e B he he hB).2.2.2 (1/2) |>.2,(j t e e A he he hA).2.2.2 (1/2) |>.2,(j t e e r he he hr).2.2.2 (1/2) |>.2]
  rw [(j t A A e hA hA he).2.2.2 (1/2) |>.2,(j t r r e hr hr he).2.2.2 (1/2) |>.2]
  rw [(j t e e B he he hB).2.2.1,(j t e e A he he hA).2.2.1,(j t e e r he he hr).2.2.1]
  abel

theorem yui_aux_0090 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ᵐ t ∂(volume.restrict (Icc a b)), let e := KdVPlan.err τ f v; let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s); KdVPlan.J t (KdVPlan.dt e t) (g t)+KdVPlan.J t (e t) (KdVPlan.dt g t) = KdVPlan.J t (KdVPlan.B t (e t) (g t)) (KdVPlan.interp τ f t)+KdVPlan.scale (1/2) (KdVPlan.J t (KdVPlan.B t (v t) (v t)) (e t))-KdVPlan.J t (KdVPlan.dt (KdVPlan.residual τ f) t) (KdVPlan.interp τ f t)" := by
  intro M τ L f v a b hM ht ht1 hv hg hE
  let e := KdVPlan.err τ f v
  let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s)
  have hp := @yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg
  have hd := @yui_aux_0068 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE
  have hr := @yui_aux_0087 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE
  obtain ⟨Cb,hCb,hB⟩ := @yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  filter_upwards [hd,hr,ae_restrict_mem measurableSet_Icc] with t hd hr htt
  have hv1 : KdVPlan.MemH 1 (v t) := by simpa using (hp.1.1 1).1 t htt
  have he1 : KdVPlan.MemH 1 (e t) := by simpa using (hp.2.2.1.1 1).1 t htt
  have hg1 : KdVPlan.MemH 1 (g t) := by
    change KdVPlan.MemH 1 (v t-KdVPlan.scale (1/2) (KdVPlan.err τ f v t))
    simpa only [Nat.cast_one] using (hp.2.2.2.1.1 1).1 t htt
  have he0 : KdVPlan.MemH 0 (e t) := by simpa using (hp.2.2.1.1 0).1 t htt
  have hg0 : KdVPlan.MemH 0 (g t) := by
    change KdVPlan.MemH 0 (v t-KdVPlan.scale (1/2) (KdVPlan.err τ f v t))
    simpa only [Nat.cast_zero] using (hp.2.2.2.1.1 0).1 t htt
  have hde : KdVPlan.dt e t = KdVPlan.B t (e t) (g t)-KdVPlan.dt (KdVPlan.residual τ f) t := hd.1
  have hdg : KdVPlan.dt g t = KdVPlan.scale (1/2) (KdVPlan.B t (v t) (v t))-KdVPlan.scale (1/2) (KdVPlan.B t (e t) (g t))+KdVPlan.scale (1/2) (KdVPlan.dt (KdVPlan.residual τ f) t) := hd.2
  have hrel : g t-KdVPlan.scale (1/2) (e t) = KdVPlan.interp τ f t := by
    funext k
    simp only [g,e,KdVPlan.err,KdVPlan.scale,Pi.sub_apply]
    ring
  have hc := @yui_aux_0089 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t (KdVPlan.B t (e t) (g t)) (KdVPlan.B t (v t) (v t)) (KdVPlan.dt (KdVPlan.residual τ f) t) (e t) (g t) (hB t (e t) (g t) he1 hg1).1 (hB t (v t) (v t) hv1 hv1).1 hr he0 hg0
  rw [hrel] at hc
  change KdVPlan.J t (KdVPlan.dt e t) (g t)+KdVPlan.J t (e t) (KdVPlan.dt g t) = KdVPlan.J t (KdVPlan.B t (e t) (g t)) (KdVPlan.interp τ f t)+KdVPlan.scale (1/2) (KdVPlan.J t (KdVPlan.B t (v t) (v t)) (e t))-KdVPlan.J t (KdVPlan.dt (KdVPlan.residual τ f) t) (KdVPlan.interp τ f t)
  rw [hde,hdg]
  exact hc

theorem yui_aux_0091 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (μ : Measure ℝ) (f g : KdVPlan.Path), (∀ k, AEStronglyMeasurable (fun t => f t k) μ) → (∀ k, AEStronglyMeasurable (fun t => g t k) μ) → ∀ k, AEStronglyMeasurable (fun t => KdVPlan.J t (f t) (g t) k) μ" := by
  intro μ f g hf hg
  have hinv (u : KdVPlan.Path) (hu : ∀ k, AEStronglyMeasurable (fun t => u t k) μ) (k : ℤ) : AEStronglyMeasurable (fun t => KdVPlan.invD (u t) k) μ := by
    by_cases hk : k=0
    · change AEStronglyMeasurable (fun t => if k=0 then 0 else (Complex.I*(k:ℂ))⁻¹*u t k) μ
      simp only [if_pos hk]
      exact aestronglyMeasurable_const
    · change AEStronglyMeasurable (fun t => if k=0 then 0 else (Complex.I*(k:ℂ))⁻¹*u t k) μ
      simp only [if_neg hk]
      exact (hu k).const_mul _
  have hsf (k : ℤ) : AEStronglyMeasurable (fun t => KdVPlan.S t (KdVPlan.invD (f t)) k) μ := by
    have hh := @yui_aux_0057 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 μ 1 (fun t => KdVPlan.invD (f t)) k (hinv f hf k)
    simpa only [one_mul] using hh
  have hsg (k : ℤ) : AEStronglyMeasurable (fun t => KdVPlan.S t (KdVPlan.invD (g t)) k) μ := by
    have hh := @yui_aux_0057 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 μ 1 (fun t => KdVPlan.invD (g t)) k (hinv g hg k)
    simpa only [one_mul] using hh
  let h : KdVPlan.Path := fun t => KdVPlan.P (KdVPlan.mul (KdVPlan.S t (KdVPlan.invD (f t))) (KdVPlan.S t (KdVPlan.invD (g t))))
  have hm (k : ℤ) : AEStronglyMeasurable (fun t => KdVPlan.mul (KdVPlan.S t (KdVPlan.invD (f t))) (KdVPlan.S t (KdVPlan.invD (g t))) k) μ := AEStronglyMeasurable.tsum (fun j : ℤ => (hsf j).mul (hsg (k-j)))
  have hp (k : ℤ) : AEStronglyMeasurable (fun t => h t k) μ := by
    by_cases hk : k=0
    · change AEStronglyMeasurable (fun t => if k=0 then 0 else _) μ
      simp only [if_pos hk]
      exact aestronglyMeasurable_const
    · change AEStronglyMeasurable (fun t => if k=0 then 0 else _) μ
      simp only [if_neg hk]
      exact hm k
  intro k
  have hh := @yui_aux_0057 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 μ (-1) h k (hp k)
  change AEStronglyMeasurable (fun t => KdVPlan.S (-t) (h t) k) μ
  simpa only [neg_one_mul] using hh

theorem yui_aux_0092 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b C D : ℝ) (f g : KdVPlan.Path), a ≤ b → 0 ≤ C → 0 ≤ D → (∀ k, AEStronglyMeasurable (fun t => f t k) (volume.restrict (Icc a b))) → (∀ k, AEStronglyMeasurable (fun t => g t k) (volume.restrict (Icc a b))) → KdVPlan.UB 0 a b f C → KdVPlan.UB 0 a b g D → ∀ k, IntervalIntegrable (fun t => KdVPlan.J t (f t) (g t) k) volume a b" := by
  intro a b C D f g hab hC hD hm hn hf hg
  obtain ⟨Cj,hCj,_,_,hJ,_⟩ := h_T005.1.1
  have hmeas := @yui_aux_0091 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (volume.restrict (Icc a b)) f g hm hn
  apply @yui_aux_0060 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 1 a b (Cj*C*D) (fun t => KdVPlan.J t (f t) (g t)) hab hmeas
  intro t ht
  have hh := (hJ t (f t) (g t) (hf t ht).1 (hg t ht).1).2.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hprod := mul_le_mul (hf t ht).2 (hg t ht).2 (Real.sqrt_nonneg _) hC
  nlinarith [mul_le_mul_of_nonneg_left hprod hCj.le]

theorem yui_aux_0093 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → ∃ C : ℝ, 0 ≤ C ∧ KdVPlan.UB s a b f C ∧ ∀ k, AEStronglyMeasurable (fun t => f t k) (volume.restrict (Icc a b))" := by
  intro s a b f hf
  refine ⟨KdVPlan.SupH s a b f,?_,(@yui_aux_0016 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f hf).2,?_⟩
  · apply Real.sSup_nonneg
    rintro x ⟨t,htt,rfl⟩
    exact Real.sqrt_nonneg _
  · intro k
    exact (@yui_aux_0062 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f hf k).aestronglyMeasurable measurableSet_Icc

theorem yui_aux_0094 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (p : Finset ℝ) (P : ℝ → ℝ → Prop), (∀ l r s : ℝ, l ≤ r → r ≤ s → P l r → P r s → P l s) → ∀ a b : ℝ, a ≤ b → (∀ l r : ℝ, a ≤ l → l ≤ r → r ≤ b → (∀ x ∈ p, x ∉ Ioo l r) → P l r) → P a b" := by
  classical
  intro p
  induction p using Finset.induction_on with
  | empty =>
    intro P htrans a b hab hlocal
    exact hlocal a b le_rfl hab le_rfl (by simp)
  | @insert x p hx ih =>
    intro P htrans a b hab hlocal
    by_cases hxab : x ∈ Ioo a b
    · have hl := ih P htrans a x hxab.1.le (by
        intro l r hal hlr hrx hfree
        apply hlocal l r hal hlr (hrx.trans hxab.2.le)
        intro y hy hyint
        rcases Finset.mem_insert.mp hy with rfl | hyp
        · exact (not_lt_of_ge hrx) hyint.2
        · exact hfree y hyp hyint)
      have hr := ih P htrans x b hxab.2.le (by
        intro l r hxl hlr hrb hfree
        apply hlocal l r (hxab.1.le.trans hxl) hlr hrb
        intro y hy hyint
        rcases Finset.mem_insert.mp hy with rfl | hyp
        · exact (not_lt_of_ge hxl) hyint.1
        · exact hfree y hyp hyint)
      exact htrans a x b hxab.1.le hxab.2.le hl hr
    · apply ih P htrans a b hab
      intro l r hal hlr hrb hfree
      apply hlocal l r hal hlr hrb
      intro y hy hyint
      rcases Finset.mem_insert.mp hy with rfl | hyp
      · exact hxab ⟨hal.trans_lt hyint.1,hyint.2.trans_le hrb⟩
      · exact hfree y hyp hyint

theorem yui_aux_0095 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), a ≤ b → KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b g → ∀ k, IntervalIntegrable (fun t => KdVPlan.J t (KdVPlan.dt f t) (g t) k) volume a b ∧ IntervalIntegrable (fun t => KdVPlan.J t (f t) (KdVPlan.dt g t) k) volume a b" := by
  intro a b f g hab hf hg
  let df : KdVPlan.Path := fun t k => iteratedDerivWithin 1 (fun r => f r k) (Icc a b) t
  let dg : KdVPlan.Path := fun t k => iteratedDerivWithin 1 (fun r => g r k) (Icc a b) t
  have hf0 : KdVPlan.ContH 0 a b f := by simpa only [Nat.cast_zero,iteratedDerivWithin_zero] using hf.2 0 0
  have hg0 : KdVPlan.ContH 0 a b g := by simpa only [Nat.cast_zero,iteratedDerivWithin_zero] using hg.2 0 0
  have hdf0 : KdVPlan.ContH 0 a b df := by simpa only [Nat.cast_zero] using hf.2 0 1
  have hdg0 : KdVPlan.ContH 0 a b dg := by simpa only [Nat.cast_zero] using hg.2 0 1
  obtain ⟨Cf,hCf,hfUB,hfm⟩ := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b f hf0
  obtain ⟨Cg,hCg,hgUB,hgm⟩ := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b g hg0
  obtain ⟨Cdf,hCdf,hdfUB,hdfm⟩ := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b df hdf0
  obtain ⟨Cdg,hCdg,hdgUB,hdgm⟩ := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b dg hdg0
  have hi1 := @yui_aux_0092 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b Cdf Cg df g hab hCdf hCg hdfm hgm hdfUB hgUB
  have hi2 := @yui_aux_0092 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b Cf Cdg f dg hab hCf hCdg hfm hdgm hfUB hdgUB
  have heqf (t : ℝ) (htt : t ∈ Ioo a b) : df t = KdVPlan.dt f t := by
    funext k
    change iteratedDerivWithin 1 (fun r => f r k) (Icc a b) t = _
    rw [iteratedDerivWithin_one,derivWithin_of_mem_nhds (Icc_mem_nhds htt.1 htt.2)]
    rfl
  have heqg (t : ℝ) (htt : t ∈ Ioo a b) : dg t = KdVPlan.dt g t := by
    funext k
    change iteratedDerivWithin 1 (fun r => g r k) (Icc a b) t = _
    rw [iteratedDerivWithin_one,derivWithin_of_mem_nhds (Icc_mem_nhds htt.1 htt.2)]
    rfl
  intro k
  constructor
  · apply (hi1 k).congr_ae
    rw [uIoc_of_le hab,← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htt
    rw [heqf t htt]
  · apply (hi2 k).congr_ae
    rw [uIoc_of_le hab,← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htt
    rw [heqg t htt]

theorem yui_aux_0096 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), a ≤ b → KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → ∀ k, IntervalIntegrable (fun t => KdVPlan.J t (KdVPlan.dt f t) (g t) k) volume a b ∧ IntervalIntegrable (fun t => KdVPlan.J t (f t) (KdVPlan.dt g t) k) volume a b" := by
  classical
  intro a b f g hab hf hg k
  obtain ⟨pf,hpf⟩ := hf.2
  obtain ⟨pg,hpg⟩ := hg.2
  apply @yui_aux_0094 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (pf∪pg) (fun l r => IntervalIntegrable (fun t => KdVPlan.J t (KdVPlan.dt f t) (g t) k) volume l r ∧ IntervalIntegrable (fun t => KdVPlan.J t (f t) (KdVPlan.dt g t) k) volume l r)
  · intro l r s hlr hrs hi1 hi2
    exact ⟨hi1.1.trans hi2.1,hi1.2.trans hi2.2⟩
  · exact hab
  · intro l r hal hlr hrb hfree
    rcases hlr.eq_or_lt with rfl | hlt
    · exact ⟨IntervalIntegrable.refl,IntervalIntegrable.refl⟩
    · have hfs := hpf l r hal hlt hrb (fun x hx => hfree x (Finset.mem_union_left pg hx))
      have hgs := hpg l r hal hlt hrb (fun x hx => hfree x (Finset.mem_union_right pf hx))
      exact @yui_aux_0095 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l r f g hlr hfs hgs k

theorem yui_aux_0097 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g h : KdVPlan.Path), a ≤ b → KdVPlan.ContH 1 a b f → KdVPlan.ContH 1 a b g → KdVPlan.ContH 0 a b h → ∀ k, IntervalIntegrable (fun t => KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t) k) volume a b" := by
  intro a b f g h hab hf hg hh
  obtain ⟨Cf,hCf,hfUB,hfm⟩ := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 1 a b f hf
  obtain ⟨Cg,hCg,hgUB,hgm⟩ := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 1 a b g hg
  obtain ⟨Ch,hCh,hhUB,hhm⟩ := @yui_aux_0093 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b h hh
  obtain ⟨Cb,hCb,hB⟩ := @yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have hBUB : KdVPlan.UB 0 a b (fun t => KdVPlan.B t (f t) (g t)) (Cb*Cf*Cg) := by
    intro t ht
    have hb := hB t (f t) (g t) (hfUB t ht).1 (hgUB t ht).1
    refine ⟨hb.1,hb.2.trans ?_⟩
    have hprod := mul_le_mul (hfUB t ht).2 (hgUB t ht).2 (Real.sqrt_nonneg _) hCf
    nlinarith [mul_le_mul_of_nonneg_left hprod hCb.le]
  have hBm := @yui_aux_0058 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (volume.restrict (Icc a b)) f g hfm hgm
  exact @yui_aux_0092 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (Cb*Cf*Cg) Ch (fun t => KdVPlan.B t (f t) (g t)) h hab (by positivity) hCh hBm hhm hBUB hhUB

theorem yui_aux_0098 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (L p q r : ℝ → ℂ) (c : ℂ), IntervalIntegrable L volume a b → IntervalIntegrable p volume a b → IntervalIntegrable q volume a b → L =ᵐ[volume.restrict (uIoc a b)] (fun t => p t+c*q t-r t) → IntervalIntegrable r volume a b ∧ (∫ t in a..b, L t) = (∫ t in a..b, p t)+c*(∫ t in a..b, q t)-(∫ t in a..b, r t)" := by
  intro a b L p q r c hL hp hq heq
  have hcq : IntervalIntegrable (fun t => c*q t) volume a b := hq.const_mul c
  have hpq : IntervalIntegrable (fun t => p t+c*q t) volume a b := hp.add hcq
  have hd : IntervalIntegrable (fun t => p t+c*q t-L t) volume a b := hpq.sub hL
  have her : (fun t => p t+c*q t-L t) =ᵐ[volume.restrict (uIoc a b)] r := by
    filter_upwards [heq] with t ht
    rw [ht]
    abel
  have hr := hd.congr_ae her
  refine ⟨hr,?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict heq,intervalIntegral.integral_sub hpq hr,intervalIntegral.integral_add hp hcq,intervalIntegral.integral_const_mul]

theorem yui_aux_0099 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ t ∈ Icc a b, let e := KdVPlan.err τ f v; let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s); (∀ k, IntervalIntegrable (fun s => KdVPlan.J s (KdVPlan.dt (KdVPlan.residual τ f) s) (KdVPlan.interp τ f s) k) volume a t) ∧ KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt e s) (g s)+KdVPlan.J s (e s) (KdVPlan.dt g s)) = KdVPlan.tri a t e g (KdVPlan.interp τ f)+KdVPlan.scale (1/2) (KdVPlan.tri a t v v e)-KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt (KdVPlan.residual τ f) s) (KdVPlan.interp τ f s))" := by
  intro M τ L f v a b hM ht ht1 hv hg hE t htt
  let e := KdVPlan.err τ f v
  let V := KdVPlan.interp τ f
  let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s)
  have hp := @yui_aux_0086 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg
  let restrictP := @yui_aux_0028 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have pv : KdVPlan.Piecewise a t v := restrictP a b a t v le_rfl htt.2 hp.1
  have pV : KdVPlan.Piecewise a t V := restrictP a b a t V le_rfl htt.2 hp.2.1
  have pe : KdVPlan.Piecewise a t e := restrictP a b a t e le_rfl htt.2 hp.2.2.1
  have pg : KdVPlan.Piecewise a t g := restrictP a b a t g le_rfl htt.2 hp.2.2.2.1
  have hz (s : ℝ) (hs : s ∈ Icc a t) : KdVPlan.ZeroMean (v s) ∧ KdVPlan.ZeroMean (V s) ∧ KdVPlan.ZeroMean (e s) ∧ KdVPlan.ZeroMean (g s) := hp.2.2.2.2 s ⟨hs.1,hs.2.trans htt.2⟩
  have htri1 := h_T005.2.2.2.1 a t e g V htt.1 pe pg pV (fun s hs => ⟨(hz s hs).2.2.1,(hz s hs).2.2.2,(hz s hs).2.1⟩)
  have htri2 := h_T005.2.2.2.1 a t v v e htt.1 pv pv pe (fun s hs => ⟨(hz s hs).1,(hz s hs).1,(hz s hs).2.2.1⟩)
  have hderiv := @yui_aux_0096 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a t e g htt.1 pe pg
  have he1 : KdVPlan.ContH 1 a t e := by simpa only [Nat.cast_one] using pe.1 1
  have hg1 : KdVPlan.ContH 1 a t g := by simpa only [Nat.cast_one] using pg.1 1
  have hv1 : KdVPlan.ContH 1 a t v := by simpa only [Nat.cast_one] using pv.1 1
  have hV0 : KdVPlan.ContH 0 a t V := by simpa only [Nat.cast_zero] using pV.1 0
  have he0 : KdVPlan.ContH 0 a t e := by simpa only [Nat.cast_zero] using pe.1 0
  have hc1 := @yui_aux_0097 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a t e g V htt.1 he1 hg1 hV0
  have hc2 := @yui_aux_0097 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a t v v e htt.1 hv1 hv1 he0
  have hd := @yui_aux_0090 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE
  have hsub : Ioc a t ⊆ Icc a b := fun s hs => ⟨hs.1.le,hs.2.trans htt.2⟩
  have hd' := ae_restrict_of_ae_restrict_of_subset hsub hd
  have hi (k : ℤ) := @yui_aux_0098 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a t (fun s => (KdVPlan.J s (KdVPlan.dt e s) (g s)+KdVPlan.J s (e s) (KdVPlan.dt g s)) k) (fun s => KdVPlan.J s (KdVPlan.B s (e s) (g s)) (V s) k) (fun s => KdVPlan.J s (KdVPlan.B s (v s) (v s)) (e s) k) (fun s => KdVPlan.J s (KdVPlan.dt (KdVPlan.residual τ f) s) (V s) k) (1/2) ((hderiv k).1.add (hderiv k).2) (hc1 k) (hc2 k) (by
    rw [uIoc_of_le htt.1]
    filter_upwards [hd'] with s hs
    exact congrFun hs k)
  refine ⟨fun k => (hi k).1,?_⟩
  have hInt : KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt e s) (g s)+KdVPlan.J s (e s) (KdVPlan.dt g s)) = KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.B s (e s) (g s)) (V s))+KdVPlan.scale (1/2) (KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.B s (v s) (v s)) (e s)))-KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt (KdVPlan.residual τ f) s) (V s)) := by
    funext k
    exact (hi k).2
  rw [htri1,htri2] at hInt
  exact hInt

theorem yui_aux_0100 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (M τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path) (a b : ℝ), 1 ≤ M → 0 < τ → τ ≤ 1 → KdVPlan.Traj gamma M τ L f v → KdVPlan.GridInterval τ L a b → KdVPlan.enorm a b τ f v ≤ 1 → ∀ t ∈ Icc a b, let e := KdVPlan.err τ f v; let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s); KdVPlan.errorF a τ f v t = KdVPlan.scale (1/3) (KdVPlan.J t (e t) (g t)-KdVPlan.J a (e a) (g a))-KdVPlan.scale (1/3) (KdVPlan.tri a t e g (KdVPlan.interp τ f))-KdVPlan.scale (1/6) (KdVPlan.tri a t v v e)+KdVPlan.scale (1/3) (KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt (KdVPlan.residual τ f) s) (KdVPlan.interp τ f s)))" := by
  intro M τ L f v a b hM ht ht1 hv hg hE t htt
  let e := KdVPlan.err τ f v
  let g : KdVPlan.Path := fun s => v s-KdVPlan.scale (1/2) (e s)
  have hraw : KdVPlan.errorF a τ f v t = KdVPlan.scale (1/3) (KdVPlan.J t (e t) (g t)-KdVPlan.J a (e a) (g a))-KdVPlan.scale (1/3) (KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt e s) (g s)+KdVPlan.J s (e s) (KdVPlan.dt g s))) := @yui_aux_0029 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg t htt
  have hint : KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt e s) (g s)+KdVPlan.J s (e s) (KdVPlan.dt g s)) = KdVPlan.tri a t e g (KdVPlan.interp τ f)+KdVPlan.scale (1/2) (KdVPlan.tri a t v v e)-KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt (KdVPlan.residual τ f) s) (KdVPlan.interp τ f s)) := (@yui_aux_0099 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 M τ L f v a b hM ht ht1 hv hg hE t htt).2
  change KdVPlan.errorF a τ f v t = KdVPlan.scale (1/3) (KdVPlan.J t (e t) (g t)-KdVPlan.J a (e a) (g a))-KdVPlan.scale (1/3) (KdVPlan.tri a t e g (KdVPlan.interp τ f))-KdVPlan.scale (1/6) (KdVPlan.tri a t v v e)+KdVPlan.scale (1/3) (KdVPlan.timeInt a t (fun s => KdVPlan.J s (KdVPlan.dt (KdVPlan.residual τ f) s) (KdVPlan.interp τ f s)))
  rw [hraw,hint]
  funext k
  simp only [KdVPlan.scale,Pi.add_apply,Pi.sub_apply]
  ring

theorem yui_aux_0101 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ N s : ℝ, 0 ≤ N → (N^2)^s = (N^s)^2" := by
  intro N s hN
  calc
    (N^2)^s = N^((2:ℝ)*s) := (Real.rpow_natCast_mul hN 2 s).symm
    _ = N^(s*2) := by rw [mul_comm]
    _ = (N^s)^(2:ℝ) := Real.rpow_mul hN s 2
    _ = (N^s)^2 := Real.rpow_natCast _ 2

theorem yui_aux_0102 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N s : ℝ) (f : KdVPlan.Coeff), 0 < N → 0 ≤ s → KdVPlan.MemH 0 f → KdVPlan.HB (-s) (KdVPlan.high N f) (N^(-s)*KdVPlan.hn 0 f)" := by
  intro N s f hN hs hf
  apply @yui_aux_0006 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-s) 0 (N^(-s)) (KdVPlan.high N f) f (Real.rpow_nonneg hN.le _) hf
  intro k
  by_cases hk : |(k:ℝ)| ≤ N
  · simp only [KdVPlan.high,KdVPlan.cutoff,hk,if_true,Pi.sub_apply,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,KdVPlan.weight,Real.rpow_zero,one_mul]
    positivity
  · have hsq : N^2 ≤ 1+(k:ℝ)^2 := by nlinarith [lt_of_not_ge hk,sq_abs (k:ℝ)]
    have hw := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hN) hsq (neg_nonpos.mpr hs)
    rw [@yui_aux_0101 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N (-s) hN.le] at hw
    simp only [KdVPlan.high,KdVPlan.cutoff,if_neg hk,Pi.sub_apply,sub_zero,KdVPlan.weight,Real.rpow_zero,one_mul]
    exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

theorem yui_aux_0103 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b C : ℝ) (f : KdVPlan.Path), 0 ≤ C → (∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn s (f t) ≤ C) → KdVPlan.EssH s a b f ≤ C ∧ essSup (fun t => ENNReal.ofReal (KdVPlan.hn s (f t))) (volume.restrict (Icc a b)) < (⊤ : ℝ≥0∞)" := by
  intro s a b C f hC hf
  have hb : essSup (fun t => ENNReal.ofReal (KdVPlan.hn s (f t))) (volume.restrict (Icc a b)) ≤ ENNReal.ofReal C := essSup_le_of_ae_le _ (hf.mono (fun t ht => ENNReal.ofReal_le_ofReal ht))
  refine ⟨?_,hb.trans_lt ENNReal.ofReal_lt_top⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hC] at hh
  exact hh

theorem yui_aux_0104 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Path), KdVPlan.EssBound s a b f → ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn s (f t) ≤ KdVPlan.EssH s a b f" := by
  intro s a b f hf
  have hb : ∀ᵐ t ∂(volume.restrict (Icc a b)), ENNReal.ofReal (KdVPlan.hn s (f t)) ≤ essSup (fun r => ENNReal.ofReal (KdVPlan.hn s (f r))) (volume.restrict (Icc a b)) := ENNReal.ae_le_essSup _
  filter_upwards [hb] with t ht
  exact (ENNReal.ofReal_le_iff_le_toReal hf.2.2.ne).mp ht

theorem yui_aux_0105 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), KdVPlan.EssBound s a b f → KdVPlan.EssBound s a b g → KdVPlan.EssBound s a b (fun t => f t+g t) ∧ KdVPlan.EssH s a b (fun t => f t+g t) ≤ KdVPlan.EssH s a b f+KdVPlan.EssH s a b g" := by
  intro s a b f g hf hg
  have hfs := @yui_aux_0104 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f hf
  have hgs := @yui_aux_0104 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b g hg
  have hmem : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.MemH s (f t+g t) := by
    filter_upwards [hf.2.1,hg.2.1] with t ht hu
    exact (@yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s (f t) (g t) ht hu).1
  have hnorm : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn s (f t+g t) ≤ KdVPlan.EssH s a b f+KdVPlan.EssH s a b g := by
    filter_upwards [hf.2.1,hg.2.1,hfs,hgs] with t ht hu htf htg
    have hh := (@yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s (f t) (g t) ht hu).2
    linarith
  have hb := @yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b (KdVPlan.EssH s a b f+KdVPlan.EssH s a b g) (fun t => f t+g t) (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hnorm
  exact ⟨⟨fun k => (hf.1 k).add (hg.1 k),hmem,hb.2⟩,hb.1⟩

theorem yui_aux_0106 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (c : ℂ) (f : KdVPlan.Path), KdVPlan.EssBound s a b f → KdVPlan.EssBound s a b (fun t => KdVPlan.scale c (f t)) ∧ KdVPlan.EssH s a b (fun t => KdVPlan.scale c (f t)) ≤ ‖c‖*KdVPlan.EssH s a b f" := by
  intro s a b c f hf
  have hfs := @yui_aux_0104 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f hf
  have hmem : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.MemH s (KdVPlan.scale c (f t)) := by
    filter_upwards [hf.2.1] with t ht
    exact (@yui_aux_0004 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s c (f t) ht).1
  have hnorm : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn s (KdVPlan.scale c (f t)) ≤ ‖c‖*KdVPlan.EssH s a b f := by
    filter_upwards [hf.2.1,hfs] with t ht htf
    rw [(@yui_aux_0004 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s c (f t) ht).2]
    exact mul_le_mul_of_nonneg_left htf (norm_nonneg c)
  have hb := @yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b (‖c‖*KdVPlan.EssH s a b f) (fun t => KdVPlan.scale c (f t)) (mul_nonneg (norm_nonneg c) ENNReal.toReal_nonneg) hnorm
  exact ⟨⟨fun k => (hf.1 k).const_mul c,hmem,hb.2⟩,hb.1⟩

theorem yui_aux_0107 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s r a b C : ℝ) (A : KdVPlan.Coeff → KdVPlan.Coeff) (f : KdVPlan.Path), 0 ≤ C → KdVPlan.EssBound s a b f → (∀ u, KdVPlan.MemH s u → KdVPlan.HB r (A u) (C*KdVPlan.hn s u)) → (∀ k, AEStronglyMeasurable (fun t => A (f t) k) (volume.restrict (Icc a b))) → KdVPlan.EssBound r a b (fun t => A (f t)) ∧ KdVPlan.EssH r a b (fun t => A (f t)) ≤ C*KdVPlan.EssH s a b f" := by
  intro s r a b C A f hC hf hA hm
  have hfs := @yui_aux_0104 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f hf
  have hmem : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.MemH r (A (f t)) := hf.2.1.mono (fun t ht => (hA (f t) ht).1)
  have hnorm : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn r (A (f t)) ≤ C*KdVPlan.EssH s a b f := by
    filter_upwards [hf.2.1,hfs] with t ht htf
    exact (hA (f t) ht).2.trans (mul_le_mul_of_nonneg_left htf hC)
  have hb := @yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 r a b (C*KdVPlan.EssH s a b f) (fun t => A (f t)) (mul_nonneg hC ENNReal.toReal_nonneg) hnorm
  exact ⟨⟨hm,hmem,hb.2⟩,hb.1⟩

theorem yui_aux_0108 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N : ℝ) (μ : Measure ℝ) (f : KdVPlan.Path), (∀ k, AEStronglyMeasurable (fun t => f t k) μ) → ∀ k, AEStronglyMeasurable (fun t => KdVPlan.cutoff N (f t) k) μ ∧ AEStronglyMeasurable (fun t => KdVPlan.high N (f t) k) μ" := by
  intro N μ f hf k
  have hc : AEStronglyMeasurable (fun t => KdVPlan.cutoff N (f t) k) μ := by
    by_cases hk : |(k:ℝ)| ≤ N
    · change AEStronglyMeasurable (fun t => if |(k:ℝ)| ≤ N then f t k else 0) μ
      simp only [if_pos hk]
      exact hf k
    · change AEStronglyMeasurable (fun t => if |(k:ℝ)| ≤ N then f t k else 0) μ
      simp only [if_neg hk]
      exact aestronglyMeasurable_const
  refine ⟨hc,?_⟩
  exact (hf k).sub hc

theorem yui_aux_0109 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b N : ℝ) (f : KdVPlan.Path), KdVPlan.EssBound s a b f → (KdVPlan.EssBound s a b (fun t => KdVPlan.cutoff N (f t)) ∧ KdVPlan.EssH s a b (fun t => KdVPlan.cutoff N (f t)) ≤ KdVPlan.EssH s a b f) ∧ (KdVPlan.EssBound s a b (fun t => KdVPlan.high N (f t)) ∧ KdVPlan.EssH s a b (fun t => KdVPlan.high N (f t)) ≤ KdVPlan.EssH s a b f)" := by
  intro s a b N f hf
  have hm := @yui_aux_0108 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N (volume.restrict (Icc a b)) f hf.1
  have hc := @yui_aux_0107 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s s a b 1 (KdVPlan.cutoff N) f (by norm_num) hf (fun u hu => by simpa only [one_mul] using (@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s N u hu).1) (fun k => (hm k).1)
  have hh := @yui_aux_0107 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s s a b 1 (KdVPlan.high N) f (by norm_num) hf (fun u hu => by simpa only [one_mul] using (@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s N u hu).2) (fun k => (hm k).2)
  exact ⟨by simpa only [one_mul] using hc,by simpa only [one_mul] using hh⟩

theorem yui_aux_0110 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N : ℝ) (f : KdVPlan.Path), KdVPlan.dt (fun t => KdVPlan.cutoff N (f t)) = (fun t => KdVPlan.cutoff N (KdVPlan.dt f t)) ∧ KdVPlan.dt (fun t => KdVPlan.high N (f t)) = (fun t => KdVPlan.high N (KdVPlan.dt f t))" := by
  intro N f
  constructor <;> funext t k <;> by_cases hk : |(k:ℝ)| ≤ N
  all_goals simp [KdVPlan.dt,KdVPlan.cutoff,KdVPlan.high,hk]

theorem yui_aux_0111 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b N : ℝ) (f : KdVPlan.Path), KdVPlan.XPath 0 a b f (KdVPlan.dt f) → KdVPlan.Xnorm a b (fun t => KdVPlan.cutoff N (f t)) (KdVPlan.dt (fun t => KdVPlan.cutoff N (f t))) ≤ KdVPlan.Xnorm a b f (KdVPlan.dt f) ∧ KdVPlan.Xnorm a b (fun t => KdVPlan.high N (f t)) (KdVPlan.dt (fun t => KdVPlan.high N (f t))) ≤ KdVPlan.Xnorm a b f (KdVPlan.dt f)" := by
  intro a b N f hf
  have h0 := @yui_aux_0109 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b N f hf.2.1
  have hd := @yui_aux_0109 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-KdVPlan.pstar) a b N (KdVPlan.dt f) hf.2.2
  have heq := @yui_aux_0110 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N f
  constructor
  · unfold KdVPlan.Xnorm
    rw [heq.1]
    exact add_le_add h0.1.2 hd.1.2
  · unfold KdVPlan.Xnorm
    rw [heq.2]
    exact add_le_add h0.2.2 hd.2.2

theorem yui_aux_0112 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b l r : ℝ) (f : KdVPlan.Path), a ≤ l → r ≤ b → KdVPlan.EssBound s a b f → KdVPlan.EssBound s l r f ∧ KdVPlan.EssH s l r f ≤ KdVPlan.EssH s a b f" := by
  intro s a b l r f hal hrb hf
  have hsub : Icc l r ⊆ Icc a b := Icc_subset_Icc hal hrb
  have hnorm := ae_restrict_of_ae_restrict_of_subset hsub (@yui_aux_0104 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f hf)
  have hb := @yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s l r (KdVPlan.EssH s a b f) f ENNReal.toReal_nonneg hnorm
  have hmem := ae_restrict_of_ae_restrict_of_subset hsub hf.2.1
  have hm (k : ℤ) : AEStronglyMeasurable (fun t => f t k) (volume.restrict (Icc l r)) := (hf.1 k).mono_measure (Measure.restrict_mono hsub le_rfl)
  exact ⟨⟨hm,hmem,hb.2⟩,hb.1⟩

theorem yui_aux_0113 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), (∀ᵐ t ∂(volume.restrict (Icc a b)), f t = g t) → KdVPlan.EssH s a b f = KdVPlan.EssH s a b g" := by
  intro s a b f g heq
  apply congrArg ENNReal.toReal
  apply essSup_congr_ae
  filter_upwards [heq] with t ht
  rw [ht]

theorem yui_aux_0114 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), KdVPlan.EssBound s a b f → KdVPlan.EssBound s a b g → KdVPlan.EssBound s a b (fun t => f t-g t) ∧ KdVPlan.EssH s a b (fun t => f t-g t) ≤ KdVPlan.EssH s a b f+KdVPlan.EssH s a b g" := by
  intro s a b f g hf hg
  have hs := @yui_aux_0106 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b (-1) g hg
  have hc : ‖(-1:ℂ)‖ = (1:ℝ) := by norm_num
  rw [hc,one_mul] at hs
  have ha := @yui_aux_0105 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f (fun t => KdVPlan.scale (-1) (g t)) hf hs.1
  have heq : (fun t => f t+KdVPlan.scale (-1) (g t)) = (fun t => f t-g t) := by
    funext t k
    simp [KdVPlan.scale,sub_eq_add_neg]
  rw [heq] at ha
  exact ⟨ha.1,ha.2.trans (add_le_add le_rfl hs.2)⟩

theorem yui_aux_0115 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f g : KdVPlan.Path), KdVPlan.EssBound s a b f → (∀ᵐ t ∂(volume.restrict (Icc a b)), f t = g t) → KdVPlan.EssBound s a b g ∧ KdVPlan.EssH s a b g = KdVPlan.EssH s a b f" := by
  intro s a b f g hf heq
  have hm (k : ℤ) : AEStronglyMeasurable (fun t => g t k) (volume.restrict (Icc a b)) := (hf.1 k).congr (heq.mono (fun t ht => congrFun ht k))
  have hmem : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.MemH s (g t) := by
    filter_upwards [hf.2.1,heq] with t ht he
    rw [← he]
    exact ht
  have hsup := essSup_congr_ae (heq.mono (fun t ht => congrArg (fun u => ENNReal.ofReal (KdVPlan.hn s u)) ht))
  refine ⟨⟨hm,hmem,?_⟩,(@yui_aux_0113 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b f g heq).symm⟩
  rw [← hsup]
  exact hf.2.2

theorem yui_aux_0116 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (v e : KdVPlan.Path), KdVPlan.Piecewise a b v → KdVPlan.Piecewise a b e → KdVPlan.XPath 0 a b v (KdVPlan.dt v) → KdVPlan.XPath 0 a b e (KdVPlan.dt e) → let g : KdVPlan.Path := fun t => v t-KdVPlan.scale (1/2) (e t); KdVPlan.EssBound 0 a b g ∧ KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt g) ∧ KdVPlan.Xnorm a b g (KdVPlan.dt g) ≤ KdVPlan.Xnorm a b v (KdVPlan.dt v)+(1/2:ℝ)*KdVPlan.Xnorm a b e (KdVPlan.dt e)" := by
  intro a b v e pv pe hv he
  let g : KdVPlan.Path := fun t => v t-KdVPlan.scale (1/2) (e t)
  have hsc0 := @yui_aux_0106 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b (1/2) e he.2.1
  have hscd := @yui_aux_0106 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-KdVPlan.pstar) a b (1/2) (KdVPlan.dt e) he.2.2
  have hc : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
  rw [hc] at hsc0 hscd
  have hg0 := @yui_aux_0114 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b v (fun t => KdVPlan.scale (1/2) (e t)) hv.2.1 hsc0.1
  have hgd := @yui_aux_0114 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-KdVPlan.pstar) a b (KdVPlan.dt v) (fun t => KdVPlan.scale (1/2) (KdVPlan.dt e t)) hv.2.2 hscd.1
  have hdv := @yui_aux_0067 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b v pv
  have hde := @yui_aux_0067 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b e pe
  have hdt : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.dt v t-KdVPlan.scale (1/2) (KdVPlan.dt e t) = KdVPlan.dt g t := by
    filter_upwards [hdv,hde] with t hvd hed
    funext k
    exact ((hvd.1 k).hasDerivAt.sub ((hed.1 k).hasDerivAt.const_mul (1/2:ℂ))).deriv.symm
  have hgc := @yui_aux_0115 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-KdVPlan.pstar) a b (fun t => KdVPlan.dt v t-KdVPlan.scale (1/2) (KdVPlan.dt e t)) (KdVPlan.dt g) hgd.1 hdt
  refine ⟨hg0.1,hgc.1,?_⟩
  change KdVPlan.EssH 0 a b g+KdVPlan.EssH (-KdVPlan.pstar) a b (KdVPlan.dt g) ≤ (KdVPlan.EssH 0 a b v+KdVPlan.EssH (-KdVPlan.pstar) a b (KdVPlan.dt v))+(1/2:ℝ)*(KdVPlan.EssH 0 a b e+KdVPlan.EssH (-KdVPlan.pstar) a b (KdVPlan.dt e))
  rw [hgc.2]
  linarith [hg0.2,hgd.2,hsc0.2,hscd.2]

theorem yui_aux_0117 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (A : KdVPlan.Coeff → KdVPlan.Coeff) (f : KdVPlan.Path), (∀ u, KdVPlan.MemH s u → KdVPlan.HB s (A u) (KdVPlan.hn s u)) → (∀ u w, A (u-w) = A u-A w) → KdVPlan.ContH s a b f → KdVPlan.ContH s a b (fun t => A (f t))" := by
  intro s a b A f hA hsub hf
  constructor
  · intro t ht
    exact (hA (f t) (hf.1 t ht)).1
  · intro t ht ε hε
    obtain ⟨δ,hδ,hd⟩ := hf.2 t ht ε hε
    refine ⟨δ,hδ,?_⟩
    intro r hr hrt
    rw [← hsub]
    have hm := (@yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s (f r) (f t) (hf.1 r hr) (hf.1 t ht)).1
    exact (hA (f r-f t) hm).2.trans_lt (hd r hr hrt)

theorem yui_aux_0118 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b N : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → KdVPlan.ContH s a b (fun t => KdVPlan.cutoff N (f t)) ∧ KdVPlan.ContH s a b (fun t => KdVPlan.high N (f t))" := by
  intro s a b N f hf
  constructor
  · apply @yui_aux_0117 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b (KdVPlan.cutoff N) f (fun u hu => (@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s N u hu).1) ?_ hf
    intro u w
    funext k
    by_cases hk : |(k:ℝ)| ≤ N <;> simp [KdVPlan.cutoff,hk]
  · apply @yui_aux_0117 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s a b (KdVPlan.high N) f (fun u hu => (@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s N u hu).2) ?_ hf
    intro u w
    funext k
    by_cases hk : |(k:ℝ)| ≤ N <;> simp [KdVPlan.high,KdVPlan.cutoff,hk]

theorem yui_aux_0119 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N : ℝ) (j : ℕ) (s : Set ℝ) (f : KdVPlan.Path) (t : ℝ), (fun k => iteratedDerivWithin j (fun r => KdVPlan.cutoff N (f r) k) s t) = KdVPlan.cutoff N (fun k => iteratedDerivWithin j (fun r => f r k) s t) ∧ (fun k => iteratedDerivWithin j (fun r => KdVPlan.high N (f r) k) s t) = KdVPlan.high N (fun k => iteratedDerivWithin j (fun r => f r k) s t)" := by
  intro N j s f t
  constructor <;> funext k <;> by_cases hk : |(k:ℝ)| ≤ N
  all_goals simp [KdVPlan.cutoff,KdVPlan.high,hk,iteratedDerivWithin_const_zero]

theorem yui_aux_0120 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b N : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b (fun t => KdVPlan.cutoff N (f t)) ∧ KdVPlan.SmoothOn a b (fun t => KdVPlan.high N (f t))" := by
  intro a b N f hf
  constructor
  · constructor
    · intro k
      by_cases hk : |(k:ℝ)| ≤ N
      · simpa only [KdVPlan.cutoff,if_pos hk] using hf.1 k
      · simp only [KdVPlan.cutoff,if_neg hk]
        exact contDiffOn_const
    · intro m j
      have hc := (@yui_aux_0118 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b N (fun t k => iteratedDerivWithin j (fun r => f r k) (Icc a b) t) (hf.2 m j)).1
      apply @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b _ _ ?_ hc
      intro t ht
      exact (@yui_aux_0119 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N j (Icc a b) f t).1.symm
  · constructor
    · intro k
      by_cases hk : |(k:ℝ)| ≤ N
      · simp only [KdVPlan.high,KdVPlan.cutoff,if_pos hk,Pi.sub_apply,sub_self]
        exact contDiffOn_const
      · simpa only [KdVPlan.high,KdVPlan.cutoff,if_neg hk,Pi.sub_apply,sub_zero] using hf.1 k
    · intro m j
      have hc := (@yui_aux_0118 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b N (fun t k => iteratedDerivWithin j (fun r => f r k) (Icc a b) t) (hf.2 m j)).2
      apply @yui_aux_0018 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b _ _ ?_ hc
      intro t ht
      exact (@yui_aux_0119 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N j (Icc a b) f t).2.symm

theorem yui_aux_0121 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b N : ℝ) (f : KdVPlan.Path), KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b (fun t => KdVPlan.cutoff N (f t)) ∧ KdVPlan.Piecewise a b (fun t => KdVPlan.high N (f t))" := by
  intro a b N f hf
  obtain ⟨p,hp⟩ := hf.2
  constructor
  · constructor
    · intro m
      exact (@yui_aux_0118 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b N f (hf.1 m)).1
    · refine ⟨p,?_⟩
      intro l r hal hlr hrb hfree
      exact (@yui_aux_0120 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l r N f (hp l r hal hlr hrb hfree)).1
  · constructor
    · intro m
      exact (@yui_aux_0118 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (m:ℝ) a b N f (hf.1 m)).2
    · refine ⟨p,?_⟩
      intro l r hal hlr hrb hfree
      exact (@yui_aux_0120 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 l r N f (hp l r hal hlr hrb hfree)).2

theorem yui_aux_0122 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ F : ℤ → ℂ, (∀ j, F j=0) → (∑' j, F j)=0" := by
  intro F hF
  have heq : F = fun _ => 0 := funext hF
  rw [heq]
  simp

theorem yui_aux_0123 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (A B : ℝ) (f g : KdVPlan.Coeff), (∀ k : ℤ, A < |(k:ℝ)| → f k=0) → (∀ k : ℤ, B < |(k:ℝ)| → g k=0) → ∀ k : ℤ, A+B < |(k:ℝ)| → KdVPlan.mul f g k=0" := by
  intro A B f g hf hg k hk
  change (∑' j : ℤ, f j*g (k-j)) = 0
  apply @yui_aux_0122 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (fun j => f j*g (k-j))
  intro j
  by_cases hj : |(j:ℝ)| ≤ A
  · by_cases hl : |((k-j:ℤ):ℝ)| ≤ B
    · have heq : (k:ℝ) = (j:ℝ)+((k-j:ℤ):ℝ) := by push_cast; ring
      have hh : |(k:ℝ)| ≤ |(j:ℝ)|+|((k-j:ℤ):ℝ)| := by
        conv_lhs => rw [heq]
        exact abs_add_le _ _
      exfalso
      linarith
    · rw [hg (k-j) (lt_of_not_ge hl),mul_zero]
  · rw [hf j (lt_of_not_ge hj),zero_mul]

theorem yui_aux_0124 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f : KdVPlan.Coeff) (k : ℤ), f k=0 → KdVPlan.S t f k=0 ∧ KdVPlan.invD f k=0 ∧ KdVPlan.P f k=0" := by
  intro t f k hk
  simp [KdVPlan.S,KdVPlan.invD,KdVPlan.P,hk]

theorem yui_aux_0125 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b A B C : ℝ) (f g h : KdVPlan.Path), (∀ (t : ℝ) (k : ℤ), A < |(k:ℝ)| → f t k=0) → (∀ (t : ℝ) (k : ℤ), B < |(k:ℝ)| → g t k=0) → (∀ (t : ℝ) (k : ℤ), C < |(k:ℝ)| → h t k=0) → ∀ k : ℤ, A+B+C < |(k:ℝ)| → KdVPlan.tri a b f g h k=0" := by
  intro a b A B C f g h hf hg hh k hk
  let diag := @yui_aux_0124 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  let conv := @yui_aux_0123 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have hz (s : ℝ) : KdVPlan.S (-s) (KdVPlan.P (KdVPlan.mul (KdVPlan.P (KdVPlan.mul (KdVPlan.S s (f s)) (KdVPlan.S s (g s)))) (KdVPlan.S s (KdVPlan.invD (h s))))) k=0 := by
    have hfs (j : ℤ) (hj : A < |(j:ℝ)|) : KdVPlan.S s (f s) j=0 := (diag s (f s) j (hf s j hj)).1
    have hgs (j : ℤ) (hj : B < |(j:ℝ)|) : KdVPlan.S s (g s) j=0 := (diag s (g s) j (hg s j hj)).1
    have hhs (j : ℤ) (hj : C < |(j:ℝ)|) : KdVPlan.S s (KdVPlan.invD (h s)) j=0 := (diag s (KdVPlan.invD (h s)) j (diag s (h s) j (hh s j hj)).2.1).1
    have hin (j : ℤ) (hj : A+B < |(j:ℝ)|) : KdVPlan.P (KdVPlan.mul (KdVPlan.S s (f s)) (KdVPlan.S s (g s))) j=0 := (diag s _ j (conv A B _ _ hfs hgs j hj)).2.2
    have hout : KdVPlan.mul (KdVPlan.P (KdVPlan.mul (KdVPlan.S s (f s)) (KdVPlan.S s (g s)))) (KdVPlan.S s (KdVPlan.invD (h s))) k=0 := conv (A+B) C _ _ hin hhs k hk
    exact (diag (-s) _ k (diag (-s) _ k hout).2.2).1
  change (∫ s in a..b, KdVPlan.S (-s) (KdVPlan.P (KdVPlan.mul (KdVPlan.P (KdVPlan.mul (KdVPlan.S s (f s)) (KdVPlan.S s (g s)))) (KdVPlan.S s (KdVPlan.invD (h s))))) k) = 0
  calc
    _ = ∫ s in a..b, (0:ℂ) := intervalIntegral.integral_congr (fun s _ => hz s)
    _ = 0 := by simp

theorem yui_aux_0126 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b N : ℝ) (f g h : KdVPlan.Path), KdVPlan.high N (KdVPlan.tri a b (fun t => KdVPlan.cutoff (N/3) (f t)) (fun t => KdVPlan.cutoff (N/3) (g t)) (fun t => KdVPlan.cutoff (N/3) (h t))) = 0" := by
  intro a b N f g h
  have hcut (u : KdVPlan.Path) (t : ℝ) (k : ℤ) (hk : N/3 < |(k:ℝ)|) : KdVPlan.cutoff (N/3) (u t) k=0 := by
    simp only [KdVPlan.cutoff,if_neg (not_le_of_gt hk)]
  have hband := @yui_aux_0125 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (N/3) (N/3) (N/3) (fun t => KdVPlan.cutoff (N/3) (f t)) (fun t => KdVPlan.cutoff (N/3) (g t)) (fun t => KdVPlan.cutoff (N/3) (h t)) (hcut f) (hcut g) (hcut h)
  funext k
  by_cases hk : |(k:ℝ)| ≤ N
  · simp [KdVPlan.high,KdVPlan.cutoff,hk]
  · have hz := hband k (by linarith [lt_of_not_ge hk])
    simp only [KdVPlan.high,KdVPlan.cutoff,if_neg hk,Pi.sub_apply,sub_zero,hz,Pi.zero_apply]

theorem yui_aux_0127 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g h : KdVPlan.Path), KdVPlan.tri a b f g h = KdVPlan.tri a b g f h" := by
  intro a b f g h
  unfold KdVPlan.tri
  congr 1
  funext t
  rw [(@yui_aux_0051 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (KdVPlan.S t (f t)) (KdVPlan.S t (g t))).1]

theorem yui_aux_0128 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f f' g h : KdVPlan.Path), a ≤ b → KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b f' → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b h → (∀ t ∈ Icc a b, KdVPlan.ZeroMean (f t) ∧ KdVPlan.ZeroMean (f' t) ∧ KdVPlan.ZeroMean (g t) ∧ KdVPlan.ZeroMean (h t)) → KdVPlan.tri a b (fun t => f t+f' t) g h = KdVPlan.tri a b f g h+KdVPlan.tri a b f' g h" := by
  intro a b f f' g h hab pf pf' pg ph hz
  have ps := @yui_aux_0021 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b f f' pf pf'
  have zs : ∀ t ∈ Icc a b, KdVPlan.ZeroMean (f t+f' t) ∧ KdVPlan.ZeroMean (g t) ∧ KdVPlan.ZeroMean (h t) := by
    intro t ht
    refine ⟨?_,(hz t ht).2.2.1,(hz t ht).2.2.2⟩
    change f t 0+f' t 0=0
    rw [(hz t ht).1,(hz t ht).2.1]
    simp
  have hnfs := h_T005.2.2.2.1 a b (fun t => f t+f' t) g h hab ps pg ph zs
  have hnff := h_T005.2.2.2.1 a b f g h hab pf pg ph (fun t ht => ⟨(hz t ht).1,(hz t ht).2.2.1,(hz t ht).2.2.2⟩)
  have hnff' := h_T005.2.2.2.1 a b f' g h hab pf' pg ph (fun t ht => ⟨(hz t ht).2.1,(hz t ht).2.2.1,(hz t ht).2.2.2⟩)
  have hf1 : KdVPlan.ContH 1 a b f := by simpa only [Nat.cast_one] using pf.1 1
  have hf1' : KdVPlan.ContH 1 a b f' := by simpa only [Nat.cast_one] using pf'.1 1
  have hg1 : KdVPlan.ContH 1 a b g := by simpa only [Nat.cast_one] using pg.1 1
  have hh0 : KdVPlan.ContH 0 a b h := by simpa only [Nat.cast_zero] using ph.1 0
  have hi1 := @yui_aux_0097 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b f g h hab hf1 hg1 hh0
  have hi2 := @yui_aux_0097 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b f' g h hab hf1' hg1 hh0
  obtain ⟨Cb,hCb,hB⟩ := @yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have hj (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.J t (KdVPlan.B t (f t+f' t) (g t)) (h t) = KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t)+KdVPlan.J t (KdVPlan.B t (f' t) (g t)) (h t) := by
    have hf0 : KdVPlan.MemH 0 (f t) := by simpa only [Nat.cast_zero] using (pf.1 0).1 t ht
    have hf0' : KdVPlan.MemH 0 (f' t) := by simpa only [Nat.cast_zero] using (pf'.1 0).1 t ht
    have hg0 : KdVPlan.MemH 0 (g t) := by simpa only [Nat.cast_zero] using (pg.1 0).1 t ht
    rw [(@yui_aux_0054 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t (f t) (f' t) (g t) hf0 hf0' hg0).1]
    exact (@yui_aux_0083 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t (KdVPlan.B t (f t) (g t)) (KdVPlan.B t (f' t) (g t)) (h t) (hB t (f t) (g t) (hf1.1 t ht) (hg1.1 t ht)).1 (hB t (f' t) (g t) (hf1'.1 t ht) (hg1.1 t ht)).1 (hh0.1 t ht)).1
  rw [← hnfs,← hnff,← hnff']
  funext k
  change (∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f t+f' t) (g t)) (h t) k) = (∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t) k)+(∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f' t) (g t)) (h t) k)
  calc
    _ = ∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t) k+KdVPlan.J t (KdVPlan.B t (f' t) (g t)) (h t) k := intervalIntegral.integral_congr (fun t ht => congrFun (hj t (by simpa only [uIcc_of_le hab] using ht)) k)
    _ = _ := intervalIntegral.integral_add (hi1 k) (hi2 k)

theorem yui_aux_0129 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g h h' : KdVPlan.Path), a ≤ b → KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b h → KdVPlan.Piecewise a b h' → (∀ t ∈ Icc a b, KdVPlan.ZeroMean (f t) ∧ KdVPlan.ZeroMean (g t) ∧ KdVPlan.ZeroMean (h t) ∧ KdVPlan.ZeroMean (h' t)) → KdVPlan.tri a b f g (fun t => h t+h' t) = KdVPlan.tri a b f g h+KdVPlan.tri a b f g h'" := by
  intro a b f g h h' hab pf pg ph ph' hz
  have ps := @yui_aux_0021 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b h h' ph ph'
  have zs : ∀ t ∈ Icc a b, KdVPlan.ZeroMean (f t) ∧ KdVPlan.ZeroMean (g t) ∧ KdVPlan.ZeroMean (h t+h' t) := by
    intro t ht
    refine ⟨(hz t ht).1,(hz t ht).2.1,?_⟩
    change h t 0+h' t 0=0
    rw [(hz t ht).2.2.1,(hz t ht).2.2.2]
    simp
  have hnfs := h_T005.2.2.2.1 a b f g (fun t => h t+h' t) hab pf pg ps zs
  have hnfh := h_T005.2.2.2.1 a b f g h hab pf pg ph (fun t ht => ⟨(hz t ht).1,(hz t ht).2.1,(hz t ht).2.2.1⟩)
  have hnfh' := h_T005.2.2.2.1 a b f g h' hab pf pg ph' (fun t ht => ⟨(hz t ht).1,(hz t ht).2.1,(hz t ht).2.2.2⟩)
  have hf1 : KdVPlan.ContH 1 a b f := by simpa only [Nat.cast_one] using pf.1 1
  have hg1 : KdVPlan.ContH 1 a b g := by simpa only [Nat.cast_one] using pg.1 1
  have hh0 : KdVPlan.ContH 0 a b h := by simpa only [Nat.cast_zero] using ph.1 0
  have hh0' : KdVPlan.ContH 0 a b h' := by simpa only [Nat.cast_zero] using ph'.1 0
  have hi1 := @yui_aux_0097 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b f g h hab hf1 hg1 hh0
  have hi2 := @yui_aux_0097 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b f g h' hab hf1 hg1 hh0'
  obtain ⟨Cb,hCb,hB⟩ := @yui_aux_0085 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have hj (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t+h' t) = KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t)+KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h' t) := (@yui_aux_0088 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 t (KdVPlan.B t (f t) (g t)) (h t) (h' t) (hB t (f t) (g t) (hf1.1 t ht) (hg1.1 t ht)).1 (hh0.1 t ht) (hh0'.1 t ht)).1
  rw [← hnfs,← hnfh,← hnfh']
  funext k
  change (∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t+h' t) k) = (∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t) k)+(∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h' t) k)
  calc
    _ = ∫ t in a..b, KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t) k+KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h' t) k := intervalIntegral.integral_congr (fun t ht => congrFun (hj t (by simpa only [uIcc_of_le hab] using ht)) k)
    _ = _ := intervalIntegral.integral_add (hi1 k) (hi2 k)

theorem yui_aux_0130 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N : ℝ) (f : KdVPlan.Coeff), KdVPlan.ZeroMean f → KdVPlan.ZeroMean (KdVPlan.cutoff N f) ∧ KdVPlan.ZeroMean (KdVPlan.high N f)" := by
  intro N f hf
  change f 0=0 at hf
  constructor
  · change KdVPlan.cutoff N f 0=0
    simp [KdVPlan.cutoff,hf]
  · change KdVPlan.high N f 0=0
    simp [KdVPlan.high,KdVPlan.cutoff,hf]

theorem yui_aux_0131 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b N : ℝ) (f g h : KdVPlan.Path), a ≤ b → KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b h → (∀ t ∈ Icc a b, KdVPlan.ZeroMean (f t) ∧ KdVPlan.ZeroMean (g t) ∧ KdVPlan.ZeroMean (h t)) → KdVPlan.tri a b f g h = KdVPlan.tri a b (fun t => KdVPlan.high N (f t)) g h+KdVPlan.tri a b (fun t => KdVPlan.cutoff N (f t)) (fun t => KdVPlan.high N (g t)) h+KdVPlan.tri a b (fun t => KdVPlan.cutoff N (f t)) (fun t => KdVPlan.cutoff N (g t)) (fun t => KdVPlan.high N (h t))+KdVPlan.tri a b (fun t => KdVPlan.cutoff N (f t)) (fun t => KdVPlan.cutoff N (g t)) (fun t => KdVPlan.cutoff N (h t))" := by
  intro a b N f g h hab pf pg ph hz
  let Lo : KdVPlan.Path → KdVPlan.Path := fun u t => KdVPlan.cutoff N (u t)
  let Hi : KdVPlan.Path → KdVPlan.Path := fun u t => KdVPlan.high N (u t)
  have hdec (u : KdVPlan.Path) : (fun t => Hi u t+Lo u t) = u := by
    funext t
    change (u t-KdVPlan.cutoff N (u t))+KdVPlan.cutoff N (u t)=u t
    abel
  have pproj := @yui_aux_0121 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have pfL : KdVPlan.Piecewise a b (Lo f) := (pproj a b N f pf).1
  have pfH : KdVPlan.Piecewise a b (Hi f) := (pproj a b N f pf).2
  have pgL : KdVPlan.Piecewise a b (Lo g) := (pproj a b N g pg).1
  have pgH : KdVPlan.Piecewise a b (Hi g) := (pproj a b N g pg).2
  have phL : KdVPlan.Piecewise a b (Lo h) := (pproj a b N h ph).1
  have phH : KdVPlan.Piecewise a b (Hi h) := (pproj a b N h ph).2
  have zproj := @yui_aux_0130 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have zf (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.ZeroMean (Lo f t) ∧ KdVPlan.ZeroMean (Hi f t) := zproj N (f t) (hz t ht).1
  have zg (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.ZeroMean (Lo g t) ∧ KdVPlan.ZeroMean (Hi g t) := zproj N (g t) (hz t ht).2.1
  have zh (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.ZeroMean (Lo h t) ∧ KdVPlan.ZeroMean (Hi h t) := zproj N (h t) (hz t ht).2.2
  have h1 := @yui_aux_0128 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (Hi f) (Lo f) g h hab pfH pfL pg ph (fun t ht => ⟨(zf t ht).2,(zf t ht).1,(hz t ht).2.1,(hz t ht).2.2⟩)
  rw [hdec f] at h1
  have h2 := @yui_aux_0128 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (Hi g) (Lo g) (Lo f) h hab pgH pgL pfL ph (fun t ht => ⟨(zg t ht).2,(zg t ht).1,(zf t ht).1,(hz t ht).2.2⟩)
  rw [hdec g] at h2
  rw [@yui_aux_0127 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b g (Lo f) h,@yui_aux_0127 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (Hi g) (Lo f) h,@yui_aux_0127 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (Lo g) (Lo f) h] at h2
  have h3 := @yui_aux_0129 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (Lo f) (Lo g) (Hi h) (Lo h) hab pfL pgL phH phL (fun t ht => ⟨(zf t ht).1,(zg t ht).1,(zh t ht).2,(zh t ht).1⟩)
  rw [hdec h] at h3
  change KdVPlan.tri a b f g h = KdVPlan.tri a b (Hi f) g h+KdVPlan.tri a b (Lo f) (Hi g) h+KdVPlan.tri a b (Lo f) (Lo g) (Hi h)+KdVPlan.tri a b (Lo f) (Lo g) (Lo h)
  rw [h1,h2,h3]
  abel

theorem yui_aux_0132 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s A B : ℝ) (f g : KdVPlan.Coeff), KdVPlan.HB s f A → KdVPlan.HB s g B → KdVPlan.HB s (f+g) (A+B) ∧ KdVPlan.HB s (f-g) (A+B)" := by
  intro s A B f g hf hg
  have ha := @yui_aux_0003 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s f g hf.1 hg.1
  have hs := @yui_aux_0005 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 s f g hf.1 hg.1
  exact ⟨⟨ha.1,ha.2.trans (add_le_add hf.2 hg.2)⟩,⟨hs.1,hs.2.trans (add_le_add hf.2 hg.2)⟩⟩

theorem yui_aux_0133 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N : ℝ) (f g : KdVPlan.Coeff), KdVPlan.cutoff N (f+g) = KdVPlan.cutoff N f+KdVPlan.cutoff N g ∧ KdVPlan.high N (f+g) = KdVPlan.high N f+KdVPlan.high N g" := by
  intro N f g
  constructor <;> funext k <;> by_cases hk : |(k:ℝ)| ≤ N
  all_goals simp [KdVPlan.cutoff,KdVPlan.high,hk]

theorem yui_aux_0134 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b N : ℝ) (f : KdVPlan.Path), KdVPlan.EssBound 0 a b f → KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt f) → let lf : KdVPlan.Path := fun t => KdVPlan.cutoff N (f t); let hf : KdVPlan.Path := fun t => KdVPlan.high N (f t); (KdVPlan.EssBound 0 a b lf ∧ KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt lf) ∧ KdVPlan.Xnorm a b lf (KdVPlan.dt lf) ≤ KdVPlan.Xnorm a b f (KdVPlan.dt f)) ∧ (KdVPlan.EssBound 0 a b hf ∧ KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt hf) ∧ KdVPlan.Xnorm a b hf (KdVPlan.dt hf) ≤ KdVPlan.Xnorm a b f (KdVPlan.dt f))" := by
  intro a b N f hf hd
  have h0 := @yui_aux_0109 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b N f hf
  have h1 := @yui_aux_0109 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-KdVPlan.pstar) a b N (KdVPlan.dt f) hd
  have heq := @yui_aux_0110 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N f
  have hdc : KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt (fun t => KdVPlan.cutoff N (f t))) := by rw [heq.1]; exact h1.1.1
  have hdh : KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt (fun t => KdVPlan.high N (f t))) := by rw [heq.2]; exact h1.2.1
  refine ⟨⟨h0.1.1,hdc,?_⟩,⟨h0.2.1,hdh,?_⟩⟩
  · unfold KdVPlan.Xnorm
    rw [heq.1]
    exact add_le_add h0.1.2 h1.1.2
  · unfold KdVPlan.Xnorm
    rw [heq.2]
    exact add_le_add h0.2.2 h1.2.2

theorem yui_aux_0135 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ N s : ℝ, 0 ≤ N → (N/3)^(-s) = (3:ℝ)^s*N^(-s)" := by
  intro N s hN
  rw [Real.div_rpow hN (by norm_num) (-s),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3) s,div_inv_eq_mul,mul_comm]

theorem yui_aux_0136 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b N C : ℝ) (f : KdVPlan.Path), 2 ≤ N → 0 ≤ C → KdVPlan.UB 0 a b f C → KdVPlan.EssH 0 a b f ≤ C ∧ KdVPlan.EssH 0 a b (fun t => KdVPlan.cutoff (N/3) (f t)) ≤ C ∧ KdVPlan.EssH (-KdVPlan.pstar) a b (fun t => KdVPlan.high (N/3) (f t)) ≤ (3:ℝ)^KdVPlan.pstar*N^(-KdVPlan.pstar)*C" := by
  intro a b N C f hN hC hf
  have hN0 : 0 < N := by linarith
  have hp : 0 ≤ KdVPlan.pstar := by norm_num [KdVPlan.pstar]
  have hfull : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn 0 (f t) ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hf t ht).2
  have hlow : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn 0 (KdVPlan.cutoff (N/3) (f t)) ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ((@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (N/3) (f t) (hf t ht).1).1.2).trans (hf t ht).2
  have hhigh : ∀ᵐ t ∂(volume.restrict (Icc a b)), KdVPlan.hn (-KdVPlan.pstar) (KdVPlan.high (N/3) (f t)) ≤ (3:ℝ)^KdVPlan.pstar*N^(-KdVPlan.pstar)*C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := @yui_aux_0102 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (N/3) KdVPlan.pstar (f t) (by positivity) hp (hf t ht).1
    rw [@yui_aux_0135 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N KdVPlan.pstar hN0.le] at hh
    exact hh.2.trans (mul_le_mul_of_nonneg_left (hf t ht).2 (by positivity))
  exact ⟨(@yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b C f hC hfull).1,(@yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 a b C (fun t => KdVPlan.cutoff (N/3) (f t)) hC hlow).1,(@yui_aux_0103 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (-KdVPlan.pstar) a b ((3:ℝ)^KdVPlan.pstar*N^(-KdVPlan.pstar)*C) (fun t => KdVPlan.high (N/3) (f t)) (by positivity) hhigh).1⟩

theorem yui_aux_0137 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ c x y z X Y Z : ℝ, 0 ≤ c → 0 ≤ y → 0 ≤ z → 0 ≤ X → 0 ≤ Y → x ≤ X → y ≤ Y → z ≤ Z → c*x*y*z ≤ c*X*Y*Z" := by
  intro c x y z X Y Z hc hy hz hX hY hx hyy hzz
  have hxy := mul_le_mul hx hyy hy hX
  have hxyz := mul_le_mul hxy hzz hz (mul_nonneg hX hY)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hxyz hc

theorem yui_aux_0138 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (N A B C : ℝ) (u v w z : KdVPlan.Coeff), KdVPlan.HB 0 u A → KdVPlan.HB 0 v B → KdVPlan.HB 0 w C → KdVPlan.high N z=0 → KdVPlan.HB 0 (KdVPlan.high N (u+v+w+z)) (A+B+C)" := by
  intro N A B C u v w z hu hv hw hz
  have hup := (@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 N u hu.1).2
  have hvp := (@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 N v hv.1).2
  have hwp := (@yui_aux_0007 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 N w hw.1).2
  have hu' : KdVPlan.HB 0 (KdVPlan.high N u) A := ⟨hup.1,hup.2.trans hu.2⟩
  have hv' : KdVPlan.HB 0 (KdVPlan.high N v) B := ⟨hvp.1,hvp.2.trans hv.2⟩
  have hw' : KdVPlan.HB 0 (KdVPlan.high N w) C := ⟨hwp.1,hwp.2.trans hw.2⟩
  have huv := (@yui_aux_0132 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 A B _ _ hu' hv').1
  have huvW := (@yui_aux_0132 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 0 (A+B) C _ _ huv hw').1
  rw [(@yui_aux_0133 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N (u+v+w) z).2,hz,add_zero,(@yui_aux_0133 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N (u+v) w).2,(@yui_aux_0133 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N u v).2]
  exact huvW

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ C : ℝ, 0 < C ∧ ∀ (a b N F G H : ℝ) (f g h : KdVPlan.Path), 0 ≤ a → a ≤ b → b-a ≤ 1 → 2 ≤ N → 0 ≤ F → 0 ≤ G → 0 ≤ H → KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → KdVPlan.Piecewise a b h → (∀ t ∈ Icc a b, KdVPlan.ZeroMean (f t) ∧ KdVPlan.ZeroMean (g t) ∧ KdVPlan.ZeroMean (h t)) → KdVPlan.EssBound 0 a b f → KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt f) → KdVPlan.EssBound 0 a b g → KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt g) → KdVPlan.EssBound 0 a b h → KdVPlan.EssBound (-KdVPlan.pstar) a b (KdVPlan.dt h) → KdVPlan.UB 0 a b f F → KdVPlan.UB 0 a b g G → KdVPlan.UB 0 a b h H → KdVPlan.HB 0 (KdVPlan.high N (KdVPlan.tri a b f g h)) (C*(b-a)*KdVPlan.Xnorm a b f (KdVPlan.dt f)*KdVPlan.Xnorm a b g (KdVPlan.dt g)*KdVPlan.Xnorm a b h (KdVPlan.dt h)+C*N^(-KdVPlan.pstar)*F*G*H)" := by
  obtain ⟨Ct,hCt,htri⟩ := h_T006.1.1
  let D : ℝ := (3:ℝ)^KdVPlan.pstar
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  refine ⟨3*Ct*(1+D),by positivity,?_⟩
  intro a b N F G H f g h ha hab hlen hN hF hG hH pf pg ph hz ef edf eg edg eh edh uf ug uh
  have hN0 : 0 < N := by linarith
  let Lo : KdVPlan.Path → KdVPlan.Path := fun u t => KdVPlan.cutoff (N/3) (u t)
  let Hi : KdVPlan.Path → KdVPlan.Path := fun u t => KdVPlan.high (N/3) (u t)
  let X : KdVPlan.Path → ℝ := fun u => KdVPlan.Xnorm a b u (KdVPlan.dt u)
  have X0 (u : KdVPlan.Path) : 0 ≤ X u := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  let B0 : ℝ := Ct*(b-a)*X f*X g*X h+Ct*D*N^(-KdVPlan.pstar)*F*G*H
  let pp := @yui_aux_0121 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have pfL : KdVPlan.Piecewise a b (Lo f) := (pp a b (N/3) f pf).1
  have pfH : KdVPlan.Piecewise a b (Hi f) := (pp a b (N/3) f pf).2
  have pgL : KdVPlan.Piecewise a b (Lo g) := (pp a b (N/3) g pg).1
  have pgH : KdVPlan.Piecewise a b (Hi g) := (pp a b (N/3) g pg).2
  have phH : KdVPlan.Piecewise a b (Hi h) := (pp a b (N/3) h ph).2
  let zp := @yui_aux_0130 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have zf (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.ZeroMean (Lo f t) ∧ KdVPlan.ZeroMean (Hi f t) := zp (N/3) (f t) (hz t ht).1
  have zg (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.ZeroMean (Lo g t) ∧ KdVPlan.ZeroMean (Hi g t) := zp (N/3) (g t) (hz t ht).2.1
  have zh (t : ℝ) (ht : t ∈ Icc a b) : KdVPlan.ZeroMean (Lo h t) ∧ KdVPlan.ZeroMean (Hi h t) := zp (N/3) (h t) (hz t ht).2.2
  have pxF := @yui_aux_0134 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (N/3) f ef edf
  have pxG := @yui_aux_0134 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (N/3) g eg edg
  have pxH := @yui_aux_0134 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (N/3) h eh edh
  have xFL : X (Lo f) ≤ X f := pxF.1.2.2
  have xFH : X (Hi f) ≤ X f := pxF.2.2.2
  have xGL : X (Lo g) ≤ X g := pxG.1.2.2
  have xGH : X (Hi g) ≤ X g := pxG.2.2.2
  have xHH : X (Hi h) ≤ X h := pxH.2.2.2
  have valF := @yui_aux_0136 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b N F f hN hF uf
  have valG := @yui_aux_0136 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b N G g hN hG ug
  have valH := @yui_aux_0136 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b N H h hN hH uh
  let mono := @yui_aux_0137 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013
  have hc : 0 ≤ Ct*(b-a) := mul_nonneg hCt.le (sub_nonneg.mpr hab)
  have hx1 : Ct*(b-a)*X (Hi f)*X g*X h ≤ Ct*(b-a)*X f*X g*X h := mono (Ct*(b-a)) (X (Hi f)) (X g) (X h) (X f) (X g) (X h) hc (X0 g) (X0 h) (X0 f) (X0 g) xFH le_rfl le_rfl
  have hx2 : Ct*(b-a)*X (Lo f)*X (Hi g)*X h ≤ Ct*(b-a)*X f*X g*X h := mono (Ct*(b-a)) (X (Lo f)) (X (Hi g)) (X h) (X f) (X g) (X h) hc (X0 (Hi g)) (X0 h) (X0 f) (X0 g) xFL xGH le_rfl
  have hx3 : Ct*(b-a)*X (Lo f)*X (Lo g)*X (Hi h) ≤ Ct*(b-a)*X f*X g*X h := mono (Ct*(b-a)) (X (Lo f)) (X (Lo g)) (X (Hi h)) (X f) (X g) (X h) hc (X0 (Lo g)) (X0 (Hi h)) (X0 f) (X0 g) xFL xGL xHH
  have he1 : Ct*KdVPlan.EssH (-KdVPlan.pstar) a b (Hi f)*KdVPlan.EssH 0 a b g*KdVPlan.EssH 0 a b h ≤ Ct*D*N^(-KdVPlan.pstar)*F*G*H := by
    calc
      _ ≤ Ct*(D*N^(-KdVPlan.pstar)*F)*G*H := mono Ct _ _ _ (D*N^(-KdVPlan.pstar)*F) G H hCt.le ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by positivity) hG valF.2.2 valG.1 valH.1
      _ = _ := by ring
  have he2 : Ct*KdVPlan.EssH (-KdVPlan.pstar) a b (Hi g)*KdVPlan.EssH 0 a b (Lo f)*KdVPlan.EssH 0 a b h ≤ Ct*D*N^(-KdVPlan.pstar)*F*G*H := by
    calc
      _ ≤ Ct*(D*N^(-KdVPlan.pstar)*G)*F*H := mono Ct _ _ _ (D*N^(-KdVPlan.pstar)*G) F H hCt.le ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by positivity) hF valG.2.2 valF.2.1 valH.1
      _ = _ := by ring
  have he3 : Ct*KdVPlan.EssH (-KdVPlan.pstar) a b (Hi h)*KdVPlan.EssH 0 a b (Lo f)*KdVPlan.EssH 0 a b (Lo g) ≤ Ct*D*N^(-KdVPlan.pstar)*F*G*H := by
    calc
      _ ≤ Ct*(D*N^(-KdVPlan.pstar)*H)*F*G := mono Ct _ _ _ (D*N^(-KdVPlan.pstar)*H) F G hCt.le ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by positivity) hF valH.2.2 valF.2.1 valG.2.1
      _ = _ := by ring
  have hb1 := (htri a b ha hab hlen (Hi f) g h pfH pg ph (fun t ht => ⟨(zf t ht).2,(hz t ht).2.1,(hz t ht).2.2⟩)).1
  have hb2 := (htri a b ha hab hlen (Lo f) (Hi g) h pfL pgH ph (fun t ht => ⟨(zf t ht).1,(zg t ht).2,(hz t ht).2.2⟩)).2.1
  have hb3 := (htri a b ha hab hlen (Lo f) (Lo g) (Hi h) pfL pgL phH (fun t ht => ⟨(zf t ht).1,(zg t ht).1,(zh t ht).2⟩)).2.2
  have h1 : KdVPlan.HB 0 (KdVPlan.tri a b (Hi f) g h) B0 := ⟨hb1.1,hb1.2.trans (add_le_add hx1 he1)⟩
  have h2 : KdVPlan.HB 0 (KdVPlan.tri a b (Lo f) (Hi g) h) B0 := ⟨hb2.1,hb2.2.trans (add_le_add hx2 he2)⟩
  have h3 : KdVPlan.HB 0 (KdVPlan.tri a b (Lo f) (Lo g) (Hi h)) B0 := ⟨hb3.1,hb3.2.trans (add_le_add hx3 he3)⟩
  have hzlow : KdVPlan.high N (KdVPlan.tri a b (Lo f) (Lo g) (Lo h))=0 := @yui_aux_0126 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b N f g h
  have hs := @yui_aux_0138 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 N B0 B0 B0 _ _ _ _ h1 h2 h3 hzlow
  have hdec : KdVPlan.tri a b f g h = KdVPlan.tri a b (Hi f) g h+KdVPlan.tri a b (Lo f) (Hi g) h+KdVPlan.tri a b (Lo f) (Lo g) (Hi h)+KdVPlan.tri a b (Lo f) (Lo g) (Lo h) := @yui_aux_0131 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 a b (N/3) f g h hab pf pg ph hz
  rw [← hdec] at hs
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hX : 0 ≤ (b-a)*X f*X g*X h := mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (X0 f)) (X0 g)) (X0 h)
  have hV : 0 ≤ N^(-KdVPlan.pstar)*F*G*H := by positivity
  change B0+B0+B0 ≤ 3*Ct*(1+D)*(b-a)*X f*X g*X h+3*Ct*(1+D)*N^(-KdVPlan.pstar)*F*G*H
  dsimp only [B0]
  nlinarith [mul_nonneg (by positivity : 0 ≤ 3*Ct*D) hX,mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 3*Ct)]
#check @checked
#print axioms checked
end YuiAuxiliary
