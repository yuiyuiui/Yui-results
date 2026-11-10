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

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_T005 : KdVPlan.BilinearOutput) (h_T006 : KdVPlan.ContinuousOutput gamma) (h_T008 : KdVPlan.StageOutput gamma) (h_T009 : KdVPlan.ResidualOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f : KdVPlan.Coeff) (k : ℤ), ‖KdVPlan.S t f k‖ = ‖f k‖" := by
  intro t f k
  change ‖Complex.exp (Complex.I * ((t*(k:ℝ)^3 : ℝ):ℂ)) * f k‖ = ‖f k‖
  rw [norm_mul, @yui_aux_0033 T gamma R h_H002 h_T005 h_T006 h_T008 h_T009 h_T013 (t*(k:ℝ)^3),one_mul]
#check @checked
#print axioms checked
end YuiAuxiliary
