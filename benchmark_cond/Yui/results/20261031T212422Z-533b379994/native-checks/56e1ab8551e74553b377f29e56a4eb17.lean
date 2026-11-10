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
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), 0 ≤ KdVPlan.hn s f" := by
  intro s f
  exact Real.sqrt_nonneg _

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ),\n (∀ f g : KdVPlan.Coeff, KdVPlan.MemH s f → KdVPlan.MemH s g →\n   KdVPlan.MemH s (f+g) ∧ KdVPlan.hn s (f+g) ≤ KdVPlan.hn s f+KdVPlan.hn s g) ∧\n (∀ f g : KdVPlan.Coeff, KdVPlan.MemH s f → KdVPlan.MemH s g →\n   KdVPlan.MemH s (f-g) ∧ KdVPlan.hn s (f-g) ≤ KdVPlan.hn s f+KdVPlan.hn s g) ∧\n (∀ (c : ℂ) (f : KdVPlan.Coeff), KdVPlan.MemH s f →\n   KdVPlan.MemH s (KdVPlan.scale c f) ∧ KdVPlan.hn s (KdVPlan.scale c f) = ‖c‖*KdVPlan.hn s f)" := by
  intro s
  rcases h_T013 with ⟨hmem, hiso, hrest⟩
  constructor
  · intro f g hf hg
    rcases (hmem s f).mp hf with ⟨x, rfl⟩
    rcases (hmem s g).mp hg with ⟨y, rfl⟩
    have heq : KdVPlan.FromLP s x + KdVPlan.FromLP s y = KdVPlan.FromLP s (x+y) := by
      ext k
      simp [KdVPlan.FromLP, mul_add]
    rw [heq]
    exact ⟨(hmem _ _).mpr ⟨x+y, rfl⟩, by simpa [hiso] using norm_add_le x y⟩
  constructor
  · intro f g hf hg
    rcases (hmem s f).mp hf with ⟨x, rfl⟩
    rcases (hmem s g).mp hg with ⟨y, rfl⟩
    have heq : KdVPlan.FromLP s x - KdVPlan.FromLP s y = KdVPlan.FromLP s (x-y) := by
      ext k
      simp [KdVPlan.FromLP, mul_sub]
    rw [heq]
    exact ⟨(hmem _ _).mpr ⟨x-y, rfl⟩, by simpa [hiso] using norm_sub_le x y⟩
  · intro c f hf
    rcases (hmem s f).mp hf with ⟨x, rfl⟩
    have heq : KdVPlan.scale c (KdVPlan.FromLP s x) = KdVPlan.FromLP s (c • x) := by
      ext k
      simp [KdVPlan.FromLP, KdVPlan.scale, mul_left_comm]
    rw [heq]
    exact ⟨(hmem _ _).mpr ⟨c • x, rfl⟩, by simpa [hiso] using norm_smul c x⟩

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f : KdVPlan.Coeff, KdVPlan.MemH 0 f →\n (KdVPlan.hn 0 f)^2 = ∑' k, ‖f k‖^2 ∧ ∀ k, ‖f k‖ ≤ KdVPlan.hn 0 f" := by
  intro f hf
  have hs : Summable (fun k => ‖f k‖^2) := by simpa [KdVPlan.MemH, KdVPlan.weight] using hf
  have he : KdVPlan.hn 0 f = Real.sqrt (∑' k, ‖f k‖^2) := by simp [KdVPlan.hn, KdVPlan.weight]
  constructor
  · rw [he, Real.sq_sqrt (tsum_nonneg (fun k => sq_nonneg _))]
  · intro k
    rw [he, ← Real.sqrt_sq (norm_nonneg (f k))]
    exact Real.sqrt_le_sqrt (hs.le_tsum k (fun j hj => sq_nonneg _))

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff), 0 ≤ s → KdVPlan.MemH s f →\n let x : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^s * ‖f k‖\n KdVPlan.NonnegL2 x ∧ KdVPlan.seqN x ≤ KdVPlan.hn s f" := by
  intro s f hs hf
  dsimp only
  let x : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^s * ‖f k‖
  have hpos : ∀ k, 0 ≤ x k := by intro k; dsimp [x]; split_ifs <;> positivity
  have hle : ∀ k, x k ^ 2 ≤ KdVPlan.weight s k * ‖f k‖^2 := by
    intro k
    by_cases hk : k = 0
    · simp [x, hk, KdVPlan.weight]
    · simp only [x, if_neg hk, mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hpow : (|(k : ℝ)|^s)^2 = ((k : ℝ)^2)^s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), mul_comm s, Real.rpow_mul (abs_nonneg _), Real.rpow_natCast, sq_abs]
      rw [hpow]
      exact Real.rpow_le_rpow (sq_nonneg _) (by linarith) hs
  have hx : Summable (fun k => x k ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hle hf
  exact ⟨⟨by simp [x], hpos, hx⟩, Real.sqrt_le_sqrt (hx.tsum_le_tsum hle hf)⟩

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ U : ℤ × ℤ × ℤ → ℝ, (∀ z, 0 ≤ U z) → Summable U →\n (∀ k : ℤ, Summable (fun p : ℤ × ℤ => U (p.1, p.2, k-p.1-p.2))) ∧\n Summable (fun k : ℤ => ∑' p : ℤ × ℤ, U (p.1,p.2,k-p.1-p.2)) ∧\n (∑' k : ℤ, ∑' p : ℤ × ℤ, U (p.1,p.2,k-p.1-p.2)) = ∑' z, U z" := by
  intro U hU hs
  let E : (ℤ × (ℤ × ℤ)) ≃ (ℤ × ℤ × ℤ) :=
   { toFun := fun p => (p.2.1,p.2.2,p.1-p.2.1-p.2.2)
     invFun := fun z => (z.1+z.2.1+z.2.2,z.1,z.2.1)
     left_inv := by intro p; rcases p with ⟨k,a,b⟩; dsimp; simp only [Prod.mk.injEq, and_true, true_and]; omega
     right_inv := by intro z; rcases z with ⟨a,b,c⟩; dsimp; simp only [Prod.mk.injEq, and_true, true_and]; omega }
  have hs' : Summable (fun p => U (E p)) := E.summable_iff.mpr hs
  have hh := (summable_prod_of_nonneg (fun p => hU (E p))).mp hs'
  refine ⟨hh.1, hh.2, ?_⟩
  exact (hs'.tsum_prod' hh.1).symm.trans (E.tsum_eq U)

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (y : ℤ → ℂ) (F : Finset ℤ), y 0 = 0 →\n let w : ℤ → ℝ := fun k => if k ∈ F then ‖y k‖ else 0\n KdVPlan.NonnegL2 w ∧ KdVPlan.seqN w = Real.sqrt (∑ k ∈ F, ‖y k‖^2)" := by
  classical
  intro y F hy
  dsimp only
  constructor
  · refine ⟨by simp [hy], fun k => by dsimp; positivity, ?_⟩
    exact summable_of_ne_finset_zero (s := F) (by intro j hj; simp [hj])
  · unfold KdVPlan.seqN
    congr 1
    rw [tsum_eq_sum (s := F) (fun k hk => by simp [hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [hk]

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (U : ℤ × ℤ × ℤ → ℂ) (y : KdVPlan.Coeff) (K : ℝ),\n 0 ≤ K → y 0 = 0 →\n (∀ k : ℤ, k ≠ 0 → y k = ∑' p : ℤ × ℤ, U (p.1,p.2,k-p.1-p.2)) →\n (∀ w : ℤ → ℝ, KdVPlan.NonnegL2 w →\n   Summable (fun z : ℤ × ℤ × ℤ => ‖U z‖ * w (z.1+z.2.1+z.2.2)) ∧\n   (∑' z : ℤ × ℤ × ℤ, ‖U z‖ * w (z.1+z.2.1+z.2.2)) ≤ K*KdVPlan.seqN w) →\n KdVPlan.HB 0 y K ∧ ∀ k : ℤ, k ≠ 0 → Summable (fun p : ℤ × ℤ => U (p.1,p.2,k-p.1-p.2))" := by
  classical
  intro U y K hK hy0 hy hh
  have hfiber : ∀ k : ℤ, k ≠ 0 → Summable (fun p : ℤ × ℤ => ‖U (p.1,p.2,k-p.1-p.2)‖) := by
    intro k hk
    let w : ℤ → ℝ := fun j => if j = k then 1 else 0
    have hw : KdVPlan.NonnegL2 w := by
      refine ⟨by simp [w, Ne.symm hk], fun j => by simp [w]; positivity, ?_⟩
      exact summable_of_ne_finset_zero (s := {k}) (by intro j hj; simp_all [w])
    have ht := (@yui_aux_0005 T gamma R h_T002 h_T003 h_T017 h_T013 _ (fun z => mul_nonneg (norm_nonneg _) (hw.2.1 _)) (hh w hw).1).1 k
    simpa [w] using ht
  have hsum : ∀ F : Finset ℤ, (∑ k ∈ F, ‖y k‖^2) ≤ K^2 := by
    intro F
    let w : ℤ → ℝ := fun k => if k ∈ F then ‖y k‖ else 0
    have hw : KdVPlan.NonnegL2 w := (@yui_aux_0006 T gamma R h_T002 h_T003 h_T017 h_T013 y F hy0).1
    have hnorm : KdVPlan.seqN w = Real.sqrt (∑ k ∈ F, ‖y k‖^2) := (@yui_aux_0006 T gamma R h_T002 h_T003 h_T017 h_T013 y F hy0).2
    have ht := @yui_aux_0005 T gamma R h_T002 h_T003 h_T017 h_T013 _ (fun z => mul_nonneg (norm_nonneg _) (hw.2.1 _)) (hh w hw).1
    have hle : (∑ k ∈ F, ‖y k‖^2) ≤ ∑' z : ℤ × ℤ × ℤ, ‖U z‖*w (z.1+z.2.1+z.2.2) := by
      rw [← ht.2.2]
      calc
        (∑ k ∈ F, ‖y k‖^2) ≤ ∑ k ∈ F, ∑' p : ℤ × ℤ, ‖U (p.1,p.2,k-p.1-p.2)‖ * w k := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hk0 : k = 0
          · subst k
            simp [hy0, w]
          · rw [hy k hk0, tsum_mul_right]
            have hn := norm_tsum_le_tsum_norm (hfiber k hk0)
            dsimp [w]
            rw [if_pos hk, pow_two]
            rw [← hy k hk0]
            exact mul_le_mul_of_nonneg_right (by simpa [hy k hk0] using hn) (norm_nonneg (y k))
        _ = ∑ k ∈ F, ∑' p : ℤ × ℤ, ‖U (p.1,p.2,k-p.1-p.2)‖ * w (p.1+p.2+(k-p.1-p.2)) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          ext p
          congr 2
          omega
        _ ≤ ∑' k : ℤ, ∑' p : ℤ × ℤ, ‖U (p.1,p.2,k-p.1-p.2)‖ * w (p.1+p.2+(k-p.1-p.2)) :=
          Summable.sum_le_tsum F (fun k hk => tsum_nonneg (fun p => mul_nonneg (norm_nonneg _) (hw.2.1 _))) ht.2.1
    have hbound := hle.trans (hh w hw).2
    rw [hnorm] at hbound
    have hspos : 0 ≤ ∑ k ∈ F, ‖y k‖^2 := Finset.sum_nonneg (fun k hk => sq_nonneg _)
    have hsqrt := Real.sq_sqrt hspos
    have hnon := Real.sqrt_nonneg (∑ k ∈ F, ‖y k‖^2)
    nlinarith [sq_nonneg (Real.sqrt (∑ k ∈ F, ‖y k‖^2)-K)]
  have hs : Summable (fun k => ‖y k‖^2) := summable_of_sum_le (fun k => sq_nonneg _) hsum
  refine ⟨⟨by simpa [KdVPlan.MemH, KdVPlan.weight] using hs, ?_⟩, fun k hk => (hfiber k hk).of_norm⟩
  have ht : (∑' k, ‖y k‖^2) ≤ K^2 := hs.tsum_le_of_sum_le hsum
  simpa [KdVPlan.hn, KdVPlan.weight, Real.sqrt_sq hK] using Real.sqrt_le_sqrt ht

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (x₁ x₂ x₃ : ℤ → ℝ) (U : ℤ × ℤ × ℤ → ℂ) (y : KdVPlan.Coeff) (D : ℝ),\n KdVPlan.NonnegL2 x₁ → KdVPlan.NonnegL2 x₂ → KdVPlan.NonnegL2 x₃ →\n 0 ≤ D → y 0 = 0 →\n (∀ k : ℤ, k ≠ 0 → y k = ∑' p : ℤ × ℤ, U (p.1,p.2,k-p.1-p.2)) →\n (∀ z : ℤ × ℤ × ℤ, ‖U z‖ ≤\n   D * (@ite ℝ (KdVPlan.Interaction z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)) (Classical.propDecidable _) (x₁ z.1*x₂ z.2.1*x₃ z.2.2 / KdVPlan.n3 z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)) 0)) →\n ∃ C : ℝ, 0 < C ∧\n   KdVPlan.HB 0 y (D*C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃) ∧\n   ∀ k : ℤ, k ≠ 0 → Summable (fun p : ℤ × ℤ => U (p.1,p.2,k-p.1-p.2))" := by
  classical
  intro x₁ x₂ x₃ U y D hx₁ hx₂ hx₃ hD hy0 hy hU
  rcases h_T003.2 with ⟨C,hC,hfour⟩
  refine ⟨C,hC,?_⟩
  apply @yui_aux_0007 T gamma R h_T002 h_T003 h_T017 h_T013 U y (D*C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃)
  · dsimp [KdVPlan.seqN]; positivity
  · exact hy0
  · exact hy
  · intro w hw
    let x₄ : ℤ → ℝ := fun d => w (-d)
    have hx₄ : KdVPlan.NonnegL2 x₄ := by
      refine ⟨by simpa [x₄] using hw.1, fun d => hw.2.1 _, ?_⟩
      exact (Equiv.neg ℤ).summable_iff.mpr hw.2.2
    have hn₄ : KdVPlan.seqN x₄ = KdVPlan.seqN w := by
      unfold KdVPlan.seqN
      congr 1
      exact (Equiv.neg ℤ).tsum_eq (fun k => w k ^ 2)
    obtain ⟨hq,hbound,hsup⟩ := hfour x₁ x₂ x₃ x₄ hx₁ hx₂ hx₃ hx₄ Set.univ
    have hle : ∀ z : ℤ × ℤ × ℤ, ‖U z‖*w (z.1+z.2.1+z.2.2) ≤
        D * KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z := by
      intro z
      have h := mul_le_mul_of_nonneg_right (hU z) (hw.2.1 (z.1+z.2.1+z.2.2))
      have he : D * KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z =
          (D * (if KdVPlan.Interaction z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)
            then x₁ z.1*x₂ z.2.1*x₃ z.2.2 / KdVPlan.n3 z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2) else 0)) *
            w (z.1+z.2.1+z.2.2) := by
        simp only [KdVPlan.quadTerm, x₄, Set.mem_univ, true_and]
        have ha : -(-z.1-z.2.1-z.2.2) = z.1+z.2.1+z.2.2 := by omega
        rw [ha]
        split_ifs <;> ring
      exact h.trans_eq he.symm
    have hsmall := Summable.of_nonneg_of_le
      (fun z => mul_nonneg (norm_nonneg _) (hw.2.1 _)) hle (hq.mul_left D)
    refine ⟨hsmall,?_⟩
    calc
      (∑' z : ℤ × ℤ × ℤ, ‖U z‖ * w (z.1+z.2.1+z.2.2)) ≤
         ∑' z, D * KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z :=
           hsmall.tsum_le_tsum hle (hq.mul_left D)
      _ = D * ∑' z, KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z := tsum_mul_left
      _ ≤ D * (C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃*KdVPlan.seqN x₄) :=
        mul_le_mul_of_nonneg_left hbound hD
      _ = (D*C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃)*KdVPlan.seqN w := by rw [hn₄]; ring

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∃ C : ℝ, 0 < C ∧ ∀ (x₁ x₂ x₃ : ℤ → ℝ) (U : ℤ × ℤ × ℤ → ℂ) (y : KdVPlan.Coeff) (D : ℝ),\n KdVPlan.NonnegL2 x₁ → KdVPlan.NonnegL2 x₂ → KdVPlan.NonnegL2 x₃ →\n 0 ≤ D → y 0 = 0 →\n (∀ k : ℤ, k ≠ 0 → y k = ∑' p : ℤ × ℤ, U (p.1,p.2,k-p.1-p.2)) →\n (∀ z : ℤ × ℤ × ℤ, ‖U z‖ ≤\n   D * (@ite ℝ (KdVPlan.Interaction z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)) (Classical.propDecidable _) (x₁ z.1*x₂ z.2.1*x₃ z.2.2 / KdVPlan.n3 z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)) 0)) →\n   KdVPlan.HB 0 y (D*C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃) ∧\n   ∀ k : ℤ, k ≠ 0 → Summable (fun p : ℤ × ℤ => U (p.1,p.2,k-p.1-p.2))" := by
  classical
  rcases h_T003.2 with ⟨C,hC,hfour⟩
  refine ⟨C,hC,?_⟩
  intro x₁ x₂ x₃ U y D hx₁ hx₂ hx₃ hD hy0 hy hU
  apply @yui_aux_0007 T gamma R h_T002 h_T003 h_T017 h_T013 U y (D*C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃)
  · dsimp [KdVPlan.seqN]; positivity
  · exact hy0
  · exact hy
  · intro w hw
    let x₄ : ℤ → ℝ := fun d => w (-d)
    have hx₄ : KdVPlan.NonnegL2 x₄ := by
      refine ⟨by simpa [x₄] using hw.1, fun d => hw.2.1 _, ?_⟩
      exact (Equiv.neg ℤ).summable_iff.mpr hw.2.2
    have hn₄ : KdVPlan.seqN x₄ = KdVPlan.seqN w := by
      unfold KdVPlan.seqN
      congr 1
      exact (Equiv.neg ℤ).tsum_eq (fun k => w k ^ 2)
    obtain ⟨hq,hbound,hsup⟩ := hfour x₁ x₂ x₃ x₄ hx₁ hx₂ hx₃ hx₄ Set.univ
    have hle : ∀ z : ℤ × ℤ × ℤ, ‖U z‖*w (z.1+z.2.1+z.2.2) ≤
        D * KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z := by
      intro z
      have h := mul_le_mul_of_nonneg_right (hU z) (hw.2.1 (z.1+z.2.1+z.2.2))
      have he : D * KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z =
          (D * (if KdVPlan.Interaction z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)
            then x₁ z.1*x₂ z.2.1*x₃ z.2.2 / KdVPlan.n3 z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2) else 0)) *
            w (z.1+z.2.1+z.2.2) := by
        simp only [KdVPlan.quadTerm, x₄, Set.mem_univ, true_and]
        have ha : -(-z.1-z.2.1-z.2.2) = z.1+z.2.1+z.2.2 := by omega
        rw [ha]
        split_ifs <;> ring
      exact h.trans_eq he.symm
    have hsmall := Summable.of_nonneg_of_le
      (fun z => mul_nonneg (norm_nonneg _) (hw.2.1 _)) hle (hq.mul_left D)
    refine ⟨hsmall,?_⟩
    calc
      (∑' z : ℤ × ℤ × ℤ, ‖U z‖ * w (z.1+z.2.1+z.2.2)) ≤
         ∑' z, D * KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z :=
           hsmall.tsum_le_tsum hle (hq.mul_left D)
      _ = D * ∑' z, KdVPlan.quadTerm Set.univ x₁ x₂ x₃ x₄ z := tsum_mul_left
      _ ≤ D * (C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃*KdVPlan.seqN x₄) :=
        mul_le_mul_of_nonneg_left hbound hD
      _ = (D*C*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃)*KdVPlan.seqN w := by rw [hn₄]; ring

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (σ τ t : ℝ) (χ : ℤ → ℤ → ℤ → ℂ),\n 0 ≤ σ → σ ≤ 1 → 0 < τ → (∀ a b c, ‖χ a b c‖ ≤ 1) →\n ∀ a b c : ℤ, KdVPlan.Interaction a b c (-(a+b+c)) → a+b ≠ 0 →\n let k := a+b+c\n let α : ℝ := 3*(a : ℝ)*(b : ℝ)*(a+b : ℤ)\n let β : ℝ := 3*(k : ℝ)*(c : ℝ)*(a+b : ℤ)\n ‖-(τ : ℂ)/(18*Complex.I*(k : ℂ)) * χ a b c * KdVPlan.phase (α+β) t * KdVPlan.eta τ α β‖ ≤\n (τ/18) * (6^(1-σ)*18^σ*τ^σ/KdVPlan.n3 a b c (-k)) *\n   (|(a : ℝ)|^σ*|(b : ℝ)|^σ*|(c : ℝ)|^σ)" := by
  intro σ τ t χ hσ hσ1 hτ hχ a b c hi hab
  dsimp only
  let k : ℤ := a+b+c
  let α : ℝ := 3*(a : ℝ)*(b : ℝ)*(a+b : ℤ)
  let β : ℝ := 3*(k : ℝ)*(c : ℝ)*(a+b : ℤ)
  have hk : k ≠ 0 := by intro hk; exact hi.2.2.2.2 (by simpa [k, hk])
  have hkr : |(k : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hk)
  have har : 0 < |(a : ℝ)| := abs_pos.mpr (by exact_mod_cast hi.2.1)
  have hbr : 0 < |(b : ℝ)| := abs_pos.mpr (by exact_mod_cast hi.2.2.1)
  have hcr : 0 < |(c : ℝ)| := abs_pos.mpr (by exact_mod_cast hi.2.2.2.1)
  have hQ : 0 < |(a : ℝ)|^σ*|(b : ℝ)|^σ*|(c : ℝ)|^σ := by positivity
  have hpow : |(a : ℝ)*(b : ℝ)*(c : ℝ)|^σ =
      |(a : ℝ)|^σ*|(b : ℝ)|^σ*|(c : ℝ)|^σ := by
    rw [abs_mul, abs_mul, Real.mul_rpow (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _),
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hm := h_T017 σ τ hσ hσ1 hτ a b c hi hab
  rw [hpow] at hm
  have hp : ‖KdVPlan.phase (α+β) t‖ = 1 := by
    simp [KdVPlan.phase, Complex.norm_exp]
  have heq : ‖-(τ : ℂ)/(18*Complex.I*(k : ℂ)) * χ a b c *
      KdVPlan.phase (α+β) t * KdVPlan.eta τ α β‖ =
     τ/(18*|(k : ℝ)|)*‖χ a b c‖*‖KdVPlan.eta τ α β‖ := by
    simp [norm_mul, norm_div, hp, abs_of_pos hτ, Complex.norm_intCast, mul_assoc]
  calc
    _ = τ/(18*|(k : ℝ)|)*‖χ a b c‖*‖KdVPlan.eta τ α β‖ := heq
    _ ≤ τ/(18*|(k : ℝ)|)*1*‖KdVPlan.eta τ α β‖ := by
      gcongr
      exact hχ a b c
    _ = (τ/18*(|(a : ℝ)|^σ*|(b : ℝ)|^σ*|(c : ℝ)|^σ)) *
      (‖KdVPlan.eta τ α β‖ / (|(k : ℝ)| * (|(a : ℝ)|^σ*|(b : ℝ)|^σ*|(c : ℝ)|^σ))) := by
      field_simp [hkr, ne_of_gt hQ]
    _ ≤ (τ/18*(|(a : ℝ)|^σ*|(b : ℝ)|^σ*|(c : ℝ)|^σ)) *
      (6^(1-σ)*18^σ*τ^σ/KdVPlan.n3 a b c (-k)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (χ : ℤ → ℤ → ℤ → ℂ) (t τ : ℝ),\n let K : ℤ → ℤ → ℤ → ℂ := fun a b c : ℤ =>\n if a+b+c = 0 ∨ a+b = 0 then 0 else\n -(τ : ℂ)/(18*Complex.I*((a+b+c : ℤ) : ℂ)) * χ a b c *\n KdVPlan.phase (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ) +\n   3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ)) t *\n KdVPlan.eta τ (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ))\n   (3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ))\n ∀ (f g h : KdVPlan.Coeff) (k : ℤ),\n KdVPlan.remWith χ t τ f g h k =\n   ∑' p : ℤ × ℤ, K p.1 p.2 (k-p.1-p.2)*f p.1*g p.2*h (k-p.1-p.2)" := by
  intro χ t τ
  let K : ℤ → ℤ → ℤ → ℂ := fun a b c : ℤ =>
   if a+b+c = 0 ∨ a+b = 0 then 0 else
   -(τ : ℂ)/(18*Complex.I*((a+b+c : ℤ) : ℂ)) * χ a b c *
   KdVPlan.phase (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ) +
     3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ)) t *
   KdVPlan.eta τ (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ))
     (3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ))
  change ∀ (f g h : KdVPlan.Coeff) (k : ℤ), KdVPlan.remWith χ t τ f g h k = ∑' p : ℤ × ℤ, K p.1 p.2 (k-p.1-p.2)*f p.1*g p.2*h (k-p.1-p.2)
  intro f g h k
  unfold KdVPlan.remWith
  by_cases hk : k = 0
  · subst k
    simp only [if_pos rfl]
    symm
    calc
      _ = ∑' _p : ℤ × ℤ, (0 : ℂ) := by
        apply tsum_congr
        intro p
        have he : p.1+p.2+(0-p.1-p.2) = (0 : ℤ) := by omega
        simp [K, he]
      _ = 0 := tsum_zero
  · rw [if_neg hk, ← tsum_mul_left]
    apply tsum_congr
    intro p
    have he : p.1+p.2+(k-p.1-p.2) = k := by omega
    by_cases hp : p.1+p.2 = 0
    · simp [K, he, hp]
    · simp only [K, he, hp, hk, false_or, or_self, if_false]
      ring

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (σ τ t : ℝ) (χ : ℤ → ℤ → ℤ → ℂ) (f g h : KdVPlan.Coeff),\n 0 ≤ σ → σ ≤ 1 → 0 < τ → (∀ a b c, ‖χ a b c‖ ≤ 1) →\n KdVPlan.ZeroMean f → KdVPlan.ZeroMean g → KdVPlan.ZeroMean h →\n let K : ℤ → ℤ → ℤ → ℂ := fun a b c : ℤ =>\n if a+b+c = 0 ∨ a+b = 0 then 0 else\n -(τ : ℂ)/(18*Complex.I*((a+b+c : ℤ) : ℂ)) * χ a b c *\n KdVPlan.phase (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ) +\n   3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ)) t *\n KdVPlan.eta τ (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ))\n   (3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ))\n let x₁ : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^σ*‖f k‖\n let x₂ : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^σ*‖g k‖\n let x₃ : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^σ*‖h k‖\n ∀ z : ℤ × ℤ × ℤ, ‖K z.1 z.2.1 z.2.2 * f z.1 * g z.2.1 * h z.2.2‖ ≤\n (τ/18*(6^(1-σ)*18^σ*τ^σ)) *\n (@ite ℝ (KdVPlan.Interaction z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)) (Classical.propDecidable _)\n (x₁ z.1*x₂ z.2.1*x₃ z.2.2 / KdVPlan.n3 z.1 z.2.1 z.2.2 (-z.1-z.2.1-z.2.2)) 0)" := by
  classical
  intro σ τ t χ f g h hσ hσ1 hτ hχ hf hg hh
  dsimp only
  intro z
  rcases z with ⟨a,b,c⟩
  dsimp only
  have hn : 0 ≤ KdVPlan.n3 a b c (-a-b-c) := by unfold KdVPlan.n3; positivity
  have hr : -(a+b+c) = -a-b-c := by omega
  by_cases hi : KdVPlan.Interaction a b c (-a-b-c)
  · have ha := hi.2.1
    have hb := hi.2.2.1
    have hc := hi.2.2.2.1
    have hk : a+b+c ≠ 0 := by intro hk; apply hi.2.2.2.2; omega
    rw [if_pos hi, if_neg ha, if_neg hb, if_neg hc]
    by_cases hab : a+b = 0
    · simp only [hab, or_true, if_true, zero_mul, norm_zero]
      positivity
    · simp only [hk, hab, or_self, if_false]
      rw [norm_mul, norm_mul, norm_mul]
      have hm := @yui_aux_0010 T gamma R h_T002 h_T003 h_T017 h_T013 σ τ t χ hσ hσ1 hτ hχ a b c (by simpa [hr] using hi) hab
      dsimp only at hm
      rw [hr] at hm
      calc
        _ ≤ ((τ/18)*(6^(1-σ)*18^σ*τ^σ/KdVPlan.n3 a b c (-a-b-c)) *
            (|(a : ℝ)|^σ*|(b : ℝ)|^σ*|(c : ℝ)|^σ)) * ‖f a‖*‖g b‖*‖h c‖ := by
          gcongr
        _ = _ := by ring
  · rw [if_neg hi, mul_zero]
    have hz : a = 0 ∨ b = 0 ∨ c = 0 ∨ a+b+c = 0 := by
      by_contra hz
      push_neg at hz
      exact hi ⟨by omega, hz.1, hz.2.1, hz.2.2.1, by omega⟩
    rcases hz with ha|hb|hc|hk
    · simp [ha, show f 0 = 0 from hf]
    · simp [hb, show g 0 = 0 from hg]
    · simp [hc, show h 0 = 0 from hh]
    · simp [hk]

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∃ C : ℝ, 0 < C ∧\n ∀ χ : ℤ → ℤ → ℤ → ℂ, (∀ a b c, ‖χ a b c‖ ≤ 1) →\n ∀ t τ : ℝ, 0 < τ → ∀ f g h : KdVPlan.Coeff,\n KdVPlan.MemH σ f → KdVPlan.MemH σ g → KdVPlan.MemH σ h →\n KdVPlan.ZeroMean f → KdVPlan.ZeroMean g → KdVPlan.ZeroMean h →\n KdVPlan.HB 0 (KdVPlan.remWith χ t τ f g h) (C*τ^(1+σ)*KdVPlan.hn σ f*KdVPlan.hn σ g*KdVPlan.hn σ h) ∧\n let K : ℤ → ℤ → ℤ → ℂ := fun a b c : ℤ =>\n if a+b+c = 0 ∨ a+b = 0 then 0 else\n -(τ : ℂ)/(18*Complex.I*((a+b+c : ℤ) : ℂ)) * χ a b c *\n KdVPlan.phase (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ) +\n   3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ)) t *\n KdVPlan.eta τ (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ))\n   (3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ))\n ∀ k : ℤ, Summable (fun p : ℤ × ℤ => K p.1 p.2 (k-p.1-p.2)*f p.1*g p.2*h (k-p.1-p.2))" := by
  intro σ hσ hσ1
  obtain ⟨C₀,hC₀,hkern⟩ := @yui_aux_0009 T gamma R h_T002 h_T003 h_T017 h_T013
  let C := (6^(1-σ)*18^σ)/18*C₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro χ hχ t τ hτ f g h hf hg hh hf0 hg0 hh0
  let K : ℤ → ℤ → ℤ → ℂ := fun a b c : ℤ =>
   if a+b+c = 0 ∨ a+b = 0 then 0 else
   -(τ : ℂ)/(18*Complex.I*((a+b+c : ℤ) : ℂ)) * χ a b c *
   KdVPlan.phase (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ) +
     3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ)) t *
   KdVPlan.eta τ (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ))
     (3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ))
  let x₁ : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^σ*‖f k‖
  let x₂ : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^σ*‖g k‖
  let x₃ : ℤ → ℝ := fun k => if k = 0 then 0 else |(k : ℝ)|^σ*‖h k‖
  have hx₁ := @yui_aux_0004 T gamma R h_T002 h_T003 h_T017 h_T013 σ f hσ hf
  have hx₂ := @yui_aux_0004 T gamma R h_T002 h_T003 h_T017 h_T013 σ g hσ hg
  have hx₃ := @yui_aux_0004 T gamma R h_T002 h_T003 h_T017 h_T013 σ h hσ hh
  let D : ℝ := τ/18*(6^(1-σ)*18^σ*τ^σ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrepr : ∀ k, KdVPlan.remWith χ t τ f g h k =
   ∑' p : ℤ × ℤ, K p.1 p.2 (k-p.1-p.2)*f p.1*g p.2*h (k-p.1-p.2) :=
   @yui_aux_0011 T gamma R h_T002 h_T003 h_T017 h_T013 χ t τ f g h
  have hdom := @yui_aux_0012 T gamma R h_T002 h_T003 h_T017 h_T013 σ τ t χ f g h hσ hσ1 hτ hχ hf0 hg0 hh0
  have hb := hkern x₁ x₂ x₃ (fun z => K z.1 z.2.1 z.2.2*f z.1*g z.2.1*h z.2.2)
   (KdVPlan.remWith χ t τ f g h) D hx₁.1 hx₂.1 hx₃.1 hD (by simp [KdVPlan.remWith])
   (fun k hk => hrepr k) hdom
  refine ⟨⟨hb.1.1,hb.1.2.trans ?_⟩,?_⟩
  · calc
      D*C₀*KdVPlan.seqN x₁*KdVPlan.seqN x₂*KdVPlan.seqN x₃ ≤
         D*C₀*KdVPlan.hn σ f*KdVPlan.hn σ g*KdVPlan.hn σ h := by
        have hx₁n : 0 ≤ KdVPlan.seqN x₁ := Real.sqrt_nonneg _
        have hx₂n : 0 ≤ KdVPlan.seqN x₂ := Real.sqrt_nonneg _
        have hx₃n : 0 ≤ KdVPlan.seqN x₃ := Real.sqrt_nonneg _
        have hnf := @yui_aux_0001 T gamma R h_T002 h_T003 h_T017 h_T013 σ f
        have hng := @yui_aux_0001 T gamma R h_T002 h_T003 h_T017 h_T013 σ g
        have hnh := @yui_aux_0001 T gamma R h_T002 h_T003 h_T017 h_T013 σ h
        gcongr <;> first | exact hx₁.2 | exact hx₂.2 | exact hx₃.2 | positivity
      _ = C*τ^(1+σ)*KdVPlan.hn σ f*KdVPlan.hn σ g*KdVPlan.hn σ h := by
        rw [Real.rpow_add hτ, Real.rpow_one]
        dsimp [D,C]
        ring
  · change ∀ k : ℤ, Summable (fun p : ℤ × ℤ => K p.1 p.2 (k-p.1-p.2)*f p.1*g p.2*h (k-p.1-p.2))
    intro k
    by_cases hk : k = 0
    · subst k
      have hz : (fun p : ℤ × ℤ => K p.1 p.2 (0-p.1-p.2)*f p.1*g p.2*h (0-p.1-p.2)) =
         (fun _ => (0 : ℂ)) := by
        ext p
        have he : p.1+p.2+(0-p.1-p.2) = (0 : ℤ) := by omega
        simp [K,he]
      rw [hz]
      exact summable_zero
    · exact hb.2 k hk

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (σ : ℝ), 0 ≤ σ → σ ≤ 1 →\n ∀ χ : ℤ → ℤ → ℤ → ℂ, (∀ a b c, ‖χ a b c‖ ≤ 1) →\n ∀ t τ : ℝ, 0 < τ → KdVPlan.TriLinearOn σ (KdVPlan.remWith χ t τ)" := by
  intro σ hσ hσ1 χ hχ t τ hτ
  obtain ⟨C,hC,hbound⟩ := @yui_aux_0013 T gamma R h_T002 h_T003 h_T017 h_T013 σ hσ hσ1
  let K : ℤ → ℤ → ℤ → ℂ := fun a b c : ℤ =>
   if a+b+c = 0 ∨ a+b = 0 then 0 else
   -(τ : ℂ)/(18*Complex.I*((a+b+c : ℤ) : ℂ)) * χ a b c *
   KdVPlan.phase (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ) +
     3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ)) t *
   KdVPlan.eta τ (3*(a : ℝ)*(b : ℝ)*(a+b : ℤ))
     (3*((a+b+c : ℤ) : ℝ)*(c : ℝ)*(a+b : ℤ))
  have hrepr : ∀ (f g h : KdVPlan.Coeff) k,
   KdVPlan.remWith χ t τ f g h k = ∑' p : ℤ × ℤ, K p.1 p.2 (k-p.1-p.2)*f p.1*g p.2*h (k-p.1-p.2) :=
   @yui_aux_0011 T gamma R h_T002 h_T003 h_T017 h_T013 χ t τ
  have hsum : ∀ (f g h : KdVPlan.Coeff), KdVPlan.MemH σ f → KdVPlan.MemH σ g → KdVPlan.MemH σ h →
   KdVPlan.ZeroMean f → KdVPlan.ZeroMean g → KdVPlan.ZeroMean h → ∀ k : ℤ,
   Summable (fun p : ℤ × ℤ => K p.1 p.2 (k-p.1-p.2)*f p.1*g p.2*h (k-p.1-p.2)) := by
    intro f g h hf hg hh hf0 hg0 hh0
    exact (hbound χ hχ t τ hτ f g h hf hg hh hf0 hg0 hh0).2
  intro f f' g g' h h' hf hf' hg hg' hh hh' hf0 hf'0 hg0 hg'0 hh0 hh'0
  refine ⟨?_,?_,?_,?_⟩
  · ext k
    change KdVPlan.remWith χ t τ (f+f') g h k =
      KdVPlan.remWith χ t τ f g h k + KdVPlan.remWith χ t τ f' g h k
    rw [hrepr, hrepr, hrepr, ← (hsum f g h hf hg hh hf0 hg0 hh0 k).tsum_add (hsum f' g h hf' hg hh hf'0 hg0 hh0 k)]
    apply tsum_congr
    intro p
    simp only [Pi.add_apply]
    ring
  · ext k
    change KdVPlan.remWith χ t τ f (g+g') h k =
      KdVPlan.remWith χ t τ f g h k + KdVPlan.remWith χ t τ f g' h k
    rw [hrepr, hrepr, hrepr, ← (hsum f g h hf hg hh hf0 hg0 hh0 k).tsum_add (hsum f g' h hf hg' hh hf0 hg'0 hh0 k)]
    apply tsum_congr
    intro p
    simp only [Pi.add_apply]
    ring
  · ext k
    change KdVPlan.remWith χ t τ f g (h+h') k =
      KdVPlan.remWith χ t τ f g h k + KdVPlan.remWith χ t τ f g h' k
    rw [hrepr, hrepr, hrepr, ← (hsum f g h hf hg hh hf0 hg0 hh0 k).tsum_add (hsum f g h' hf hg hh' hf0 hg0 hh'0 k)]
    apply tsum_congr
    intro p
    simp only [Pi.add_apply]
    ring
  · intro z
    refine ⟨?_,?_,?_⟩
    · ext k
      change KdVPlan.remWith χ t τ (KdVPlan.scale z f) g h k = z*KdVPlan.remWith χ t τ f g h k
      rw [hrepr, hrepr, ← tsum_mul_left]
      apply tsum_congr
      intro p
      simp only [KdVPlan.scale]
      ring
    · ext k
      change KdVPlan.remWith χ t τ f (KdVPlan.scale z g) h k = z*KdVPlan.remWith χ t τ f g h k
      rw [hrepr, hrepr, ← tsum_mul_left]
      apply tsum_congr
      intro p
      simp only [KdVPlan.scale]
      ring
    · ext k
      change KdVPlan.remWith χ t τ f g (KdVPlan.scale z h) k = z*KdVPlan.remWith χ t τ f g h k
      rw [hrepr, hrepr, ← tsum_mul_left]
      apply tsum_congr
      intro p
      simp only [KdVPlan.scale]
      ring

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (n : ℕ) (f : KdVPlan.Coeff), KdVPlan.Poly (KdVPlan.cutoff (n : ℝ) f) ∧\n (KdVPlan.ZeroMean f → KdVPlan.ZeroMean (KdVPlan.cutoff (n : ℝ) f))) ∧\n ∀ (s : ℝ) (N : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s f →\n KdVPlan.MemH s (KdVPlan.cutoff N f) ∧ KdVPlan.hn s (KdVPlan.cutoff N f) ≤ KdVPlan.hn s f" := by
  constructor
  · intro n f
    constructor
    · apply (Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset
      intro k hk
      have hkn : |(k : ℝ)| ≤ (n : ℝ) := by
        by_contra hn
        have hk0 : KdVPlan.cutoff (n : ℝ) f k ≠ 0 := hk
        exact hk0 (by simp [KdVPlan.cutoff, hn])
      have ha := abs_le.mp hkn
      constructor
      · exact_mod_cast ha.1
      · exact_mod_cast ha.2
    · intro hf
      change (if |((0 : ℤ) : ℝ)| ≤ (n : ℝ) then f 0 else 0) = 0
      simp [show f 0 = 0 from hf]
  · intro s N f hf
    have hle : ∀ k, KdVPlan.weight s k * ‖KdVPlan.cutoff N f k‖^2 ≤ KdVPlan.weight s k * ‖f k‖^2 := by
      intro k
      unfold KdVPlan.cutoff
      split_ifs
      · rfl
      · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
        unfold KdVPlan.weight
        positivity
    have hn : ∀ k, 0 ≤ KdVPlan.weight s k * ‖KdVPlan.cutoff N f k‖^2 := by
      intro k
      unfold KdVPlan.weight
      positivity
    have hc := Summable.of_nonneg_of_le hn hle hf
    exact ⟨hc,Real.sqrt_le_sqrt (hc.tsum_le_tsum hle hf)⟩

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (A : KdVPlan.Coeff → KdVPlan.Coeff → KdVPlan.Coeff → KdVPlan.Coeff),\n KdVPlan.TriLinearOn s A →\n ∀ f f' g g' h h' : KdVPlan.Coeff,\n KdVPlan.MemH s f → KdVPlan.MemH s f' → KdVPlan.MemH s g → KdVPlan.MemH s g' → KdVPlan.MemH s h → KdVPlan.MemH s h' →\n KdVPlan.ZeroMean f → KdVPlan.ZeroMean f' → KdVPlan.ZeroMean g → KdVPlan.ZeroMean g' → KdVPlan.ZeroMean h → KdVPlan.ZeroMean h' →\n A f g h - A f' g' h' =\n   A (f-f') g h + A f' (g-g') h + A f' g' (h-h')" := by
  intro s A hA f f' g g' h h' hf hf' hg hg' hh hh' hf0 hf'0 hg0 hg'0 hh0 hh'0
  have hd := (@yui_aux_0002 T gamma R h_T002 h_T003 h_T017 h_T013 s).2.1
  have hff := (hd f f' hf hf').1
  have hgg := (hd g g' hg hg').1
  have hhh := (hd h h' hh hh').1
  have hff0 : KdVPlan.ZeroMean (f-f') := by change f 0-f' 0=0; rw [show f 0 = 0 from hf0, show f' 0 = 0 from hf'0, sub_self]
  have hgg0 : KdVPlan.ZeroMean (g-g') := by change g 0-g' 0=0; rw [show g 0 = 0 from hg0, show g' 0 = 0 from hg'0, sub_self]
  have hhh0 : KdVPlan.ZeroMean (h-h') := by change h 0-h' 0=0; rw [show h 0 = 0 from hh0, show h' 0 = 0 from hh'0, sub_self]
  have he1 := (hA (f-f') f' g g h h hff hf' hg hg hh hh hff0 hf'0 hg0 hg0 hh0 hh0).1
  have he2 := (hA f' f' (g-g') g' h h hf' hf' hgg hg' hh hh hf'0 hf'0 hgg0 hg'0 hh0 hh0).2.1
  have he3 := (hA f' f' g' g' (h-h') h' hf' hf' hg' hg' hhh hh' hf'0 hf'0 hg'0 hg'0 hhh0 hh'0).2.2.1
  rw [sub_add_cancel] at he1 he2 he3
  rw [he1, he2, he3]
  abel

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (A : KdVPlan.Coeff → KdVPlan.Coeff → KdVPlan.Coeff → KdVPlan.Coeff),\n KdVPlan.BoundedTri s A → ∃ C : ℝ, 0 ≤ C ∧ ∀ f f' g g' h h' : KdVPlan.Coeff,\n KdVPlan.MemH s f → KdVPlan.MemH s f' → KdVPlan.MemH s g → KdVPlan.MemH s g' → KdVPlan.MemH s h → KdVPlan.MemH s h' →\n KdVPlan.ZeroMean f → KdVPlan.ZeroMean f' → KdVPlan.ZeroMean g → KdVPlan.ZeroMean g' → KdVPlan.ZeroMean h → KdVPlan.ZeroMean h' →\n\n KdVPlan.HB 0 (A f g h - A f' g' h')\n (C*(KdVPlan.hn s (f-f')*KdVPlan.hn s g*KdVPlan.hn s h +\n     KdVPlan.hn s f'*KdVPlan.hn s (g-g')*KdVPlan.hn s h +\n     KdVPlan.hn s f'*KdVPlan.hn s g'*KdVPlan.hn s (h-h')))" := by
  intro s A hA
  obtain ⟨C,hC,hbound⟩ := hA.2
  refine ⟨C,hC,?_⟩
  intro f f' g g' h h' hf hf' hg hg' hh hh' hf0 hf'0 hg0 hg'0 hh0 hh'0
  have hd := (@yui_aux_0002 T gamma R h_T002 h_T003 h_T017 h_T013 s).2.1
  have hff := (hd f f' hf hf').1
  have hgg := (hd g g' hg hg').1
  have hhh := (hd h h' hh hh').1
  have hff0 : KdVPlan.ZeroMean (f-f') := by change f 0-f' 0=0; rw [show f 0 = 0 from hf0, show f' 0 = 0 from hf'0, sub_self]
  have hgg0 : KdVPlan.ZeroMean (g-g') := by change g 0-g' 0=0; rw [show g 0 = 0 from hg0, show g' 0 = 0 from hg'0, sub_self]
  have hhh0 : KdVPlan.ZeroMean (h-h') := by change h 0-h' 0=0; rw [show h 0 = 0 from hh0, show h' 0 = 0 from hh'0, sub_self]
  have hb₁ := hbound (f-f') g h hff hg hh hff0 hg0 hh0
  have hb₂ := hbound f' (g-g') h hf' hgg hh hf'0 hgg0 hh0
  have hb₃ := hbound f' g' (h-h') hf' hg' hhh hf'0 hg'0 hhh0
  have ha := (@yui_aux_0002 T gamma R h_T002 h_T003 h_T017 h_T013 0).1
  have h12 := ha _ _ hb₁.1 hb₂.1
  have h123 := ha _ _ h12.1 hb₃.1
  rw [@yui_aux_0016 T gamma R h_T002 h_T003 h_T017 h_T013 s A hA.1 f f' g g' h h' hf hf' hg hg' hh hh' hf0 hf'0 hg0 hg'0 hh0 hh'0]
  refine ⟨h123.1,?_⟩
  calc
    _ ≤ KdVPlan.hn 0 (A (f-f') g h + A f' (g-g') h) + KdVPlan.hn 0 (A f' g' (h-h')) := h123.2
    _ ≤ (KdVPlan.hn 0 (A (f-f') g h) + KdVPlan.hn 0 (A f' (g-g') h)) + KdVPlan.hn 0 (A f' g' (h-h')) := add_le_add h12.2 le_rfl
    _ ≤ (C*KdVPlan.hn s (f-f')*KdVPlan.hn s g*KdVPlan.hn s h +
         C*KdVPlan.hn s f'*KdVPlan.hn s (g-g')*KdVPlan.hn s h) +
         C*KdVPlan.hn s f'*KdVPlan.hn s g'*KdVPlan.hn s (h-h') :=
           add_le_add (add_le_add hb₁.2 hb₂.2) hb₃.2
    _ = _ := by ring

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T002 : KdVPlan.CovarianceBounds) (h_T003 : KdVPlan.FourFrequency) (h_T017 : KdVPlan.MultiplierBound) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (A : KdVPlan.Coeff → KdVPlan.Coeff → KdVPlan.Coeff → KdVPlan.Coeff),\n KdVPlan.BoundedTri s A → KdVPlan.FourierApprox3 s A" := by
  intro s A hA f g h hf hg hh hf0 hg0 hh0
  obtain ⟨C,hC,hdiff⟩ := @yui_aux_0017 T gamma R h_T002 h_T003 h_T017 h_T013 s A hA
  obtain ⟨K,hK,hbound⟩ := hA.2
  have hn := @yui_aux_0001 T gamma R h_T002 h_T003 h_T017 h_T013
  have hcut := (@yui_aux_0015 T gamma R h_T002 h_T003 h_T017 h_T013).2
  have hcut0 := (@yui_aux_0015 T gamma R h_T002 h_T003 h_T017 h_T013).1
  refine ⟨(hbound f g h hf hg hh hf0 hg0 hh0).1,?_⟩
  intro ε hε
  let B := 1+KdVPlan.hn s f+KdVPlan.hn s g+KdVPlan.hn s h
  have hB : 0 < B := by dsimp [B]; linarith [hn s f,hn s g,hn s h]
  have hfB : KdVPlan.hn s f ≤ B := by dsimp [B]; linarith [hn s g,hn s h]
  have hgB : KdVPlan.hn s g ≤ B := by dsimp [B]; linarith [hn s f,hn s h]
  have hhB : KdVPlan.hn s h ≤ B := by dsimp [B]; linarith [hn s f,hn s g]
  let δ := ε/(3*(C+1)*B^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨mf,hmf⟩ := (h_T013.2.2.1 s f hf).2 δ hδ
  obtain ⟨mg,hmg⟩ := (h_T013.2.2.1 s g hg).2 δ hδ
  obtain ⟨mh,hmh⟩ := (h_T013.2.2.1 s h hh).2 δ hδ
  refine ⟨max mf (max mg mh),?_⟩
  intro n hnlarge
  have hnf : mf ≤ n := by omega
  have hng : mg ≤ n := by omega
  have hnh : mh ≤ n := by omega
  have hdf := hmf n hnf
  have hdg := hmg n hng
  have hdh := hmh n hnh
  have hcf := hcut s (n : ℝ) f hf
  have hcg := hcut s (n : ℝ) g hg
  have hch := hcut s (n : ℝ) h hh
  have hcf0 := (hcut0 n f).2 hf0
  have hcg0 := (hcut0 n g).2 hg0
  have hch0 := (hcut0 n h).2 hh0
  have hcgn : KdVPlan.hn s (KdVPlan.cutoff (n : ℝ) g) ≤ B := hcg.2.trans hgB
  have hchn : KdVPlan.hn s (KdVPlan.cutoff (n : ℝ) h) ≤ B := hch.2.trans hhB
  have hd := hdiff (KdVPlan.cutoff (n : ℝ) f) f (KdVPlan.cutoff (n : ℝ) g) g
   (KdVPlan.cutoff (n : ℝ) h) h hcf.1 hf hcg.1 hg hch.1 hh hcf0 hf0 hcg0 hg0 hch0 hh0
  refine ⟨hd.1,hd.2.trans ?_⟩
  calc
    _ ≤ C*(δ*B*B+B*δ*B+B*B*δ) := by
      have hfpos := hn s f
      have hgpos := hn s g
      have hcgpos := hn s (KdVPlan.cutoff (n : ℝ) g)
      have hchpos := hn s (KdVPlan.cutoff (n : ℝ) h)
      gcongr
      · exact hdf.2
      · exact hcgn
      · exact hchn
      · exact hfB
      · exact hdg.2
      · exact hchn
      · exact hfB
      · exact hgB
      · exact hdh.2
    _ ≤ ε := by
      have hden : 3*(C+1)*B^2 ≠ 0 := by positivity
      have he : (3*(C+1)*B^2)*δ = ε := by dsimp [δ]; field_simp
      nlinarith [mul_nonneg (le_of_lt hδ) (sq_nonneg B)]
#check @checked
#print axioms checked
end YuiAuxiliary
