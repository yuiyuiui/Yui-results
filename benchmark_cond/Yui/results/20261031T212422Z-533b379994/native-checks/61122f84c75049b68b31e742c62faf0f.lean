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

namespace Translation
set_option autoImplicit false

namespace Local_T011
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s : ℝ, (∀ f g : KdVPlan.Coeff, KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.MemH s (f-g) ∧ KdVPlan.hn s (f-g) ≤ KdVPlan.hn s f + KdVPlan.hn s g) ∧ (∀ f g : KdVPlan.Coeff, KdVPlan.MemH s f → KdVPlan.MemH s g → |KdVPlan.hn s f-KdVPlan.hn s g| ≤ KdVPlan.hn s (f-g))" := by
  intro s
  have hsub (x y : lp (fun _ : ℤ => ℂ) 2) :
      KdVPlan.FromLP s (x-y) = KdVPlan.FromLP s x - KdVPlan.FromLP s y := by
    funext k
    simp [KdVPlan.FromLP, mul_sub]
  constructor
  · intro f g hf hg
    obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
    obtain ⟨y, rfl⟩ := (h_T013.1 s g).mp hg
    rw [← hsub]
    exact ⟨(h_T013.1 s _).mpr ⟨x-y, rfl⟩, by
      simpa only [h_T013.2.1] using norm_sub_le x y⟩
  · intro f g hf hg
    obtain ⟨x, rfl⟩ := (h_T013.1 s f).mp hf
    obtain ⟨y, rfl⟩ := (h_T013.1 s g).mp hg
    rw [← hsub]
    simpa only [h_T013.2.1] using abs_norm_sub_norm_le x y

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ s a b : ℝ, ∀ f g : KdVPlan.Path, KdVPlan.ContH s a b f → KdVPlan.ContH s a b g → KdVPlan.ContH s a b (fun t => f t-g t) ∧ ContinuousOn (fun t => KdVPlan.hn s (f t-g t)) (Icc a b)" := by
  intro s a b f g hf hg
  have hop := (@yui_aux_0001 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013 s)
  have hc : KdVPlan.ContH s a b (fun t => f t-g t) := by
    constructor
    · intro t ht
      exact (hop.1 _ _ (hf.1 t ht) (hg.1 t ht)).1
    · intro t ht ε hε
      obtain ⟨δ₁, hδ₁, hd₁⟩ := hf.2 t ht (ε/2) (by linarith)
      obtain ⟨δ₂, hδ₂, hd₂⟩ := hg.2 t ht (ε/2) (by linarith)
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro r hr hrt
      have h₁ := hd₁ r hr (lt_of_lt_of_le hrt (min_le_left _ _))
      have h₂ := hd₂ r hr (lt_of_lt_of_le hrt (min_le_right _ _))
      have heq : (f r-g r)-(f t-g t) = (f r-f t)-(g r-g t) := by abel
      rw [heq]
      exact lt_of_le_of_lt (hop.1 _ _ (hop.1 _ _ (hf.1 r hr) (hf.1 t ht)).1
        (hop.1 _ _ (hg.1 r hr) (hg.1 t ht)).1).2 (by linarith)
  refine ⟨hc, ?_⟩
  intro t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hc.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [Real.dist_eq] at hrt ⊢
  exact lt_of_le_of_lt (hop.2 _ _ (hc.1 r hr) (hc.1 t ht)) (hd r hr hrt)

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (δ τ D : ℝ) (m N L : ℕ) (g : ℝ → ℝ) (b : ℝ),\n  0 < τ → 0 ≤ D → (m : ℝ)*τ ≤ δ →\n  T = (L : ℝ)*τ → T ≤ (N : ℝ)*((m : ℝ)*τ) →\n  b ∈ Icc 0 T → g 0 = 0 →\n  (∀ n : ℕ, ∀ t : ℝ, n ≤ L → (n : ℝ)*τ ≤ t → t ≤ T →\n    t-(n : ℝ)*τ ≤ δ → (∀ r ∈ Icc ((n : ℝ)*τ) t, g r ≤ 1) →\n    g t ≤ 2*g ((n : ℝ)*τ)+D) →\n  (∀ t ∈ Icc 0 b, g t ≤ 1) →\n  ∀ t ∈ Icc 0 b, g t ≤ D*((2:ℝ)^N-1)" := by
  intro δ τ D m N L g b hτ hD hm hT hN hb hg0 hloc hboot
  have hind : ∀ j : ℕ, ∀ t ∈ Icc 0 b, t ≤ (j : ℝ)*((m : ℝ)*τ) →
      g t ≤ D*((2:ℝ)^j-1) := by
    intro j
    induction j with
    | zero =>
      intro t ht hstep
      have : t = 0 := by norm_num at hstep; linarith [ht.1]
      simp [this, hg0]
    | succ j ih =>
      intro t ht hstep
      have hmono : D*((2:ℝ)^j-1) ≤ D*((2:ℝ)^(j+1)-1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) j,
          mul_nonneg hD (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) j)]
      by_cases hta : t ≤ (j : ℝ)*((m : ℝ)*τ)
      · exact (ih t ht hta).trans hmono
      · have hat : (j : ℝ)*((m : ℝ)*τ) ≤ t := (lt_of_not_ge hta).le
        have ha0 : 0 ≤ (j : ℝ)*((m : ℝ)*τ) := by positivity
        have ha := ih ((j : ℝ)*((m : ℝ)*τ)) ⟨ha0, hat.trans ht.2⟩ le_rfl
        have hn : j*m ≤ L := by
          have hnc : ((j*m : ℕ) : ℝ) ≤ (L : ℝ) := by
            have htt : t ≤ (L : ℝ)*τ := by rw [← hT]; exact ht.2.trans hb.2
            push_cast
            nlinarith
          exact_mod_cast hnc
        have hd : t - ((j*m : ℕ) : ℝ)*τ ≤ δ := by
          push_cast at hstep ⊢
          nlinarith
        have h := hloc (j*m) t hn (by push_cast; nlinarith)
          (ht.2.trans hb.2) hd (by
            intro r hr
            apply hboot r
            constructor
            · have := hr.1
              push_cast at this
              nlinarith
            · exact hr.2.trans ht.2)
        have heq : (((j*m : ℕ) : ℝ)*τ) = (j : ℝ)*((m : ℝ)*τ) := by push_cast; ring
        rw [heq] at h
        rw [pow_succ]
        nlinarith
  intro t ht
  exact hind N t ht (ht.2.trans (hb.2.trans hN))

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (g : ℝ → ℝ) (c : ℝ), ContinuousOn g (Icc 0 T) → g 0 = 0 → c < 1 →\n  (∀ b ∈ Icc 0 T, (∀ t ∈ Icc 0 b, g t ≤ 1) → ∀ t ∈ Icc 0 b, g t ≤ c) →\n  ∀ t ∈ Icc 0 T, g t ≤ c" := by
  intro g c hc hg0 hsmall hbound
  have hn : ¬ ∃ t ∈ Icc 0 T, 1 ≤ g t := by
    rintro ⟨t, ht, hgt⟩
    let S : Set ℝ := {r ∈ Icc 0 T | 1 ≤ g r}
    have hclosed : IsClosed S := isClosed_Icc.isClosed_le continuousOn_const hc
    have hcompact : IsCompact S :=
      isCompact_Icc.of_isClosed_subset hclosed (fun r hr => hr.1)
    obtain ⟨b, hb, hleast⟩ := hcompact.exists_isLeast ⟨t, ht, hgt⟩
    have hb0 : b ∈ Icc 0 T := hb.1
    have hgb : g b ≤ 1 := by
      by_contra hbad
      have hbig : 1 < g b := lt_of_not_ge hbad
      obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc hb0.1
        (hc.mono (Icc_subset_Icc le_rfl hb0.2))
        (show (1:ℝ) ∈ Icc (g 0) (g b) by rw [hg0]; exact ⟨by norm_num, hbig.le⟩)
      have hrl : r < b := lt_of_le_of_ne hr.2 (by
        intro heq
        rw [heq] at hgr
        linarith)
      have hmem : r ∈ S := ⟨⟨hr.1, hr.2.trans hb0.2⟩, by rw [hgr]⟩
      exact (not_lt_of_ge (hleast hmem)) hrl
    have hboot : ∀ r ∈ Icc 0 b, g r ≤ 1 := by
      intro r hr
      by_cases heq : r = b
      · simpa [heq] using hgb
      · have hrb : r < b := lt_of_le_of_ne hr.2 heq
        by_contra hbad
        have hmem : r ∈ S := ⟨⟨hr.1, hr.2.trans hb0.2⟩, (lt_of_not_ge hbad).le⟩
        exact (not_lt_of_ge (hleast hmem)) hrb
    have h := hbound b hb0 hboot b ⟨hb0.1, le_rfl⟩
    linarith [hb.2]
  have hboot : ∀ t ∈ Icc 0 T, g t ≤ 1 := by
    intro t ht
    exact (lt_of_not_ge (fun h => hn ⟨t, ht, h⟩)).le
  exact hbound T ⟨h_H001.le, le_rfl⟩ hboot

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (τ : ℝ) (f : KdVPlan.Coeff), 0 < τ → KdVPlan.Data 0 f →\n  ∀ n : ℕ, KdVPlan.Data 0 (KdVPlan.numerical τ f n)" := by
  intro τ f hτ hf n
  have hp := (h_T007.1 τ hτ).2.2.1
  induction n with
  | zero => simpa [KdVPlan.numerical] using hf
  | succ n ih =>
    have h := (hp _ ih).1
    simpa [KdVPlan.numerical, Function.iterate_succ_apply'] using h

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (k : ℤ), ‖Complex.exp (Complex.I * ((t * (k : ℝ)^3 : ℝ) : ℂ))‖ = 1" := by
  intro t k
  exact Complex.norm_exp_I_mul_ofReal (t * (k : ℝ)^3)

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s t : ℝ) (f g : KdVPlan.Coeff),\n  (KdVPlan.MemH s (KdVPlan.S t f) ↔ KdVPlan.MemH s f) ∧\n  KdVPlan.hn s (KdVPlan.S t f) = KdVPlan.hn s f ∧\n  KdVPlan.S t (f-g) = KdVPlan.S t f-KdVPlan.S t g ∧ KdVPlan.S 0 f = f" := by
  intro s t f g
  have hn (k : ℤ) : ‖KdVPlan.S t f k‖ = ‖f k‖ := by
    dsimp only [KdVPlan.S]
    rw [norm_mul, @yui_aux_0006 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013]
    exact one_mul _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [KdVPlan.MemH, hn]
  · simp only [KdVPlan.hn, hn]
  · funext k
    exact mul_sub _ _ _
  · funext k
    simp [KdVPlan.S]

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ C δ : ℝ, 0 < C → 0 < δ →\n  let τ₀ := min 1 (min (δ/2) ((1/(4*(C+1)))^(1/gamma)))\n  0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →\n    τ ≤ 1 ∧ τ ≤ δ/2 ∧ C*τ^gamma < 1/4" := by
  intro C δ hC hδ
  dsimp only
  have hx : 0 < 1/(4*(C+1)) := by positivity
  constructor
  · exact lt_min (by norm_num) (lt_min (by positivity) (Real.rpow_pos_of_pos hx _))
  · intro τ hτ hle
    refine ⟨hle.trans (min_le_left _ _),
      hle.trans ((min_le_right _ _).trans (min_le_left _ _)), ?_⟩
    have hpow : τ^gamma ≤ 1/(4*(C+1)) := by
      have hle' : τ ≤ (1/(4*(C+1)))^(1/gamma) :=
        hle.trans ((min_le_right _ _).trans (min_le_right _ _))
      have h := Real.rpow_le_rpow hτ.le hle' h_H002.1.le
      rw [← Real.rpow_mul hx.le, one_div_mul_cancel h_H002.1.ne', Real.rpow_one] at h
      exact h
    have hfrac : C * (1/(4*(C+1))) < 1/4 := by
      apply (lt_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
      have hden : 0 < 4*(C+1) := by positivity
      have : C/(4*(C+1)) < (1/4:ℝ) := (div_lt_iff₀ hden).mpr (by linarith)
      simpa [div_eq_mul_inv] using (mul_lt_mul_of_pos_right this (by norm_num : (0:ℝ)<4))
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow hC.le) hfrac

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ δ τ : ℝ, 0 < δ → 0 < τ → τ ≤ δ/2 →\n  let m := ⌊δ/τ⌋₊\n  let N := ⌈2*T/δ⌉₊+1\n  (m : ℝ)*τ ≤ δ ∧ δ/2 ≤ (m : ℝ)*τ ∧ T ≤ (N : ℝ)*((m : ℝ)*τ)" := by
  intro δ τ hδ hτ ht
  dsimp only
  have hf := Nat.floor_le (show 0 ≤ δ/τ by positivity)
  have hf' := Nat.lt_floor_add_one (δ/τ)
  have hceil := Nat.le_ceil (2*T/δ)
  have hm : (⌊δ/τ⌋₊ : ℝ)*τ ≤ δ := (le_div_iff₀ hτ).mp hf
  have hm' : δ/2 ≤ (⌊δ/τ⌋₊ : ℝ)*τ := by
    have : δ < ((⌊δ/τ⌋₊ : ℝ)+1)*τ := (div_lt_iff₀ hτ).mp hf'
    nlinarith
  refine ⟨hm, hm', ?_⟩
  have hc : 2*T ≤ (⌈2*T/δ⌉₊ : ℝ)*δ := (div_le_iff₀ hδ).mp hceil
  have hnn : 0 ≤ (⌈2*T/δ⌉₊ : ℝ)+1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hm' hnn
  push_cast
  nlinarith

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (δ K τ : ℝ) (L : ℕ) (f : KdVPlan.Coeff) (v : KdVPlan.Path),\n  0 < δ → δ ≤ 1 → 0 < K → 0 < τ → τ ≤ δ/2 → T = (L : ℝ)*τ →\n  KdVPlan.Data 0 f → KdVPlan.Smooth f → KdVPlan.ContH 0 0 T v → v 0 = f →\n  (∀ a b : ℝ, KdVPlan.GridInterval τ L a b → b-a ≤ δ → KdVPlan.enorm a b τ f v ≤ 1 →\n    KdVPlan.enorm a b τ f v ≤ 2*KdVPlan.hn 0 (KdVPlan.err τ f v a)+K*δ*τ^gamma) →\n  let N := ⌈2*T/δ⌉₊+1\n  let C := K*δ*((2:ℝ)^N-1)\n  C*τ^gamma < 1 →\n  KdVPlan.UB 0 0 T (KdVPlan.err τ f v) (C*τ^gamma)" := by
  intro δ K τ L f v hδ hδ1 hK hτ ht hT hf hsf hv hv0 hstab
  dsimp only
  intro hsmall
  let N : ℕ := ⌈2*T/δ⌉₊+1
  let C : ℝ := K*δ*((2:ℝ)^N-1)
  let g : ℝ → ℝ := fun t => KdVPlan.hn 0 (KdVPlan.err τ f v t)
  obtain ⟨hpiece, hreal, hgrid⟩ := h_T007.2.2.2 τ f L hτ hf hsf
  have hV : KdVPlan.ContH 0 0 T (KdVPlan.interp τ f) := by
    rw [hT]
    simpa only [Nat.cast_zero] using hpiece.1 0
  have hcont := @yui_aux_0002 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
    0 0 T v (KdVPlan.interp τ f) hv hV
  have hc : ContinuousOn g (Icc 0 T) := hcont.2
  have hV0 : KdVPlan.interp τ f 0 = f := by
    have h := hgrid 0 (Nat.zero_le L)
    have hzero := (@yui_aux_0007 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013 0 0 f f).2.2.2
    simpa [KdVPlan.twistedNum, KdVPlan.numerical, hzero] using h
  have hg0 : g 0 = 0 := by
    simp [g, KdVPlan.err, hv0, hV0, KdVPlan.hn]
  have hloc : ∀ n : ℕ, ∀ t : ℝ, n ≤ L → (n : ℝ)*τ ≤ t → t ≤ T →
      t-(n : ℝ)*τ ≤ δ → (∀ r ∈ Icc ((n : ℝ)*τ) t, g r ≤ 1) →
      g t ≤ 2*g ((n : ℝ)*τ)+K*δ*τ^gamma := by
    intro n t hn hat htT hd hboot
    have ha0 : 0 ≤ (n : ℝ)*τ := by positivity
    have hgi : KdVPlan.GridInterval τ L ((n : ℝ)*τ) t :=
      ⟨ha0, hat, by rw [← hT]; exact htT, n, hn, rfl⟩
    have hE : KdVPlan.enorm ((n : ℝ)*τ) t τ f v ≤ 1 := by
      apply csSup_le
      · exact ⟨g ((n : ℝ)*τ), (n : ℝ)*τ, ⟨le_rfl, hat⟩, rfl⟩
      · rintro x ⟨r, hr, rfl⟩
        exact hboot r hr
    have h := hstab _ _ hgi hd hE
    have hbd : BddAbove {x : ℝ | ∃ r ∈ Icc ((n : ℝ)*τ) t, x = g r} :=
      ⟨1, by rintro x ⟨r, hr, rfl⟩; exact hboot r hr⟩
    have hpoint : g t ≤ KdVPlan.enorm ((n : ℝ)*τ) t τ f v :=
      le_csSup hbd ⟨t, ⟨hat, le_rfl⟩, rfl⟩
    exact hpoint.trans h
  have hfloor := @yui_aux_0009 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
    δ τ hδ hτ ht
  have hbound : ∀ t ∈ Icc 0 T, g t ≤ C*τ^gamma := by
    apply @yui_aux_0004 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
      g (C*τ^gamma) hc hg0 hsmall
    intro b hb hboot t htb
    have h := @yui_aux_0003 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
      δ τ (K*δ*τ^gamma) ⌊δ/τ⌋₊ N L g b hτ (by positivity) hfloor.1 hT
      hfloor.2.2 hb hg0 hloc hboot t htb
    dsimp only [C]
    nlinarith
  intro t ht
  exact ⟨hcont.1.1 t ht, hbound t ht⟩

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → KdVPlan.ContH 0 a b f" := by
  intro a b f hf
  simpa using hf.2 0 0

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f : KdVPlan.Coeff), KdVPlan.ZeroMean f → KdVPlan.RealField f →\n  KdVPlan.ZeroMean (KdVPlan.S t f) ∧ KdVPlan.RealField (KdVPlan.S t f)" := by
  intro t f hz hr
  constructor
  · change Complex.exp _ * f 0 = 0
    rw [hz, mul_zero]
  · intro k
    change Complex.exp _ * f (-k) = star (Complex.exp _ * f k)
    rw [hr k]
    simp only [star_mul', Complex.star_def]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp
    <;> ring

end Local_T011
open Local_T011 in
theorem T011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_H001 : 0 < T) (h_H002 : 0 < gamma ∧ gamma ≤ 1) (h_H003 : 0 < R) (h_T001 : KdVPlan.FlowOutput T gamma R) (h_T007 : KdVPlan.SchemeOutput) (h_T010 : KdVPlan.StabilityOutput gamma) (h_T013 : KdVPlan.SobolevInfrastructure) :
    KdVPlan.SmoothOutput T gamma R := by
  classical
  obtain ⟨A, hA, hflow⟩ := h_T001.1
  let M : ℝ := 1+A
  have hM : 1 ≤ M := by dsimp [M]; linarith
  obtain ⟨δ, K, hδ, hδ1, hK, hstab⟩ := (h_T010 M hM).2
  let N : ℕ := ⌈2*T/δ⌉₊+1
  let C : ℝ := K*δ*((2:ℝ)^N-1)
  have hC : 0 < C := by
    apply mul_pos (mul_pos hK hδ)
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num : (1:ℝ) < 2) (by dsimp [N]; omega))
  let τ₀ : ℝ := min 1 (min (δ/2) ((1/(4*(C+1)))^(1/gamma)))
  have hsmall := @yui_aux_0008 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
    C δ hC hδ
  refine ⟨C, τ₀, hC, hsmall.1, ?_⟩
  intro f hf hsf hRf L hL hstep
  let τ : ℝ := T/(L : ℝ)
  have hLc : 0 < (L : ℝ) := by exact_mod_cast hL
  have hτ : 0 < τ := div_pos h_H001 hLc
  have hT : T = (L : ℝ)*τ := by dsimp [τ]; field_simp
  obtain ⟨hτ1, hτδ, hsmallτ⟩ := hsmall.2 τ hτ hstep
  have hf0 : KdVPlan.Data 0 f :=
    ⟨(h_T013.2.2.2.1 0 gamma f h_H002.1.le hf.1).1, hf.2⟩
  obtain ⟨u, hu, hbu, hbv, hmu, hsmooth⟩ := hflow f hf hRf
  obtain ⟨hsu, hsv, hder⟩ := hsmooth hsf
  have hS := @yui_aux_0007 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
  have hvcont : KdVPlan.ContH 0 0 T (KdVPlan.Twist u) :=
    @yui_aux_0011 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
      0 T (KdVPlan.Twist u) hsv
  have hreal : KdVPlan.RealPath 0 T (KdVPlan.Twist u) := by
    intro t ht
    obtain ⟨hz, hr⟩ := hu.1.2.1 t ht
    exact @yui_aux_0012 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
      (-t) (u t) hz hr
  have hvbound : KdVPlan.UB gamma 0 T (KdVPlan.Twist u) M := by
    intro t ht
    exact ⟨(hbv t ht).1, (hbv t ht).2.trans (by dsimp [M]; linarith)⟩
  have htraj : KdVPlan.Traj gamma M τ L f (KdVPlan.Twist u) := by
    rw [← hT]
    exact ⟨hf0, hsf, hsv, hreal, hvbound, hder⟩
  have hfull : KdVPlan.UB 0 0 T (KdVPlan.err τ f (KdVPlan.Twist u)) (C*τ^gamma) := by
    apply @yui_aux_0010 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
      δ K τ L f (KdVPlan.Twist u) hδ hδ1 hK hτ hτδ hT hf0 hsf hvcont hu.1.2.2.1
    · intro a b hgrid hlength hboot
      exact hstab τ L f (KdVPlan.Twist u) a b hτ hτδ htraj hgrid hlength hboot
    · change C*τ^gamma < 1
      linarith
  refine ⟨u, hu, hfull, ?_⟩
  intro n hn
  refine ⟨@yui_aux_0005 T gamma R h_H001 h_H002 h_H003 h_T001 h_T007 h_T010 h_T013
    τ f hτ hf0 n, ?_⟩
  have hgrid := (h_T007.2.2.2 τ f L hτ hf0 hsf).2.2 n hn
  have ht : (n : ℝ)*τ ∈ Icc 0 T := by
    constructor
    · positivity
    · rw [hT]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hτ.le
  have heq : KdVPlan.err τ f (KdVPlan.Twist u) ((n : ℝ)*τ) =
      KdVPlan.S (-((n : ℝ)*τ)) (u ((n : ℝ)*τ)-KdVPlan.numerical τ f n) := by
    dsimp only [KdVPlan.err, KdVPlan.Twist]
    rw [hgrid]
    dsimp only [KdVPlan.twistedNum]
    rw [show -(n : ℝ)*τ = -((n : ℝ)*τ) by ring]
    exact (hS 0 (-((n : ℝ)*τ)) (u ((n : ℝ)*τ)) (KdVPlan.numerical τ f n)).2.2.1.symm
  have hb := hfull ((n : ℝ)*τ) ht
  rw [heq] at hb
  have hi := hS 0 (-((n : ℝ)*τ)) (u ((n : ℝ)*τ)-KdVPlan.numerical τ f n) f
  exact ⟨hi.1.mp hb.1, by rw [← hi.2.1]; exact hb.2⟩

#check @T011
#print axioms T011

end Translation
