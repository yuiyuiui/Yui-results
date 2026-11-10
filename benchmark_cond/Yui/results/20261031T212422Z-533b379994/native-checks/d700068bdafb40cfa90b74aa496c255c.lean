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
theorem yui_aux_0001 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f : KdVPlan.Coeff) (k : ℤ), KdVPlan.MemH s f → KdVPlan.weight s k * ‖f k‖^2 ≤ (KdVPlan.hn s f)^2" := by
  intro s f k hf
  have hw : ∀ j : ℤ, 0 ≤ KdVPlan.weight s j * ‖f j‖ ^ 2 := by
    intro j
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  have hs : 0 ≤ ∑' j, KdVPlan.weight s j * ‖f j‖ ^ 2 := tsum_nonneg hw
  rw [KdVPlan.hn, Real.sq_sqrt hs]
  exact Summable.le_tsum hf k (fun j _ => hw j)

theorem yui_aux_0002 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s : ℝ) (f g : KdVPlan.Coeff), KdVPlan.MemH s f → KdVPlan.MemH s g → KdVPlan.MemH s (f-g) ∧ |KdVPlan.hn s f-KdVPlan.hn s g| ≤ KdVPlan.hn s (f-g)" := by
  intro s f g hf hg
  rcases h_T013.1 s f |>.mp hf with ⟨x, rfl⟩
  rcases h_T013.1 s g |>.mp hg with ⟨y, rfl⟩
  have he : KdVPlan.FromLP s x - KdVPlan.FromLP s y = KdVPlan.FromLP s (x-y) := by
    funext k
    simp [KdVPlan.FromLP, mul_sub]
  rw [he]
  constructor
  · exact (h_T013.1 _ _).mpr ⟨x-y, rfl⟩
  · simp only [h_T013.2.1]
    exact abs_norm_sub_norm_le x y

theorem yui_aux_0003 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (s a b : ℝ) (f : KdVPlan.Path), KdVPlan.ContH s a b f → ContinuousOn (fun t => KdVPlan.hn s (f t)) (Set.Icc a b)" := by
  intro s a b f hf t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  rcases hf.2 t ht ε hε with ⟨δ, hδ, hd⟩
  refine ⟨δ, hδ, ?_⟩
  intro r hr hdr
  rw [Real.dist_eq]
  exact lt_of_le_of_lt ((yui_aux_0002 T gamma R h_T016 h_T013 s (f r) (f t) (hf.1 r hr) (hf.1 t ht)).2) (hd r hr (by simpa [Real.dist_eq] using hdr))

theorem yui_aux_0004 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f : KdVPlan.Coeff) (k : ℤ), (KdVPlan.MemH 0 f → ‖f k‖ ≤ KdVPlan.hn 0 f) ∧ (KdVPlan.MemH 2 f → ‖f k‖ ≤ KdVPlan.hn 2 f / (1+(k : ℝ)^2))" := by
  intro f k
  constructor
  · intro hf
    have h := yui_aux_0001 T gamma R h_T016 h_T013 0 f k hf
    simp only [KdVPlan.weight, Real.rpow_zero, one_mul] at h
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp h
  · intro hf
    have h := yui_aux_0001 T gamma R h_T016 h_T013 2 f k hf
    simp only [KdVPlan.weight, Real.rpow_two] at h
    apply (le_div_iff₀ (by positivity : 0 < 1+(k : ℝ)^2)).mpr
    apply (sq_le_sq₀ (by positivity) (show 0 ≤ KdVPlan.hn 2 f from Real.sqrt_nonneg _)).mp
    simpa only [mul_pow, mul_comm] using h

theorem yui_aux_0005 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Path), KdVPlan.ContH 2 a b f → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ k : ℤ, ‖f t k‖ ≤ C / (1+(k : ℝ)^2)" := by
  intro a b f hf
  rcases isCompact_Icc.exists_bound_of_continuousOn (yui_aux_0003 T gamma R h_T016 h_T013 2 a b f hf) with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht k
  apply (yui_aux_0004 T gamma R h_T016 h_T013 (f t) k).2 (hf.1 t ht) |>.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (le_abs_self _).trans ((hC t ht).trans (le_max_left _ _))

theorem yui_aux_0006 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (k : ℤ) (f : ℤ → ℂ), (∑' j : ℤ, f (k-j)) = ∑' j : ℤ, f j" := by
  intro k f
  simpa only [Equiv.subLeft_apply] using ((Equiv.subLeft k).tsum_eq f)

theorem yui_aux_0007 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ f g : KdVPlan.Coeff, KdVPlan.mul f g = KdVPlan.mul g f) ∧ (∀ (t : ℝ) (f g : KdVPlan.Coeff), KdVPlan.J t f g = KdVPlan.J t g f)" := by
  have hm : ∀ f g : KdVPlan.Coeff, KdVPlan.mul f g = KdVPlan.mul g f := by
    intro f g
    funext k
    unfold KdVPlan.mul
    calc
      (∑' j : ℤ, f j*g (k-j)) = ∑' j : ℤ, g (k-j)*f (k-(k-j)) := by
        apply tsum_congr
        intro j
        simp only [sub_sub_cancel]
        exact mul_comm _ _
      _ = ∑' j : ℤ, g j*f (k-j) := yui_aux_0006 T gamma R h_T016 h_T013 k (fun j : ℤ => g j * f (k-j))
  exact ⟨hm, fun t f g => by unfold KdVPlan.J; rw [hm]⟩

theorem yui_aux_0008 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "Summable (fun j : ℤ => (1 : ℝ) / (1+(j : ℝ)^2))" := by
  have h : Summable (fun j : ℤ => if j = 0 then (1 : ℝ) else 1/(j : ℝ)^2) := by
    have hs : Summable (fun j : ℤ => (1 : ℝ)/(j : ℝ)^2) := Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)
    exact hs.congr_cofinite (by filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with j hj; simp [hj])
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ h
  intro j
  split_ifs with hj
  · subst j; norm_num
  · exact one_div_le_one_div_of_le (by positivity) (by linarith [sq_nonneg (j : ℝ)])

theorem yui_aux_0009 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (k j : ℤ), Complex.exp (Complex.I * ((-t) * (k : ℝ)^3 : ℝ)) * Complex.exp (Complex.I * (t * (j : ℝ)^3 : ℝ)) * Complex.exp (Complex.I * (t * ((k-j : ℤ) : ℝ)^3 : ℝ)) = KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t" := by
  intro t k j
  unfold KdVPlan.phase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem yui_aux_0010 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g : KdVPlan.Coeff) (k : ℤ), k ≠ 0 → KdVPlan.J t f g k = ∑' j : ℤ, (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f j * g (k-j)" := by
  intro t f g k hk
  simp only [KdVPlan.J, KdVPlan.S, KdVPlan.P, if_neg hk, KdVPlan.mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [← yui_aux_0009 T gamma R h_T016 h_T013 t k j]
  by_cases hj : j = 0
  · simp [KdVPlan.invD, hj]
  by_cases hs : k-j = 0
  · simp [KdVPlan.invD, hs]
  simp only [KdVPlan.invD, if_neg hj, if_neg hs, mul_inv_rev, div_eq_mul_inv]
  ring

theorem yui_aux_0011 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (t : ℝ) (f g : KdVPlan.Coeff) (k : ℤ), KdVPlan.B t f g k = ∑' j : ℤ, (Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f j * g (k-j)" := by
  intro t f g k
  simp only [KdVPlan.B, KdVPlan.S, KdVPlan.dx, KdVPlan.mul]
  rw [← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [← yui_aux_0009 T gamma R h_T016 h_T013 t k j]
  ring

theorem yui_aux_0012 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (α t : ℝ), ‖KdVPlan.phase α t‖ = 1) ∧ (∀ j : ℤ, ‖(Complex.I * (j : ℂ))⁻¹‖ ≤ 1)" := by
  constructor
  · intro α t
    simp [KdVPlan.phase, Complex.norm_exp]
  · intro j
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul]
    by_cases hj : j = 0
    · simp [hj]
    have hj1 : (1 : ℝ) ≤ ‖(j : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast (Int.one_le_abs hj)
    exact inv_le_one_of_one_le₀ hj1

theorem yui_aux_0013 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (α t : ℝ), HasDerivAt (KdVPlan.phase α) ((-Complex.I * (α : ℂ)) * KdVPlan.phase α t) t" := by
  intro α t
  unfold KdVPlan.phase
  convert (((hasDerivAt_id t).mul_const α).ofReal_comp.const_mul (-Complex.I)).cexp using 1 <;> simp only [id_eq, one_mul] <;> ring

theorem yui_aux_0014 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (k j : ℤ), j ≠ 0 → k-j ≠ 0 → (-Complex.I * ((3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ) : ℝ) : ℂ)) / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ))) = 3 * Complex.I * (k : ℂ)" := by
  intro k j hj hs
  have hjc : (j : ℂ) ≠ 0 := by exact_mod_cast hj
  have hsc : ((k-j : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast at hsc ⊢
  field_simp [hjc, hsc]
  ring_nf
  simp [Complex.I_sq]

theorem yui_aux_0015 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (k j : ℤ) (t : ℝ) (f g : ℝ → ℂ) (df dg : ℂ), HasDerivAt f df t → HasDerivAt g dg t → (j = 0 → f t = 0) → (k-j = 0 → g t = 0) → HasDerivAt (fun r => (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) r / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f r * g r) (3 * ((Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t * g t) + (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * df * g t + (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t * dg) t" := by
  intro k j t f g df dg hf hg hfj hgs
  have h := (((yui_aux_0013 T gamma R h_T016 h_T013 (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t).div_const ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))).mul hf).mul hg
  apply h.congr_deriv
  simp only [Pi.mul_apply]
  by_cases hj : j = 0
  · simp [hj, hfj hj]
  by_cases hs : k-j = 0
  · simp [hs, hgs hs]
  have he := yui_aux_0014 T gamma R h_T016 h_T013 k j hj hs
  simp only [div_eq_mul_inv] at he ⊢
  linear_combination (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t * g t) * he

theorem yui_aux_0016 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (k j : ℤ) (t : ℝ), ‖KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))‖ ≤ 1" := by
  intro k j t
  rw [div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul, (yui_aux_0012 T gamma R h_T016 h_T013).1, one_mul]
  exact (mul_le_mul (yui_aux_0012 T gamma R h_T016 h_T013 |>.2 (k-j)) (yui_aux_0012 T gamma R h_T016 h_T013 |>.2 j) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem yui_aux_0017 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Path), KdVPlan.ContH 0 a b f → ∀ k : ℤ, ContinuousOn (fun t => f t k) (Set.Icc a b)" := by
  intro a b f hf k t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  rcases hf.2 t ht ε hε with ⟨δ, hδ, hd⟩
  refine ⟨δ, hδ, ?_⟩
  intro r hr hdr
  rw [dist_eq_norm]
  exact lt_of_le_of_lt ((yui_aux_0004 T gamma R h_T016 h_T013 (f r-f t) k).1 ((yui_aux_0002 T gamma R h_T016 h_T013 0 (f r) (f t) (hf.1 r hr) (hf.1 t ht)).1)) (hd r hr (by simpa [Real.dist_eq] using hdr))

theorem yui_aux_0018 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (k j : ℤ) (t A D : ℝ) (x y : ℂ), 0 ≤ A → 0 ≤ D → ‖x‖ ≤ A / (1+(j : ℝ)^2) → ‖y‖ ≤ D → ‖(Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * x * y‖ ≤ (|(k : ℝ)| * A * D) / (1+(j : ℝ)^2) ∧ ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * x * y‖ ≤ (A * D) / (1+(j : ℝ)^2)" := by
  intro k j t A D x y hA hD hx hy
  have hm : ‖x‖ * ‖y‖ ≤ A*D/(1+(j : ℝ)^2) := by
    calc
      _ ≤ A/(1+(j : ℝ)^2)*D := mul_le_mul hx hy (norm_nonneg _) (by positivity)
      _ = _ := by ring
  constructor
  · simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, (yui_aux_0012 T gamma R h_T016 h_T013).1, mul_one, one_mul]
    calc
      |(k : ℝ)| * ‖x‖ * ‖y‖ = |(k : ℝ)| * (‖x‖ * ‖y‖) := by ring
      _ ≤ |(k : ℝ)| * (A*D/(1+(j : ℝ)^2)) := mul_le_mul_of_nonneg_left hm (abs_nonneg _)
      _ = _ := by ring
  · simp only [norm_mul]
    calc
      _ ≤ 1 * ‖x‖ * ‖y‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (yui_aux_0016 T gamma R h_T016 h_T013 k j t) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ _ := by simpa using hm

theorem yui_aux_0019 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path) (A D : ℝ), 0 ≤ A → 0 ≤ D → (∀ k : ℤ, ContinuousOn (fun t => f t k) (Set.Icc a b)) → (∀ k : ℤ, ContinuousOn (fun t => g t k) (Set.Icc a b)) → (∀ t ∈ Set.Icc a b, ∀ j : ℤ, ‖f t j‖ ≤ A / (1+(j : ℝ)^2)) → (∀ t ∈ Set.Icc a b, ∀ j : ℤ, ‖g t j‖ ≤ D) → ∀ k : ℤ, ContinuousOn (fun t => KdVPlan.B t (f t) (g t) k) (Set.Icc a b) ∧ ContinuousOn (fun t => KdVPlan.J t (f t) (g t) k) (Set.Icc a b) ∧ ∀ t ∈ Set.Icc a b, Summable (fun j : ℤ => (Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j)) ∧ Summable (fun j : ℤ => (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * g t (k-j))" := by
  intro a b f g A D hA hD hf hg hfb hgb k
  have hpc : ∀ α : ℝ, Continuous (KdVPlan.phase α) := fun α => continuous_iff_continuousAt.mpr (fun t => (yui_aux_0013 T gamma R h_T016 h_T013 α t).continuousAt)
  have hb : ∀ (j : ℤ) (t : ℝ), t ∈ Set.Icc a b → ‖(Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j)‖ ≤ (|(k : ℝ)| * A * D) / (1+(j : ℝ)^2) := fun j t ht => (yui_aux_0018 T gamma R h_T016 h_T013 k j t A D (f t j) (g t (k-j)) hA hD (hfb t ht j) (hgb t ht (k-j))).1
  have hj : ∀ (j : ℤ) (t : ℝ), t ∈ Set.Icc a b → ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * g t (k-j)‖ ≤ (A * D) / (1+(j : ℝ)^2) := fun j t ht => (yui_aux_0018 T gamma R h_T016 h_T013 k j t A D (f t j) (g t (k-j)) hA hD (hfb t ht j) (hgb t ht (k-j))).2
  have hbs : Summable (fun j : ℤ => (|(k : ℝ)| * A * D) / (1+(j : ℝ)^2)) := by simpa only [mul_one_div] using (yui_aux_0008 T gamma R h_T016 h_T013).mul_left (|(k : ℝ)| * A * D)
  have hjs : Summable (fun j : ℤ => (A * D) / (1+(j : ℝ)^2)) := by simpa only [mul_one_div] using (yui_aux_0008 T gamma R h_T016 h_T013).mul_left (A * D)
  refine ⟨?_, ?_, fun t ht => ⟨Summable.of_norm_bounded hbs (fun j => hb j t ht), Summable.of_norm_bounded hjs (fun j => hj j t ht)⟩⟩
  · simp_rw [yui_aux_0011 T gamma R h_T016 h_T013]
    exact continuousOn_tsum (fun j => ((continuousOn_const.mul (hpc _).continuousOn).mul (hf j)).mul (hg (k-j))) hbs hb
  · by_cases hk : k = 0
    · subst k
      simpa [KdVPlan.J, KdVPlan.S, KdVPlan.P] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) (Set.Icc a b))
    · simp_rw [yui_aux_0010 T gamma R h_T016 h_T013 _ _ _ k hk]
      exact continuousOn_tsum (fun j => (((hpc _).continuousOn.div_const _).mul (hf j)).mul (hg (k-j))) hjs hj

theorem yui_aux_0020 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g df dg : KdVPlan.Path) (C : ℝ), 0 ≤ C → (∀ u ∈ ({f,g,df,dg} : Set KdVPlan.Path), ∀ t ∈ Set.Icc a b, ∀ j : ℤ, ‖u t j‖ ≤ C / (1+(j : ℝ)^2)) → (∀ t ∈ Set.Ioo a b, ∀ j : ℤ, HasDerivAt (fun r => f r j) (df t j) t ∧ HasDerivAt (fun r => g r j) (dg t j) t) → (∀ t ∈ Set.Icc a b, KdVPlan.ZeroMean (f t) ∧ KdVPlan.ZeroMean (g t)) → ∀ t ∈ Set.Ioo a b, ∀ k : ℤ, HasDerivAt (fun r => KdVPlan.J r (f r) (g r) k) (3 * KdVPlan.B t (f t) (g t) k + KdVPlan.J t (df t) (g t) k + KdVPlan.J t (f t) (dg t) k) t" := by
  intro a b f g df dg C hC hbd hd hz t ht k
  by_cases hk : k = 0
  · subst k
    simpa [KdVPlan.J, KdVPlan.B, KdVPlan.S, KdVPlan.P, KdVPlan.dx] using (hasDerivAt_const t (0 : ℂ))
  have hplain : ∀ u ∈ ({f,g,df,dg} : Set KdVPlan.Path), ∀ t ∈ Set.Icc a b, ∀ j : ℤ, ‖u t j‖ ≤ C := by
    intro u hu r hr j
    exact (hbd u hu r hr j).trans (div_le_self hC (by nlinarith [sq_nonneg (j : ℝ)]))
  have hbound : ∀ (j : ℤ) (t : ℝ), t ∈ Set.Icc a b →
   ‖3 * ((Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j)) + (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * df t j * g t (k-j) + (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * dg t (k-j)‖ ≤ ((3*|(k : ℝ)|+2)*C*C) / (1+(j : ℝ)^2) := by
    intro j t ht
    have h1 := (yui_aux_0018 T gamma R h_T016 h_T013 k j t C C (f t j) (g t (k-j)) hC hC (hbd f (by simp) t ht j) (hplain g (by simp) t ht (k-j))).1
    have h2 := (yui_aux_0018 T gamma R h_T016 h_T013 k j t C C (df t j) (g t (k-j)) hC hC (hbd df (by simp) t ht j) (hplain g (by simp) t ht (k-j))).2
    have h3 := (yui_aux_0018 T gamma R h_T016 h_T013 k j t C C (f t j) (dg t (k-j)) hC hC (hbd f (by simp) t ht j) (hplain dg (by simp) t ht (k-j))).2
    calc
      _ ≤ (3 : ℝ)*‖(Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j)‖ + ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * df t j * g t (k-j)‖ + ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * dg t (k-j)‖ := by
        calc
          _ ≤ ‖3 * ((Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j)) + (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * df t j * g t (k-j)‖ + ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * dg t (k-j)‖ := norm_add_le _ _
          _ ≤ (3 : ℝ)*‖(Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j)‖ + ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * df t j * g t (k-j)‖ + ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * dg t (k-j)‖ := by
            apply add_le_add
            · calc
                _ ≤ ‖3 * ((Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j))‖ + ‖(KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * df t j * g t (k-j)‖ := norm_add_le _ _
                _ = _ := by simp only [norm_mul, Complex.norm_ofNat]
            · exact le_rfl
      _ ≤ 3*(|(k : ℝ)| *C*C/(1+(j : ℝ)^2)) + (C*C/(1+(j : ℝ)^2)) + (C*C/(1+(j : ℝ)^2)) := by gcongr
      _ = _ := by ring
  have hs : Summable (fun j : ℤ => ((3*|(k : ℝ)|+2)*C*C) / (1+(j : ℝ)^2)) := by
    simpa only [mul_one_div] using (yui_aux_0008 T gamma R h_T016 h_T013).mul_left ((3*|(k : ℝ)|+2)*C*C)
  have hs' : Summable (fun j : ℤ => C*C / (1+(j : ℝ)^2)) := by
    simpa only [mul_one_div] using (yui_aux_0008 T gamma R h_T016 h_T013).mul_left (C*C)
  have hbase : Summable (fun j : ℤ => (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * g t (k-j)) := Summable.of_norm_bounded hs' (fun j => (yui_aux_0018 T gamma R h_T016 h_T013 k j t C C (f t j) (g t (k-j)) hC hC (hbd f (by simp) t (Set.Ioo_subset_Icc_self ht) j) (hplain g (by simp) t (Set.Ioo_subset_Icc_self ht) (k-j))).2)
  have H := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo (convex_Ioo a b).isPreconnected
    (fun j r hr => yui_aux_0015 T gamma R h_T016 h_T013 k j r (fun x => f x j) (fun x => g x (k-j)) (df r j) (dg r (k-j)) (hd r hr j).1 (hd r hr (k-j)).2 (fun hj => by subst j; exact (hz r (Set.Ioo_subset_Icc_self hr)).1) (fun hj => by rw [hj]; exact (hz r (Set.Ioo_subset_Icc_self hr)).2))
    (fun j r hr => hbound j r (Set.Ioo_subset_Icc_self hr)) ht hbase ht
  simp_rw [yui_aux_0010 T gamma R h_T016 h_T013 _ _ _ k hk]
  apply H.congr_deriv
  have hdf : Summable (fun j : ℤ => (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * df t j * g t (k-j)) := Summable.of_norm_bounded hs' (fun j => (yui_aux_0018 T gamma R h_T016 h_T013 k j t C C (df t j) (g t (k-j)) hC hC (hbd df (by simp) t (Set.Ioo_subset_Icc_self ht) j) (hplain g (by simp) t (Set.Ioo_subset_Icc_self ht) (k-j))).2)
  have hdg : Summable (fun j : ℤ => (KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t / ((Complex.I * (j : ℂ)) * (Complex.I * ((k-j : ℤ) : ℂ)))) * f t j * dg t (k-j)) := Summable.of_norm_bounded hs' (fun j => (yui_aux_0018 T gamma R h_T016 h_T013 k j t C C (f t j) (dg t (k-j)) hC hC (hbd f (by simp) t (Set.Ioo_subset_Icc_self ht) j) (hplain dg (by simp) t (Set.Ioo_subset_Icc_self ht) (k-j))).2)
  have hbs : Summable (fun j : ℤ => (Complex.I * (k : ℂ)) * KdVPlan.phase (3*(k : ℝ)*(j : ℝ)*((k-j : ℤ) : ℝ)) t * f t j * g t (k-j)) := by
    apply Summable.of_norm_bounded ((yui_aux_0008 T gamma R h_T016 h_T013).mul_left (|(k : ℝ)| *C*C))
    intro j
    simpa only [mul_one_div] using (yui_aux_0018 T gamma R h_T016 h_T013 k j t C C (f t j) (g t (k-j)) hC hC (hbd f (by simp) t (Set.Ioo_subset_Icc_self ht) j) (hplain g (by simp) t (Set.Ioo_subset_Icc_self ht) (k-j))).1
  rw [Summable.tsum_add ((hbs.mul_left 3).add hdf) hdg, Summable.tsum_add (hbs.mul_left 3) hdf, tsum_mul_left, yui_aux_0011 T gamma R h_T016 h_T013]

theorem yui_aux_0021 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f : KdVPlan.Path), KdVPlan.SmoothOn a b f → ∃ (df : KdVPlan.Path) (C : ℝ), 0 ≤ C ∧ (∀ k : ℤ, ContinuousOn (fun t => f t k) (Set.Icc a b)) ∧ (∀ k : ℤ, ContinuousOn (fun t => df t k) (Set.Icc a b)) ∧ (∀ t ∈ Set.Icc a b, ∀ j : ℤ, ‖f t j‖ ≤ C / (1+(j : ℝ)^2) ∧ ‖df t j‖ ≤ C / (1+(j : ℝ)^2)) ∧ (∀ t ∈ Set.Ioo a b, ∀ j : ℤ, HasDerivAt (fun r => f r j) (df t j) t ∧ df t j = KdVPlan.dt f t j)" := by
  intro a b f hf
  let df : KdVPlan.Path := fun t k => derivWithin (fun r => f r k) (Set.Icc a b) t
  have hfc : KdVPlan.ContH 2 a b f := by simpa only [iteratedDerivWithin_zero, Nat.cast_ofNat] using hf.2 2 0
  have hdc : KdVPlan.ContH 2 a b df := by simpa only [iteratedDerivWithin_one, Nat.cast_ofNat] using hf.2 2 1
  have hd0 : KdVPlan.ContH 0 a b df := by simpa only [iteratedDerivWithin_one, Nat.cast_zero] using hf.2 0 1
  rcases yui_aux_0005 T gamma R h_T016 h_T013 a b f hfc with ⟨A, hA, hbA⟩
  rcases yui_aux_0005 T gamma R h_T016 h_T013 a b df hdc with ⟨D, hD, hbD⟩
  refine ⟨df, A+D, add_nonneg hA hD, (fun k => (hf.1 k).continuousOn), yui_aux_0017 T gamma R h_T016 h_T013 a b df hd0, ?_, ?_⟩
  · intro t ht j
    exact ⟨(hbA t ht j).trans (div_le_div_of_nonneg_right (by linarith) (by positivity)), (hbD t ht j).trans (div_le_div_of_nonneg_right (by linarith) (by positivity))⟩
  · intro t ht j
    have he : df t j = KdVPlan.dt f t j := derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    refine ⟨?_, he⟩
    rw [he]
    exact (((hf.1 j).differentiableOn (by simp)) t (Set.Ioo_subset_Icc_self ht)).differentiableAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivAt

theorem yui_aux_0022 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (u : ℝ → ℂ), ContinuousOn u (Set.Icc a b) → a ≤ b → IntervalIntegrable u MeasureTheory.volume a b" := by
  intro a b u hu hab
  exact hu.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab

theorem yui_aux_0023 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : ℝ → ℂ), a ≤ b → Set.EqOn f g (Set.Ioo a b) → (∫ t in a..b, f t) = ∫ t in a..b, g t" := by
  intro a b f g hab hfg
  exact intervalIntegral.integral_congr_Ioo_of_le (μ := MeasureTheory.volume) hab hfg

theorem yui_aux_0024 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), a ≤ b → KdVPlan.SmoothOn a b f → KdVPlan.SmoothOn a b g → (∀ t ∈ Set.Icc a b, KdVPlan.ZeroMean (f t) ∧ KdVPlan.ZeroMean (g t)) → ∀ k : ℤ, IntervalIntegrable (fun t => KdVPlan.B t (f t) (g t) k) MeasureTheory.volume a b ∧ IntervalIntegrable (fun t => KdVPlan.J t (KdVPlan.dt f t) (g t) k + KdVPlan.J t (f t) (KdVPlan.dt g t) k) MeasureTheory.volume a b ∧ KdVPlan.J b (f b) (g b) k-KdVPlan.J a (f a) (g a) k = 3*(∫ t in a..b, KdVPlan.B t (f t) (g t) k)+(∫ t in a..b, KdVPlan.J t (KdVPlan.dt f t) (g t) k+KdVPlan.J t (f t) (KdVPlan.dt g t) k)" := by
  intro a b f g hab hf hg hz k
  rcases yui_aux_0021 T gamma R h_T016 h_T013 a b f hf with ⟨df, A, hA, hfc, hdfc, hfb, hfd⟩
  rcases yui_aux_0021 T gamma R h_T016 h_T013 a b g hg with ⟨dg, D, hD, hgc, hdgc, hgb, hgd⟩
  let C := A+D
  have hC : 0 ≤ C := add_nonneg hA hD
  have HC : ∀ u ∈ ({f,g,df,dg} : Set KdVPlan.Path), ∀ k : ℤ, ContinuousOn (fun t => u t k) (Set.Icc a b) := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hfc
    · exact hgc
    · exact hdfc
    · exact hdgc
  have HB : ∀ u ∈ ({f,g,df,dg} : Set KdVPlan.Path), ∀ t ∈ Set.Icc a b, ∀ j : ℤ, ‖u t j‖ ≤ C / (1+(j : ℝ)^2) := by
    intro u hu t ht j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact (hfb t ht j).1.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
    · exact (hgb t ht j).1.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
    · exact (hfb t ht j).2.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
    · exact (hgb t ht j).2.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
  have H (u : KdVPlan.Path) (hu : u ∈ ({f,g,df,dg} : Set KdVPlan.Path)) (v : KdVPlan.Path) (hv : v ∈ ({f,g,df,dg} : Set KdVPlan.Path)) :=
    yui_aux_0019 T gamma R h_T016 h_T013 a b u v C C hC hC (HC u hu) (HC v hv) (HB u hu) (fun t ht j => (HB v hv t ht j).trans (div_le_self hC (by nlinarith [sq_nonneg (j : ℝ)]))) k
  have ib := (H f (by simp) g (by simp)).1.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have idf := (H df (by simp) g (by simp)).2.1.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have idg := (H f (by simp) dg (by simp)).2.1.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  have heq : Set.EqOn (fun t => KdVPlan.J t (df t) (g t) k+KdVPlan.J t (f t) (dg t) k) (fun t => KdVPlan.J t (KdVPlan.dt f t) (g t) k+KdVPlan.J t (f t) (KdVPlan.dt g t) k) (Set.Ioo a b) := by
    intro t ht
    have hfe : df t = KdVPlan.dt f t := funext (fun j => (hfd t ht j).2)
    have hge : dg t = KdVPlan.dt g t := funext (fun j => (hgd t ht j).2)
    dsimp only
    rw [hfe, hge]
  have idt := (idf.add idg).congr_uIoo (by simpa only [Set.uIoo_of_le hab] using heq)
  refine ⟨ib, idt, ?_⟩
  have hd := yui_aux_0020 T gamma R h_T016 h_T013 a b f g df dg C hC HB (fun t ht j => ⟨(hfd t ht j).1, (hgd t ht j).1⟩) hz
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (H f (by simp) g (by simp)).2.1 (fun t ht => hd t ht k) (((ib.const_mul 3).add idf).add idg)
  rw [intervalIntegral.integral_add ((ib.const_mul 3).add idf) idg, intervalIntegral.integral_add (ib.const_mul 3) idf, intervalIntegral.integral_const_mul] at hftc
  have ie := yui_aux_0023 T gamma R h_T016 h_T013 a b _ _ hab heq
  rw [intervalIntegral.integral_add idf idg] at ie
  linear_combination -hftc + ie

theorem yui_aux_0025 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (p : Finset ℝ) (a b : ℝ) (U V H : ℝ → ℂ), a ≤ b → (∀ l r : ℝ, a ≤ l → l < r → r ≤ b → (∀ x ∈ p, x ∉ Set.Ioo l r) → IntervalIntegrable U MeasureTheory.volume l r ∧ IntervalIntegrable V MeasureTheory.volume l r ∧ H r-H l = 3*(∫ t in l..r, U t)+(∫ t in l..r, V t)) → IntervalIntegrable U MeasureTheory.volume a b ∧ IntervalIntegrable V MeasureTheory.volume a b ∧ H b-H a = 3*(∫ t in a..b, U t)+(∫ t in a..b, V t)" := by
  classical
  intro p
  induction p using Finset.induction_on with
  | empty =>
    intro a b U V H hab hs
    by_cases he : a = b
    · subst b; simp
    · exact hs a b le_rfl (lt_of_le_of_ne hab he) le_rfl (by simp)
  | @insert x p hxp ih =>
    intro a b U V H hab hs
    by_cases hx : x ∈ Set.Ioo a b
    · have hl := ih a x U V H hx.1.le (by
        intro l r hal hlr hrx hp
        apply hs l r hal hlr (hrx.trans hx.2.le)
        intro y hy hylr
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (not_lt_of_ge hrx) hylr.2
        · exact hp y hy hylr)
      have hr := ih x b U V H hx.2.le (by
        intro l r hxl hlr hrb hp
        apply hs l r (hx.1.le.trans hxl) hlr hrb
        intro y hy hylr
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (not_lt_of_ge hxl) hylr.1
        · exact hp y hy hylr)
      refine ⟨hl.1.trans hr.1, hl.2.1.trans hr.2.1, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hl.1 hr.1, ← intervalIntegral.integral_add_adjacent_intervals hl.2.1 hr.2.1]
      linear_combination hl.2.2 + hr.2.2
    · apply ih a b U V H hab
      intro l r hal hlr hrb hp
      apply hs l r hal hlr hrb
      intro y hy hylr
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx ⟨lt_of_le_of_lt hal hylr.1, lt_of_lt_of_le hylr.2 hrb⟩
      · exact hp y hy hylr

theorem yui_aux_0026 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Path), a ≤ b → KdVPlan.Piecewise a b f → KdVPlan.Piecewise a b g → (∀ t ∈ Set.Icc a b, KdVPlan.ZeroMean (f t)) → (∀ t ∈ Set.Icc a b, KdVPlan.ZeroMean (g t)) → KdVPlan.timeInt a b (fun t => KdVPlan.B t (f t) (g t)) = KdVPlan.scale (1/3) (KdVPlan.J b (f b) (g b)-KdVPlan.J a (f a) (g a)) - KdVPlan.scale (1/3) (KdVPlan.timeInt a b (fun t => KdVPlan.J t (KdVPlan.dt f t) (g t)+KdVPlan.J t (f t) (KdVPlan.dt g t)))" := by
  classical
  intro a b f g hab hf hg hzf hzg
  rcases hf.2 with ⟨p, hp⟩
  rcases hg.2 with ⟨q, hq⟩
  funext k
  have H := yui_aux_0025 T gamma R h_T016 h_T013 (p ∪ q) a b
    (fun t => KdVPlan.B t (f t) (g t) k)
    (fun t => KdVPlan.J t (KdVPlan.dt f t) (g t) k+KdVPlan.J t (f t) (KdVPlan.dt g t) k)
    (fun t => KdVPlan.J t (f t) (g t) k) hab (by
      intro l r hal hlr hrb hclear
      exact yui_aux_0024 T gamma R h_T016 h_T013 l r f g hlr.le
        (hp l r hal hlr hrb (fun x hx => hclear x (Finset.mem_union_left q hx)))
        (hq l r hal hlr hrb (fun x hx => hclear x (Finset.mem_union_right p hx)))
        (fun t ht => ⟨hzf t ⟨hal.trans ht.1, ht.2.trans hrb⟩, hzg t ⟨hal.trans ht.1, ht.2.trans hrb⟩⟩) k)
  change (∫ t in a..b, KdVPlan.B t (f t) (g t) k) =
    (1/3 : ℂ)*(KdVPlan.J b (f b) (g b) k-KdVPlan.J a (f a) (g a) k) -
    (1/3 : ℂ)*(∫ t in a..b, KdVPlan.J t (KdVPlan.dt f t) (g t) k+KdVPlan.J t (f t) (KdVPlan.dt g t) k)
  linear_combination (-1/3 : ℂ)*H.2.2

theorem yui_aux_0027 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (t : ℝ) (f : KdVPlan.Coeff), KdVPlan.S t (KdVPlan.S (-t) f) = f) ∧ (∀ (t : ℝ) (f : KdVPlan.Coeff), KdVPlan.invD (KdVPlan.S t f) = KdVPlan.S t (KdVPlan.invD f)) ∧ (∀ f : KdVPlan.Coeff, KdVPlan.invD (KdVPlan.dx f) = KdVPlan.P f)" := by
  constructor
  · intro t f
    funext k
    simp only [KdVPlan.S, ← mul_assoc, ← Complex.exp_add]
    have he : Complex.I * (t*(k : ℝ)^3 : ℝ) + Complex.I * ((-t)*(k : ℝ)^3 : ℝ) = 0 := by push_cast; ring
    rw [he, Complex.exp_zero, one_mul]
  constructor
  · intro t f
    funext k
    by_cases hk : k = 0
    · simp [KdVPlan.invD, KdVPlan.S, hk]
    · simp only [KdVPlan.invD, KdVPlan.S, if_neg hk]
      ring
  · intro f
    funext k
    by_cases hk : k = 0
    · simp [KdVPlan.invD, KdVPlan.P, hk]
    · simp only [KdVPlan.invD, KdVPlan.dx, KdVPlan.P, if_neg hk]
      rw [inv_mul_cancel_left₀]
      exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)

theorem yui_aux_0028 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g h : KdVPlan.Path), KdVPlan.timeInt a b (fun t => KdVPlan.J t (KdVPlan.B t (f t) (g t)) (h t)) = KdVPlan.tri a b f g h" := by
  intro a b f g h
  have he : ∀ t : ℝ, KdVPlan.S t (KdVPlan.invD (KdVPlan.B t (f t) (g t))) = KdVPlan.P (KdVPlan.mul (KdVPlan.S t (f t)) (KdVPlan.S t (g t))) := by
    intro t
    unfold KdVPlan.B
    rw [(yui_aux_0027 T gamma R h_T016 h_T013).2.1, (yui_aux_0027 T gamma R h_T016 h_T013).2.2, (yui_aux_0027 T gamma R h_T016 h_T013).1]

  unfold KdVPlan.tri KdVPlan.J
  simp_rw [he]

theorem yui_aux_0029 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (f g : KdVPlan.Coeff) (k : ℤ), KdVPlan.MemH 0 f → KdVPlan.MemH 0 g → Summable (fun j : ℤ => ‖f j‖*‖g (k-j)‖)" := by
  intro f g k hf hg
  have hfs : Summable (fun j : ℤ => ‖f j‖^2) := by simpa [KdVPlan.MemH, KdVPlan.weight] using hf
  have hgs : Summable (fun j : ℤ => ‖g j‖^2) := by simpa [KdVPlan.MemH, KdVPlan.weight] using hg
  have hgs' : Summable (fun j : ℤ => ‖g (k-j)‖^2) := by
    exact ((Equiv.subLeft k).summable_iff.mpr hgs).congr (fun j => by simp only [Function.comp_apply, Equiv.subLeft_apply])
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ ((hfs.add hgs').div_const 2)
  intro j
  nlinarith [sq_nonneg (‖f j‖-‖g (k-j)‖)]

theorem yui_aux_0030 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "(∀ (t : ℝ) (f : KdVPlan.Coeff), KdVPlan.J t 0 f = 0 ∧ KdVPlan.J t f 0 = 0) ∧ (∀ (n : ℕ) (s : ℝ) (f : KdVPlan.Coeff), KdVPlan.MemH s (KdVPlan.cutoff (n : ℝ) f))" := by
  constructor
  · intro t f
    constructor <;> funext k <;> simp [KdVPlan.J, KdVPlan.S, KdVPlan.invD, KdVPlan.P, KdVPlan.mul]
  · intro n s f
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(n : ℤ)) (n : ℤ))
    intro k hk
    have hb : ¬ |(k : ℝ)| ≤ (n : ℝ) := by
      intro h
      have hr := abs_le.mp h
      have h1 : -(n : ℤ) ≤ k := by exact_mod_cast hr.1
      have h2 : k ≤ (n : ℤ) := by exact_mod_cast hr.2
      exact hk (Finset.mem_Icc.mpr ⟨h1,h2⟩)
    simp [KdVPlan.cutoff, hb]

theorem yui_aux_0031 (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ (a b : ℝ) (f g : KdVPlan.Coeff), a ≤ b → KdVPlan.MemH 2 f → KdVPlan.MemH 2 g → KdVPlan.ZeroMean f → KdVPlan.ZeroMean g → (∀ k : ℤ, IntervalIntegrable (fun t => KdVPlan.B t f g k) MeasureTheory.volume a b) ∧ KdVPlan.stage a b f g = KdVPlan.scale (1/6) (KdVPlan.J b f g-KdVPlan.J a f g)" := by
  intro a b f g hab hf hg hzf hzg
  let C := KdVPlan.hn 2 f+KdVPlan.hn 2 g
  have hC : 0 ≤ C := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfbd : ∀ j : ℤ, ‖f j‖ ≤ C/(1+(j : ℝ)^2) := by
    intro j
    exact ((yui_aux_0004 T gamma R h_T016 h_T013 f j).2 hf).trans (div_le_div_of_nonneg_right (by dsimp [C, KdVPlan.hn]; linarith [Real.sqrt_nonneg (∑' k, KdVPlan.weight 2 k*‖g k‖^2)]) (by positivity))
  have hgbd : ∀ j : ℤ, ‖g j‖ ≤ C/(1+(j : ℝ)^2) := by
    intro j
    exact ((yui_aux_0004 T gamma R h_T016 h_T013 g j).2 hg).trans (div_le_div_of_nonneg_right (by dsimp [C, KdVPlan.hn]; linarith [Real.sqrt_nonneg (∑' k, KdVPlan.weight 2 k*‖f k‖^2)]) (by positivity))
  have H := yui_aux_0019 T gamma R h_T016 h_T013 a b (fun _ => f) (fun _ => g) C C hC hC (fun _ => continuousOn_const) (fun _ => continuousOn_const) (fun _ _ => hfbd) (fun _ _ j => (hgbd j).trans (div_le_self hC (by nlinarith [sq_nonneg (j : ℝ)])))
  have hd := yui_aux_0020 T gamma R h_T016 h_T013 a b (fun _ => f) (fun _ => g) 0 0 C hC (by
    intro u hu t ht j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hfbd j
    · exact hgbd j
    · simpa only [Pi.zero_apply, norm_zero] using (div_nonneg hC (by positivity : 0 ≤ 1+(j : ℝ)^2))
    · simpa only [Pi.zero_apply, norm_zero] using (div_nonneg hC (by positivity : 0 ≤ 1+(j : ℝ)^2))) (fun t ht j => ⟨hasDerivAt_const t _, hasDerivAt_const t _⟩) (fun _ _ => ⟨hzf,hzg⟩)
  have hi : ∀ k : ℤ, IntervalIntegrable (fun t => KdVPlan.B t f g k) MeasureTheory.volume a b := fun k => (H k).1.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  refine ⟨hi, ?_⟩
  funext k
  have hder : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun r => KdVPlan.J r f g k) (3*KdVPlan.B t f g k) t := by
    intro t ht
    simpa only [Pi.zero_apply, (yui_aux_0030 T gamma R h_T016 h_T013).1 t g |>.1, (yui_aux_0030 T gamma R h_T016 h_T013).1 t f |>.2, add_zero] using hd t ht k
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (H k).2.1 hder ((hi k).const_mul 3)
  rw [intervalIntegral.integral_const_mul] at he
  change (1/2 : ℂ)*(∫ t in a..b, KdVPlan.B t f g k) = (1/6 : ℂ)*(KdVPlan.J b f g k-KdVPlan.J a f g k)
  linear_combination (1/6 : ℂ)*he

theorem checked (T : ℝ) (gamma : ℝ) (R : ℝ) (h_T016 : KdVPlan.BasicBilinearBounds) (h_T013 : KdVPlan.SobolevInfrastructure) : yui_aux_type% "∀ f : KdVPlan.Coeff, (∀ (N : ℝ) (j : ℤ), ‖KdVPlan.cutoff N f j‖ ≤ ‖f j‖) ∧ (∀ (j : ℤ), ∀ᶠ n : ℕ in Filter.atTop, KdVPlan.cutoff (n : ℝ) f j = f j) ∧ (KdVPlan.ZeroMean f → ∀ N : ℝ, KdVPlan.ZeroMean (KdVPlan.cutoff N f))" := by
  intro f
  refine ⟨?_, ?_, ?_⟩
  · intro N j
    unfold KdVPlan.cutoff
    split_ifs <;> simp
  · intro j
    filter_upwards [Filter.eventually_ge_atTop j.natAbs] with n hn
    apply if_pos
    have hr : |(j : ℝ)| = (j.natAbs : ℝ) := by norm_cast; exact Int.natCast_natAbs j |>.symm
    rw [hr]
    exact_mod_cast hn
  · intro hf N
    change (if |((0 : ℤ) : ℝ)| ≤ N then f 0 else 0) = 0
    rw [hf]
    split_ifs <;> rfl
#check @checked
#print axioms checked
end YuiAuxiliary
