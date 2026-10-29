import Mathlib

noncomputable section
namespace LR

def localRing (p : ℕ) : Subring ℚ := Subring.closure {q | ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ) / d}
abbrev R (p : ℕ) := ↥(localRing p)
noncomputable instance rRat (p : ℕ) : Algebra (R p) ℚ := (localRing p).subtype.toAlgebra
noncomputable instance rComplex (p : ℕ) : Algebra (R p) ℂ := ((algebraMap ℚ ℂ).comp (localRing p).subtype).toAlgebra
variable {V : Type} [AddCommGroup V] [Module ℂ V]
noncomputable instance rModule (p : ℕ) : Module (R p) V := Module.compHom V (algebraMap (R p) ℂ)
noncomputable instance rTower (p : ℕ) : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V

def vec (y : Module.End ℂ V) (v : V) (i : ℕ) : V := ((i.factorial : ℂ)⁻¹) • (y ^ i) v
def divided (x : Module.End ℂ V) (r : ℕ) : Module.End ℂ V := ((r.factorial : ℂ)⁻¹) • x ^ r
def MR (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) V := Submodule.span (R p) (M : Set V)
def embed (p : ℕ) (M : Submodule ℤ V) (m : M) : MR p M := ⟨m, Submodule.subset_span m.property⟩
def J (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) : Submodule (R p) ℂ := (MR p M).comap ((LinearMap.toSpanSingleton ℂ V (vec y v i)).restrictScalars (R p))
def unit {F W : Type} [Field F] [AddCommGroup W] [Module F W] (l : ℕ) (b : Module.Basis (Fin (l+1)) F W) (i j : Fin (l+1)) : Module.End F W := (b.coord j).smulRight (b i)
abbrev VK (K : Type) [Field K] (M : Submodule ℤ V) := TensorProduct ℤ K M
structure Lift (M : Submodule ℤ V) (f : Module.End ℂ V) where
  map : Module.End ℤ M
  agrees : ∀ m : M, (map m : V) = f m
structure Actions (M : Submodule ℤ V) (x y h : Module.End ℂ V) where
  lx : Lift M x
  ly : Lift M y
  lh : Lift M h
  dX : ∀ r : ℕ, Lift M (divided x r)
  dY : ∀ r : ℕ, Lift M (divided y r)
def induced (K : Type) [Field K] (M : Submodule ℤ V) (f : Module.End ℤ M) : Module.End K (VK K M) := f.baseChange K
def inv {F W : Type} [Field F] [AddCommGroup W] [Module F W] (W' : Submodule F W) (f : Module.End F W) : Prop := ∀ w ∈ W', f w ∈ W'
def pMR (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) (MR p M) := LinearMap.range ((p : R p) • (LinearMap.id : Module.End (R p) (MR p M)))
abbrev QMR (p : ℕ) (M : Submodule ℤ V) := (MR p M) ⧸ pMR p M

def Strings (l : ℕ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  (∀ t : ℕ, h ((y^t) v) = ((l : ℂ)-2*(t : ℂ)) • (y^t) v) ∧
  (∀ t : ℕ, 1 ≤ t → x ((y^t) v) = ((t : ℂ)*((l : ℂ)-(t : ℂ)+1)) • (y^(t-1)) v) ∧
  (∀ i : ℕ, i ≤ l → vec y v i ≠ 0)
def CBasis (l : ℕ) (y : Module.End ℂ V) (v : V) : Prop :=
  (∃ b : Module.Basis (Fin (l+1)) ℂ V, ∀ i, b i = vec y v i.val) ∧ (∀ t : ℕ, l < t → (y^t) v = 0)
def BasicMatrices (l : ℕ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  x (vec y v 0) = 0 ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ l → x (vec y v i) = ((l-i+1 : ℕ) : ℂ) • vec y v (i-1)) ∧
  (∀ i : ℕ, i < l → y (vec y v i) = ((i+1 : ℕ) : ℂ) • vec y v (i+1)) ∧
  y (vec y v l) = 0 ∧
  (∀ i : ℕ, i ≤ l → h (vec y v i) = ((l : ℂ)-2*(i : ℂ)) • vec y v i)
def DivMatrices (l : ℕ) (x y : Module.End ℂ V) (v : V) : Prop :=
  (∀ r i : ℕ, i ≤ l → divided x r (vec y v i) = if r ≤ i then ((Nat.choose (l-i+r) r : ℕ) : ℂ) • vec y v (i-r) else 0) ∧
  (∀ r i : ℕ, i ≤ l → divided y r (vec y v i) = if i+r ≤ l then ((Nat.choose (i+r) r : ℕ) : ℂ) • vec y v (i+r) else 0)
def N1 (l : ℕ) (x y h : Module.End ℂ V) (v : V) : Prop := Strings l x y h v ∧ CBasis l y v ∧ BasicMatrices l x y h v ∧ DivMatrices l x y v

def LocalBasis (p l : ℕ) (M : Submodule ℤ V) : Prop :=
  (∃ f : TensorProduct ℤ (R p) M ≃ₗ[R p] MR p M, ∀ r m, (f (TensorProduct.tmul ℤ r m) : V) = r • (m : V)) ∧
  Nonempty (Module.Basis (Fin (l+1)) (R p) (MR p M)) ∧ Submodule.span ℂ (MR p M : Set V) = ⊤
def LocalStable (p : ℕ) (M : Submodule ℤ V) (x y : Module.End ℂ V) : Prop :=
  ∀ r : ℕ, (∀ w ∈ MR p M, divided x r w ∈ MR p M) ∧ (∀ w ∈ MR p M, divided y r w ∈ MR p M)
def PartialUnits (l : ℕ) (x y : Module.End ℂ V) (b : Module.Basis (Fin (l+1)) ℂ V) : Prop :=
  divided y l * divided x l = unit l b ⟨l, Nat.lt_succ_self l⟩ ⟨l, Nat.lt_succ_self l⟩ ∧
  (∀ i, divided x (l-i.val) * unit l b ⟨l, Nat.lt_succ_self l⟩ ⟨l, Nat.lt_succ_self l⟩ = unit l b i ⟨l, Nat.lt_succ_self l⟩) ∧
  (∀ j, unit l b ⟨l, Nat.lt_succ_self l⟩ ⟨l, Nat.lt_succ_self l⟩ * divided y (l-j.val) = ((Nat.choose l j.val : ℕ) : ℂ) • unit l b ⟨l, Nat.lt_succ_self l⟩ j)
def AllUnits (p l : ℕ) (M : Submodule ℤ V) (x y : Module.End ℂ V) (b : Module.Basis (Fin (l+1)) ℂ V) : Prop :=
  (∀ j : Fin (l+1), IsUnit ((Nat.choose l j.val : ℕ) : R p)) ∧
  (∀ i j, unit l b i j = (((Nat.choose l j.val : ℕ) : ℂ)⁻¹) • (divided x (l-i.val) * (divided y l * divided x l) * divided y (l-j.val))) ∧
  (∀ i j w, w ∈ MR p M → unit l b i j w ∈ MR p M)
def N2 (p l : ℕ) (M : Submodule ℤ V) (x y : Module.End ℂ V) (v : V) : Prop :=
  LocalBasis p l M ∧ LocalStable p M x y ∧ ∀ b : Module.Basis (Fin (l+1)) ℂ V, (∀ i, b i = vec y v i.val) → PartialUnits l x y b ∧ AllUnits p l M x y b

def Decomposition (p l : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  (∀ i : Fin (l+1), J p M y v i.val = J p M y v 0) ∧
  J p M y v 0 ≠ ⊥ ∧ Module.Finite (R p) (J p M y v 0) ∧
  (∀ w : V, w ∈ MR p M ↔ ∃ c : Fin (l+1) → ℂ, (∀ i, c i ∈ J p M y v 0) ∧ w = ∑ i, c i • vec y v i.val) ∧
  (∀ c : Fin (l+1) → ℂ, (∑ i, c i • vec y v i.val) = 0 → ∀ i, c i = 0)
def TensorLine (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ mu : TensorProduct (R p) ℚ (J p M y v 0) →ₗ[ℚ] ℂ,
    (∀ q c, mu (TensorProduct.tmul (R p) q c) = q • (c : ℂ)) ∧ Function.Injective mu ∧
    LinearMap.range mu = Submodule.span ℚ (J p M y v 0 : Set ℂ) ∧ Module.Finite ℚ (TensorProduct (R p) ℚ (J p M y v 0))
def RankOne (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop := Module.finrank ℚ (TensorProduct (R p) ℚ (J p M y v 0)) = 1
def Generators (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ a : ℂ, a ∈ J p M y v 0 ∧ a ≠ 0 ∧ ∃ k : ℕ, 0 < k ∧ ∃ q : Fin k → ℚ,
    (∀ j, q j ≠ 0) ∧ J p M y v 0 = Submodule.span (R p) (Set.range (fun j => (q j : ℂ) * a))
def Valuations (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ a : ℂ, a ∈ J p M y v 0 ∧ a ≠ 0 ∧ ∃ k : ℕ, 0 < k ∧ ∃ (nu : Fin k → ℤ) (u : Fin k → (R p)ˣ),
    J p M y v 0 = Submodule.span (R p) (Set.range (fun j => (((p : ℚ) ^ nu j * ((u j : R p) : ℚ) : ℚ) : ℂ) * a))
def Generates (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop := b ∈ J p M y v 0 ∧ b ≠ 0 ∧ J p M y v 0 = Submodule.span (R p) {b}
def ScaledBasis (p l : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop :=
  ∃ d : Module.Basis (Fin (l+1)) (R p) (MR p M), ∀ i, (d i : V) = b • vec y v i.val
def N3 (p l : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  Decomposition p l M y v ∧ TensorLine p M y v ∧ RankOne p M y v ∧ (∃ b, Generates p M y v b) ∧
  (∀ b, Generates p M y v b → ScaledBasis p l M y v b)

variable (K : Type) [Field K]
def ResidueMaps (p : ℕ) (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) : Prop :=
  letI : CharP K p := c
  (∀ (q : R p) (a d : ℤ), ¬ (p : ℤ) ∣ d → (q : ℚ) = (a : ℚ)/d → rho q = (a : K)/(d : K)) ∧
  RingHom.ker rho = Ideal.span {(p : R p)} ∧
  Function.Surjective sigma ∧ RingHom.ker sigma = Ideal.span {(p : R p)} ∧
  (∃ eta : (R p ⧸ Ideal.span {(p : R p)}) ≃+* ZMod p, ∀ r, eta (Ideal.Quotient.mk _ r) = sigma r) ∧
  rho = (ZMod.castHom (dvd_refl p) K).comp sigma
structure TransportData (p : ℕ) (M : Submodule ℤ V) [Algebra (R p) K] [Algebra (ZMod p) K] [Module (ZMod p) (QMR p M)] where
  first : VK K M ≃ₗ[K] TensorProduct (R p) K (MR p M)
  first_pure : ∀ k m, first (TensorProduct.tmul ℤ k m) = TensorProduct.tmul (R p) k (embed p M m)
  second : TensorProduct (R p) K (MR p M) ≃ₗ[K] TensorProduct (ZMod p) K (QMR p M)
  second_pure : ∀ k m, second (TensorProduct.tmul (R p) k m) = TensorProduct.tmul (ZMod p) k ((pMR p M).mkQ m)
  first_intertwines : ∀ (a : Module.End ℤ M) (aR : Module.End (R p) (MR p M)), (∀ m, aR (embed p M m) = embed p M (a m)) → ∀ z, first (induced K M a z) = aR.baseChange K (first z)
  second_intertwines : ∀ (aR : Module.End (R p) (MR p M)) (aQ : Module.End (ZMod p) (QMR p M)), (∀ m, (pMR p M).mkQ (aR m) = aQ ((pMR p M).mkQ m)) → ∀ z, second (aR.baseChange K z) = aQ.baseChange K (second z)
def Transport (p : ℕ) (M : Submodule ℤ V) (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) : Prop :=
  letI : CharP K p := c
  letI : Algebra (R p) K := rho.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  ∃ s : Module (ZMod p) (QMR p M),
    letI : Module (ZMod p) (QMR p M) := s
    (∀ (r : R p) (z : QMR p M), r • z = sigma r • z) ∧ Nonempty (TransportData K p M)
def ReducedMatrices (l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (A : Actions M x y h) (beta : Module.Basis (Fin (l+1)) K (VK K M)) : Prop :=
  induced K M A.lx.map (beta 0) = 0 ∧
  (∀ i j : Fin (l+1), j.val+1 = i.val → induced K M A.lx.map (beta i) = ((l-i.val+1 : ℕ) : K) • beta j) ∧
  (∀ i j : Fin (l+1), j.val = i.val+1 → induced K M A.ly.map (beta i) = ((i.val+1 : ℕ) : K) • beta j) ∧
  induced K M A.ly.map (beta ⟨l, Nat.lt_succ_self l⟩) = 0 ∧
  (∀ i, induced K M A.lh.map (beta i) = ((l : K)-2*(i.val : K)) • beta i)
def Reduction (p l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (v : V) (A : Actions M x y h) (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) : Prop :=
  letI : CharP K p := c
  letI : Algebra (R p) K := rho.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  ∃ s : Module (ZMod p) (QMR p M),
    letI : Module (ZMod p) (QMR p M) := s
    (∀ (r : R p) (z : QMR p M), r • z = sigma r • z) ∧
    ∃ t : TransportData K p M, ∀ b : ℂ, Generates p M y v b →
      ∀ d : Module.Basis (Fin (l+1)) (R p) (MR p M), (∀ i, (d i : V) = b • vec y v i.val) →
      ∃ (beta : Module.Basis (Fin (l+1)) K (VK K M)) (gamma : Module.Basis (Fin (l+1)) (ZMod p) (QMR p M)),
        (∀ i, t.first (beta i) = TensorProduct.tmul (R p) 1 (d i)) ∧
        (∀ i, gamma i = (pMR p M).mkQ (d i)) ∧
        (∀ i, t.second (t.first (beta i)) = TensorProduct.tmul (ZMod p) 1 (gamma i)) ∧
        ReducedMatrices K l M x y h A beta ∧
        (∀ (ec : Module.Basis (Fin (l+1)) ℂ V), (∀ i, ec i = vec y v i.val) →
          ∀ i j (aR : Module.End (R p) (MR p M)), (∀ m, (aR m : V) = unit l ec i j m) →
          ∀ z, t.first (unit l beta i j z) = aR.baseChange K (t.first z))
def ModularUnits (l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (A : Actions M x y h) : Prop :=
  (∀ r : ℕ, r ≤ l → (r.factorial : K) ≠ 0 ∧ induced K M (A.dX r).map = (r.factorial : K)⁻¹ • (induced K M A.lx.map)^r ∧ induced K M (A.dY r).map = (r.factorial : K)⁻¹ • (induced K M A.ly.map)^r) ∧
  (∀ j : Fin (l+1), ((Nat.choose l j.val : ℕ) : K) ≠ 0) ∧
  ∀ beta : Module.Basis (Fin (l+1)) K (VK K M), ReducedMatrices K l M x y h A beta →
    (∀ i j, unit l beta i j = (((Nat.choose l j.val : ℕ) : K)⁻¹) • (induced K M (A.dX (l-i.val)).map * (induced K M (A.dY l).map * induced K M (A.dX l).map) * induced K M (A.dY (l-j.val)).map)) ∧
    (∀ W : Submodule K (VK K M), inv W (induced K M A.lx.map) → inv W (induced K M A.ly.map) → ∀ i j, inv W (unit l beta i j))
def N4 (p l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (v : V) : Prop :=
  ∃ (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) (A : Actions M x y h),
    ResidueMaps K p c rho sigma ∧ Reduction K p l M x y h v A c rho sigma ∧ ModularUnits K l M x y h A
end LR

namespace Translation
set_option autoImplicit false

theorem T001 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l+1 ∧ h*x-x*h = (2 : ℂ) • x ∧ h*y-y*h = (-2 : ℂ) • y ∧ x*y-y*x = h ∧ (∀ W : Submodule ℂ V, LR.inv W x → LR.inv W y → LR.inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (l : ℂ) • v) :
    LR.Strings l x y h v := by
  have hy : ∀ w : V, h (y w) = y (h w) - (2 : ℂ) • y w := by
    intro w
    have hw := congrArg (fun f : Module.End ℂ V => f w) h_H002.2.2.2.1
    have hw' : h (y w) - y (h w) = -(2 : ℂ) • y w := hw
    rw [neg_smul] at hw'
    exact (sub_eq_iff_eq_add.mp hw').trans (by abel)
  have xy : ∀ w : V, x (y w) = y (x w) + h w := by
    intro w
    have hw : x (y w) - y (x w) = h w := congrArg (fun f : Module.End ℂ V => f w) h_H002.2.2.2.2.1
    exact (sub_eq_iff_eq_add.mp hw).trans (by abel)
  have yp : ∀ t : ℕ, (y ^ (t+1)) v = y ((y^t) v) := by
    intro t
    rw [pow_succ', Module.End.mul_apply]
  have hh : ∀ t : ℕ, h ((y^t) v) = ((l : ℂ)-2*(t : ℂ)) • (y^t) v := by
    intro t
    induction t with
    | zero => simpa using h_H003.2.2
    | succ t ih =>
      rw [yp, hy, ih, map_smul, ← sub_smul]
      congr 1
      push_cast
      ring
  have xx : ∀ t : ℕ, x ((y^(t+1)) v) = (((t : ℂ)+1)*((l : ℂ)-(t : ℂ))) • (y^t) v := by
    intro t
    induction t with
    | zero => simpa [yp, xy, h_H003.2.1] using h_H003.2.2
    | succ t ih =>
      rw [yp (t+1), xy, ih, map_smul, hh, ← yp, ← add_smul]
      congr 1
      push_cast
      ring
  refine ⟨hh, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [xx s]
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    congr 2
    ring
  · have nz : ∀ i : ℕ, i ≤ l → (y^i) v ≠ 0 := by
      intro i
      induction i with
      | zero => intro _; simpa using h_H003.1
      | succ i ih =>
        intro hi hz
        have hp : ((i : ℂ)+1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero i)
        have hl : (l : ℂ) - (i : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show l ≠ i by omega))
        have hn := smul_ne_zero (mul_ne_zero hp hl) (ih (by omega))
        have he := xx i
        rw [hz, map_zero] at he
        exact hn he.symm
    intro i hi
    unfold LR.vec
    exact smul_ne_zero (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i)) (nz i hi)

theorem T002 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l+1 ∧ h*x-x*h = (2 : ℂ) • x ∧ h*y-y*h = (-2 : ℂ) • y ∧ x*y-y*x = h ∧ (∀ W : Submodule ℂ V, LR.inv W x → LR.inv W y → LR.inv W h → W = ⊥ ∨ W = ⊤)) (h_T001 : LR.Strings l x y h v) :
    LR.CBasis l y v := by
  classical
  let e : Fin (l+1) → V := fun i => LR.vec y v i.val
  let μ : Fin (l+1) → ℂ := fun i => (l : ℂ) - 2 * (i.val : ℂ)
  have he : ∀ i, h (e i) = μ i • e i := by
    intro i
    dsimp [e, LR.vec, μ]
    rw [map_smul, h_T001.1]
    exact smul_comm _ _ _
  have hinj : Function.Injective μ := by
    intro i j hij
    apply Fin.ext
    have hc : (i.val : ℂ) = (j.val : ℂ) := by
      dsimp [μ] at hij
      linear_combination -hij / 2
    exact_mod_cast hc
  have hli : LinearIndependent ℂ e := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    let P : Polynomial ℂ := ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (μ k))
    have evalP (a : ℂ) : P.eval a = ∏ k ∈ Finset.univ.erase j, (a - μ k) := by
      simp [P, Polynomial.eval_prod]
    have hj : P.eval (μ j) ≠ 0 := by
      rw [evalP]
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact sub_ne_zero.mpr (fun hh => (Finset.mem_erase.mp hk).1 (hinj hh).symm)
    have hk : ∀ k, k ≠ j → P.eval (μ k) = 0 := by
      intro k hkj
      rw [evalP]
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
      simp
    have hp := congrArg (fun w : V => (Polynomial.aeval h P) w) hc
    simp only [map_sum, map_smul, map_zero] at hp
    have ha : ∀ k, (Polynomial.aeval h P) (e k) = P.eval (μ k) • e k :=
      fun k => Module.End.aeval_apply_of_mem_apply_eq_smul (he k)
    change (∑ k, c k • (Polynomial.aeval h P) (e k)) = 0 at hp
    simp_rw [ha] at hp
    have hs : (∑ k, c k • P.eval (μ k) • e k) = c j • P.eval (μ j) • e j := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [hk k hkj, zero_smul, smul_zero]
      · simp
    rw [hs, smul_smul] at hp
    have hn : e j ≠ 0 := h_T001.2.2 j.val (Nat.le_of_lt_succ j.isLt)
    exact (mul_eq_zero.mp ((smul_eq_zero.mp hp).resolve_right hn)).resolve_right hj
  letI : FiniteDimensional ℂ V := h_H002.1
  have hcard : Fintype.card (Fin (l+1)) = Module.finrank ℂ V := by
    rw [Fintype.card_fin, h_H002.2.1]
  let b : Module.Basis (Fin (l+1)) ℂ V := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ i, b i = LR.vec y v i.val := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i
  refine ⟨⟨b, hb⟩, ?_⟩
  have he' : ∀ i, h (b i) = ((l : ℂ) - 2 * (i.val : ℂ)) • b i := by
    intro i
    rw [hb i]
    dsimp [LR.vec]
    rw [map_smul, h_T001.1]
    exact smul_comm _ _ _
  have hzero : (y ^ (l+1)) v = 0 := by
    let w := (y ^ (l+1)) v
    have hw : h w = ((l : ℂ) - 2 * ((l+1 : ℕ) : ℂ)) • w := h_T001.1 (l+1)
    have hc : ∀ i, b.repr w i = 0 := by
      intro i
      have hexp := b.sum_repr w
      have hh := congrArg (fun z : V => h z) hexp
      simp only [map_sum, map_smul] at hh
      simp_rw [he'] at hh
      have hi := congrArg (b.coord i) hh
      simp only [map_sum, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul] at hi
      change (∑ k, b.repr w k * (((l : ℂ) - 2 * (k.val : ℂ)) * (Finsupp.single k (1 : ℂ)) i)) = b.repr (h w) i at hi
      simp only [Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hi
      rw [hw] at hi
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hi
      have hn : ((l : ℂ) - 2 * (i.val : ℂ)) - ((l : ℂ) - 2 * ((l+1 : ℕ) : ℂ)) ≠ 0 := by
        intro hz
        have hc : (i.val : ℂ) = ((l+1 : ℕ) : ℂ) := by linear_combination -hz / 2
        have hn : i.val = l+1 := by exact_mod_cast hc
        omega
      apply (mul_eq_zero.mp ?_).resolve_left hn
      linear_combination hi
    apply b.repr.injective
    ext i
    simpa using hc i
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show l+1 ≤ t by omega)
  rw [add_comm (l+1) k, pow_add, Module.End.mul_apply, hzero, map_zero]

theorem T003 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : LR.Strings l x y h v) (h_T002 : LR.CBasis l y v) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (l : ℂ) • v) :
    LR.N1 l x y h v := by
  have hb : LR.BasicMatrices l x y h v := by
    have hx0 : x (LR.vec y v 0) = 0 := by simpa [LR.vec] using h_H003.2.1
    refine ⟨hx0, ?_, ?_, ?_, ?_⟩
    · intro i hi hil
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hc : ((l - (j+1) + 1 : ℕ) : ℂ) = (l : ℂ) - (j+1 : ℕ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hil]; push_cast; ring
      simp only [LR.vec, map_smul, h_T001.2.1 (j+1) (by omega), Nat.succ_sub_one]
      rw [smul_smul, smul_smul, hc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      congr 1
      field_simp
    · intro i hi
      have hp : (y ^ (i+1)) v = y ((y^i) v) := by rw [pow_succ']; rfl
      simp only [LR.vec, map_smul, ← hp, smul_smul]
      congr 1
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero i)
      field_simp
    · have hp : y ((y^l) v) = (y^(l+1)) v := by rw [pow_succ']; rfl
      simp only [LR.vec, map_smul, hp, h_T002.2 (l+1) (by omega), smul_zero]
    · intro i hi
      simp only [LR.vec, map_smul, h_T001.1 i, smul_smul]
      congr 1
      ring
  refine ⟨h_T001, h_T002, hb, ?_⟩
  have comb (n r : ℕ) : r.factorial * Nat.choose n r * (n+1) = (r+1).factorial * Nat.choose (n+1) (r+1) := by
    calc
      _ = r.factorial * ((n+1) * Nat.choose n r) := by ring
      _ = _ := by rw [Nat.add_one_mul_choose_eq, Nat.factorial_succ]; ring
  have px : ∀ r i : ℕ, i ≤ l → (x^r) (LR.vec y v i) = if r ≤ i then ((r.factorial * Nat.choose (l-i+r) r : ℕ) : ℂ) • LR.vec y v (i-r) else 0 := by
    intro r
    induction r with
    | zero => intro i hi; simp
    | succ r ih =>
      intro i hi
      have hp : (x^(r+1)) (LR.vec y v i) = x ((x^r) (LR.vec y v i)) := by rw [pow_succ']; rfl
      rw [hp, ih i hi]
      by_cases hr : r ≤ i
      · rw [if_pos hr, map_smul]
        by_cases hs : r+1 ≤ i
        · rw [if_pos hs, hb.2.1 (i-r) (by omega) (by omega), smul_smul]
          have he : l - (i-r) + 1 = l-i+r+1 := by omega
          have he' : i-r-1 = i-(r+1) := by omega
          rw [he, he']
          congr 1
          norm_cast
          exact comb (l-i+r) r
        · have he : i-r = 0 := by omega
          rw [if_neg hs, he, hb.1, smul_zero]
      · have hs : ¬ r+1 ≤ i := by omega
        rw [if_neg hr, map_zero, if_neg hs]
  have py : ∀ r i : ℕ, i ≤ l → (y^r) (LR.vec y v i) = if i+r ≤ l then ((r.factorial * Nat.choose (i+r) r : ℕ) : ℂ) • LR.vec y v (i+r) else 0 := by
    intro r
    induction r with
    | zero => intro i hi; simp [hi]
    | succ r ih =>
      intro i hi
      have hp : (y^(r+1)) (LR.vec y v i) = y ((y^r) (LR.vec y v i)) := by rw [pow_succ']; rfl
      rw [hp, ih i hi]
      by_cases hr : i+r ≤ l
      · rw [if_pos hr, map_smul]
        by_cases hs : i+(r+1) ≤ l
        · rw [if_pos hs, hb.2.2.1 (i+r) (by omega), smul_smul]
          rw [show i+r+1 = i+(r+1) by omega]
          congr 1
          norm_cast
          simpa [Nat.add_assoc] using comb (i+r) r
        · have he : i+r = l := by omega
          rw [if_neg hs, he, hb.2.2.2.1, smul_zero]
      · have hs : ¬ i+(r+1) ≤ l := by omega
        rw [if_neg hr, map_zero, if_neg hs]
  have hf (n : ℕ) : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  constructor
  · intro r i hi
    simp only [LR.divided, LinearMap.smul_apply, px r i hi]
    split_ifs <;> simp [smul_smul, Nat.cast_mul, hf]
  · intro r i hi
    simp only [LR.divided, LinearMap.smul_apply, py r i hi]
    split_ifs <;> simp [smul_smul, Nat.cast_mul, hf]

theorem T004 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_H004 : (∃ (ι : Type) (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℂ V), ∀ i, (b i : V) = c i) ∧ (∀ r : ℕ, (∀ m : M, LR.divided x r m ∈ M) ∧ (∀ m : M, LR.divided y r m ∈ M))) (h_T003 : LR.N1 l x y h v) :
    (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d) ∧ LR.LocalBasis p l M := by
  classical
  constructor
  · have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp h_H001.1
    let S : Subring ℚ :=
      { carrier := {q | ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ) / d}
        zero_mem' := ⟨0, 1, hp.not_dvd_one, by simp⟩
        one_mem' := ⟨1, 1, hp.not_dvd_one, by simp⟩
        add_mem' := by
          rintro q r ⟨a, d, hd, rfl⟩ ⟨b, e, he, rfl⟩
          have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (fun h : d = 0 => hd (h ▸ dvd_zero _))
          have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast (fun h : e = 0 => he (h ▸ dvd_zero _))
          refine ⟨a*e+b*d, d*e, fun h => (hp.dvd_mul.mp h).elim hd he, ?_⟩
          push_cast
          field_simp
        neg_mem' := by
          rintro q ⟨a, d, hd, rfl⟩
          exact ⟨-a, d, hd, by simp [neg_div]⟩
        mul_mem' := by
          rintro q r ⟨a, d, hd, rfl⟩ ⟨b, e, he, rfl⟩
          exact ⟨a*b, d*e, fun h => (hp.dvd_mul.mp h).elim hd he, by push_cast; ring⟩ }
    intro q
    constructor
    · intro hq
      exact (Subring.closure_le.mpr (show {q | ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d} ⊆ S from fun _ h => h)) hq
    · intro hq
      exact Subring.subset_closure hq
  · rcases h_H004.1 with ⟨ι, b₀, c₀, hc₀⟩
    rcases h_T003.2.1.1 with ⟨ec, hec⟩
    let e : ι ≃ Fin (l+1) := c₀.indexEquiv ec
    let b := b₀.reindex e
    let c := c₀.reindex e
    have hc : ∀ i, (b i : V) = c i := by
      intro i
      simpa [b, c] using hc₀ (e.symm i)
    have hspan : Submodule.span (LR.R p) (Set.range c) = LR.MR p M := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        rw [← hc]
        exact Submodule.subset_span (b i).property
      · apply Submodule.span_le.mpr
        intro m hm
        let m' : M := ⟨m, hm⟩
        have hs : (∑ i, (b.repr m' i) • (b i : V)) = (m' : V) := by
          exact_mod_cast b.sum_repr m'
        change (m' : V) ∈ Submodule.span (LR.R p) (Set.range c)
        rw [← hs]
        apply Submodule.sum_mem
        intro i hi
        apply Submodule.smul_of_tower_mem
        rw [hc]
        exact Submodule.subset_span (Set.mem_range_self i)
    letI : Module.IsTorsionFree (LR.R p) ℂ := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      change Function.Injective ((algebraMap ℚ ℂ).comp (LR.localRing p).subtype)
      exact (algebraMap ℚ ℂ).injective.comp Subtype.val_injective)
    let d : Module.Basis (Fin (l+1)) (LR.R p) (LR.MR p M) :=
      (c.restrictScalars (LR.R p)).map (LinearEquiv.ofEq _ _ hspan)
    have hd : ∀ i, (d i : V) = (b i : V) := by
      intro i
      simpa [d] using (hc i).symm
    let f : TensorProduct ℤ (LR.R p) M ≃ₗ[LR.R p] LR.MR p M :=
      (b.baseChange (LR.R p)).equiv d (Equiv.refl _)
    have hf : ∀ i, f (TensorProduct.tmul ℤ (1 : LR.R p) (b i)) = d i := by
      intro i
      change (b.baseChange (LR.R p)).equiv d (Equiv.refl _) _ = _
      rw [← Module.Basis.baseChange_apply]
      exact Module.Basis.equiv_apply (b.baseChange (LR.R p)) i d (Equiv.refl _)
    let F : M →ₗ[ℤ] V :=
      ((LR.MR p M).subtype.restrictScalars ℤ).comp
        ((f.toLinearMap.restrictScalars ℤ).comp (TensorProduct.mk ℤ (LR.R p) M 1))
    have hF : F = M.subtype := by
      apply b.ext
      intro i
      change (f (TensorProduct.tmul ℤ 1 (b i)) : V) = (b i : V)
      rw [hf, hd]
    refine ⟨⟨f, ?_⟩, ⟨d⟩, ?_⟩
    · intro r m
      have h1 : (f (TensorProduct.tmul ℤ 1 m) : V) = (m : V) :=
        LinearMap.congr_fun hF m
      have ht : TensorProduct.tmul ℤ r m = r • TensorProduct.tmul ℤ (1 : LR.R p) m := by
        simp [TensorProduct.smul_tmul']
      rw [ht, map_smul, Submodule.coe_smul, h1]
    · apply top_unique
      rw [← c.span_eq]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      rw [← hc]
      exact Submodule.subset_span (b i).property

theorem T005 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H004 : (∃ (ι : Type) (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℂ V), ∀ i, (b i : V) = c i) ∧ (∀ r : ℕ, (∀ m : M, LR.divided x r m ∈ M) ∧ (∀ m : M, LR.divided y r m ∈ M))) (h_T004 : (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d) ∧ LR.LocalBasis p l M) :
    LR.LocalStable p M x y := by
  have extend (f : Module.End ℂ V) (hf : ∀ m : M, f m ∈ M) :
      ∀ w ∈ LR.MR p M, f w ∈ LR.MR p M := by
    have hle : LR.MR p M ≤ (LR.MR p M).comap (f.restrictScalars (LR.R p)) := by
      apply Submodule.span_le.mpr
      intro m hm
      change f m ∈ LR.MR p M
      exact Submodule.subset_span (hf ⟨m, hm⟩)
    intro w hw
    exact hle hw
  intro r
  exact ⟨extend (LR.divided x r) (h_H004.2 r).1,
    extend (LR.divided y r) (h_H004.2 r).2⟩

theorem T006 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T003 : LR.N1 l x y h v) :
    ∀ b : Module.Basis (Fin (l+1)) ℂ V, (∀ i, b i = LR.vec y v i.val) → LR.PartialUnits l x y b := by
  classical
  intro b hb
  have hx := h_T003.2.2.2.1
  have hy := h_T003.2.2.2.2
  let top : Fin (l+1) := ⟨l, Nat.lt_succ_self l⟩
  have hu (i j k : Fin (l+1)) : LR.unit l b i j (b k) = if k = j then b i else 0 := by
    simp [LR.unit, Module.Basis.coord_apply, Finsupp.single_apply, ite_smul]
  have hxt (i : Fin (l+1)) : LR.divided x (l-i.val) (LR.vec y v l) = LR.vec y v i.val := by
    rw [hx (l-i.val) l (le_refl l)]
    simp [Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)]
  have hyl : LR.divided y l (LR.vec y v 0) = LR.vec y v l := by
    simpa using hy l 0 (Nat.zero_le l)
  have hq (k : ℕ) (hk : k ≤ l) :
      (LR.divided y l * LR.divided x l) (LR.vec y v k) = if k = l then LR.vec y v l else 0 := by
    rw [Module.End.mul_apply, hx l k hk]
    by_cases he : k = l
    · subst k
      simp [hyl]
    · have hn : ¬ l ≤ k := by omega
      simp [hn, he]
  have hqeq : LR.divided y l * LR.divided x l = LR.unit l b top top := by
    apply b.ext
    intro k
    rw [hu, hb k, hq k.val (Nat.le_of_lt_succ k.isLt)]
    by_cases he : k = top
    · subst k
      simp [top, hb]
    · have hn : k.val ≠ l := by
        intro hh
        apply he
        apply Fin.ext
        exact hh
      simp [he, hn]
  change (LR.divided y l * LR.divided x l = LR.unit l b top top) ∧ _
  refine ⟨hqeq, ?_, ?_⟩
  · intro i
    apply b.ext
    intro k
    rw [Module.End.mul_apply, hu, hu]
    by_cases he : k = ⟨l, Nat.lt_succ_self l⟩
    · simp only [he, if_true]
      rw [hb, hxt, hb]
    · simp [he]
  · intro j
    rw [← hqeq]
    apply b.ext
    intro k
    rw [Module.End.mul_apply, LinearMap.smul_apply, hu, hb k, hy (l-j.val) k.val (Nat.le_of_lt_succ k.isLt)]
    by_cases hkj : k.val ≤ j.val
    · have hr : k.val + (l-j.val) ≤ l := by omega
      rw [if_pos hr, map_smul, hq _ hr]
      by_cases he : k = j
      · subst k
        have hj : j.val + (l-j.val) = l := by omega
        simp [hj, Nat.choose_symm (Nat.le_of_lt_succ j.isLt), hb]
      · have hn : k.val + (l-j.val) ≠ l := by
          intro hh
          apply he
          apply Fin.ext
          omega
        simp [hn, he]
    · have hr : ¬ k.val + (l-j.val) ≤ l := by omega
      have he : k ≠ j := by intro hh; subst k; exact hkj (le_refl _)
      simp [hr, he]

theorem T007 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T003 : LR.N1 l x y h v) (h_T004 : (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d) ∧ LR.LocalBasis p l M) (h_T005 : LR.LocalStable p M x y) (h_T006 : ∀ b : Module.Basis (Fin (l+1)) ℂ V, (∀ i, b i = LR.vec y v i.val) → LR.PartialUnits l x y b) :
    LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d) := by
  classical
  have arithmetic : ∀ j : Fin (l+1), IsUnit ((Nat.choose l j.val : ℕ) : LR.R p) ∧ ∃ a : LR.R p, algebraMap (LR.R p) ℂ a = ((Nat.choose l j.val : ℂ)⁻¹) := by
    intro j
    have hj : j.val ≤ l := Nat.le_of_lt_succ j.isLt
    have hn : ¬ p ∣ Nat.choose l j.val := by
      intro hd
      have hf : p ∣ l.factorial := by
        rw [← Nat.choose_mul_factorial_mul_factorial hj]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
      exact (not_le_of_gt h_H001.2.2) ((h_H001.1.dvd_factorial).mp hf)
    have hz : ¬ (p : ℤ) ∣ (Nat.choose l j.val : ℤ) := by exact_mod_cast hn
    have hne : (Nat.choose l j.val : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj).ne'
    let a : LR.R p := ⟨(Nat.choose l j.val : ℚ)⁻¹, (h_T004.1 _).2 ⟨1, (Nat.choose l j.val : ℤ), hz, by simp⟩⟩
    have ha : (Nat.choose l j.val : LR.R p) * a = 1 := by
      apply Subtype.ext
      change (Nat.choose l j.val : ℚ) * (Nat.choose l j.val : ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ hne
    constructor
    · exact isUnit_iff_exists_inv.mpr ⟨a, ha⟩
    · refine ⟨a, ?_⟩
      change (((Nat.choose l j.val : ℚ)⁻¹ : ℚ) : ℂ) = _
      push_cast
      rfl
  refine ⟨⟨h_T004.2, h_T005, ?_⟩, h_T004.1⟩
  intro b hb
  have hp := h_T006 b hb
  refine ⟨hp, ?_⟩
  have umul : ∀ i j k : Fin (l+1), LR.unit l b i k * LR.unit l b k j = LR.unit l b i j := by
    intro i j k
    ext w
    simp [LR.unit, Module.End.mul_apply]
  have formula : ∀ i j, LR.unit l b i j = (((Nat.choose l j.val : ℕ) : ℂ)⁻¹) • (LR.divided x (l-i.val) * (LR.divided y l * LR.divided x l) * LR.divided y (l-j.val)) := by
    intro i j
    have hc : (Nat.choose l j.val : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)).ne'
    have he : LR.divided x (l-i.val) * (LR.divided y l * LR.divided x l) * LR.divided y (l-j.val) = (Nat.choose l j.val : ℂ) • LR.unit l b i j := by
      rw [hp.1, mul_assoc, hp.2.2 j, mul_smul_comm]
      congr 1
      rw [← umul ⟨l, Nat.lt_succ_self l⟩ j ⟨l, Nat.lt_succ_self l⟩, ← mul_assoc, hp.2.1 i, umul]
    rw [he, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨fun j => (arithmetic j).1, formula, ?_⟩
  intro i j w hw
  rcases (arithmetic j).2 with ⟨a, ha⟩
  have hs : (LR.divided x (l-i.val) * (LR.divided y l * LR.divided x l) * LR.divided y (l-j.val)) w ∈ LR.MR p M := by
    exact (h_T005 _).1 _ ((h_T005 l).2 _ ((h_T005 l).1 _ ((h_T005 _).2 w hw)))
  rw [formula]
  change ((Nat.choose l j.val : ℂ)⁻¹) • ((LR.divided x (l-i.val) * (LR.divided y l * LR.divided x l) * LR.divided y (l-j.val)) w) ∈ LR.MR p M
  rw [← ha, IsScalarTower.algebraMap_smul]
  exact (LR.MR p M).smul_mem a hs

theorem T008 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T003 : LR.N1 l x y h v) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) :
    LR.Decomposition p l M y v := by
  classical
  rcases h_T003.2.1.1 with ⟨b, hb⟩
  have hs := (h_T007.1.2.2 b hb).2.2.2
  have hJ (i : Fin (l+1)) (c : ℂ) : c ∈ LR.J p M y v i.val ↔ c • b i ∈ LR.MR p M := by
    simp [LR.J, hb]
  have hu (i j : Fin (l+1)) (c : ℂ) : LR.unit l b i j (c • b j) = c • b i := by
    simp [LR.unit, Module.Basis.coord_apply]
  have hle (i j : Fin (l+1)) : LR.J p M y v j.val ≤ LR.J p M y v i.val := by
    intro c hc
    apply (hJ i c).2
    rw [← hu i j c]
    exact hs i j _ ((hJ j c).1 hc)
  have heq (i : Fin (l+1)) : LR.J p M y v i.val = LR.J p M y v 0 :=
    le_antisymm (hle 0 i) (hle i 0)
  have hc (w : V) (hw : w ∈ LR.MR p M) (i : Fin (l+1)) : b.repr w i ∈ LR.J p M y v 0 := by
    rw [← heq i]
    apply (hJ i _).2
    simpa [LR.unit, Module.Basis.coord_apply] using hs i i w hw
  have hd (w : V) : w ∈ LR.MR p M ↔ ∃ c : Fin (l+1) → ℂ, (∀ i, c i ∈ LR.J p M y v 0) ∧ w = ∑ i, c i • LR.vec y v i.val := by
    constructor
    · intro hw
      exact ⟨fun i => b.repr w i, hc w hw, by simpa only [← hb] using (b.sum_repr w).symm⟩
    · rintro ⟨c, hc', rfl⟩
      apply Submodule.sum_mem
      intro i hi
      rw [← hb i]
      apply (hJ i (c i)).1
      rw [heq i]
      exact hc' i
  have hind (c : Fin (l+1) → ℂ) (hz : (∑ i, c i • LR.vec y v i.val) = 0) : ∀ i, c i = 0 := by
    intro i
    have hh := congrArg (b.coord i) hz
    simpa [← hb, map_sum, Module.Basis.coord_apply, Finsupp.single_apply] using hh
  have hn : LR.J p M y v 0 ≠ ⊥ := by
    intro hz
    have hm (w : V) (hw : w ∈ LR.MR p M) : w = 0 := by
      obtain ⟨c, hcm, rfl⟩ := (hd w).1 hw
      have hcz (i) : c i = 0 := by simpa [hz] using hcm i
      simp [hcz]
    have hspan : Submodule.span ℂ (LR.MR p M : Set V) ≤ ⊥ := by
      apply Submodule.span_le.2
      intro w hw
      exact hm w hw
    rw [h_T007.1.1.2.2] at hspan
    have hz' : b (0 : Fin (l+1)) = 0 := hspan (Submodule.mem_top)
    have hh := congrArg (b.coord (0 : Fin (l+1))) hz'
    simpa [Module.Basis.coord_apply] using hh
  rcases h_T007.1.1.2.1 with ⟨d⟩
  letI : Module.Finite (LR.R p) (LR.MR p M) := Module.Finite.of_basis d
  let f : LR.MR p M →ₗ[LR.R p] ℂ := ((b.coord 0).restrictScalars (LR.R p)).comp (LR.MR p M).subtype
  let g : LR.MR p M →ₗ[LR.R p] LR.J p M y v 0 := f.codRestrict _ (fun w => hc w w.property 0)
  have hg : Function.Surjective g := by
    intro c
    refine ⟨⟨(c : ℂ) • b 0, (hJ 0 c).1 c.property⟩, ?_⟩
    apply Subtype.ext
    simp [g, f, Module.Basis.coord_apply]
  have hf : Module.Finite (LR.R p) (LR.J p M y v 0) := Module.Finite.of_surjective g hg
  exact ⟨heq, hn, hf, hd, hind⟩

theorem T009 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) (h_T008 : LR.Decomposition p l M y v) :
    LR.TensorLine p M y v := by
  letI : IsLocalization (nonZeroDivisors (LR.R p)) ℚ := by
    apply (isLocalization_iff _ _).2
    constructor
    · intro s
      apply isUnit_iff_ne_zero.mpr
      change (s.val : ℚ) ≠ 0
      exact fun hs => (nonZeroDivisors.ne_zero s.property) (Subtype.ext hs)
    constructor
    · intro q
      refine ⟨((q.num : LR.R p), ⟨(q.den : LR.R p), ?_⟩), ?_⟩
      · apply mem_nonZeroDivisors_iff_ne_zero.mpr
        exact_mod_cast q.den_ne_zero
      · change q * (q.den : ℚ) = (q.num : ℚ)
        exact Rat.mul_den_eq_num q
    · intro a b hab
      exact ⟨1, by simpa using (Subtype.ext hab : a = b)⟩
  letI : IsScalarTower (LR.R p) ℚ ℂ := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let C := LR.J p M y v 0
  let f : ℚ →ₗ[ℚ] (C →ₗ[LR.R p] ℂ) :=
    { toFun := fun q => q • C.subtype
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [mul_smul] }
  let mu := TensorProduct.AlgebraTensorModule.lift f
  have hpure : ∀ q c, mu (TensorProduct.tmul (LR.R p) q c) = q • (c : ℂ) := fun q c => rfl
  refine ⟨mu, hpure, ?_, ?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    obtain ⟨⟨c, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors (LR.R p)) (TensorProduct.mk (LR.R p) ℚ C 1) z
    have hc : (c : ℂ) = 0 := by
      have hh := congrArg mu hs
      simpa [LinearMap.map_smul_of_tower, hz, hpure] using hh.symm
    have hc0 : c = 0 := Subtype.ext hc
    have hs0 : (s.val : ℚ) ≠ 0 := fun he => (nonZeroDivisors.ne_zero s.property) (Subtype.ext he)
    have htransport : s • z = (s.val : ℚ) • z := by
      change s.val • z = (algebraMap (LR.R p) ℚ s.val) • z
      exact (IsScalarTower.algebraMap_smul ℚ s.val z).symm
    have hh : (s.val : ℚ) • z = 0 := by
      rw [← htransport]
      simpa only [hc0, map_zero] using hs
    exact (smul_eq_zero.mp hh).resolve_left hs0
  · apply le_antisymm
    · rintro a ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simpa using (Submodule.zero_mem (Submodule.span ℚ (C : Set ℂ)))
      | tmul q c =>
        rw [hpure]
        exact Submodule.smul_mem _ q (Submodule.subset_span c.property)
      | add a b ha hb => simpa using Submodule.add_mem (Submodule.span ℚ (C : Set ℂ)) ha hb
    · apply Submodule.span_le.mpr
      intro c hc
      exact ⟨TensorProduct.tmul (LR.R p) 1 (⟨c, hc⟩ : C), by simp [hpure]⟩
  · letI : Module.Finite (LR.R p) C := h_T008.2.2.1
    infer_instance

theorem T010 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) (h_T008 : LR.Decomposition p l M y v) (h_T009 : LR.TensorLine p M y v) :
    Nonempty (TensorProduct (LR.R p) ℚ (LR.MR p M) ≃ₗ[ℚ] (Fin (l+1) → TensorProduct (LR.R p) ℚ (LR.J p M y v 0))) ∧ LR.RankOne p M y v := by
  classical
  let ins (i : Fin (l+1)) : LR.J p M y v 0 →ₗ[LR.R p] V :=
    ((LinearMap.toSpanSingleton ℂ V (LR.vec y v i.val)).restrictScalars (LR.R p)).comp (LR.J p M y v 0).subtype
  let s : (Fin (l+1) → LR.J p M y v 0) →ₗ[LR.R p] V :=
    ∑ i, (ins i).comp (LinearMap.proj i)
  have hs (c : Fin (l+1) → LR.J p M y v 0) : s c = ∑ i, (c i : ℂ) • LR.vec y v i.val := by
    simp [s, ins]
  have hmem (c : Fin (l+1) → LR.J p M y v 0) : s c ∈ LR.MR p M := by
    rw [hs]
    apply Submodule.sum_mem
    intro i hi
    have hc : (c i : ℂ) ∈ LR.J p M y v i.val := by
      rw [h_T008.1 i]
      exact (c i).property
    exact hc
  let f := s.codRestrict (LR.MR p M) hmem
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have hz : ∑ i, (c i : ℂ) • LR.vec y v i.val = 0 := by
      rw [← hs]
      exact congrArg Subtype.val hc
    have hz' := h_T008.2.2.2.2 (fun i => (c i : ℂ)) hz
    funext i
    apply Subtype.ext
    exact hz' i
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨c, hc, hw⟩ := (h_T008.2.2.2.1 w).mp w.property
    refine ⟨fun i => ⟨c i, hc i⟩, ?_⟩
    apply Subtype.ext
    change s _ = (w : V)
    rw [hs]
    exact hw.symm
  let e := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm
  let E : TensorProduct (LR.R p) ℚ (LR.MR p M) ≃ₗ[ℚ] (Fin (l+1) → TensorProduct (LR.R p) ℚ (LR.J p M y v 0)) :=
    (e.baseChange (LR.R p) ℚ _ _).trans (TensorProduct.piRight (LR.R p) ℚ ℚ (fun _ : Fin (l+1) => LR.J p M y v 0))
  refine ⟨⟨E⟩, ?_⟩
  obtain ⟨b⟩ := h_T007.1.1.2.1
  obtain ⟨mu, hmu, hmuinj, hrange, hfinite⟩ := h_T009
  letI := hfinite
  letI : Module.Free ℚ (TensorProduct (LR.R p) ℚ (LR.J p M y v 0)) := Module.Free.of_divisionRing ℚ _
  have hd1 : Module.finrank ℚ (TensorProduct (LR.R p) ℚ (LR.MR p M)) = l+1 := by
    simpa using Module.finrank_eq_card_basis (b.baseChange ℚ)
  have hd2 : Module.finrank ℚ (Fin (l+1) → TensorProduct (LR.R p) ℚ (LR.J p M y v 0)) = (l+1) * Module.finrank ℚ (TensorProduct (LR.R p) ℚ (LR.J p M y v 0)) := by
    have hd := Module.finrank_pi_fintype ℚ (M := fun _ : Fin (l+1) => TensorProduct (LR.R p) ℚ (LR.J p M y v 0))
    simpa using hd
  have heq := E.finrank_eq
  rw [hd1, hd2] at heq
  unfold LR.RankOne
  nlinarith

theorem T011 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T008 : LR.Decomposition p l M y v) (h_T009 : LR.TensorLine p M y v) (h_T010 : Nonempty (TensorProduct (LR.R p) ℚ (LR.MR p M) ≃ₗ[ℚ] (Fin (l+1) → TensorProduct (LR.R p) ℚ (LR.J p M y v 0))) ∧ LR.RankOne p M y v) :
    LR.Generators p M y v := by
  classical
  have hn : LR.J p M y v 0 ≠ ⊥ := h_T008.2.1
  have hf : Module.Finite (LR.R p) (LR.J p M y v 0) := h_T008.2.2.1
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp hf)
  have hDfin : (S \ {0}).Finite := hSfin.sdiff
  obtain ⟨k, g, hg⟩ := hDfin.fin_embedding
  have hgmem (j : Fin k) : g j ∈ S \ {0} := by
    rw [← hg]
    exact Set.mem_range_self j
  have hg0 (j : Fin k) : g j ≠ 0 := by simpa using (hgmem j).2
  have hgJ (j : Fin k) : g j ∈ LR.J p M y v 0 := by
    rw [← hS]
    exact Submodule.subset_span (hgmem j).1
  have hspan : Submodule.span (LR.R p) (Set.range g) = LR.J p M y v 0 := by
    rw [hg, Submodule.span_sdiff_singleton_zero, hS]
  have hk : 0 < k := by
    by_contra hh
    have hk0 : k = 0 := by omega
    have he : Set.range g = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨j, rfl⟩
      have := j.isLt
      omega
    exact hn (by simpa [he] using hspan.symm)
  rcases h_T009 with ⟨mu, hmu, hminj, hmrange, hmfin⟩
  letI := hmfin
  let ta : TensorProduct (LR.R p) ℚ (LR.J p M y v 0) := TensorProduct.tmul (LR.R p) 1 ⟨a, ha⟩
  have hta : mu ta = a := by simpa [ta] using hmu 1 ⟨a, ha⟩
  have hta0 : ta ≠ 0 := by
    intro hz
    apply ha0
    rw [← hta, hz, map_zero]
  have hr : Module.finrank ℚ (TensorProduct (LR.R p) ℚ (LR.J p M y v 0)) = 1 := h_T010.2
  have hex (j : Fin k) : ∃ q : ℚ, g j = (q : ℂ) * a := by
    obtain ⟨q, hq⟩ := (finrank_eq_one_iff_of_nonzero' ta hta0).mp hr (TensorProduct.tmul (LR.R p) 1 (⟨g j, hgJ j⟩ : LR.J p M y v 0))
    have heq : q • a = g j := by
      have hh := congrArg mu hq
      simpa only [map_smul, hta, hmu, one_smul] using hh
    exact ⟨q, by simpa [Algebra.smul_def] using heq.symm⟩
  choose q hq using hex
  refine ⟨a, ha, ha0, k, hk, q, ?_, ?_⟩
  · intro j hzero
    apply hg0 j
    simp [hq j, hzero]
  · have heq : (fun j => (q j : ℂ) * a) = (fun j => g j) := by
      funext j
      exact (hq j).symm
    rw [heq]
    exact hspan.symm

theorem T012 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) (h_T011 : LR.Generators p M y v) :
    LR.Valuations p M y v := by
  classical
  have factorRat : ∀ q : ℚ, q ≠ 0 → ∃ (n : ℤ) (u : (LR.R p)ˣ), q = (p : ℚ)^n * ((u : LR.R p) : ℚ) := by
    intro q hq
    have factor : ∀ z : ℤ, z ≠ 0 → ∃ (e : ℕ) (b : ℤ), ¬ (p : ℤ) ∣ b ∧ z = (p : ℤ)^e * b := by
      intro z hz
      have hf : FiniteMultiplicity (p : ℤ) z := Int.finiteMultiplicity_iff.mpr ⟨by simpa using h_H001.1.ne_one, hz⟩
      obtain ⟨b, hb, hnb⟩ := hf.exists_eq_pow_mul_and_not_dvd
      exact ⟨_, b, hnb, hb⟩
    obtain ⟨e, b, hb, he⟩ := factor q.num (Rat.num_ne_zero.mpr hq)
    obtain ⟨f, d, hd, hf⟩ := factor (q.den : ℤ) (by exact_mod_cast q.den_ne_zero)
    have hb0 : b ≠ 0 := by intro h; apply hb; simp [h]
    have hd0 : d ≠ 0 := by intro h; apply hd; simp [h]
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    let r : LR.R p := ⟨(b : ℚ) / d, (h_T007.2 _).mpr ⟨b, d, hd, rfl⟩⟩
    let s : LR.R p := ⟨(d : ℚ) / b, (h_T007.2 _).mpr ⟨d, b, hb, rfl⟩⟩
    have hrs : r * s = 1 := by
      apply Subtype.ext
      change (b : ℚ) / d * ((d : ℚ) / b) = 1
      field_simp
    have hsr : s * r = 1 := by rw [mul_comm]; exact hrs
    let u : (LR.R p)ˣ := ⟨r, s, hrs, hsr⟩
    refine ⟨(e : ℤ) - f, u, ?_⟩
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
    have heQ : (q.num : ℚ) = (p : ℚ)^e * b := by exact_mod_cast he
    have hfQ : (q.den : ℚ) = (p : ℚ)^f * d := by exact_mod_cast hf
    change q = (p : ℚ)^((e : ℤ) - f) * ((b : ℚ) / d)
    rw [zpow_sub₀ hpQ, zpow_natCast, zpow_natCast, ← Rat.num_div_den q, heQ, hfQ]
    ring
  rcases h_T011 with ⟨a, ha, ha0, k, hk, q, hq, hspan⟩
  choose nu u hu using fun j => factorRat (q j) (hq j)
  refine ⟨a, ha, ha0, k, hk, nu, u, ?_⟩
  have hfun : (fun j => (q j : ℂ) * a) = (fun j => (((p : ℚ)^nu j * ((u j : LR.R p) : ℚ) : ℚ) : ℂ) * a) := by
    funext j
    exact congrArg (fun t : ℚ => (t : ℂ) * a) (hu j)
  rw [← hfun]
  exact hspan

theorem T013 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T003 : LR.N1 l x y h v) (h_T008 : LR.Decomposition p l M y v) (h_T009 : LR.TensorLine p M y v) (h_T010 : Nonempty (TensorProduct (LR.R p) ℚ (LR.MR p M) ≃ₗ[ℚ] (Fin (l+1) → TensorProduct (LR.R p) ℚ (LR.J p M y v 0))) ∧ LR.RankOne p M y v) (h_T012 : LR.Valuations p M y v) :
    LR.N3 p l M y v := by
  classical
  refine ⟨h_T008, h_T009, h_T010.2, ?_, ?_⟩
  · rcases h_T012 with ⟨a, ha, ha0, k, hk, nu, u, hJ⟩
    let j₀ : Fin k := ⟨0, hk⟩
    obtain ⟨s, -, hs⟩ := Finset.exists_min_image Finset.univ nu ⟨j₀, Finset.mem_univ _⟩
    have hs' (j : Fin k) : nu s ≤ nu j := hs j (Finset.mem_univ _)
    let φ : LR.R p →+* ℂ := algebraMap (LR.R p) ℂ
    have hφ (r : LR.R p) : φ r = ((r : ℚ) : ℂ) := rfl
    have hp : (p : ℂ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
    let b : ℂ := (p : ℂ) ^ nu s * a
    have hb0 : b ≠ 0 := mul_ne_zero (zpow_ne_zero _ hp) ha0
    let g : Fin k → ℂ := fun j => (((p : ℚ) ^ nu j * ((u j : LR.R p) : ℚ) : ℚ) : ℂ) * a
    have hg (j : Fin k) : g j = (p : ℂ) ^ nu j * φ (u j) * a := by
      simp [g, hφ, Rat.cast_mul, Rat.cast_zpow]
    let r : Fin k → LR.R p := fun j => (p : LR.R p) ^ (nu j - nu s).toNat * (u j : LR.R p)
    have hrel (j : Fin k) : g j = r j • b := by
      have he : ((nu j - nu s).toNat : ℤ) = nu j - nu s := Int.toNat_of_nonneg (sub_nonneg.mpr (hs' j))
      have hr : φ (r j) = (p : ℂ) ^ (nu j - nu s) * φ (u j) := by
        simp only [r, map_mul, map_pow, map_natCast]
        rw [← zpow_natCast, he]
      change g j = φ (r j) * b
      rw [hg, hr]
      dsimp [b]
      have he' : (p : ℂ) ^ (nu j - nu s) * (p : ℂ) ^ nu s = (p : ℂ) ^ nu j := by
        rw [← zpow_add₀ hp]; congr 1; omega
      calc
        _ = ((p : ℂ) ^ (nu j - nu s) * (p : ℂ) ^ nu s) * φ (u j) * a := by rw [he']
        _ = _ := by ring
    have hgs : g s ∈ LR.J p M y v 0 := by
      rw [hJ]
      exact Submodule.subset_span (Set.mem_range_self s)
    have hbs : b = ((↑(u s)⁻¹ : LR.R p)) • g s := by
      rw [hrel]
      have hr : r s = (u s : LR.R p) := by simp [r]
      rw [hr, ← mul_smul]
      simp
    have hb : b ∈ LR.J p M y v 0 := by
      rw [hbs]; exact Submodule.smul_mem _ _ hgs
    refine ⟨b, hb, hb0, le_antisymm ?_ ?_⟩
    · rw [hJ]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨r j, (hrel j).symm⟩
    · exact Submodule.span_le.mpr (by simpa using hb)
  · intro b hb
    rcases hb with ⟨hb, hb0, hJ⟩
    have hm (i : Fin (l+1)) : b • LR.vec y v i.val ∈ LR.MR p M := by
      have hi : b ∈ LR.J p M y v i.val := by rw [h_T008.1 i]; exact hb
      exact hi
    let d : Fin (l+1) → LR.MR p M := fun i => ⟨b • LR.vec y v i.val, hm i⟩
    let φ : LR.R p →+* ℂ := algebraMap (LR.R p) ℂ
    have hφinj : Function.Injective φ := by
      intro r s he
      exact Subtype.ext (Rat.cast_injective (α := ℂ) he)
    have hsum (c : Fin (l+1) → LR.R p) :
        ((∑ i, c i • d i : LR.MR p M) : V) = ∑ i, (φ (c i) * b) • LR.vec y v i.val := by
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, d]
      change (∑ i, φ (c i) • (b • LR.vec y v i.val)) = _
      simp only [mul_smul]
    have hli : LinearIndependent (LR.R p) d := by
      apply Fintype.linearIndependent_iff.mpr
      intro c hc i
      have hv : (∑ j, (φ (c j) * b) • LR.vec y v j.val) = 0 := by
        rw [← hsum, hc]; rfl
      have hz : φ (c i) * b = 0 := h_T008.2.2.2.2 _ hv i
      apply hφinj
      simpa using (mul_eq_zero.mp hz).resolve_right hb0
    have hsp : ⊤ ≤ Submodule.span (LR.R p) (Set.range d) := by
      intro w _
      obtain ⟨c, hc, hw⟩ := (h_T008.2.2.2.1 (w : V)).mp w.property
      have hex (i : Fin (l+1)) : ∃ r : LR.R p, r • b = c i := by
        apply Submodule.mem_span_singleton.mp
        rw [← hJ]; exact hc i
      choose r hr using hex
      have heq : w = ∑ i, r i • d i := by
        apply Subtype.ext
        rw [hsum, hw]
        congr 1
        funext i
        rw [← hr i]
        rfl
      rw [heq]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    refine ⟨Module.Basis.mk hli hsp, ?_⟩
    intro i
    rw [Module.Basis.mk_apply]

theorem T014 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l+1 ∧ h*x-x*h = (2 : ℂ) • x ∧ h*y-y*h = (-2 : ℂ) • y ∧ x*y-y*x = h ∧ (∀ W : Submodule ℂ V, LR.inv W x → LR.inv W y → LR.inv W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (ι : Type) (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℂ V), ∀ i, (b i : V) = c i) ∧ (∀ r : ℕ, (∀ m : M, LR.divided x r m ∈ M) ∧ (∀ m : M, LR.divided y r m ∈ M))) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) :
    ∃ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p) (A : LR.Actions M x y h), LR.ResidueMaps K p c rho sigma := by
  classical
  letI : Fact p.Prime := ⟨h_H001.1⟩
  letI : CharP K p := h_H001.2.1
  let S := (IsUnit.submonoid (ZMod p)).comap (Int.castRingHom (ZMod p))
  have hs (d : ℤ) : d ∈ S ↔ ¬ (p : ℤ) ∣ d := by
    change IsUnit (d : ZMod p) ↔ _
    rw [isUnit_iff_ne_zero, Ne, CharP.intCast_eq_zero_iff (ZMod p) p]
  letI : IsLocalization S (LR.R p) := (isLocalization_iff S (LR.R p)).2 (by
    refine ⟨?_, ?_, ?_⟩
    · intro d
      have hd := (hs d).1 d.property
      have hd0 : (d : ℤ) ≠ 0 := fun h => hd (h ▸ dvd_zero _)
      let z : LR.R p := ⟨(1 : ℚ) / (d : ℤ), (h_T007.2 _).2 ⟨1, d, hd, by simp⟩⟩
      apply isUnit_iff_exists_inv.2
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change (d : ℤ) * ((1 : ℚ) / (d : ℤ)) = 1
      simp [hd0]
    · intro z
      obtain ⟨a, d, hd, hz⟩ := (h_T007.2 _).1 z.property
      refine ⟨⟨a, ⟨d, (hs d).2 hd⟩⟩, ?_⟩
      apply Subtype.ext
      change (z : ℚ) * (d : ℚ) = (a : ℚ)
      rw [hz]
      have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 from fun h => hd (h ▸ dvd_zero _))
      exact div_mul_cancel₀ _ hd0
    · intro a b hab
      refine ⟨1, ?_⟩
      have : a = b := by
        have he : (a : ℚ) = (b : ℚ) := congrArg Subtype.val hab
        exact_mod_cast he
      simp [this])
  have hg (d : S) : IsUnit ((Int.castRingHom (ZMod p)) d) := d.property
  let sigma : LR.R p →+* ZMod p := IsLocalization.lift (M := S) (S := LR.R p) hg
  let rho : LR.R p →+* K := (ZMod.castHom (dvd_refl p) K).comp sigma
  have general : ∀ (F : Type) [Field F] [CharP F p] (f : LR.R p →+* F),
      (∀ (q : LR.R p) (a d : ℤ), ¬ (p : ℤ) ∣ d → (q : ℚ) = (a : ℚ) / d → f q = (a : F) / (d : F)) ∧
      RingHom.ker f = Ideal.span {(p : LR.R p)} := by
    intro F _ _ f
    have formula (q : LR.R p) (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d) (hq : (q : ℚ) = (a : ℚ) / d) : f q = (a : F) / (d : F) := by
      have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 from fun h => hd (h ▸ dvd_zero _))
      have he : q * (d : LR.R p) = (a : LR.R p) := by
        apply Subtype.ext
        change (q : ℚ) * (d : ℚ) = (a : ℚ)
        rw [hq, div_mul_cancel₀ _ hd0]
      have hf : f q * (d : F) = (a : F) := by simpa using congrArg f he
      exact (eq_div_iff ((CharP.intCast_eq_zero_iff F p d).not.mpr hd)).2 hf
    refine ⟨formula, le_antisymm ?_ ?_⟩
    · intro q hq
      obtain ⟨a, d, hd, he⟩ := (h_T007.2 _).1 q.property
      have hf : (a : F) = 0 := by
        have hz : f q = 0 := hq
        rw [formula q a d hd he, div_eq_zero_iff] at hz
        exact hz.resolve_right ((CharP.intCast_eq_zero_iff F p d).not.mpr hd)
      obtain ⟨z, hz⟩ := (CharP.intCast_eq_zero_iff F p a).1 hf
      let t : LR.R p := ⟨(z : ℚ) / d, (h_T007.2 _).2 ⟨z, d, hd, rfl⟩⟩
      apply Ideal.mem_span_singleton.2
      refine ⟨t, ?_⟩
      apply Subtype.ext
      change (q : ℚ) = (p : ℚ) * ((z : ℚ) / d)
      rw [he, hz]
      push_cast
      ring
    · apply Ideal.span_le.2
      intro q hq
      obtain rfl := Set.mem_singleton_iff.1 hq
      change f (p : LR.R p) = 0
      simp
  have hsurj : Function.Surjective sigma := ZMod.ringHom_surjective sigma
  have hker := (general (ZMod p) sigma).2
  let eta : (LR.R p ⧸ Ideal.span {(p : LR.R p)}) ≃+* ZMod p :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have heta (r : LR.R p) : eta (Ideal.Quotient.mk _ r) = sigma r := by
    simp [eta]
  have hx (m : M) : x m ∈ M := by simpa [LR.divided] using (h_H004.2 1).1 m
  have hy (m : M) : y m ∈ M := by simpa [LR.divided] using (h_H004.2 1).2 m
  have hh (m : M) : h m ∈ M := by
    rw [← h_H002.2.2.2.2.1]
    change x (y m) - y (x m) ∈ M
    exact M.sub_mem (hx ⟨y m, hy m⟩) (hy ⟨x m, hx m⟩)
  have lift (f : Module.End ℂ V) (hf : ∀ m : M, f m ∈ M) : LR.Lift M f :=
    { map := (f.restrictScalars ℤ).restrict (fun w hw => hf ⟨w, hw⟩)
      agrees := fun _ => rfl }
  let A : LR.Actions M x y h := ⟨lift x hx, lift y hy, lift h hh,
    (fun r => lift (LR.divided x r) (h_H004.2 r).1),
    (fun r => lift (LR.divided y r) (h_H004.2 r).2)⟩
  refine ⟨h_H001.2.1, rho, sigma, A, ?_⟩
  exact ⟨(general K rho).1, (general K rho).2, hsurj, hker, ⟨eta, heta⟩, rfl⟩

theorem T015 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) :
    ∀ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p), LR.ResidueMaps K p c rho sigma → LR.Transport K p M c rho sigma := by
  classical
  intro c rho sigma hr
  letI := c
  letI := rho.toAlgebra
  letI := ZMod.algebra K p
  let Q := LR.QMR p M
  let phi : LR.R p →+* AddMonoid.End Q := Module.toAddMonoidEnd _ _
  have hp : phi (p : LR.R p) = 0 := by
    ext z
    obtain ⟨m, rfl⟩ := (LR.pMR p M).mkQ_surjective z
    change (LR.pMR p M).mkQ ((p : LR.R p) • m) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact ⟨m, rfl⟩
  have hkphi : RingHom.ker sigma ≤ RingHom.ker phi := by
    rw [hr.2.2.2.1]
    apply Ideal.span_le.2
    intro a ha
    have ha' : a = (p : LR.R p) := Set.mem_singleton_iff.1 ha
    subst a
    exact (RingHom.mem_ker).2 hp
  let psi := sigma.liftOfSurjective hr.2.2.1 ⟨phi, hkphi⟩
  letI s : Module (ZMod p) Q := Module.compHom Q psi
  have ha (r : LR.R p) (z : LR.QMR p M) : r • z = sigma r • z := by
    change phi r z = psi (sigma r) z
    rw [RingHom.liftOfSurjective_comp_apply]
  refine ⟨s, ha, ?_⟩
  obtain ⟨e, he⟩ := h_T007.1.1.1
  let F := (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (LR.R p) K K M).symm.trans (e.baseChange (LR.R p) K _ _)
  have Fpure (k : K) (m : M) : F (TensorProduct.tmul ℤ k m) = TensorProduct.tmul (LR.R p) k (LR.embed p M m) := by
    have hem : e (TensorProduct.tmul ℤ (1 : LR.R p) m) = LR.embed p M m := by
      apply (Subtype.val_injective (p := fun w : V => w ∈ LR.MR p M))
      change (e (TensorProduct.tmul ℤ (1 : LR.R p) m) : V) = (m : V)
      simpa using he 1 m
    simp [F, hem]
  have hrK (r : LR.R p) (k : K) : r • k = sigma r • k := by
    change rho r * k = algebraMap (ZMod p) K (sigma r) * k
    rw [hr.2.2.2.2.2]
    rfl
  letI : TensorProduct.CompatibleSMul (ZMod p) (LR.R p) K (LR.QMR p M) := ⟨by
    intro r k z
    rw [hrK, ha]
    exact TensorProduct.smul_tmul _ _ _⟩
  letI : TensorProduct.CompatibleSMul (LR.R p) (ZMod p) K (LR.QMR p M) := ⟨by
    intro t k z
    obtain ⟨r, rfl⟩ := hr.2.2.1 t
    rw [← hrK, ← ha]
    exact TensorProduct.smul_tmul _ _ _⟩
  have hz : LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor K K (LR.pMR p M).subtype) = ⊥ := by
    rw [LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw, LinearMap.zero_apply, add_zero]
    | tmul k m =>
      obtain ⟨u, hu⟩ := m.property
      change TensorProduct.tmul (LR.R p) k (m : LR.MR p M) = 0
      rw [← hu]
      change TensorProduct.tmul (LR.R p) k ((p : LR.R p) • u) = 0
      rw [← TensorProduct.smul_tmul]
      have hpk : (p : LR.R p) • k = (0 : K) := by simp [Algebra.smul_def]
      rw [hpk, TensorProduct.zero_tmul]
  let q := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := LR.R p) K (LR.R p) K (LR.pMR p M)
  let e0 := (q.trans (Submodule.quotEquivOfEqBot _ hz)).symm
  let e1 := TensorProduct.equivOfCompatibleSMul (ZMod p) (LR.R p) K K (LR.QMR p M)
  let G := e0.trans e1
  have Gpure (k : K) (m : LR.MR p M) : G (TensorProduct.tmul (LR.R p) k m) = TensorProduct.tmul (ZMod p) k ((LR.pMR p M).mkQ m) := by
    have he0 : e0 (TensorProduct.tmul (LR.R p) k m) = TensorProduct.tmul (LR.R p) k ((LR.pMR p M).mkQ m) := by
      apply (LinearEquiv.symm_apply_eq _).2
      rfl
    exact (congrArg (fun z => e1 z) he0).trans rfl
  refine ⟨{ first := F, first_pure := Fpure, second := G, second_pure := Gpure, first_intertwines := ?_, second_intertwines := ?_ }⟩
  · intro a aR haR z
    change F (a.baseChange K z) = aR.baseChange K (F z)
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul k m =>
      rw [LinearMap.baseChange_tmul, Fpure, Fpure, LinearMap.baseChange_tmul, haR]
  · intro aR aQ haQ z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul k m =>
      rw [LinearMap.baseChange_tmul, Gpure, Gpure, LinearMap.baseChange_tmul, haQ]

theorem T016 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T003 : LR.N1 l x y h v) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) (h_T013 : LR.N3 p l M y v) (h_T015 : ∀ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p), LR.ResidueMaps K p c rho sigma → LR.Transport K p M c rho sigma) :
    ∀ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p) (A : LR.Actions M x y h), LR.ResidueMaps K p c rho sigma → LR.Reduction K p l M x y h v A c rho sigma := by
  classical
  intro c rho sigma A hr
  letI : CharP K p := c
  letI : Algebra (LR.R p) K := rho.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Fact p.Prime := ⟨h_H001.1⟩
  obtain ⟨s, hs, ⟨t⟩⟩ := h_T015 c rho sigma hr
  letI : Module (ZMod p) (LR.QMR p M) := s
  refine ⟨s, hs, t, ?_⟩
  intro b hg d hd
  let beta := (d.baseChange K).map t.first.symm
  have hb : ∀ i, t.first (beta i) = TensorProduct.tmul (LR.R p) 1 (d i) := by
    intro i
    simp [beta]
  let g : Fin (l+1) → LR.QMR p M := fun i => (LR.pMR p M).mkQ (d i)
  let delta := (d.baseChange K).map t.second
  have hdelta : ∀ i, delta i = TensorProduct.tmul (ZMod p) (1 : K) (g i) := by
    intro i
    simpa [delta, g] using t.second_pure 1 (d i)
  have ht : ∀ (a : ZMod p) (z : LR.QMR p M), (algebraMap (ZMod p) K a) • TensorProduct.tmul (ZMod p) (1 : K) z = TensorProduct.tmul (ZMod p) (1 : K) (a • z) := by
    intro a z
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    congr 1
  have hli : LinearIndependent (ZMod p) g := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have he : ∑ j, (algebraMap (ZMod p) K (a j)) • delta j = 0 := by
      simp only [hdelta, ht, ← TensorProduct.tmul_sum, ha, TensorProduct.tmul_zero]
    have hz := (Fintype.linearIndependent_iff.mp delta.linearIndependent) _ he i
    exact (algebraMap (ZMod p) K).injective (by simpa using hz)
  have hsp : ⊤ ≤ Submodule.span (ZMod p) (Set.range g) := by
    intro z hz
    obtain ⟨w, rfl⟩ := (LR.pMR p M).mkQ_surjective z
    have he : (LR.pMR p M).mkQ w = ∑ i, sigma (d.repr w i) • g i := by
      conv_lhs => rw [← d.sum_repr w]
      simp only [map_sum, map_smul, hs, g]
    rw [he]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let gamma := Module.Basis.mk hli hsp
  have hgamma : ∀ i, gamma i = (LR.pMR p M).mkQ (d i) := fun i => Module.Basis.mk_apply _ _ i
  refine ⟨beta, gamma, hb, hgamma, ?_, ?_, ?_⟩
  · intro i
    rw [hb, t.second_pure, hgamma]
  · have extend : ∀ (f : Module.End ℂ V) (L : LR.Lift M f), ∃ aR : Module.End (LR.R p) (LR.MR p M), (∀ w, (aR w : V) = f w) ∧ (∀ m, aR (LR.embed p M m) = LR.embed p M (L.map m)) := by
      intro f L
      have hs' : LR.MR p M ≤ (LR.MR p M).comap (f.restrictScalars (LR.R p)) := by
        apply Submodule.span_le.mpr
        intro m hm
        change f m ∈ LR.MR p M
        rw [← L.agrees ⟨m, hm⟩]
        exact Submodule.subset_span (L.map ⟨m, hm⟩).property
      let aR : Module.End (LR.R p) (LR.MR p M) := (f.restrictScalars (LR.R p)).restrict (fun w hw => hs' hw)
      refine ⟨aR, fun w => rfl, ?_⟩
      intro m
      apply Subtype.ext
      exact (L.agrees m).symm
    have tr : ∀ (f : Module.End ℂ V) (L : LR.Lift M f) (i j : Fin (l+1)) (n : ℤ), f (LR.vec y v i.val) = (n : ℂ) • LR.vec y v j.val → LR.induced K M L.map (beta i) = (n : K) • beta j := by
      intro f L i j n hf
      obtain ⟨aR, ha, hm⟩ := extend f L
      have he : aR (d i) = (n : LR.R p) • d j := by
        apply Subtype.ext
        change (aR (d i) : V) = (n : LR.R p) • (d j : V)
        rw [ha, hd, hd, map_smul, hf]
        change b • (n : ℂ) • LR.vec y v j.val = (algebraMap (LR.R p) ℂ (n : LR.R p)) • (b • LR.vec y v j.val)
        simp only [map_intCast]
        exact smul_comm _ _ _
      apply t.first.injective
      rw [t.first_intertwines L.map aR hm, hb, LinearMap.baseChange_tmul, he, map_smul, hb]
      rw [TensorProduct.tmul_smul]
      simp [Algebra.smul_def, TensorProduct.smul_tmul']
    have tr0 : ∀ (f : Module.End ℂ V) (L : LR.Lift M f) (i : Fin (l+1)), f (LR.vec y v i.val) = 0 → LR.induced K M L.map (beta i) = 0 := by
      intro f L i hf
      have he := tr f L i i 0 (by simpa using hf)
      simpa using he
    rcases h_T003.2.2.1 with ⟨hx0, hx, hy, hyl, hh⟩
    refine ⟨tr0 x A.lx 0 hx0, ?_, ?_, tr0 y A.ly ⟨l, Nat.lt_succ_self l⟩ hyl, ?_⟩
    · intro i j hij
      have hij' : i.val - 1 = j.val := by omega
      have he := tr x A.lx i j (Int.ofNat (l-i.val+1)) (by simpa [hij'] using hx i.val (by omega) (by omega))
      simpa using he
    · intro i j hij
      have he := tr y A.ly i j (Int.ofNat (i.val+1)) (by simpa [← hij] using hy i.val (by omega))
      simpa using he
    · intro i
      have he := tr h A.lh i i ((l : ℤ)-2*(i.val : ℤ)) (by simpa using hh i.val (by omega))
      simpa using he
  · intro ec hc i j aR ha
    have he : ∀ k, aR (d k) = if j = k then d i else 0 := by
      intro k
      apply Subtype.ext
      rw [ha, hd, ← hc k, map_smul]
      split_ifs with hk
      · subst k
        simp [LR.unit, hd, ← hc]
      · simp [LR.unit, Module.Basis.coord_apply, Ne.symm hk]
    have hm : t.first.toLinearMap.comp (LR.unit l beta i j) = (aR.baseChange K).comp t.first.toLinearMap := by
      apply beta.ext
      intro k
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hb, LinearMap.baseChange_tmul, he]
      by_cases hk : j = k
      · subst k
        simp [LR.unit, hb]
      · simp [LR.unit, Module.Basis.coord_apply, hk]
    intro z
    exact LinearMap.congr_fun hm z

theorem T017 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T003 : LR.N1 l x y h v) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) (h_T013 : LR.N3 p l M y v) (h_T014 : ∃ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p) (A : LR.Actions M x y h), LR.ResidueMaps K p c rho sigma) (h_T016 : ∀ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p) (A : LR.Actions M x y h), LR.ResidueMaps K p c rho sigma → LR.Reduction K p l M x y h v A c rho sigma) :
    LR.N4 K p l M x y h v ∧ ∃ b : ℂ, LR.Generates p M y v b ∧ LR.ScaledBasis p l M y v b := by
  classical
  rcases h_T014 with ⟨c, rho, sigma, A, hres⟩
  letI : CharP K p := c
  have hred := h_T016 c rho sigma A hres
  have hdiv : ∀ (f : Module.End ℂ V) (a : LR.Lift M f) (r : ℕ) (d : LR.Lift M (LR.divided f r)), (r.factorial : K) ≠ 0 → LR.induced K M d.map = (r.factorial : K)⁻¹ • (LR.induced K M a.map)^r := by
    intro f a r d hn
    have hp : ∀ n (m : M), ((a.map ^ n) m : V) = (f ^ n) m := by
      intro n
      induction n with
      | zero => intro m; rfl
      | succ n ih => intro m; simp only [pow_succ', Module.End.mul_apply, a.agrees, ih]
    have he : (r.factorial : ℤ) • d.map = a.map ^ r := by
      ext m
      change (r.factorial : ℤ) • (d.map m : V) = _
      rw [d.agrees, hp]
      simp [LR.divided, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, Nat.factorial_ne_zero]
    have hb := congrArg (fun f : Module.End ℤ M => f.baseChange K) he
    rw [LinearMap.baseChange_smul, LinearMap.baseChange_pow] at hb
    have hs : (r.factorial : K) • LR.induced K M d.map = (LR.induced K M a.map)^r := by
      simpa only [LR.induced, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul] using hb
    rw [← hs, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hf : ∀ r : ℕ, r ≤ l → (r.factorial : K) ≠ 0 ∧ LR.induced K M (A.dX r).map = (r.factorial : K)⁻¹ • (LR.induced K M A.lx.map)^r ∧ LR.induced K M (A.dY r).map = (r.factorial : K)⁻¹ • (LR.induced K M A.ly.map)^r := by
    intro r hr
    have hn : (r.factorial : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p]
      intro hh
      have := h_H001.1.dvd_factorial.mp hh
      omega
    exact ⟨hn, hdiv x A.lx r (A.dX r) hn, hdiv y A.ly r (A.dY r) hn⟩
  rcases h_T003.2.1.1 with ⟨ec, hec⟩
  have hall := (h_T007.1.2.2 ec hec).2
  have hc : ∀ j : Fin (l+1), ((Nat.choose l j.val : ℕ) : K) ≠ 0 := by
    intro j
    simpa using ((hall.1 j).map rho).ne_zero
  have hbase : ∃ beta : Module.Basis (Fin (l+1)) K (LR.VK K M), LR.ReducedMatrices K l M x y h A beta ∧ ∀ i j, ((Nat.choose l j.val : ℕ) : K) • LR.unit l beta i j = (LR.induced K M (A.dX (l-i.val)).map * (LR.induced K M (A.dY l).map * LR.induced K M (A.dX l).map) * LR.induced K M (A.dY (l-j.val)).map) := by
    letI : Algebra (LR.R p) K := rho.toAlgebra
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    rcases hred with ⟨s, hs, t, ht⟩
    letI : Module (ZMod p) (LR.QMR p M) := s
    rcases h_T013.2.2.2.1 with ⟨a, ha⟩
    rcases h_T013.2.2.2.2 a ha with ⟨d, hd⟩
    rcases ht a ha d hd with ⟨beta, gamma, hbeta, hgamma, htensor, hmat, hu⟩
    have stable := h_T007.1.2.1
    let Dx (r : ℕ) : Module.End (LR.R p) (LR.MR p M) := ((LR.divided x r).restrictScalars (LR.R p)).restrict (stable r).1
    let Dy (r : ℕ) : Module.End (LR.R p) (LR.MR p M) := ((LR.divided y r).restrictScalars (LR.R p)).restrict (stable r).2
    let U (i j : Fin (l+1)) : Module.End (LR.R p) (LR.MR p M) := ((LR.unit l ec i j).restrictScalars (LR.R p)).restrict (hall.2.2 i j)
    have hx (r : ℕ) (z) : t.first (LR.induced K M (A.dX r).map z) = (Dx r).baseChange K (t.first z) := by
      apply t.first_intertwines
      intro m
      apply Subtype.ext
      exact ((A.dX r).agrees m).symm
    have hy (r : ℕ) (z) : t.first (LR.induced K M (A.dY r).map z) = (Dy r).baseChange K (t.first z) := by
      apply t.first_intertwines
      intro m
      apply Subtype.ext
      exact ((A.dY r).agrees m).symm
    refine ⟨beta, hmat, ?_⟩
    intro i j
    have hn : ((Nat.choose l j.val : ℕ) : ℂ) ≠ 0 := by
      have hn' := ((hall.1 j).map (algebraMap (LR.R p) ℂ)).ne_zero
      simpa using hn'
    have hec' : ((Nat.choose l j.val : ℕ) : ℂ) • LR.unit l ec i j = LR.divided x (l-i.val) * (LR.divided y l * LR.divided x l) * LR.divided y (l-j.val) := by
      rw [hall.2.1 i j, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have he : ((Nat.choose l j.val : ℕ) : LR.R p) • U i j = Dx (l-i.val) * (Dy l * Dx l) * Dy (l-j.val) := by
      ext w
      have hw := congrArg (fun f : Module.End ℂ V => f w) hec'
      simpa [U, Dx, Dy, Module.End.mul_apply, Nat.cast_smul_eq_nsmul] using hw
    have hb := congrArg (fun f : Module.End (LR.R p) (LR.MR p M) => f.baseChange K) he
    rw [LinearMap.baseChange_smul, LinearMap.baseChange_mul, LinearMap.baseChange_mul, LinearMap.baseChange_mul] at hb
    have hb' : ((Nat.choose l j.val : ℕ) : K) • (U i j).baseChange K = (Dx (l-i.val)).baseChange K * ((Dy l).baseChange K * (Dx l).baseChange K) * (Dy (l-j.val)).baseChange K := by
      simpa only [Nat.cast_smul_eq_nsmul] using hb
    apply LinearMap.ext
    intro z
    apply t.first.injective
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, hx, hy, hu ec hec i j (U i j) (by intro m; rfl)]
    exact congrArg (fun f : Module.End K (TensorProduct (LR.R p) K (LR.MR p M)) => f (t.first z)) hb'
  rcases hbase with ⟨b₀, hb₀, hbase⟩
  have hformula₀ (i j : Fin (l+1)) : LR.unit l b₀ i j = (((Nat.choose l j.val : ℕ) : K)⁻¹) • (LR.induced K M (A.dX (l-i.val)).map * (LR.induced K M (A.dY l).map * LR.induced K M (A.dX l).map) * LR.induced K M (A.dY (l-j.val)).map) := by
    rw [← hbase i j, smul_smul, inv_mul_cancel₀ (hc j), one_smul]
  have hform : ∀ b : Module.Basis (Fin (l+1)) K (LR.VK K M), LR.ReducedMatrices K l M x y h A b → ∀ i j, LR.unit l b i j = (((Nat.choose l j.val : ℕ) : K)⁻¹) • (LR.induced K M (A.dX (l-i.val)).map * (LR.induced K M (A.dY l).map * LR.induced K M (A.dX l).map) * LR.induced K M (A.dY (l-j.val)).map) := by
    intro b hb
    let e := b₀.equiv b (Equiv.refl _)
    have he (i) : e (b₀ i) = b i := by simp [e]
    have hes (i) : e.symm (b i) = b₀ i := by rw [← he, e.symm_apply_apply]
    let C := e.conjAlgEquiv (R := K)
    have hCx : C (LR.induced K M A.lx.map) = LR.induced K M A.lx.map := by
      apply b.ext
      intro i
      change e (LR.induced K M A.lx.map (e.symm (b i))) = _
      rw [hes]
      by_cases hi : i.val = 0
      · have hi' : i = 0 := Fin.ext hi
        subst i
        rw [hb₀.1, hb.1, map_zero]
      · let j : Fin (l+1) := ⟨i.val-1, by omega⟩
        have hj : j.val+1 = i.val := by dsimp [j]; omega
        rw [hb₀.2.1 i j hj, hb.2.1 i j hj, map_smul, he]
    have hCy : C (LR.induced K M A.ly.map) = LR.induced K M A.ly.map := by
      apply b.ext
      intro i
      change e (LR.induced K M A.ly.map (e.symm (b i))) = _
      rw [hes]
      by_cases hi : i.val = l
      · have hi' : i = ⟨l, Nat.lt_succ_self l⟩ := Fin.ext hi
        subst i
        rw [hb₀.2.2.2.1, hb.2.2.2.1, map_zero]
      · let j : Fin (l+1) := ⟨i.val+1, by omega⟩
        have hj : j.val = i.val+1 := rfl
        rw [hb₀.2.2.1 i j hj, hb.2.2.1 i j hj, map_smul, he]
    have hCu (i j) : C (LR.unit l b₀ i j) = LR.unit l b i j := by
      apply b.ext
      intro k
      change e (LR.unit l b₀ i j (e.symm (b k))) = _
      rw [hes]
      simp [LR.unit, he, Module.Basis.coord_apply]
    have hCdX (r) (hr : r ≤ l) : C (LR.induced K M (A.dX r).map) = LR.induced K M (A.dX r).map := by
      rw [(hf r hr).2.1, map_smul, map_pow, hCx]
    have hCdY (r) (hr : r ≤ l) : C (LR.induced K M (A.dY r).map) = LR.induced K M (A.dY r).map := by
      rw [(hf r hr).2.2, map_smul, map_pow, hCy]
    intro i j
    have hh := congrArg C (hformula₀ i j)
    simp only [map_smul, map_mul] at hh
    rw [hCu, hCdX _ (Nat.sub_le _ _), hCdY l le_rfl, hCdX l le_rfl, hCdY _ (Nat.sub_le _ _)] at hh
    exact hh
  have hmod : LR.ModularUnits K l M x y h A := by
    refine ⟨hf, hc, ?_⟩
    intro b hb
    refine ⟨hform b hb, ?_⟩
    intro W hX hY
    have hp (f : Module.End K (LR.VK K M)) (hi : LR.inv W f) : ∀ n, LR.inv W (f^n) := by
      intro n
      induction n with
      | zero => intro w hw; simpa using hw
      | succ n ih =>
        intro w hw
        simpa only [pow_succ', Module.End.mul_apply] using hi _ (ih w hw)
    have hdX (r) (hr : r ≤ l) : LR.inv W (LR.induced K M (A.dX r).map) := by
      rw [(hf r hr).2.1]
      intro w hw
      exact W.smul_mem _ (hp _ hX r w hw)
    have hdY (r) (hr : r ≤ l) : LR.inv W (LR.induced K M (A.dY r).map) := by
      rw [(hf r hr).2.2]
      intro w hw
      exact W.smul_mem _ (hp _ hY r w hw)
    intro i j w hw
    rw [hform b hb i j]
    exact W.smul_mem _ (hdX _ (Nat.sub_le _ _) _ (hdY l le_rfl _ (hdX l le_rfl _ (hdY _ (Nat.sub_le _ _) w hw))))
  refine ⟨⟨c, rho, sigma, A, hres, hred, hmod⟩, ?_⟩
  rcases h_T013.2.2.2.1 with ⟨a, ha⟩
  exact ⟨a, ha, h_T013.2.2.2.2 a ha⟩

theorem T018 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_T017 : LR.N4 K p l M x y h v ∧ ∃ b : ℂ, LR.Generates p M y v b ∧ LR.ScaledBasis p l M y v b) :
    ∃ (A : LR.Actions M x y h) (beta : Module.Basis (Fin (l+1)) K (LR.VK K M)), Nontrivial (LR.VK K M) ∧ ∀ W : Submodule K (LR.VK K M), LR.inv W (LR.induced K M A.lx.map) → LR.inv W (LR.induced K M A.ly.map) → ∀ i j, LR.inv W (LR.unit l beta i j) := by
  rcases h_T017 with ⟨hN, b, hb, d, hd⟩
  rcases hN with ⟨c, rho, sigma, A, hres, hred, hmod⟩
  letI : CharP K p := c
  letI : Algebra (LR.R p) K := rho.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  rcases hred with ⟨s, hs, t, ht⟩
  letI : Module (ZMod p) (LR.QMR p M) := s
  rcases ht b hb d hd with ⟨beta, gamma, hfirst, hgamma, hsecond, hmat, hunit⟩
  refine ⟨A, beta, ?_, ?_⟩
  · exact nontrivial_of_ne (beta (0 : Fin (l+1))) 0 (beta.ne_zero 0)
  · exact (hmod.2.2 beta hmat).2

theorem T019 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  :
    ∀ (beta : Module.Basis (Fin (l+1)) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), (∀ i j, LR.inv W (LR.unit l beta i j)) → W ≠ ⊥ → W = ⊤ := by
  classical
  intro beta W hunit hW
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hex : ∃ j, beta.coord j w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hw0 ((beta.forall_coord_eq_zero_iff).mp hn)
  obtain ⟨j, hj⟩ := hex
  have hb : ∀ i, beta i ∈ W := by
    intro i
    have hm : beta.coord j w • beta i ∈ W := by
      simpa [LR.unit, LinearMap.smulRight_apply] using hunit i j w hw
    have hi := W.smul_mem (beta.coord j w)⁻¹ hm
    rw [smul_smul, inv_mul_cancel₀ hj, one_smul] at hi
    exact hi
  apply top_unique
  intro z hz
  rw [← beta.sum_repr z]
  exact W.sum_mem (fun i _ => W.smul_mem _ (hb i))

theorem T020 (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l+1 ∧ h*x-x*h = (2 : ℂ) • x ∧ h*y-y*h = (-2 : ℂ) • y ∧ x*y-y*x = h ∧ (∀ W : Submodule ℂ V, LR.inv W x → LR.inv W y → LR.inv W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (ι : Type) (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℂ V), ∀ i, (b i : V) = c i) ∧ (∀ r : ℕ, (∀ m : M, LR.divided x r m ∈ M) ∧ (∀ m : M, LR.divided y r m ∈ M))) (h_T018 : ∃ (A : LR.Actions M x y h) (beta : Module.Basis (Fin (l+1)) K (LR.VK K M)), Nontrivial (LR.VK K M) ∧ ∀ W : Submodule K (LR.VK K M), LR.inv W (LR.induced K M A.lx.map) → LR.inv W (LR.induced K M A.ly.map) → ∀ i j, LR.inv W (LR.unit l beta i j)) (h_T019 : ∀ (beta : Module.Basis (Fin (l+1)) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), (∀ i j, LR.inv W (LR.unit l beta i j)) → W ≠ ⊥ → W = ⊤) :
    ∃ A : LR.Actions M x y h, Nontrivial (LR.VK K M) ∧ ∀ W : Submodule K (LR.VK K M), LR.inv W (LR.induced K M A.lx.map) → LR.inv W (LR.induced K M A.ly.map) → LR.inv W (LR.induced K M A.lh.map) → W = ⊥ ∨ W = ⊤ := by
  classical
  obtain ⟨A, beta, hnontrivial, hunits⟩ := h_T018
  refine ⟨A, hnontrivial, ?_⟩
  intro W hx hy hh
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · exact Or.inr (h_T019 beta W (hunits W hx hy) hW)

set_option Elab.async false in
theorem P (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l+1 ∧ h*x-x*h = (2 : ℂ) • x ∧ h*y-y*h = (-2 : ℂ) • y ∧ x*y-y*x = h ∧ (∀ W : Submodule ℂ V, LR.inv W x → LR.inv W y → LR.inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (l : ℂ) • v) (h_H004 : (∃ (ι : Type) (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℂ V), ∀ i, (b i : V) = c i) ∧ (∀ r : ℕ, (∀ m : M, LR.divided x r m ∈ M) ∧ (∀ m : M, LR.divided y r m ∈ M))) :
    ∃ A : LR.Actions M x y h, Nontrivial (LR.VK K M) ∧ ∀ W : Submodule K (LR.VK K M), LR.inv W (LR.induced K M A.lx.map) → LR.inv W (LR.induced K M A.ly.map) → LR.inv W (LR.induced K M A.lh.map) → W = ⊥ ∨ W = ⊤ := by
  have h_T001 : LR.Strings l x y h v := @T001 p K fieldK l V addV modV x y h v M h_H001 h_H002 h_H003
  have h_T002 : LR.CBasis l y v := @T002 p K fieldK l V addV modV x y h v M h_H002 h_T001
  have h_T003 : LR.N1 l x y h v := @T003 p K fieldK l V addV modV x y h v M h_T001 h_T002 h_H003
  have h_T004 : (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d) ∧ LR.LocalBasis p l M := @T004 p K fieldK l V addV modV x y h v M h_H001 h_H004 h_T003
  have h_T005 : LR.LocalStable p M x y := @T005 p K fieldK l V addV modV x y h v M h_H004 h_T004
  have h_T006 : ∀ b : Module.Basis (Fin (l+1)) ℂ V, (∀ i, b i = LR.vec y v i.val) → LR.PartialUnits l x y b := @T006 p K fieldK l V addV modV x y h v M h_T003
  have h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d) := @T007 p K fieldK l V addV modV x y h v M h_H001 h_T003 h_T004 h_T005 h_T006
  have h_T008 : LR.Decomposition p l M y v := @T008 p K fieldK l V addV modV x y h v M h_H001 h_T003 h_T007
  have h_T009 : LR.TensorLine p M y v := @T009 p K fieldK l V addV modV x y h v M h_H001 h_T007 h_T008
  have h_T010 : Nonempty (TensorProduct (LR.R p) ℚ (LR.MR p M) ≃ₗ[ℚ] (Fin (l+1) → TensorProduct (LR.R p) ℚ (LR.J p M y v 0))) ∧ LR.RankOne p M y v := @T010 p K fieldK l V addV modV x y h v M h_H001 h_T007 h_T008 h_T009
  have h_T011 : LR.Generators p M y v := @T011 p K fieldK l V addV modV x y h v M h_T008 h_T009 h_T010
  have h_T012 : LR.Valuations p M y v := @T012 p K fieldK l V addV modV x y h v M h_H001 h_T007 h_T011
  have h_T013 : LR.N3 p l M y v := @T013 p K fieldK l V addV modV x y h v M h_H001 h_T003 h_T008 h_T009 h_T010 h_T012
  have h_T014 : ∃ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p) (A : LR.Actions M x y h), LR.ResidueMaps K p c rho sigma := @T014 p K fieldK l V addV modV x y h v M h_H001 h_H002 h_H004 h_T007
  have h_T015 : ∀ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p), LR.ResidueMaps K p c rho sigma → LR.Transport K p M c rho sigma := @T015 p K fieldK l V addV modV x y h v M h_T007
  have h_T016 : ∀ (c : CharP K p) (rho : LR.R p →+* K) (sigma : LR.R p →+* ZMod p) (A : LR.Actions M x y h), LR.ResidueMaps K p c rho sigma → LR.Reduction K p l M x y h v A c rho sigma := @T016 p K fieldK l V addV modV x y h v M h_H001 h_T003 h_T007 h_T013 h_T015
  have h_T017 : LR.N4 K p l M x y h v ∧ ∃ b : ℂ, LR.Generates p M y v b ∧ LR.ScaledBasis p l M y v b := @T017 p K fieldK l V addV modV x y h v M h_H001 h_T003 h_T007 h_T013 h_T014 h_T016
  have h_T018 : ∃ (A : LR.Actions M x y h) (beta : Module.Basis (Fin (l+1)) K (LR.VK K M)), Nontrivial (LR.VK K M) ∧ ∀ W : Submodule K (LR.VK K M), LR.inv W (LR.induced K M A.lx.map) → LR.inv W (LR.induced K M A.ly.map) → ∀ i j, LR.inv W (LR.unit l beta i j) := @T018 p K fieldK l V addV modV x y h v M h_H001 h_T017
  have h_T019 : ∀ (beta : Module.Basis (Fin (l+1)) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), (∀ i j, LR.inv W (LR.unit l beta i j)) → W ≠ ⊥ → W = ⊤ := @T019 p K fieldK l V addV modV x y h v M 
  have h_T020 : ∃ A : LR.Actions M x y h, Nontrivial (LR.VK K M) ∧ ∀ W : Submodule K (LR.VK K M), LR.inv W (LR.induced K M A.lx.map) → LR.inv W (LR.induced K M A.ly.map) → LR.inv W (LR.induced K M A.lh.map) → W = ⊥ ∨ W = ⊤ := @T020 p K fieldK l V addV modV x y h v M h_H001 h_H002 h_H004 h_T018 h_T019
  exact h_T020

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ l < p) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l+1 ∧ h*x-x*h = (2 : ℂ) • x ∧ h*y-y*h = (-2 : ℂ) • y ∧ x*y-y*x = h ∧ (∀ W : Submodule ℂ V, LR.inv W x → LR.inv W y → LR.inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (l : ℂ) • v) (h_H004 : (∃ (ι : Type) (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℂ V), ∀ i, (b i : V) = c i) ∧ (∀ r : ℕ, (∀ m : M, LR.divided x r m ∈ M) ∧ (∀ m : M, LR.divided y r m ∈ M))) : ∃ A : LR.Actions M x y h, Nontrivial (LR.VK K M) ∧ ∀ W : Submodule K (LR.VK K M), LR.inv W (LR.induced K M A.lx.map) → LR.inv W (LR.induced K M A.ly.map) → LR.inv W (LR.induced K M A.lh.map) → W = ⊥ ∨ W = ⊤ := by
  exact @Translation.P p K fieldK l V addV modV x y h v M h_H001 h_H002 h_H003 h_H004

#check @P
#print axioms P
end AuditBExport
