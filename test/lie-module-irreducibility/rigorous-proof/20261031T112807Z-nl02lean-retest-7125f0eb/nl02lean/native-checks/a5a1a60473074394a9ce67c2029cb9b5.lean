import Mathlib
open scoped TensorProduct
noncomputable section
namespace SL2Reduction
abbrev Index (lam : ℤ) := Fin (lam.toNat + 1)
def localRing (p : ℕ) : Subalgebra ℤ ℚ :=
  Algebra.adjoin ℤ {q : ℚ | ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)}
abbrev R (p : ℕ) := ↥(localRing p)
instance complexAlgebra (p : ℕ) : Algebra (R p) ℂ :=
  ((algebraMap ℚ ℂ).comp (localRing p).val.toRingHom).toAlgebra
instance ratComplexTower (p : ℕ) : IsScalarTower (R p) ℚ ℂ :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
instance (priority := 50) localModule (p : ℕ) : Module (R p) V := Module.restrictScalars (R p) ℂ V
instance (priority := 50) localTower (p : ℕ) : IsScalarTower (R p) ℂ V := IsScalarTower.restrictScalars (R p) ℂ V
def divided (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r
def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V := divided y i v
abbrev MR (p : ℕ) (M : Submodule ℤ V) := R p ⊗[ℤ] M
abbrev VK (K : Type*) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
def iota (p : ℕ) (M : Submodule ℤ V) : MR p M →ₗ[R p] V :=
  M.subtype.liftBaseChange (R p)
def localizedImage (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) V :=
  (iota p M).range
def Ji (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) : Submodule (R p) ℂ :=
  (localizedImage p M).comap ((LinearMap.toSpanSingleton ℂ V (e y v i)).restrictScalars (R p))
def J (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) := Ji p M y v 0
def qmul (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) :
  (ℚ ⊗[R p] J p M y v) →ₗ[ℚ] ℂ :=
  (J p M y v).subtype.liftBaseChange ℚ

def Preserves (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ m : M, f (m : V) ∈ M
def RPreserves (p : ℕ) (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ u ∈ localizedImage p M, f u ∈ localizedImage p M
structure LatticeOps (M : Submodule ℤ V) where
  x : Module.End ℤ M
  y : Module.End ℤ M
  h : Module.End ℤ M
  X : ℕ → Module.End ℤ M
  Y : ℕ → Module.End ℤ M
def Agrees (M : Submodule ℤ V) (x y h : Module.End ℂ V) (a : LatticeOps M) : Prop :=
  (∀ m : M, (a.x m : V) = x (m : V)) ∧
  (∀ m : M, (a.y m : V) = y (m : V)) ∧
  (∀ m : M, (a.h m : V) = h (m : V)) ∧
  (∀ r (m : M), (a.X r m : V) = divided x r (m : V)) ∧
  (∀ r (m : M), (a.Y r m : V) = divided y r (m : V))
def Invariant {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (W : Submodule F U) (f : Module.End F U) : Prop :=
  ∀ u ∈ W, f u ∈ W
def Simple {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (x y h : Module.End F U) : Prop :=
  Nontrivial U ∧ ∀ W : Submodule F U,
    Invariant W x → Invariant W y → Invariant W h → W = ⊥ ∨ W = ⊤
def Highest (lam : ℤ) (x h : Module.End ℂ V) : Prop :=
  ∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lam : ℂ) • w
def Admissible (M : Submodule ℤ V) (x y : Module.End ℂ V) : Prop :=
  (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (c : Module.Basis (Fin d) ℂ V),
    ∀ i, (b i : V) = c i) ∧
  ∀ r : ℕ, Preserves M (divided x r) ∧ Preserves M (divided y r)
def extendFamily {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (b : Index lam → U) (i : ℕ) : U :=
  if hi : i < lam.toNat + 1 then b ⟨i, hi⟩ else 0
def GeneratorFormulas {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (b : Index lam → U) (x y h : Module.End F U) : Prop :=
  ∀ i : Index lam,
    x (b i) = (if i.val = 0 then 0 else
      (((lam - (i.val : ℤ) + 1 : ℤ) : F) • extendFamily (F := F) lam b (i.val - 1))) ∧
    y (b i) = ((i.val + 1 : ℕ) : F) • extendFamily (F := F) lam b (i.val + 1) ∧
    h (b i) = (((lam - 2 * (i.val : ℤ) : ℤ) : F) • b i)
def DividedFormulas {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (b : Index lam → U) (X Y : ℕ → Module.End F U) : Prop :=
  ∀ (i : Index lam) (r : ℕ),
    X r (b i) = (if r ≤ i.val then
      ((Nat.choose (lam.toNat - i.val + r) r : ℕ) : F) • extendFamily (F := F) lam b (i.val - r)
      else 0) ∧
    Y r (b i) = ((Nat.choose (i.val + r) r : ℕ) : F) • extendFamily (F := F) lam b (i.val + r)
def E (lam : ℤ) (b : Module.Basis (Index lam) ℂ V) (i j : Index lam) : Module.End ℂ V :=
  (b.coord j).smulRight (b i)
def MatrixWord {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (X Y : ℕ → Module.End F U) (i j : Index lam) : Module.End F U :=
  ((Nat.choose lam.toNat j.val : F)⁻¹) •
    (X (lam.toNat - i.val) * (Y lam.toNat * X lam.toNat) * Y (lam.toNat - j.val))
def BasisLift (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop :=
  ∃ c : Module.Basis (Index lam) (R p) (MR p M),
    ∀ i, iota p M (c i) = b • e y v i.val
def Principal (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop :=
  b ≠ 0 ∧ J p M y v = Submodule.span (R p) {b}
def Target (K : Type*) [Field K] (M : Submodule ℤ V) (x y h : Module.End ℂ V) : Prop :=
  ∃ a : LatticeOps M, Agrees M x y h a ∧
    Simple (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K)


def Lowering (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  ∀ t : ℕ,
    h ((y ^ t) v) = (((lam - 2 * (t : ℤ) : ℤ) : ℂ) • (y ^ t) v) ∧
    x ((y ^ (t + 1)) v) =
      (((((t + 1 : ℕ) : ℤ) * (lam - (t : ℤ)) : ℤ) : ℂ) • (y ^ t) v)
def CoordinateCore (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  (∃ b : Module.Basis (Index lam) ℂ V, ∀ i, b i = e y v i.val) ∧
  (∀ t : ℕ, lam.toNat < t → (y ^ t) v = 0) ∧
  GeneratorFormulas lam (fun i : Index lam => e y v i.val) x y h
def Coordinates (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  ((lam.toNat + 1 : ℕ) : ℤ) = lam + 1 ∧
  0 < lam.toNat + 1 ∧ Fintype.card (Index lam) = lam.toNat + 1 ∧
  Lowering lam x y h v ∧
  (∀ i : Index lam, e y v i.val ≠ 0) ∧
  CoordinateCore lam x y h v ∧
  DividedFormulas lam (fun i : Index lam => e y v i.val) (divided x) (divided y)
def LocalLattice (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (x y h : Module.End ℂ V) : Prop :=
  Function.Injective (iota p M) ∧
  (iota p M).range = Submodule.span (R p) (M : Set V) ∧
  Nonempty (Module.Basis (Index lam) (R p) (MR p M)) ∧
  Submodule.span ℂ (localizedImage p M : Set V) = ⊤ ∧
  (∀ r, Preserves M (divided x r) ∧ Preserves M (divided y r) ∧
    RPreserves p M (divided x r) ∧ RPreserves p M (divided y r)) ∧
  Preserves M x ∧ Preserves M y ∧ Preserves M h ∧
  RPreserves p M x ∧ RPreserves p M y ∧ RPreserves p M h ∧
  ∃ a : LatticeOps M, Agrees M x y h a
def MatrixIdentities (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (x y : Module.End ℂ V) (v : V) : Prop :=
  ∀ b : Module.Basis (Index lam) ℂ V, (∀ i, b i = e y v i.val) →
  ∀ i j : Index lam,
    (divided y lam.toNat * divided x lam.toNat) =
      E lam b (Fin.last lam.toNat) (Fin.last lam.toNat) ∧
    divided x (lam.toNat - i.val) * (divided y lam.toNat * divided x lam.toNat) =
      E lam b i (Fin.last lam.toNat) ∧
    (divided y lam.toNat * divided x lam.toNat) * divided y (lam.toNat - j.val) =
      (Nat.choose lam.toNat j.val : ℂ) • E lam b (Fin.last lam.toNat) j ∧
    (∃ c : R p, (c : ℚ) = (Nat.choose lam.toNat j.val : ℚ) ∧ IsUnit c) ∧
    E lam b i j = MatrixWord lam (divided x) (divided y) i j ∧
    RPreserves p M (E lam b i j)
def CommonModule (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (y : Module.End ℂ V) (v : V) : Prop :=
  (∀ i : Index lam, Ji p M y v i.val = J p M y v) ∧
  Nontrivial (J p M y v) ∧ Module.Finite (R p) (J p M y v) ∧
  ∃ c : (Index lam → J p M y v) ≃ₗ[R p] MR p M,
    ∀ g, iota p M (c g) = ∑ i : Index lam, (g i : ℂ) • e y v i.val
def RationalLine (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  Function.Injective (qmul p M y v) ∧
  (qmul p M y v).range = Submodule.span ℚ (J p M y v : Set ℂ) ∧
  Module.Finite ℚ (ℚ ⊗[R p] J p M y v) ∧
  Module.finrank ℚ (ℚ ⊗[R p] J p M y v) = 1
def PrincipalLattice (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (y : Module.End ℂ V) (v : V) : Prop :=
  RationalLine p M y v ∧ (∃ b : ℂ, Principal p M y v b) ∧
  ∀ b : ℂ, Principal p M y v b → BasisLift p lam M y v b
def TensorMaps (p : ℕ) (K : Type*) [Field K] (hp : CharP K p) (M : Submodule ℤ V)
    (kap : R p →+* K) : Prop :=
  letI : CharP K p := hp
  letI : Algebra (R p) K := kap.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  ∃ (phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M))
    (psi : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p)),
    (∀ (c : K) (m : M), phi (c ⊗ₜ[ℤ] m) = c ⊗ₜ[R p] (1 ⊗ₜ[ℤ] m)) ∧
    (∀ (c : K) (u : MR p M), psi (c ⊗ₜ[R p] u) =
      c ⊗ₜ[ZMod p] (ModN.mkQ p u)) ∧
    (∀ (f : Module.End ℤ M) (z : VK K M),
      phi (f.baseChange K z) = (f.baseChange (R p)).baseChange K (phi z)) ∧
    (∀ f : Module.End (R p) (MR p M),
      ∃ fbar : Module.End (ZMod p) (ModN (MR p M) p),
        (∀ u, fbar (ModN.mkQ p u) = ModN.mkQ p (f u)) ∧
        ∀ z, psi (f.baseChange K z) = fbar.baseChange K (psi z))
def ScalarReduction (p : ℕ) (K : Type*) [Field K] (M : Submodule ℤ V) : Prop :=
  ∃ (hp : CharP K p) (kap : R p →+* K),
    (∀ (r : R p) (a b : ℤ), b ≠ 0 → ¬ (p : ℤ) ∣ b →
      (r : ℚ) = (a : ℚ) / (b : ℚ) → kap r = (a : K) / (b : K)) ∧
    TensorMaps p K hp M kap
def ReducedBasis (p : ℕ) (lam : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (x y h : Module.End ℂ V) (v : V) : Prop :=
  ∀ a : LatticeOps M, Agrees M x y h a →
  ∃ (beta : Module.Basis (Index lam) K (VK K M)) (b : ℂ),
    Principal p M y v b ∧
    (∃ (kap : R p →+* K),
      letI : Algebra (R p) K := kap.toAlgebra
      ∃ (phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M))
        (c : Module.Basis (Index lam) (R p) (MR p M)),
        (∀ (s : K) (m : M), phi (s ⊗ₜ[ℤ] m) = s ⊗ₜ[R p] (1 ⊗ₜ[ℤ] m)) ∧
        (∀ i, iota p M (c i) = b • e y v i.val) ∧
        ∀ i, phi (beta i) = 1 ⊗ₜ[R p] (c i)) ∧
    Module.finrank K (VK K M) = lam.toNat + 1 ∧
    GeneratorFormulas lam (fun i => beta i) (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K)
def ReducedUnits (lam : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (x y h : Module.End ℂ V) : Prop :=
  (∀ r : ℕ, r ≤ lam.toNat → (r.factorial : K) ≠ 0) ∧
  (∀ j : Index lam, (Nat.choose lam.toNat j.val : K) ≠ 0) ∧
  ∀ a : LatticeOps M, Agrees M x y h a →
    (∀ r : ℕ, r ≤ lam.toNat →
      (a.X r).baseChange K = (r.factorial : K)⁻¹ • (a.x.baseChange K) ^ r ∧
      (a.Y r).baseChange K = (r.factorial : K)⁻¹ • (a.y.baseChange K) ^ r) ∧
    ∀ beta : Module.Basis (Index lam) K (VK K M),
      GeneratorFormulas lam (fun i => beta i) (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) →
      ∀ i j k : Index lam,
        MatrixWord lam (fun r => (a.X r).baseChange K) (fun r => (a.Y r).baseChange K) i j (beta k) =
          if j = k then beta i else 0

end SL2Reduction
open SL2Reduction

namespace Translation
set_option autoImplicit false

theorem T001 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = (lam + 1).toNat ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ Highest lam x h ∧ Simple x y h) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) :
    Lowering lam x y h v := by
  have comm : (∀ w : V, h (y w) = y (h w) - (2 : ℂ) • y w) ∧
      (∀ w : V, x (y w) = y (x w) + h w) := by
    rcases h_H003 with ⟨_, _, _, hhy, hxy, _⟩
    constructor
    · intro w
      have hw := congrArg (fun f : Module.End ℂ V => f w) hhy
      change h (y w) - y (h w) = (-2 : ℂ) • y w at hw
      rw [neg_smul] at hw
      calc
        h (y w) = -((2 : ℂ) • y w) + y (h w) := sub_eq_iff_eq_add.mp hw
        _ = y (h w) - (2 : ℂ) • y w := by abel
    · intro w
      have hw := congrArg (fun f : Module.End ℂ V => f w) hxy
      change x (y w) - y (x w) = h w at hw
      exact (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)
  have hyp := h_H004
  rcases hyp with ⟨hv, hxv, hhv⟩
  intro t
  induction t with
  | zero =>
    constructor
    · simpa using hhv
    · simpa [pow_succ', comm.2, hxv, hhv] using comm.2 v
  | succ t ih =>
    have hh : h ((y ^ (t + 1)) v) =
        (((lam - 2 * ((t + 1 : ℕ) : ℤ) : ℤ) : ℂ) • (y ^ (t + 1)) v) := by
      rw [pow_succ', Module.End.mul_apply, comm.1, ih.1, map_smul]
      push_cast
      module
    constructor
    · exact hh
    · rw [show t + 1 + 1 = (t + 1) + 1 by rfl, pow_succ',
        Module.End.mul_apply, comm.2, ih.2, map_smul, hh]
      rw [← Module.End.mul_apply, ← pow_succ']
      push_cast
      module

theorem T002 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) (h_T001 : Lowering lam x y h v) :
    ∀ i : Index lam, e y v i.val ≠ 0 ∧ h (e y v i.val) = (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) • e y v i.val) := by
  classical
  have hiter : ∀ n : ℕ, (x ^ n) ((y ^ n) v) =
      ((n.factorial : ℂ) * ∏ t ∈ Finset.range n, (((lam - (t : ℤ) : ℤ) : ℂ))) • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ x, Module.End.mul_apply, (h_T001 n).2, map_smul, ih]
        simp only [Nat.factorial_succ, Nat.cast_mul, Finset.prod_range_succ,
          Int.cast_mul, Int.cast_natCast, smul_smul]
        congr 1
        ring
  intro i
  have hfac : (i.val.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i.val
  have hprod : (∏ t ∈ Finset.range i.val, (((lam - (t : ℤ) : ℤ) : ℂ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro t ht
    have ht' : t < i.val := Finset.mem_range.mp ht
    have hi := i.isLt
    have hlam := h_H002.1
    have hpos : 0 < lam - (t : ℤ) := by omega
    exact_mod_cast (ne_of_gt hpos)
  have hynz : (y ^ i.val) v ≠ 0 := by
    intro hz
    have heq := hiter i.val
    rw [hz, map_zero] at heq
    exact (smul_ne_zero (mul_ne_zero hfac hprod) h_H004.1) heq.symm
  constructor
  · change ((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v ≠ 0
    exact smul_ne_zero (inv_ne_zero hfac) hynz
  · change h (((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v) =
      (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ)) •
        (((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v)
    rw [map_smul, (h_T001 i.val).1]
    exact smul_comm _ _ _

theorem T003 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = (lam + 1).toNat ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ Highest lam x h ∧ Simple x y h) (h_T001 : Lowering lam x y h v) (h_T002 : ∀ i : Index lam, e y v i.val ≠ 0 ∧ h (e y v i.val) = (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) • e y v i.val)) :
    CoordinateCore lam x y h v := by
  classical
  have hli : LinearIndependent ℂ (fun i : Index lam => e y v i.val) := by
    classical
    let μ : Index lam → ℂ := fun i => ((lam - 2 * (i.val : ℤ) : ℤ) : ℂ)
    have hinj : Function.Injective μ := by
      intro i j hij
      have hij' : lam - 2 * (i.val : ℤ) = lam - 2 * (j.val : ℤ) := by
        dsimp [μ] at hij
        exact_mod_cast hij
      apply Fin.ext
      omega
    have hprod : ∀ s : Finset (Index lam), ∃ P : Module.End ℂ V,
        ∀ i, P (e y v i.val) = (∏ k ∈ s, (μ i - μ k)) • e y v i.val := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨1, by simp⟩
      | @insert k s hk ih =>
        obtain ⟨P, hP⟩ := ih
        refine ⟨(h - μ k • 1) * P, ?_⟩
        intro i
        simp only [Module.End.mul_apply, hP, map_smul, LinearMap.sub_apply,
          LinearMap.smul_apply, Module.End.one_apply, (h_T002 i).2,
          Finset.prod_insert hk]
        dsimp [μ]
        module
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    obtain ⟨P, hP⟩ := hprod (Finset.univ.erase j)
    have hp := congrArg P hc
    simp only [map_sum, map_smul, hP, map_zero, smul_smul] at hp
    have hzero : ∀ i : Index lam, i ≠ j →
        ∏ k ∈ Finset.univ.erase j, (μ i - μ k) = 0 := by
      intro i hij
      exact Finset.prod_eq_zero_iff.mpr ⟨i, by simp [hij], sub_self _⟩
    have hsingle : (∑ i : Index lam,
        (c i * ∏ k ∈ Finset.univ.erase j, (μ i - μ k)) • e y v i.val) =
        (c j * ∏ k ∈ Finset.univ.erase j, (μ j - μ k)) • e y v j.val := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        rw [hzero i hij, mul_zero, zero_smul]
      · simp
    rw [hsingle] at hp
    have hn : (∏ k ∈ Finset.univ.erase j, (μ j - μ k)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hk).1 (hinj he).symm)
    exact (mul_eq_zero.mp ((smul_eq_zero.mp hp).resolve_right (h_T002 j).1)).resolve_right hn
  have hcard : Fintype.card (Index lam) = Module.finrank ℂ V := by
    rw [h_H003.2.1]
    simp only [Index, Fintype.card_fin]
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ i, b i = e y v i.val :=
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i
  have hexclude : ∀ (z : V) (μ : ℂ), h z = μ • z →
      (∀ i : Index lam, μ ≠ (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ))) → z = 0 := by
    have aux : ∀ (b : Module.Basis (Index lam) ℂ V), (∀ i, b i = e y v i.val) →
        ∀ (z : V) (μ : ℂ), h z = μ • z →
        (∀ i : Index lam, μ ≠ (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ))) → z = 0 := by
      classical
      intro b hb z μ hz hμ
      have heig : ∀ i : Index lam,
          h (b i) = (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ)) • b i := by
        intro i
        rw [hb]
        exact (h_T002 i).2
      have hmap : h z = ∑ k : Index lam,
          (b.repr z k * (((lam - 2 * (k.val : ℤ) : ℤ) : ℂ))) • b k := by
        calc
          h z = h (∑ k : Index lam, b.repr z k • b k) := by rw [b.sum_repr]
          _ = _ := by simp only [map_sum, map_smul, heig, smul_smul]
      apply b.repr.injective
      ext i
      have hi := congrArg (fun w : V => b.repr w i) hz
      have hi' : b.repr z i * (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ)) = μ * b.repr z i := by
        rw [hmap] at hi
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
          Module.Basis.repr_self_apply, smul_eq_mul] at hi
        simpa using hi
      have hc : b.repr z i = 0 := by
        have hm : ( (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ)) - μ) * b.repr z i = 0 := by
          linear_combination hi'
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr (hμ i).symm)
      simpa using hc
    exact aux b hb
  have hnat : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg h_H002.1
  have hz0 : (y ^ (lam.toNat + 1)) v = 0 := by
    apply hexclude _ (((lam - 2 * ((lam.toNat + 1 : ℕ) : ℤ) : ℤ) : ℂ))
      (h_T001 (lam.toNat + 1)).1
    intro i he
    have he' : lam - 2 * ((lam.toNat + 1 : ℕ) : ℤ) = lam - 2 * (i.val : ℤ) := by
      exact_mod_cast he
    have hi := i.isLt
    omega
  have hterminate : ∀ t : ℕ, lam.toNat < t → (y ^ t) v = 0 := by
    intro t ht
    have ht' : t = (t - (lam.toNat + 1)) + (lam.toNat + 1) := by omega
    rw [ht', pow_add, Module.End.mul_apply, hz0, map_zero]
  have hxv : x v = 0 := by
    have hvh : h v = (lam : ℂ) • v := by simpa using (h_T001 0).1
    have hc := congrArg (fun f : Module.End ℂ V => f v) h_H003.2.2.1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hvh, map_smul] at hc
    have hxvh : h (x v) = (((lam + 2 : ℤ) : ℂ)) • x v := by
      calc
        h (x v) = (2 : ℂ) • x v + (lam : ℂ) • x v := eq_add_of_sub_eq hc
        _ = _ := by push_cast; module
    apply hexclude _ _ hxvh
    intro i he
    have he' : lam + 2 = lam - 2 * (i.val : ℤ) := by exact_mod_cast he
    omega
  have hrec : ∀ n : ℕ,
      y (e y v n) = ((n + 1 : ℕ) : ℂ) • e y v (n + 1) ∧
      x (e y v (n + 1)) = (((lam - (n : ℤ) : ℤ) : ℂ)) • e y v n := by
    intro n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hs : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    constructor
    · have hy : y ((y ^ n) v) = (y ^ (n + 1)) v := by
        rw [pow_succ', Module.End.mul_apply]
      simp only [e, divided, LinearMap.smul_apply, map_smul, hy, smul_smul]
      congr 1
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
    · simp only [e, divided, LinearMap.smul_apply, map_smul, (h_T001 n).2,
        smul_smul]
      congr 1
      rw [Nat.factorial_succ, Nat.cast_mul]
      push_cast
      have hs' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      field_simp
  refine ⟨⟨b, hb⟩, hterminate, ?_⟩
  intro i
  refine ⟨?_, ?_, (h_T002 i).2⟩
  · by_cases hi : i.val = 0
    · simp [hi, e, divided, hxv]
    · rw [if_neg hi]
      have hrange : i.val - 1 < lam.toNat + 1 := by have := i.isLt; omega
      simp only [extendFamily, dif_pos hrange]
      change x (e y v i.val) =
        (((lam - (i.val : ℤ) + 1 : ℤ) : ℂ)) • e y v (i.val - 1)
      have hs : i.val - 1 + 1 = i.val := by omega
      have hcoef : lam - ((i.val - 1 : ℕ) : ℤ) = lam - (i.val : ℤ) + 1 := by omega
      simpa only [hs, hcoef] using (hrec (i.val - 1)).2
  · rw [(hrec i.val).1]
    by_cases hi : i.val + 1 < lam.toNat + 1
    · simp only [extendFamily, dif_pos hi]
    · simp only [extendFamily, dif_neg hi, smul_zero]
      simp only [e, divided, LinearMap.smul_apply,
        hterminate (i.val + 1) (by omega), smul_zero]

theorem T004 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T001 : Lowering lam x y h v) (h_T002 : ∀ i : Index lam, e y v i.val ≠ 0 ∧ h (e y v i.val) = (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) • e y v i.val)) (h_T003 : CoordinateCore lam x y h v) :
    Coordinates lam x y h v := by
  classical
  have hn : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg h_H002.1
  have hstep : ∀ (f : Module.End ℂ V) (r : ℕ) (w : V),
      divided f (r + 1) w = ((r + 1 : ℕ) : ℂ)⁻¹ • f (divided f r w) := by
    intro f r w
    simp [divided, Nat.factorial_succ, pow_succ', mul_smul, mul_comm]
    exact smul_comm _ _ _
  have hc : ∀ n r : ℕ,
      ((r + 1 : ℕ) : ℂ)⁻¹ * (Nat.choose n r : ℂ) * ((n + 1 : ℕ) : ℂ) =
        (Nat.choose (n + 1) (r + 1) : ℂ) := by
    intro n r
    have he : ((n + 1 : ℕ) : ℂ) * (Nat.choose n r : ℂ) =
        (Nat.choose (n + 1) (r + 1) : ℂ) * ((r + 1 : ℕ) : ℂ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n r
    have hr : ((r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    calc
      _ = ((r + 1 : ℕ) : ℂ)⁻¹ *
          (((n + 1 : ℕ) : ℂ) * (Nat.choose n r : ℂ)) := by ring
      _ = _ := by rw [he]; field_simp
  let b : ℕ → V := extendFamily (F := ℂ) lam (fun i : Index lam => e y v i.val)
  have hb : ∀ i : Index lam, b i.val = e y v i.val := by
    intro i
    simp [b, extendFamily, i.isLt]
  have hz : ∀ k : ℕ, lam.toNat + 1 ≤ k → b k = 0 := by
    intro k hk
    simp [b, extendFamily, not_lt.mpr hk]
  have hy : ∀ k : ℕ, y (b k) = ((k + 1 : ℕ) : ℂ) • b (k + 1) := by
    intro k
    by_cases hk : k < lam.toNat + 1
    · have hh := (h_T003.2.2 ⟨k, hk⟩).2.1
      change y (e y v k) = ((k + 1 : ℕ) : ℂ) • b (k + 1) at hh
      rw [hb ⟨k, hk⟩]
      exact hh
    · rw [hz k (by omega), map_zero, hz (k + 1) (by omega), smul_zero]

  have hx : ∀ k : ℕ, k ≤ lam.toNat →
      x (b k) = if k = 0 then 0 else
        (((lam - (k : ℤ) + 1 : ℤ) : ℂ) • b (k - 1)) := by
    intro k hk
    have hh := (h_T003.2.2 ⟨k, by omega⟩).1
    change x (e y v k) =
      (if k = 0 then 0 else (((lam - (k : ℤ) + 1 : ℤ) : ℂ) • b (k - 1))) at hh
    rw [hb ⟨k, by omega⟩]
    exact hh

  have hydiv : ∀ (i : Index lam) (r : ℕ),
      divided y r (e y v i.val) =
        (Nat.choose (i.val + r) r : ℂ) • b (i.val + r) := by
    intro i r
    change divided y r (e y v i.val) = (Nat.choose (i.val + r) r : ℂ) • b (i.val + r)
    induction r with
    | zero => simp [divided, ← hb i]
    | succ r ih =>
      rw [hstep, ih, map_smul, hy]
      simp only [smul_smul]
      rw [← mul_assoc, hc]
      simp only [Nat.add_assoc]
  have hxdiv : ∀ (i : Index lam) (r : ℕ),
      divided x r (e y v i.val) =
        if r ≤ i.val then
          (Nat.choose (lam.toNat - i.val + r) r : ℂ) • b (i.val - r)
        else 0 := by
    intro i r
    change divided x r (e y v i.val) =
      if r ≤ i.val then (Nat.choose (lam.toNat - i.val + r) r : ℂ) • b (i.val - r) else 0
    induction r with
    | zero => simp [divided, ← hb i]
    | succ r ih =>
      rw [hstep, ih]
      by_cases hr : r ≤ i.val
      · rw [if_pos hr, map_smul, hx (i.val - r) (by omega)]
        by_cases hri : r < i.val
        · have hk0 : i.val - r ≠ 0 := by omega
          have hr1 : r + 1 ≤ i.val := by omega
          have he : lam - ((i.val - r : ℕ) : ℤ) + 1 =
              ((lam.toNat - i.val + r + 1 : ℕ) : ℤ) := by
            have hi := i.isLt
            omega
          have hec : ((lam - ((i.val - r : ℕ) : ℤ) + 1 : ℤ) : ℂ) =
              ((lam.toNat - i.val + r + 1 : ℕ) : ℂ) := by
            exact_mod_cast he
          rw [if_neg hk0, if_pos hr1, hec]
          simp only [smul_smul]
          rw [← mul_assoc, hc]
          congr 2 <;> omega
        · have hzero : i.val - r = 0 := by omega
          have hr1 : ¬ r + 1 ≤ i.val := by omega
          simp [hzero, hr1]
      · have hr1 : ¬ r + 1 ≤ i.val := by omega
        simp [hr, hr1]
  refine ⟨?_, Nat.succ_pos _, ?_, h_T001, ?_, h_T003, ?_⟩
  · simp only [Nat.cast_add, Nat.cast_one, hn]
  · simp [Index]
  · intro i
    exact (h_T002 i).1
  · intro i r
    exact ⟨hxdiv i r, hydiv i r⟩

theorem T005 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) :
    (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ := by
  have hp : Prime (p : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using h_H001.1)
  constructor
  · intro q
    constructor
    · intro hq
      change q ∈ Algebra.adjoin ℤ {q : ℚ | ∃ a b : ℤ,
        b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)} at hq
      induction hq using Algebra.adjoin_induction with
      | mem q hq => exact hq
      | algebraMap a =>
          exact ⟨a, 1, one_ne_zero, hp.not_dvd_one, by simp⟩
      | add q r hq hr ihq ihr =>
          rcases ihq with ⟨a, b, hb, hpb, hq'⟩
          rcases ihr with ⟨c, d, hd, hpd, hr'⟩
          refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_, ?_⟩
          · intro hbd
            rcases hp.dvd_mul.mp hbd with h | h
            · exact hpb h
            · exact hpd h
          · have hb' : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
            have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
            rw [hq', hr']
            push_cast
            field_simp
      | mul q r hq hr ihq ihr =>
          rcases ihq with ⟨a, b, hb, hpb, hq'⟩
          rcases ihr with ⟨c, d, hd, hpd, hr'⟩
          refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_, ?_⟩
          · intro hbd
            rcases hp.dvd_mul.mp hbd with h | h
            · exact hpb h
            · exact hpd h
          · rw [hq', hr']
            push_cast
            exact div_mul_div_comm (a : ℚ) b c d
    · intro hq
      exact Algebra.subset_adjoin hq
  · infer_instance

theorem T006 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = (lam + 1).toNat ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ Highest lam x h ∧ Simple x y h) (h_H005 : Admissible M x y) (h_T004 : Coordinates lam x y h v) :
    LocalLattice p lam M x y h := by
  classical
  obtain ⟨⟨d, b, c, hbc⟩, hdiv⟩ := h_H005
  obtain ⟨be, hbe⟩ := h_T004.2.2.2.2.2.1.1
  have hd : d = lam.toNat + 1 := by
    have hc := Module.finrank_eq_card_basis c
    have he := Module.finrank_eq_card_basis be
    simpa only [Fintype.card_fin] using hc.symm.trans he
  let br : Module.Basis (Fin d) (R p) (MR p M) := b.baseChange (R p)
  have himg : ∀ i, iota p M (br i) = c i := by
    intro i
    simp [br, Module.Basis.baseChange_apply, iota, hbc]
  have hs : Function.Injective (fun r : R p => r • (1 : ℂ)) := by
    change Function.Injective (fun r : R p => (algebraMap (R p) ℂ r) * (1 : ℂ))
    simp only [mul_one]
    change Function.Injective ((algebraMap ℚ ℂ).comp (localRing p).val.toRingHom)
    exact (algebraMap ℚ ℂ).injective.comp Subtype.val_injective
  have hi : LinearIndependent (R p) (fun i => c i) :=
    LinearIndependent.restrict_scalars (R := R p) (K := ℂ) hs c.linearIndependent
  have hinj : Function.Injective (iota p M) := by
    apply LinearMap.injective_of_linearIndependent br.span_eq
    have he : (iota p M) ∘ br = fun i => c i := funext himg
    rw [he]
    exact hi
  have hrange : (iota p M).range = Submodule.span (R p) (M : Set V) := by
    simp only [iota, LinearMap.range_liftBaseChange, Submodule.range_subtype]
  have hfull : Submodule.span ℂ (localizedImage p M : Set V) = ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem c).2
    intro i
    apply Submodule.subset_span
    exact ⟨br i, himg i⟩
  have hext : ∀ f : Module.End ℂ V, Preserves M f → RPreserves p M f := by
    intro f hf u hu
    change u ∈ (iota p M).range at hu
    change f u ∈ (iota p M).range
    rw [hrange] at hu ⊢
    induction hu using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (hf ⟨z, hz⟩)
    | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span (R p) (M : Set V)))
    | add z w hz hw ihz ihw =>
        simpa only [map_add] using (Submodule.add_mem (Submodule.span (R p) (M : Set V)) ihz ihw)
    | smul r z hz ih =>
        change (f.restrictScalars (R p)) (r • z) ∈ _
        rw [map_smul]
        exact Submodule.smul_mem _ r ih
  have hx : Preserves M x := by
    simpa [divided] using (hdiv 1).1
  have hy : Preserves M y := by
    simpa [divided] using (hdiv 1).2
  have hh : Preserves M h := by
    intro m
    have heq : h (m : V) = x (y (m : V)) - y (x (m : V)) := by
      have he := congrArg (fun f : Module.End ℂ V => f (m : V)) h_H003.2.2.2.2.1
      simpa only [LinearMap.sub_apply, Module.End.mul_apply] using he.symm
    rw [heq]
    exact M.sub_mem (hx ⟨y m, hy m⟩) (hy ⟨x m, hx m⟩)
  let res : (f : Module.End ℂ V) → Preserves M f → Module.End ℤ M :=
    fun f hf => (f.restrictScalars ℤ).restrict (fun z hz => hf ⟨z, hz⟩)
  let a : LatticeOps M :=
    { x := res x hx
      y := res y hy
      h := res h hh
      X := fun r => res (divided x r) (hdiv r).1
      Y := fun r => res (divided y r) (hdiv r).2 }
  have ha : Agrees M x y h a := by
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  refine ⟨hinj, hrange, ?_, hfull, ?_, hx, hy, hh, hext x hx, hext y hy, hext h hh, a, ha⟩
  · exact ⟨br.reindex (finCongr hd)⟩
  · intro r
    exact ⟨(hdiv r).1, (hdiv r).2, hext _ (hdiv r).1, hext _ (hdiv r).2⟩

theorem T007 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T005 : (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ) (h_T006 : LocalLattice p lam M x y h) :
    LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v := by
  classical
  have hEdges : ∀ (b : Module.Basis (Index lam) ℂ V), (∀ i, b i = e y v i.val) → ∀ i j : Index lam, (divided y lam.toNat * divided x lam.toNat = E lam b (Fin.last lam.toNat) (Fin.last lam.toNat)) ∧ (divided x (lam.toNat - i.val) * (divided y lam.toNat * divided x lam.toNat) = E lam b i (Fin.last lam.toNat)) ∧ ((divided y lam.toNat * divided x lam.toNat) * divided y (lam.toNat - j.val) = (Nat.choose lam.toNat j.val : ℂ) • E lam b (Fin.last lam.toNat) j) := by
    classical
    intro b hb
    have hf : (fun i : Index lam => e y v i.val) = (fun i => b i) := funext (fun i => (hb i).symm)
    have hd := h_T004.2.2.2.2.2.2
    rw [hf] at hd
    have hext (k : Index lam) : extendFamily (F := ℂ) lam (fun i => b i) k.val = b k := by
      simp [extendFamily, k.isLt]
    have hx (k : Index lam) :
        divided x lam.toNat (b k) = if k = Fin.last lam.toNat then b ⟨0, by omega⟩ else 0 := by
      rw [(hd k lam.toNat).1]
      by_cases hk : k = Fin.last lam.toNat
      · subst k
        simp [extendFamily]
      · have hk' : k.val < lam.toNat := by
          have := k.isLt
          have : k.val ≠ lam.toNat := fun hh => hk (Fin.ext hh)
          omega
        simp [Nat.not_le.mpr hk', hk]
    have hy : divided y lam.toNat (b ⟨0, by omega⟩) = b (Fin.last lam.toNat) := by
      rw [(hd ⟨0, by omega⟩ lam.toNat).2]
      simp [extendFamily, Fin.last]
    have hp : divided y lam.toNat * divided x lam.toNat =
        E lam b (Fin.last lam.toNat) (Fin.last lam.toNat) := by
      apply b.ext
      intro k
      simp only [Module.End.mul_apply, hx]
      split_ifs with hk
      · subst k
        simpa [E] using hy
      · simp [E, hk, Ne.symm hk]
    have hxi (i : Index lam) :
        divided x (lam.toNat - i.val) (b (Fin.last lam.toNat)) = b i := by
      rw [(hd (Fin.last lam.toNat) (lam.toNat - i.val)).1]
      have hi : i.val ≤ lam.toNat := by have := i.isLt; omega
      have hn : lam.toNat - (lam.toNat - i.val) = i.val := by omega
      simp [hi, hn, extendFamily, i.isLt]
    intro i j
    refine ⟨hp, ?_, ?_⟩
    · rw [hp]
      apply b.ext
      intro k
      by_cases hk : k = Fin.last lam.toNat
      · subst k
        simpa [E] using hxi i
      · simp [Module.End.mul_apply, E, hk, Ne.symm hk]
    · apply b.ext
      intro k
      rw [Module.End.mul_apply, (hd k (lam.toNat - j.val)).2, map_smul, hp]
      by_cases hkj : k = j
      · subst k
        have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
        have hn : j.val + (lam.toNat - j.val) = lam.toNat := by omega
        simp [hn, extendFamily, E, Fin.last, Nat.choose_symm hj]
      · by_cases hlt : k.val + (lam.toNat - j.val) < lam.toNat + 1
        · let a : Index lam := ⟨k.val + (lam.toNat - j.val), hlt⟩
          have ha : a ≠ Fin.last lam.toNat := by
            intro ha
            have hv := congrArg Fin.val ha
            have hj := j.isLt
            have hk := k.isLt
            apply hkj
            apply Fin.ext
            dsimp [a] at hv
            omega
          simp [extendFamily, hlt, E, hkj, Ne.symm hkj, show (⟨k.val + (lam.toNat - j.val), hlt⟩ : Index lam) ≠ Fin.last lam.toNat from ha, Ne.symm ha]
        · simp [extendFamily, hlt, E, hkj, Ne.symm hkj]
  have hUnits : ∀ j : Index lam, ∃ (c d : R p), (c : ℚ) = (Nat.choose lam.toNat j.val : ℚ) ∧ IsUnit c ∧ (algebraMap (R p) ℂ d) = (Nat.choose lam.toNat j.val : ℂ)⁻¹ := by
    intro j
    have hn : lam.toNat < p := by
      have hl : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg h_H002.1
      omega
    have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
    have hnd : ¬ p ∣ Nat.choose lam.toNat j.val := by
      intro hh
      have hd : p ∣ lam.toNat.factorial := by
        rw [← Nat.choose_mul_factorial_mul_factorial hj]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hh _) _
      exact (not_le_of_gt hn) ((h_H001.1.dvd_factorial).mp hd)
    have hci : ¬ (p : ℤ) ∣ (Nat.choose lam.toNat j.val : ℤ) := by
      exact_mod_cast hnd
    have hc0 : Nat.choose lam.toNat j.val ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hj)
    have hq0 : (Nat.choose lam.toNat j.val : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hmem : (Nat.choose lam.toNat j.val : ℚ)⁻¹ ∈ localRing p := by
      apply (h_T005.1 _).2
      refine ⟨1, (Nat.choose lam.toNat j.val : ℤ), ?_, hci, ?_⟩
      · exact_mod_cast hc0
      · simp
    let c : R p := (Nat.choose lam.toNat j.val : R p)
    let d : R p := ⟨(Nat.choose lam.toNat j.val : ℚ)⁻¹, hmem⟩
    have hcd : c * d = 1 := by
      apply Subtype.ext
      change (Nat.choose lam.toNat j.val : ℚ) * (Nat.choose lam.toNat j.val : ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ hq0
    refine ⟨c, d, ?_, isUnit_iff_exists_inv.mpr ⟨d, hcd⟩, ?_⟩
    · simp [c]
    · change algebraMap ℚ ℂ ((Nat.choose lam.toNat j.val : ℚ)⁻¹) = _
      simp
  refine ⟨h_T006, ?_⟩
  intro b hb i j
  obtain ⟨hp, hl, hr⟩ := hEdges b hb i j
  obtain ⟨c, d, hc, hcu, hd⟩ := hUnits j
  have hcoef : (Nat.choose lam.toNat j.val : ℂ) ≠ 0 := by
    have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hj))
  have hxe : divided x (lam.toNat - i.val) * E lam b (Fin.last lam.toNat) j = E lam b i j := by
    apply b.ext
    intro k
    by_cases hk : k = j
    · subst k
      have hv := congrArg (fun f : Module.End ℂ V => f (b (Fin.last lam.toNat))) hl
      simpa [Module.End.mul_apply, hp, E] using hv
    · simp [Module.End.mul_apply, E, hk, Ne.symm hk]
  have hraw :
      divided x (lam.toNat - i.val) * (divided y lam.toNat * divided x lam.toNat) *
          divided y (lam.toNat - j.val) =
        (Nat.choose lam.toNat j.val : ℂ) • E lam b i j := by
    rw [mul_assoc, hr, mul_smul_comm, hxe]
  have hw : E lam b i j = MatrixWord lam (divided x) (divided y) i j := by
    unfold MatrixWord
    rw [hraw, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
  refine ⟨hp, hl, hr, ⟨c, hc, hcu⟩, hw, ?_⟩
  intro u hu
  rw [hw]
  have hpres := h_T006.2.2.2.2.1
  have hu1 := (hpres (lam.toNat - j.val)).2.2.2 u hu
  have hu2 := (hpres lam.toNat).2.2.1 _ hu1
  have hu3 := (hpres lam.toNat).2.2.2 _ hu2
  have hu4 := (hpres (lam.toNat - i.val)).2.2.1 _ hu3
  have hsmul : d • (divided x (lam.toNat - i.val) (divided y lam.toNat (divided x lam.toNat (divided y (lam.toNat - j.val) u)))) =
      (Nat.choose lam.toNat j.val : ℂ)⁻¹ • (divided x (lam.toNat - i.val) (divided y lam.toNat (divided x lam.toNat (divided y (lam.toNat - j.val) u)))) := by
    change (algebraMap (R p) ℂ d) • (divided x (lam.toNat - i.val) (divided y lam.toNat (divided x lam.toNat (divided y (lam.toNat - j.val) u)))) = _
    rw [hd]
  simpa only [MatrixWord, LinearMap.smul_apply, Module.End.mul_apply, ← hsmul] using
    (localizedImage p M).smul_mem d hu4

theorem T008 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) :
    ∀ i : Index lam, Ji p M y v i.val = J p M y v := by
  classical
  rcases h_T004 with ⟨_, _, _, _, _, hcore, _⟩
  rcases hcore.1 with ⟨b, hb⟩
  have transport (i j : Index lam) : Ji p M y v j.val ≤ Ji p M y v i.val := by
    intro c hc
    change c • e y v j.val ∈ localizedImage p M at hc
    change c • e y v i.val ∈ localizedImage p M
    have hpres : RPreserves p M (E lam b i j) :=
      (h_T007.2 b hb i j).2.2.2.2.2
    have heval : E lam b i j (c • e y v j.val) = c • e y v i.val := by
      rw [← hb j, ← hb i]
      simp [E, LinearMap.smulRight_apply, Module.Basis.coord_apply]
    rw [← heval]
    exact hpres _ hc
  let z : Index lam := ⟨0, Nat.zero_lt_succ _⟩
  intro i
  change Ji p M y v i.val = Ji p M y v z.val
  exact le_antisymm (transport z i) (transport i z)

theorem T009 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) (h_T008 : ∀ i : Index lam, Ji p M y v i.val = J p M y v) :
    CommonModule p lam M y v := by
  classical
  obtain ⟨b, hb⟩ := h_T004.2.2.2.2.2.1.1
  have hcoord : ∀ (u : MR p M) (i : Index lam),
      b.repr (iota p M u) i ∈ J p M y v := by
    intro u i
    rw [← h_T008 i]
    change (b.repr (iota p M u) i) • e y v i.val ∈ localizedImage p M
    rw [← hb i]
    have hp := (h_T007.2 b hb i i).2.2.2.2.2
    have hu : iota p M u ∈ localizedImage p M := ⟨u, rfl⟩
    simpa [E, Module.Basis.coord] using hp (iota p M u) hu
  let d : MR p M →ₗ[R p] (Index lam → J p M y v) :=
    LinearMap.pi (fun i =>
      (((b.coord i).restrictScalars (R p)).comp (iota p M)).codRestrict
        (J p M y v) (fun u => hcoord u i))
  have hd : ∀ u i, (d u i : ℂ) = b.repr (iota p M u) i := by
    intro u i
    rfl
  have hdecomp : ∀ u : MR p M,
      iota p M u = ∑ i : Index lam, (d u i : ℂ) • e y v i.val := by
    intro u
    simpa only [hd, ← hb] using (b.sum_repr (iota p M u)).symm
  have hdinj : Function.Injective d := by
    intro u w huw
    apply h_T007.1.1
    apply b.repr.injective
    ext i
    simpa only [hd] using congrArg (fun g : Index lam → J p M y v => (g i : ℂ)) huw
  have hdsurj : Function.Surjective d := by
    intro g
    have hsum : (∑ i : Index lam, (g i : ℂ) • e y v i.val) ∈ localizedImage p M := by
      apply Submodule.sum_mem
      intro i hi
      have hg : (g i : ℂ) ∈ Ji p M y v i.val := by
        rw [h_T008 i]
        exact (g i).property
      exact hg
    obtain ⟨u, hu⟩ := hsum
    refine ⟨u, ?_⟩
    funext i
    apply Subtype.ext
    rw [hd, hu]
    simpa only [hb] using congrFun (b.repr_sum_self (fun i => (g i : ℂ))) i
  let c : (Index lam → J p M y v) ≃ₗ[R p] MR p M :=
    (LinearEquiv.ofBijective d ⟨hdinj, hdsurj⟩).symm
  have hc : ∀ g, iota p M (c g) = ∑ i : Index lam, (g i : ℂ) • e y v i.val := by
    intro g
    have hdc : d (c g) = g := (LinearEquiv.ofBijective d ⟨hdinj, hdsurj⟩).apply_symm_apply g
    rw [hdecomp, hdc]
  let i0 : Index lam := ⟨0, Nat.zero_lt_succ _⟩
  have hnon : Nontrivial (J p M y v) := by
    by_contra hn
    letI : Subsingleton (J p M y v) := not_nontrivial_iff_subsingleton.mp hn
    have hz : ∀ u : MR p M, iota p M u = 0 := by
      intro u
      rw [hdecomp]
      apply Finset.sum_eq_zero
      intro i hi
      have hi0 : (d u i : ℂ) = 0 :=
        congrArg Subtype.val (Subsingleton.elim (d u i) 0)
      rw [hi0, zero_smul]
    have hs : Submodule.span ℂ (localizedImage p M : Set V) ≤ (⊥ : Submodule ℂ V) := by
      apply Submodule.span_le.mpr
      intro z hz'
      obtain ⟨u, rfl⟩ := hz'
      exact hz u
    have hbzero : b i0 = 0 := by
      have hm : b i0 ∈ (⊥ : Submodule ℂ V) := hs (by
        rw [h_T007.1.2.2.2.1]
        trivial)
      exact hm
    exact (h_T004.2.2.2.2.1 i0) (by rw [← hb i0]; exact hbzero)
  obtain ⟨rb⟩ := h_T007.1.2.2.1
  letI : Module.Finite (R p) (MR p M) := Module.Finite.of_basis rb
  let proj : MR p M →ₗ[R p] J p M y v := (LinearMap.proj i0).comp d
  have hproj : Function.Surjective proj := by
    intro t
    obtain ⟨u, hu⟩ := hdsurj (fun _ => t)
    refine ⟨u, ?_⟩
    change d u i0 = t
    exact congrFun hu i0
  have hfin : Module.Finite (R p) (J p M y v) := Module.Finite.of_surjective proj hproj
  exact ⟨h_T008, hnon, hfin, c, hc⟩

theorem T010 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T005 : (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ) (h_T009 : CommonModule p lam M y v) :
    Function.Injective (qmul p M y v) ∧ (qmul p M y v).range = Submodule.span ℚ (J p M y v : Set ℂ) ∧ Module.Finite ℚ (ℚ ⊗[R p] J p M y v) := by
  letI : IsFractionRing (R p) ℚ := h_T005.2
  letI : Module.Finite (R p) (J p M y v) := h_T009.2.2.1
  refine ⟨?_, ?_, inferInstance⟩
  · apply (qmul p M y v).ker_eq_bot.mp
    apply le_antisymm
    · intro z hz
      have hz0 : qmul p M y v z = 0 := hz
      obtain ⟨⟨c, d⟩, hdc⟩ := IsLocalizedModule.surj (nonZeroDivisors (R p))
        (TensorProduct.mk (R p) ℚ (J p M y v) 1) z
      change (d : R p) • z = 1 ⊗ₜ[R p] c at hdc
      have he := congrArg (qmul p M y v) hdc
      rw [LinearMap.map_smul_of_tower, hz0, smul_zero] at he
      have hc : (c : ℂ) = 0 := by
        simpa only [qmul, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, one_smul] using he.symm
      have hc0 : c = 0 := Subtype.ext hc
      have hdz : (d : R p) • z = 0 := by
        simpa only [hc0, TensorProduct.tmul_zero] using hdc
      have hd : algebraMap (R p) ℚ (d : R p) ≠ 0 := (IsLocalization.map_units ℚ d).ne_zero
      have hdz' : algebraMap (R p) ℚ (d : R p) • z = 0 := by
        simpa only [algebraMap_smul] using hdz
      have hz' : z = 0 := by
        calc
          z = ((algebraMap (R p) ℚ (d : R p))⁻¹ * algebraMap (R p) ℚ (d : R p)) • z := by
            rw [inv_mul_cancel₀ hd, one_smul]
          _ = 0 := by rw [mul_smul, hdz', smul_zero]
      exact hz'
    · exact bot_le
  · simpa only [qmul, LinearMap.range_liftBaseChange, Submodule.range_subtype]

theorem T011 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T005 : (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) (h_T009 : CommonModule p lam M y v) (h_T010 : Function.Injective (qmul p M y v) ∧ (qmul p M y v).range = Submodule.span ℚ (J p M y v : Set ℂ) ∧ Module.Finite ℚ (ℚ ⊗[R p] J p M y v)) :
    RationalLine p M y v := by
  classical
  refine ⟨h_T010.1, h_T010.2.1, h_T010.2.2, ?_⟩
  letI : Module.Finite ℚ (ℚ ⊗[R p] J p M y v) := h_T010.2.2
  letI : Module.Free ℚ (ℚ ⊗[R p] J p M y v) := Module.Free.of_divisionRing ℚ _
  obtain ⟨b⟩ := h_T007.1.2.2.1
  letI : Module.Free (R p) (MR p M) := Module.Free.of_basis b
  have hbase : Module.finrank ℚ (ℚ ⊗[R p] MR p M) = lam.toNat + 1 := by
    rw [Module.finrank_baseChange (R := ℚ) (S := R p) (M' := MR p M)]
    simpa only [Index, Fintype.card_fin] using Module.finrank_eq_card_basis b
  obtain ⟨c, hc⟩ := h_T009.2.2.2
  let cq : (ℚ ⊗[R p] MR p M) ≃ₗ[ℚ] (ℚ ⊗[R p] (Index lam → J p M y v)) :=
    c.symm.baseChange (R p) ℚ _ _
  let d : (ℚ ⊗[R p] (Index lam → J p M y v)) ≃ₗ[ℚ]
      (Index lam → (ℚ ⊗[R p] J p M y v)) :=
    TensorProduct.piRight (R p) ℚ ℚ (fun _ : Index lam => J p M y v)
  have hpi : Module.finrank ℚ (Index lam → (ℚ ⊗[R p] J p M y v)) =
      (lam.toNat + 1) * Module.finrank ℚ (ℚ ⊗[R p] J p M y v) := by
    have hh := @Module.finrank_pi_fintype ℚ _ _ (Index lam) _
      (fun _ => (ℚ ⊗[R p] J p M y v))
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => inferInstance) (fun _ => h_T010.2.2)
    simpa only [Finset.sum_const, Finset.card_univ, Index, Fintype.card_fin, smul_eq_mul] using hh
  have heq : lam.toNat + 1 =
      (lam.toNat + 1) * Module.finrank ℚ (ℚ ⊗[R p] J p M y v) := by
    calc
      lam.toNat + 1 = Module.finrank ℚ (ℚ ⊗[R p] MR p M) := hbase.symm
      _ = Module.finrank ℚ (Index lam → (ℚ ⊗[R p] J p M y v)) := (cq.trans d).finrank_eq
      _ = _ := hpi
  nlinarith

theorem T012 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T005 : (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ) (h_T009 : CommonModule p lam M y v) (h_T011 : RationalLine p M y v) :
    ∃ b : ℂ, Principal p M y v b := by
  classical
  have decomp : ∀ q : ℚ, q ≠ 0 → ∃ (η : ℤ) (u : R p), IsUnit u ∧ q = (p : ℚ) ^ η * (u : ℚ) := by
    classical
    intro q hq
    have hp := h_H001.1
    have pp : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have strip : ∀ z : ℤ, z ≠ 0 → ∃ (n : ℕ) (a : ℤ), z = (p : ℤ)^n * a ∧ ¬ (p : ℤ) ∣ a := by
      intro z hz
      have hf : FiniteMultiplicity (p : ℤ) z :=
        Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.ne_one, hz⟩
      obtain ⟨a, ha, hpa⟩ := hf.exists_eq_pow_mul_and_not_dvd
      exact ⟨_, a, ha, hpa⟩
    obtain ⟨n, a, ha, hpa⟩ := strip q.num (Rat.num_ne_zero.mpr hq)
    obtain ⟨m, b, hb, hpb⟩ := strip (q.den : ℤ) (by exact_mod_cast q.den_ne_zero)
    have a0 : a ≠ 0 := by intro h; simp [h] at hpa
    have b0 : b ≠ 0 := by intro h; simp [h] at hpb
    let u : R p := ⟨(a : ℚ) / (b : ℚ), (h_T005.1 _).mpr ⟨a,b,b0,hpb,rfl⟩⟩
    let w : R p := ⟨(b : ℚ) / (a : ℚ), (h_T005.1 _).mpr ⟨b,a,a0,hpa,rfl⟩⟩
    have huw : u * w = 1 := by
      apply Subtype.ext
      change (a : ℚ) / b * ((b : ℚ) / a) = 1
      have aa : (a : ℚ) ≠ 0 := by exact_mod_cast a0
      have bb : (b : ℚ) ≠ 0 := by exact_mod_cast b0
      field_simp
    refine ⟨(n : ℤ) - m, u, isUnit_iff_exists_inv.mpr ⟨w, huw⟩, ?_⟩
    have haQ : (q.num : ℚ) = (p : ℚ)^n * a := by exact_mod_cast ha
    have hbQ : (q.den : ℚ) = (p : ℚ)^m * b := by exact_mod_cast hb
    rw [← Rat.num_div_den q, haQ, hbQ]
    change (p : ℚ)^n * a / ((p : ℚ)^m * b) = (p : ℚ)^((n : ℤ) - m) * ((a : ℚ) / b)
    rw [zpow_sub₀ pp, zpow_natCast, zpow_natCast]
    ring
  have coords : ∃ a : ℂ, a ∈ J p M y v ∧ a ≠ 0 ∧ ∃ s : Finset ℂ, s.Nonempty ∧ 0 ∉ s ∧ Submodule.span (R p) (s : Set ℂ) = J p M y v ∧ ∀ g ∈ s, ∃ q : ℚ, q ≠ 0 ∧ g = q • a := by
    classical
    let L : Submodule (R p) ℂ := J p M y v
    letI : Nontrivial L := h_T009.2.1
    letI : Module.Finite (R p) L := h_T009.2.2.1
    obtain ⟨a, ha⟩ := exists_ne (0 : L)
    have a0 : (a : ℂ) ≠ 0 := by
      intro hz
      apply ha
      exact Subtype.ext hz
    have hdim : Module.finrank ℚ (Submodule.span ℚ (L : Set ℂ)) = 1 := by
      rw [← h_T011.2.1]
      exact (LinearMap.finrank_range_of_inj h_T011.1).trans h_T011.2.2.2
    have hline : Submodule.span ℚ (L : Set ℂ) = Submodule.span ℚ {(a : ℂ)} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hdim (Submodule.subset_span a.property) a0
    have coord : ∀ g : ℂ, g ∈ L → g ≠ 0 → ∃ q : ℚ, q ≠ 0 ∧ g = q • (a : ℂ) := by
      intro g hg hg0
      have hgS : g ∈ Submodule.span ℚ {(a : ℂ)} := hline ▸ Submodule.subset_span hg
      obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hgS
      refine ⟨q, ?_, hq.symm⟩
      intro hz
      exact hg0 (by simpa [hz] using hq.symm)
    obtain ⟨t, ht⟩ : L.FG := Module.Finite.iff_fg.mp inferInstance
    let s : Finset ℂ := t.erase 0
    have hs : Submodule.span (R p) (s : Set ℂ) = L := by
      simpa only [s, Finset.coe_erase, Submodule.span_sdiff_singleton_zero] using ht
    have sn : s.Nonempty := by
      by_contra hn
      have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hL : L = ⊥ := by simpa [he] using hs.symm
      have : (a : ℂ) = 0 := by simpa [hL] using a.property
      exact a0 this
    refine ⟨(a : ℂ), a.property, a0, s, sn, ?_, hs, ?_⟩
    · exact Finset.notMem_erase _ _
    · intro g hg
      apply coord g
      · rw [← hs]
        exact Submodule.subset_span hg
      · intro hg0
        subst g
        exact (Finset.notMem_erase 0 t) hg
  obtain ⟨a, ha, a0, s, sn, s0, hs, hg⟩ := coords
  choose q q0 qeq using (fun g : ↥s => hg g.val g.property)
  choose η u hu heq using (fun g : ↥s => decomp (q g) (q0 g))
  obtain ⟨g₀, hg₀⟩ := sn
  letI : Nonempty ↥s := ⟨⟨g₀, hg₀⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_min η
  have pp : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
  let b : ℂ := ((p : ℚ) ^ η j) • a
  have b0 : b ≠ 0 := smul_ne_zero (zpow_ne_zero _ pp) a0
  have smul_coe : ∀ (r : R p) (z : ℂ), r • z = (r : ℚ) • z := by
    intro r z
    rfl
  have gj : (j : ℂ) = (u j) • b := by
    rw [smul_coe]
    change (j : ℂ) = (u j : ℚ) • ((p : ℚ)^η j • a)
    rw [qeq j, heq j, smul_smul, mul_comm]
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp (hu j)
  have wb : w • (j : ℂ) = b := by
    rw [gj, ← mul_smul, mul_comm w, hw, one_smul]
  have bJ : b ∈ J p M y v := by
    rw [← wb]
    apply Submodule.smul_mem
    rw [← hs]
    exact Submodule.subset_span j.property
  refine ⟨b, b0, le_antisymm ?_ ?_⟩
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro g hg'
    let i : ↥s := ⟨g, hg'⟩
    let r : R p := ⟨(p : ℚ)^((η i - η j).toNat) * (u i : ℚ),
      (localRing p).mul_mem
        ((localRing p).pow_mem ((localRing p).natCast_mem p) _)
        (u i).property⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    rw [smul_coe]
    change ((p : ℚ)^((η i - η j).toNat) * (u i : ℚ)) • ((p : ℚ)^η j • a) = g
    rw [smul_smul]
    have hpow : (p : ℚ)^η i * (u i : ℚ) =
        ((p : ℚ)^((η i - η j).toNat) * (u i : ℚ)) * (p : ℚ)^η j := by
      rw [mul_right_comm, ← zpow_natCast,
        Int.toNat_of_nonneg (sub_nonneg.mpr (hj i)),
        ← zpow_add₀ pp, sub_add_cancel]
    rw [← hpow, ← heq i]
    exact (qeq i).symm
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr bJ)

theorem T013 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) (h_T009 : CommonModule p lam M y v) (h_T011 : RationalLine p M y v) (h_T012 : ∃ b : ℂ, Principal p M y v b) :
    PrincipalLattice p lam M y v := by
  classical
  refine ⟨h_T011, h_T012, ?_⟩
  intro b hb
  rcases hb with ⟨hb0, hbspan⟩
  obtain ⟨c, hc⟩ := h_T009.2.2.2
  have hbmem : b ∈ J p M y v := by
    rw [hbspan]
    exact Submodule.mem_span_singleton_self b
  let bj : J p M y v := ⟨b, hbmem⟩
  let f : R p →ₗ[R p] J p M y v :=
    LinearMap.toSpanSingleton (R p) (J p M y v) bj
  have hfinj : Function.Injective f := by
    intro r s hrs
    have hc' : (algebraMap ℚ ℂ (r : ℚ)) * b =
        (algebraMap ℚ ℂ (s : ℚ)) * b :=
      congrArg (fun z : J p M y v => (z : ℂ)) hrs
    have he : algebraMap ℚ ℂ (r : ℚ) = algebraMap ℚ ℂ (s : ℚ) :=
      mul_right_cancel₀ hb0 hc'
    apply Subtype.ext
    exact (algebraMap ℚ ℂ).injective he
  have hfsurj : Function.Surjective f := by
    intro z
    have hz : (z : ℂ) ∈ Submodule.span (R p) {b} := hbspan ▸ z.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hr
  let d : R p ≃ₗ[R p] J p M y v :=
    LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hd1 : d 1 = bj := by
    change (1 : R p) • bj = bj
    exact one_smul (R p) bj
  let q : (Index lam → R p) ≃ₗ[R p] MR p M :=
    (LinearEquiv.piCongrRight (fun _ : Index lam => d)).trans c
  refine ⟨(Pi.basisFun (R p) (Index lam)).map q, ?_⟩
  intro i
  change iota p M (c ((LinearEquiv.piCongrRight (fun _ : Index lam => d))
    ((Pi.basisFun (R p) (Index lam)) i))) = b • e y v i.val
  rw [hc]
  have hg : (LinearEquiv.piCongrRight (fun _ : Index lam => d))
      ((Pi.basisFun (R p) (Index lam)) i) = Pi.single i bj := by
    ext j
    by_cases hij : i = j
    · subst j
      simp [Pi.basisFun_apply]
      exact hd1
    · simp [Pi.basisFun_apply, Pi.single_apply, hij, d, f]
  rw [hg]
  rw [Finset.sum_eq_single i]
  · simp [bj]
  · intro j hj hji
    simp [Pi.single_apply, hji]
  · simp

theorem T014 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_T005 : (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) :
    ScalarReduction p K M := by
  classical
  letI : CharP K p := h_H001.2
  let S : Submonoid ℤ :=
    { carrier := {b | (b : K) ≠ 0}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change ((a * b : ℤ) : K) ≠ 0
        rw [Int.cast_mul]
        exact mul_ne_zero ha hb }
  have hS (b : ℤ) : b ∈ S ↔ ¬ (p : ℤ) ∣ b := by
    exact not_congr (CharP.intCast_eq_zero_iff K p b)
  letI : IsLocalization S (R p) := by
    apply (isLocalization_iff S (R p)).2
    refine ⟨?_, ?_, ?_⟩
    · intro b
      have hb : ¬ (p : ℤ) ∣ (b : ℤ) := (hS b).1 b.property
      have hb0 : (b : ℤ) ≠ 0 := fun hh => hb (hh ▸ dvd_zero _)
      let c : R p := ⟨1 / (b : ℚ), (h_T005.1 _).2 ⟨1, b, hb0, hb, by simp⟩⟩
      apply IsUnit.of_mul_eq_one c
      apply Subtype.ext
      change (b : ℚ) * (1 / (b : ℚ)) = 1
      simp [hb0]
    · intro r
      obtain ⟨a, b, hb0, hb, hr⟩ := (h_T005.1 _).1 r.property
      refine ⟨(a, ⟨b, (hS b).2 hb⟩), ?_⟩
      apply Subtype.ext
      change (r : ℚ) * (b : ℚ) = (a : ℚ)
      rw [hr, div_mul_cancel₀ _ (Int.cast_ne_zero.mpr hb0)]
    · intro a b hab
      refine ⟨1, ?_⟩
      have habQ : (a : ℚ) = (b : ℚ) := congrArg (fun r : R p => (r : ℚ)) hab
      simpa using (Int.cast_injective habQ : a = b)
  have hu : ∀ b : S, IsUnit (Int.castRingHom K (b : ℤ)) := by
    intro b
    exact isUnit_iff_ne_zero.mpr b.property
  let kap : R p →+* K := IsLocalization.lift (M := S) hu
  have hkap (r : R p) (a b : ℤ) (hb0 : b ≠ 0) (hb : ¬ (p : ℤ) ∣ b)
      (hr : (r : ℚ) = (a : ℚ) / (b : ℚ)) :
      kap r = (a : K) / (b : K) := by
    have heq : r * (b : R p) = (a : R p) := by
      apply Subtype.ext
      change (r : ℚ) * (b : ℚ) = (a : ℚ)
      rw [hr, div_mul_cancel₀ _ (Int.cast_ne_zero.mpr hb0)]
    apply (eq_div_iff ((hS b).2 hb)).2
    have hh := congrArg kap heq
    simpa using hh
  letI : Algebra (R p) K := kap.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (R p) K K M).symm
  have hphi (c : K) (m : M) :
      phi (c ⊗ₜ[ℤ] m) = c ⊗ₜ[R p] (1 ⊗ₜ[ℤ] m) := by
    rfl
  letI : TensorProduct.CompatibleSMul ℤ (R p) K (MR p M) :=
    IsLocalization.tensorProduct_compatibleSMul S (R p) K (MR p M)
  let eps : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ℤ] MR p M) :=
    TensorProduct.equivOfCompatibleSMul ℤ (R p) K K (MR p M)
  have heps (c : K) (u : MR p M) :
      eps (c ⊗ₜ[R p] u) = c ⊗ₜ[ℤ] u := rfl
  let q0 : MR p M →ₗ[ℤ] (K ⊗[ZMod p] ModN (MR p M) p) :=
    ((TensorProduct.mk (ZMod p) K (ModN (MR p M) p) 1).restrictScalars ℤ).comp
      (ModN.mkQ p).toIntLinearMap
  let qf : (K ⊗[ℤ] MR p M) →ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p) :=
    q0.liftBaseChange K
  have hqf (c : K) (u : MR p M) :
      qf (c ⊗ₜ[ℤ] u) = c ⊗ₜ[ZMod p] ModN.mkQ p u := by
    simp [qf, q0, TensorProduct.smul_tmul']
  let d : ModN (MR p M) p →ₗ[ZMod p] (K ⊗[ℤ] MR p M) :=
    ModN.liftEquiv'.symm ⟨(TensorProduct.mk ℤ K (MR p M) 1).toAddMonoidHom, by
      intro u
      rw [← Nat.cast_smul_eq_nsmul K p, CharP.cast_eq_zero K p, zero_smul]⟩
  have hd (u : MR p M) : d (ModN.mkQ p u) = 1 ⊗ₜ[ℤ] u := by rfl
  let qb : (K ⊗[ZMod p] ModN (MR p M) p) →ₗ[K] (K ⊗[ℤ] MR p M) :=
    d.liftBaseChange K
  have hqb (c : K) (u : MR p M) :
      qb (c ⊗ₜ[ZMod p] ModN.mkQ p u) = c ⊗ₜ[ℤ] u := by
    simp [qb, hd, TensorProduct.smul_tmul']
  have hfb : qf.comp qb = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c u
    obtain ⟨u, rfl⟩ := (LinearMap.range (LinearMap.lsmul ℤ (MR p M) p)).mkQ_surjective u
    change qf (qb (c ⊗ₜ[ZMod p] ModN.mkQ p u)) = _
    rw [hqb, hqf]
    rfl
  have hbf : qb.comp qf = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c u
    change qb (qf (c ⊗ₜ[ℤ] u)) = c ⊗ₜ[ℤ] u
    rw [hqf, hqb]
  let qe : (K ⊗[ℤ] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p) :=
    LinearEquiv.ofLinear qf qb hfb hbf
  let psi : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p) :=
    eps.trans qe
  have hpsi (c : K) (u : MR p M) :
      psi (c ⊗ₜ[R p] u) = c ⊗ₜ[ZMod p] ModN.mkQ p u := by
    change qf (eps (c ⊗ₜ[R p] u)) = _
    rw [heps, hqf]
  refine ⟨h_H001.2, kap, hkap, ?_⟩
  refine ⟨phi, psi, hphi, hpsi, ?_, ?_⟩
  · intro f z
    have hf : phi.toLinearMap.comp (f.baseChange K) =
        ((f.baseChange (R p)).baseChange K).comp phi.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c m
      simp [hphi]
    exact DFunLike.congr_fun hf z
  · intro f
    let fbar : Module.End (ZMod p) (ModN (MR p M) p) :=
      ModN.liftEquiv'.symm ⟨(ModN.mkQ p).comp f.toAddMonoidHom, by
        intro u
        rw [← Nat.cast_smul_eq_nsmul (ZMod p) p, CharP.cast_eq_zero (ZMod p) p, zero_smul]⟩
    have hbar (u : MR p M) :
        fbar (ModN.mkQ p u) = ModN.mkQ p (f u) := by rfl
    refine ⟨fbar, hbar, ?_⟩
    intro z
    have hf : psi.toLinearMap.comp (f.baseChange K) =
        (fbar.baseChange K).comp psi.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c u
      simp [hpsi, hbar]
    exact DFunLike.congr_fun hf z

theorem T015 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) (h_T013 : PrincipalLattice p lam M y v) (h_T014 : ScalarReduction p K M) :
    ReducedBasis p lam K M x y h v := by
  classical
    intro a hag
    obtain ⟨b, hb⟩ := h_T013.2.1
    obtain ⟨c, hc⟩ := h_T013.2.2 b hb
    obtain ⟨hp, kap, hkap, hmaps⟩ := h_T014
    letI : CharP K p := hp
    letI : Algebra (R p) K := kap.toAlgebra
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    obtain ⟨phi, psi, hphi, hpsi, hcomm, hdesc⟩ := hmaps
    let beta : Module.Basis (Index lam) K (VK K M) := (c.baseChange K).map phi.symm
    have hbeta (i : Index lam) : phi (beta i) = 1 ⊗ₜ[R p] c i := by
      simp [beta]
    have hiota := h_T007.1.1
    have hcov : ∀ (f : Module.End ℤ M) (g : Module.End ℂ V),
        (∀ m : M, (f m : V) = g (m : V)) →
        ∀ u : MR p M, iota p M (f.baseChange (R p) u) = g (iota p M u) := by
      intro f g ha u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r m =>
        simp only [LinearMap.baseChange_tmul, iota, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply]
        rw [ha]
        exact (g.map_smul_of_tower r (m : V)).symm
      | add u w hu hw => simp only [map_add, hu, hw]
    have hact : ∀ (f : Module.End ℤ M) (g : Module.End ℂ V),
        (∀ m : M, (f m : V) = g (m : V)) →
        ∀ (i j : Index lam) (z : ℤ),
          g (e y v i.val) = (z : ℂ) • e y v j.val →
          f.baseChange K (beta i) = (z : K) • beta j := by
      intro f g ha i j z hz
      have hr : f.baseChange (R p) (c i) = z • c j := by
        apply hiota
        rw [hcov f g ha, hc, map_smul, hz, map_zsmul, hc]
        simp only [Int.cast_smul_eq_zsmul]
        exact smul_comm b z (e y v j.val)
      apply phi.injective
      rw [hcomm, hbeta, LinearMap.baseChange_tmul, hr, map_smul, hbeta]
      exact (TensorProduct.tmul_smul z (1 : K) (c j)).trans
        (Int.cast_smul_eq_zsmul (M := K ⊗[R p] MR p M) K z ((1 : K) ⊗ₜ[R p] c j)).symm
    have hzero : ∀ (f : Module.End ℤ M) (g : Module.End ℂ V),
        (∀ m : M, (f m : V) = g (m : V)) →
        ∀ i : Index lam, g (e y v i.val) = 0 → f.baseChange K (beta i) = 0 := by
      intro f g ha i hz
      simpa using hact f g ha i i 0 (by simpa using hz)
    refine ⟨beta, b, hb, ?_, ?_, ?_⟩
    · exact ⟨kap, phi, c, hphi, hc, hbeta⟩
    · simpa [Index] using Module.finrank_eq_card_basis beta
    · have hgen := h_T004.2.2.2.2.2.1.2.2
      intro i
      refine ⟨?_, ?_, ?_⟩
      · by_cases hi : i.val = 0
        · simp only [hi, if_pos]
          exact hzero a.x x hag.1 i (by simpa [hi] using (hgen i).1)
        · have hn : i.val - 1 < lam.toNat + 1 := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
          have he := (hgen i).1
          simp only [hi, if_false, extendFamily, dif_pos hn] at he
          have ht := hact a.x x hag.1 i ⟨i.val - 1, hn⟩ (lam - (i.val : ℤ) + 1) he
          simpa only [hi, if_false, extendFamily, dif_pos hn] using ht
      · by_cases hn : i.val + 1 < lam.toNat + 1
        · have he := (hgen i).2.1
          simp only [extendFamily, dif_pos hn] at he
          have ht := hact a.y y hag.2.1 i ⟨i.val + 1, hn⟩ ((i.val + 1 : ℕ) : ℤ) (by simpa using he)
          simpa [extendFamily, hn] using ht
        · have he : y (e y v i.val) = 0 := by
            simpa [extendFamily, hn] using (hgen i).2.1
          simpa [extendFamily, hn] using hzero a.y y hag.2.1 i he
      · exact hact a.h h hag.2.2.1 i i (lam - 2 * (i.val : ℤ)) (hgen i).2.2

theorem T016 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) (h_T013 : PrincipalLattice p lam M y v) (h_T014 : ScalarReduction p K M) (h_T015 : ReducedBasis p lam K M x y h v) :
    ScalarReduction p K M ∧ ReducedBasis p lam K M x y h v ∧ ReducedUnits lam K M x y h ∧ ∃ a : LatticeOps M, Agrees M x y h a := by
  classical
  have hn : (∀ r : ℕ, r ≤ lam.toNat → (r.factorial : K) ≠ 0) ∧
      (∀ j : Index lam, (Nat.choose lam.toNat j.val : K) ≠ 0) := by
    letI : CharP K p := h_H001.2
    have hlt : lam.toNat < p := by omega
    have hf : ∀ r : ℕ, r ≤ lam.toNat → (r.factorial : K) ≠ 0 := by
      intro r hr hz
      have hd := (CharP.cast_eq_zero_iff K p r.factorial).mp hz
      have := (h_H001.1.dvd_factorial).mp hd
      omega
    refine ⟨hf, ?_⟩
    intro j hj
    have he : (Nat.choose lam.toNat j.val : K) * (j.val.factorial : K) *
        ((lam.toNat - j.val).factorial : K) = (lam.toNat.factorial : K) := by
      simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : K))
        (Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ j.isLt))
    rw [hj, zero_mul, zero_mul] at he
    exact hf lam.toNat le_rfl he.symm
  have hdiv : ∀ a : LatticeOps M, Agrees M x y h a →
   (∀ r : ℕ, r ≤ lam.toNat →
   (a.X r).baseChange K = (r.factorial : K)⁻¹ • (a.x.baseChange K) ^ r ∧
   (a.Y r).baseChange K = (r.factorial : K)⁻¹ • (a.y.baseChange K) ^ r) := by
    have hfac : ∀ (f : Module.End ℤ M) (F : Module.End ℂ V) (D : ℕ → Module.End ℤ M),
     (∀ m : M, (f m : V) = F (m : V)) →
     (∀ r (m : M), (D r m : V) = divided F r (m : V)) →
     ∀ r, (r.factorial : K) • (D r).baseChange K = (f.baseChange K) ^ r := by
     intro f F D hf hD r
     have hp : ∀ n (m : M), ((f ^ n) m : V) = (F ^ n) (m : V) := by
       intro n
       induction n with
       | zero => intro m; rfl
       | succ n ih =>
         intro m
         simpa only [pow_succ', Module.End.mul_apply] using
           (hf ((f ^ n) m)).trans (congrArg F (ih m))
     have he : (r.factorial : ℤ) • D r = f ^ r := by
       ext m
       change (r.factorial : ℤ) • (D r m : V) = ((f ^ r) m : V)
       rw [hD, hp]
       simp [divided, LinearMap.smul_apply, smul_smul,
         ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℤ,
         Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)]
     have hk := congrArg (fun f : Module.End ℤ M => f.baseChange K) he
     simp only [LinearMap.baseChange_smul, LinearMap.baseChange_pow] at hk
     have hk' : (r.factorial : K) • (D r).baseChange K = (f.baseChange K) ^ r := by
       simpa only [Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul,
         natCast_zsmul] using hk
     exact hk'
    intro a ha r hr
    constructor
    · have he := congrArg (fun z : Module.End K (VK K M) => (r.factorial : K)⁻¹ • z)
        (hfac a.x x a.X ha.1 ha.2.2.2.1 r)
      simpa only [smul_smul, inv_mul_cancel₀ (hn.1 r hr), one_smul] using he
    · have he := congrArg (fun z : Module.End K (VK K M) => (r.factorial : K)⁻¹ • z)
        (hfac a.y y a.Y ha.2.1 ha.2.2.2.2 r)
      simpa only [smul_smul, inv_mul_cancel₀ (hn.1 r hr), one_smul] using he
  have hcanonical : ∀ a : LatticeOps M, Agrees M x y h a →
   ∃ beta : Module.Basis (Index lam) K (VK K M),
   GeneratorFormulas lam (fun i => beta i) (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) ∧
   ∀ i j k : Index lam,
   (a.X (lam.toNat - i.val) * (a.Y lam.toNat * a.X lam.toNat) *
     a.Y (lam.toNat - j.val)).baseChange K (beta k) =
   (Nat.choose lam.toNat j.val : K) • (if j = k then beta i else 0) := by
    classical
    have hlift : ∀ (f : Module.End ℤ M) (F : Module.End ℂ V),
     (∀ m : M, (f m : V) = F (m : V)) →
     ∀ u : MR p M, iota p M (f.baseChange (R p) u) = F (iota p M u) := by
     intro f F hf u
     induction u using TensorProduct.induction_on with
     | zero => simp
     | tmul r m =>
       change r • (f m : V) = F (r • (m : V))
       rw [hf]
       exact ((F.restrictScalars (R p)).map_smul r (m : V)).symm
     | add u w hu hw => simp only [map_add, hu, hw]
    intro a ha
    obtain ⟨beta, b, hb, ⟨kap, phi, c, hphi, hc, hbeta⟩, hdim, hgen⟩ := h_T015 a ha
    letI : Algebra (R p) K := kap.toAlgebra
    have hcomm : ∀ (f : Module.End ℤ M) (z : VK K M),
     phi (f.baseChange K z) = (f.baseChange (R p)).baseChange K (phi z) := by
     intro f z
     induction z using TensorProduct.induction_on with
     | zero => simp
     | tmul s m => simp only [LinearMap.baseChange_tmul, hphi]
     | add z w hz hw => simp only [map_add, hz, hw]
    obtain ⟨bC, hbC⟩ := h_T004.2.2.2.2.2.1.1
    refine ⟨beta, hgen, ?_⟩
    intro i j k
    let W : Module.End ℤ M := a.X (lam.toNat - i.val) *
     (a.Y lam.toNat * a.X lam.toNat) * a.Y (lam.toNat - j.val)
    let WC : Module.End ℂ V := divided x (lam.toNat - i.val) *
     (divided y lam.toNat * divided x lam.toNat) * divided y (lam.toNat - j.val)
    have hW : ∀ m : M, (W m : V) = WC (m : V) := by
     intro m
     simp only [W, WC, Module.End.mul_apply, ha.2.2.2.1, ha.2.2.2.2]
    have hWC : WC = (Nat.choose lam.toNat j.val : ℂ) • E lam bC i j := by
     have he := (h_T007.2 bC hbC i j).2.2.2.2.1
     have hn : (Nat.choose lam.toNat j.val : ℂ) ≠ 0 :=
       Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)))
     change E lam bC i j = (Nat.choose lam.toNat j.val : ℂ)⁻¹ • WC at he
     rw [he, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have haction : W.baseChange (R p) (c k) =
     (Nat.choose lam.toNat j.val : R p) • (if j = k then c i else 0) := by
     apply h_T007.1.1
     rw [hlift W WC hW, hc]
     rw [WC.map_smul, hWC]
     have he : E lam bC i j (e y v k.val) = if j = k then e y v i.val else 0 := by
       rw [← hbC k]
       simp only [E, LinearMap.smulRight_apply, Module.Basis.coord_apply,
         Module.Basis.repr_self, Finsupp.single_apply]
       by_cases hj : j = k
       · subst k; simp [hbC]
       · simp [hj, Ne.symm hj]
     simp only [LinearMap.smul_apply, he]
     split_ifs with hj
     · subst k
       rw [map_smul, hc]
       change b • ((Nat.choose lam.toNat j.val : ℂ) • e y v i.val) =
         (Nat.choose lam.toNat j.val : R p) • (b • e y v i.val)
       rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_comm]
       rfl
     · simp
    apply phi.injective
    rw [hcomm W, hbeta]
    simp only [LinearMap.baseChange_tmul, haction]
    rw [map_smul]
    split_ifs with hj
    · subst k
      rw [hbeta]
      simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
      simp only [Nat.cast_smul_eq_nsmul]
    · simp
  have htransport : ∀ (b0 b1 : Module.Basis (Index lam) K (VK K M))
   (X Y H : Module.End K (VK K M)),
   GeneratorFormulas lam (fun i => b0 i) X Y H →
   GeneratorFormulas lam (fun i => b1 i) X Y H →
   ∃ T : VK K M ≃ₗ[K] VK K M,
   (∀ i, T (b0 i) = b1 i) ∧
   (∀ u, T (X u) = X (T u)) ∧ (∀ u, T (Y u) = Y (T u)) := by
    classical
    intro b0 b1 X Y H h0 h1
    let T := b0.equiv b1 (Equiv.refl (Index lam))
    have hT : ∀ i, T (b0 i) = b1 i := by intro i; simp [T]
    have hext : ∀ n, T (extendFamily (F := K) lam (fun i => b0 i) n) =
     extendFamily (F := K) lam (fun i => b1 i) n := by
     intro n
     unfold extendFamily
     split_ifs <;> simp [hT]
    have hx : T.toLinearMap.comp X = X.comp T.toLinearMap := by
     apply b0.ext
     intro i
     change T (X (b0 i)) = X (T (b0 i))
     rw [(h0 i).1, hT, (h1 i).1]
     split_ifs <;> simp [hext]
    have hy : T.toLinearMap.comp Y = Y.comp T.toLinearMap := by
     apply b0.ext
     intro i
     change T (Y (b0 i)) = Y (T (b0 i))
     rw [(h0 i).2.1, hT, (h1 i).2.1, map_smul, hext]
    exact ⟨T, hT, (fun u => LinearMap.congr_fun hx u),
     (fun u => LinearMap.congr_fun hy u)⟩
  refine ⟨h_T014, h_T015, ?_, ?_⟩
  · refine ⟨hn.1, hn.2, ?_⟩
    intro a ha
    refine ⟨hdiv a ha, ?_⟩
    intro beta hgen
    obtain ⟨b0, hgen0, hact⟩ := hcanonical a ha
    have hdelta : ∀ i j k : Index lam,
        MatrixWord lam (fun r => (a.X r).baseChange K)
          (fun r => (a.Y r).baseChange K) i j (b0 k) =
        if j = k then b0 i else 0 := by
      intro i j k
      have he := hact i j k
      simp only [LinearMap.baseChange_mul] at he
      unfold MatrixWord
      rw [LinearMap.smul_apply, he, smul_smul, inv_mul_cancel₀ (hn.2 j), one_smul]
    obtain ⟨T, hT, hx, hy⟩ :=
      htransport b0 beta (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) hgen0 hgen
    have hpow : ∀ F : Module.End K (VK K M),
        (∀ u, T (F u) = F (T u)) →
        ∀ n u, T ((F ^ n) u) = (F ^ n) (T u) := by
      intro F hF n
      induction n with
      | zero => intro u; rfl
      | succ n ih =>
        intro u
        simp only [pow_succ', Module.End.mul_apply, hF, ih]
    have hX : ∀ r, r ≤ lam.toNat → ∀ u,
        T ((a.X r).baseChange K u) = (a.X r).baseChange K (T u) := by
      intro r hr u
      rw [(hdiv a ha r hr).1]
      simp only [LinearMap.smul_apply, map_smul, hpow _ hx]
    have hY : ∀ r, r ≤ lam.toNat → ∀ u,
        T ((a.Y r).baseChange K u) = (a.Y r).baseChange K (T u) := by
      intro r hr u
      rw [(hdiv a ha r hr).2]
      simp only [LinearMap.smul_apply, map_smul, hpow _ hy]
    intro i j k
    have hW : ∀ u,
        T (MatrixWord lam (fun r => (a.X r).baseChange K)
          (fun r => (a.Y r).baseChange K) i j u) =
        MatrixWord lam (fun r => (a.X r).baseChange K)
          (fun r => (a.Y r).baseChange K) i j (T u) := by
      intro u
      simp only [MatrixWord, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
        hX _ (Nat.sub_le _ _), hY _ (Nat.sub_le _ _), hX _ le_rfl, hY _ le_rfl]
    have he := congrArg T (hdelta i j k)
    rw [hW, hT] at he
    simpa only [apply_ite T, hT, map_zero] using he
  · rcases h_T007.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, ha⟩
    exact ha

theorem T017 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T016 : ScalarReduction p K M ∧ ReducedBasis p lam K M x y h v ∧ ReducedUnits lam K M x y h ∧ ∃ a : LatticeOps M, Agrees M x y h a) :
    ∀ (a : LatticeOps M) (W : Submodule K (VK K M)), Agrees M x y h a → Invariant W (a.x.baseChange K) → Invariant W (a.y.baseChange K) → Invariant W (a.h.baseChange K) → ∀ i j : Index lam, Invariant W (MatrixWord lam (fun r => (a.X r).baseChange K) (fun r => (a.Y r).baseChange K) i j) := by
  intro a W ha hx hy hh i j
  have hpowers : ∀ (f : Module.End K (VK K M)), Invariant W f →
      ∀ n : ℕ, Invariant W (f ^ n) := by
    intro f hf n
    induction n with
    | zero =>
        intro u hu
        simpa using hu
    | succ n ih =>
        intro u hu
        rw [pow_succ']
        exact hf _ (ih u hu)
  have hdiv := (h_T016.2.2.1.2.2 a ha).1
  have hX : ∀ r : ℕ, r ≤ lam.toNat → Invariant W ((a.X r).baseChange K) := by
    intro r hr
    rw [(hdiv r hr).1]
    intro u hu
    exact W.smul_mem _ (hpowers _ hx r u hu)
  have hY : ∀ r : ℕ, r ≤ lam.toNat → Invariant W ((a.Y r).baseChange K) := by
    intro r hr
    rw [(hdiv r hr).2]
    intro u hu
    exact W.smul_mem _ (hpowers _ hy r u hu)
  intro u hu
  unfold MatrixWord
  exact W.smul_mem _
    (hX (lam.toNat - i.val) (Nat.sub_le _ _) _
      (hY lam.toNat le_rfl _
        (hX lam.toNat le_rfl _
          (hY (lam.toNat - j.val) (Nat.sub_le _ _) u hu))))

theorem T018 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T016 : ScalarReduction p K M ∧ ReducedBasis p lam K M x y h v ∧ ReducedUnits lam K M x y h ∧ ∃ a : LatticeOps M, Agrees M x y h a) (h_T017 : ∀ (a : LatticeOps M) (W : Submodule K (VK K M)), Agrees M x y h a → Invariant W (a.x.baseChange K) → Invariant W (a.y.baseChange K) → Invariant W (a.h.baseChange K) → ∀ i j : Index lam, Invariant W (MatrixWord lam (fun r => (a.X r).baseChange K) (fun r => (a.Y r).baseChange K) i j)) :
    ∀ a : LatticeOps M, Agrees M x y h a → Simple (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) := by
  classical
  intro a ha
  rcases h_T016.2.1 a ha with ⟨beta, b, hb, hlift, hdim, hgen⟩
  have hmatrix := (h_T016.2.2.1.2.2 a ha).2 beta hgen
  have hnontrivial : Nontrivial (VK K M) :=
    nontrivial_of_ne (beta (⟨0, Nat.succ_pos _⟩ : Index lam)) 0
      (beta.ne_zero _)
  refine ⟨hnontrivial, ?_⟩
  intro W hx hy hh
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    have hwitness :
        ∃ (w : VK K M) (c : Index lam → K) (j : Index lam),
          w ∈ W ∧ w = ∑ k, c k • beta k ∧ w ≠ 0 ∧ c j ≠ 0 := by
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      have hc : ∃ j : Index lam, beta.repr w j ≠ 0 := by
        by_contra hc
        have hz : ∀ j : Index lam, beta.repr w j = 0 := by
          simpa only [not_exists, not_not] using hc
        apply hw0
        calc
          w = ∑ k, beta.repr w k • beta k := (beta.sum_repr w).symm
          _ = 0 := by simp [hz]
      obtain ⟨j, hj⟩ := hc
      exact ⟨w, fun k => beta.repr w k, j, hwW, (beta.sum_repr w).symm, hw0, hj⟩
    obtain ⟨w, c, j, hwW, hw, hw0, hcj⟩ := hwitness
    apply (Submodule.eq_top_iff_forall_basis_mem beta).2
    intro i
    let A : Module.End K (VK K M) :=
      MatrixWord lam (fun r => (a.X r).baseChange K) (fun r => (a.Y r).baseChange K) i j
    have hA : A w = c j • beta i := by
      rw [hw, map_sum]
      simp [A, map_smul, hmatrix, smul_ite]
    have hmem : c j • beta i ∈ W := by
      rw [← hA]
      exact h_T017 a W ha hx hy hh i j w hwW
    have hdiv := W.smul_mem (c j)⁻¹ hmem
    simpa [smul_smul, hcj] using hdiv

theorem T019 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = (lam + 1).toNat ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ Highest lam x h ∧ Simple x y h) (h_T016 : ScalarReduction p K M ∧ ReducedBasis p lam K M x y h v ∧ ReducedUnits lam K M x y h ∧ ∃ a : LatticeOps M, Agrees M x y h a) (h_T018 : ∀ a : LatticeOps M, Agrees M x y h a → Simple (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K)) :
    Target K M x y h := by
  rcases h_T016.2.2.2 with ⟨a, ha⟩
  exact ⟨a, ha, h_T018 a ha⟩

set_option Elab.async false in
theorem P {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = (lam + 1).toNat ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ Highest lam x h ∧ Simple x y h) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) (h_H005 : Admissible M x y) :
    Target K M x y h := by
  have h_T001 : Lowering lam x y h v := @T001 V instVAdd instVMod p lam K instK x y h v M h_H002 h_H003 h_H004
  have h_T002 : ∀ i : Index lam, e y v i.val ≠ 0 ∧ h (e y v i.val) = (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) • e y v i.val) := @T002 V instVAdd instVMod p lam K instK x y h v M h_H002 h_H004 h_T001
  have h_T003 : CoordinateCore lam x y h v := @T003 V instVAdd instVMod p lam K instK x y h v M h_H002 h_H003 h_T001 h_T002
  have h_T004 : Coordinates lam x y h v := @T004 V instVAdd instVMod p lam K instK x y h v M h_H002 h_T001 h_T002 h_T003
  have h_T005 : (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ := @T005 V instVAdd instVMod p lam K instK x y h v M h_H001
  have h_T006 : LocalLattice p lam M x y h := @T006 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_H003 h_H005 h_T004
  have h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v := @T007 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T004 h_T005 h_T006
  have h_T008 : ∀ i : Index lam, Ji p M y v i.val = J p M y v := @T008 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T004 h_T007
  have h_T009 : CommonModule p lam M y v := @T009 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T004 h_T007 h_T008
  have h_T010 : Function.Injective (qmul p M y v) ∧ (qmul p M y v).range = Submodule.span ℚ (J p M y v : Set ℂ) ∧ Module.Finite ℚ (ℚ ⊗[R p] J p M y v) := @T010 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T005 h_T009
  have h_T011 : RationalLine p M y v := @T011 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T004 h_T005 h_T007 h_T009 h_T010
  have h_T012 : ∃ b : ℂ, Principal p M y v b := @T012 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T005 h_T009 h_T011
  have h_T013 : PrincipalLattice p lam M y v := @T013 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T004 h_T007 h_T009 h_T011 h_T012
  have h_T014 : ScalarReduction p K M := @T014 V instVAdd instVMod p lam K instK x y h v M h_H001 h_T005 h_T007
  have h_T015 : ReducedBasis p lam K M x y h v := @T015 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T004 h_T007 h_T013 h_T014
  have h_T016 : ScalarReduction p K M ∧ ReducedBasis p lam K M x y h v ∧ ReducedUnits lam K M x y h ∧ ∃ a : LatticeOps M, Agrees M x y h a := @T016 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_T004 h_T007 h_T013 h_T014 h_T015
  have h_T017 : ∀ (a : LatticeOps M) (W : Submodule K (VK K M)), Agrees M x y h a → Invariant W (a.x.baseChange K) → Invariant W (a.y.baseChange K) → Invariant W (a.h.baseChange K) → ∀ i j : Index lam, Invariant W (MatrixWord lam (fun r => (a.X r).baseChange K) (fun r => (a.Y r).baseChange K) i j) := @T017 V instVAdd instVMod p lam K instK x y h v M h_H002 h_T016
  have h_T018 : ∀ a : LatticeOps M, Agrees M x y h a → Simple (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) := @T018 V instVAdd instVMod p lam K instK x y h v M h_T016 h_T017
  have h_T019 : Target K M x y h := @T019 V instVAdd instVMod p lam K instK x y h v M h_H001 h_H002 h_H003 h_T016 h_T018
  exact h_T019

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false

end AuditBExport

open Lean Meta Elab Command in
run_cmd do
  let result ← liftTermElabM do
    let info ← getConstInfo `Translation.P
    forallTelescope info.type fun xs body => do
      let mut retained := #[]
      let omitted : Array String := #[]
      for x in xs do
        let decl ← getFVarLocalDecl x
        if !omitted.contains decl.userName.toString then
          retained := retained.push x
      let exported ← mkForallFVars retained body
      let used := (collectLevelParams {} exported).params.toList
      return Json.mkObj [("parameters", toJson (info.levelParams.map Name.toString)),
        ("export_used_parameters", toJson (used.map Name.toString))]
  logInfo m!"YUI_ASSEMBLY_LEVELS_JSON:{result.compress}"
