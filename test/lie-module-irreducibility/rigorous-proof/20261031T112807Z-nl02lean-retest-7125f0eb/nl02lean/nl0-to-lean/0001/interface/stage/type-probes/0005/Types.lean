import Mathlib
open scoped TensorProduct
noncomputable section
namespace SL2Reduction
def Index (lam : ℤ) := Fin (lam.toNat + 1)
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
      (((lam - (i.val : ℤ) + 1 : ℤ) : F) • extendFamily lam b (i.val - 1))) ∧
    y (b i) = ((i.val + 1 : ℕ) : F) • extendFamily lam b (i.val + 1) ∧
    h (b i) = (((lam - 2 * (i.val : ℤ) : ℤ) : F) • b i)
def DividedFormulas {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (b : Index lam → U) (X Y : ℕ → Module.End F U) : Prop :=
  ∀ (i : Index lam) (r : ℕ),
    X r (b i) = (if r ≤ i.val then
      ((Nat.choose (lam.toNat - i.val + r) r : ℕ) : F) • extendFamily lam b (i.val - r)
      else 0) ∧
    Y r (b i) = ((Nat.choose (i.val + r) r : ℕ) : F) • extendFamily lam b (i.val + r)
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

end SL2Reduction
open SL2Reduction


set_option autoImplicit false
def __probe_0 :=
  (fun {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) => (Target K M x y h))
def __probe_1 :=
  (fun {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) => (GeneratorFormulas lam (fun i : Index lam => e y v i.val) x y h))
