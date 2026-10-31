import Mathlib
open scoped TensorProduct
namespace LR
abbrev L := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ
abbrev R (p : ℕ) := Subring.closure {q : ℚ | ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b}
abbrev C (p : ℕ) := RestrictScalars (R p) ℚ ℂ
abbrev I (l : ℤ) := Fin (l.toNat + 1)
abbrev MR (p : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
abbrev VK (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Submodule ℤ V) := K ⊗[ℤ] M
noncomputable def dp {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V := ((r.factorial : ℂ)⁻¹) • f ^ r

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
noncomputable def eNat (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dp y i v
def Stable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] (W : Submodule F A) (f : Module.End F A) : Prop := ∀ w ∈ W, f w ∈ W
def ComplexHyp (l : ℤ) (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) : Prop :=
  IsSl2Triple h x y ∧ Submodule.span ℂ ({x,y,h} : Set L) = ⊤ ∧
  (∀ s t : L, rho ⁅s,t⁆ = rho s * rho t - rho t * rho s) ∧
  FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l.toNat + 1 ∧
  Nontrivial V ∧
  (∀ W : Submodule ℂ V, (∀ t : L, Stable W (rho t)) → W = ⊥ ∨ W = ⊤) ∧
  (∃ w : V, w ≠ 0 ∧ rho x w = 0 ∧ rho h w = (l : ℂ) • w)
def Admissible (rho : L →ₗ[ℂ] Module.End ℂ V) (x y : L) (M : Submodule ℤ V) : Prop :=
  (∃ (ι : Type) (b : Module.Basis ι ℤ M) (bc : Module.Basis ι ℂ V), ∀ i, (b i : V) = bc i) ∧
  (∀ r : ℕ, ∀ m ∈ M, dp (rho x) r m ∈ M ∧ dp (rho y) r m ∈ M)
def Strings (l : ℤ) (a d t : Module.End ℂ V) (v : V) : Prop :=
  (∀ r : ℕ, t ((d ^ r) v) = ((l : ℂ) - 2 * (r : ℂ)) • (d ^ r) v) ∧
  (∀ r : ℕ, 0 < r → a ((d ^ r) v) = ((r : ℂ) * ((l : ℂ) - (r : ℂ) + 1)) • (d ^ (r-1)) v)
def BasisString (l : ℤ) (d : Module.End ℂ V) (v : V) : Prop :=
  ∃ b : Module.Basis (I l) ℂ V, (∀ i, b i = eNat d v i.val) ∧
    (∀ r : ℕ, l.toNat < r → (d ^ r) v = 0)
def Matrices {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
    (l : ℤ) (a d t : Module.End F A) (e : ℕ → A) : Prop :=
  a (e 0) = 0 ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → a (e i) = ((l : F) - (i : F) + 1) • e (i-1)) ∧
  (∀ i : ℕ, i < l.toNat → d (e i) = ((i : F)+1) • e (i+1)) ∧
  d (e l.toNat) = 0 ∧
  (∀ i : ℕ, i ≤ l.toNat → t (e i) = ((l : F) - 2*(i : F)) • e i)
def DividedMatrices (l : ℤ) (a d : Module.End ℂ V) (v : V) : Prop :=
  ∀ r i : ℕ, i ≤ l.toNat →
    dp a r (eNat d v i) =
      (if r ≤ i then (Nat.choose (l.toNat-i+r) r : ℂ) • eNat d v (i-r) else 0) ∧
    dp d r (eNat d v i) =
      (if i+r ≤ l.toNat then (Nat.choose (i+r) r : ℂ) • eNat d v (i+r) else 0)
def N1 (l : ℤ) (a d t : Module.End ℂ V) (v : V) : Prop :=
  0 < l+1 ∧ Fintype.card (I l) = (l+1).toNat ∧ Strings l a d t v ∧
  BasisString l d v ∧ Matrices l a d t (eNat d v) ∧ DividedMatrices l a d v
noncomputable def unit (l : ℤ) (b : Module.Basis (I l) ℂ V) (i j : I l) : Module.End ℂ V :=
  (b.coord j).smulRight (b i)
def BasisSpec (l : ℤ) (d : Module.End ℂ V) (v : V) (b : Module.Basis (I l) ℂ V) : Prop :=
  ∀ i, b i = eNat d v i.val
def LocalRingSpec (p : ℕ) : Prop :=
  (∀ q : ℚ, q ∈ R p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b) ∧
  (∀ b : ℤ, ¬ (p : ℤ) ∣ b → IsUnit (b : R p))
def SmallUnits (p : ℕ) (l : ℤ) : Prop :=
  (∀ r : ℕ, r ≤ l.toNat → ¬ p ∣ r.factorial ∧ IsUnit (r.factorial : R p)) ∧
  (∀ j : I l, IsUnit (Nat.choose l.toNat j.val : R p))
def IotaSpec (p : ℕ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V) : Prop :=
  (∀ (r : R p) (m : M), f (r ⊗ₜ[ℤ] m) = (((r : ℚ) : ℂ)) • (m : V)) ∧
  (∀ (r : R p) (z : MR p M), f (r • z) = (((r : ℚ) : ℂ)) • f z)
def LocalBasis (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V) : Prop :=
  Function.Injective f ∧
  Nonempty (Module.Basis (I l) (R p) (MR p M)) ∧
  Submodule.span ℂ (Set.range f) = ⊤
def Preserved (p : ℕ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V) (a d : Module.End ℂ V) : Prop :=
  (∀ r : ℕ, ∀ m ∈ M, dp a r m ∈ M ∧ dp d r m ∈ M) ∧
  (∀ r : ℕ, ∀ z : MR p M, dp a r (f z) ∈ Set.range f ∧ dp d r (f z) ∈ Set.range f)
def UnitIdentities (l : ℤ) (a d : Module.End ℂ V) (b : Module.Basis (I l) ℂ V) : Prop :=
  ∀ i j : I l,
    dp d l.toNat * dp a l.toNat = unit l b (Fin.last l.toNat) (Fin.last l.toNat) ∧
    dp a (l.toNat-i.val) * (dp d l.toNat * dp a l.toNat) = unit l b i (Fin.last l.toNat) ∧
    (dp d l.toNat * dp a l.toNat) * dp d (l.toNat-j.val) = (Nat.choose l.toNat j.val : ℂ) • unit l b (Fin.last l.toNat) j
def AllUnits (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V)
    (a d : Module.End ℂ V) (b : Module.Basis (I l) ℂ V) : Prop :=
  ∀ i j : I l,
    unit l b i j = ((Nat.choose l.toNat j.val : ℂ)⁻¹) •
      (dp a (l.toNat-i.val) * (dp d l.toNat * dp a l.toNat) * dp d (l.toNat-j.val)) ∧
    (∀ z : MR p M, unit l b i j (f z) ∈ Set.range f)
end LR

set_option autoImplicit false
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => LR.N1 l (rho x) (rho y) (rho h) v)
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => LR.LocalRingSpec p)
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => ∀ f : LR.MR p M →ₗ[ℤ] V, LR.IotaSpec p M f)
