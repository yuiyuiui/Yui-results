import Mathlib

universe u v w
open scoped BigOperators TensorProduct

namespace Reduction

def Stable {R : Type*} [Semiring R] {T : Type*} [AddCommMonoid T]
    [Module R T] (W : Submodule R T) (f : T → T) : Prop :=
  ∀ z ∈ W, f z ∈ W

noncomputable def dp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  (Nat.factorial r : ℂ)⁻¹ • f ^ r

noncomputable def e {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (y : Module.End ℂ V) (v : V) (i : Fin (lam.toNat + 1)) : V :=
  dp y i.val v

def IsBasisFamily {R : Type*} [CommRing R] {T : Type*} [AddCommGroup T]
    [Module R T] {n : ℕ} (a : Fin n → T) : Prop :=
  ∃ b : Module.Basis (Fin n) R T, ∀ i, b i = a i

def Scaled {M : Type*} [AddCommGroup M] [Module ℤ M]
    (m : ℕ) (A B : ℕ → Module.End ℤ M) (i j : Fin (m + 1)) : Module.End ℤ M :=
  ((Nat.factorial j.val * Nat.factorial (m - j.val) : ℕ) : ℤ) •
    (A (m - i.val) * B m * A m * B (m - j.val))

noncomputable def ComplexScaled {V : Type*} [AddCommGroup V] [Module ℂ V]
    (m : ℕ) (x y : Module.End ℂ V) (i j : Fin (m + 1)) : Module.End ℂ V :=
  ((Nat.factorial j.val * Nat.factorial (m - j.val) : ℕ) : ℂ) •
    (dp x (m - i.val) * dp y m * dp x m * dp y (m - j.val))

noncomputable def Fext (K : Type*) [Field K] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : Module.End ℤ M) : Module.End K (K ⊗[ℤ] M) :=
  f.baseChange K

noncomputable def U (K : Type*) [Field K] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (m : ℕ) (A B : ℕ → Module.End ℤ M)
    (i j : Fin (m + 1)) : Module.End K (K ⊗[ℤ] M) :=
  (Nat.factorial m : K)⁻¹ • Fext K (Scaled m A B i j)

def MatrixUnits {F : Type*} [Field F] {T : Type*} [AddCommGroup T] [Module F T]
    (n : ℕ) (C : Fin n → Fin n → Module.End F T) : Prop :=
  (∀ i j k l, C i j * C k l = if j = k then C i l else 0) ∧
    (∑ i, C i i) = 1

abbrev VK (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module ℤ M] :=
  M ⊗[ℤ] K

noncomputable instance originalModule (K : Type*) [Field K] (M : Type*)
    [AddCommGroup M] [Module ℤ M] : Module K (VK K M) :=
  let flip : VK K M ≃+ (K ⊗[ℤ] M) :=
    { toEquiv := (TensorProduct.comm ℤ M K).toEquiv
      map_add' := (TensorProduct.comm ℤ M K).map_add }
  flip.module K

def originalAction (K : Type*) [Field K] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : Module.End ℤ M) : Module.End ℤ (VK K M) :=
  TensorProduct.map f (LinearMap.id : K →ₗ[ℤ] K)

def Standing (p : ℕ) (K : Type*) [Field K] (lam : ℤ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (x y h : Module.End ℂ V) (v : V)
    (M : Submodule ℤ V) (A B : ℕ → Module.End ℤ M) : Prop :=
  Nat.Prime p ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ) ∧
  (Module.finrank ℂ V : ℤ) = lam + 1 ∧
  h * x - x * h = (2 : ℂ) • x ∧
  h * y - y * h = -(2 : ℂ) • y ∧ x * y - y * x = h ∧
  v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧
  (∀ W : Submodule ℂ V, Stable W x → Stable W y → Stable W h →
    W = ⊥ ∨ W = ⊤) ∧
  (∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℤ M,
    ∃ c : Module.Basis (Fin n) ℂ V, ∀ i, c i = (b i : V)) ∧
  (∀ r (z : M), (A r z : V) = dp x r (z : V)) ∧
  (∀ r (z : M), (B r z : V) = dp y r (z : V))

end Reduction

namespace YuiClosed
set_option autoImplicit false
theorem P : ∀ (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B), Nontrivial (Reduction.VK K M) ∧
  ∀ W : Submodule K (Reduction.VK K M),
    Reduction.Stable W (Reduction.originalAction K (A 1)) →
    Reduction.Stable W (Reduction.originalAction K (B 1)) →
    Reduction.Stable W (Reduction.originalAction K (A 1 * B 1 - B 1 * A 1)) →
    W = ⊥ ∨ W = ⊤ := by sorry
end YuiClosed
