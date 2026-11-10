import Mathlib
open scoped TensorProduct
open Module
universe u v
namespace SL2Lattice
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
noncomputable def dp (t : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  (Nat.factorial r : ℂ)⁻¹ • t ^ r
noncomputable def vec (y : Module.End ℂ V) (w : V) (i : ℕ) : V := dp y i w
def n (l : ℤ) : ℕ := l.toNat + 1
def coeff (l : ℤ) (j : ℕ) : ℤ := (Nat.choose l.toNat j : ℤ)
def detCoeff (l : ℤ) : ℤ := ∏ j : Fin (n l), coeff l j.val
def otherCoeff (l : ℤ) (i : Fin (n l)) : ℤ :=
  ∏ j ∈ (Finset.univ : Finset (Fin (n l))).erase i, coeff l j.val
noncomputable def raw (l : ℤ) (x y : Module.End ℂ V) (i j : Fin (n l)) : Module.End ℂ V :=
  dp x (l.toNat - i.val) * dp y l.toNat * dp x l.toNat * dp y (l.toNat - j.val)
def Stable (M : Submodule ℤ V) (t : Module.End ℂ V) : Prop :=
  ∀ m : V, m ∈ M → t m ∈ M
def Inv {R : Type v} [Field R] {U : Type u} [AddCommGroup U] [Module R U]
    (W : Submodule R U) (t : Module.End R U) : Prop :=
  ∀ w : U, w ∈ W → t w ∈ W
structure Actions (M : Submodule ℤ V) (x y h : Module.End ℂ V) where
  xZ : Module.End ℤ M
  yZ : Module.End ℤ M
  hZ : Module.End ℤ M
  XZ : ℕ → Module.End ℤ M
  YZ : ℕ → Module.End ℤ M
  x_eq : ∀ m : M, (xZ m : V) = x (m : V)
  y_eq : ∀ m : M, (yZ m : V) = y (m : V)
  h_eq : ∀ m : M, (hZ m : V) = h (m : V)
  X_eq : ∀ r (m : M), (XZ r m : V) = dp x r (m : V)
  Y_eq : ∀ r (m : M), (YZ r m : V) = dp y r (m : V)
def rawZ {M : Submodule ℤ V} {x y h : Module.End ℂ V}
    (a : Actions M x y h) (l : ℤ) (i j : Fin (n l)) : Module.End ℤ M :=
  a.XZ (l.toNat - i.val) * a.YZ l.toNat * a.XZ l.toNat * a.YZ (l.toNat - j.val)
noncomputable def red (K : Type v) [Field K] {M : Submodule ℤ V}
    (t : Module.End ℤ M) : Module.End K (TensorProduct ℤ K M) :=
  t.baseChange K
noncomputable def matrixUnit (K : Type v) [Field K] {M : Submodule ℤ V}
    {x y h : Module.End ℂ V} (a : Actions M x y h) (l : ℤ)
    (i j : Fin (n l)) : Module.End K (TensorProduct ℤ K M) :=
  (coeff l j.val : K)⁻¹ • red K (rawZ a l i j)
end SL2Lattice
open SL2Lattice

namespace YuiClosed
set_option autoImplicit false
theorem P : ∀ (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))), Nontrivial (TensorProduct ℤ K M) ∧ Nonempty (Actions M x y h) ∧ (∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) → W = ⊥ ∨ W = ⊤) := by sorry
end YuiClosed
