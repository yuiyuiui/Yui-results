import Mathlib

namespace YuiObjects

noncomputable def dividedPower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((Nat.factorial r : ℂ)⁻¹) • (a ^ r)

def stable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (a : Module.End F V) (W : Submodule F V) : Prop :=
  ∀ w ∈ W, a w ∈ W

def highestWeightData {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℕ) (h x y : Module.End ℂ V) (v : V) : Prop :=
  v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧
  h * x - x * h = (2 : ℂ) • x ∧
  h * y - y * h = (-2 : ℂ) • y ∧
  x * y - y * x = h ∧ Module.finrank ℂ V = lam + 1

def admissibleLattice {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℕ) (x y : Module.End ℂ V) (M : Submodule ℤ V) : Prop :=
  (∃ (b : Module.Basis (Fin (lam + 1)) ℤ M)
      (e : Module.Basis (Fin (lam + 1)) ℂ V), ∀ i, (b i : V) = e i) ∧
  (∀ (r : ℕ) (m : M), dividedPower x r (m : V) ∈ M) ∧
  (∀ (r : ℕ) (m : M), dividedPower y r (m : V) ∈ M)

def matrixUnits {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype I] [DecidableEq I] (f : I → I → Module.End F V) : Prop :=
  (∀ i j k l, f i j * f k l = if j = k then f i l else 0) ∧
  (∑ i, f i i) = 1

end YuiObjects

set_option autoImplicit false
def __probe_0 :=
  (fun (K : Type) [instK : Field K] (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (M : Submodule ℤ V) => (Module K (TensorProduct ℤ M K)))
def __probe_1 :=
  (fun (K : Type) [instK : Field K] (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (M : Submodule ℤ V) => (Module K (TensorProduct ℤ K M)))
def __probe_2 :=
  (fun (K : Type) [instK : Field K] (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (M : Submodule ℤ V) => (@TensorProduct.comm))
def __probe_3 :=
  (fun (K : Type) [instK : Field K] (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (M : Submodule ℤ V) => (@LinearMap.restrictScalars))
