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

namespace YuiObjects
noncomputable def latticeEnd {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : Submodule ℤ V) (f : Module.End ℂ V) : Module.End ℤ M :=
  @dite (Module.End ℤ M) (∀ z ∈ M, f z ∈ M)
    (Classical.propDecidable _) (fun hs => (f.restrictScalars ℤ).restrict hs) (fun _ => 0)
end YuiObjects

universe uK uV
namespace YuiObjects
abbrev ell (lam : ℤ) : ℕ := lam.toNat
abbrev Idx (lam : ℤ) := Fin (ell lam + 1)
noncomputable def ev {V : Type*} [AddCommGroup V] [Module ℂ V]
    (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dividedPower y i v
def coeff (lam : ℤ) (j : Idx lam) : ℕ := Nat.choose (ell lam) j.val
def coeffProd (lam : ℤ) : ℕ := ∏ j : Idx lam, coeff lam j
def coeffOmit (lam : ℤ) (i : Idx lam) : ℕ :=
  ∏ j ∈ (Finset.univ.erase i), coeff lam j
noncomputable def projector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (x y : Module.End ℂ V) : Module.End ℂ V :=
  dividedPower y (ell lam) * dividedPower x (ell lam)
noncomputable def integralMatrix {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (x y : Module.End ℂ V) (i j : Idx lam) : Module.End ℂ V :=
  dividedPower x (ell lam - i.val) * projector lam x y *
    dividedPower y (ell lam - j.val)
abbrev TensorLeft (K M : Type*) [Field K] [AddCommGroup M] := TensorProduct ℤ K M
abbrev TensorRight (K M : Type*) [Field K] [AddCommGroup M] := TensorProduct ℤ M K
noncomputable instance rightTensorModule (K M : Type*) [Field K] [AddCommGroup M] :
    Module K (TensorRight K M) :=
  (TensorProduct.comm ℤ M K).toAddEquiv.module K
noncomputable def tensorSwap (K M : Type*) [Field K] [AddCommGroup M] :
    TensorRight K M ≃ₗ[K] TensorLeft K M :=
  (TensorProduct.comm ℤ M K).toAddEquiv.linearEquiv K
noncomputable def hat {K M : Type*} [Field K] [AddCommGroup M]
    (f : Module.End ℤ M) : Module.End K (TensorLeft K M) := f.baseChange K
noncomputable def induced {K M : Type*} [Field K] [AddCommGroup M]
    (f : Module.End ℤ M) : Module.End K (TensorRight K M) :=
  (tensorSwap K M).symm.toLinearMap.comp ((hat (K := K) f).comp (tensorSwap K M).toLinearMap)
noncomputable def scaledMatrix {K V : Type*} [Field K] [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (x y : Module.End ℂ V) (M : Submodule ℤ V)
    (i j : Idx lam) : Module.End K (TensorLeft K M) :=
  ((coeff lam j : K)⁻¹) • hat (K := K) (latticeEnd M (integralMatrix lam x y i j))
end YuiObjects
open YuiObjects

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ (b : Module.Basis (Idx lam) ℂ V), (∀ i, b i = ev y v i.val) → ∀ w : V, ∀ i : Idx lam, b.repr (h w) i = ((ell lam : ℂ) - 2 * (i.val : ℂ)) * b.repr w i" := by
  classical
  intro b hb w i
  have he : ∀ j : Idx lam, h (b j) = ((ell lam : ℂ) - 2 * (j.val : ℂ)) • b j := by
    intro j
    simpa only [hb] using (h_T008.1 j).2
  have hh := congrArg (fun z : V => b.repr z i) (congrArg h (b.sum_repr w))
  simp only [map_sum, map_smul, he, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul] at hh
  rw [← hh, Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [hji]
  · simp

theorem checked (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "(∀ r : ℕ, ell lam < r → (y ^ r) v = 0)" := by
  classical
  obtain ⟨b, hb⟩ := h_T008.2.2.2
  have hc := @yui_aux_0001 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005 b hb
  have hz : (y ^ (ell lam + 1)) v = 0 := by
    apply b.repr.injective
    apply Finsupp.ext
    intro i
    have hh := congrArg (fun z : V => b.repr z i) (h_T007.2.2.1 (ell lam + 1))
    rw [hc] at hh
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hh
    have hi : i.val ≤ ell lam := by have := i.isLt; omega
    have hiC : (i.val : ℂ) ≠ ((ell lam + 1 : ℕ) : ℂ) := by
      exact_mod_cast (show i.val ≠ ell lam + 1 by omega)
    have hn : (ell lam : ℂ) - 2 * (i.val : ℂ) -
        ((ell lam : ℂ) - 2 * ((ell lam + 1 : ℕ) : ℂ)) ≠ 0 := by
      intro hz
      apply hiC
      linear_combination -(1 / 2 : ℂ) * hz
    have hp : ((ell lam : ℂ) - 2 * (i.val : ℂ) -
        ((ell lam : ℂ) - 2 * ((ell lam + 1 : ℕ) : ℂ))) *
        b.repr ((y ^ (ell lam + 1)) v) i = 0 := by linear_combination hh
    simpa using (mul_eq_zero.mp hp).resolve_left hn
  intro r hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show ell lam + 1 ≤ r by omega)
  rw [add_comm, pow_add, Module.End.mul_apply, hz, map_zero]
#check @checked
#print axioms checked
end YuiAuxiliary
