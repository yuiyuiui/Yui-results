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

namespace Translation
set_option autoImplicit false

namespace Local_T008
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ r : ℕ, r ≤ ell lam → (y ^ r) v ≠ 0" := by
  intro r
  induction r with
  | zero =>
      intro _
      simpa using h_H005.1
  | succ r ih =>
      intro hr hz
      have hn : ell lam ≠ r := by omega
      have hc : (ell lam : ℂ) - (r : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
      have hs : ((r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero r)
      have hv : (y ^ r) v ≠ 0 := ih (by omega)
      have he := h_T007.2.2.2 r
      rw [hz, map_zero] at he
      exact (smul_ne_zero (mul_ne_zero hs hc) hv) he.symm

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "(∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧ Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ))" := by
  constructor
  · intro i
    have hn : (y ^ i.val) v ≠ 0 :=
      (@yui_aux_0001 p K instK lam V instV instCV x y h v M h_T007 h_H004 h_H005) i.val (by have := i.isLt; omega)
    have hf : (Nat.factorial i.val : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    constructor
    · simpa only [ev, dividedPower, LinearMap.smul_apply] using smul_ne_zero (inv_ne_zero hf) hn
    · simp only [ev, dividedPower, LinearMap.smul_apply, map_smul]
      rw [h_T007.2.2.1 i.val, smul_comm]
  · intro i j he
    apply Fin.ext
    have hc : (i.val : ℂ) = (j.val : ℂ) := by
      linear_combination (-1 / 2 : ℂ) * he
    exact_mod_cast hc

end Local_T008
open Local_T008 in
theorem T008 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) :
    (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) := by
  classical
  have he := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T007 h_H004 h_H005
  have hli : LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) := by
    apply h.eigenvectors_linearIndependent' (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) he.2
    intro i
    exact ⟨Module.End.mem_eigenspace_iff.mpr (he.1 i).2, (he.1 i).1⟩
  letI : FiniteDimensional ℂ V := h_H004.1
  have hdZ : (Module.finrank ℂ V : ℤ) = ((ell lam + 1 : ℕ) : ℤ) := by
    push_cast
    rw [h_T007.1]
    exact h_H004.2.1
  have hd : Module.finrank ℂ V = ell lam + 1 := by exact_mod_cast hdZ
  have hc : Fintype.card (Idx lam) = Module.finrank ℂ V := by
    simpa only [Idx, Fintype.card_fin] using hd.symm
  refine ⟨he.1, he.2, hli, ?_⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' (fun i : Idx lam => ev y v i.val) hli hc, ?_⟩
  intro i
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℂ) (fun i : Idx lam => ev y v i.val) hli hc) i

#check @T008
#print axioms T008

end Translation
