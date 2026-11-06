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

namespace Local_T007
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "(ell lam : ℤ) = lam ∧ (ell lam : ℂ) = (lam : ℂ)" := by
  have he : (ell lam : ℤ) = lam := Int.toNat_of_nonneg h_H003.1
  refine ⟨he, ?_⟩
  exact_mod_cast he

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ w : V, h (y w) = y (h w) + (-2 : ℂ) • y w" := by
  intro w
  have hc := congrArg (fun f : Module.End ℂ V => f w) h_H005.2.2.2.2.1
  have hc' : h (y w) - y (h w) = (-2 : ℂ) • y w := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] using hc
  exact sub_eq_iff_eq_add'.mp hc'

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)" := by
  have he := (@yui_aux_0001 p K instK lam V instV instCV x y h v M h_H003 h_H005).2
  have hc := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_H003 h_H005
  intro r
  induction r with
  | zero => simpa [he] using h_H005.2.2.1
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, hc, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ w : V, x (y w) = y (x w) + h w" := by
  intro w
  have hc := congrArg (fun f : Module.End ℂ V => f w) h_H005.2.2.2.2.2
  have hc' : x (y w) - y (x w) = h w := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply] using hc
  exact sub_eq_iff_eq_add'.mp hc'

end Local_T007
open Local_T007 in
theorem T007 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v)) := by
  have he := @yui_aux_0001 p K instK lam V instV instCV x y h v M h_H003 h_H005
  have hh := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_H003 h_H005
  have hc := @yui_aux_0004 p K instK lam V instV instCV x y h v M h_H003 h_H005
  refine ⟨he.1, Nat.succ_pos _, hh, ?_⟩
  have hy (r : ℕ) : y ((y ^ r) v) = (y ^ (r + 1)) v := by
    rw [pow_succ', Module.End.mul_apply]
  intro r
  induction r with
  | zero =>
    simpa [hc, h_H005.2.1, he.2] using h_H005.2.2.1
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, hc, ih, map_smul, hh (r + 1), hy r, ← add_smul]
    congr 1
    push_cast
    ring

#check @T007
#print axioms T007

end Translation
