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
namespace YuiPortTypes
abbrev T005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  ∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤
end YuiPortTypes

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

namespace Local_T001
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

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
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

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "ev y v 0 = v ∧ (∀ n : ℕ, y (ev y v n) = ((n + 1 : ℕ) : ℂ) • ev y v (n + 1)) ∧ (∀ n : ℕ, x (ev y v (n + 1)) = ((ell lam : ℂ) - (n : ℂ)) • ev y v n) ∧ (∀ n : ℕ, ell lam < n → ev y v n = 0)" := by
  have hf : ∀ n : ℕ, (Nat.factorial n : ℂ) ≠ 0 := fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  refine ⟨by simp [ev, dividedPower], ?_, ?_, ?_⟩
  · intro n
    simp only [ev, dividedPower, LinearMap.smul_apply, map_smul, pow_succ',
      Module.End.mul_apply, smul_smul]
    congr 1
    push_cast [Nat.factorial_succ]
    field_simp
  · intro n
    simp only [ev, dividedPower, LinearMap.smul_apply, map_smul, h_T007.2.2.2,
      smul_smul]
    congr 1
    push_cast [Nat.factorial_succ]
    field_simp
  · intro n hn
    simp [ev, dividedPower, @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005 n hn]

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ (r i : ℕ), i ≤ ell lam → r ≤ i → (x ^ r) (ev y v i) = (((Nat.factorial (ell lam - i + r) : ℂ) / (Nat.factorial (ell lam - i) : ℂ))) • ev y v (i - r)" := by
  have hs := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have hf : ∀ n : ℕ, (Nat.factorial n : ℂ) ≠ 0 := fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  intro r
  induction r with
  | zero =>
    intro i hi hr
    simp [hf]
  | succ r ih =>
    intro i hi hr
    rw [pow_succ', Module.End.mul_apply, ih i hi (by omega), map_smul]
    have hn : i - r = (i - (r + 1)) + 1 := by omega
    rw [hn, hs.2.2.1, smul_smul]
    have hc : (ell lam : ℂ) - ((i - (r + 1) : ℕ) : ℂ) =
        ((ell lam - i + r + 1 : ℕ) : ℂ) := by
      rw [← Nat.cast_sub (show i - (r + 1) ≤ ell lam by omega)]
      congr 1
      omega
    rw [hc]
    congr 1
    simp only [Nat.succ_eq_add_one, ← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

theorem yui_aux_0005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ (r i : ℕ), (y ^ r) (ev y v i) = (((Nat.factorial (i + r) : ℂ) / (Nat.factorial i : ℂ))) • ev y v (i + r)" := by
  have hs := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have hf : ∀ n : ℕ, (Nat.factorial n : ℂ) ≠ 0 := fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  intro r
  induction r with
  | zero => intro i; simp [hf]
  | succ r ih =>
    intro i
    rw [pow_succ', Module.End.mul_apply, ih i, map_smul, hs.2.1, smul_smul]
    simp only [Nat.succ_eq_add_one, ← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem yui_aux_0006 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ (r i : ℕ), i ≤ ell lam → i < r → (x ^ r) (ev y v i) = 0" := by
  have hs := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have hx := @yui_aux_0004 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  intro r i hi hr
  have hz : (x ^ (i + 1)) (ev y v i) = 0 := by
    rw [pow_succ', Module.End.mul_apply, hx i i hi le_rfl]
    simp [map_smul, hs.1, h_H005.2.1]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ r by omega)
  rw [add_comm, pow_add, Module.End.mul_apply, hz, map_zero]

theorem yui_aux_0007 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) : yui_aux_type% "∀ n r : ℕ, (Nat.factorial r : ℂ)⁻¹ * ((Nat.factorial (n + r) : ℂ) / (Nat.factorial n : ℂ)) = (Nat.choose (n + r) r : ℂ)" := by
  intro n r
  rw [Nat.cast_choose ℂ (show r ≤ n + r by omega), Nat.add_sub_cancel_right]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end Local_T001
open Local_T001 in
theorem T001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0) := by
  have hs := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have ht := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have hx := @yui_aux_0004 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have hy := @yui_aux_0005 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have hxz := @yui_aux_0006 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  have hbin := @yui_aux_0007 p K instK lam V instV instCV x y h v M h_T007 h_T008 h_H003 h_H004 h_H005
  refine ⟨h_T007.1, h_T007.2.1, h_T008.2.2.2, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hs.1] using h_H005.2.1
  · intro i hi
    have hle : i.val ≤ ell lam := by have := i.isLt; omega
    have hn : i.val - 1 + 1 = i.val := by omega
    have hc : (ell lam : ℂ) - ((i.val - 1 : ℕ) : ℂ) =
        ((ell lam - i.val + 1 : ℕ) : ℂ) := by
      rw [Nat.cast_add, Nat.cast_sub hle,
        Nat.cast_sub (show 1 ≤ i.val by omega), Nat.cast_one]
      ring
    simpa only [hn, hc] using hs.2.2.1 (i.val - 1)
  · intro i hi
    exact hs.2.1 i.val
  · rw [hs.2.1, hs.2.2.2 (ell lam + 1) (by omega), smul_zero]
  · intro i
    exact (h_T008.1 i).2
  · intro r i
    have hi : i.val ≤ ell lam := by have := i.isLt; omega
    by_cases hr : r ≤ i.val
    · rw [if_pos hr]
      simp only [dividedPower, LinearMap.smul_apply, hx r i.val hi hr, smul_smul,
        hbin]
    · rw [if_neg hr]
      simp only [dividedPower, LinearMap.smul_apply,
        hxz r i.val hi (by omega), smul_zero]
  · intro r i
    by_cases hr : i.val + r ≤ ell lam
    · rw [if_pos hr]
      simp only [dividedPower, LinearMap.smul_apply, hy r i.val, smul_smul, hbin]
    · rw [if_neg hr]
      simp only [dividedPower, LinearMap.smul_apply, hy r i.val,
        hs.2.2.2 (i.val + r) (by omega), smul_zero]

namespace Local_T002
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧ projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧ (∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧ (∀ i j k : Idx lam, integralMatrix lam x y i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0)" := by
  classical
  rcases h_T001 with ⟨hl, hn, hb, hy0, hx0, hx1, hy1, hyend, hh, hx, hy⟩
  have hc (j : Idx lam) : 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j := by
    have hj : j.val ≤ ell lam := by omega
    exact ⟨Nat.choose_pos hj, Nat.choose_mul_factorial_mul_factorial hj, Nat.choose_symm hj⟩
  have htop : projector lam x y (ev y v (ell lam)) = ev y v (ell lam) := by
    have ht := hx (ell lam) (⟨ell lam, by omega⟩ : Idx lam)
    have hz := hy (ell lam) (⟨0, by omega⟩ : Idx lam)
    simp only [Fin.val_mk, le_refl, if_true, Nat.sub_self, Nat.zero_add, Nat.choose_self, Nat.cast_one, one_smul] at ht hz
    simpa only [projector, Module.End.mul_apply, ht, hz]
  have hlow (k : ℕ) (hk : k < ell lam) : projector lam x y (ev y v k) = 0 := by
    have ht := hx (ell lam) (⟨k, by omega⟩ : Idx lam)
    simp only [Fin.val_mk, show ¬ell lam ≤ k by omega, if_false] at ht
    simp only [projector, Module.End.mul_apply, ht, map_zero]
  refine ⟨hc, htop, hlow, ?_⟩
  intro i j k
  have hi : i.val ≤ ell lam := by omega
  have hj : j.val ≤ ell lam := by omega
  have hk : k.val ≤ ell lam := by omega
  have hxi := hx (ell lam - i.val) (⟨ell lam, by omega⟩ : Idx lam)
  simp only [Fin.val_mk, Nat.sub_self, Nat.zero_add, Nat.choose_self, Nat.cast_one, one_smul, Nat.sub_sub_self hi, if_pos (Nat.sub_le _ _)] at hxi
  change dividedPower x (ell lam - i.val) (projector lam x y (dividedPower y (ell lam - j.val) (ev y v k.val))) = _
  rw [hy]
  by_cases hkj : k = j
  · subst k
    have he : j.val + (ell lam - j.val) = ell lam := by omega
    rw [if_pos (by omega), he, map_smul, htop, map_smul, hxi, (hc j).2.2]
    simp
  · rw [if_neg hkj]
    by_cases hlt : k.val < j.val
    · rw [if_pos (by omega), map_smul, hlow _ (by omega), smul_zero, map_zero]
    · rw [if_neg (by
        have : k.val ≠ j.val := fun he => hkj (Fin.ext he)
        omega), map_zero, map_zero]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ (f : Module.End ℂ V) (hf : ∀ z ∈ M, f z ∈ M) (m : M), (latticeEnd M f m : V) = f (m : V)" := by
  intro f hf m
  unfold latticeEnd
  rw [dif_pos hf]
  rfl

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ (n : ℕ) (z : V), (n : ℤ) • z = (n : ℂ) • z" := by
  intro n z
  simpa only [Int.cast_natCast] using (Int.cast_smul_eq_zsmul ℂ (n : ℤ) z).symm

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧ (∀ i j k l : Idx lam, integralMatrix lam x y i j * integralMatrix lam x y k l = if j = k then (coeff lam j : ℤ) • integralMatrix lam x y i l else 0) ∧ (∑ i : Idx lam, (coeffOmit lam i : ℤ) • integralMatrix lam x y i i) = (coeffProd lam : ℤ) • (1 : Module.End ℂ V)" := by
  classical
  have ha := (@yui_aux_0001 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006).2.2.2
  have hz := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  obtain ⟨b, hb⟩ := h_T001.2.2.1
  have hp (i : Idx lam) : coeffProd lam = coeff lam i * coeffOmit lam i := by
    exact (Finset.mul_prod_erase Finset.univ (coeff lam) (Finset.mem_univ i)).symm
  refine ⟨hp, ?_, ?_⟩
  · intro i j k l
    apply b.ext
    intro t
    rw [hb]
    by_cases htl : t = l <;> by_cases hjk : j = k
    · subst t
      subst k
      simp only [Module.End.mul_apply, ha, if_true, map_smul, LinearMap.smul_apply, hz, smul_smul]
      rw [mul_comm]
    · subst t
      simp [Module.End.mul_apply, ha, map_smul, hjk, Ne.symm hjk]
    · simp [Module.End.mul_apply, ha, htl, hjk]
    · simp [Module.End.mul_apply, ha, htl, hjk]
  · apply b.ext
    intro t
    rw [hb]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, ha]
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_eq_single t]
    · simp only [if_true, hz, smul_smul, Module.End.one_apply]
      rw [hp t, Nat.cast_mul, mul_comm]
    · intro i hi hit
      simp [Ne.symm hit]
    · simp

theorem yui_aux_0005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ (r : ℕ) (z : V), z ∈ M → dividedPower x r z ∈ M) ∧ (∀ (r : ℕ) (z : V), z ∈ M → dividedPower y r z ∈ M) ∧ (∀ z ∈ M, x z ∈ M) ∧ (∀ z ∈ M, y z ∈ M) ∧ (∀ z ∈ M, h z ∈ M) ∧ (∀ (i j : Idx lam) (z : V), z ∈ M → integralMatrix lam x y i j z ∈ M)" := by
  have hx (r : ℕ) (z : V) (hz : z ∈ M) : dividedPower x r z ∈ M := h_H006.2.1 r ⟨z, hz⟩
  have hy (r : ℕ) (z : V) (hz : z ∈ M) : dividedPower y r z ∈ M := h_H006.2.2 r ⟨z, hz⟩
  have hxx (z : V) (hz : z ∈ M) : x z ∈ M := by
    simpa [dividedPower] using hx 1 z hz
  have hyy (z : V) (hz : z ∈ M) : y z ∈ M := by
    simpa [dividedPower] using hy 1 z hz
  refine ⟨hx, hy, hxx, hyy, ?_, ?_⟩
  · intro z hz
    rw [← h_H005.2.2.2.2.2]
    exact M.sub_mem (hxx _ (hyy z hz)) (hyy _ (hxx z hz))
  · intro i j z hz
    exact hx _ _ (hy _ _ (hx _ _ (hy _ _ hz)))

theorem yui_aux_0006 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ (f : Module.End ℂ V) (hf : ∀ (r : ℕ) (z : V), z ∈ M → dividedPower f r z ∈ M) (r : ℕ), (r.factorial : ℤ) • latticeEnd M (dividedPower f r) = (latticeEnd M f) ^ r" := by
  intro f hf
  have hr := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  have hz := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  have hf1 (z : V) (hz : z ∈ M) : f z ∈ M := by
    simpa [dividedPower] using hf 1 z hz
  have hpow (r : ℕ) (m : M) : (((latticeEnd M f)^r) m : V) = (f^r) (m : V) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply, hr f hf1, ih]
  intro r
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  simp only [LinearMap.smul_apply, Submodule.coe_smul, hr _ (hf r), hpow, hz]
  have hn : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  simp [dividedPower, smul_smul, hn]

theorem yui_aux_0007 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ i j k l : Idx lam, latticeEnd M (integralMatrix lam x y i j) * latticeEnd M (integralMatrix lam x y k l) = if j = k then (coeff lam j : ℤ) • latticeEnd M (integralMatrix lam x y i l) else 0) ∧ (∑ i : Idx lam, (coeffOmit lam i : ℤ) • latticeEnd M (integralMatrix lam x y i i)) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M)" := by
  classical
  have hr := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  have hs := (@yui_aux_0005 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006).2.2.2.2.2
  have ha := @yui_aux_0004 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  constructor
  · intro i j k l
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    have he := congrArg (fun f : Module.End ℂ V => f (m : V)) (ha.2.1 i j k l)
    by_cases hjk : j = k
    · simpa only [hjk, if_true, Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul, hr _ (hs _ _)] using he
    · simpa only [hjk, if_false, Module.End.mul_apply, LinearMap.zero_apply, Submodule.coe_zero, hr _ (hs _ _)] using he
  · apply LinearMap.ext
    intro m
    apply Subtype.ext
    have he := congrArg (fun f : Module.End ℂ V => f (m : V)) ha.2.2
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, hr _ (hs _ _), Module.End.one_apply] using he

theorem yui_aux_0008 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "latticeEnd M h = latticeEnd M x * latticeEnd M y - latticeEnd M y * latticeEnd M x ∧ (∀ i j : Idx lam, latticeEnd M (integralMatrix lam x y i j) = latticeEnd M (dividedPower x (ell lam-i.val)) * latticeEnd M (dividedPower y (ell lam)) * latticeEnd M (dividedPower x (ell lam)) * latticeEnd M (dividedPower y (ell lam-j.val)))" := by
  have hr := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  rcases (@yui_aux_0005 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006) with ⟨hx, hy, hxx, hyy, hh, ha⟩
  constructor
  · apply LinearMap.ext
    intro m
    apply Subtype.ext
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hr _ hh, hr _ hxx, hr _ hyy]
    exact (congrArg (fun f : Module.End ℂ V => f (m : V)) h_H005.2.2.2.2.2).symm
  · intro i j
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    simp only [Module.End.mul_apply, hr _ (ha _ _), hr _ (hx _), hr _ (hy _)]
    rfl

end Local_T002
open Local_T002 in
theorem T002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) :
    (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val)) := by
  classical
  rcases (@yui_aux_0001 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006) with ⟨hc, hq, hlow, ha⟩
  have hr := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  rcases (@yui_aux_0004 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006) with ⟨hprod, _, _⟩
  rcases (@yui_aux_0005 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006) with ⟨hx, hy, hxx, hyy, hh, hA⟩
  have hfact := @yui_aux_0006 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  rcases (@yui_aux_0007 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006) with ⟨hmul, hsum⟩
  rcases (@yui_aux_0008 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006) with ⟨hcomm, hcomp⟩
  refine ⟨hc, hq, hlow, ha, ?_, hmul, hsum, hprod, ?_, ?_, ?_, hcomm, hcomp⟩
  · intro i j m
    exact ⟨hA i j m m.property, hr _ (hA i j) m⟩
  · intro r
    exact ⟨hfact x hx r, hfact y hy r⟩
  · intro r m
    exact ⟨hr _ (hx r) m, hr _ (hy r) m⟩
  · intro m
    exact ⟨hxx m m.property, hyy m m.property, hh m m.property, hr x hxx m, hr y hyy m, hr h hh m⟩

namespace Local_T009
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f" := by
  intro z f
  obtain ⟨⟨b, e, hb⟩, hx, hy⟩ := h_H006
  let beta : Module.Basis (Idx lam) K (TensorLeft K M) := b.baseChange K
  apply beta.ext
  intro i
  simp [beta, hat, ← Int.cast_smul_eq_zsmul K]

end Local_T009
open Local_T009 in
theorem T009 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) := by
  classical
  have hcast : (ell lam : ℤ) = lam := Int.toNat_of_nonneg h_H003.1
  have hlt : ell lam < p := by omega
  have hscalar := @yui_aux_0001 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H006
  obtain ⟨⟨b, e, hb⟩, hx, hy⟩ := h_H006
  let beta : Module.Basis (Idx lam) K (TensorLeft K M) := b.baseChange K
  have hbeta : ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i) := by
    intro i
    exact Module.Basis.baseChange_apply K b i
  have hn : Nontrivial (TensorLeft K M) :=
    ⟨⟨beta ⟨0, Nat.succ_pos _⟩, 0, beta.ne_zero _⟩⟩
  have hd : FiniteDimensional K (TensorLeft K M) := beta.finiteDimensional_of_finite
  have hr : Module.finrank K (TensorLeft K M) = ell lam + 1 := by
    simpa only [Idx, Fintype.card_fin] using Module.finrank_eq_card_basis beta
  have hadd : ∀ f g : Module.End ℤ M, hat (K := K) (f + g) = hat f + hat g := by
    intro f g
    apply beta.ext
    intro i
    simp [hbeta, hat]
  have hmul : ∀ f g : Module.End ℤ M, hat (K := K) (f * g) = hat f * hat g := by
    intro f g
    apply beta.ext
    intro i
    simp [hbeta, hat, Module.End.mul_apply]
  have hone : hat (K := K) (1 : Module.End ℤ M) = 1 := by
    apply beta.ext
    intro i
    simp [hbeta, hat]
  refine ⟨hcast, hlt, Nat.succ_pos _, ⟨b, beta, hbeta⟩, hn, hd, hr, ?_⟩
  refine ⟨fun f g => ⟨hadd f g, hmul f g⟩, hscalar, hone, ?_, ?_, ?_⟩
  · intro q fs
    change (Module.End.baseChangeHom ℤ K M) (∑ i, fs i) = ∑ i, (Module.End.baseChangeHom ℤ K M) (fs i)
    exact map_sum (Module.End.baseChangeHom ℤ K M) fs Finset.univ
  · intro f r
    induction r with
    | zero => simpa using hone
    | succ r ih => rw [pow_succ, hmul, ih, pow_succ]
  · intro f a m
    exact LinearMap.baseChange_tmul f a m

namespace Local_T010
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) : yui_aux_type% "∀ j : Idx lam, (coeff lam j : K) * (j.val.factorial : K) * ((ell lam - j.val).factorial : K) = ((ell lam).factorial : K)" := by
  intro j
  have hj : j.val ≤ ell lam := Nat.le_of_lt_succ j.isLt
  have hn : coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial := Nat.choose_mul_factorial_mul_factorial hj
  have hc := congrArg (fun n : ℕ => (n : K)) hn
  simpa only [Nat.cast_mul] using hc

end Local_T010
open Local_T010 in
theorem T010 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) :
    (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨h_H001⟩
  letI : CharP K p := h_H002
  have hcast : (ell lam : ℤ) = lam := Int.toNat_of_nonneg h_H003.1
  have hlt : ell lam < p := by omega
  have hfac : ∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0 := by
    intro r hr
    have hu : IsUnit (r.factorial : K) :=
      (IsUnit.natCast_factorial_iff_of_charP (A := K) p (n := r)).2 (lt_of_le_of_lt hr hlt)
    exact hu.ne_zero
  have hcoeff : ∀ j : Idx lam, (coeff lam j : K) ≠ 0 := by
    intro j hj
    have hid := @yui_aux_0001 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 j
    have hz : ((ell lam).factorial : K) = 0 := by
      rw [hj, zero_mul, zero_mul] at hid
      exact hid.symm
    exact hfac (ell lam) (le_refl _) hz
  refine ⟨hfac, hcoeff, ?_⟩
  classical
  simpa only [coeffProd, Nat.cast_prod] using
    (Finset.prod_ne_zero_iff.mpr (fun j (_ : j ∈ (Finset.univ : Finset (Idx lam))) => hcoeff j) :
      (∏ j : Idx lam, (coeff lam j : K)) ≠ 0)

namespace Local_T003
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ i : Idx lam, (coeffProd lam : K) = (coeff lam i : K) * (coeffOmit lam i : K)" := by
  intro i
  have hp : coeffProd lam = coeff lam i * coeffOmit lam i :=
    h_T002.2.2.2.2.2.2.2.1 i
  rw [hp, Nat.cast_mul]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ i j l : Idx lam, ((coeff lam j : K)⁻¹ * (coeff lam l : K)⁻¹) • ((coeff lam j : K) • hat (K := K) (latticeEnd M (integralMatrix lam x y i l))) = (coeff lam l : K)⁻¹ • hat (K := K) (latticeEnd M (integralMatrix lam x y i l))" := by
  intro i j l
  rw [smul_smul]
  have hc : (coeff lam j : K) ≠ 0 := h_T010.2.1 j
  have heq : ((coeff lam j : K)⁻¹ * (coeff lam l : K)⁻¹) * (coeff lam j : K) =
      (coeff lam l : K)⁻¹ := by
    calc
      _ = ((coeff lam j : K)⁻¹ * (coeff lam j : K)) * (coeff lam l : K)⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ hc, one_mul]
  rw [heq]

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "matrixUnits (scaledMatrix (K := K) lam x y M)" := by
  classical
  have hcast := @yui_aux_0001 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  have hcancel := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  rcases h_T009 with ⟨hl, hp, hd, hb, hn, hfd, hfin, hop⟩
  rcases hop with ⟨ham, hz, hone, hs, hpow, ht⟩
  rcases h_T002 with ⟨hc, htop, hlow, hact, hpres, hm, hsum, hprod, hfact, hdiv, hgen, hh, ha⟩
  have hzero : hat (K := K) (0 : Module.End ℤ M) = 0 := by
    simpa using hz (0 : ℤ) (1 : Module.End ℤ M)
  have hnat (n : ℕ) (f : Module.End ℤ M) :
      hat (K := K) ((n : ℤ) • f) = (n : K) • hat (K := K) f := by
    simpa using hz (n : ℤ) f
  have hm' (i j k l : Idx lam) :
      hat (K := K) (latticeEnd M (integralMatrix lam x y i j)) *
        hat (K := K) (latticeEnd M (integralMatrix lam x y k l)) =
      if j = k then (coeff lam j : K) •
        hat (K := K) (latticeEnd M (integralMatrix lam x y i l)) else 0 := by
    rw [← (ham _ _).2, hm]
    split_ifs <;> simp only [hnat, hzero]
  have hsum' :
      (∑ i : Idx lam, (coeffOmit lam i : K) •
        hat (K := K) (latticeEnd M (integralMatrix lam x y i i))) =
      (coeffProd lam : K) • (1 : Module.End K (TensorLeft K M)) := by
    calc
      _ = hat (K := K) (∑ i : Idx lam, (coeffOmit lam i : ℤ) •
          latticeEnd M (integralMatrix lam x y i i)) := by
        rw [hs]
        simp only [hnat]
      _ = _ := by rw [hsum, hnat, hone]
  have hscalar (i : Idx lam) :
      (coeffProd lam : K)⁻¹ * (coeffOmit lam i : K) = (coeff lam i : K)⁻¹ := by
    have heq : (coeffProd lam : K) =
        (coeff lam i : K) * (coeffOmit lam i : K) := by
      exact hcast i
    have hcne := h_T010.2.1 i
    have hpne := h_T010.2.2
    apply (mul_left_cancel₀ hpne)
    rw [← mul_assoc, mul_inv_cancel₀ hpne, one_mul, heq]
    simp [mul_assoc, mul_comm, mul_left_comm, hcne]
  constructor
  · intro i j k l
    dsimp only [scaledMatrix]
    rw [smul_mul_smul_comm, hm']
    by_cases hjk : j = k
    · subst k
      simpa only [ite_true] using hcancel i j l
    · simp [hjk]
  · change (∑ i : Idx lam, (coeff lam i : K)⁻¹ •
        hat (K := K) (latticeEnd M (integralMatrix lam x y i i))) = 1
    calc
      _ = (coeffProd lam : K)⁻¹ •
          (∑ i : Idx lam, (coeffOmit lam i : K) •
          hat (K := K) (latticeEnd M (integralMatrix lam x y i i))) := by
        simp only [Finset.smul_sum, smul_smul, hscalar]
      _ = 1 := by rw [hsum', inv_smul_smul₀ h_T010.2.2]

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ f : Module.End ℤ M, (-1 : K) • hat (K := K) f = -hat (K := K) f" := by
  intro f
  exact neg_one_smul K (hat (K := K) f)

theorem yui_aux_0005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ f : Module.End ℤ M, hat (K := K) (-f) = -hat (K := K) f" := by
  have hn := @yui_aux_0004 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  intro f
  have hz : hat (K := K) ((-1 : ℤ) • f) = ((-1 : ℤ) : K) • hat (K := K) f :=
    h_T009.2.2.2.2.2.2.2.2.1 (-1 : ℤ) f
  have hcast : ((-1 : ℤ) : K) = (-1 : K) := by norm_num
  have hz' : hat (K := K) (-f) = (-1 : K) • hat (K := K) f := by
    simpa only [hcast, neg_one_smul ℤ] using hz
  exact hz'.trans (hn f)

end Local_T003
open Local_T003 in
theorem T003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x) := by
  classical
  have hneg := @yui_aux_0005 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  have hmu := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  rcases h_T009 with ⟨hl, hp, hd, hb, hn, hfd, hfin, hop⟩
  have hop' := hop
  rcases hop' with ⟨ham, hz, hone, hs, hpow, ht⟩
  rcases h_T002 with ⟨hc, htop, hlow, hact, hpres, hm, hsum, hprod, hfact, hdiv, hgen, hh, ha⟩
  have hnat (n : ℕ) (f : Module.End ℤ M) :
      hat (K := K) ((n : ℤ) • f) = (n : K) • hat (K := K) f := by
    simpa using hz (n : ℤ) f
  have hsub (f g : Module.End ℤ M) :
      hat (K := K) (f - g) = hat (K := K) f - hat (K := K) g := by
    rw [sub_eq_add_neg, (ham _ _).1, hneg, sub_eq_add_neg]
  refine ⟨hl, hp, hd, hn, hfd, hfin, h_T010, hmu, hop, ?_, ?_⟩
  · intro r hr
    constructor
    · apply (eq_inv_smul_iff₀ (h_T010.1 r hr)).2
      calc
        _ = hat (K := K) ((r.factorial : ℤ) • latticeEnd M (dividedPower x r)) :=
          (hnat r.factorial _).symm
        _ = _ := by rw [(hfact r).1, hpow]
    · apply (eq_inv_smul_iff₀ (h_T010.1 r hr)).2
      calc
        _ = hat (K := K) ((r.factorial : ℤ) • latticeEnd M (dividedPower y r)) :=
          (hnat r.factorial _).symm
        _ = _ := by rw [(hfact r).2, hpow]
  · rw [hh, hsub, (ham _ _).2, (ham _ _).2]

namespace Local_T011
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : yui_aux_type% "∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m" := by
  intro m a
  rfl

end Local_T011
open Local_T011 in
theorem T011 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  :
    (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u)) := by
  have swap_tmul := @yui_aux_0001 p K instK lam V instV instCV x y h v M
  refine ⟨swap_tmul, ?_, ?_, ?_⟩
  · intro a b m
    apply (tensorSwap K M).injective
    rw [(tensorSwap K M).map_smul, swap_tmul, swap_tmul]
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  · intro f m a
    apply (tensorSwap K M).injective
    simp only [induced, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, swap_tmul, hat, LinearMap.baseChange_tmul]
  · intro f u
    simp only [induced, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

namespace Local_T004
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T003 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)) (h_T011 : (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ i j : Idx lam,\nhat (K := K) (latticeEnd M (integralMatrix lam x y i j)) =\nhat (K := K) (latticeEnd M (dividedPower x (ell lam-i.val))) *\nhat (K := K) (latticeEnd M (dividedPower y (ell lam))) *\nhat (K := K) (latticeEnd M (dividedPower x (ell lam))) *\nhat (K := K) (latticeEnd M (dividedPower y (ell lam-j.val)))" := by
  intro i j
  have hf := h_T002.2.2.2.2.2.2.2.2.2.2.2.2 i j
  dsimp only at hf
  have hm : ∀ f g : Module.End ℤ M, hat (K := K) (f * g) = hat f * hat g :=
    fun f g => (h_T003.2.2.2.2.2.2.2.2.1.1 f g).2
  exact (congrArg (hat (K := K)) hf).trans (by rw [hm, hm, hm])

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T003 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)) (h_T011 : (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ W : Submodule K (TensorLeft K M), stable (hat (K := K) (latticeEnd M x)) W → stable (hat (K := K) (latticeEnd M y)) W → ∀ i j, stable (scaledMatrix (K := K) lam x y M i j) W" := by
  have hfour := @yui_aux_0001 p K instK lam V instV instCV x y h v M h_T002 h_T003 h_T011 h_H005 h_H006
  have hdiv := h_T003.2.2.2.2.2.2.2.2.2.1
  intro W hx hy
  have smul_stable (a : K) (f : Module.End K (TensorLeft K M))
      (hf : stable f W) : stable (a • f) W := by
    intro w hw
    exact W.smul_mem a (hf w hw)
  have mul_stable (f g : Module.End K (TensorLeft K M))
      (hf : stable f W) (hg : stable g W) : stable (f * g) W := by
    intro w hw
    exact hf (g w) (hg w hw)
  have pow_stable (f : Module.End K (TensorLeft K M))
      (hf : stable f W) (r : ℕ) : stable (f ^ r) W := by
    induction r with
    | zero => intro w hw; simpa using hw
    | succ r ih =>
      rw [pow_succ']
      exact mul_stable f (f ^ r) hf ih
  have hxdiv (r : ℕ) (hr : r ≤ ell lam) :
      stable (hat (K := K) (latticeEnd M (dividedPower x r))) W := by
    rw [(hdiv r hr).1]
    exact smul_stable _ _ (pow_stable _ hx r)
  have hydiv (r : ℕ) (hr : r ≤ ell lam) :
      stable (hat (K := K) (latticeEnd M (dividedPower y r))) W := by
    rw [(hdiv r hr).2]
    exact smul_stable _ _ (pow_stable _ hy r)
  intro i j
  apply smul_stable
  rw [hfour i j]
  exact mul_stable _ _ (mul_stable _ _ (mul_stable _ _
    (hxdiv _ (Nat.sub_le _ _)) (hydiv _ le_rfl)) (hxdiv _ le_rfl))
    (hydiv _ (Nat.sub_le _ _))

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T003 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)) (h_T011 : (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ f : Module.End ℤ M,\n (tensorSwap K M).symm.conjAlgEquiv K (hat (K := K) f) = induced (K := K) f" := by
  intro f
  rfl

end Local_T004
open Local_T004 in
theorem T004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T003 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)) (h_T011 : (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) :
    Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) := by
  classical
  have hleft := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T002 h_T003 h_T011 h_H005 h_H006
  have hconvert := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T002 h_T003 h_T011 h_H005 h_H006
  rcases h_T003 with ⟨he, hp, hn, hnt, hfd, hdim, hc, hmu, hmaps, hdiv, hh⟩
  letI : Nontrivial (TensorLeft K M) := hnt
  letI : FiniteDimensional K (TensorLeft K M) := hfd
  let s : TensorRight K M ≃ₗ[K] TensorLeft K M := tensorSwap K M
  let C : Module.End K (TensorLeft K M) ≃ₐ[K] Module.End K (TensorRight K M) :=
    s.symm.conjAlgEquiv K
  have hind (f : Module.End ℤ M) : C (hat (K := K) f) = induced (K := K) f :=
    hconvert f
  have capp (f : Module.End K (TensorLeft K M)) (w : TensorRight K M) :
      C f w = s.symm (f (s w)) := rfl
  let G : Idx lam → Idx lam → Module.End K (TensorRight K M) :=
    fun i j => C (scaledMatrix (K := K) lam x y M i j)
  have hmuG : matrixUnits G := by
    constructor
    · intro i j k l
      change C _ * C _ = if j = k then C _ else 0
      rw [← map_mul, hmu.1 i j k l]
      by_cases hj : j = k
      · rw [if_pos hj, if_pos hj]
      · rw [if_neg hj, if_neg hj, map_zero]
    · change (∑ i, C (scaledMatrix (K := K) lam x y M i i)) = 1
      rw [← map_sum, hmu.2, map_one]
  have hstable : ∀ W : Submodule K (TensorRight K M),
      stable (induced (K := K) (latticeEnd M x)) W →
      stable (induced (K := K) (latticeEnd M y)) W →
      ∀ i j, stable (G i j) W := by
    intro W hx hy
    have htransport (f : Module.End ℤ M) (hf : stable (induced (K := K) f) W) :
        stable (hat (K := K) f) (W.map s.toLinearMap) := by
      intro z hz
      rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
      apply Submodule.mem_map.mpr
      exact ⟨induced (K := K) f w, hf w hw, h_T011.2.2.2 f w⟩
    have ht := hleft (W.map s.toLinearMap)
      (htransport _ hx) (htransport _ hy)
    intro i j w hw
    have hm := ht i j (s w) (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)
    rcases Submodule.mem_map.mp hm with ⟨u, hu, heu⟩
    change C (scaledMatrix (K := K) lam x y M i j) w ∈ W
    rw [capp, ← heu]
    simpa using hu
  have hcomm :
      induced (K := K) (latticeEnd M h) =
      induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
      induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) := by
    rw [← hind, hh, map_sub, map_mul, map_mul, hind, hind]
  exact ⟨s.toEquiv.nontrivial, s.symm.finiteDimensional,
    s.finrank_eq.trans hdim, hn, ⟨G, hmuG, hstable⟩, hcomm, h_T011.2.2.1⟩

theorem T005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  :
    ∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤ := by
  classical
  intro F U0 _ _ _ n0 _ G hn hdim hG W hW
  rcases hG with ⟨hmul, hsum⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hsumw : ∑ j, G j j w = w := by
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using congrArg (fun f : Module.End F U0 => f w) hsum
  have hex : ∃ j, G j j w ≠ 0 := by
    by_contra he
    have hz : ∀ j, G j j w = 0 := by simpa using he
    have : w = 0 := by simpa [hz] using hsumw.symm
    exact hw0 this
  obtain ⟨j, hj⟩ := hex
  let u : U0 := G j j w
  have huW : u ∈ W := hW j j w hwW
  have hu0 : u ≠ 0 := hj
  have hju : G j j u = u := by
    change (G j j * G j j) w = G j j w
    rw [hmul j j j j, if_pos rfl]
  let z : Fin n0 → U0 := fun i => G i j u
  have hzW : ∀ i, z i ∈ W := fun i => hW i j u huW
  have hact : ∀ k i, G j k (z i) = if k = i then u else 0 := by
    intro k i
    change (G j k * G i j) u = _
    rw [hmul j k i j]
    by_cases hki : k = i
    · simp [hki, hju]
    · simp [hki]
  have hli : LinearIndependent F z := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc k
    have hk := congrArg (fun a : U0 => G j k a) hc
    have hck : c k • u = 0 := by
      simpa [map_sum, hact] using hk
    exact (smul_eq_zero.mp hck).resolve_right hu0
  have hspan : Submodule.span F (Set.range z) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simpa using hdim.symm)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro a ⟨i, rfl⟩
  exact hzW i

theorem T006 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T004 : Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a)) (h_T005 : @YuiPortTypes.T005 p K instK lam V instV instCV x y h v M) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) :
    Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤ := by
  rcases h_T004 with ⟨hne, hfd, hdim, hpos, ⟨G, hG, hstable⟩, hrest⟩
  letI : FiniteDimensional K (TensorRight K M) := hfd
  refine ⟨hne, ?_⟩
  intro W hx hy hh
  exact h_T005 K (TensorRight K M) (ell lam + 1) G hpos hdim hG W (hstable W hx hy)

private theorem __connected_T007 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v)) := by
  exact @T007 p K instK lam V instV instCV x y h v M h_H003 h_H005

private theorem __connected_T008 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) :
    (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) := by
  exact @T008 p K instK lam V instV instCV x y h v M (@__connected_T007 p K instK lam V instV instCV x y h v M h_H003 h_H005) h_H004 h_H005

private theorem __connected_T001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0) := by
  exact @T001 p K instK lam V instV instCV x y h v M (@__connected_T007 p K instK lam V instV instCV x y h v M h_H003 h_H005) (@__connected_T008 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005) h_H003 h_H004 h_H005

private theorem __connected_T002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) :
    (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val)) := by
  exact @T002 p K instK lam V instV instCV x y h v M (@__connected_T001 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005) h_H005 h_H006

private theorem __connected_T009 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) := by
  exact @T009 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H006

private theorem __connected_T010 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) :
    (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0 := by
  exact @T010 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003

private theorem __connected_T003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x) := by
  exact @T003 p K instK lam V instV instCV x y h v M (@__connected_T002 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005 h_H006) (@__connected_T009 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H006) (@__connected_T010 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003) h_H001 h_H002 h_H003 h_H004 h_H006

private theorem __connected_T011 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  :
    (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u)) := by
  exact @T011 p K instK lam V instV instCV x y h v M

private theorem __connected_T004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) :
    Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) := by
  exact @T004 p K instK lam V instV instCV x y h v M (@__connected_T002 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005 h_H006) (@__connected_T003 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006) (@__connected_T011 p K instK lam V instV instCV x y h v M) h_H005 h_H006

private theorem __connected_T005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  :
    ∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤ := by
  exact @T005 p K instK lam V instV instCV x y h v M

private theorem __connected_T006 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) :
    Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤ := by
  exact @T006 p K instK lam V instV instCV x y h v M (@__connected_T004 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006) (@__connected_T005 p K instK lam V instV instCV x y h v M) h_H003 h_H005 h_H006

theorem P (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤ := by
  exact @__connected_T006 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤ := by
  exact @Translation.P.{_, _} p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006

#check @P
#print axioms P
end AuditBExport

/- Trusted inspector appended after the generated proof, never a worker tool.
   Its only substitution is an array of escaped (id, selector, expected type) strings. -/
namespace NL2LeanAuditProbe
open Lean Meta Elab Command Term

private def nameOf (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def showType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def binderInventory (type : Expr) : MetaM Json :=
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    for x in xs do
      let d ← getFVarLocalDecl x
      rows := rows.push <| Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← showType d.type)), ("proof_valued", toJson (← isProp d.type))]
    return Json.mkObj [("binders", toJson rows), ("result", toJson (← showType body))]

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
    ("type", toJson (← showType info.type)),
    ("signature", ← binderInventory info.type),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("direct_constants", toJson ((info.getUsedConstantsAsSet.toArray.qsort Name.lt).map Name.toString)),
    ("axioms", toJson ((← collectAxioms name).map Name.toString))]

private def inspect (roots : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    rows := rows.push (← record name)
    if !(← getEnv).isImportedConst name then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
  return Json.mkObj [("declarations", toJson rows), ("truncated", toJson (!pending.isEmpty))]

private def actualType (selector : String) (parts : Array String) : TermElabM Expr := do
  if selector.startsWith "decl:" then
    return (← getConstInfo (nameOf parts)).type
  if selector.startsWith "value:" then
    let .defnInfo decl ← getConstInfo (nameOf parts) | throwError "Expected a defined proposition"
    return decl.value
  if selector.startsWith "premise:" then
    let wanted := "h_" ++ (selector.drop 8).toString
    let root ← getConstInfo `AuditBExport.P
    return ← forallTelescope root.type fun xs _ => do
      let mut context : Array Expr := #[]
      for x in xs do
        let binder ← getFVarLocalDecl x
        if binder.userName.toString == wanted then
          return ← mkForallFVars context binder.type
        context := context.push x
      throwError "Missing actual root premise {wanted}"
  throwError "Unsupported selector {selector}"

/- Universe parameter names belong to each declaration's binder scope.
   Rename them bijectively, retaining repetitions and all level expressions.
   This is alpha-equivalence, not a proof of logical equivalence. -/
private def sameSignature (actual expected : Expr) : MetaM (Bool × String) := do
  if ← withoutModifyingState <| isDefEq actual expected then
    return (true, "definitional")
  let actualParams := (collectLevelParams {} actual).params.toList
  let expectedParams := (collectLevelParams {} expected).params.toList
  if actualParams.length != expectedParams.length then
    return (false, "different_universe_binders")
  let levels := (List.range actualParams.length).map fun i =>
    Level.param (Name.mkSimple ("_yuiAuditLevel" ++ toString i))
  let equal ← withoutModifyingState <| isDefEq
    (actual.instantiateLevelParams actualParams levels)
    (expected.instantiateLevelParams expectedParams levels)
  return (equal, "bijective_universe_renaming")

elab "#nl2lean_audit_probe" : command => do
  let result ← liftTermElabM <| withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
    let checks : Array (String × String × String × Array String) := #[("P", "decl:AuditBExport.P", "∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M), Nontrivial (TensorRight K M) ∧\n∀ W : Submodule K (TensorRight K M),\n stable (induced (K := K) (latticeEnd M x)) W →\n stable (induced (K := K) (latticeEnd M y)) W →\n stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤", #["AuditBExport", "P"]), ("__frozen__P", "decl:AuditBExport.P", "∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M), Nontrivial (TensorRight K M) ∧\n∀ W : Submodule K (TensorRight K M),\n stable (induced (K := K) (latticeEnd M x)) W →\n stable (induced (K := K) (latticeEnd M y)) W →\n stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤", #["AuditBExport", "P"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`AuditBExport.P]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      let row := Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if id.startsWith "__frozen__" then
        frozenComparisons := frozenComparisons.push row
      else
        comparisons := comparisons.push row
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons),
      ("frozen_comparisons", toJson frozenComparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

#nl2lean_audit_probe
end NL2LeanAuditProbe
