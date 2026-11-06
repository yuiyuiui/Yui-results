import Mathlib

namespace YuiBasisObjects

noncomputable def dividedPower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r

def Stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (f : Module.End K V) : Prop :=
  ∀ w, w ∈ W → f w ∈ W

structure AdmissibleLattice (n : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (x y : Module.End ℂ V) where
  carrier : Submodule ℤ V
  zBasis : Module.Basis (Fin n) ℤ carrier
  cBasis : Module.Basis (Fin n) ℂ V
  coe_basis : ∀ i, (zBasis i : V) = cBasis i
  stableX : ∀ (r : ℕ) (m : V), m ∈ carrier → dividedPower x r m ∈ carrier
  stableY : ∀ (r : ℕ) (m : V), m ∈ carrier → dividedPower y r m ∈ carrier

end YuiBasisObjects

universe uK uV

namespace Reduction
open scoped BigOperators
open YuiBasisObjects
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
noncomputable def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V :=
  (i.factorial : ℂ)⁻¹ • (y ^ i) v
def c (ell : ℕ) (j : Fin (ell + 1)) : ℕ := Nat.choose ell j.val
def Dprod (ell : ℕ) : ℕ := ∏ j : Fin (ell + 1), c ell j
def d (ell : ℕ) (j : Fin (ell + 1)) : ℕ :=
  ∏ k : Fin (ell + 1), if k = j then 1 else c ell k
def hM {M : Type*} [AddCommGroup M] [Module ℤ M]
    (XM YM : ℕ → Module.End ℤ M) : Module.End ℤ M :=
  XM 1 * YM 1 - YM 1 * XM 1
def A {M : Type*} [AddCommGroup M] [Module ℤ M]
    (XM YM : ℕ → Module.End ℤ M) (ell : ℕ)
    (i j : Fin (ell + 1)) : Module.End ℤ M :=
  XM (ell - i.val) * (YM ell * XM ell) * YM (ell - j.val)
noncomputable def AC (x y : Module.End ℂ V) (ell : ℕ)
    (i j : Fin (ell + 1)) : Module.End ℂ V :=
  dividedPower x (ell - i.val) *
    (dividedPower y ell * dividedPower x ell) * dividedPower y (ell - j.val)
def VK (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] :=
  TensorProduct ℤ M K
def pure (K : Type*) {M : Type*} [Field K] [AddCommGroup M] [Module ℤ M]
    (m : M) (a : K) : VK K M := TensorProduct.tmul ℤ m a
noncomputable instance vkAdd (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] :
    AddCommGroup (VK K M) := inferInstanceAs (AddCommGroup (TensorProduct ℤ M K))
noncomputable def swapAdd (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] :
    VK K M ≃+ TensorProduct ℤ K M :=
  letI : Module ℤ (TensorProduct ℤ M K) := TensorProduct.instModule
  letI : Module ℤ (TensorProduct ℤ K M) := TensorProduct.instModule
  (TensorProduct.comm ℤ M K).toAddEquiv
noncomputable instance vkModule (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] :
    Module K (VK K M) := (swapAdd K M).module K
noncomputable def swap (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] :
    VK K M ≃ₗ[K] TensorProduct ℤ K M :=
  (swapAdd K M).linearEquiv K
noncomputable def F (K : Type*) {M : Type*} [Field K] [AddCommGroup M] [Module ℤ M]
    (f : Module.End ℤ M) : Module.End K (TensorProduct ℤ K M) := f.baseChange K
noncomputable def ind (K : Type*) {M : Type*} [Field K] [AddCommGroup M] [Module ℤ M]
    (f : Module.End ℤ M) : Module.End K (VK K M) :=
  (swap K M).symm.toLinearMap ∘ₗ F K f ∘ₗ (swap K M).toLinearMap
noncomputable def T (K : Type*) {M : Type*} [Field K] [AddCommGroup M] [Module ℤ M]
    (XM YM : ℕ → Module.End ℤ M) (ell : ℕ)
    (i j : Fin (ell + 1)) : Module.End K (TensorProduct ℤ K M) :=
  (c ell j : K)⁻¹ • F K (A XM YM ell i j)
def MatrixUnits {k : Type*} [Field k] {U : Type*} [AddCommGroup U] [Module k U]
    (n : ℕ) (t : Fin n → Fin n → Module.End k U) : Prop :=
  (∀ i j a b, t i j * t a b = if j = a then t i b else 0) ∧
  (∑ j, t j j) = 1
end Reduction
namespace YuiPortTypes
abbrev T011 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) : Prop :=
  ∀ (k0 : Type uK) [Field k0] (U0 : Type (max uK uV))
 [AddCommGroup U0] [Module k0 U0] (n0 : ℕ)
 (t : Fin n0 → Fin n0 → Module.End k0 U0),
 0 < n0 → FiniteDimensional k0 U0 → Module.finrank k0 U0 = n0 →
 Reduction.MatrixUnits n0 t →
 ∀ W0 : Submodule k0 U0, (∀ i j, YuiBasisObjects.Stable W0 (t i j)) →
 W0 = ⊥ ∨ W0 = ⊤
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) : yui_aux_type% "(∀ w : V, h (y w) = y (h w) - (2 : ℂ) • y w) ∧ (∀ w : V, x (y w) = y (x w) + h w)" := by
  constructor
  · intro w
    have hh := congrArg (fun f : Module.End ℂ V => f w) h_H005.2.1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hh
    have he : h (y w) - y (h w) = -(2 : ℂ) • y w := hh
    calc
      h (y w) = (h (y w) - y (h w)) + y (h w) := by abel
      _ = y (h w) - (2 : ℂ) • y w := by rw [he, neg_smul]; abel
  · intro w
    have hh := congrArg (fun f : Module.End ℂ V => f w) h_H005.2.2
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hh
    calc
      x (y w) = (x (y w) - y (x w)) + y (x w) := by abel
      _ = y (x w) + h w := by rw [hh]; abel

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) : yui_aux_type% "(lambda : ℂ) = (lambda.toNat : ℂ)" := by
  have hl : lambda = (lambda.toNat : ℤ) := by omega
  have hh : (lambda : ℂ) = ((lambda.toNat : ℤ) : ℂ) := congrArg (fun z : ℤ => (z : ℂ)) hl
  simpa only [Int.cast_natCast] using hh

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) : yui_aux_type% "∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)" := by
  have hc := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006
  have hr := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006
  intro i
  induction i with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, sub_zero, hc] using h_H006.2.2
  | succ t ih =>
    calc
      h ((y ^ (t + 1)) v) = h (y ((y ^ t) v)) := by rw [pow_succ', Module.End.mul_apply]
      _ = y (h ((y ^ t) v)) - (2 : ℂ) • y ((y ^ t) v) := hr.1 _
      _ = ((lambda.toNat : ℂ) - 2 * (t : ℂ) - 2) • y ((y ^ t) v) := by
        rw [ih, map_smul]
        simp only [sub_smul]
      _ = ((lambda.toNat : ℂ) - 2 * ((t + 1 : ℕ) : ℂ)) • ((y ^ (t + 1)) v) := by
        rw [pow_succ', Module.End.mul_apply]
        congr 1
        push_cast
        ring

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) : yui_aux_type% "∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) = ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v)" := by
  have hc := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006
  have hr := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006
  have hh := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006
  have hs : ∀ t : ℕ, x ((y ^ (t + 1)) v) = (((t + 1 : ℕ) : ℂ) * ((lambda.toNat : ℂ) - ((t + 1 : ℕ) : ℂ) + 1)) • ((y ^ t) v) := by
    intro t
    induction t with
    | zero =>
      simp only [zero_add, pow_one, hr.2, h_H006.2.1, map_zero, zero_add, h_H006.2.2, hc, Nat.cast_one, one_mul, sub_add_cancel, pow_zero, Module.End.one_apply]
    | succ t ih =>
      calc
        x ((y ^ (t + 1 + 1)) v) = x (y ((y ^ (t + 1)) v)) := by rw [pow_succ', Module.End.mul_apply]
        _ = y (x ((y ^ (t + 1)) v)) + h ((y ^ (t + 1)) v) := hr.2 _
        _ = ((((t + 1 : ℕ) : ℂ) * ((lambda.toNat : ℂ) - ((t + 1 : ℕ) : ℂ) + 1)) + ((lambda.toNat : ℂ) - 2 * ((t + 1 : ℕ) : ℂ))) • ((y ^ (t + 1)) v) := by
          rw [ih, map_smul, hh]
          simp only [add_smul, pow_succ', Module.End.mul_apply]
        _ = (((t + 1 + 1 : ℕ) : ℂ) * ((lambda.toNat : ℂ) - ((t + 1 + 1 : ℕ) : ℂ) + 1)) • ((y ^ (t + 1)) v) := by
          congr 1
          push_cast
          ring
  intro i hi
  cases i with
  | zero => omega
  | succ t => simpa only [Nat.add_sub_cancel] using hs t

end Local_T001
open Local_T001 in
theorem T001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) :
    (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v)) := by
  have hl : lambda = (lambda.toNat : ℤ) := by omega
  have hp : lambda.toNat < p := by omega
  have hd : Module.finrank ℂ V = lambda.toNat + 1 := by
    have hh := h_H004.2.1
    omega
  have hc := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006
  have hv : h v = (lambda.toNat : ℂ) • v := by
    simpa only [hc] using h_H006.2.2
  exact ⟨⟨hl, hp, h_H004.1, hd⟩, h_H006.1, h_H006.2.1, hv,
    @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006,
    @yui_aux_0004 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006⟩

namespace Local_T002
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) : yui_aux_type% "∀ i : ℕ, (x ^ i) ((y ^ i) v) = (∏ r ∈ Finset.range i, (((r + 1 : ℕ) : ℂ) * ((lambda.toNat : ℂ) - (r : ℂ)))) • v" := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hr := h_T001.2.2.2.2.2 (i + 1) (by omega)
    rw [pow_succ, Module.End.mul_apply, hr]
    simp only [Nat.add_sub_cancel, map_smul, ih, smul_smul, Finset.prod_range_succ]
    congr 1
    push_cast
    ring

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) : yui_aux_type% "∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧ h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val" := by
  intro i
  have hp : (∏ r ∈ Finset.range i.val, (((r + 1 : ℕ) : ℂ) * ((lambda.toNat : ℂ) - (r : ℂ)))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    apply mul_ne_zero
    · exact_mod_cast (Nat.succ_ne_zero r)
    · apply sub_ne_zero.mpr
      have hlt : r < lambda.toNat := by
        have := Finset.mem_range.mp hr
        omega
      exact_mod_cast (Nat.ne_of_gt hlt)
  have hy : (y ^ i.val) v ≠ 0 := by
    intro hz
    have heq := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_T001 i.val
    rw [hz, map_zero] at heq
    exact (smul_ne_zero hp h_T001.2.1) heq.symm
  constructor
  · exact smul_ne_zero (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val)) hy
  · dsimp [Reduction.e]
    rw [map_smul, h_T001.2.2.2.2.1 i.val, smul_comm]

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) : yui_aux_type% "Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ))" := by
  intro i j hij
  apply Fin.ext
  have hm : (2 : ℂ) * (i.val : ℂ) = 2 * (j.val : ℂ) := sub_right_inj.mp hij
  have heq : (i.val : ℂ) = (j.val : ℂ) := (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)) hm
  exact_mod_cast heq

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) : yui_aux_type% "LinearIndependent ℂ (fun i : Fin (lambda.toNat + 1) => Reduction.e y v i.val)" := by
  classical
  let μ : Fin (lambda.toNat + 1) → ℂ := fun i => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)
  have hev := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_T001
  have hinj := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_T001
  apply Fintype.linearIndependent_iff.mpr
  intro ζ hsum j
  let q : Polynomial ℂ := ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (μ k))
  have heval (i : Fin (lambda.toNat + 1)) : q.eval (μ i) = ∏ k ∈ Finset.univ.erase j, (μ i - μ k) := by
    simp [q, Polynomial.eval_prod]
  have hkill (i : Fin (lambda.toNat + 1)) (hij : i ≠ j) : q.eval (μ i) = 0 := by
    rw [heval]
    exact Finset.prod_eq_zero_iff.mpr ⟨i, by simp [hij], sub_self _⟩
  have hsurv : q.eval (μ j) ≠ 0 := by
    rw [heval]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro he
    have hjk : j = k := hinj he
    exact (Finset.mem_erase.mp hk).1 hjk.symm
  have ha (i : Fin (lambda.toNat + 1)) : (Polynomial.aeval h q) (Reduction.e y v i.val) = q.eval (μ i) • Reduction.e y v i.val :=
    Module.End.aeval_apply_of_mem_apply_eq_smul (p := q) (hev i).2
  have hh := congrArg (fun w : V => (Polynomial.aeval h q) w) hsum
  simp only [map_sum, map_smul, map_zero, ha] at hh
  have hs : (∑ i : Fin (lambda.toNat + 1), ζ i • (q.eval (μ i) • Reduction.e y v i.val)) = ζ j • (q.eval (μ j) • Reduction.e y v j.val) := by
    apply Finset.sum_eq_single j
    · intro i hi hij
      rw [hkill i hij, zero_smul, smul_zero]
    · simp
  rw [hs, smul_smul] at hh
  have hm : ζ j * q.eval (μ j) = 0 := (smul_eq_zero.mp hh).resolve_right (hev j).1
  exact (mul_eq_zero.mp hm).resolve_right hsurv

end Local_T002
open Local_T002 in
theorem T002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) :
    (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) := by
  classical
  have hev := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_T001
  have hinj := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_T001
  have hli := @yui_aux_0004 p K instK lambda V instV instCV x y h v M XM YM h_T001
  letI : FiniteDimensional ℂ V := h_T001.1.2.2.1
  have hcard : Fintype.card (Fin (lambda.toNat + 1)) = Module.finrank ℂ V := by
    rw [Fintype.card_fin, h_T001.1.2.2.2]
  refine ⟨hev, hinj, ?_⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' (fun i : Fin (lambda.toNat + 1) => Reduction.e y v i.val) hli hcard, ?_⟩
  intro i
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℂ) (fun i : Fin (lambda.toNat + 1) => Reduction.e y v i.val) hli hcard) i

namespace Local_T003
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ i : Fin (lambda.toNat + 1), ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) - ((lambda.toNat : ℂ) - 2 * ((lambda.toNat + 1 : ℕ) : ℂ)) ≠ 0" := by
  intro i hh
  have hi : (i.val : ℝ) < (lambda.toNat : ℝ) + 1 := by exact_mod_cast i.isLt
  have hh' := congrArg Complex.re hh
  simp at hh'
  push_cast at hh'
  linarith

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "(y ^ (lambda.toNat + 1)) v = 0" := by
  classical
  rcases h_T002.2.2 with ⟨b, hb⟩
  let z := (y ^ (lambda.toNat + 1)) v
  have hz := h_T001.2.2.2.2.1 (lambda.toNat + 1)
  change h z = _ at hz
  have hc (i : Fin (lambda.toNat + 1)) :
      b.repr (h z) i = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) * b.repr z i := by
    have he : (b.coord i).comp h =
        (((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • b.coord i) := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hb j, (h_T002.1 j).2, map_smul]
      rw [← hb j]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply, smul_eq_mul]
      split_ifs with hij
      · subst j; rfl
      · simp
    exact LinearMap.congr_fun he z
  have hz0 : z = 0 := by
    apply b.repr.injective
    ext i
    have hh := congrArg (fun w => b.repr w i) hz
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hh
    rw [hc i] at hh
    have hn := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002 i
    have : b.repr z i = 0 := (mul_eq_zero.mp (show
        (((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) -
        ((lambda.toNat : ℂ) - 2 * ((lambda.toNat + 1 : ℕ) : ℂ))) * b.repr z i = 0 by
          linear_combination hh)).resolve_left hn
    simpa using this
  exact hz0

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0" := by
  intro s hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [add_comm, pow_add, Module.End.mul_apply, @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002, map_zero]

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ i : ℕ, i ≠ 0 → (i.factorial : ℂ) = (i : ℂ) * ((i - 1).factorial : ℂ)" := by
  intro i hi
  have hn : i = (i - 1) + 1 := by omega
  have hh : i.factorial = i * (i - 1).factorial := by
    conv_lhs => rw [hn, Nat.factorial_succ]
    rw [← hn]
  exact_mod_cast hh

theorem yui_aux_0005 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ i : ℕ, i ≤ lambda.toNat → x (Reduction.e y v i) = if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)" := by
  intro i hi
  by_cases hz : i = 0
  · subst i
    simp [Reduction.e, h_T001.2.2.1]
  · rw [if_neg hz]
    unfold Reduction.e
    rw [map_smul, h_T001.2.2.2.2.2 i (by omega), smul_smul, smul_smul]
    congr 1
    have hf : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hfm : ((i - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i - 1)
    have hfac := @yui_aux_0004 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002 i hz
    rw [Nat.cast_add, Nat.cast_sub hi]
    rw [hfac]
    field_simp
    <;> ring

theorem yui_aux_0006 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ i : ℕ, i ≤ lambda.toNat → y (Reduction.e y v i) = if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0" := by
  intro i hi
  have hy : y (Reduction.e y v i) = (i.factorial : ℂ)⁻¹ • (y ^ (i+1)) v := by
    simp [Reduction.e, pow_succ', Module.End.mul_apply]
  by_cases ht : i < lambda.toNat
  · rw [if_pos ht, hy, Reduction.e, smul_smul]
    congr 1
    have hf : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  · rw [if_neg ht, hy, @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002 (i+1) (by omega), smul_zero]

theorem yui_aux_0007 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ (r i : ℕ), i ≤ lambda.toNat → (x ^ r) (Reduction.e y v i) = if r ≤ i then (( (lambda.toNat - i + r).factorial : ℂ) / ((lambda.toNat - i).factorial : ℂ)) • Reduction.e y v (i - r) else 0" := by
  intro r
  induction r with
  | zero =>
    intro i hi
    simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (lambda.toNat - i))]
  | succ r ih =>
    intro i hi
    rw [pow_succ', Module.End.mul_apply, ih i hi]
    by_cases hr : r ≤ i
    · rw [if_pos hr, map_smul, @yui_aux_0005 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002 (i-r) (by omega)]
      by_cases hs : r+1 ≤ i
      · rw [if_pos hs, if_neg (by omega), smul_smul]
        have hn : lambda.toNat - (i-r) + 1 = lambda.toNat - i + r + 1 := by omega
        have he : i-r-1 = i-(r+1) := by omega
        rw [hn, he]
        congr 1
        rw [← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      · rw [if_neg hs, if_pos (by omega), smul_zero]
    · rw [if_neg hr, map_zero, if_neg (by omega)]

theorem yui_aux_0008 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ (r i : ℕ), i ≤ lambda.toNat → YuiBasisObjects.dividedPower x r (Reduction.e y v i) = if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0" := by
  intro r i hi
  unfold YuiBasisObjects.dividedPower
  rw [LinearMap.smul_apply, @yui_aux_0007 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002 r i hi]
  by_cases hr : r ≤ i
  · simp only [if_pos hr, smul_smul]
    congr 1
    rw [Nat.cast_choose ℂ (show r ≤ lambda.toNat - i + r by omega)]
    rw [Nat.add_sub_cancel]
    ring
  · simp only [if_neg hr, smul_zero]

theorem yui_aux_0009 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ (r i : ℕ), i ≤ lambda.toNat → (y ^ r) (Reduction.e y v i) = if i + r ≤ lambda.toNat then (((i + r).factorial : ℂ) / (i.factorial : ℂ)) • Reduction.e y v (i + r) else 0" := by
  intro r
  induction r with
  | zero =>
    intro i hi
    simp [hi, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)]
  | succ r ih =>
    intro i hi
    rw [pow_succ', Module.End.mul_apply, ih i hi]
    by_cases hr : i+r ≤ lambda.toNat
    · rw [if_pos hr, map_smul, @yui_aux_0006 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002 (i+r) hr]
      by_cases hs : i+(r+1) ≤ lambda.toNat
      · rw [if_pos hs, if_pos (by omega), smul_smul]
        rw [← Nat.add_assoc]
        congr 1
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      · rw [if_neg hs, if_neg (by omega), smul_zero]
    · rw [if_neg hr, map_zero, if_neg (by omega)]

theorem yui_aux_0010 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) : yui_aux_type% "∀ (r i : ℕ), i ≤ lambda.toNat → YuiBasisObjects.dividedPower y r (Reduction.e y v i) = if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0" := by
  intro r i hi
  unfold YuiBasisObjects.dividedPower
  rw [LinearMap.smul_apply, @yui_aux_0009 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002 r i hi]
  by_cases hr : i+r ≤ lambda.toNat
  · simp only [if_pos hr, smul_smul]
    congr 1
    rw [Nat.cast_choose ℂ (show r ≤ i+r by omega), Nat.add_sub_cancel]
    ring
  · simp only [if_neg hr, smul_zero]

end Local_T003
open Local_T003 in
theorem T003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v))) (h_T002 : (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val)) :
    (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0)) := by
  refine ⟨h_T001.1, h_T002.2.2,
    @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002,
    @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002,
    ⟨@yui_aux_0005 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002,
     @yui_aux_0006 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002, ?_⟩,
    @yui_aux_0008 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002,
    @yui_aux_0010 p K instK lambda V instV instCV x y h v M XM YM h_T001 h_T002⟩
  intro i hi
  exact (h_T002.1 ⟨i, by omega⟩).2

namespace Local_T004
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) : yui_aux_type% "∀ m : M, (XM 1 m : V) = x (m : V)" := by
  intro m
  simpa [YuiBasisObjects.dividedPower] using h_H007.2.1 1 m

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) : yui_aux_type% "∀ (n : ℕ) (m : M), ((n • m : M) : V) = n • (m : V)" := by
  intro n m
  exact map_nsmul M.subtype n m

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) : yui_aux_type% "∀ (f : Module.End ℂ V) (Z : ℕ → Module.End ℤ M), (∀ (r : ℕ) (m : M), (Z r m : V) = YuiBasisObjects.dividedPower f r (m : V)) → ∀ r : ℕ, r.factorial • Z r = Z 1 ^ r" := by
  intro f Z hZ
  have h1 : ∀ m : M, (Z 1 m : V) = f (m : V) := by
    intro m
    simpa [YuiBasisObjects.dividedPower] using hZ 1 m
  have hp : ∀ (r : ℕ) (m : M), ((Z 1 ^ r) m : V) = (f ^ r) (m : V) := by
    intro r
    induction r with
    | zero => intro m; simp
    | succ r ih =>
      intro m
      simp only [pow_succ', Module.End.mul_apply]
      rw [h1, ih]
  intro r
  ext m
  have hn : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  change (r.factorial • Z r m : M).val = ((Z 1 ^ r) m : V)
  rw [@yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007, hZ, hp]
  change r.factorial • ((r.factorial : ℂ)⁻¹ • (f ^ r) (m : V)) = _
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn, one_smul]

end Local_T004
open Local_T004 in
theorem T004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) :
    (∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V)) := by
  have hx : ∀ m : M, (XM 1 m : V) = x (m : V) :=
    @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007
  have hy : ∀ m : M, (YM 1 m : V) = y (m : V) := by
    intro m
    simpa [YuiBasisObjects.dividedPower] using h_H007.2.2 1 m
  have hf := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007
  refine ⟨hf x XM h_H007.2.1, hf y YM h_H007.2.2, hx, hy, ?_⟩
  intro m
  have hc := congrArg (fun f : Module.End ℂ V => f (m : V)) h_H005.2.2
  simpa [Reduction.hM, LinearMap.sub_apply, Module.End.mul_apply, hx, hy] using hc

namespace Local_T005
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T003 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0))) : yui_aux_type% "∀ k : ℕ, k ≤ lambda.toNat → (YuiBasisObjects.dividedPower y lambda.toNat * YuiBasisObjects.dividedPower x lambda.toNat) (Reduction.e y v k) = if k = lambda.toNat then Reduction.e y v lambda.toNat else 0" := by
  intro k hk
  have hx := h_T003.2.2.2.2.2.1
  have hy := h_T003.2.2.2.2.2.2
  rw [Module.End.mul_apply, hx _ _ hk]
  by_cases he : k = lambda.toNat
  · subst k
    simp only [le_refl, if_true, Nat.sub_self, Nat.zero_add, Nat.choose_self, Nat.cast_one, one_smul]
    rw [hy _ _ (Nat.zero_le _)]
    simp
  · have hn : ¬lambda.toNat ≤ k := by omega
    simp [hn, he]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T003 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0))) : yui_aux_type% "∀ i j k : Fin (lambda.toNat + 1), Reduction.AC x y lambda.toNat i j (Reduction.e y v k.val) = if j = k then (Reduction.c lambda.toNat j : ℂ) • Reduction.e y v i.val else 0" := by
  classical
  intro i j k
  have hi : i.val ≤ lambda.toNat := by omega
  have hj : j.val ≤ lambda.toNat := by omega
  have hk : k.val ≤ lambda.toNat := by omega
  have hx := h_T003.2.2.2.2.2.1
  have hy := h_T003.2.2.2.2.2.2
  have hq := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_T003
  have hxtop : YuiBasisObjects.dividedPower x (lambda.toNat - i.val) (Reduction.e y v lambda.toNat) = Reduction.e y v i.val := by
    rw [hx _ _ (le_refl _)]
    simp [Nat.sub_le, Nat.sub_sub_self hi]
  change YuiBasisObjects.dividedPower x (lambda.toNat - i.val) ((YuiBasisObjects.dividedPower y lambda.toNat * YuiBasisObjects.dividedPower x lambda.toNat) (YuiBasisObjects.dividedPower y (lambda.toNat - j.val) (Reduction.e y v k.val))) = _
  rw [hy _ _ hk]
  by_cases he : j = k
  · subst k
    have hs : j.val + (lambda.toNat - j.val) = lambda.toNat := by omega
    simp only [hs, le_refl, if_true, map_smul]
    rw [hq _ (le_refl _)]
    simp only [if_true, map_smul, hxtop]
    rw [Nat.choose_symm hj]
    rfl
  · by_cases hb : k.val + (lambda.toNat - j.val) ≤ lambda.toNat
    · have hn : k.val + (lambda.toNat - j.val) ≠ lambda.toNat := by
        intro hh
        apply he
        apply Fin.ext
        omega
      simp only [hb, if_true, map_smul, hq _ hb, hn, if_false, smul_zero, map_zero, he]
    · simp [hb, he]

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T003 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0))) : yui_aux_type% "∀ j : Fin (lambda.toNat + 1), Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat" := by
  classical
  intro j
  have hd : Reduction.d lambda.toNat j = ∏ k ∈ (Finset.univ.erase j), Reduction.c lambda.toNat k := by
    unfold Reduction.d
    rw [← Finset.prod_erase (s := Finset.univ) (a := j) (by simp : (if j = j then 1 else Reduction.c lambda.toNat j) = 1)]
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    simp [hk.1]
  rw [hd]
  exact Finset.prod_erase_mul Finset.univ (Reduction.c lambda.toNat) (Finset.mem_univ j)

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T003 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0))) : yui_aux_type% "∀ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V, (∀ i, b i = Reduction.e y v i.val) → ∀ i j, Reduction.AC x y lambda.toNat i j = (Reduction.c lambda.toNat j : ℂ) • (b.coord j).smulRight (b i)" := by
  classical
  intro b hb i j
  apply b.ext
  intro k
  rw [LinearMap.smul_apply, LinearMap.smulRight_apply]
  change Reduction.AC x y lambda.toNat i j (b k) = (Reduction.c lambda.toNat j : ℂ) • (b.repr (b k) j • b i)
  rw [Module.Basis.repr_self_apply, hb k, @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_T003 i j k]
  by_cases hjk : j = k
  · subst k
    simp only [if_true, one_smul, hb]
  · simp [hjk, Ne.symm hjk]

end Local_T005
open Local_T005 in
theorem T005 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T003 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0))) :
    (∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.AC x y lambda.toNat i j * Reduction.AC x y lambda.toNat k l =
 if j = k then (Reduction.c lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat i l else 0) ∧
(∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧
((∑ j : Fin (lambda.toNat + 1),
 (Reduction.d lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat j j) =
 (Reduction.Dprod lambda.toNat : ℂ) • (1 : Module.End ℂ V)) := by
  classical
  rcases h_T003.2.1 with ⟨b, hb⟩
  have ha := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_T003
  have hd := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_T003
  let E : Fin (lambda.toNat + 1) → Fin (lambda.toNat + 1) → Module.End ℂ V :=
    fun i j => (b.coord j).smulRight (b i)
  have he : ∀ i j k, E i j (b k) = if j = k then b i else 0 := by
    intro i j k
    by_cases hjk : j = k
    · subst k
      simp [E, Module.Basis.coord_apply]
    · simp [E, Module.Basis.coord_apply, Module.Basis.repr_self_apply, hjk, Ne.symm hjk]
  have hac : ∀ i j, Reduction.AC x y lambda.toNat i j =
      (Reduction.c lambda.toNat j : ℂ) • E i j := by
    exact @yui_aux_0004 p K instK lambda V instV instCV x y h v M XM YM h_T003 b hb
  have hemul : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    apply b.ext
    intro a
    by_cases hla : l = a <;> by_cases hjk : j = k <;>
      simp [Module.End.mul_apply, he, hla, hjk]
  constructor
  · intro i j k l
    by_cases hjk : j = k
    · subst k
      simp [hac, smul_mul_assoc, mul_smul_comm, hemul, smul_smul, mul_comm]
    · simp [hac, smul_mul_assoc, mul_smul_comm, hemul, hjk]
  constructor
  · exact hd
  · apply b.ext
    intro k
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hdiag : ∀ j, Reduction.AC x y lambda.toNat j j (b k) =
        if j = k then (Reduction.c lambda.toNat j : ℂ) • b k else 0 := by
      intro j
      rw [hb, ha]
      by_cases hjk : j = k
      · subst j
        simp [hb]
      · simp [hjk]
    simp only [hdiag]
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, smul_smul]
    rw [← Nat.cast_mul, hd]

namespace Local_T006
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T004 : (∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) (h_T005 : (∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.AC x y lambda.toNat i j * Reduction.AC x y lambda.toNat k l =
 if j = k then (Reduction.c lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat i l else 0) ∧
(∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧
((∑ j : Fin (lambda.toNat + 1),
 (Reduction.d lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat j j) =
 (Reduction.Dprod lambda.toNat : ℂ) • (1 : Module.End ℂ V))) : yui_aux_type% "∀ i j : Fin (lambda.toNat + 1), ∀ m : M, (Reduction.A XM YM lambda.toNat i j m : V) = Reduction.AC x y lambda.toNat i j (m : V)" := by
  intro i j m
  simp only [Reduction.A, Reduction.AC, Module.End.mul_apply]
  rw [h_H007.2.1, h_H007.2.2, h_H007.2.1, h_H007.2.2]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T004 : (∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) (h_T005 : (∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.AC x y lambda.toNat i j * Reduction.AC x y lambda.toNat k l =
 if j = k then (Reduction.c lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat i l else 0) ∧
(∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧
((∑ j : Fin (lambda.toNat + 1),
 (Reduction.d lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat j j) =
 (Reduction.Dprod lambda.toNat : ℂ) • (1 : Module.End ℂ V))) : yui_aux_type% "∀ (n : ℕ) (m : M), ((n • m : M) : V) = (n : ℂ) • (m : V)" := by
  intro n m
  simp [Nat.cast_smul_eq_nsmul]

end Local_T006
open Local_T006 in
theorem T006 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T004 : (∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) (h_T005 : (∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.AC x y lambda.toNat i j * Reduction.AC x y lambda.toNat k l =
 if j = k then (Reduction.c lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat i l else 0) ∧
(∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧
((∑ j : Fin (lambda.toNat + 1),
 (Reduction.d lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat j j) =
 (Reduction.Dprod lambda.toNat : ℂ) • (1 : Module.End ℂ V))) :
    ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M)) := by
  classical
  have hA := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T004 h_T005
  have hs := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T004 h_T005
  refine ⟨h_T004, ?_, h_T005.2.1, ?_⟩
  · intro i j k l
    ext m
    have hc := congrArg (fun f : Module.End ℂ V => f (m : V)) (h_T005.1 i j k l)
    by_cases hjk : j = k
    · simp only [hjk, if_pos, Module.End.mul_apply, LinearMap.smul_apply] at hc ⊢
      rw [hA, hA, hs, hA]
      exact hc
    · simp only [hjk, if_false, Module.End.mul_apply, LinearMap.zero_apply] at hc ⊢
      rw [hA, hA]
      exact hc
  · ext m
    have hc := congrArg (fun f : Module.End ℂ V => f (m : V)) h_T005.2.2
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, hs, hA] using hc

theorem T007 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) :
    (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M) := by
  classical
  letI : FiniteDimensional ℂ V := h_H004.1
  have hcast : (lambda.toNat : ℤ) = lambda := Int.toNat_of_nonneg h_H003.1
  have hdim : Module.finrank ℂ V = lambda.toNat + 1 := by
    have hd := h_H004.2.1
    omega
  obtain ⟨I, bZ, bC, hcoe⟩ := h_H007.1
  letI : Finite I := Module.Finite.finite_basis bC
  letI : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = lambda.toNat + 1 :=
    (Module.finrank_eq_card_basis bC).symm.trans hdim
  let beta : I ≃ Fin (lambda.toNat + 1) := Fintype.equivFinOfCardEq hcard
  let b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M := bZ.reindex beta
  let q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M) :=
    b.baseChange K
  have hq : ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i) := by
    intro i
    exact Module.Basis.baseChange_apply K b i
  letI : FiniteDimensional K (TensorProduct ℤ K M) := Module.Finite.of_basis q
  have hdimK : Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis q
  have hn : 0 < lambda.toNat + 1 := Nat.succ_pos _
  let i : Fin (lambda.toNat + 1) := ⟨0, hn⟩
  have hq0 : q i ≠ 0 := by
    intro hz
    have hc := congrArg (fun w => q.repr w i) hz
    simpa using hc
  have hnontrivial : Nontrivial (TensorProduct ℤ K M) := ⟨⟨q i, 0, hq0⟩⟩
  exact ⟨⟨b, q, hq⟩, inferInstance, hdimK, hn, hnontrivial⟩

namespace Local_T008
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) (h_T007 : (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) : yui_aux_type% "(∀ (m : M) (a : K), Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧ (∀ (a : K) (m : M), (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧ (∀ (a b : K) (m : M), a • Reduction.pure K m b = Reduction.pure K m (a * b))" := by
  constructor
  · intro m a
    rfl
  constructor
  · intro a m
    rfl
  · intro a b m
    apply (Reduction.swap K M).injective
    rw [map_smul]
    change a • TensorProduct.tmul ℤ b m = TensorProduct.tmul ℤ (a * b) m
    rfl

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) (h_T007 : (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) : yui_aux_type% "∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), (∀ f, G f = Reduction.F K f) ∧ (∀ (f : Module.End ℤ M) (a : K) (m : M), Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))" := by
  refine ⟨(Module.End.baseChangeHom ℤ K M).toRingHom, ?_, ?_⟩
  · intro f
    rfl
  · intro f a m
    exact LinearMap.baseChange_tmul f a m

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) (h_T007 : (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) : yui_aux_type% "(∀ (f : Module.End ℤ M) (m : M) (a : K), Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧ (∀ (f : Module.End ℤ M) (w : Reduction.VK K M), Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w))" := by
  obtain ⟨hs, hi, _⟩ := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_E001 h_T007
  obtain ⟨G, hG, hF⟩ := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_E001 h_T007
  constructor
  · intro f m a
    change (Reduction.swap K M).symm (Reduction.F K f (Reduction.swap K M (TensorProduct.tmul ℤ m a))) = _
    rw [hs, hF, hi]
  · intro f w
    change (Reduction.swap K M) ((Reduction.swap K M).symm (Reduction.F K f (Reduction.swap K M w))) = _
    exact (Reduction.swap K M).apply_symm_apply _

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) (h_T007 : (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) : yui_aux_type% "∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)), YuiBasisObjects.Stable W (Reduction.ind K f) ↔ YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)" := by
  have ht := (@yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_E001 h_T007).2
  intro f W
  constructor
  · intro hw z hz
    rcases Submodule.mem_map.mp hz with ⟨w, hw', rfl⟩
    exact Submodule.mem_map.mpr ⟨Reduction.ind K f w, hw w hw', ht f w⟩
  · intro hz w hw
    have hmem := hz ((Reduction.swap K M) w) (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)
    rcases Submodule.mem_map.mp hmem with ⟨w', hw', he⟩
    have he' : w' = Reduction.ind K f w := (Reduction.swap K M).injective (he.trans (ht f w).symm)
    simpa only [he'] using hw'

end Local_T008
open Local_T008 in
theorem T008 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) (h_T007 : (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) :
    ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M)) := by
  obtain ⟨hs, hi, hscalar⟩ := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_E001 h_T007
  have hF := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_E001 h_T007
  obtain ⟨hind, ht⟩ := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_E001 h_T007
  have hstable := @yui_aux_0004 p K instK lambda V instV instCV x y h v M XM YM h_E001 h_T007
  refine ⟨h_T007, hF, hscalar, hs, hi, hind, ht, hstable, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W
    ext w
    simp only [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  · intro Z
    ext z
    simp only [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  · exact Submodule.map_bot _
  · ext z
    simp only [Submodule.mem_map_equiv, Submodule.mem_top]
  · exact Submodule.map_bot _
  · ext w
    simp only [Submodule.mem_map_equiv, Submodule.mem_top]
  · letI : Nontrivial (TensorProduct ℤ K M) := h_T007.2.2.2.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (TensorProduct ℤ K M)
    exact ⟨⟨(Reduction.swap K M).symm a, (Reduction.swap K M).symm b,
      fun he => hab ((Reduction.swap K M).symm.injective he)⟩⟩

namespace Local_T009
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) : yui_aux_type% "lambda.toNat < p ∧ ∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0" := by
  have hlt : lambda.toNat < p := by omega
  haveI : CharP K p := h_H002
  refine ⟨hlt, ?_⟩
  intro r hr hz
  have hd : p ∣ r.factorial := (CharP.cast_eq_zero_iff K p r.factorial).mp hz
  have hpr : p ≤ r := h_H001.dvd_factorial.mp hd
  omega

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) : yui_aux_type% "∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0" := by
  have hf := (@yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003).2
  intro j hz
  have hj : j.val ≤ lambda.toNat := Nat.le_of_lt_succ j.isLt
  have hn : Nat.choose lambda.toNat j.val * j.val.factorial * (lambda.toNat - j.val).factorial = lambda.toNat.factorial := Nat.choose_mul_factorial_mul_factorial hj
  have hc : (Reduction.c lambda.toNat j : K) * (j.val.factorial : K) * ((lambda.toNat - j.val).factorial : K) = (lambda.toNat.factorial : K) := by
    simpa only [Reduction.c, Nat.cast_mul] using congrArg (fun n : ℕ => (n : K)) hn
  apply hf lambda.toNat le_rfl
  rw [← hc, hz, zero_mul, zero_mul]

end Local_T009
open Local_T009 in
theorem T009 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) :
    lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0 := by
  have hf := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003
  have hc := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003
  refine ⟨hf.1, hf.2, hc, ?_⟩
  simp only [Reduction.Dprod, Nat.cast_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)

namespace Local_T010
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) (h_T009 : lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) : yui_aux_type% "∀ (n : ℕ) (f : Module.End ℤ M), Reduction.F K (n • f) = (n : K) • Reduction.F K f" := by
  rcases h_T008.2.1 with ⟨G, hG, _⟩
  intro n f
  rw [← hG, map_nsmul, hG]
  simp only [Nat.cast_smul_eq_nsmul]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) (h_T009 : lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) : yui_aux_type% "∀ r : ℕ, r ≤ lambda.toNat → Reduction.F K (XM r) = (r.factorial : K)⁻¹ • Reduction.F K (XM 1) ^ r ∧ Reduction.F K (YM r) = (r.factorial : K)⁻¹ • Reduction.F K (YM 1) ^ r" := by
  rcases h_T008.2.1 with ⟨G, hG, _⟩
  have hnat := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T006 h_T008 h_T009
  have hp : ∀ (f : Module.End ℤ M) (r : ℕ), Reduction.F K (f ^ r) = Reduction.F K f ^ r := by
    intro f r
    simpa only [hG] using map_pow G f r
  intro r hr
  have hn := h_T009.2.1 r hr
  constructor
  · have he := congrArg (Reduction.F K) (h_T006.1.1 r)
    rw [hnat, hp] at he
    rw [← he, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · have he := congrArg (Reduction.F K) (h_T006.1.2.1 r)
    rw [hnat, hp] at he
    rw [← he, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) (h_T009 : lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) : yui_aux_type% "(∀ f : Fin (lambda.toNat + 1) → Module.End ℤ M, Reduction.F K (∑ j, f j) = ∑ j, Reduction.F K (f j)) ∧ (∀ j b : Fin (lambda.toNat + 1), ((Reduction.c lambda.toNat j : K)⁻¹ * (Reduction.c lambda.toNat b : K)⁻¹) * (Reduction.c lambda.toNat j : K) = (Reduction.c lambda.toNat b : K)⁻¹)" := by
  rcases h_T008.2.1 with ⟨G, hG, _⟩
  constructor
  · intro f
    have he := map_sum G f Finset.univ
    simpa only [hG] using he
  · intro j b
    calc
      ((Reduction.c lambda.toNat j : K)⁻¹ * (Reduction.c lambda.toNat b : K)⁻¹) *
          (Reduction.c lambda.toNat j : K) =
          ((Reduction.c lambda.toNat j : K)⁻¹ * (Reduction.c lambda.toNat j : K)) *
            (Reduction.c lambda.toNat b : K)⁻¹ := by ring
      _ = (Reduction.c lambda.toNat b : K)⁻¹ := by
        rw [inv_mul_cancel₀ (h_T009.2.2.1 j), one_mul]

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) (h_T009 : lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) : yui_aux_type% "Reduction.MatrixUnits (lambda.toNat + 1) (Reduction.T K XM YM lambda.toNat)" := by
  classical
  rcases h_T008.2.1 with ⟨G, hG, _⟩
  have hnat := @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T006 h_T008 h_T009
  have hm : ∀ f g : Module.End ℤ M, Reduction.F K (f * g) = Reduction.F K f * Reduction.F K g := by
    intro f g
    simpa only [hG] using map_mul G f g
  have hconv := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T006 h_T008 h_T009
  constructor
  · intro i j a b
    unfold Reduction.T
    rw [smul_mul_assoc, mul_smul_comm, ← hm, h_T006.2.1]
    split_ifs with he
    · subst a
      rw [hnat, smul_smul, smul_smul]
      congr 1
      exact hconv.2 j b
    · simp [← hG]
  · have hs := congrArg G h_T006.2.2.2
    simp only [hG] at hs
    rw [hconv.1] at hs
    simp only [hnat] at hs
    have hone : Reduction.F K (1 : Module.End ℤ M) = 1 := by
      simpa only [hG] using G.map_one
    rw [hone] at hs
    have hd : ∀ j : Fin (lambda.toNat + 1),
        (Reduction.d lambda.toNat j : K) =
        (Reduction.Dprod lambda.toNat : K) * (Reduction.c lambda.toNat j : K)⁻¹ := by
      intro j
      calc
        (Reduction.d lambda.toNat j : K) =
            (Reduction.d lambda.toNat j : K) *
              ((Reduction.c lambda.toNat j : K) * (Reduction.c lambda.toNat j : K)⁻¹) := by
                rw [mul_inv_cancel₀ (h_T009.2.2.1 j), mul_one]
        _ = (Reduction.Dprod lambda.toNat : K) *
              (Reduction.c lambda.toNat j : K)⁻¹ := by
                rw [← mul_assoc, ← Nat.cast_mul, h_T006.2.2.1 j]
    have ht : (∑ j, Reduction.T K XM YM lambda.toNat j j) =
        (Reduction.Dprod lambda.toNat : K)⁻¹ •
          (∑ j, (Reduction.d lambda.toNat j : K) •
            Reduction.F K (Reduction.A XM YM lambda.toNat j j)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hd, smul_smul, ← mul_assoc, inv_mul_cancel₀ h_T009.2.2.2, one_mul]
      rfl
    rw [ht, hs, smul_smul, inv_mul_cancel₀ h_T009.2.2.2, one_smul]

theorem yui_aux_0005 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) (h_T009 : lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) : yui_aux_type% "∀ W : Submodule K (TensorProduct ℤ K M), YuiBasisObjects.Stable W (Reduction.F K (XM 1)) → YuiBasisObjects.Stable W (Reduction.F K (YM 1)) → ∀ i j : Fin (lambda.toNat + 1), YuiBasisObjects.Stable W (Reduction.T K XM YM lambda.toNat i j)" := by
  have hfac := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T006 h_T008 h_T009
  rcases h_T008.2.1 with ⟨G, hG, _⟩
  have hm : ∀ f g : Module.End ℤ M, Reduction.F K (f * g) = Reduction.F K f * Reduction.F K g := by
    intro f g
    simpa only [hG] using map_mul G f g
  intro W hX hY
  have hmul : ∀ f g : Module.End K (TensorProduct ℤ K M),
      YuiBasisObjects.Stable W f → YuiBasisObjects.Stable W g →
      YuiBasisObjects.Stable W (f * g) := by
    intro f g hf hg w hw
    exact hf (g w) (hg w hw)
  have hsmul : ∀ (a : K) (f : Module.End K (TensorProduct ℤ K M)),
      YuiBasisObjects.Stable W f → YuiBasisObjects.Stable W (a • f) := by
    intro a f hf w hw
    exact W.smul_mem a (hf w hw)
  have hpow : ∀ f : Module.End K (TensorProduct ℤ K M),
      YuiBasisObjects.Stable W f → ∀ r : ℕ, YuiBasisObjects.Stable W (f ^ r) := by
    intro f hf r
    induction r with
    | zero =>
      intro w hw
      simpa using hw
    | succ r ih =>
      rw [pow_succ]
      exact hmul _ _ ih hf
  have hx : ∀ r : ℕ, r ≤ lambda.toNat → YuiBasisObjects.Stable W (Reduction.F K (XM r)) := by
    intro r hr
    rw [(hfac r hr).1]
    exact hsmul _ _ (hpow _ hX r)
  have hy : ∀ r : ℕ, r ≤ lambda.toNat → YuiBasisObjects.Stable W (Reduction.F K (YM r)) := by
    intro r hr
    rw [(hfac r hr).2]
    exact hsmul _ _ (hpow _ hY r)
  intro i j
  unfold Reduction.T Reduction.A
  rw [hm, hm, hm]
  exact hsmul _ _ (hmul _ _
    (hmul _ _ (hx _ (Nat.sub_le _ _))
      (hmul _ _ (hy _ le_rfl) (hx _ le_rfl)))
    (hy _ (Nat.sub_le _ _)))

end Local_T010
open Local_T010 in
theorem T010 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) (h_T009 : lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) :
    (lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) ∧
Reduction.MatrixUnits (lambda.toNat + 1) (Reduction.T K XM YM lambda.toNat) ∧
(∀ r : ℕ, r ≤ lambda.toNat →
 Reduction.F K (XM r) = (r.factorial : K)⁻¹ • Reduction.F K (XM 1) ^ r ∧
 Reduction.F K (YM r) = (r.factorial : K)⁻¹ • Reduction.F K (YM 1) ^ r) ∧ (∀ W : Submodule K (TensorProduct ℤ K M),
 YuiBasisObjects.Stable W (Reduction.F K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.F K (YM 1)) →
 ∀ i j : Fin (lambda.toNat + 1),
 YuiBasisObjects.Stable W (Reduction.T K XM YM lambda.toNat i j)) := by
  exact ⟨h_T009,
    @yui_aux_0004 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T006 h_T008 h_T009,
    @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T006 h_T008 h_T009,
    @yui_aux_0005 p K instK lambda V instV instCV x y h v M XM YM h_H007 h_T006 h_T008 h_T009⟩

theorem T011 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M)  :
    ∀ (k0 : Type uK) [Field k0] (U0 : Type (max uK uV))
 [AddCommGroup U0] [Module k0 U0] (n0 : ℕ)
 (t : Fin n0 → Fin n0 → Module.End k0 U0),
 0 < n0 → FiniteDimensional k0 U0 → Module.finrank k0 U0 = n0 →
 Reduction.MatrixUnits n0 t →
 ∀ W0 : Submodule k0 U0, (∀ i j, YuiBasisObjects.Stable W0 (t i j)) →
 W0 = ⊥ ∨ W0 = ⊤ := by
  classical
  intro k0 _ U0 _ _ n0 t hn hfd hdim ht W hstable
  rcases ht with ⟨hmul, hsum⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨w, hwW, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hdiag : (∑ j, t j j w) = w := by
      simpa only [LinearMap.sum_apply, Module.End.one_apply] using
        congrArg (fun f : Module.End k0 U0 => f w) hsum
    have hex : ∃ j, t j j w ≠ 0 := by
      by_contra hh
      push_neg at hh
      have : w = 0 := by
        rw [← hdiag]
        exact Finset.sum_eq_zero fun j _ => hh j
      exact hw this
    obtain ⟨j, hj⟩ := hex
    let u : U0 := t j j w
    have huW : u ∈ W := hstable j j w hwW
    have hu : u ≠ 0 := hj
    have hfix : t j j u = u := by
      change (t j j * t j j) w = t j j w
      rw [hmul, if_pos rfl]
    let b : Fin n0 → U0 := fun i => t i j u
    have hbW : ∀ i, b i ∈ W := fun i => hstable i j u huW
    have hact : ∀ k i, t j k (b i) = if k = i then u else 0 := by
      intro k i
      change (t j k * t i j) u = _
      rw [hmul]
      by_cases hki : k = i
      · simp [hki, hfix]
      · simp [hki]
    have hli : LinearIndependent k0 b := by
      apply Fintype.linearIndependent_iff.mpr
      intro a ha k
      have heq := congrArg (fun z : U0 => t j k z) ha
      have hz : a k • u = 0 := by
        simpa [map_sum, hact, map_smul] using heq
      exact (smul_eq_zero.mp hz).resolve_right hu
    have hspan : Submodule.span k0 (Set.range b) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simpa using hdim.symm)
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hbW i

namespace Local_T012
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) : yui_aux_type% "∃ J : Module.End ℤ M →+* Module.End K (Reduction.VK K M), ∀ f, J f = Reduction.ind K f" := by
  rcases h_T008.2.1 with ⟨G, hG, _⟩
  let J : Module.End ℤ M →+* Module.End K (Reduction.VK K M) :=
    (Reduction.swap K M).symm.conjRingEquiv.toRingHom.comp G
  refine ⟨J, ?_⟩
  intro f
  ext w
  change (Reduction.swap K M).symm (G f (Reduction.swap K M w)) =
    (Reduction.swap K M).symm (Reduction.F K f (Reduction.swap K M w))
  rw [hG]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) : yui_aux_type% "∀ w : V, (2 : ℂ) • w = (2 : ℤ) • w ∧ (-2 : ℂ) • w = (-2 : ℤ) • w" := by
  intro w
  constructor
  · simpa only [Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℂ (2 : ℤ) w)
  · simpa only [Int.cast_neg, Int.cast_ofNat] using (Int.cast_smul_eq_zsmul ℂ (-2 : ℤ) w)

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) : yui_aux_type% "(Reduction.hM XM YM * XM 1 - XM 1 * Reduction.hM XM YM = (2 : ℤ) • XM 1) ∧ (Reduction.hM XM YM * YM 1 - YM 1 * Reduction.hM XM YM = (-2 : ℤ) • YM 1) ∧ (XM 1 * YM 1 - YM 1 * XM 1 = Reduction.hM XM YM)" := by
  rcases h_T006.1 with ⟨_, _, hx, hy, hh⟩
  have hs := @yui_aux_0002 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007 h_T006 h_T008
  refine ⟨?_, ?_, rfl⟩
  · ext m
    have he := congrArg (fun f : Module.End ℂ V => f (m : V)) h_H005.1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at he ⊢
    rw [Submodule.coe_sub, Submodule.coe_smul, hh, hx, hx, hh]
    exact he.trans (hs (x (m : V))).1
  · ext m
    have he := congrArg (fun f : Module.End ℂ V => f (m : V)) h_H005.2.1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at he ⊢
    rw [Submodule.coe_sub, Submodule.coe_smul, hh, hy, hy, hh]
    exact he.trans (hs (y (m : V))).2

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) : yui_aux_type% "∀ (n : ℤ) (f g t : Module.End ℤ M), f * g - g * f = n • t → Reduction.ind K f * Reduction.ind K g - Reduction.ind K g * Reduction.ind K f = (n : K) • Reduction.ind K t" := by
  rcases @yui_aux_0001 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007 h_T006 h_T008 with ⟨J, hJ⟩
  intro n f g t he
  have hz : J (n • t) = (n : K) • J t := by
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have ht : J (f * g - g * f) = J (n • t) := congrArg J he
  rw [map_sub, map_mul, map_mul, hz] at ht
  simpa only [hJ] using ht

end Local_T012
open Local_T012 in
theorem T012 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) :
    ((Reduction.hM XM YM) * (XM 1) - (XM 1) * (Reduction.hM XM YM) = (2 : ℤ) • (XM 1) ∧
(Reduction.hM XM YM) * (YM 1) - (YM 1) * (Reduction.hM XM YM) = (-2 : ℤ) • (YM 1) ∧
(XM 1) * (YM 1) - (YM 1) * (XM 1) = (Reduction.hM XM YM)) ∧
((Reduction.ind K (Reduction.hM XM YM)) * (Reduction.ind K (XM 1)) - (Reduction.ind K (XM 1)) * (Reduction.ind K (Reduction.hM XM YM)) = (2 : K) • (Reduction.ind K (XM 1)) ∧
(Reduction.ind K (Reduction.hM XM YM)) * (Reduction.ind K (YM 1)) - (Reduction.ind K (YM 1)) * (Reduction.ind K (Reduction.hM XM YM)) = (-2 : K) • (Reduction.ind K (YM 1)) ∧
(Reduction.ind K (XM 1)) * (Reduction.ind K (YM 1)) - (Reduction.ind K (YM 1)) * (Reduction.ind K (XM 1)) = (Reduction.ind K (Reduction.hM XM YM))) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) ∧
  YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) ∧
  YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM))) ↔
 (∀ a b c : K, YuiBasisObjects.Stable W
 (a • Reduction.ind K (XM 1) + b • Reduction.ind K (YM 1) +
 c • Reduction.ind K (Reduction.hM XM YM)))) := by
  have hi := @yui_aux_0003 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007 h_T006 h_T008
  have ht := @yui_aux_0004 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007 h_T006 h_T008
  refine ⟨hi, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [Int.cast_ofNat] using ht 2 (Reduction.hM XM YM) (XM 1) (XM 1) hi.1
  · simpa only [Int.cast_neg, Int.cast_ofNat] using ht (-2) (Reduction.hM XM YM) (YM 1) (YM 1) hi.2.1
  · simpa only [Int.cast_one, one_smul] using
      ht 1 (XM 1) (YM 1) (Reduction.hM XM YM) (by simpa only [one_smul] using hi.2.2)
  · intro W
    constructor
    · rintro ⟨hx, hy, hh⟩ a b c w hw
      change a • (Reduction.ind K (XM 1) w) + b • (Reduction.ind K (YM 1) w) +
        c • (Reduction.ind K (Reduction.hM XM YM) w) ∈ W
      exact W.add_mem (W.add_mem (W.smul_mem a (hx w hw)) (W.smul_mem b (hy w hw)))
        (W.smul_mem c (hh w hw))
    · intro hall
      exact ⟨by simpa only [one_smul, zero_smul, add_zero] using hall 1 0 0,
        by simpa only [one_smul, zero_smul, zero_add, add_zero] using hall 0 1 0,
        by simpa only [one_smul, zero_smul, zero_add] using hall 0 0 1⟩

theorem T013 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_T003 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0))) (h_T006 : ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M))) (h_T008 : ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M))) (h_T010 : (lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) ∧
Reduction.MatrixUnits (lambda.toNat + 1) (Reduction.T K XM YM lambda.toNat) ∧
(∀ r : ℕ, r ≤ lambda.toNat →
 Reduction.F K (XM r) = (r.factorial : K)⁻¹ • Reduction.F K (XM 1) ^ r ∧
 Reduction.F K (YM r) = (r.factorial : K)⁻¹ • Reduction.F K (YM 1) ^ r) ∧ (∀ W : Submodule K (TensorProduct ℤ K M),
 YuiBasisObjects.Stable W (Reduction.F K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.F K (YM 1)) →
 ∀ i j : Fin (lambda.toNat + 1),
 YuiBasisObjects.Stable W (Reduction.T K XM YM lambda.toNat i j))) (h_T011 : @YuiPortTypes.T011 p K instK lambda V instV instCV x y h v M XM YM) (h_T012 : ((Reduction.hM XM YM) * (XM 1) - (XM 1) * (Reduction.hM XM YM) = (2 : ℤ) • (XM 1) ∧
(Reduction.hM XM YM) * (YM 1) - (YM 1) * (Reduction.hM XM YM) = (-2 : ℤ) • (YM 1) ∧
(XM 1) * (YM 1) - (YM 1) * (XM 1) = (Reduction.hM XM YM)) ∧
((Reduction.ind K (Reduction.hM XM YM)) * (Reduction.ind K (XM 1)) - (Reduction.ind K (XM 1)) * (Reduction.ind K (Reduction.hM XM YM)) = (2 : K) • (Reduction.ind K (XM 1)) ∧
(Reduction.ind K (Reduction.hM XM YM)) * (Reduction.ind K (YM 1)) - (Reduction.ind K (YM 1)) * (Reduction.ind K (Reduction.hM XM YM)) = (-2 : K) • (Reduction.ind K (YM 1)) ∧
(Reduction.ind K (XM 1)) * (Reduction.ind K (YM 1)) - (Reduction.ind K (YM 1)) * (Reduction.ind K (XM 1)) = (Reduction.ind K (Reduction.hM XM YM))) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) ∧
  YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) ∧
  YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM))) ↔
 (∀ a b c : K, YuiBasisObjects.Stable W
 (a • Reduction.ind K (XM 1) + b • Reduction.ind K (YM 1) +
 c • Reduction.ind K (Reduction.hM XM YM))))) :
    Nontrivial (Reduction.VK K M) ∧
∀ W : Submodule K (Reduction.VK K M),
 YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM)) →
 W = ⊥ ∨ W = ⊤ := by
  rcases h_T008 with ⟨hDim, hF, hS⟩
  rcases hS with ⟨hScalar, hSwap, hInv, hInd, hInter, hStable, hBack, hForward, hBot, hTop, hBotInv, hTopInv, hNontriv⟩
  refine ⟨hNontriv, ?_⟩
  intro W hX hY hH
  let Z : Submodule K (TensorProduct ℤ K M) :=
    W.map (Reduction.swap K M).toLinearMap
  have hZX : YuiBasisObjects.Stable Z (Reduction.F K (XM 1)) :=
    (hStable (XM 1) W).mp hX
  have hZY : YuiBasisObjects.Stable Z (Reduction.F K (YM 1)) :=
    (hStable (YM 1) W).mp hY
  have hZT : ∀ i j : Fin (lambda.toNat + 1),
      YuiBasisObjects.Stable Z (Reduction.T K XM YM lambda.toNat i j) :=
    h_T010.2.2.2 Z hZX hZY
  have hCases : Z = ⊥ ∨ Z = ⊤ :=
    h_T011 K (TensorProduct ℤ K M) (lambda.toNat + 1)
      (Reduction.T K XM YM lambda.toNat)
      hDim.2.2.2.1 hDim.2.1 hDim.2.2.1 h_T010.2.1 Z hZT
  rcases hCases with hZ | hZ
  · left
    calc
      W = Z.map (Reduction.swap K M).symm.toLinearMap := (hBack W).symm
      _ = ⊥ := by rw [hZ, hBotInv]
  · right
    calc
      W = Z.map (Reduction.swap K M).symm.toLinearMap := (hBack W).symm
      _ = ⊤ := by rw [hZ, hTopInv]

private theorem __connected_T001 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) :
    (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ v ≠ 0 ∧ x v = 0 ∧ h v = (lambda.toNat : ℂ) • v ∧ (∀ i : ℕ, h ((y ^ i) v) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • ((y ^ i) v)) ∧
(∀ i : ℕ, 1 ≤ i → x ((y ^ i) v) =
 ((i : ℂ) * ((lambda.toNat : ℂ) - (i : ℂ) + 1)) • ((y ^ (i - 1)) v)) := by
  exact @T001 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006

private theorem __connected_T002 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) :
    (∀ i : Fin (lambda.toNat + 1), Reduction.e y v i.val ≠ 0 ∧
 h (Reduction.e y v i.val) = ((lambda.toNat : ℂ) - 2 * (i.val : ℂ)) • Reduction.e y v i.val) ∧
Function.Injective (fun i : Fin (lambda.toNat + 1) => (lambda.toNat : ℂ) - 2 * (i.val : ℂ)) ∧
(∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) := by
  exact @T002 p K instK lambda V instV instCV x y h v M XM YM (@__connected_T001 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006)

private theorem __connected_T003 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) :
    (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lambda.toNat + 1) ∧ (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℂ V,
 ∀ i, b i = Reduction.e y v i.val) ∧ (y ^ (lambda.toNat + 1)) v = 0 ∧
(∀ s : ℕ, lambda.toNat + 1 ≤ s → (y ^ s) v = 0) ∧
((∀ i : ℕ, i ≤ lambda.toNat →
 x (Reduction.e y v i) =
  if i = 0 then 0 else ((lambda.toNat - i + 1 : ℕ) : ℂ) • Reduction.e y v (i - 1)) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 y (Reduction.e y v i) =
  if i < lambda.toNat then ((i + 1 : ℕ) : ℂ) • Reduction.e y v (i + 1) else 0) ∧
(∀ i : ℕ, i ≤ lambda.toNat →
 h (Reduction.e y v i) = ((lambda.toNat : ℂ) - 2 * (i : ℂ)) • Reduction.e y v i)) ∧ ((∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower x r (Reduction.e y v i) =
  if r ≤ i then (Nat.choose (lambda.toNat - i + r) r : ℂ) • Reduction.e y v (i - r) else 0) ∧
(∀ (r i : ℕ), i ≤ lambda.toNat →
 YuiBasisObjects.dividedPower y r (Reduction.e y v i) =
  if i + r ≤ lambda.toNat then (Nat.choose (i + r) r : ℂ) • Reduction.e y v (i + r) else 0)) := by
  exact @T003 p K instK lambda V instV instCV x y h v M XM YM (@__connected_T001 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006) (@__connected_T002 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006)

private theorem __connected_T004 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) :
    (∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V)) := by
  exact @T004 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007

private theorem __connected_T005 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) :
    (∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.AC x y lambda.toNat i j * Reduction.AC x y lambda.toNat k l =
 if j = k then (Reduction.c lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat i l else 0) ∧
(∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧
((∑ j : Fin (lambda.toNat + 1),
 (Reduction.d lambda.toNat j : ℂ) • Reduction.AC x y lambda.toNat j j) =
 (Reduction.Dprod lambda.toNat : ℂ) • (1 : Module.End ℂ V)) := by
  exact @T005 p K instK lambda V instV instCV x y h v M XM YM (@__connected_T003 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006)

private theorem __connected_T006 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) :
    ((∀ r : ℕ, r.factorial • XM r = XM 1 ^ r) ∧
(∀ r : ℕ, r.factorial • YM r = YM 1 ^ r) ∧
(∀ m : M, (XM 1 m : V) = x (m : V)) ∧
(∀ m : M, (YM 1 m : V) = y (m : V)) ∧
(∀ m : M, (Reduction.hM XM YM m : V) = h (m : V))) ∧ ((∀ i j k l : Fin (lambda.toNat + 1),
 Reduction.A XM YM lambda.toNat i j * Reduction.A XM YM lambda.toNat k l =
 if j = k then Reduction.c lambda.toNat j • Reduction.A XM YM lambda.toNat i l else 0)) ∧ (∀ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j * Reduction.c lambda.toNat j = Reduction.Dprod lambda.toNat) ∧ ((∑ j : Fin (lambda.toNat + 1),
 Reduction.d lambda.toNat j • Reduction.A XM YM lambda.toNat j j) =
 Reduction.Dprod lambda.toNat • (1 : Module.End ℤ M)) := by
  exact @T006 p K instK lambda V instV instCV x y h v M XM YM h_H007 (@__connected_T004 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007) (@__connected_T005 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006)

private theorem __connected_T007 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) :
    (∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M) := by
  exact @T007 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H007

private theorem __connected_T008 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) :
    ((∃ b : Module.Basis (Fin (lambda.toNat + 1)) ℤ M,
 ∃ q : Module.Basis (Fin (lambda.toNat + 1)) K (TensorProduct ℤ K M),
 ∀ i, q i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
FiniteDimensional K (TensorProduct ℤ K M) ∧
Module.finrank K (TensorProduct ℤ K M) = lambda.toNat + 1 ∧
0 < lambda.toNat + 1 ∧ Nontrivial (TensorProduct ℤ K M)) ∧ (∃ G : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M),
 (∀ f, G f = Reduction.F K f) ∧
 (∀ (f : Module.End ℤ M) (a : K) (m : M),
 Reduction.F K f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧ ((∀ (a b : K) (m : M),
 a • Reduction.pure K m b = Reduction.pure K m (a * b)) ∧
(∀ (m : M) (a : K),
 Reduction.swap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a : K) (m : M),
 (Reduction.swap K M).symm (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ m a) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 Reduction.ind K f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (w : Reduction.VK K M),
 Reduction.swap K M (Reduction.ind K f w) = Reduction.F K f (Reduction.swap K M w)) ∧
(∀ (f : Module.End ℤ M) (W : Submodule K (Reduction.VK K M)),
 YuiBasisObjects.Stable W (Reduction.ind K f) ↔
 YuiBasisObjects.Stable (W.map (Reduction.swap K M).toLinearMap) (Reduction.F K f)) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (W.map (Reduction.swap K M).toLinearMap).map (Reduction.swap K M).symm.toLinearMap = W) ∧
(∀ Z : Submodule K (TensorProduct ℤ K M),
 (Z.map (Reduction.swap K M).symm.toLinearMap).map (Reduction.swap K M).toLinearMap = Z) ∧
((⊥ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊥) ∧
((⊤ : Submodule K (Reduction.VK K M)).map (Reduction.swap K M).toLinearMap = ⊤) ∧
((⊥ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊥) ∧
((⊤ : Submodule K (TensorProduct ℤ K M)).map (Reduction.swap K M).symm.toLinearMap = ⊤) ∧
Nontrivial (Reduction.VK K M)) := by
  exact @T008 p K instK lambda V instV instCV x y h v M XM YM h_E001 (@__connected_T007 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H007)

private theorem __connected_T009 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) :
    lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0 := by
  exact @T009 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003

private theorem __connected_T010 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) :
    (lambda.toNat < p ∧
(∀ r : ℕ, r ≤ lambda.toNat → (r.factorial : K) ≠ 0) ∧
(∀ j : Fin (lambda.toNat + 1), (Reduction.c lambda.toNat j : K) ≠ 0) ∧
(Reduction.Dprod lambda.toNat : K) ≠ 0) ∧
Reduction.MatrixUnits (lambda.toNat + 1) (Reduction.T K XM YM lambda.toNat) ∧
(∀ r : ℕ, r ≤ lambda.toNat →
 Reduction.F K (XM r) = (r.factorial : K)⁻¹ • Reduction.F K (XM 1) ^ r ∧
 Reduction.F K (YM r) = (r.factorial : K)⁻¹ • Reduction.F K (YM 1) ^ r) ∧ (∀ W : Submodule K (TensorProduct ℤ K M),
 YuiBasisObjects.Stable W (Reduction.F K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.F K (YM 1)) →
 ∀ i j : Fin (lambda.toNat + 1),
 YuiBasisObjects.Stable W (Reduction.T K XM YM lambda.toNat i j)) := by
  exact @T010 p K instK lambda V instV instCV x y h v M XM YM h_H007 (@__connected_T006 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006 h_H007) (@__connected_T008 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H007 h_E001) (@__connected_T009 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003)

private theorem __connected_T011 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M)  :
    ∀ (k0 : Type uK) [Field k0] (U0 : Type (max uK uV))
 [AddCommGroup U0] [Module k0 U0] (n0 : ℕ)
 (t : Fin n0 → Fin n0 → Module.End k0 U0),
 0 < n0 → FiniteDimensional k0 U0 → Module.finrank k0 U0 = n0 →
 Reduction.MatrixUnits n0 t →
 ∀ W0 : Submodule k0 U0, (∀ i j, YuiBasisObjects.Stable W0 (t i j)) →
 W0 = ⊥ ∨ W0 = ⊤ := by
  exact @T011 p K instK lambda V instV instCV x y h v M XM YM

private theorem __connected_T012 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) :
    ((Reduction.hM XM YM) * (XM 1) - (XM 1) * (Reduction.hM XM YM) = (2 : ℤ) • (XM 1) ∧
(Reduction.hM XM YM) * (YM 1) - (YM 1) * (Reduction.hM XM YM) = (-2 : ℤ) • (YM 1) ∧
(XM 1) * (YM 1) - (YM 1) * (XM 1) = (Reduction.hM XM YM)) ∧
((Reduction.ind K (Reduction.hM XM YM)) * (Reduction.ind K (XM 1)) - (Reduction.ind K (XM 1)) * (Reduction.ind K (Reduction.hM XM YM)) = (2 : K) • (Reduction.ind K (XM 1)) ∧
(Reduction.ind K (Reduction.hM XM YM)) * (Reduction.ind K (YM 1)) - (Reduction.ind K (YM 1)) * (Reduction.ind K (Reduction.hM XM YM)) = (-2 : K) • (Reduction.ind K (YM 1)) ∧
(Reduction.ind K (XM 1)) * (Reduction.ind K (YM 1)) - (Reduction.ind K (YM 1)) * (Reduction.ind K (XM 1)) = (Reduction.ind K (Reduction.hM XM YM))) ∧
(∀ W : Submodule K (Reduction.VK K M),
 (YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) ∧
  YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) ∧
  YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM))) ↔
 (∀ a b c : K, YuiBasisObjects.Stable W
 (a • Reduction.ind K (XM 1) + b • Reduction.ind K (YM 1) +
 c • Reduction.ind K (Reduction.hM XM YM)))) := by
  exact @T012 p K instK lambda V instV instCV x y h v M XM YM h_H005 h_H007 (@__connected_T006 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006 h_H007) (@__connected_T008 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H007 h_E001)

private theorem __connected_T013 (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) :
    Nontrivial (Reduction.VK K M) ∧
∀ W : Submodule K (Reduction.VK K M),
 YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM)) →
 W = ⊥ ∨ W = ⊤ := by
  exact @T013 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003 (@__connected_T003 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006) (@__connected_T006 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006 h_H007) (@__connected_T008 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H007 h_E001) (@__connected_T010 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 h_H007 h_E001) (@__connected_T011 p K instK lambda V instV instCV x y h v M XM YM) (@__connected_T012 p K instK lambda V instV instCV x y h v M XM YM h_H003 h_H004 h_H005 h_H006 h_H007 h_E001)

theorem P (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) : Nontrivial (Reduction.VK K M) ∧
∀ W : Submodule K (Reduction.VK K M),
 YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM)) →
 W = ⊥ ∨ W = ⊤ := by
  exact @__connected_T013 p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 h_H007 h_E001

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) (h_E001 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)) : Nontrivial (Reduction.VK K M) ∧
∀ W : Submodule K (Reduction.VK K M),
 YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM)) →
 W = ⊥ ∨ W = ⊤ := by
  exact @Translation.P.{_, _, _, _} p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 h_H007 h_E001

#check @P
#print axioms P
end AuditBExport


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] [FiniteDimensional F U] (b : I → U), LinearIndependent F b → Fintype.card I = Module.finrank F U → Submodule.span F (Set.range b) = ⊤ := by
  intro F U I _ _ _ _ _ b hb hc
  exact hb.span_eq_top_of_card_eq_finrank' hc
set_option Elab.async false in
theorem B002 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M), ∃ c : Module.Basis (Fin n) K (TensorProduct ℤ K M), (∀ i, c i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧ Module.finrank K (TensorProduct ℤ K M) = n := by
  intro K M _ _ _ n b
  refine ⟨b.baseChange K, ?_, ?_⟩
  · intro i
    simp
  · simpa using Module.finrank_eq_card_basis (b.baseChange K)
set_option Elab.async false in
theorem B003 : ∀ (K : Type*) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → (r.factorial : K) ≠ 0 := by
  intro K _ p _ _ r hr
  exact ((IsUnit.natCast_factorial_iff_of_charP (A := K) p).2 hr).ne_zero
set_option Elab.async false in
theorem B004 : ∀ (n j : ℕ), j ≤ n → Nat.choose n j * j.factorial * (n - j).factorial = n.factorial := by
  intro n j hj
  exact Nat.choose_mul_factorial_mul_factorial hj
set_option Elab.async false in
theorem B005 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m) := by
  intro K M _ _ _
  let F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M) :=
    { toFun := fun f => f.baseChange K
      map_one' := LinearMap.baseChange_one ℤ M
      map_mul' := fun f g => LinearMap.baseChange_mul f g
      map_zero' := LinearMap.baseChange_zero
      map_add' := fun f g => LinearMap.baseChange_add f g }
  refine ⟨F, ?_⟩
  intro f a m
  rfl
set_option Elab.async false in
theorem B006 : ∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] (b : Module.Basis I F U), (∀ u, ∑ i, b.repr u i • b i = u) ∧ (∀ f g : Module.End F U, (∀ i, f (b i) = g (b i)) → f = g) := by
  intro F U I _ _ _ _ b
  refine ⟨b.sum_repr, ?_⟩
  intro f g h
  exact b.ext h
set_option Elab.async false in
theorem B007 : ∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [FiniteDimensional F U] (b : Module.Basis I F U), Finite I ∧ Nat.card I = Module.finrank F U := by
  intro F U I _ _ _ _ b
  exact ⟨Module.Finite.finite_basis b, (Module.finrank_eq_nat_card_basis b).symm⟩

end YuiBasis

namespace YuiClosed
set_option autoImplicit false
set_option Elab.async false in
theorem P (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lambda ∧ lambda < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lambda + 1 ∧ Nontrivial V ∧
(∀ W : Submodule ℂ V, YuiBasisObjects.Stable W x → YuiBasisObjects.Stable W y →
 YuiBasisObjects.Stable W h → W = ⊥ ∨ W = ⊤) ∧
(∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lambda : ℂ) • w)) (h_H005 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : v ≠ 0 ∧ x v = 0 ∧ h v = (lambda : ℂ) • v) (h_H007 : (∃ (I : Type uV) (bZ : Module.Basis I ℤ M) (bC : Module.Basis I ℂ V),
 ∀ i, (bZ i : V) = bC i) ∧
(∀ (r : ℕ) (m : M), (XM r m : V) = YuiBasisObjects.dividedPower x r (m : V)) ∧
(∀ (r : ℕ) (m : M), (YM r m : V) = YuiBasisObjects.dividedPower y r (m : V))) : Nontrivial (Reduction.VK K M) ∧
∀ W : Submodule K (Reduction.VK K M),
 YuiBasisObjects.Stable W (Reduction.ind K (XM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (YM 1)) →
 YuiBasisObjects.Stable W (Reduction.ind K (Reduction.hM XM YM)) →
 W = ⊥ ∨ W = ⊤ := by
  exact @AuditBExport.P.{_, _, _, _} p K instK lambda V instV instCV x y h v M XM YM h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 h_H007 (@YuiBasis.B005)

end YuiClosed
