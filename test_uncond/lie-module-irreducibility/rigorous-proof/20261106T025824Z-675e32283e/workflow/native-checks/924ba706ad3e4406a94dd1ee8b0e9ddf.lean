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

#check @T001
#print axioms T001

end Translation
