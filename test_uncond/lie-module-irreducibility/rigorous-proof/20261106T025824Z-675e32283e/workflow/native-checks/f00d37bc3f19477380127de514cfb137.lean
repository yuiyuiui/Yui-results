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

namespace YuiAuxiliary
set_option autoImplicit false
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

theorem checked (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
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
#check @checked
#print axioms checked
end YuiAuxiliary
