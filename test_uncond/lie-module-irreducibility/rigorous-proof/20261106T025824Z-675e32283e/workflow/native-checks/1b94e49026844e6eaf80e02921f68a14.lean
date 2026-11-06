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

theorem checked (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T001 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
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
#check @checked
#print axioms checked
end YuiAuxiliary
