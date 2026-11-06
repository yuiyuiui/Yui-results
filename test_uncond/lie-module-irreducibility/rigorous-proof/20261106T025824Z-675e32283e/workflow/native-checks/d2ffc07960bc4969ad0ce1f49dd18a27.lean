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

namespace Translation
set_option autoImplicit false

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

#check @T007
#print axioms T007

end Translation
