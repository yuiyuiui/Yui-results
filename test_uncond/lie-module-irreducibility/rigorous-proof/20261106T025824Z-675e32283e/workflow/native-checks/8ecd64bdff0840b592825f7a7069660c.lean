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

#check @T011
#print axioms T011

end Translation
