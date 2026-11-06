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

theorem checked (p : ℕ) (K : Type uK) [instK : Field K] (lambda : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (XM : ℕ → Module.End ℤ M) (YM : ℕ → Module.End ℤ M) (h_T003 : (lambda = (lambda.toNat : ℤ) ∧ lambda.toNat < p ∧
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
#check @checked
#print axioms checked
end YuiAuxiliary
