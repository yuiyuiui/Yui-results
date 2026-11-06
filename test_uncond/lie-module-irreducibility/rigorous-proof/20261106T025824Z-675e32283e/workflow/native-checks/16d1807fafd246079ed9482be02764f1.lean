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

#check @T012
#print axioms T012

end Translation
