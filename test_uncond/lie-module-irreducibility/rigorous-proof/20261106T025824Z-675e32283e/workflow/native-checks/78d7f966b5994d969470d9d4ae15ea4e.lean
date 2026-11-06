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

namespace Translation
set_option autoImplicit false

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

#check @T013
#print axioms T013

end Translation
