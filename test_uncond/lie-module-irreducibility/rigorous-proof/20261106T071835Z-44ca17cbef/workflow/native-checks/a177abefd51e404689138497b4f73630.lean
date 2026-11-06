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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

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

#check @T009
#print axioms T009

end Translation
