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

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ i : Idx lam, (coeffProd lam : K) = (coeff lam i : K) * (coeffOmit lam i : K)" := by
  intro i
  have hp : coeffProd lam = coeff lam i * coeffOmit lam i :=
    h_T002.2.2.2.2.2.2.2.1 i
  rw [hp, Nat.cast_mul]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ i j l : Idx lam, ((coeff lam j : K)⁻¹ * (coeff lam l : K)⁻¹) • ((coeff lam j : K) • hat (K := K) (latticeEnd M (integralMatrix lam x y i l))) = (coeff lam l : K)⁻¹ • hat (K := K) (latticeEnd M (integralMatrix lam x y i l))" := by
  intro i j l
  rw [smul_smul]
  have hc : (coeff lam j : K) ≠ 0 := h_T010.2.1 j
  have heq : ((coeff lam j : K)⁻¹ * (coeff lam l : K)⁻¹) * (coeff lam j : K) =
      (coeff lam l : K)⁻¹ := by
    calc
      _ = ((coeff lam j : K)⁻¹ * (coeff lam j : K)) * (coeff lam l : K)⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ hc, one_mul]
  rw [heq]

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "matrixUnits (scaledMatrix (K := K) lam x y M)" := by
  classical
  have hcast := @yui_aux_0001 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  have hcancel := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  rcases h_T009 with ⟨hl, hp, hd, hb, hn, hfd, hfin, hop⟩
  rcases hop with ⟨ham, hz, hone, hs, hpow, ht⟩
  rcases h_T002 with ⟨hc, htop, hlow, hact, hpres, hm, hsum, hprod, hfact, hdiv, hgen, hh, ha⟩
  have hzero : hat (K := K) (0 : Module.End ℤ M) = 0 := by
    simpa using hz (0 : ℤ) (1 : Module.End ℤ M)
  have hnat (n : ℕ) (f : Module.End ℤ M) :
      hat (K := K) ((n : ℤ) • f) = (n : K) • hat (K := K) f := by
    simpa using hz (n : ℤ) f
  have hm' (i j k l : Idx lam) :
      hat (K := K) (latticeEnd M (integralMatrix lam x y i j)) *
        hat (K := K) (latticeEnd M (integralMatrix lam x y k l)) =
      if j = k then (coeff lam j : K) •
        hat (K := K) (latticeEnd M (integralMatrix lam x y i l)) else 0 := by
    rw [← (ham _ _).2, hm]
    split_ifs <;> simp only [hnat, hzero]
  have hsum' :
      (∑ i : Idx lam, (coeffOmit lam i : K) •
        hat (K := K) (latticeEnd M (integralMatrix lam x y i i))) =
      (coeffProd lam : K) • (1 : Module.End K (TensorLeft K M)) := by
    calc
      _ = hat (K := K) (∑ i : Idx lam, (coeffOmit lam i : ℤ) •
          latticeEnd M (integralMatrix lam x y i i)) := by
        rw [hs]
        simp only [hnat]
      _ = _ := by rw [hsum, hnat, hone]
  have hscalar (i : Idx lam) :
      (coeffProd lam : K)⁻¹ * (coeffOmit lam i : K) = (coeff lam i : K)⁻¹ := by
    have heq : (coeffProd lam : K) =
        (coeff lam i : K) * (coeffOmit lam i : K) := by
      exact hcast i
    have hcne := h_T010.2.1 i
    have hpne := h_T010.2.2
    apply (mul_left_cancel₀ hpne)
    rw [← mul_assoc, mul_inv_cancel₀ hpne, one_mul, heq]
    simp [mul_assoc, mul_comm, mul_left_comm, hcne]
  constructor
  · intro i j k l
    dsimp only [scaledMatrix]
    rw [smul_mul_smul_comm, hm']
    by_cases hjk : j = k
    · subst k
      simpa only [ite_true] using hcancel i j l
    · simp [hjk]
  · change (∑ i : Idx lam, (coeff lam i : K)⁻¹ •
        hat (K := K) (latticeEnd M (integralMatrix lam x y i i))) = 1
    calc
      _ = (coeffProd lam : K)⁻¹ •
          (∑ i : Idx lam, (coeffOmit lam i : K) •
          hat (K := K) (latticeEnd M (integralMatrix lam x y i i))) := by
        simp only [Finset.smul_sum, smul_smul, hscalar]
      _ = 1 := by rw [hsum', inv_smul_smul₀ h_T010.2.2]

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ f : Module.End ℤ M, (-1 : K) • hat (K := K) f = -hat (K := K) f" := by
  intro f
  exact neg_one_smul K (hat (K := K) f)

theorem checked (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ f : Module.End ℤ M, hat (K := K) (-f) = -hat (K := K) f" := by
  have hn := @yui_aux_0004 p K instK lam V instV instCV x y h v M h_T002 h_T009 h_T010 h_H001 h_H002 h_H003 h_H004 h_H006
  intro f
  have hz : hat (K := K) ((-1 : ℤ) • f) = ((-1 : ℤ) : K) • hat (K := K) f :=
    h_T009.2.2.2.2.2.2.2.2.1 (-1 : ℤ) f
  have hcast : ((-1 : ℤ) : K) = (-1 : K) := by norm_num
  have hz' : hat (K := K) (-f) = (-1 : K) • hat (K := K) f := by
    simpa only [hcast, neg_one_smul ℤ] using hz
  exact hz'.trans (hn f)
#check @checked
#print axioms checked
end YuiAuxiliary
