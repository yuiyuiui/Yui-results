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
theorem yui_aux_0001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧ projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧ (∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧ (∀ i j k : Idx lam, integralMatrix lam x y i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0)" := by
  classical
  rcases h_T001 with ⟨hl, hn, hb, hy0, hx0, hx1, hy1, hyend, hh, hx, hy⟩
  have hc (j : Idx lam) : 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j := by
    have hj : j.val ≤ ell lam := by omega
    exact ⟨Nat.choose_pos hj, Nat.choose_mul_factorial_mul_factorial hj, Nat.choose_symm hj⟩
  have htop : projector lam x y (ev y v (ell lam)) = ev y v (ell lam) := by
    have ht := hx (ell lam) (⟨ell lam, by omega⟩ : Idx lam)
    have hz := hy (ell lam) (⟨0, by omega⟩ : Idx lam)
    simp only [Fin.val_mk, le_refl, if_true, Nat.sub_self, Nat.zero_add, Nat.choose_self, Nat.cast_one, one_smul] at ht hz
    simpa only [projector, Module.End.mul_apply, ht, hz]
  have hlow (k : ℕ) (hk : k < ell lam) : projector lam x y (ev y v k) = 0 := by
    have ht := hx (ell lam) (⟨k, by omega⟩ : Idx lam)
    simp only [Fin.val_mk, show ¬ell lam ≤ k by omega, if_false] at ht
    simp only [projector, Module.End.mul_apply, ht, map_zero]
  refine ⟨hc, htop, hlow, ?_⟩
  intro i j k
  have hi : i.val ≤ ell lam := by omega
  have hj : j.val ≤ ell lam := by omega
  have hk : k.val ≤ ell lam := by omega
  have hxi := hx (ell lam - i.val) (⟨ell lam, by omega⟩ : Idx lam)
  simp only [Fin.val_mk, Nat.sub_self, Nat.zero_add, Nat.choose_self, Nat.cast_one, one_smul, Nat.sub_sub_self hi, if_pos (Nat.sub_le _ _)] at hxi
  change dividedPower x (ell lam - i.val) (projector lam x y (dividedPower y (ell lam - j.val) (ev y v k.val))) = _
  rw [hy]
  by_cases hkj : k = j
  · subst k
    have he : j.val + (ell lam - j.val) = ell lam := by omega
    rw [if_pos (by omega), he, map_smul, htop, map_smul, hxi, (hc j).2.2]
    simp
  · rw [if_neg hkj]
    by_cases hlt : k.val < j.val
    · rw [if_pos (by omega), map_smul, hlow _ (by omega), smul_zero, map_zero]
    · rw [if_neg (by
        have : k.val ≠ j.val := fun he => hkj (Fin.ext he)
        omega), map_zero, map_zero]

theorem yui_aux_0002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ (f : Module.End ℂ V) (hf : ∀ z ∈ M, f z ∈ M) (m : M), (latticeEnd M f m : V) = f (m : V)" := by
  intro f hf m
  unfold latticeEnd
  rw [dif_pos hf]
  rfl

theorem yui_aux_0003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ (n : ℕ) (z : V), (n : ℤ) • z = (n : ℂ) • z" := by
  intro n z
  simpa only [Int.cast_natCast] using (Int.cast_smul_eq_zsmul ℂ (n : ℤ) z).symm

theorem yui_aux_0004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧ (∀ i j k l : Idx lam, integralMatrix lam x y i j * integralMatrix lam x y k l = if j = k then (coeff lam j : ℤ) • integralMatrix lam x y i l else 0) ∧ (∑ i : Idx lam, (coeffOmit lam i : ℤ) • integralMatrix lam x y i i) = (coeffProd lam : ℤ) • (1 : Module.End ℂ V)" := by
  classical
  have ha := (@yui_aux_0001 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006).2.2.2
  have hz := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  obtain ⟨b, hb⟩ := h_T001.2.2.1
  have hp (i : Idx lam) : coeffProd lam = coeff lam i * coeffOmit lam i := by
    exact (Finset.mul_prod_erase Finset.univ (coeff lam) (Finset.mem_univ i)).symm
  refine ⟨hp, ?_, ?_⟩
  · intro i j k l
    apply b.ext
    intro t
    rw [hb]
    by_cases htl : t = l <;> by_cases hjk : j = k
    · subst t
      subst k
      simp only [Module.End.mul_apply, ha, if_true, map_smul, LinearMap.smul_apply, hz, smul_smul]
      rw [mul_comm]
    · subst t
      simp [Module.End.mul_apply, ha, map_smul, hjk, Ne.symm hjk]
    · simp [Module.End.mul_apply, ha, htl, hjk]
    · simp [Module.End.mul_apply, ha, htl, hjk]
  · apply b.ext
    intro t
    rw [hb]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, ha]
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_eq_single t]
    · simp only [if_true, hz, smul_smul, Module.End.one_apply]
      rw [hp t, Nat.cast_mul, mul_comm]
    · intro i hi hit
      simp [Ne.symm hit]
    · simp

theorem yui_aux_0005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ (r : ℕ) (z : V), z ∈ M → dividedPower x r z ∈ M) ∧ (∀ (r : ℕ) (z : V), z ∈ M → dividedPower y r z ∈ M) ∧ (∀ z ∈ M, x z ∈ M) ∧ (∀ z ∈ M, y z ∈ M) ∧ (∀ z ∈ M, h z ∈ M) ∧ (∀ (i j : Idx lam) (z : V), z ∈ M → integralMatrix lam x y i j z ∈ M)" := by
  have hx (r : ℕ) (z : V) (hz : z ∈ M) : dividedPower x r z ∈ M := h_H006.2.1 r ⟨z, hz⟩
  have hy (r : ℕ) (z : V) (hz : z ∈ M) : dividedPower y r z ∈ M := h_H006.2.2 r ⟨z, hz⟩
  have hxx (z : V) (hz : z ∈ M) : x z ∈ M := by
    simpa [dividedPower] using hx 1 z hz
  have hyy (z : V) (hz : z ∈ M) : y z ∈ M := by
    simpa [dividedPower] using hy 1 z hz
  refine ⟨hx, hy, hxx, hyy, ?_, ?_⟩
  · intro z hz
    rw [← h_H005.2.2.2.2.2]
    exact M.sub_mem (hxx _ (hyy z hz)) (hyy _ (hxx z hz))
  · intro i j z hz
    exact hx _ _ (hy _ _ (hx _ _ (hy _ _ hz)))

theorem yui_aux_0006 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "∀ (f : Module.End ℂ V) (hf : ∀ (r : ℕ) (z : V), z ∈ M → dividedPower f r z ∈ M) (r : ℕ), (r.factorial : ℤ) • latticeEnd M (dividedPower f r) = (latticeEnd M f) ^ r" := by
  intro f hf
  have hr := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  have hz := @yui_aux_0003 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  have hf1 (z : V) (hz : z ∈ M) : f z ∈ M := by
    simpa [dividedPower] using hf 1 z hz
  have hpow (r : ℕ) (m : M) : (((latticeEnd M f)^r) m : V) = (f^r) (m : V) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply, hr f hf1, ih]
  intro r
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  simp only [LinearMap.smul_apply, Submodule.coe_smul, hr _ (hf r), hpow, hz]
  have hn : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  simp [dividedPower, smul_smul, hn]

theorem checked (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) : yui_aux_type% "(∀ i j k l : Idx lam, latticeEnd M (integralMatrix lam x y i j) * latticeEnd M (integralMatrix lam x y k l) = if j = k then (coeff lam j : ℤ) • latticeEnd M (integralMatrix lam x y i l) else 0) ∧ (∑ i : Idx lam, (coeffOmit lam i : ℤ) • latticeEnd M (integralMatrix lam x y i i)) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M)" := by
  classical
  have hr := @yui_aux_0002 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  have hs := (@yui_aux_0005 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006).2.2.2.2.2
  have ha := @yui_aux_0004 p K instK lam V instV instCV x y h v M h_T001 h_H005 h_H006
  constructor
  · intro i j k l
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    have he := congrArg (fun f : Module.End ℂ V => f (m : V)) (ha.2.1 i j k l)
    by_cases hjk : j = k
    · simpa only [hjk, if_true, Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul, hr _ (hs _ _)] using he
    · simpa only [hjk, if_false, Module.End.mul_apply, LinearMap.zero_apply, Submodule.coe_zero, hr _ (hs _ _)] using he
  · apply LinearMap.ext
    intro m
    apply Subtype.ext
    have he := congrArg (fun f : Module.End ℂ V => f (m : V)) ha.2.2
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, hr _ (hs _ _), Module.End.one_apply] using he
#check @checked
#print axioms checked
end YuiAuxiliary
