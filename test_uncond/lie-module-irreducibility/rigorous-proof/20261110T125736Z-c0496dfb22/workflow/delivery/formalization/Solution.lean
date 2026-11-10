import Mathlib
open scoped TensorProduct
open Module
universe u v
namespace SL2Lattice
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
noncomputable def dp (t : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  (Nat.factorial r : ℂ)⁻¹ • t ^ r
noncomputable def vec (y : Module.End ℂ V) (w : V) (i : ℕ) : V := dp y i w
def n (l : ℤ) : ℕ := l.toNat + 1
def coeff (l : ℤ) (j : ℕ) : ℤ := (Nat.choose l.toNat j : ℤ)
def detCoeff (l : ℤ) : ℤ := ∏ j : Fin (n l), coeff l j.val
def otherCoeff (l : ℤ) (i : Fin (n l)) : ℤ :=
  ∏ j ∈ (Finset.univ : Finset (Fin (n l))).erase i, coeff l j.val
noncomputable def raw (l : ℤ) (x y : Module.End ℂ V) (i j : Fin (n l)) : Module.End ℂ V :=
  dp x (l.toNat - i.val) * dp y l.toNat * dp x l.toNat * dp y (l.toNat - j.val)
def Stable (M : Submodule ℤ V) (t : Module.End ℂ V) : Prop :=
  ∀ m : V, m ∈ M → t m ∈ M
def Inv {R : Type v} [Field R] {U : Type u} [AddCommGroup U] [Module R U]
    (W : Submodule R U) (t : Module.End R U) : Prop :=
  ∀ w : U, w ∈ W → t w ∈ W
structure Actions (M : Submodule ℤ V) (x y h : Module.End ℂ V) where
  xZ : Module.End ℤ M
  yZ : Module.End ℤ M
  hZ : Module.End ℤ M
  XZ : ℕ → Module.End ℤ M
  YZ : ℕ → Module.End ℤ M
  x_eq : ∀ m : M, (xZ m : V) = x (m : V)
  y_eq : ∀ m : M, (yZ m : V) = y (m : V)
  h_eq : ∀ m : M, (hZ m : V) = h (m : V)
  X_eq : ∀ r (m : M), (XZ r m : V) = dp x r (m : V)
  Y_eq : ∀ r (m : M), (YZ r m : V) = dp y r (m : V)
def rawZ {M : Submodule ℤ V} {x y h : Module.End ℂ V}
    (a : Actions M x y h) (l : ℤ) (i j : Fin (n l)) : Module.End ℤ M :=
  a.XZ (l.toNat - i.val) * a.YZ l.toNat * a.XZ l.toNat * a.YZ (l.toNat - j.val)
noncomputable def red (K : Type v) [Field K] {M : Submodule ℤ V}
    (t : Module.End ℤ M) : Module.End K (TensorProduct ℤ K M) :=
  t.baseChange K
noncomputable def matrixUnit (K : Type v) [Field K] {M : Submodule ℤ V}
    {x y h : Module.End ℂ V} (a : Actions M x y h) (l : ℤ)
    (i j : Fin (n l)) : Module.End K (TensorProduct ℤ K M) :=
  (coeff l j.val : K)⁻¹ • red K (rawZ a l i j)
end SL2Lattice
open SL2Lattice
namespace YuiPortTypes
abbrev E001 : Prop :=
  ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤
abbrev M001 : Prop :=
  ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (ι : Type*) [Fintype ι] (v : ι → U), LinearIndependent K v → Fintype.card ι = Module.finrank K U → Submodule.span K (Set.range v) = ⊤
abbrev M002 : Prop :=
  ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (ι : Type*) (b : Basis ι ℤ M), ∃ B : Basis ι K (TensorProduct ℤ K M), ∀ i : ι, B i = TensorProduct.tmul ℤ (1 : K) (b i)
abbrev M003 : Prop :=
  ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ ρ : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (t : Module.End ℤ M) (a : K) (m : M), ρ t (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (t m)
abbrev M004 : Prop :=
  ∀ (A : Type*) [Ring A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p] (n : ℕ), IsUnit (Nat.factorial n : A) ↔ n < p
abbrev M006 : Prop :=
  ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] (ι : Type*) (b : Basis ι K U), Module.finrank K U = Nat.card ι
abbrev M007 : Prop :=
  ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ e : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M, ∀ (m : M) (a : K), e (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) : yui_aux_type% "∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w" := by
  rcases h_H002 with ⟨_, _, _, hhy, _, _, _, hw, _⟩
  have hy (v : V) : h (y v) = y (h v) + (-2 : ℂ) • y v := by
    have e := congrArg (fun t : Module.End ℂ V => t v) hhy
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at e
    exact sub_eq_iff_eq_add.mp e |>.trans (add_comm _ _)
  intro i
  induction i with
  | zero => simpa using hw
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, hy, ih, map_smul]
    rw [← add_smul]
    congr 1
    push_cast
    ring

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) : yui_aux_type% "∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w" := by
  have hh := @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_H002
  rcases h_H002 with ⟨_, _, _, _, hxy, _, hxw, hw, _⟩
  have hxy' (v : V) : x (y v) = y (x v) + h v := by
    have e := congrArg (fun t : Module.End ℂ V => t v) hxy
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    exact (sub_eq_iff_eq_add.mp e).trans (add_comm _ _)
  intro i
  induction i with
  | zero => simpa [pow_succ', hxy', hxw] using hw
  | succ i ih =>
    rw [pow_succ' y (i + 1), Module.End.mul_apply, hxy', ih, map_smul, hh]
    rw [← Module.End.mul_apply, ← pow_succ' y i, ← add_smul]
    congr 1
    push_cast
    ring

theorem yui_aux_0003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) : yui_aux_type% "∀ i : ℕ, (x ^ i) ((y ^ i) w) = ((Nat.factorial i : ℂ) * ∏ t ∈ Finset.range i, ((l : ℂ) - (t : ℂ))) • w" := by
  have hx := @yui_aux_0002 p K instK l V instV instCV x y h w M h_H001 h_H002
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ x, Module.End.mul_apply, hx, map_smul, ih, smul_smul]
    rw [Nat.factorial_succ, Nat.cast_mul, Finset.prod_range_succ]
    congr 1
    ring

theorem yui_aux_0004 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) : yui_aux_type% "∀ i : ℕ, i ≤ l.toNat → ((Nat.factorial i : ℂ) * ∏ t ∈ Finset.range i, ((l : ℂ) - (t : ℂ))) ≠ 0" := by
  have hl : (l.toNat : ℤ) = l := Int.toNat_of_nonneg h_H001.2.2.1
  intro i hi
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero i
  · apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    have hti : t < i := Finset.mem_range.mp ht
    have hz : (l - (t : ℤ)) ≠ 0 := by omega
    have hc : ((l - (t : ℤ) : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hz
    simpa only [Int.cast_sub, Int.cast_natCast] using hc

end Local_T001
open Local_T001 in
theorem T001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) :
    (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i)) := by
  have hh := @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_H002
  have hx := @yui_aux_0002 p K instK l V instV instCV x y h w M h_H001 h_H002
  have hit := @yui_aux_0003 p K instK l V instV instCV x y h w M h_H001 h_H002
  have hc := @yui_aux_0004 p K instK l V instV instCV x y h w M h_H001 h_H002
  refine ⟨hh, hx, ?_, ?_⟩
  · intro i
    have hi : i.val ≤ l.toNat := by have := i.isLt; unfold n at this; omega
    have hw : w ≠ 0 := h_H002.2.2.2.2.2.1
    have hy : (y ^ i.val) w ≠ 0 := by
      intro hz
      have he := hit i.val
      rw [hz, map_zero] at he
      exact (smul_ne_zero (hc i.val hi) hw) he.symm
    have hf : (Nat.factorial i.val : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    simpa only [vec, dp, LinearMap.smul_apply] using smul_ne_zero (inv_ne_zero hf) hy
  · intro i
    simp only [vec, dp, LinearMap.smul_apply, map_smul, hh]
    exact smul_comm _ _ _

namespace Local_T002
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) : yui_aux_type% "Function.Injective (fun i : Fin (n l) => (l : ℂ) - 2 * (i.val : ℂ))" := by
  intro i j hij
  have he : (i.val : ℂ) = (j.val : ℂ) := by
    linear_combination (-1 / 2 : ℂ) * hij
  apply Fin.ext
  exact_mod_cast he

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) : yui_aux_type% "∀ (q : Polynomial ℂ) (i : Fin (n l)), (Polynomial.aeval h q) (vec y w i.val) = q.eval ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w i.val" := by
  intro q i
  exact Module.End.aeval_apply_of_mem_apply_eq_smul (p := q) (h_T001.2.2.2 i.val)

end Local_T002
open Local_T002 in
theorem T002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) :
    LinearIndependent ℂ (fun i : Fin (n l) => vec y w (i.val)) := by
  classical
  let μ : Fin (n l) → ℂ := fun i => (l : ℂ) - 2 * (i.val : ℂ)
  have hμ : Function.Injective μ :=
    @yui_aux_0001 p K instK l V instV instCV x y h w M h_T001
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  let q : Polynomial ℂ := ∏ k ∈ (Finset.univ : Finset (Fin (n l))).erase j,
    (Polynomial.X - Polynomial.C (μ k))
  have h_eval (i : Fin (n l)) : q.eval (μ i) =
      ∏ k ∈ (Finset.univ : Finset (Fin (n l))).erase j, (μ i - μ k) := by
    simp [q, Polynomial.eval_prod]
  have h_off (i : Fin (n l)) (hij : i ≠ j) : q.eval (μ i) = 0 := by
    rw [h_eval]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) (sub_self (μ i))
  have h_diag : q.eval (μ j) ≠ 0 := by
    rw [h_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro he
    exact (Finset.mem_erase.mp hk).1 (hμ he).symm
  have hact (i : Fin (n l)) : (Polynomial.aeval h q) (vec y w i.val) =
      q.eval (μ i) • vec y w i.val :=
    @yui_aux_0002 p K instK l V instV instCV x y h w M h_T001 q i
  have hz := congrArg (fun v : V => (Polynomial.aeval h q) v) ha
  simp only [map_sum, map_smul, map_zero, hact, smul_smul] at hz
  have hisolate : (∑ i : Fin (n l), (a i * q.eval (μ i)) • vec y w i.val) =
      (a j * q.eval (μ j)) • vec y w j.val := by
    apply Finset.sum_eq_single j
    · intro i hi hij
      rw [h_off i hij, mul_zero, zero_smul]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [hisolate] at hz
  have hm : a j * q.eval (μ j) = 0 := (smul_eq_zero.mp hz).resolve_right (h_T001.2.2.1 j)
  exact (mul_eq_zero.mp hm).resolve_right h_diag

theorem T003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_T002 : LinearIndependent ℂ (fun i : Fin (n l) => vec y w (i.val))) (h_M001 : @YuiPortTypes.M001.{0, u, 0}) :
    ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val) := by
  letI : FiniteDimensional ℂ V := h_H002.1
  have hcard : Fintype.card (Fin (n l)) = Module.finrank ℂ V := by
    simpa only [Fintype.card_fin] using h_H002.2.1.symm
  have hspan : Submodule.span ℂ (Set.range (fun i : Fin (n l) => vec y w i.val)) = ⊤ :=
    h_M001 ℂ V (Fin (n l)) (fun i : Fin (n l) => vec y w i.val) h_T002 hcard
  refine ⟨Basis.mk h_T002 (le_of_eq hspan.symm), ?_⟩
  intro i
  exact Basis.mk_apply h_T002 (le_of_eq hspan.symm) i

namespace Local_T004
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) : yui_aux_type% "∀ (b : Basis (Fin (n l)) ℂ V), (∀ i, b i = vec y w i.val) → ∀ (z : V) (i : Fin (n l)), b.repr (h z) i = ((l : ℂ) - 2 * (i.val : ℂ)) * b.repr z i" := by
  classical
  intro b hb z i
  have hd (j : Fin (n l)) : h (b j) = ((l : ℂ) - 2 * (j.val : ℂ)) • b j := by
    rw [hb, h_T001.2.2.2, ← hb]
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, map_smul, hd, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, smul_eq_mul]
  simp [mul_comm]

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) : yui_aux_type% "(y ^ (l.toNat + 1)) w = 0" := by
  classical
  obtain ⟨b, hb⟩ := h_T003
  let z : V := (y ^ (l.toNat + 1)) w
  have he : h z = ((l : ℂ) - 2 * ((l.toNat + 1 : ℕ) : ℂ)) • z := h_T001.1 _
  have hdiag := @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_H002 h_T001 ⟨b, hb⟩ b hb z
  have hc (i : Fin (n l)) : b.repr z i = 0 := by
    have eq := hdiag i
    rw [he] at eq
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at eq
    have hi : (i.val : ℂ) ≠ ((l.toNat + 1 : ℕ) : ℂ) := by
      exact_mod_cast (show i.val ≠ l.toNat + 1 by have := i.isLt; unfold n at this; omega)
    have hn : (l : ℂ) - 2 * ((l.toNat + 1 : ℕ) : ℂ) -
        ((l : ℂ) - 2 * (i.val : ℂ)) ≠ 0 := by
      intro hh
      apply hi
      linear_combination hh / 2
    exact (mul_eq_zero.mp (show
        ((l : ℂ) - 2 * ((l.toNat + 1 : ℕ) : ℂ) -
          ((l : ℂ) - 2 * (i.val : ℂ))) * b.repr z i = 0 by
        linear_combination eq)).resolve_left hn
  have hz : z = 0 := by
    apply b.repr.injective
    ext i
    simpa using hc i
  exact hz

theorem yui_aux_0003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) : yui_aux_type% "∀ i : ℕ, y (vec y w i) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)" := by
  intro i
  have hf : (Nat.factorial i : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hs : ((i + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  simp only [vec, dp, LinearMap.smul_apply, map_smul]
  rw [pow_succ', Module.End.mul_apply]
  simp only [Nat.factorial_succ, Nat.cast_mul]
  rw [smul_smul]
  congr 1
  field_simp

theorem yui_aux_0004 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) : yui_aux_type% "∀ i : ℕ, 1 ≤ i → x (vec y w i) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)" := by
  intro i hi
  cases i with
  | zero => omega
  | succ j =>
    have hf : (Nat.factorial j : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hs : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    simp only [Nat.succ_eq_add_one, vec, dp, LinearMap.smul_apply, map_smul,
      h_T001.2.1, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, smul_smul]
    congr 1
    push_cast
    field_simp
    <;> ring

end Local_T004
open Local_T004 in
theorem T004 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_T001 : (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i))) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) :
    ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) := by
  have hz := @yui_aux_0002 p K instK l V instV instCV x y h w M h_H001 h_H002 h_T001 h_T003
  have hy := @yui_aux_0003 p K instK l V instV instCV x y h w M h_H001 h_H002 h_T001 h_T003
  have hx := @yui_aux_0004 p K instK l V instV instCV x y h w M h_H001 h_H002 h_T001 h_T003
  refine ⟨hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have he : r = (r - (l.toNat + 1)) + (l.toNat + 1) := by omega
    conv_lhs => rw [he, pow_add, Module.End.mul_apply]
    rw [hz, map_zero]
  · simpa [vec, dp] using h_H002.2.2.2.2.2.2.1
  · intro i hi _
    exact hx i hi
  · intro i _
    exact hy i
  · rw [hy]
    simp [vec, dp, hz]
  · intro i
    exact h_T001.2.2.2 i.val

namespace Local_T005
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : yui_aux_type% "∀ (i : Fin (n l)) (r : ℕ), dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0" := by
  have yui_nested_cb75dc93d5d8d7f1_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
   (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
   (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
   y (vec y w (l.toNat)) = 0 ∧
   (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : (∀ (i : Fin (n l)) (r : ℕ), (y ^ r) (vec y w i.val) = if i.val + r ≤ l.toNat then ((Nat.factorial (i.val + r) : ℂ) / (Nat.factorial i.val : ℂ)) • vec y w (i.val + r) else 0) := by
    intro i r
    have hi : i.val ≤ l.toNat := by
      have := i.isLt
      dsimp [n] at this
      omega
    have hfac : (Nat.factorial i.val : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    induction r with
    | zero =>
        simp [hi, hfac]
    | succ r ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        by_cases hr : i.val + r ≤ l.toNat
        · rw [if_pos hr, map_smul]
          by_cases ht : i.val + r < l.toNat
          · have hs : i.val + (r + 1) ≤ l.toNat := by omega
            rw [if_pos hs, h_T004.2.2.2.2.1 (i.val + r) ht, smul_smul]
            have he : i.val + (r + 1) = (i.val + r) + 1 := by omega
            rw [he, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            congr 1
            ring
          · have he : i.val + r = l.toNat := by omega
            have hs : ¬ i.val + (r + 1) ≤ l.toNat := by omega
            rw [if_neg hs, he, h_T004.2.2.2.2.2.1, smul_zero]
        · have hs : ¬ i.val + (r + 1) ≤ l.toNat := by omega
          rw [if_neg hr, if_neg hs, map_zero]
  have yui_nested_cb75dc93d5d8d7f1_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
   (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
   (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
   y (vec y w (l.toNat)) = 0 ∧
   (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : (∀ (i r : ℕ), (Nat.factorial r : ℂ)⁻¹ * ((Nat.factorial (i + r) : ℂ) / (Nat.factorial i : ℂ)) = (Nat.choose (i + r) r : ℂ)) := by
    intro i r
    have hr : (Nat.factorial r : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hi : (Nat.factorial i : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn : i + r - r = i := by omega
    have hc : (Nat.choose (i + r) r : ℂ) * (Nat.factorial r : ℂ) *
        (Nat.factorial i : ℂ) = (Nat.factorial (i + r) : ℂ) := by
      have hnat := h_M005 (i + r) r (by omega)
      rw [hn] at hnat
      exact_mod_cast hnat
    rw [← hc]
    field_simp
  intro i r
  change (Nat.factorial r : ℂ)⁻¹ • (y ^ r) (vec y w i.val) = _
  rw [@yui_nested_cb75dc93d5d8d7f1_0001 p K instK l V instV instCV x y h w M h_H001 h_T003 h_T004 h_M005 i r]
  by_cases hr : i.val + r ≤ l.toNat
  · rw [if_pos hr, smul_smul,
      @yui_nested_cb75dc93d5d8d7f1_0002 p K instK l V instV instCV x y h w M h_H001 h_T003 h_T004 h_M005 i.val r,
      if_pos hr]
  · rw [if_neg hr, smul_zero, if_neg hr]

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : yui_aux_type% "∀ (i : Fin (n l)) (r : ℕ), dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0" := by
  have yui_nested_7fad142c8d271975_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
   (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
   (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
   y (vec y w (l.toNat)) = 0 ∧
   (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : ((l : ℂ) = (l.toNat : ℂ)) := by
    exact_mod_cast (Int.toNat_of_nonneg h_H001.2.2.1).symm
  have yui_nested_7fad142c8d271975_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
   (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
   (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
   y (vec y w (l.toNat)) = 0 ∧
   (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : (∀ (i r : ℕ), i ≤ l.toNat → (x ^ r) (vec y w i) = if r ≤ i then ((Nat.factorial (l.toNat - i + r) : ℂ) / (Nat.factorial (l.toNat - i) : ℂ)) • vec y w (i - r) else 0) := by
    have hlcast : (l : ℂ) = (l.toNat : ℂ) :=
      @yui_nested_7fad142c8d271975_0001 p K instK l V instV instCV x y h w M h_H001 h_T003 h_T004 h_M005
    have hx0 : x (vec y w 0) = 0 := h_T004.2.2.1
    have hx : ∀ i : ℕ, 1 ≤ i → i ≤ l.toNat →
        x (vec y w i) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1) :=
      h_T004.2.2.2.1
    intro i r hi
    induction r with
    | zero =>
        simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (l.toNat - i))]
    | succ r ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        by_cases hr : r ≤ i
        · rw [if_pos hr, map_smul]
          by_cases hs : r + 1 ≤ i
          · have hpos : 1 ≤ i - r := by omega
            rw [hx (i - r) hpos (by omega), smul_smul, if_pos hs]
            have hind : i - r - 1 = i - (r + 1) := by omega
            rw [hind]
            congr 1
            have hc : (l : ℂ) - ((i - r : ℕ) : ℂ) + 1 =
                ((l.toNat - i + r + 1 : ℕ) : ℂ) := by
              rw [hlcast, Nat.cast_sub hr, Nat.cast_add, Nat.cast_add,
                Nat.cast_sub hi]
              push_cast
              ring
            rw [hc, show l.toNat - i + (r + 1) = (l.toNat - i + r) + 1 by omega,
              Nat.factorial_succ, Nat.cast_mul]
            ring
          · have heq : i - r = 0 := by omega
            rw [heq, hx0, smul_zero, if_neg hs]
        · rw [if_neg hr, map_zero, if_neg (show ¬ r + 1 ≤ i by omega)]
  have yui_nested_7fad142c8d271975_0003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
   (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
   (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
   y (vec y w (l.toNat)) = 0 ∧
   (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : (∀ a r : ℕ, (Nat.factorial r : ℂ)⁻¹ * ((Nat.factorial (a + r) : ℂ) / (Nat.factorial a : ℂ)) = (Nat.choose (a + r) r : ℂ)) := by
    intro a r
    have hnat := h_M005 (a + r) r (by omega)
    have hc : (Nat.choose (a + r) r : ℂ) * (Nat.factorial r : ℂ) *
        (Nat.factorial a : ℂ) = (Nat.factorial (a + r) : ℂ) := by
      exact_mod_cast (show Nat.choose (a + r) r * Nat.factorial r *
        Nat.factorial a = Nat.factorial (a + r) by simpa using hnat)
    have hr : (Nat.factorial r : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    have ha : (Nat.factorial a : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
    rw [← hc]
    field_simp

  intro i r
  have hi : i.val ≤ l.toNat := by
    have hi' := i.isLt
    dsimp [n] at hi'
    omega
  have hraw := @yui_nested_7fad142c8d271975_0002 p K instK l V instV instCV x y h w M
    h_H001 h_T003 h_T004 h_M005 i.val r hi
  change (Nat.factorial r : ℂ)⁻¹ • ((x ^ r) (vec y w i.val)) = _
  rw [hraw]
  by_cases hr : r ≤ i.val
  · rw [if_pos hr, if_pos hr, smul_smul]
    rw [@yui_nested_7fad142c8d271975_0003 p K instK l V instV instCV x y h w M
      h_H001 h_T003 h_T004 h_M005 (l.toNat - i.val) r]
  · rw [if_neg hr, if_neg hr, smul_zero]

end Local_T005
open Local_T005 in
theorem T005 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T003 : ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) (h_T004 : ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val)))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0)) := by
  refine ⟨h_T003, h_T004.2.2, ?_⟩
  intro i r
  exact ⟨@yui_aux_0002 p K instK l V instV instCV x y h w M h_H001 h_T003 h_T004 h_M005 i r,
    @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_T003 h_T004 h_M005 i r⟩

namespace Local_T006
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T005 : (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0))) : yui_aux_type% "∀ (i : Fin (n l)) (r : ℕ), (dp x r (vec y w i.val) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧ (dp y r (vec y w i.val) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0)" := by
  exact h_T005.2.2

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T005 : (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0))) : yui_aux_type% "∀ k : Fin (n l), dp y l.toNat (dp x l.toNat (vec y w k.val)) = if k.val = l.toNat then vec y w l.toNat else 0" := by
  have hd := @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T005
  intro k
  have hk : k.val ≤ l.toNat := by have := k.isLt; unfold n at this; omega
  by_cases he : k.val = l.toNat
  · have hx := (hd k l.toNat).1
    rw [he] at hx
    simp only [le_refl, if_true, Nat.sub_self, zero_add, Nat.choose_self,
      Nat.cast_one, one_smul] at hx
    rw [he, hx]
    have hy := (hd (⟨0, by simp [n]⟩ : Fin (n l)) l.toNat).2
    simpa using hy
  · have hn : ¬ l.toNat ≤ k.val := by omega
    rw [(hd k l.toNat).1, if_neg hn, map_zero, if_neg he]

theorem yui_aux_0003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T005 : (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0))) : yui_aux_type% "∀ i : Fin (n l), dp x (l.toNat - i.val) (vec y w l.toNat) = vec y w i.val" := by
  have hd := @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T005
  intro i
  have hi : i.val ≤ l.toNat := by have := i.isLt; unfold n at this; omega
  have hx := (hd (⟨l.toNat, by simp [n]⟩ : Fin (n l)) (l.toNat - i.val)).1
  have he : l.toNat - (l.toNat - i.val) = i.val := by omega
  simpa [Nat.sub_self, Nat.sub_le, he] using hx

theorem yui_aux_0004 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T005 : (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0))) : yui_aux_type% "∀ j k : Fin (n l), dp y l.toNat (dp x l.toNat (dp y (l.toNat - j.val) (vec y w k.val))) = if j = k then (coeff l j.val : ℂ) • vec y w l.toNat else 0" := by
  classical
  have hd := @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T005
  have hQ := @yui_aux_0002 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T005
  intro j k
  have hj : j.val ≤ l.toNat := by have := j.isLt; unfold n at this; omega
  rw [(hd k (l.toNat - j.val)).2]
  by_cases ha : k.val + (l.toNat - j.val) ≤ l.toNat
  · rw [if_pos ha, map_smul, map_smul]
    let a : Fin (n l) := ⟨k.val + (l.toNat - j.val), by simp only [n]; omega⟩
    have hqa := hQ a
    change dp y l.toNat (dp x l.toNat (vec y w (k.val + (l.toNat - j.val)))) =
      (if k.val + (l.toNat - j.val) = l.toNat then vec y w l.toNat else 0) at hqa
    rw [hqa]
    by_cases he : j = k
    · subst k
      have hs : j.val + (l.toNat - j.val) = l.toNat := by omega
      simp only [hs, if_true]
      rw [Nat.choose_symm hj]
      simp [coeff]
    · have hn : k.val + (l.toNat - j.val) ≠ l.toNat := by
        intro hh
        apply he
        apply Fin.ext
        omega
      simp [hn, he]
  · have hn : j ≠ k := by intro he; subst k; omega
    simp [ha, hn]

end Local_T006
open Local_T006 in
theorem T006 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T005 : (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0))) :
    ∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) := by
  classical
  obtain ⟨b, hb⟩ := h_T005.1
  let E : Fin (n l) → Fin (n l) → Module.End ℂ V :=
    fun i j => b.constr ℂ (fun k => if j = k then vec y w i.val else 0)
  have hE : ∀ i j k : Fin (n l),
      E i j (vec y w k.val) = if j = k then vec y w i.val else 0 := by
    intro i j k
    rw [← hb k]
    exact b.constr_basis ℂ _ k
  have hQY := @yui_aux_0004 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T005
  have hX := @yui_aux_0003 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T005
  refine ⟨E, hE, ?_, ?_⟩
  · intro i j
    apply b.ext
    intro k
    rw [hb k]
    simp only [raw, Module.End.mul_apply, LinearMap.smul_apply]
    rw [hQY j k, hE i j k]
    by_cases he : j = k
    · simp only [he, if_true, map_smul, hX i]
    · simp [he]
  · intro i j m hm
    simp only [raw, Module.End.mul_apply]
    exact (h_H003.2 (l.toNat - i.val)).1 _
      ((h_H003.2 l.toNat).2 _
        ((h_H003.2 l.toNat).1 _
          ((h_H003.2 (l.toNat - j.val)).2 m hm)))

namespace Local_T007
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_T005 : (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0))) (h_T006 : ∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j))) : yui_aux_type% "∀ i : Fin (n l), (otherCoeff l i : ℂ) * (coeff l i.val : ℂ) = (detCoeff l : ℂ)" := by
  intro i
  have hi : otherCoeff l i * coeff l i.val = detCoeff l := by
    exact Finset.prod_erase_mul Finset.univ (fun j : Fin (n l) => coeff l j.val) (Finset.mem_univ i)
  exact_mod_cast hi

end Local_T007
open Local_T007 in
theorem T007 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_T005 : (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0))) (h_T006 : ∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j))) :
    (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i) := by
  classical
  have hc : ∀ i : Fin (n l), (otherCoeff l i : ℂ) * (coeff l i.val : ℂ) = (detCoeff l : ℂ) :=
    @yui_aux_0001 p K instK l V instV instCV x y h w M h_T005 h_T006
  rcases h_T005.1 with ⟨b, hb⟩
  rcases h_T006 with ⟨E, hE, hraw, hstable⟩
  have hmul : ∀ i j k q : Fin (n l), E i j * E k q = if j = k then E i q else 0 := by
    intro i j k q
    apply b.ext
    intro t
    rw [hb t]
    by_cases hj : j = k <;> by_cases hq : q = t <;>
      simp [Module.End.mul_apply, hE, hj, hq]
  have hsum : (∑ i : Fin (n l), E i i) = 1 := by
    apply b.ext
    intro t
    rw [hb t]
    simp [LinearMap.sum_apply, hE]
  refine ⟨⟨E, hE, hraw⟩, hstable, ?_, ?_⟩
  · intro i j k q
    by_cases hj : j = k <;>
      simp [hraw, smul_mul_assoc, mul_smul_comm, hmul, hj, smul_smul, mul_comm]
  · symm
    simp_rw [hraw, smul_smul, hc]
    rw [← Finset.smul_sum, hsum]

namespace Local_T010
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T007 : (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i)) : yui_aux_type% "∀ (a : Actions M x y h) (i j : Fin (n l)) (m : M), (rawZ a l i j m : V) = raw l x y i j (m : V)" := by
  intro a i j m
  simp only [rawZ, raw, Module.End.mul_apply, a.X_eq, a.Y_eq]

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T007 : (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i)) : yui_aux_type% "∀ (t : Module.End ℂ V) (z : Module.End ℤ M) (Z : ℕ → Module.End ℤ M), (∀ m : M, (z m : V) = t (m : V)) → (∀ r (m : M), (Z r m : V) = dp t r (m : V)) → ∀ r : ℕ, (Nat.factorial r : ℤ) • Z r = z ^ r" := by
  intro t z Z hz hZ
  have hp : ∀ r (m : M), ((z ^ r) m : V) = (t ^ r) (m : V) := by
    intro r
    induction r with
    | zero => intro m; rfl
    | succ r ih =>
      intro m
      simp only [pow_succ', Module.End.mul_apply, hz, ih]
  intro r
  ext m
  have hn : (Nat.factorial r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  simp only [LinearMap.smul_apply, Submodule.coe_smul, hZ, hp, dp, LinearMap.smul_apply]
  rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul, mul_inv_cancel₀ hn, one_smul]

end Local_T010
open Local_T010 in
theorem T010 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T007 : (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i)) :
    ∀ a : Actions M x y h,
 (∀ i j : Fin (n l), ∀ m : M, (rawZ a l i j m : V) = raw l x y i j (m : V)) ∧
 (∀ i j k q : Fin (n l), rawZ a l i j * rawZ a l k q = if j = k then (coeff l j.val : ℤ) • rawZ a l i q else 0) ∧
 ((detCoeff l : ℤ) • (1 : Module.End ℤ M) = ∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.XZ r = a.xZ ^ r) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.YZ r = a.yZ ^ r) := by
  classical
  intro a
  have hr := @yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T007 a
  have hf := @yui_aux_0002 p K instK l V instV instCV x y h w M h_H001 h_H003 h_T007
  refine ⟨hr, ?_, ?_, hf x a.xZ a.XZ a.x_eq a.X_eq, hf y a.yZ a.YZ a.y_eq a.Y_eq⟩
  · intro i j k q
    ext m
    have he := congrArg (fun t : Module.End ℂ V => t (m : V)) (h_T007.2.2.1 i j k q)
    by_cases hjk : j = k
    · simpa [hjk, Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul, hr, Int.cast_smul_eq_zsmul] using he
    · simpa [hjk, Module.End.mul_apply, hr] using he
  · ext m
    have he := congrArg (fun t : Module.End ℂ V => t (m : V)) h_T007.2.2.2
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_smul, hr, Int.cast_smul_eq_zsmul] using he

namespace Local_T011
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_M003 : @YuiPortTypes.M003.{v, u}) (h_M007 : @YuiPortTypes.M007.{v, u}) : yui_aux_type% "∃ ρ : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ t : Module.End ℤ M, ρ t = red K t" := by
  obtain ⟨ρ, hρ⟩ := h_M003 K M
  refine ⟨ρ, ?_⟩
  intro t
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c m => simpa only [red, LinearMap.baseChange_tmul] using hρ t c m
  | add a b ha hb => simp only [map_add, ha, hb]

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_M003 : @YuiPortTypes.M003.{v, u}) (h_M007 : @YuiPortTypes.M007.{v, u}) : yui_aux_type% "∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M, (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧ (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧ (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z))" := by
  obtain ⟨σ, hσ⟩ := h_M007 K M
  refine ⟨σ, hσ, ?_, ?_⟩
  · intro d z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => simp [hσ, TensorProduct.smul_tmul', smul_eq_mul]
    | add a b ha hb => simp only [map_add, smul_add, ha, hb]
  · intro t z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => simp [hσ, red]
    | add a b ha hb => simp only [map_add, ha, hb]

theorem yui_aux_0003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_M003 : @YuiPortTypes.M003.{v, u}) (h_M007 : @YuiPortTypes.M007.{v, u}) : yui_aux_type% "∀ (z : ℤ) (t : Module.End K (TensorProduct ℤ K M)), (z : K) • t = z • t" := by
  intro z t
  exact Int.cast_smul_eq_zsmul K z t

theorem yui_aux_0004 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_M003 : @YuiPortTypes.M003.{v, u}) (h_M007 : @YuiPortTypes.M007.{v, u}) : yui_aux_type% "∀ (ρ : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M)) (z : ℤ) (t : Module.End ℤ M), ρ (z • t) = z • ρ t" := by
  intro ρ z t
  exact map_zsmul ρ z t

end Local_T011
open Local_T011 in
theorem T011 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_M003 : @YuiPortTypes.M003.{v, u}) (h_M007 : @YuiPortTypes.M007.{v, u}) :
    (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z))) := by
  obtain ⟨ρ, hρ⟩ := @yui_aux_0001 p K instK l V instV instCV x y h w M h_M003 h_M007
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t c m
    simp only [red, LinearMap.baseChange_tmul]
  · intro s t
    simpa only [hρ] using ρ.map_add s t
  · intro s t
    simpa only [hρ] using ρ.map_mul s t
  · simpa only [hρ] using ρ.map_one
  · intro z t
    rw [← hρ (z • t), ← hρ t,
      @yui_aux_0003 p K instK l V instV instCV x y h w M h_M003 h_M007 z (ρ t)]
    exact @yui_aux_0004 p K instK l V instV instCV x y h w M h_M003 h_M007 ρ z t
  · intro t r
    simpa only [hρ] using map_pow ρ t r
  · exact @yui_aux_0002 p K instK l V instV instCV x y h w M h_M003 h_M007

theorem T008 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_M004 : @YuiPortTypes.M004.{v}) :
    ∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨h_H001.1⟩
  letI : CharP K p := h_H001.2.1
  intro r hr
  have hrp : r < p := by
    have hnonneg : 0 ≤ l := h_H001.2.2.1
    have hlt : l < (p : ℤ) := h_H001.2.2.2
    omega
  have hu : IsUnit (Nat.factorial r : K) := (h_M004 K p r).2 hrp
  exact hu.ne_zero

namespace Local_T009
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T008 : ∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) : yui_aux_type% "∀ j : ℕ, j ≤ l.toNat → (Nat.choose l.toNat j : K) * (Nat.factorial j : K) * (Nat.factorial (l.toNat - j) : K) = (Nat.factorial l.toNat : K)" := by
  intro j hj
  have hid := congrArg (fun a : ℕ => (a : K)) (h_M005 l.toNat j hj)
  simpa only [Nat.cast_mul] using hid

end Local_T009
open Local_T009 in
theorem T009 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T008 : ∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    (∀ j : Fin (n l), (coeff l j.val : K) ≠ 0) ∧ (∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) ∧ ((detCoeff l : K) ≠ 0) := by
  have hc : ∀ j : Fin (n l), (coeff l j.val : K) ≠ 0 := by
    intro j
    have hj : j.val ≤ l.toNat := by
      have := j.isLt
      unfold n at this
      omega
    have hid : (Nat.choose l.toNat j.val : K) *
        (Nat.factorial j.val : K) *
        (Nat.factorial (l.toNat - j.val) : K) =
        (Nat.factorial l.toNat : K) :=
      @yui_aux_0001 p K instK l V instV instCV x y h w M
        h_H001 h_T008 h_M005 j.val hj
    intro hz
    have hz' : (Nat.choose l.toNat j.val : K) = 0 := by
      simpa only [coeff, Int.cast_natCast] using hz
    rw [hz', zero_mul, zero_mul] at hid
    exact h_T008 l.toNat le_rfl hid.symm
  refine ⟨hc, h_T008, ?_⟩
  simpa only [detCoeff, Int.cast_prod] using
    (Finset.prod_ne_zero_iff.mpr (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n l)))) => hc j))

namespace Local_T012
theorem yui_aux_0001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T007 : (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i)) (h_T009 : (∀ j : Fin (n l), (coeff l j.val : K) ≠ 0) ∧ (∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) ∧ ((detCoeff l : K) ≠ 0)) (h_T010 : ∀ a : Actions M x y h,
 (∀ i j : Fin (n l), ∀ m : M, (rawZ a l i j m : V) = raw l x y i j (m : V)) ∧
 (∀ i j k q : Fin (n l), rawZ a l i j * rawZ a l k q = if j = k then (coeff l j.val : ℤ) • rawZ a l i q else 0) ∧
 ((detCoeff l : ℤ) • (1 : Module.End ℤ M) = ∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.XZ r = a.xZ ^ r) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.YZ r = a.yZ ^ r)) (h_T011 : (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z)))) : yui_aux_type% "∀ i : Fin (n l), (detCoeff l : K) = (coeff l i.val : K) * (otherCoeff l i : K)" := by
  classical
  intro i
  have hi : detCoeff l = coeff l i.val * otherCoeff l i := by
    exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin (n l))) (fun j => coeff l j.val) (Finset.mem_univ i)).symm
  have hc : (detCoeff l : K) = ((coeff l i.val * otherCoeff l i : ℤ) : K) := congrArg (fun z : ℤ => (z : K)) hi
  simpa only [Int.cast_mul] using hc

theorem yui_aux_0002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T007 : (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i)) (h_T009 : (∀ j : Fin (n l), (coeff l j.val : K) ≠ 0) ∧ (∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) ∧ ((detCoeff l : K) ≠ 0)) (h_T010 : ∀ a : Actions M x y h,
 (∀ i j : Fin (n l), ∀ m : M, (rawZ a l i j m : V) = raw l x y i j (m : V)) ∧
 (∀ i j k q : Fin (n l), rawZ a l i j * rawZ a l k q = if j = k then (coeff l j.val : ℤ) • rawZ a l i q else 0) ∧
 ((detCoeff l : ℤ) • (1 : Module.End ℤ M) = ∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.XZ r = a.xZ ^ r) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.YZ r = a.yZ ^ r)) (h_T011 : (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z)))) : yui_aux_type% "∀ a : Actions M x y h,\n (∀ i j k q : Fin (n l), red K (rawZ a l i j) * red K (rawZ a l k q) = if j = k then (coeff l j.val : K) • red K (rawZ a l i q) else 0) ∧\n ((detCoeff l : K) • (1 : Module.End K (TensorProduct ℤ K M)) = ∑ i : Fin (n l), (otherCoeff l i : K) • red K (rawZ a l i i))" := by
  classical
  intro a
  have hz : red K (0 : Module.End ℤ M) = 0 := by
    apply add_left_cancel (a := red K (0 : Module.End ℤ M))
    simpa only [zero_add, add_zero] using (h_T011.2.1 0 0).symm
  let R : Module.End ℤ M →+ Module.End K (TensorProduct ℤ K M) :=
    { toFun := red K
      map_zero' := hz
      map_add' := h_T011.2.1 }
  constructor
  · intro i j k q
    rw [← h_T011.2.2.1, (h_T010 a).2.1]
    split_ifs with hjk
    · exact h_T011.2.2.2.2.1 _ _
    · exact hz
  · have hd := congrArg (fun t : Module.End ℤ M => R t) (h_T010 a).2.2.1
    change red K ((detCoeff l : ℤ) • (1 : Module.End ℤ M)) = R (∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) at hd
    rw [h_T011.2.2.2.2.1, h_T011.2.2.2.1, map_sum] at hd
    change (detCoeff l : K) • (1 : Module.End K (TensorProduct ℤ K M)) = ∑ i : Fin (n l), red K ((otherCoeff l i : ℤ) • rawZ a l i i) at hd
    simp_rw [h_T011.2.2.2.2.1] at hd
    exact hd

theorem yui_aux_0003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T007 : (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i)) (h_T009 : (∀ j : Fin (n l), (coeff l j.val : K) ≠ 0) ∧ (∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) ∧ ((detCoeff l : K) ≠ 0)) (h_T010 : ∀ a : Actions M x y h,
 (∀ i j : Fin (n l), ∀ m : M, (rawZ a l i j m : V) = raw l x y i j (m : V)) ∧
 (∀ i j k q : Fin (n l), rawZ a l i j * rawZ a l k q = if j = k then (coeff l j.val : ℤ) • rawZ a l i q else 0) ∧
 ((detCoeff l : ℤ) • (1 : Module.End ℤ M) = ∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.XZ r = a.xZ ^ r) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.YZ r = a.yZ ^ r)) (h_T011 : (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z)))) : yui_aux_type% "∀ i : Fin (n l), (detCoeff l : K)⁻¹ * (otherCoeff l i : K) = (coeff l i.val : K)⁻¹" := by
  intro i
  have hp := (@yui_aux_0001 p K instK l V instV instCV x y h w M h_H001 h_T007 h_T009 h_T010 h_T011) i
  have hc := h_T009.1 i
  have hd := h_T009.2.2
  calc
    (detCoeff l : K)⁻¹ * (otherCoeff l i : K) =
        ((detCoeff l : K)⁻¹ * ((coeff l i.val : K) * (otherCoeff l i : K))) * (coeff l i.val : K)⁻¹ := by
          field_simp
    _ = (coeff l i.val : K)⁻¹ := by rw [← hp, inv_mul_cancel₀ hd, one_mul]

end Local_T012
open Local_T012 in
theorem T012 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T007 : (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i)) (h_T009 : (∀ j : Fin (n l), (coeff l j.val : K) ≠ 0) ∧ (∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) ∧ ((detCoeff l : K) ≠ 0)) (h_T010 : ∀ a : Actions M x y h,
 (∀ i j : Fin (n l), ∀ m : M, (rawZ a l i j m : V) = raw l x y i j (m : V)) ∧
 (∀ i j k q : Fin (n l), rawZ a l i j * rawZ a l k q = if j = k then (coeff l j.val : ℤ) • rawZ a l i q else 0) ∧
 ((detCoeff l : ℤ) • (1 : Module.End ℤ M) = ∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.XZ r = a.xZ ^ r) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.YZ r = a.yZ ^ r)) (h_T011 : (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z)))) :
    ∀ a : Actions M x y h,
 (∀ i j k q : Fin (n l), matrixUnit K a l i j * matrixUnit K a l k q = if j = k then matrixUnit K a l i q else 0) ∧
 ((∑ i : Fin (n l), matrixUnit K a l i i) = 1) := by
  classical
  intro a
  have ht := (@yui_aux_0002 p K instK l V instV instCV x y h w M h_H001 h_T007 h_T009 h_T010 h_T011) a
  have hn := @yui_aux_0003 p K instK l V instV instCV x y h w M h_H001 h_T007 h_T009 h_T010 h_T011
  constructor
  · intro i j k q
    unfold matrixUnit
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ht.1 i j k q]
    by_cases hjk : j = k
    · simp only [if_pos hjk, smul_smul]
      have hs : (coeff l j.val : K)⁻¹ * (coeff l q.val : K)⁻¹ * (coeff l j.val : K) = (coeff l q.val : K)⁻¹ := by
        rw [mul_right_comm, inv_mul_cancel₀ (h_T009.1 j), one_mul]
      rw [hs]
    · simp only [if_neg hjk, smul_zero]
  · have hd := congrArg (fun t : Module.End K (TensorProduct ℤ K M) => (detCoeff l : K)⁻¹ • t) ht.2
    rw [smul_smul, inv_mul_cancel₀ h_T009.2.2, one_smul, Finset.smul_sum] at hd
    simp_rw [smul_smul, hn] at hd
    exact hd.symm

theorem T013 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_T010 : ∀ a : Actions M x y h,
 (∀ i j : Fin (n l), ∀ m : M, (rawZ a l i j m : V) = raw l x y i j (m : V)) ∧
 (∀ i j k q : Fin (n l), rawZ a l i j * rawZ a l k q = if j = k then (coeff l j.val : ℤ) • rawZ a l i q else 0) ∧
 ((detCoeff l : ℤ) • (1 : Module.End ℤ M) = ∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.XZ r = a.xZ ^ r) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.YZ r = a.yZ ^ r)) (h_T011 : (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z)))) (h_T012 : ∀ a : Actions M x y h,
 (∀ i j k q : Fin (n l), matrixUnit K a l i j * matrixUnit K a l k q = if j = k then matrixUnit K a l i q else 0) ∧
 ((∑ i : Fin (n l), matrixUnit K a l i i) = 1)) :
    (∀ a : Actions M x y h,
 (∀ i j k q : Fin (n l), matrixUnit K a l i j * matrixUnit K a l k q = if j = k then matrixUnit K a l i q else 0) ∧
 ((∑ i : Fin (n l), matrixUnit K a l i i) = 1)) ∧ (∀ a : Actions M x y h, ∀ r : ℕ, r ≤ l.toNat →
 ((Nat.factorial r : K) • red K (a.XZ r) = (red K a.xZ) ^ r) ∧
 ((Nat.factorial r : K) • red K (a.YZ r) = (red K a.yZ) ^ r)) := by
  refine ⟨h_T012, ?_⟩
  intro a r hr
  have hx := (h_T010 a).2.2.2.1 r
  have hy := (h_T010 a).2.2.2.2 r
  constructor
  · have hxred := congrArg (red K) hx
    simpa only [h_T011.2.2.2.2.1, h_T011.2.2.2.2.2.1, Int.cast_natCast] using hxred
  · have hyred := congrArg (red K) hy
    simpa only [h_T011.2.2.2.2.1, h_T011.2.2.2.2.2.1, Int.cast_natCast] using hyred

theorem T014 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_T011 : (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z)))) (h_M002 : @YuiPortTypes.M002.{v, u, 0}) (h_M006 : @YuiPortTypes.M006.{0, u, 0}) (h_M006_2 : @YuiPortTypes.M006.{v, max u v, 0}) :
    FiniteDimensional K (TensorProduct ℤ K M) ∧ Module.finrank K (TensorProduct ℤ K M) = n l ∧ Nontrivial (TensorProduct ℤ K M) := by
  classical
  obtain ⟨q, b, bC, hb⟩ := h_H003.1
  have hq : q = n l := by
    have hc : Module.finrank ℂ V = q := by
      simpa using h_M006 ℂ V (Fin q) bC
    exact hc.symm.trans h_H002.2.1
  obtain ⟨B, hB⟩ := h_M002 K M (Fin q) b
  have hfinite : FiniteDimensional K (TensorProduct ℤ K M) :=
    B.finiteDimensional_of_finite
  have hdim : Module.finrank K (TensorProduct ℤ K M) = n l := by
    have hc : Module.finrank K (TensorProduct ℤ K M) = q := by
      simpa using h_M006_2 K (TensorProduct ℤ K M) (Fin q) B
    exact hc.trans hq
  refine ⟨hfinite, hdim, ?_⟩
  apply Module.nontrivial_of_finrank_pos (R := K)
  rw [hdim]
  exact Nat.zero_lt_succ l.toNat

theorem T017 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) :
    Nonempty (Actions M x y h) := by
  have hx : Stable M x := by
    simpa [dp] using (h_H003.2 1).1
  have hy : Stable M y := by
    simpa [dp] using (h_H003.2 1).2
  have hcomm : x * y - y * x = h := h_H002.2.2.2.2.1
  have hh : Stable M h := by
    intro m hm
    have hm' : x (y m) - y (x m) ∈ M :=
      M.sub_mem (hx (y m) (hy m hm)) (hy (x m) (hx m hm))
    have heq : h m = x (y m) - y (x m) := by
      rw [← hcomm]
      rfl
    rw [heq]
    exact hm'
  let res : (t : Module.End ℂ V) → Stable M t → Module.End ℤ M :=
    fun t ht => (t.restrictScalars ℤ).restrict (p := M) (q := M) ht
  exact ⟨{
    xZ := res x hx
    yZ := res y hy
    hZ := res h hh
    XZ := fun r => res (dp x r) (h_H003.2 r).1
    YZ := fun r => res (dp y r) (h_H003.2 r).2
    x_eq := fun m => rfl
    y_eq := fun m => rfl
    h_eq := fun m => rfl
    X_eq := fun r m => rfl
    Y_eq := fun r m => rfl
  }⟩

theorem T015 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T009 : (∀ j : Fin (n l), (coeff l j.val : K) ≠ 0) ∧ (∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) ∧ ((detCoeff l : K) ≠ 0)) (h_T013 : (∀ a : Actions M x y h,
 (∀ i j k q : Fin (n l), matrixUnit K a l i j * matrixUnit K a l k q = if j = k then matrixUnit K a l i q else 0) ∧
 ((∑ i : Fin (n l), matrixUnit K a l i i) = 1)) ∧ (∀ a : Actions M x y h, ∀ r : ℕ, r ≤ l.toNat →
 ((Nat.factorial r : K) • red K (a.XZ r) = (red K a.xZ) ^ r) ∧
 ((Nat.factorial r : K) • red K (a.YZ r) = (red K a.yZ) ^ r))) (h_T017 : Nonempty (Actions M x y h)) :
    ∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) →
 ∀ i j : Fin (n l), Inv W (matrixUnit K a l i j) := by
  intro a W hx hy hh
  have hp : ∀ (t : Module.End K (TensorProduct ℤ K M)),
      Inv W t → ∀ r : ℕ, Inv W (t ^ r) := by
    intro t ht r
    induction r with
    | zero =>
        intro z hz
        simpa using hz
    | succ r ih =>
        intro z hz
        simpa only [pow_succ, Module.End.mul_apply] using ih (t z) (ht z hz)
  have hd : ∀ (t s : Module.End K (TensorProduct ℤ K M)) (r : ℕ),
      Inv W t → r ≤ l.toNat →
      (Nat.factorial r : K) • s = t ^ r → Inv W s := by
    intro t s r ht hr he z hz
    have hc : (Nat.factorial r : K) ≠ 0 := h_T009.2.1 r hr
    have hez : (Nat.factorial r : K) • s z = (t ^ r) z :=
      congrArg (fun f : Module.End K (TensorProduct ℤ K M) => f z) he
    have hm := W.smul_mem (Nat.factorial r : K)⁻¹ (hp t ht r z hz)
    rw [← hez, inv_smul_smul₀ hc] at hm
    exact hm
  have hX : ∀ r : ℕ, r ≤ l.toNat → Inv W (red K (a.XZ r)) := by
    intro r hr
    exact hd (red K a.xZ) (red K (a.XZ r)) r hx hr (h_T013.2 a r hr).1
  have hY : ∀ r : ℕ, r ≤ l.toNat → Inv W (red K (a.YZ r)) := by
    intro r hr
    exact hd (red K a.yZ) (red K (a.YZ r)) r hy hr (h_T013.2 a r hr).2
  intro i j z hz
  change (coeff l j.val : K)⁻¹ • (red K (rawZ a l i j)) z ∈ W
  apply W.smul_mem
  simp only [red, rawZ, LinearMap.baseChange_mul, Module.End.mul_apply]
  exact hX (l.toNat - i.val) (Nat.sub_le _ _)
    _ (hY l.toNat le_rfl _ (hX l.toNat le_rfl _
      (hY (l.toNat - j.val) (Nat.sub_le _ _) z hz)))

theorem T016 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T013 : (∀ a : Actions M x y h,
 (∀ i j k q : Fin (n l), matrixUnit K a l i j * matrixUnit K a l k q = if j = k then matrixUnit K a l i q else 0) ∧
 ((∑ i : Fin (n l), matrixUnit K a l i i) = 1)) ∧ (∀ a : Actions M x y h, ∀ r : ℕ, r ≤ l.toNat →
 ((Nat.factorial r : K) • red K (a.XZ r) = (red K a.xZ) ^ r) ∧
 ((Nat.factorial r : K) • red K (a.YZ r) = (red K a.yZ) ^ r))) (h_T014 : FiniteDimensional K (TensorProduct ℤ K M) ∧ Module.finrank K (TensorProduct ℤ K M) = n l ∧ Nontrivial (TensorProduct ℤ K M)) (h_T015 : ∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) →
 ∀ i j : Fin (n l), Inv W (matrixUnit K a l i j)) (h_E001 : @YuiPortTypes.E001.{v, max u v}) (h_T017 : Nonempty (Actions M x y h)) :
    Nontrivial (TensorProduct ℤ K M) ∧ Nonempty (Actions M x y h) ∧ (∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) → W = ⊥ ∨ W = ⊤) := by
  letI : FiniteDimensional K (TensorProduct ℤ K M) := h_T014.1
  refine ⟨h_T014.2.2, h_T017, ?_⟩
  intro a W hx hy hh
  exact h_E001 K (TensorProduct ℤ K M) (n l) (matrixUnit K a l)
    h_T014.2.1 (h_T013.1 a).1 (h_T013.1 a).2 W
    (h_T015 a W hx hy hh)

end Translation

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (ι : Type*) [Fintype ι] (v : ι → U), LinearIndependent K v → Fintype.card ι = Module.finrank K U → Submodule.span K (Set.range v) = ⊤ := by
  intro K U _ _ _ _ ι _ v hv hc
  exact hv.span_eq_top_of_card_eq_finrank' hc
set_option Elab.async false in
theorem B002 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (ι : Type*) (b : Basis ι ℤ M), ∃ B : Basis ι K (TensorProduct ℤ K M), ∀ i : ι, B i = TensorProduct.tmul ℤ (1 : K) (b i) := by
  intro K M _ _ _ ι b
  refine ⟨b.baseChange K, ?_⟩
  intro i
  exact b.baseChange_apply K i
set_option Elab.async false in
theorem B003 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ ρ : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (t : Module.End ℤ M) (a : K) (m : M), ρ t (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (t m) := by
  intro K M _ _ _
  let ρ : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M) :=
    { toFun := fun t => t.baseChange K
      map_one' := by exact LinearMap.baseChange_one ℤ M
      map_mul' := by intro f g; exact LinearMap.baseChange_mul f g
      map_zero' := by exact LinearMap.baseChange_zero
      map_add' := by intro f g; exact LinearMap.baseChange_add f g }
  refine ⟨ρ, ?_⟩
  intro t a m
  rfl
set_option Elab.async false in
theorem B004 : ∀ (A : Type*) [Ring A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p] (n : ℕ), IsUnit (Nat.factorial n : A) ↔ n < p := by
  intro A _ p _ _ n
  exact IsUnit.natCast_factorial_iff_of_charP (A := A) p
set_option Elab.async false in
theorem B006 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] (ι : Type*) (b : Basis ι K U), Module.finrank K U = Nat.card ι := by
  intro K U _ _ _ ι b
  exact Module.finrank_eq_nat_card_basis b
set_option Elab.async false in
theorem B007 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ e : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M, ∀ (m : M) (a : K), e (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m := by
  intro K M _ _ _
  letI : Module ℤ (TensorProduct ℤ M K) := TensorProduct.instModule
  letI : Module ℤ (TensorProduct ℤ K M) := TensorProduct.instModule
  refine ⟨(TensorProduct.comm ℤ M K).toAddEquiv, ?_⟩
  intro m a
  rfl
set_option Elab.async false in
theorem B008 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  intro K U _ _ _ _ n F hdim hmul hsum W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hex : ∃ j : Fin n, F j j w ≠ 0 := by
    by_contra hn
    have hz : ∀ j : Fin n, F j j w = 0 := by simpa using hn
    have hs := congrArg (fun f : Module.End K U => f w) hsum
    have : w = 0 := by simpa [LinearMap.sum_apply, hz] using hs.symm
    exact hw0 this
  obtain ⟨j, hj⟩ := hex
  let u : U := F j j w
  have hu0 : u ≠ 0 := hj
  have huW : u ∈ W := hW j j w hw
  have huu : F j j u = u := by
    have ht := congrArg (fun f : Module.End K U => f w) (hmul j j j j)
    simpa [Module.End.mul_apply, u] using ht
  let v : Fin n → U := fun i => F i j u
  have hact (k i : Fin n) : F j k (v i) = if k = i then u else 0 := by
    have ht := congrArg (fun f : Module.End K U => f u) (hmul j k i j)
    change F j k (F i j u) = _
    by_cases hki : k = i
    · simpa [Module.End.mul_apply, hki, huu] using ht
    · simpa [Module.End.mul_apply, hki] using ht
  have hli : LinearIndependent K v := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg k
    have ht := congrArg (fun x : U => F j k x) hg
    have hs : g k • u = 0 := by
      simpa [map_sum, map_smul, hact] using ht
    exact (smul_eq_zero.mp hs).resolve_right hu0
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    YuiBasis.B001 K U (Fin n) v hli (by simpa using hdim.symm)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact hW i j u huW

end YuiBasis

namespace Translation
set_option autoImplicit false
private theorem __connected_T001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) :
    (∀ i : ℕ, h ((y ^ i) w) = ((l : ℂ) - 2 * (i : ℂ)) • (y ^ i) w) ∧ (∀ i : ℕ, x ((y ^ (i + 1)) w) = (((i + 1 : ℕ) : ℂ) * ((l : ℂ) - (i : ℂ))) • (y ^ i) w) ∧ (∀ i : Fin (n l), vec y w (i.val) ≠ 0) ∧ (∀ i : ℕ, h (vec y w (i)) = ((l : ℂ) - 2 * (i : ℂ)) • vec y w (i)) := by
  exact @T001 p K instK l V instV instCV x y h w M h_H001 h_H002

private theorem __connected_T002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) :
    LinearIndependent ℂ (fun i : Fin (n l) => vec y w (i.val)) := by
  exact @T002 p K instK l V instV instCV x y h w M (@__connected_T001 p K instK l V instV instCV x y h w M h_H001 h_H002)

private theorem __connected_T003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) :
    ∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val) := by
  exact @T003 p K instK l V instV instCV x y h w M h_H001 h_H002 (@__connected_T002 p K instK l V instV instCV x y h w M h_H001 h_H002) (@YuiBasis.B001.{0, u, 0})

private theorem __connected_T004 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) :
    ((y ^ (l.toNat + 1)) w = 0) ∧ (∀ r : ℕ, l.toNat < r → (y ^ r) w = 0) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) := by
  exact @T004 p K instK l V instV instCV x y h w M h_H001 h_H002 (@__connected_T001 p K instK l V instV instCV x y h w M h_H001 h_H002) (@__connected_T003 p K instK l V instV instCV x y h w M h_H001 h_H002)

private theorem __connected_T005 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    (∃ b : Basis (Fin (n l)) ℂ V, ∀ i, b i = vec y w (i.val)) ∧ (x (vec y w (0)) = 0 ∧
 (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → x (vec y w (i)) = ((l : ℂ) - (i : ℂ) + 1) • vec y w (i - 1)) ∧
 (∀ i : ℕ, i < l.toNat → y (vec y w (i)) = ((i + 1 : ℕ) : ℂ) • vec y w (i + 1)) ∧
 y (vec y w (l.toNat)) = 0 ∧
 (∀ i : Fin (n l), h (vec y w (i.val)) = ((l : ℂ) - 2 * (i.val : ℂ)) • vec y w (i.val))) ∧ (∀ (i : Fin (n l)) (r : ℕ),
 (dp x r (vec y w (i.val)) = if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • vec y w (i.val - r) else 0) ∧
 (dp y r (vec y w (i.val)) = if i.val + r ≤ l.toNat then (Nat.choose (i.val + r) r : ℂ) • vec y w (i.val + r) else 0)) := by
  exact @T005 p K instK l V instV instCV x y h w M h_H001 (@__connected_T003 p K instK l V instV instCV x y h w M h_H001 h_H002) (@__connected_T004 p K instK l V instV instCV x y h w M h_H001 h_H002) h_M005

private theorem __connected_T006 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    ∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) := by
  exact @T006 p K instK l V instV instCV x y h w M h_H001 h_H003 (@__connected_T005 p K instK l V instV instCV x y h w M h_H001 h_H002 h_M005)

private theorem __connected_T007 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    (∃ E : Fin (n l) → Fin (n l) → Module.End ℂ V, (∀ i j k : Fin (n l), E i j (vec y w (k.val)) = if j = k then vec y w (i.val) else 0) ∧ (∀ i j : Fin (n l), raw l x y i j = (coeff l j.val : ℂ) • E i j)) ∧ (∀ i j : Fin (n l), Stable M (raw l x y i j)) ∧ (∀ i j k q : Fin (n l), raw l x y i j * raw l x y k q = if j = k then (coeff l j.val : ℂ) • raw l x y i q else 0) ∧ ((detCoeff l : ℂ) • (1 : Module.End ℂ V) = ∑ i : Fin (n l), (otherCoeff l i : ℂ) • raw l x y i i) := by
  exact @T007 p K instK l V instV instCV x y h w M (@__connected_T005 p K instK l V instV instCV x y h w M h_H001 h_H002 h_M005) (@__connected_T006 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005)

private theorem __connected_T010 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    ∀ a : Actions M x y h,
 (∀ i j : Fin (n l), ∀ m : M, (rawZ a l i j m : V) = raw l x y i j (m : V)) ∧
 (∀ i j k q : Fin (n l), rawZ a l i j * rawZ a l k q = if j = k then (coeff l j.val : ℤ) • rawZ a l i q else 0) ∧
 ((detCoeff l : ℤ) • (1 : Module.End ℤ M) = ∑ i : Fin (n l), (otherCoeff l i : ℤ) • rawZ a l i i) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.XZ r = a.xZ ^ r) ∧
 (∀ r : ℕ, (Nat.factorial r : ℤ) • a.YZ r = a.yZ ^ r) := by
  exact @T010 p K instK l V instV instCV x y h w M h_H001 h_H003 (@__connected_T007 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005)

private theorem __connected_T011 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V)  :
    (∀ (t : Module.End ℤ M) (c : K) (m : M), red K t (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (t m)) ∧
 (∀ s t : Module.End ℤ M, red K (s + t) = red K s + red K t) ∧
 (∀ s t : Module.End ℤ M, red K (s * t) = red K s * red K t) ∧
 (red K (1 : Module.End ℤ M) = 1) ∧
 (∀ (z : ℤ) (t : Module.End ℤ M), red K (z • t) = (z : K) • red K t) ∧
 (∀ (t : Module.End ℤ M) (r : ℕ), red K (t ^ r) = red K t ^ r) ∧
 (∃ σ : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M,
  (∀ (m : M) (c : K), σ (TensorProduct.tmul ℤ m c) = TensorProduct.tmul ℤ c m) ∧
  (∀ (d : K) (z : TensorProduct ℤ M K), σ (TensorProduct.map (LinearMap.id : M →ₗ[ℤ] M) (LinearMap.mulLeft ℤ d) z) = d • σ z) ∧
  (∀ (t : Module.End ℤ M) z, σ (TensorProduct.map t (LinearMap.id : K →ₗ[ℤ] K) z) = red K t (σ z))) := by
  exact @T011 p K instK l V instV instCV x y h w M (@YuiBasis.B003.{v, u}) (@YuiBasis.B007.{v, u})

private theorem __connected_T008 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) :
    ∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0 := by
  exact @T008 p K instK l V instV instCV x y h w M h_H001 (@YuiBasis.B004.{v})

private theorem __connected_T009 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    (∀ j : Fin (n l), (coeff l j.val : K) ≠ 0) ∧ (∀ r : ℕ, r ≤ l.toNat → (Nat.factorial r : K) ≠ 0) ∧ ((detCoeff l : K) ≠ 0) := by
  exact @T009 p K instK l V instV instCV x y h w M h_H001 (@__connected_T008 p K instK l V instV instCV x y h w M h_H001) h_M005

private theorem __connected_T012 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    ∀ a : Actions M x y h,
 (∀ i j k q : Fin (n l), matrixUnit K a l i j * matrixUnit K a l k q = if j = k then matrixUnit K a l i q else 0) ∧
 ((∑ i : Fin (n l), matrixUnit K a l i i) = 1) := by
  exact @T012 p K instK l V instV instCV x y h w M h_H001 (@__connected_T007 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005) (@__connected_T009 p K instK l V instV instCV x y h w M h_H001 h_M005) (@__connected_T010 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005) (@__connected_T011 p K instK l V instV instCV x y h w M)

private theorem __connected_T013 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    (∀ a : Actions M x y h,
 (∀ i j k q : Fin (n l), matrixUnit K a l i j * matrixUnit K a l k q = if j = k then matrixUnit K a l i q else 0) ∧
 ((∑ i : Fin (n l), matrixUnit K a l i i) = 1)) ∧ (∀ a : Actions M x y h, ∀ r : ℕ, r ≤ l.toNat →
 ((Nat.factorial r : K) • red K (a.XZ r) = (red K a.xZ) ^ r) ∧
 ((Nat.factorial r : K) • red K (a.YZ r) = (red K a.yZ) ^ r)) := by
  exact @T013 p K instK l V instV instCV x y h w M (@__connected_T010 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005) (@__connected_T011 p K instK l V instV instCV x y h w M) (@__connected_T012 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005)

private theorem __connected_T014 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) :
    FiniteDimensional K (TensorProduct ℤ K M) ∧ Module.finrank K (TensorProduct ℤ K M) = n l ∧ Nontrivial (TensorProduct ℤ K M) := by
  exact @T014 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 (@__connected_T011 p K instK l V instV instCV x y h w M) (@YuiBasis.B002.{v, u, 0}) (@YuiBasis.B006.{0, u, 0}) (@YuiBasis.B006.{v, max u v, 0})

private theorem __connected_T017 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) :
    Nonempty (Actions M x y h) := by
  exact @T017 p K instK l V instV instCV x y h w M h_H002 h_H003

private theorem __connected_T015 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    ∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) →
 ∀ i j : Fin (n l), Inv W (matrixUnit K a l i j) := by
  exact @T015 p K instK l V instV instCV x y h w M h_H001 (@__connected_T009 p K instK l V instV instCV x y h w M h_H001 h_M005) (@__connected_T013 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005) (@__connected_T017 p K instK l V instV instCV x y h w M h_H002 h_H003)

private theorem __connected_T016 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) :
    Nontrivial (TensorProduct ℤ K M) ∧ Nonempty (Actions M x y h) ∧ (∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) → W = ⊥ ∨ W = ⊤) := by
  exact @T016 p K instK l V instV instCV x y h w M h_H001 (@__connected_T013 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005) (@__connected_T014 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003) (@__connected_T015 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005) (@YuiBasis.B008.{v, max u v}) (@__connected_T017 p K instK l V instV instCV x y h w M h_H002 h_H003)

theorem P (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_M001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (ι : Type*) [Fintype ι] (v : ι → U), LinearIndependent K v → Fintype.card ι = Module.finrank K U → Submodule.span K (Set.range v) = ⊤) (h_M002 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (ι : Type*) (b : Basis ι ℤ M), ∃ B : Basis ι K (TensorProduct ℤ K M), ∀ i : ι, B i = TensorProduct.tmul ℤ (1 : K) (b i)) (h_M003 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ ρ : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (t : Module.End ℤ M) (a : K) (m : M), ρ t (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (t m)) (h_M004 : ∀ (A : Type*) [Ring A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p] (n : ℕ), IsUnit (Nat.factorial n : A) ↔ n < p) (h_M005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n) (h_M006 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] (ι : Type*) (b : Basis ι K U), Module.finrank K U = Nat.card ι) (h_M007 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ e : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M, ∀ (m : M) (a : K), e (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : Nontrivial (TensorProduct ℤ K M) ∧ Nonempty (Actions M x y h) ∧ (∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) → W = ⊥ ∨ W = ⊤) := by
  exact @__connected_T016 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_M005

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
theorem resolved_M001 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (ι : Type*) [Fintype ι] (v : ι → U), LinearIndependent K v → Fintype.card ι = Module.finrank K U → Submodule.span K (Set.range v) = ⊤ := by
  intro K U _ _ _ _ ι _ v hv hcard
  exact hv.span_eq_top_of_card_eq_finrank' hcard

theorem resolved_M002 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (ι : Type*) (b : Basis ι ℤ M), ∃ B : Basis ι K (TensorProduct ℤ K M), ∀ i : ι, B i = TensorProduct.tmul ℤ (1 : K) (b i) := by
  intro K M _ _ _ ι b
  exact ⟨b.baseChange K, fun i => b.baseChange_apply K i⟩

theorem resolved_M003 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ ρ : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (t : Module.End ℤ M) (a : K) (m : M), ρ t (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (t m) := by
  intro K M _ _ _
  refine ⟨{ toFun := fun t => t.baseChange K
            map_one' := by ext; simp
            map_mul' := by intro s t; ext; simp
            map_zero' := by ext; simp
            map_add' := by intro s t; ext; simp }, ?_⟩
  intro t a m
  exact LinearMap.baseChange_tmul t a m

theorem resolved_M004 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : ∀ (A : Type*) [Ring A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p] (n : ℕ), IsUnit (Nat.factorial n : A) ↔ n < p := by
  intro A _ p _ _ n
  exact IsUnit.natCast_factorial_iff_of_charP p

theorem resolved_M005 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n := by
  intro n k h
  exact Nat.choose_mul_factorial_mul_factorial h

theorem resolved_M006 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] (ι : Type*) (b : Basis ι K U), Module.finrank K U = Nat.card ι := by
  intro K U _ _ _ ι b
  exact Module.finrank_eq_nat_card_basis b

theorem resolved_M007 (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ e : TensorProduct ℤ M K ≃+ TensorProduct ℤ K M, ∀ (m : M) (a : K), e (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m := by
  intro K M _ _ _
  let σ := TensorProduct.comm ℤ M K
  refine ⟨{ toFun := fun z => σ z
            invFun := fun z => σ.symm z
            left_inv := fun z => LinearEquiv.symm_apply_apply σ z
            right_inv := fun z => LinearEquiv.apply_symm_apply σ z
            map_add' := fun z z' => σ.map_add z z' }, ?_⟩
  intro m a
  exact TensorProduct.comm_tmul ℤ M K m a

set_option Elab.async false in
theorem P (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) (h_E001 : ∀ (K U : Type*) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U] (n : ℕ) (F : Fin n → Fin n → Module.End K U), Module.finrank K U = n → (∀ i j k l, F i j * F k l = if j = k then F i l else 0) → (∑ i : Fin n, F i i) = 1 → ∀ W : Submodule K U, (∀ i j (w : U), w ∈ W → F i j w ∈ W) → W = ⊥ ∨ W = ⊤) : Nontrivial (TensorProduct ℤ K M) ∧ Nonempty (Actions M x y h) ∧ (∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) → W = ⊥ ∨ W = ⊤) := by
  exact @Translation.P.{_, _, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, _, _} p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 (@resolved_M001 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_E001) (@resolved_M002 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_E001) (@resolved_M003 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_E001) (@resolved_M004 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_E001) (@resolved_M005 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_E001) (@resolved_M006 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_E001) (@resolved_M007 p K instK l V instV instCV x y h w M h_H001 h_H002 h_H003 h_E001) h_E001

#check @P
#print axioms P
end AuditBExport


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n := by
  intro n k h
  exact Nat.choose_mul_factorial_mul_factorial h

end YuiBasis

namespace YuiClosed
set_option autoImplicit false
/- Instantiate only universes that disappear when checked E proofs replace
   premises. Public levels are inferred from the actual arguments/target.
   This elaborator builds an ordinary application, checked by Lean's kernel;
   it adds no theorem, axiom or proof dependency. -/
open Lean Elab Term in
elab "yui_basis_declared_levels%" : term => do
  return toExpr (← getLevelNames)

-- Capture only the header's explicitly declared levels, before P introduces
-- auto-generated Type* names. Those names can shift after E is removed.
private def yuiBasisDeclaredLevels : List Lean.Name := yui_basis_declared_levels%

open Lean Meta Elab Term in
elab "yui_basis_export%" "(" args:term,* ")" : term <= expectedType => do
  let info ← getConstInfo `AuditBExport.P
  let used ← forallTelescope info.type fun xs body => do
    let mut retained := #[]
    let omitted : Array String := #["h_E001"]
    for x in xs do
      let decl ← getFVarLocalDecl x
      if !omitted.contains decl.userName.toString then
        retained := retained.push x
    return (collectLevelParams {} (← mkForallFVars retained body)).params
  let levels ← info.levelParams.mapM fun name =>
    if !used.contains name then pure Level.zero
    -- A named public level retains its name, including max/imax expressions
    -- that cannot be uniquely reconstructed from fresh metavariables. Type*
    -- introduces fresh local levels; infer those from the actual arguments.
    else if yuiBasisDeclaredLevels.contains name then pure (Level.param name)
    else mkFreshLevelMVar
  elabAppArgs (mkConst `AuditBExport.P levels) #[] (args.getElems.map Arg.stx)
    expectedType (explicit := true) (ellipsis := false)

set_option Elab.async false in
theorem P (p : ℕ) (K : Type v) [instK : Field K] (l : ℤ) (V : Type u) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (w : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n l ∧
 (h * x - x * h = (2 : ℂ) • x) ∧
 (h * y - y * h = (-2 : ℂ) • y) ∧
 (x * y - y * x = h) ∧ w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w ∧
 (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤)) (h_H003 : (∃ (q : ℕ) (b : Basis (Fin q) ℤ M) (bC : Basis (Fin q) ℂ V), ∀ i, (b i : V) = bC i) ∧
 (∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r))) : Nontrivial (TensorProduct ℤ K M) ∧ Nonempty (Actions M x y h) ∧ (∀ a : Actions M x y h, ∀ W : Submodule K (TensorProduct ℤ K M),
 Inv W (red K a.xZ) → Inv W (red K a.yZ) → Inv W (red K a.hZ) → W = ⊥ ∨ W = ⊤) := by
  exact yui_basis_export%(p, K, instK, l, V, instV, instCV, x, y, h, w, M, h_H001, h_H002, h_H003, (@YuiBasis.B008))

end YuiClosed
