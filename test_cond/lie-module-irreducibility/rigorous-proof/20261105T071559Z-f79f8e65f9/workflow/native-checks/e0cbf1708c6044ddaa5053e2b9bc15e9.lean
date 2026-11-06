import Mathlib
open scoped TensorProduct
noncomputable section
namespace Chevalley
def R (p : ℕ) : Subalgebra ℤ ℚ :=
  Algebra.adjoin ℤ {q : ℚ | ∃ b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (b : ℚ)⁻¹}
instance rComplex (p : ℕ) : Algebra (R p) ℂ :=
  Algebra.compHom ℂ (algebraMap (R p) ℚ)
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def dp (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r
def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dp y i v
abbrev MR (p : ℕ) (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
def mu (p : ℕ) (M : Submodule ℤ V) : MR p M → V :=
  letI := Module.compHom V (algebraMap (R p) ℂ)
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  M.subtype.liftBaseChange (R p)
def image (p : ℕ) (M : Submodule ℤ V) : Set V := Set.range (mu p M)
def latticeOp (M : Submodule ℤ V) (f : Module.End ℂ V) : Module.End ℤ M :=
  letI := Classical.propDecidable
  if hf : ∀ u ∈ M, f u ∈ M then (f.restrictScalars ℤ).restrict hf else 0
abbrev VK (K : Type) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
def opK (K : Type) [Field K] (M : Submodule ℤ V) (f : Module.End ℂ V) :
    Module.End K (VK K M) := (latticeOp M f).baseChange K
def unitOp {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {ι : Type} (b : Module.Basis ι F W) (i j : ι) : Module.End F W :=
  (b.coord j).smulRight (b i)
def muR (p : ℕ) (M : Submodule ℤ V) :
    letI := Module.compHom V (algebraMap (R p) ℂ)
    MR p M →ₗ[R p] V :=
  letI := Module.compHom V (algebraMap (R p) ℂ)
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  M.subtype.liftBaseChange (R p)
def J (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) :
    Submodule (R p) ℂ :=
  letI := Module.compHom V (algebraMap (R p) ℂ)
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  (muR p M).range.comap (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[R p] ℂ) (e y v i))
def QJ (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) :
    Submodule ℚ ℂ := Submodule.span ℚ (J p M y v 0 : Set ℂ)
def qmul (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) :
    ℚ ⊗[R p] (J p M y v 0) →ₗ[ℚ] ℂ :=
  letI := IsScalarTower.of_compHom (R p) ℚ ℂ
  (J p M y v 0).subtype.liftBaseChange ℚ
abbrev Index (ell : ℤ) := Fin (ell.toNat + 1)
def stable {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (U : Submodule F W) (f : Module.End F W) : Prop := ∀ w ∈ U, f w ∈ U
def inImage (p : ℕ) (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ w ∈ image p M, f w ∈ image p M
def preserves (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ w ∈ M, f w ∈ M
def reductions (K : Type) [Field K] (p : ℕ) (M : Submodule ℤ V) : Prop :=
  ∃ hc : CharP K p,
  letI := hc
  letI := ZMod.algebra K p
  ∃ ρ : R p →+* K,
  (∀ a : ℤ, ρ (a : R p) = (a : K)) ∧
  letI := ρ.toAlgebra
  ∃ Φ : VK K M ≃ₗ[K] (K ⊗[R p] MR p M),
    (∀ (c : K) (m : M), Φ (c ⊗ₜ[ℤ] m) = c ⊗ₜ[R p] ((1 : R p) ⊗ₜ[ℤ] m)) ∧
    ∃ Ψ : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p),
      ∀ (c : K) (u : MR p M), Ψ (c ⊗ₜ[R p] u) = c ⊗ₜ[ZMod p] ModN.mkQ p u
def basisVec {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {n : ℕ} (b : Module.Basis (Fin n) F W) (i : ℕ) : W :=
  if hi : i < n then b ⟨i, hi⟩ else 0
def stringActions {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (ell : ℤ) (x y h : Module.End F W) (a : ℕ → W) : Prop :=
  ∀ i : ℕ, i ≤ ell.toNat →
    x (a i) = (if i = 0 then 0 else ((ell - (i : ℤ) + 1 : ℤ) : F) • a (i - 1)) ∧
    y (a i) = (if i < ell.toNat then ((i + 1 : ℕ) : F) • a (i + 1) else 0) ∧
    h (a i) = ((ell - 2 * (i : ℤ) : ℤ) : F) • a i
def dividedActions {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (ell : ℤ) (X Y : ℕ → Module.End F W) (a : ℕ → W) : Prop :=
  ∀ (r i : ℕ), i ≤ ell.toNat →
    X r (a i) = (if r ≤ i then ((Nat.choose (ell.toNat - i + r) r : ℕ) : F) • a (i - r) else 0) ∧
    Y r (a i) = (if i + r ≤ ell.toNat then ((Nat.choose (i + r) r : ℕ) : F) • a (i + r) else 0)
def matrixK (K : Type) [Field K] (ell : ℤ) (M : Submodule ℤ V)
    (x y : Module.End ℂ V) (i j : Index ell) : Module.End K (VK K M) :=
  ((Nat.choose ell.toNat j.val : K)⁻¹) •
    (opK K M (dp x (ell.toNat - i.val)) *
      (opK K M (dp y ell.toNat) * opK K M (dp x ell.toNat)) *
        opK K M (dp y (ell.toNat - j.val)))
end Chevalley

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, h (b i) = ((ell : ℂ) - 2 * (i.val : ℂ)) • b i) → ∀ w i, b.repr (h w) i = ((ell : ℂ) - 2 * (i.val : ℂ)) * b.repr w i" := by
  intro b hb w i
  have hw : h w = ∑ j, ((b.repr w j) * ((ell : ℂ) - 2 * (j.val : ℂ))) • b j := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, hb, smul_smul]
  have hc := congrArg (b.coord i) hw
  classical
  simpa [map_sum, map_smul, Module.Basis.coord_apply, Finsupp.single_apply, mul_comm] using hc

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0" := by
  have hh : ∀ i, h (Chevalley.e y v i) = ((ell : ℂ) - 2 * (i : ℂ)) • Chevalley.e y v i := by
    intro i
    simp only [Chevalley.e, Chevalley.dp, LinearMap.smul_apply, map_smul, h_T001.1 i, smul_smul]
    congr 1
    ring
  obtain ⟨b, hb⟩ := h_T002
  have hd := yui_aux_0001 V K p ell x y h v M h_H001 h_H003 h_T001 ⟨b, hb⟩ b (fun i => by rw [hb i]; exact hh i.val)
  have hz : (y ^ (ell.toNat + 1)) v = 0 := by
    apply b.repr.injective
    ext i
    have he := congrArg (fun w => b.repr w i) (h_T001.1 (ell.toNat + 1))
    rw [hd] at he
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
    have hn : ((ell : ℂ) - 2 * (i.val : ℂ)) ≠ ((ell : ℂ) - 2 * ((ell.toNat + 1 : ℕ) : ℂ)) := by
      intro heq
      have hi : (i.val : ℂ) = ((ell.toNat + 1 : ℕ) : ℂ) := by linear_combination -heq / 2
      have hi' : i.val = ell.toNat + 1 := by exact_mod_cast hi
      have := i.isLt
      omega
    have hc : b.repr ((y ^ (ell.toNat + 1)) v) i = 0 := (mul_eq_mul_right_iff.mp he).resolve_left hn
    simpa using hc
  intro t ht
  have ht' : t = (t - (ell.toNat + 1)) + (ell.toNat + 1) := by omega
  rw [ht', pow_add, Module.End.mul_apply, hz, map_zero]

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "(∀ i : ℕ, x (Chevalley.e y v (i+1)) = ((ell : ℂ) - (i : ℂ)) • Chevalley.e y v i) ∧ (∀ i : ℕ, y (Chevalley.e y v i) = ((i+1 : ℕ) : ℂ) • Chevalley.e y v (i+1))" := by
  have hf : ∀ i : ℕ, (i.factorial : ℂ) ≠ 0 := fun i => by exact_mod_cast Nat.factorial_ne_zero i
  constructor
  · intro i
    simp only [Chevalley.e, Chevalley.dp, LinearMap.smul_apply, map_smul]
    rw [h_T001.2 (i+1) (by omega)]
    simp only [Nat.add_sub_cancel, smul_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    congr 1
    have hi : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero i)
    field_simp
    <;> ring
  · intro i
    simp only [Chevalley.e, Chevalley.dp, LinearMap.smul_apply, map_smul]
    rw [pow_succ', Module.End.mul_apply]
    simp only [smul_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    congr 1
    have hi : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero i)
    field_simp

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "Chevalley.stringActions ell x y h (Chevalley.e y v)" := by
  have hg := yui_aux_0003 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002
  have hz := yui_aux_0002 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002
  intro i hi
  refine ⟨?_, ?_, ?_⟩
  · cases i with
    | zero => simpa [Chevalley.e, Chevalley.dp] using h_H003.2.1
    | succ i =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      rw [hg.1 i]
      congr 1
      push_cast
      ring
  · rw [hg.2 i]
    split_ifs with ht
    · rfl
    · have he : Chevalley.e y v (i+1) = 0 := by
        simp only [Chevalley.e, Chevalley.dp, LinearMap.smul_apply, hz (i+1) (by omega), smul_zero]
      rw [he, smul_zero]
  · simp only [Chevalley.e, Chevalley.dp, LinearMap.smul_apply, map_smul, h_T001.1 i, smul_smul]
    congr 1
    push_cast
    ring

theorem checked (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "∀ r i : ℕ, (y ^ r) (Chevalley.e y v i) = (((i+1).ascFactorial r : ℕ) : ℂ) • Chevalley.e y v (i+r)" := by
  have hg := (yui_aux_0003 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002).2
  intro r
  induction r with
  | zero => intro i; simp
  | succ r ih =>
    intro i
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hg, smul_smul, Nat.ascFactorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have he : i + (r + 1) = i + r + 1 := by omega
    rw [he]
    congr 1
    ring
#check @checked
#print axioms checked
end YuiAuxiliary
