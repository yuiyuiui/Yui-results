import Mathlib

universe u v w
open scoped BigOperators TensorProduct

namespace Reduction

def Stable {R : Type*} [Semiring R] {T : Type*} [AddCommMonoid T]
    [Module R T] (W : Submodule R T) (f : T → T) : Prop :=
  ∀ z ∈ W, f z ∈ W

noncomputable def dp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  (Nat.factorial r : ℂ)⁻¹ • f ^ r

noncomputable def e {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (y : Module.End ℂ V) (v : V) (i : Fin (lam.toNat + 1)) : V :=
  dp y i.val v

def IsBasisFamily {R : Type*} [CommRing R] {T : Type*} [AddCommGroup T]
    [Module R T] {n : ℕ} (a : Fin n → T) : Prop :=
  ∃ b : Module.Basis (Fin n) R T, ∀ i, b i = a i

def Scaled {M : Type*} [AddCommGroup M] [Module ℤ M]
    (m : ℕ) (A B : ℕ → Module.End ℤ M) (i j : Fin (m + 1)) : Module.End ℤ M :=
  ((Nat.factorial j.val * Nat.factorial (m - j.val) : ℕ) : ℤ) •
    (A (m - i.val) * B m * A m * B (m - j.val))

noncomputable def ComplexScaled {V : Type*} [AddCommGroup V] [Module ℂ V]
    (m : ℕ) (x y : Module.End ℂ V) (i j : Fin (m + 1)) : Module.End ℂ V :=
  ((Nat.factorial j.val * Nat.factorial (m - j.val) : ℕ) : ℂ) •
    (dp x (m - i.val) * dp y m * dp x m * dp y (m - j.val))

noncomputable def Fext (K : Type*) [Field K] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : Module.End ℤ M) : Module.End K (K ⊗[ℤ] M) :=
  f.baseChange K

noncomputable def U (K : Type*) [Field K] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (m : ℕ) (A B : ℕ → Module.End ℤ M)
    (i j : Fin (m + 1)) : Module.End K (K ⊗[ℤ] M) :=
  (Nat.factorial m : K)⁻¹ • Fext K (Scaled m A B i j)

def MatrixUnits {F : Type*} [Field F] {T : Type*} [AddCommGroup T] [Module F T]
    (n : ℕ) (C : Fin n → Fin n → Module.End F T) : Prop :=
  (∀ i j k l, C i j * C k l = if j = k then C i l else 0) ∧
    (∑ i, C i i) = 1

abbrev VK (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module ℤ M] :=
  M ⊗[ℤ] K

noncomputable instance originalModule (K : Type*) [Field K] (M : Type*)
    [AddCommGroup M] [Module ℤ M] : Module K (VK K M) :=
  let flip : VK K M ≃+ (K ⊗[ℤ] M) :=
    { toEquiv := (TensorProduct.comm ℤ M K).toEquiv
      map_add' := (TensorProduct.comm ℤ M K).map_add }
  flip.module K

def originalAction (K : Type*) [Field K] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : Module.End ℤ M) : Module.End ℤ (VK K M) :=
  TensorProduct.map f (LinearMap.id : K →ₗ[ℤ] K)

def Standing (p : ℕ) (K : Type*) [Field K] (lam : ℤ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (x y h : Module.End ℂ V) (v : V)
    (M : Submodule ℤ V) (A B : ℕ → Module.End ℤ M) : Prop :=
  Nat.Prime p ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ) ∧
  (Module.finrank ℂ V : ℤ) = lam + 1 ∧
  h * x - x * h = (2 : ℂ) • x ∧
  h * y - y * h = -(2 : ℂ) • y ∧ x * y - y * x = h ∧
  v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧
  (∀ W : Submodule ℂ V, Stable W x → Stable W y → Stable W h →
    W = ⊥ ∨ W = ⊤) ∧
  (∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℤ M,
    ∃ c : Module.Basis (Fin n) ℂ V, ∀ i, c i = (b i : V)) ∧
  (∀ r (z : M), (A r z : V) = dp x r (z : V)) ∧
  (∀ r (z : M), (B r z : V) = dp y r (z : V))

end Reduction
namespace YuiPortTypes
abbrev E001 : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (ι : Type w) (f : Module.End ℂ V) (μ : ι → ℂ) (a : ι → V), Function.Injective μ → (∀ i, f.HasEigenvector (μ i) (a i)) → LinearIndependent ℂ a
abbrev E002 : Prop :=
  ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (a : Fin n → V), Module.finrank K V = n → LinearIndependent K a → Submodule.span K (Set.range a) = ⊤
abbrev E003 : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M) (K : Type u) [Field K], ∃ c : Module.Basis (Fin n) K (K ⊗[ℤ] M), ∀ i, c i = (1 : K) ⊗ₜ[ℤ] b i
abbrev E004 : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (K : Type u) [Field K], ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M), ∀ (f : Module.End ℤ M) (a : K) (m : M), Φ f (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] f m
abbrev E005 : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → IsUnit (Nat.factorial r : K)
abbrev E006 : Prop :=
  ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] (n : ℕ) (b : Module.Basis (Fin n) K V), Module.finrank K V = n
abbrev T016 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) : Prop :=
  ∀ (F : Type u) [Field F] (T : Type (max u v)) [AddCommGroup T] [Module F T]
  [FiniteDimensional F T] (n : ℕ), 0 < n → Module.finrank F T = n →
  ∀ C : Fin n → Fin n → Module.End F T, Reduction.MatrixUnits n C →
  ∀ Z : Submodule F T, (∀ i j, Reduction.Stable Z (C i j)) → Z = ⊥ ∨ Z = ⊤
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

theorem T009 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_E003 : @YuiPortTypes.E003.{u, v}) (h_E006 : @YuiPortTypes.E006.{0, v}) (h_E006_2 : @YuiPortTypes.E006.{u, max u v}) :
    (∀ b : Module.Basis (Fin (lam.toNat + 1)) ℤ M,
    Reduction.IsBasisFamily (R := K) (fun i => (1 : K) ⊗ₜ[ℤ] b i)) ∧
  FiniteDimensional K (K ⊗[ℤ] M) ∧
  Module.finrank K (K ⊗[ℤ] M) = lam.toNat + 1 ∧ Nontrivial (K ⊗[ℤ] M) := by
  classical
  have hall : ∀ b : Module.Basis (Fin (lam.toNat + 1)) ℤ M,
      Reduction.IsBasisFamily (R := K) (fun i => (1 : K) ⊗ₜ[ℤ] b i) := by
    intro b
    exact h_E003 M (lam.toNat + 1) b K
  rcases h_H001 with ⟨_, _, hlam, _, hdim, _, _, _, _, _, _, _, ⟨n, b, c, hbc⟩, _, _⟩
  have hcount : Module.finrank ℂ V = n := h_E006 ℂ V n c
  have hcast : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg hlam
  have hn : n = lam.toNat + 1 := by omega
  let b' : Module.Basis (Fin (lam.toNat + 1)) ℤ M := b.reindex (finCongr hn)
  obtain ⟨c', hc'⟩ := h_E003 M (lam.toNat + 1) b' K
  refine ⟨hall, c'.finiteDimensional_of_finite, h_E006_2 K (K ⊗[ℤ] M) (lam.toNat + 1) c', ?_⟩
  exact ⟨⟨c' ⟨0, Nat.zero_lt_succ _⟩, 0, c'.ne_zero _⟩⟩

theorem T010 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M)  :
    (∀ (a t : K) (z : M),
    a • (z ⊗ₜ[ℤ] t : Reduction.VK K M) = z ⊗ₜ[ℤ] (a * t)) ∧
  ∃ τ : Reduction.VK K M ≃ₗ[K] (K ⊗[ℤ] M),
    (∀ (z : M) (a : K), τ (z ⊗ₜ[ℤ] a) = a ⊗ₜ[ℤ] z) ∧
    (∀ (a : K) (z : M), τ.symm (a ⊗ₜ[ℤ] z) = z ⊗ₜ[ℤ] a) ∧
    (∀ (f : Module.End ℤ M) (z : Reduction.VK K M),
      τ (Reduction.originalAction K f z) = Reduction.Fext K f (τ z)) := by
  let flip : Reduction.VK K M ≃+ (K ⊗[ℤ] M) :=
    { toEquiv := (TensorProduct.comm ℤ M K).toEquiv
      map_add' := (TensorProduct.comm ℤ M K).map_add }
  let τ : Reduction.VK K M ≃ₗ[K] (K ⊗[ℤ] M) := flip.linearEquiv K
  have hτ : ∀ (z : M) (a : K), τ (z ⊗ₜ[ℤ] a) = a ⊗ₜ[ℤ] z := by
    intros
    rfl
  have hσ : ∀ (a : K) (z : M), τ.symm (a ⊗ₜ[ℤ] z) = z ⊗ₜ[ℤ] a := by
    intros
    rfl
  constructor
  · intro a t z
    apply τ.injective
    rw [map_smul, hτ, hτ, TensorProduct.smul_tmul']
    rfl
  · refine ⟨τ, hτ, hσ, ?_⟩
    intro f z
    induction z using TensorProduct.inductionOn with
    | tmul z a => simp [Reduction.originalAction, Reduction.Fext, hτ]
    | add z w hz hw =>
      simp only [map_add, hz, hw]

theorem T011 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T009 : (∀ b : Module.Basis (Fin (lam.toNat + 1)) ℤ M,
    Reduction.IsBasisFamily (R := K) (fun i => (1 : K) ⊗ₜ[ℤ] b i)) ∧
  FiniteDimensional K (K ⊗[ℤ] M) ∧
  Module.finrank K (K ⊗[ℤ] M) = lam.toNat + 1 ∧ Nontrivial (K ⊗[ℤ] M)) (h_T010 : (∀ (a t : K) (z : M),
    a • (z ⊗ₜ[ℤ] t : Reduction.VK K M) = z ⊗ₜ[ℤ] (a * t)) ∧
  ∃ τ : Reduction.VK K M ≃ₗ[K] (K ⊗[ℤ] M),
    (∀ (z : M) (a : K), τ (z ⊗ₜ[ℤ] a) = a ⊗ₜ[ℤ] z) ∧
    (∀ (a : K) (z : M), τ.symm (a ⊗ₜ[ℤ] z) = z ⊗ₜ[ℤ] a) ∧
    (∀ (f : Module.End ℤ M) (z : Reduction.VK K M),
      τ (Reduction.originalAction K f z) = Reduction.Fext K f (τ z))) :
    ((∀ b : Module.Basis (Fin (lam.toNat + 1)) ℤ M,
    Reduction.IsBasisFamily (R := K) (fun i => (1 : K) ⊗ₜ[ℤ] b i)) ∧
  FiniteDimensional K (K ⊗[ℤ] M) ∧
  Module.finrank K (K ⊗[ℤ] M) = lam.toNat + 1 ∧ Nontrivial (K ⊗[ℤ] M)) ∧ ((∀ (a t : K) (z : M),
    a • (z ⊗ₜ[ℤ] t : Reduction.VK K M) = z ⊗ₜ[ℤ] (a * t)) ∧
  ∃ τ : Reduction.VK K M ≃ₗ[K] (K ⊗[ℤ] M),
    (∀ (z : M) (a : K), τ (z ⊗ₜ[ℤ] a) = a ⊗ₜ[ℤ] z) ∧
    (∀ (a : K) (z : M), τ.symm (a ⊗ₜ[ℤ] z) = z ⊗ₜ[ℤ] a) ∧
    (∀ (f : Module.End ℤ M) (z : Reduction.VK K M),
      τ (Reduction.originalAction K f z) = Reduction.Fext K f (τ z))) ∧
  FiniteDimensional K (Reduction.VK K M) ∧
  Module.finrank K (Reduction.VK K M) = lam.toNat + 1 ∧
  Nontrivial (Reduction.VK K M) ∧ ((∀ z : M, (A 1 z : V) = x (z : V)) ∧
  (∀ z : M, (B 1 z : V) = y (z : V)) ∧
  (∀ z : M, ((A 1 * B 1 - B 1 * A 1) z : V) = h (z : V))) := by
  classical
  rcases h_T010.2 with ⟨τ, hτ, hτinv, hinter⟩
  letI : FiniteDimensional K (K ⊗[ℤ] M) := h_T009.2.1
  letI : Nontrivial (K ⊗[ℤ] M) := h_T009.2.2.2
  have hfinite : FiniteDimensional K (Reduction.VK K M) :=
    τ.symm.finiteDimensional
  have hdim : Module.finrank K (Reduction.VK K M) = lam.toNat + 1 :=
    τ.finrank_eq.trans h_T009.2.2.1
  have hnontrivial : Nontrivial (Reduction.VK K M) :=
    τ.toEquiv.nontrivial
  rcases h_H001 with ⟨_, _, _, _, _, _, _, hxy, _, _, _, _, _, hA, hB⟩
  have ha : ∀ z : M, (A 1 z : V) = x (z : V) := by
    intro z
    simpa [Reduction.dp] using hA 1 z
  have hb : ∀ z : M, (B 1 z : V) = y (z : V) := by
    intro z
    simpa [Reduction.dp] using hB 1 z
  refine ⟨h_T009, h_T010, hfinite, hdim, hnontrivial, ha, hb, ?_⟩
  intro z
  calc
    (((A 1 * B 1 - B 1 * A 1) z : M) : V) =
        x (y (z : V)) - y (x (z : V)) := by
      change (A 1 (B 1 z) : V) - (B 1 (A 1 z) : V) = _
      rw [ha, hb, hb, ha]
    _ = h (z : V) := by
      have heq := congrArg (fun f : Module.End ℂ V => f (z : V)) hxy
      simpa using heq

theorem T001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v) := by
  have hlam : 0 ≤ lam := h_H001.2.2.1
  have hhy : h * y - y * h = -(2 : ℂ) • y := h_H001.2.2.2.2.2.2.1
  have hhv : h v = (lam : ℂ) • v := h_H001.2.2.2.2.2.2.2.2.2.2.1
  have hell : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg hlam
  intro t
  induction t with
  | zero => simpa [hell] using hhv
  | succ t ih =>
    have hrel : h (y ((y ^ t) v)) - y (h ((y ^ t) v)) = -(2 : ℂ) • y ((y ^ t) v) := by
      simpa using congrArg (fun f : Module.End ℂ V => f ((y ^ t) v)) hhy
    rw [ih, map_smul] at hrel
    rw [pow_succ']
    change h (y ((y ^ t) v)) =
      ((lam.toNat : ℤ) - 2 * ((t + 1 : ℕ) : ℤ) : ℂ) • y ((y ^ t) v)
    calc
      h (y ((y ^ t) v)) = -(2 : ℂ) • y ((y ^ t) v) +
          ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • y ((y ^ t) v) :=
        sub_eq_iff_eq_add.mp hrel
      _ = _ := by
        rw [← add_smul]
        congr 1
        push_cast
        ring

namespace Local_T002
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T001 : ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) : yui_aux_type% "x ((y ^ (1 : ℕ)) v) = (((1 : ℕ) : ℂ) * ((lam.toNat : ℤ) - ((1 : ℕ) : ℤ) + 1 : ℂ)) • ((y ^ ((1 : ℕ) - 1)) v)" := by
  rcases h_H001 with ⟨hp, hchar, hlam, hlt, hdim, hhx, hhy, hxy, hv, hxv, hhv, hrest⟩
  have hz := congrArg (fun f : Module.End ℂ V => f v) hxy
  have hw : h v = ((lam.toNat : ℤ) : ℂ) • v := by
    simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, Int.cast_zero,
      mul_zero, sub_zero] using h_T001 0
  change x (y v) - y (x v) = h v at hz
  rw [hw] at hz
  simpa only [pow_one, Nat.cast_one, Int.cast_one, sub_add_cancel,
    Nat.sub_self, pow_zero, Module.End.one_apply, one_mul, hxv, map_zero,
    sub_zero] using hz

end Local_T002
open Local_T002 in
theorem T002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T001 : ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) :
    ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v) := by
  have hbase := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T001
  rcases h_H001 with ⟨hp, hchar, hlam, hlt, hdim, hhx, hhy, hxy, hv, hxv, hhv, hrest⟩
  have comm (z : V) : x (y z) = y (x z) + h z := by
    have hz := congrArg (fun f : Module.End ℂ V => f z) hxy
    change x (y z) - y (x z) = h z at hz
    exact (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hbase
  | succ t ht ih =>
      have hy : y ((y ^ (t - 1)) v) = (y ^ t) v := by
        rw [← Module.End.mul_apply, ← pow_succ']
        have he : t - 1 + 1 = t := by omega
        rw [he]
      calc
        x ((y ^ (t + 1)) v) = y (x ((y ^ t) v)) + h ((y ^ t) v) := by
          rw [pow_succ', Module.End.mul_apply, comm]
        _ = ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ t) v) +
            (((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ)) • ((y ^ t) v) := by
          rw [ih, map_smul, hy, h_T001]
        _ = (((t + 1 : ℕ) : ℂ) *
            ((lam.toNat : ℤ) - ((t + 1 : ℕ) : ℤ) + 1 : ℂ)) •
            ((y ^ (t + 1 - 1)) v) := by
          simp only [Nat.add_sub_cancel]
          rw [← add_smul]
          congr 1
          push_cast
          ring

namespace Local_T003
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T001 : ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) (h_T002 : ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) : yui_aux_type% "∀ t : ℕ, (x ^ t) ((y ^ t) v) = ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v" := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ x, Module.End.mul_apply, h_T002 (t + 1) (by omega)]
    simp only [Nat.add_sub_cancel, map_smul]
    rw [ih, smul_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Finset.prod_range_succ]
    congr 1
    push_cast
    ring

theorem yui_aux_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T001 : ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) (h_T002 : ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) : yui_aux_type% "∀ t : ℕ, t ≤ lam.toNat → ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) ≠ 0" := by
  intro t ht
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero t
  · apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    have ha' : a < lam.toNat := lt_of_lt_of_le (Finset.mem_range.mp ha) ht
    have hz : (lam.toNat : ℤ) - (a : ℤ) ≠ 0 := by omega
    exact_mod_cast hz

theorem yui_aux_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T001 : ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) (h_T002 : ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) : yui_aux_type% "∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i = (Nat.factorial i.val : ℂ)⁻¹ • (y ^ i.val) v" := by
  intro i
  simp only [Reduction.e, Reduction.dp, LinearMap.smul_apply]

theorem yui_aux_0004 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T001 : ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) (h_T002 : ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) : yui_aux_type% "Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ))" := by
  intro i j hij
  change ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) = ((lam.toNat : ℤ) - 2 * (j.val : ℤ) : ℂ) at hij
  have hz : (lam.toNat : ℤ) - 2 * (i.val : ℤ) = (lam.toNat : ℤ) - 2 * (j.val : ℤ) := by
    exact_mod_cast hij
  apply Fin.ext
  omega

end Local_T003
open Local_T003 in
theorem T003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T001 : ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) (h_T002 : ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) :
    (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ))) := by
  have hiter := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T001 h_T002
  have hcoeff := @yui_aux_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T001 h_T002
  have he := @yui_aux_0003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T001 h_T002
  have hinj := @yui_aux_0004 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T001 h_T002
  have hv : v ≠ 0 := h_H001.2.2.2.2.2.2.2.2.1
  have hnonzero : ∀ t : ℕ, t ≤ lam.toNat → (x ^ t) ((y ^ t) v) ≠ 0 := by
    intro t ht
    rw [hiter t]
    exact smul_ne_zero (hcoeff t ht) hv
  refine ⟨h_T001, h_T002, ?_, ?_, hinj⟩
  · intro t ht
    exact ⟨hiter t, hnonzero t ht⟩
  · intro i
    have hyi : (y ^ i.val) v ≠ 0 := by
      intro hz
      apply hnonzero i.val (by omega)
      rw [hz, map_zero]
    have hfac : (Nat.factorial i.val : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero i.val
    rw [he i]
    constructor
    · exact smul_ne_zero (inv_ne_zero hfac) hyi
    · rw [map_smul, h_T001]
      exact smul_comm _ _ _

theorem T004 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T003 : (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) :
    Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v) := by
  classical
  have heig : ∀ i : Fin (lam.toNat + 1),
      h.HasEigenvector ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)
        (Reduction.e lam y v i) := by
    intro i
    exact Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (h_T003.2.2.2.1 i).2,
        (h_T003.2.2.2.1 i).1⟩
  have hli : LinearIndependent ℂ (Reduction.e lam y v) :=
    h_E001 V (Fin (lam.toNat + 1)) h
      (fun i : Fin (lam.toNat + 1) =>
        ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ))
      (Reduction.e lam y v) h_T003.2.2.2.2 heig
  have hnat : (lam.toNat : ℤ) = lam :=
    Int.toNat_of_nonneg h_H001.2.2.1
  have hdimZ : (Module.finrank ℂ V : ℤ) = ((lam.toNat + 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one, hnat] using h_H001.2.2.2.2.1
  have hdim : Module.finrank ℂ V = lam.toNat + 1 := by
    exact_mod_cast hdimZ
  have hspan : Submodule.span ℂ (Set.range (Reduction.e lam y v)) = ⊤ :=
    h_E002 ℂ V (lam.toNat + 1) (Reduction.e lam y v) hdim hli
  refine ⟨Module.Basis.mk hli (ge_of_eq hspan), ?_⟩
  intro i
  exact Module.Basis.mk_apply hli (ge_of_eq hspan) i

namespace Local_T005
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T003 : (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)))) (h_T004 : Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) : yui_aux_type% "∀ (b : Module.Basis (Fin (lam.toNat + 1)) ℂ V),\n(∀ i, h (b i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • b i) →\n∀ (w : V) (i : Fin (lam.toNat + 1)),\nb.repr (h w) i = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) * b.repr w i" := by
  classical
  intro b he w i
  change b.coord i (h w) = _
  have hex : h w = ∑ j, b.repr w j • h (b j) := by
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    congr 1
    funext j
    exact h.map_smul _ _
  rw [hex, map_sum]
  simp only [map_smul, he, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    smul_eq_mul]
  simp [mul_ite, mul_comm]

theorem yui_aux_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T003 : (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)))) (h_T004 : Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) : yui_aux_type% "(y ^ (lam.toNat + 1)) v = 0" := by
  classical
  rcases h_T004 with ⟨b, hb⟩
  have he (i : Fin (lam.toNat + 1)) :
      h (b i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • b i := by
    simpa only [hb] using (h_T003.2.2.2.1 i).2
  have hd := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T003 ⟨b, hb⟩ b he
  apply b.repr.injective
  ext i
  have hw := h_T003.1 (lam.toNat + 1)
  have hc := hd ((y ^ (lam.toNat + 1)) v) i
  rw [hw] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have hn : (((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) -
      ((lam.toNat : ℤ) - 2 * ((lam.toNat + 1 : ℕ) : ℤ) : ℂ)) ≠ 0 := by
    have hz : (lam.toNat : ℤ) - 2 * (i.val : ℤ) -
        ((lam.toNat : ℤ) - 2 * ((lam.toNat + 1 : ℕ) : ℤ)) ≠ 0 := by
      have := i.isLt
      omega
    exact_mod_cast hz
  have hz : ((((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) -
      ((lam.toNat : ℤ) - 2 * ((lam.toNat + 1 : ℕ) : ℤ) : ℂ)) *
      b.repr ((y ^ (lam.toNat + 1)) v) i) = 0 := by
    linear_combination -hc
  simpa using (mul_eq_zero.mp hz).resolve_left hn

theorem yui_aux_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T003 : (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)))) (h_T004 : Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) : yui_aux_type% "∀ n : ℕ, y (Reduction.dp y n v) =\n  (n + 1 : ℂ) • Reduction.dp y (n + 1) v" := by
  intro n
  have hf : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [Reduction.dp, LinearMap.smul_apply, map_smul]
  rw [pow_succ', Module.End.mul_apply]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_smul]
  congr 1
  field_simp

theorem yui_aux_0004 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T003 : (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)))) (h_T004 : Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) : yui_aux_type% "∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),\n    ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →\n    x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)" := by
  intro i hi j hj
  have hfac : Nat.factorial i.val = i.val * Nat.factorial (i.val - 1) := by
    conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
    rw [Nat.factorial_succ]
    congr 1 <;> omega
  have hf : (Nat.factorial (i.val - 1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (i.val - 1)
  have hn : (i.val : ℂ) ≠ 0 := by
    exact_mod_cast (show i.val ≠ 0 by omega)
  simp only [Reduction.e, Reduction.dp, LinearMap.smul_apply, map_smul]
  rw [h_T003.2.1 i.val hi]
  simp only [hj, smul_smul]
  congr 1
  rw [hfac, Nat.cast_mul]
  field_simp
  <;> ring

end Local_T005
open Local_T005 in
theorem T005 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T003 : (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)))) (h_T004 : Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) :
    (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
  (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
  (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
    x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
    y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
  (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
    ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i))) := by
  have hz := @yui_aux_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T003 h_T004
  have hy := @yui_aux_0003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T003 h_T004
  have hx := @yui_aux_0004 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T003 h_T004
  refine ⟨h_T004, ⟨hz, ?_⟩, ?_, hx, ?_, ?_, ?_⟩
  · intro t ht
    rw [show t = (t - (lam.toNat + 1)) + (lam.toNat + 1) by omega,
      pow_add, Module.End.mul_apply, hz, map_zero]
  · rcases h_H001 with ⟨hp, hc, hl, hlt, hd, hhx, hhy, hxy, hv, hxv, rest⟩
    simpa [Reduction.e, Reduction.dp] using hxv
  · intro i hi j hj
    simpa only [Reduction.e, hj] using hy i.val
  · change y (Reduction.dp y lam.toNat v) = 0
    rw [hy]
    simp [Reduction.dp, LinearMap.smul_apply, hz]
  · intro i
    exact (h_T003.2.2.2.1 i).2

namespace Local_T006
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
  (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
  (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
    x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
    y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
  (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
    ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : yui_aux_type% "Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)" := by
  have yui_nested_c7adab41de543832_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : (Function.Injective (fun i : Fin (lam.toNat + 1) =>
    ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ))) := by
    intro i j hij
    dsimp only at hij
    have hz : (lam.toNat : ℤ) - 2 * (i.val : ℤ) =
        (lam.toNat : ℤ) - 2 * (j.val : ℤ) := by
      exact_mod_cast hij
    apply Fin.ext
    omega
  classical
  rcases h_T005.1 with ⟨b, hb⟩
  have hnz (i : Fin (lam.toNat + 1)) : Reduction.e lam y v i ≠ 0 := by
    rw [← hb i]
    exact b.ne_zero i
  let μ : Fin (lam.toNat + 1) → ℂ :=
    fun i => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ)
  have hμ : Function.Injective μ :=
    @yui_nested_c7adab41de543832_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B
      h_H001 h_T005 h_E001 h_E002
  have heig : ∀ i, h.HasEigenvector (μ i) (Reduction.e lam y v i) := by
    intro i
    exact ⟨Module.End.mem_eigenspace_iff.mpr (h_T005.2.2.2.2.2.2 i), hnz i⟩
  have hli : LinearIndependent ℂ (Reduction.e lam y v) :=
    h_E001 V (Fin (lam.toNat + 1)) h μ (Reduction.e lam y v) hμ heig
  have hlam : 0 ≤ lam := h_H001.2.2.1
  have hdimZ : (Module.finrank ℂ V : ℤ) = lam + 1 := h_H001.2.2.2.2.1
  have hdim : Module.finrank ℂ V = lam.toNat + 1 := by
    omega
  have hspan : Submodule.span ℂ (Set.range (Reduction.e lam y v)) = ⊤ :=
    h_E002 ℂ V (lam.toNat + 1) (Reduction.e lam y v) hdim hli
  exact ⟨Module.Basis.mk hli hspan.ge, fun i => Module.Basis.mk_apply hli hspan.ge i⟩

theorem yui_aux_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
  (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
  (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
    x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
    y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
  (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
    ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : yui_aux_type% "(∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val → ∀ j : Fin (lam.toNat + 1), j.val = i.val - r → Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧ (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0)" := by
  have yui_nested_9acd1b75ca9729a8_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val) (j : Fin (lam.toNat + 1)), j.val = i.val - 1 → x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • Reduction.e lam y v j) := by
    exact h_T005.2.2.2.1
  have yui_nested_9acd1b75ca9729a8_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val → ∀ j : Fin (lam.toNat + 1), j.val = i.val - r → (x ^ r) (Reduction.e lam y v i) = ((lam.toNat - i.val + 1).ascFactorial r : ℂ) • (Reduction.e lam y v j)) := by
    intro r
    induction r with
    | zero =>
        intro i hi j hj
        have hji : j = i := Fin.ext (by simpa using hj)
        subst j
        simp
    | succ r ih =>
        intro i hi j hj
        let k : Fin (lam.toNat + 1) := ⟨i.val - r, by omega⟩
        have hk : k.val = i.val - r := rfl
        have hkpos : 1 ≤ k.val := by omega
        have hjk : j.val = k.val - 1 := by omega
        have hdiff : (lam.toNat : ℤ) - (k.val : ℤ) + 1 = ((lam.toNat - i.val + 1 + r : ℕ) : ℤ) := by
          have := i.isLt
          omega
        have hc : ((lam.toNat : ℤ) - (k.val : ℤ) + 1 : ℂ) = ((lam.toNat - i.val + 1 + r : ℕ) : ℂ) := by
          exact_mod_cast hdiff
        rw [pow_succ', Module.End.mul_apply, ih i (by omega) k hk, map_smul,
          (@yui_nested_9acd1b75ca9729a8_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002) k hkpos j hjk, smul_smul, hc, Nat.ascFactorial_succ]
        congr 1
        push_cast
        ring
  have yui_nested_9acd1b75ca9729a8_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → (x ^ r) (Reduction.e lam y v i) = 0) := by
    intro r
    induction r with
    | zero =>
        intro i hi
        omega
    | succ r ih =>
        intro i hi
        by_cases hir : i.val < r
        · rw [pow_succ', Module.End.mul_apply, ih i hir, map_zero]
        · have hie : i.val = r := by omega
          have hz : (⟨0, Nat.zero_lt_succ lam.toNat⟩ : Fin (lam.toNat + 1)).val = i.val - r := by simp [hie]
          rw [pow_succ', Module.End.mul_apply,
            (@yui_nested_9acd1b75ca9729a8_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002) r i (by omega) ⟨0, Nat.zero_lt_succ lam.toNat⟩ hz,
            map_smul, h_T005.2.2.1, smul_zero]
  constructor
  · intro r i hi j hj
    have hraw := (@yui_nested_9acd1b75ca9729a8_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002) r i hi j hj
    have hf : (Nat.factorial r : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero r
    change (Nat.factorial r : ℂ)⁻¹ • ((x ^ r) (Reduction.e lam y v i)) = _
    rw [hraw, Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_smul,
      inv_mul_cancel_left₀ hf]
  · intro r i hi
    change (Nat.factorial r : ℂ)⁻¹ • ((x ^ r) (Reduction.e lam y v i)) = 0
    rw [(@yui_nested_9acd1b75ca9729a8_0003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002) r i hi, smul_zero]

theorem yui_aux_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
  (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
  (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
    x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
    y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
  (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
    ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : yui_aux_type% "(∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat → ∀ j : Fin (lam.toNat + 1), j.val = i.val + r → Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧ (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r → Reduction.dp y r (Reduction.e lam y v i) = 0)" := by
  have yui_nested_0b580d01893dd02d_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : ((∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat → ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 → y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • Reduction.e lam y v j) ∧ y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0) := by
    exact ⟨h_T005.2.2.2.2.1, h_T005.2.2.2.2.2.1⟩
  have yui_nested_0b580d01893dd02d_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : (∀ i r : ℕ, (((i + 1).ascFactorial r : ℕ) : ℂ) * (((i + r : ℕ) : ℂ) + 1) = (((i + 1).ascFactorial (r + 1) : ℕ) : ℂ)) := by
    intro i r
    rw [Nat.ascFactorial_succ]
    push_cast
    ring
  have yui_nested_0b580d01893dd02d_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : (∀ r : ℕ, (∀ (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat → ∀ j : Fin (lam.toNat + 1), j.val = i.val + r → (y ^ r) (Reduction.e lam y v i) = (((i.val + 1).ascFactorial r : ℕ) : ℂ) • Reduction.e lam y v j) ∧ (∀ (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r → (y ^ r) (Reduction.e lam y v i) = 0)) := by
    have hy := @yui_nested_0b580d01893dd02d_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002
    have hc := @yui_nested_0b580d01893dd02d_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002
    intro r
    induction r with
    | zero =>
        constructor
        · intro i hi j hj
          have he : j = i := Fin.ext (by simpa using hj)
          subst j
          simp
        · intro i hi
          have := i.isLt
          omega
    | succ r ih =>
        constructor
        · intro i hi j hj
          let k : Fin (lam.toNat + 1) := ⟨i.val + r, by omega⟩
          have hk : k.val = i.val + r := rfl
          have hklt : k.val < lam.toNat := by omega
          rw [pow_succ', Module.End.mul_apply, ih.1 i (by omega) k hk,
            map_smul, hy.1 k hklt j (by omega), smul_smul]
          congr 1
          exact hc i.val r
        · intro i hi
          rw [pow_succ', Module.End.mul_apply]
          by_cases hprev : lam.toNat < i.val + r
          · rw [ih.2 i hprev, map_zero]
          · have heq : i.val + r = lam.toNat := by omega
            let k : Fin (lam.toNat + 1) := ⟨lam.toNat, Nat.lt_succ_self _⟩
            rw [ih.1 i (by omega) k (by dsimp [k]; omega), map_smul]
            have htop : y (Reduction.e lam y v k) = 0 := hy.2
            rw [htop, smul_zero]
  have yui_nested_0b580d01893dd02d_0004 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
    (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
    (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
      ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
      x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
      ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
      y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
    y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
    (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
      ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) : (∀ i r : ℕ, (Nat.factorial r : ℂ)⁻¹ * (((i + 1).ascFactorial r : ℕ) : ℂ) = (Nat.choose (i + r) r : ℂ)) := by
    intro i r
    have hf : (Nat.factorial r : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
      inv_mul_cancel₀ hf, one_mul]
  have hraw := @yui_nested_0b580d01893dd02d_0003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002
  have hcoeff := @yui_nested_0b580d01893dd02d_0004 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002
  constructor
  · intro r i hi j hj
    change (Nat.factorial r : ℂ)⁻¹ • ((y ^ r) (Reduction.e lam y v i)) = _
    rw [(hraw r).1 i hi j hj, smul_smul, hcoeff i.val r]
  · intro r i hi
    change (Nat.factorial r : ℂ)⁻¹ • ((y ^ r) (Reduction.e lam y v i)) = 0
    rw [(hraw r).2 i hi, smul_zero]

end Local_T006
open Local_T006 in
theorem T006 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T005 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
  (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
  (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
    x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
    y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
  (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
    ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)))) (h_E001 : @YuiPortTypes.E001.{v, 0}) (h_E002 : @YuiPortTypes.E002.{0, v}) :
    (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0)) := by
  have hb := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002
  have hx := @yui_aux_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002
  have hy := @yui_aux_0003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T005 h_E001 h_E002
  exact ⟨hb, hx.1, hx.2, hy.1, hy.2⟩

namespace Local_T007
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) : yui_aux_type% "∀ i k : Fin (lam.toNat + 1), Reduction.dp x (lam.toNat - i.val) (Reduction.dp y lam.toNat (Reduction.dp x lam.toNat (Reduction.e lam y v k))) = if k.val = lam.toNat then Reduction.e lam y v i else 0" := by
  rcases h_T006 with ⟨hb, hx, hx0, hy, hy0⟩
  intro i k
  let z : Fin (lam.toNat + 1) := ⟨0, by omega⟩
  let t : Fin (lam.toNat + 1) := ⟨lam.toNat, by omega⟩
  by_cases hk : k.val = lam.toNat
  · have hxk := hx lam.toNat k (by omega) z (by simp [z, hk])
    have hyz := hy lam.toNat z (by simp [z]) t (by simp [z, t])
    have hxt := hx (lam.toNat - i.val) t (by simp [t]) i (by dsimp [t]; omega)
    have hxk' : Reduction.dp x lam.toNat (Reduction.e lam y v k) = Reduction.e lam y v z := by
      simpa [hk] using hxk
    have hyz' : Reduction.dp y lam.toNat (Reduction.e lam y v z) = Reduction.e lam y v t := by
      simpa [z] using hyz
    have hxt' : Reduction.dp x (lam.toNat - i.val) (Reduction.e lam y v t) = Reduction.e lam y v i := by
      simpa [t] using hxt
    simp only [hk, ↓reduceIte, hxk', hyz', hxt']
  · have hzero := hx0 lam.toNat k (by have := k.isLt; omega)
    simp [hk, hzero]

theorem yui_aux_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) : yui_aux_type% "∀ j : Fin (lam.toNat + 1), ((Nat.factorial j.val * Nat.factorial (lam.toNat - j.val) : ℕ) : ℂ) * (Nat.choose lam.toNat (lam.toNat - j.val) : ℂ) = (Nat.factorial lam.toNat : ℂ)" := by
  intro j
  have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
  have hn : (Nat.factorial j.val * Nat.factorial (lam.toNat - j.val)) * Nat.choose lam.toNat (lam.toNat - j.val) = Nat.factorial lam.toNat := by
    rw [Nat.choose_symm hj]
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.choose_mul_factorial_mul_factorial hj)
  exact_mod_cast hn

end Local_T007
open Local_T007 in
theorem T007 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) :
    ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0 := by
  have hcore := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006
  have hcoeff := @yui_aux_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006
  rcases h_T006 with ⟨hb, hx, hx0, hy, hy0⟩
  intro i j k
  have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
  simp only [Reduction.ComplexScaled, LinearMap.smul_apply, Module.End.mul_apply]
  by_cases hkj : k = j
  · subst k
    simp only [if_pos rfl]
    let t : Fin (lam.toNat + 1) := ⟨lam.toNat, by omega⟩
    have hs : j.val + (lam.toNat - j.val) = lam.toNat := by omega
    have hyj : Reduction.dp y (lam.toNat - j.val) (Reduction.e lam y v j) = (Nat.choose lam.toNat (lam.toNat - j.val) : ℂ) • Reduction.e lam y v t := by
      simpa only [hs] using hy (lam.toNat - j.val) j (by omega) t (by dsimp [t]; omega)
    rw [hyj, map_smul, map_smul, map_smul, hcore i t]
    simp only [t, ↓reduceIte, smul_smul]
    rw [hcoeff j]
  · simp only [if_neg hkj]
    by_cases hlt : k.val < j.val
    · let q : Fin (lam.toNat + 1) := ⟨k.val + (lam.toNat - j.val), by omega⟩
      have hyq := hy (lam.toNat - j.val) k (by omega) q rfl
      have hq : q.val ≠ lam.toNat := by dsimp [q]; omega
      rw [hyq, map_smul, map_smul, map_smul, hcore i q]
      simp [hq]
    · have hne : k.val ≠ j.val := by
        intro he
        exact hkj (Fin.ext he)
      have hzero := hy0 (lam.toNat - j.val) k (by omega)
      simp [hzero]

namespace Local_T008
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) (h_T007 : ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) : yui_aux_type% "∀ (n : ℕ) (z : V), (n : ℤ) • z = (n : ℂ) • z" := by
  intro n z
  simp only [Nat.cast_smul_eq_nsmul]

theorem yui_aux_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) (h_T007 : ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) : yui_aux_type% "∀ (i j : Fin (lam.toNat + 1)) (z : M), (Reduction.Scaled lam.toNat A B i j z : V) = Reduction.ComplexScaled lam.toNat x y i j (z : V)" := by
  have castsmul := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007
  rcases h_H001 with ⟨hp, hc, hl, hlt, hd, hx, hy, hxy, hv, hxv, hhv, hirr, hbas, hA, hB⟩
  intro i j z
  simp only [Reduction.Scaled, Reduction.ComplexScaled, LinearMap.smul_apply, Module.End.mul_apply, Submodule.coe_smul]
  rw [hA, hB, hA, hB]
  exact castsmul _ _

theorem yui_aux_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) (h_T007 : ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) : yui_aux_type% "(∀ i j k l : Fin (lam.toNat + 1), Reduction.ComplexScaled lam.toNat x y i j * Reduction.ComplexScaled lam.toNat x y k l = if j = k then (Nat.factorial lam.toNat : ℂ) • Reduction.ComplexScaled lam.toNat x y i l else 0) ∧ (∑ i : Fin (lam.toNat + 1), Reduction.ComplexScaled lam.toNat x y i i) = (Nat.factorial lam.toNat : ℂ) • (1 : Module.End ℂ V)" := by
  classical
  rcases h_T006.1 with ⟨b, hb⟩
  constructor
  · intro i j k l
    apply b.ext
    intro t
    rw [hb]
    by_cases hjk : j = k <;> by_cases htl : t = l <;>
      simp [Module.End.mul_apply, LinearMap.smul_apply, h_T007, hjk, htl, eq_comm]
  · apply b.ext
    intro t
    rw [hb]
    simp [LinearMap.sum_apply, h_T007]

theorem yui_aux_0004 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) (h_T007 : ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) : yui_aux_type% "(∀ i j k l : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i j * Reduction.Scaled lam.toNat A B k l = if j = k then (Nat.factorial lam.toNat : ℤ) • Reduction.Scaled lam.toNat A B i l else 0) ∧ (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) = (Nat.factorial lam.toNat : ℤ) • (1 : Module.End ℤ M)" := by
  classical
  have hs := @yui_aux_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007
  have hc := @yui_aux_0003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007
  have castsmul := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007
  constructor
  · intro i j k l
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    have he := congrArg (fun f : Module.End ℂ V => f (z : V)) (hc.1 i j k l)
    by_cases hjk : j = k
    · simpa only [if_pos hjk, Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul, hs, castsmul] using he
    · simpa only [if_neg hjk, Module.End.mul_apply, LinearMap.zero_apply, Submodule.coe_zero, hs] using he
  · apply LinearMap.ext
    intro z
    apply Subtype.ext
    have he := congrArg (fun f : Module.End ℂ V => f (z : V)) hc.2
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sum, Submodule.coe_smul, hs, castsmul] using he

theorem yui_aux_0005 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) (h_T007 : ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) : yui_aux_type% "∀ (f : Module.End ℂ V) (C : ℕ → Module.End ℤ M), (∀ (r : ℕ) (z : M), (C r z : V) = Reduction.dp f r (z : V)) → ∀ r : ℕ, (Nat.factorial r : ℤ) • C r = C 1 ^ r" := by
  intro f C hC
  have h1 : ∀ z : M, (C 1 z : V) = f (z : V) := by
    intro z
    simpa [Reduction.dp] using hC 1 z
  have hpow : ∀ (r : ℕ) (z : M), ((C 1 ^ r) z : V) = (f ^ r) (z : V) := by
    intro r
    induction r with
    | zero => intro z; rfl
    | succ r ih =>
      intro z
      simp only [pow_succ', Module.End.mul_apply, h1, ih]
  intro r
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [LinearMap.smul_apply, Submodule.coe_smul, hC, hpow]
  rw [@yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007]
  simp [Reduction.dp, smul_smul, Nat.factorial_ne_zero]

end Local_T008
open Local_T008 in
theorem T008 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T006 : (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0))) (h_T007 : ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) :
    (∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) ∧ (∀ (i j : Fin (lam.toNat + 1)) (z : M),
  (Reduction.Scaled lam.toNat A B i j z : V) =
    Reduction.ComplexScaled lam.toNat x y i j (z : V)) ∧ ((∀ i j k l : Fin (lam.toNat + 1),
    Reduction.Scaled lam.toNat A B i j * Reduction.Scaled lam.toNat A B k l =
    if j = k then (Nat.factorial lam.toNat : ℤ) • Reduction.Scaled lam.toNat A B i l else 0) ∧
  (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) =
    (Nat.factorial lam.toNat : ℤ) • (1 : Module.End ℤ M)) ∧ (∀ r : ℕ, (Nat.factorial r : ℤ) • A r = A 1 ^ r ∧
  (Nat.factorial r : ℤ) • B r = B 1 ^ r) := by
  have hs := @yui_aux_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007
  have hm := @yui_aux_0004 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007
  have hpows := @yui_aux_0005 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T006 h_T007
  refine ⟨h_T007, hs, hm, ?_⟩
  rcases h_H001 with ⟨hp, hc, hl, hlt, hd, hx, hy, hxy, hv, hxv, hhv, hirr, hbas, hA, hB⟩
  intro r
  exact ⟨hpows x A hA r, hpows y B hB r⟩

theorem T012 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_E004 : @YuiPortTypes.E004.{u, v}) :
    ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f := by
  obtain ⟨Φ, hΦ⟩ := h_E004 M K
  refine ⟨Φ, ?_⟩
  intro f
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      simpa only [Reduction.Fext, LinearMap.baseChange_tmul] using hΦ f a m
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add, hz₁, hz₂]

theorem T013 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_E005 : @YuiPortTypes.E005.{u}) :
    ∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0 := by
  intro r hr
  rcases h_H001 with ⟨hp, hchar, hlam, hlt, hrest⟩
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : CharP K p := hchar
  have hrp : r < p := by omega
  have hu : IsUnit (Nat.factorial r : K) := h_E005 K p r hrp
  exact ⟨hu, hu.ne_zero⟩

namespace Local_T014
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T008 : (∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) ∧ (∀ (i j : Fin (lam.toNat + 1)) (z : M),
  (Reduction.Scaled lam.toNat A B i j z : V) =
    Reduction.ComplexScaled lam.toNat x y i j (z : V)) ∧ ((∀ i j k l : Fin (lam.toNat + 1),
    Reduction.Scaled lam.toNat A B i j * Reduction.Scaled lam.toNat A B k l =
    if j = k then (Nat.factorial lam.toNat : ℤ) • Reduction.Scaled lam.toNat A B i l else 0) ∧
  (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) =
    (Nat.factorial lam.toNat : ℤ) • (1 : Module.End ℤ M)) ∧ (∀ r : ℕ, (Nat.factorial r : ℤ) • A r = A 1 ^ r ∧
  (Nat.factorial r : ℤ) • B r = B 1 ^ r)) (h_T012 : ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) (h_T013 : ∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) : yui_aux_type% "∀ (f g : Module.End ℤ M) (n : ℕ), Reduction.Fext K (f * g) = Reduction.Fext K f * Reduction.Fext K g ∧ Reduction.Fext K (f ^ n) = Reduction.Fext K f ^ n ∧ Reduction.Fext K ((n : ℤ) • f) = (n : K) • Reduction.Fext K f" := by
  obtain ⟨Φ, hΦ⟩ := h_T012
  intro f g n
  have hm : Φ (f * g) = Φ f * Φ g := Φ.map_mul f g
  have hp : Φ (f ^ n) = Φ f ^ n := map_pow Φ f n
  have hs : Φ ((n : ℤ) • f) = (n : K) • Φ f := by
    simpa only [Int.cast_id, Int.cast_natCast] using (map_intCast_smul Φ ℤ K (n : ℤ) f)
  simpa only [hΦ] using And.intro hm (And.intro hp hs)

theorem yui_aux_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T008 : (∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) ∧ (∀ (i j : Fin (lam.toNat + 1)) (z : M),
  (Reduction.Scaled lam.toNat A B i j z : V) =
    Reduction.ComplexScaled lam.toNat x y i j (z : V)) ∧ ((∀ i j k l : Fin (lam.toNat + 1),
    Reduction.Scaled lam.toNat A B i j * Reduction.Scaled lam.toNat A B k l =
    if j = k then (Nat.factorial lam.toNat : ℤ) • Reduction.Scaled lam.toNat A B i l else 0) ∧
  (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) =
    (Nat.factorial lam.toNat : ℤ) • (1 : Module.End ℤ M)) ∧ (∀ r : ℕ, (Nat.factorial r : ℤ) • A r = A 1 ^ r ∧
  (Nat.factorial r : ℤ) • B r = B 1 ^ r)) (h_T012 : ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) (h_T013 : ∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) : yui_aux_type% "∀ (n : ℕ) (f : Module.End ℤ M), Reduction.Fext K ((n : ℤ) • f) = (n : K) • Reduction.Fext K f" := by
  intro n f
  exact (@yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T008 h_T012 h_T013 f (1 : Module.End ℤ M) n).2.2

theorem yui_aux_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T008 : (∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) ∧ (∀ (i j : Fin (lam.toNat + 1)) (z : M),
  (Reduction.Scaled lam.toNat A B i j z : V) =
    Reduction.ComplexScaled lam.toNat x y i j (z : V)) ∧ ((∀ i j k l : Fin (lam.toNat + 1),
    Reduction.Scaled lam.toNat A B i j * Reduction.Scaled lam.toNat A B k l =
    if j = k then (Nat.factorial lam.toNat : ℤ) • Reduction.Scaled lam.toNat A B i l else 0) ∧
  (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) =
    (Nat.factorial lam.toNat : ℤ) • (1 : Module.End ℤ M)) ∧ (∀ r : ℕ, (Nat.factorial r : ℤ) • A r = A 1 ^ r ∧
  (Nat.factorial r : ℤ) • B r = B 1 ^ r)) (h_T012 : ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) (h_T013 : ∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) : yui_aux_type% "(∀ r : ℕ, (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧ (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (∀ i j k l : Fin (lam.toNat + 1), Reduction.Fext K (Reduction.Scaled lam.toNat A B i j) * Reduction.Fext K (Reduction.Scaled lam.toNat A B k l) = if j = k then (Nat.factorial lam.toNat : K) • Reduction.Fext K (Reduction.Scaled lam.toNat A B i l) else 0) ∧ (∑ i : Fin (lam.toNat + 1), Reduction.Fext K (Reduction.Scaled lam.toNat A B i i)) = (Nat.factorial lam.toNat : K) • (1 : Module.End K (K ⊗[ℤ] M))" := by
  have hm := @yui_aux_0001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T008 h_T012 h_T013
  have hs := @yui_aux_0002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T008 h_T012 h_T013
  obtain ⟨Φ, hΦ⟩ := h_T012
  have hz : Reduction.Fext K (0 : Module.End ℤ M) = 0 := by
    rw [← hΦ]; exact map_zero Φ
  have hsum : Reduction.Fext K (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) = ∑ i : Fin (lam.toNat + 1), Reduction.Fext K (Reduction.Scaled lam.toNat A B i i) := by
    have hh := map_sum Φ (fun i : Fin (lam.toNat + 1) => Reduction.Scaled lam.toNat A B i i) Finset.univ
    simpa only [hΦ] using hh
  have ho : Reduction.Fext K (1 : Module.End ℤ M) = 1 := by
    rw [← hΦ]; exact map_one Φ
  refine ⟨?_, ?_, ?_⟩
  · intro r
    constructor
    · have hh := congrArg (Reduction.Fext K) (h_T008.2.2.2 r).1
      rw [hs, (hm (A 1) (A 1) r).2.1] at hh
      exact hh
    · have hh := congrArg (Reduction.Fext K) (h_T008.2.2.2 r).2
      rw [hs, (hm (B 1) (B 1) r).2.1] at hh
      exact hh
  · intro i j k l
    have hh := congrArg (Reduction.Fext K) (h_T008.2.2.1.1 i j k l)
    rw [(hm _ _ 0).1] at hh
    by_cases hjk : j = k
    · rw [if_pos hjk, hs] at hh
      simpa only [if_pos hjk] using hh
    · rw [if_neg hjk, hz] at hh
      simpa only [if_neg hjk] using hh
  · have hh := congrArg (Reduction.Fext K) h_T008.2.2.1.2
    rw [hsum, hs, ho] at hh
    exact hh

end Local_T014
open Local_T014 in
theorem T014 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T008 : (∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) ∧ (∀ (i j : Fin (lam.toNat + 1)) (z : M),
  (Reduction.Scaled lam.toNat A B i j z : V) =
    Reduction.ComplexScaled lam.toNat x y i j (z : V)) ∧ ((∀ i j k l : Fin (lam.toNat + 1),
    Reduction.Scaled lam.toNat A B i j * Reduction.Scaled lam.toNat A B k l =
    if j = k then (Nat.factorial lam.toNat : ℤ) • Reduction.Scaled lam.toNat A B i l else 0) ∧
  (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) =
    (Nat.factorial lam.toNat : ℤ) • (1 : Module.End ℤ M)) ∧ (∀ r : ℕ, (Nat.factorial r : ℤ) • A r = A 1 ^ r ∧
  (Nat.factorial r : ℤ) • B r = B 1 ^ r)) (h_T012 : ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) (h_T013 : ∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) :
    (∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) ∧ (∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) ∧ (Nat.factorial lam.toNat : K) ≠ 0 ∧
  (∀ r : ℕ, r ≤ lam.toNat →
  (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧
  (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B)) := by
  classical
  have ht := @yui_aux_0003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 h_T008 h_T012 h_T013
  have hd : (Nat.factorial lam.toNat : K) ≠ 0 := (h_T013 lam.toNat le_rfl).2
  refine ⟨h_T012, h_T013, hd, ?_, ?_⟩
  · intro r hr
    exact ht.1 r
  · unfold Reduction.MatrixUnits
    constructor
    · intro i j k l
      dsimp only [Reduction.U]
      rw [smul_mul_smul_comm, ht.2.1 i j k l]
      by_cases hjk : j = k
      · simp only [if_pos hjk, smul_smul, mul_assoc, inv_mul_cancel₀ hd, mul_one]
      · simp only [if_neg hjk, smul_zero]
    · simp only [Reduction.U, ← Finset.smul_sum, ht.2.2, smul_smul,
        inv_mul_cancel₀ hd, one_smul]

namespace Local_T015
theorem yui_aux_0001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T014 : (∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) ∧ (∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) ∧ (Nat.factorial lam.toNat : K) ≠ 0 ∧
  (∀ r : ℕ, r ≤ lam.toNat →
  (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧
  (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B))) (h_E004 : @YuiPortTypes.E004.{u, v}) (h_E005 : @YuiPortTypes.E005.{u}) : yui_aux_type% "∀ (Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M)) (c : ℤ) (f : Module.End ℤ M), Φ (c • f) = (c : K) • Φ f" := by
  intro Φ c f
  rw [map_smul]
  exact (Int.cast_smul_eq_zsmul K c (Φ f)).symm

theorem yui_aux_0002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T014 : (∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) ∧ (∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) ∧ (Nat.factorial lam.toNat : K) ≠ 0 ∧
  (∀ r : ℕ, r ≤ lam.toNat →
  (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧
  (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B))) (h_E004 : @YuiPortTypes.E004.{u, v}) (h_E005 : @YuiPortTypes.E005.{u}) : yui_aux_type% "∀ i j : Fin (lam.toNat + 1), Reduction.Fext K (Reduction.Scaled lam.toNat A B i j) = ((Nat.factorial j.val * Nat.factorial (lam.toNat - j.val) : ℕ) : K) • (Reduction.Fext K (A (lam.toNat - i.val)) * Reduction.Fext K (B lam.toNat) * Reduction.Fext K (A lam.toNat) * Reduction.Fext K (B (lam.toNat - j.val)))" := by
  rcases h_E004 M K with ⟨Φ, hΦ⟩
  have hΦeq : ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f := by
    intro f
    apply LinearMap.ext
    intro q
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul a z => simpa only [Reduction.Fext, LinearMap.baseChange_tmul] using hΦ f a z
    | add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  intro i j
  rw [← hΦeq, Reduction.Scaled, yui_aux_0001 p K lam V x y h v M A B h_H001 h_T014 h_E004 h_E005]
  simp only [map_mul]
  simp only [hΦeq, Int.cast_natCast]

theorem yui_aux_0003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T014 : (∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) ∧ (∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) ∧ (Nat.factorial lam.toNat : K) ≠ 0 ∧
  (∀ r : ℕ, r ≤ lam.toNat →
  (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧
  (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B))) (h_E004 : @YuiPortTypes.E004.{u, v}) (h_E005 : @YuiPortTypes.E005.{u}) : yui_aux_type% "∀ r : ℕ, r ≤ lam.toNat → Reduction.Fext K (A r) = (Nat.factorial r : K)⁻¹ • Reduction.Fext K (A 1) ^ r ∧ Reduction.Fext K (B r) = (Nat.factorial r : K)⁻¹ • Reduction.Fext K (B 1) ^ r" := by
  have hp : Nat.Prime p := h_H001.1
  have hc : CharP K p := h_H001.2.1
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : CharP K p := hc
  have hlam : 0 ≤ lam := h_H001.2.2.1
  have hlam_lt : lam < (p : ℤ) := h_H001.2.2.2.1
  have hnat : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg hlam
  have hellp : lam.toNat < p := by omega
  intro r hr
  have hu : IsUnit (Nat.factorial r : K) := h_E005 K p r (lt_of_le_of_lt hr hellp)
  have hn : (Nat.factorial r : K) ≠ 0 := hu.ne_zero
  have ha := (h_T014.2.2.2.1 r hr).1
  have hb := (h_T014.2.2.2.1 r hr).2
  constructor
  · simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using congrArg (fun f : Module.End K (K ⊗[ℤ] M) => (Nat.factorial r : K)⁻¹ • f) ha
  · simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using congrArg (fun f : Module.End K (K ⊗[ℤ] M) => (Nat.factorial r : K)⁻¹ • f) hb

theorem yui_aux_0004 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T014 : (∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) ∧ (∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) ∧ (Nat.factorial lam.toNat : K) ≠ 0 ∧
  (∀ r : ℕ, r ≤ lam.toNat →
  (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧
  (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B))) (h_E004 : @YuiPortTypes.E004.{u, v}) (h_E005 : @YuiPortTypes.E005.{u}) : yui_aux_type% "∀ (W : Submodule K (K ⊗[ℤ] M)) (f : Module.End K (K ⊗[ℤ] M)), Reduction.Stable W f → ∀ r : ℕ, Reduction.Stable W ((f ^ r) : Module.End K (K ⊗[ℤ] M))" := by
  intro W f hf r
  induction r with
  | zero =>
      intro z hz
      simpa only [pow_zero, Module.End.one_apply] using hz
  | succ r ih =>
      intro z hz
      rw [pow_succ]
      exact ih (f z) (hf z hz)

end Local_T015
open Local_T015 in
theorem T015 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T014 : (∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) ∧ (∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) ∧ (Nat.factorial lam.toNat : K) ≠ 0 ∧
  (∀ r : ℕ, r ≤ lam.toNat →
  (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧
  (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B))) (h_E004 : @YuiPortTypes.E004.{u, v}) (h_E005 : @YuiPortTypes.E005.{u}) :
    (Nat.factorial lam.toNat : K) ≠ 0 ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B)) ∧ (∀ W : Submodule K (K ⊗[ℤ] M),
  Reduction.Stable W (Reduction.Fext K (A 1)) →
  Reduction.Stable W (Reduction.Fext K (B 1)) →
  ∀ i j : Fin (lam.toNat + 1), Reduction.Stable W (Reduction.U K lam.toNat A B i j)) := by
  refine ⟨h_T014.2.2.1, h_T014.2.2.2.2, ?_⟩
  intro W hA hB
  have hmul : ∀ f g : Module.End K (K ⊗[ℤ] M),
      Reduction.Stable W f → Reduction.Stable W g → Reduction.Stable W (f * g) := by
    intro f g hf hg z hz
    exact hf (g z) (hg z hz)
  have hsmul : ∀ (c : K) (f : Module.End K (K ⊗[ℤ] M)),
      Reduction.Stable W f → Reduction.Stable W (c • f) := by
    intro c f hf z hz
    exact W.smul_mem c (hf z hz)
  have hpow := yui_aux_0004 p K lam V x y h v M A B h_H001 h_T014 h_E004 h_E005 W
  have hAr : ∀ r : ℕ, r ≤ lam.toNat → Reduction.Stable W (Reduction.Fext K (A r)) := by
    intro r hr
    rw [(yui_aux_0003 p K lam V x y h v M A B h_H001 h_T014 h_E004 h_E005 r hr).1]
    exact hsmul _ _ (hpow _ hA r)
  have hBr : ∀ r : ℕ, r ≤ lam.toNat → Reduction.Stable W (Reduction.Fext K (B r)) := by
    intro r hr
    rw [(yui_aux_0003 p K lam V x y h v M A B h_H001 h_T014 h_E004 h_E005 r hr).2]
    exact hsmul _ _ (hpow _ hB r)
  intro i j
  unfold Reduction.U
  rw [yui_aux_0002 p K lam V x y h v M A B h_H001 h_T014 h_E004 h_E005 i j]
  apply hsmul
  apply hsmul
  apply hmul
  · apply hmul
    · apply hmul
      · exact hAr _ (Nat.sub_le _ _)
      · exact hBr _ (le_refl _)
    · exact hAr _ (le_refl _)
  · exact hBr _ (Nat.sub_le _ _)

theorem T016 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_E002 : @YuiPortTypes.E002.{u, max u v}) :
    ∀ (F : Type u) [Field F] (T : Type (max u v)) [AddCommGroup T] [Module F T]
  [FiniteDimensional F T] (n : ℕ), 0 < n → Module.finrank F T = n →
  ∀ C : Fin n → Fin n → Module.End F T, Reduction.MatrixUnits n C →
  ∀ Z : Submodule F T, (∀ i j, Reduction.Stable Z (C i j)) → Z = ⊥ ∨ Z = ⊤ := by
  classical
  intro F _ T _ _ _ n hn hdim C hC Z hstable
  rcases hC with ⟨hmul, hsum⟩
  by_cases hZ : Z = ⊥
  · exact Or.inl hZ
  · right
    obtain ⟨w, hwZ, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
    have hdiag : ∃ j : Fin n, C j j w ≠ 0 := by
      by_contra hnone
      have hzero : ∀ j : Fin n, C j j w = 0 := by simpa using hnone
      have hwSum := congrArg (fun f : Module.End F T => f w) hsum
      have hw : (0 : T) = w := by
        simpa [LinearMap.sum_apply, hzero] using hwSum
      exact hw0 hw.symm
    obtain ⟨j, hj⟩ := hdiag
    let z : T := C j j w
    have hz0 : z ≠ 0 := hj
    have hzZ : z ∈ Z := hstable j j w hwZ
    have hzfix : C j j z = z := by
      change (C j j * C j j) w = C j j w
      rw [hmul j j j j, if_pos rfl]
    let family : Fin n → T := fun i => C i j z
    have hfamilyZ : ∀ i, family i ∈ Z := fun i => hstable i j z hzZ
    have haction (k i : Fin n) :
        C j k (C i j z) = if k = i then z else 0 := by
      calc
        C j k (C i j z) = (C j k * C i j) z := rfl
        _ = (if k = i then C j j else 0) z :=
          congrArg (fun f : Module.End F T => f z) (hmul j k i j)
        _ = if k = i then z else 0 := by
          split_ifs
          · exact hzfix
          · rfl
    have hli : LinearIndependent F family := by
      rw [Fintype.linearIndependent_iff]
      intro a ha k
      have happ := congrArg (fun t : T => C j k t) ha
      have hcoeff : a k • z = 0 := by
        simpa [family, map_sum, haction] using happ
      exact (smul_eq_zero.mp hcoeff).resolve_right hz0
    have hspan : Submodule.span F (Set.range family) = ⊤ :=
      h_E002 F T n family hdim hli
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro t ⟨i, rfl⟩
    exact hfamilyZ i

theorem T017 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_T011 : ((∀ b : Module.Basis (Fin (lam.toNat + 1)) ℤ M,
    Reduction.IsBasisFamily (R := K) (fun i => (1 : K) ⊗ₜ[ℤ] b i)) ∧
  FiniteDimensional K (K ⊗[ℤ] M) ∧
  Module.finrank K (K ⊗[ℤ] M) = lam.toNat + 1 ∧ Nontrivial (K ⊗[ℤ] M)) ∧ ((∀ (a t : K) (z : M),
    a • (z ⊗ₜ[ℤ] t : Reduction.VK K M) = z ⊗ₜ[ℤ] (a * t)) ∧
  ∃ τ : Reduction.VK K M ≃ₗ[K] (K ⊗[ℤ] M),
    (∀ (z : M) (a : K), τ (z ⊗ₜ[ℤ] a) = a ⊗ₜ[ℤ] z) ∧
    (∀ (a : K) (z : M), τ.symm (a ⊗ₜ[ℤ] z) = z ⊗ₜ[ℤ] a) ∧
    (∀ (f : Module.End ℤ M) (z : Reduction.VK K M),
      τ (Reduction.originalAction K f z) = Reduction.Fext K f (τ z))) ∧
  FiniteDimensional K (Reduction.VK K M) ∧
  Module.finrank K (Reduction.VK K M) = lam.toNat + 1 ∧
  Nontrivial (Reduction.VK K M) ∧ ((∀ z : M, (A 1 z : V) = x (z : V)) ∧
  (∀ z : M, (B 1 z : V) = y (z : V)) ∧
  (∀ z : M, ((A 1 * B 1 - B 1 * A 1) z : V) = h (z : V)))) (h_T015 : (Nat.factorial lam.toNat : K) ≠ 0 ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B)) ∧ (∀ W : Submodule K (K ⊗[ℤ] M),
  Reduction.Stable W (Reduction.Fext K (A 1)) →
  Reduction.Stable W (Reduction.Fext K (B 1)) →
  ∀ i j : Fin (lam.toNat + 1), Reduction.Stable W (Reduction.U K lam.toNat A B i j))) (h_T016 : @YuiPortTypes.T016 p K instK lam V instVAdd instVModule instVFinite x y h v M A B) :
    Nontrivial (Reduction.VK K M) ∧
  ∀ W : Submodule K (Reduction.VK K M),
    Reduction.Stable W (Reduction.originalAction K (A 1)) →
    Reduction.Stable W (Reduction.originalAction K (B 1)) →
    Reduction.Stable W (Reduction.originalAction K (A 1 * B 1 - B 1 * A 1)) →
    W = ⊥ ∨ W = ⊤ := by
  rcases h_T011 with ⟨hQ, hbridge, hfd, hdim, hnontrivial, hrest⟩
  rcases hbridge.2 with ⟨τ, hτpure, hτsymm, hintertwine⟩
  letI : FiniteDimensional K (K ⊗[ℤ] M) := hQ.2.1
  refine ⟨hnontrivial, ?_⟩
  intro W hWA hWB hWH
  let Z : Submodule K (K ⊗[ℤ] M) := W.map τ.toLinearMap
  have transport (f : Module.End ℤ M)
      (hf : Reduction.Stable W (Reduction.originalAction K f)) :
      Reduction.Stable Z (Reduction.Fext K f) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    apply Submodule.mem_map.mpr
    exact ⟨Reduction.originalAction K f w, hf w hw, hintertwine f w⟩
  have hZA : Reduction.Stable Z (Reduction.Fext K (A 1)) :=
    transport (A 1) hWA
  have hZB : Reduction.Stable Z (Reduction.Fext K (B 1)) :=
    transport (B 1) hWB
  have hZU : ∀ i j : Fin (lam.toNat + 1),
      Reduction.Stable Z (Reduction.U K lam.toNat A B i j) :=
    h_T015.2.2 Z hZA hZB
  have hsimple : Z = ⊥ ∨ Z = ⊤ :=
    h_T016 K (K ⊗[ℤ] M) (lam.toNat + 1) (Nat.zero_lt_succ _) hQ.2.2.1
      (Reduction.U K lam.toNat A B) h_T015.2.1 Z hZU
  rcases hsimple with hbot | htop
  · left
    apply le_antisymm
    · intro w hw
      have hmem : τ w ∈ Z := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
      have heq : τ w = 0 := by simpa only [hbot, Submodule.mem_bot] using hmem
      have hwzero : w = 0 := τ.injective (heq.trans τ.map_zero.symm)
      simpa only [Submodule.mem_bot] using hwzero
    · exact bot_le
  · right
    apply top_unique
    intro w hw
    have hmem : τ w ∈ Z := by rw [htop]; exact Submodule.mem_top
    obtain ⟨w', hw', heq⟩ := Submodule.mem_map.mp hmem
    have heq' : w' = w := τ.injective heq
    exact heq' ▸ hw'

end Translation

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (ι : Type w) (f : Module.End ℂ V) (μ : ι → ℂ) (a : ι → V), Function.Injective μ → (∀ i, f.HasEigenvector (μ i) (a i)) → LinearIndependent ℂ a := by
  intro V _ _ ι f μ a hμ ha
  exact f.eigenvectors_linearIndependent' μ hμ a ha
set_option Elab.async false in
theorem B002 : ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (a : Fin n → V), Module.finrank K V = n → LinearIndependent K a → Submodule.span K (Set.range a) = ⊤ := by
  intro K _ V _ _ _ n a hd hi
  exact hi.span_eq_top_of_card_eq_finrank' (by simpa using hd.symm)
set_option Elab.async false in
theorem B003 : ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M) (K : Type u) [Field K], ∃ c : Module.Basis (Fin n) K (K ⊗[ℤ] M), ∀ i, c i = (1 : K) ⊗ₜ[ℤ] b i := by
  intro M _ _ n b K _
  refine ⟨b.baseChange K, ?_⟩
  intro i
  simp
set_option Elab.async false in
theorem B004 : ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (K : Type u) [Field K], ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M), ∀ (f : Module.End ℤ M) (a : K) (m : M), Φ f (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] f m := by
  intro M _ _ K _
  let Ψ : Module.End ℤ M →+* Module.End K (K ⊗[ℤ] M) :=
    { toFun := fun f => f.baseChange K
      map_one' := by simp
      map_mul' := by intro f g; exact LinearMap.baseChange_mul f g
      map_zero' := by simp
      map_add' := by intro f g; exact LinearMap.baseChange_add (A := K) f g }
  let Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M) :=
    { toRingHom := Ψ
      commutes' := by intro z; simp }
  refine ⟨Φ, ?_⟩
  intro f a m
  rfl
set_option Elab.async false in
theorem B005 : ∀ (K : Type u) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → IsUnit (Nat.factorial r : K) := by
  intro K _ p _ _ r hr
  exact (IsUnit.natCast_factorial_iff_of_charP p).2 hr
set_option Elab.async false in
theorem B006 : ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] (n : ℕ) (b : Module.Basis (Fin n) K V), Module.finrank K V = n := by
  intro K _ V _ _ n b
  simpa using Module.finrank_eq_card_basis b

end YuiBasis

namespace Translation
set_option autoImplicit false
private theorem __connected_T009 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    (∀ b : Module.Basis (Fin (lam.toNat + 1)) ℤ M,
    Reduction.IsBasisFamily (R := K) (fun i => (1 : K) ⊗ₜ[ℤ] b i)) ∧
  FiniteDimensional K (K ⊗[ℤ] M) ∧
  Module.finrank K (K ⊗[ℤ] M) = lam.toNat + 1 ∧ Nontrivial (K ⊗[ℤ] M) := by
  exact @T009 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@YuiBasis.B003.{u, v}) (@YuiBasis.B006.{0, v}) (@YuiBasis.B006.{u, max u v})

private theorem __connected_T010 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M)  :
    (∀ (a t : K) (z : M),
    a • (z ⊗ₜ[ℤ] t : Reduction.VK K M) = z ⊗ₜ[ℤ] (a * t)) ∧
  ∃ τ : Reduction.VK K M ≃ₗ[K] (K ⊗[ℤ] M),
    (∀ (z : M) (a : K), τ (z ⊗ₜ[ℤ] a) = a ⊗ₜ[ℤ] z) ∧
    (∀ (a : K) (z : M), τ.symm (a ⊗ₜ[ℤ] z) = z ⊗ₜ[ℤ] a) ∧
    (∀ (f : Module.End ℤ M) (z : Reduction.VK K M),
      τ (Reduction.originalAction K f z) = Reduction.Fext K f (τ z)) := by
  exact @T010 p K instK lam V instVAdd instVModule instVFinite x y h v M A B

private theorem __connected_T011 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    ((∀ b : Module.Basis (Fin (lam.toNat + 1)) ℤ M,
    Reduction.IsBasisFamily (R := K) (fun i => (1 : K) ⊗ₜ[ℤ] b i)) ∧
  FiniteDimensional K (K ⊗[ℤ] M) ∧
  Module.finrank K (K ⊗[ℤ] M) = lam.toNat + 1 ∧ Nontrivial (K ⊗[ℤ] M)) ∧ ((∀ (a t : K) (z : M),
    a • (z ⊗ₜ[ℤ] t : Reduction.VK K M) = z ⊗ₜ[ℤ] (a * t)) ∧
  ∃ τ : Reduction.VK K M ≃ₗ[K] (K ⊗[ℤ] M),
    (∀ (z : M) (a : K), τ (z ⊗ₜ[ℤ] a) = a ⊗ₜ[ℤ] z) ∧
    (∀ (a : K) (z : M), τ.symm (a ⊗ₜ[ℤ] z) = z ⊗ₜ[ℤ] a) ∧
    (∀ (f : Module.End ℤ M) (z : Reduction.VK K M),
      τ (Reduction.originalAction K f z) = Reduction.Fext K f (τ z))) ∧
  FiniteDimensional K (Reduction.VK K M) ∧
  Module.finrank K (Reduction.VK K M) = lam.toNat + 1 ∧
  Nontrivial (Reduction.VK K M) ∧ ((∀ z : M, (A 1 z : V) = x (z : V)) ∧
  (∀ z : M, (B 1 z : V) = y (z : V)) ∧
  (∀ z : M, ((A 1 * B 1 - B 1 * A 1) z : V) = h (z : V))) := by
  exact @T011 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T009 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@__connected_T010 p K instK lam V instVAdd instVModule instVFinite x y h v M A B)

private theorem __connected_T001 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    ∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v) := by
  exact @T001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001

private theorem __connected_T002 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v) := by
  exact @T002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001)

private theorem __connected_T003 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    (∀ t : ℕ, h ((y ^ t) v) = ((lam.toNat : ℤ) - 2 * (t : ℤ) : ℂ) • ((y ^ t) v)) ∧ (∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
  ((t : ℂ) * ((lam.toNat : ℤ) - (t : ℤ) + 1 : ℂ)) • ((y ^ (t - 1)) v)) ∧ ((∀ t : ℕ, t ≤ lam.toNat →
  (x ^ t) ((y ^ t) v) =
    ((Nat.factorial t : ℂ) * ∏ a ∈ Finset.range t, ((lam.toNat : ℤ) - (a : ℤ) : ℂ)) • v ∧
  (x ^ t) ((y ^ t) v) ≠ 0) ∧
  (∀ i : Fin (lam.toNat + 1), Reduction.e lam y v i ≠ 0 ∧
    h (Reduction.e lam y v i) = ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i)) ∧
  Function.Injective (fun i : Fin (lam.toNat + 1) => ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ))) := by
  exact @T003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T001 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@__connected_T002 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001)

private theorem __connected_T004 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v) := by
  exact @T004 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@YuiBasis.B001.{v, 0}) (@YuiBasis.B002.{0, v})

private theorem __connected_T005 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ (((y ^ (lam.toNat + 1)) v = 0) ∧
  (∀ t : ℕ, lam.toNat + 1 ≤ t → (y ^ t) v = 0)) ∧ ((x (Reduction.e lam y v ⟨0, Nat.zero_lt_succ lam.toNat⟩) = 0) ∧
  (∀ (i : Fin (lam.toNat + 1)) (hi : 1 ≤ i.val),
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - 1 →
    x (Reduction.e lam y v i) = ((lam.toNat : ℤ) - (i.val : ℤ) + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (i : Fin (lam.toNat + 1)), i.val < lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + 1 →
    y (Reduction.e lam y v i) = (i.val + 1 : ℂ) • (Reduction.e lam y v j)) ∧
  y (Reduction.e lam y v ⟨lam.toNat, Nat.lt_succ_self lam.toNat⟩) = 0 ∧
  (∀ i : Fin (lam.toNat + 1), h (Reduction.e lam y v i) =
    ((lam.toNat : ℤ) - 2 * (i.val : ℤ) : ℂ) • (Reduction.e lam y v i))) := by
  exact @T005 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T003 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@__connected_T004 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001)

private theorem __connected_T006 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    (Reduction.IsBasisFamily (R := ℂ) (Reduction.e lam y v)) ∧ ((∀ (r : ℕ) (i : Fin (lam.toNat + 1)), r ≤ i.val →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val - r →
    Reduction.dp x r (Reduction.e lam y v i) = (Nat.choose (lam.toNat - i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val < r → Reduction.dp x r (Reduction.e lam y v i) = 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), i.val + r ≤ lam.toNat →
    ∀ j : Fin (lam.toNat + 1), j.val = i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = (Nat.choose (i.val + r) r : ℂ) • (Reduction.e lam y v j)) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)), lam.toNat < i.val + r →
    Reduction.dp y r (Reduction.e lam y v i) = 0)) := by
  exact @T006 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T005 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@YuiBasis.B001.{v, 0}) (@YuiBasis.B002.{0, v})

private theorem __connected_T007 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    ∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0 := by
  exact @T007 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T006 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001)

private theorem __connected_T008 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    (∀ i j k : Fin (lam.toNat + 1),
  Reduction.ComplexScaled lam.toNat x y i j (Reduction.e lam y v k) =
    if k = j then (Nat.factorial lam.toNat : ℂ) • (Reduction.e lam y v i) else 0) ∧ (∀ (i j : Fin (lam.toNat + 1)) (z : M),
  (Reduction.Scaled lam.toNat A B i j z : V) =
    Reduction.ComplexScaled lam.toNat x y i j (z : V)) ∧ ((∀ i j k l : Fin (lam.toNat + 1),
    Reduction.Scaled lam.toNat A B i j * Reduction.Scaled lam.toNat A B k l =
    if j = k then (Nat.factorial lam.toNat : ℤ) • Reduction.Scaled lam.toNat A B i l else 0) ∧
  (∑ i : Fin (lam.toNat + 1), Reduction.Scaled lam.toNat A B i i) =
    (Nat.factorial lam.toNat : ℤ) • (1 : Module.End ℤ M)) ∧ (∀ r : ℕ, (Nat.factorial r : ℤ) • A r = A 1 ^ r ∧
  (Nat.factorial r : ℤ) • B r = B 1 ^ r) := by
  exact @T008 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T006 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@__connected_T007 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001)

private theorem __connected_T012 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M)  :
    ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f := by
  exact @T012 p K instK lam V instVAdd instVModule instVFinite x y h v M A B (@YuiBasis.B004.{u, v})

private theorem __connected_T013 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    ∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0 := by
  exact @T013 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@YuiBasis.B005.{u})

private theorem __connected_T014 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    (∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M),
  ∀ f : Module.End ℤ M, Φ f = Reduction.Fext K f) ∧ (∀ r : ℕ, r ≤ lam.toNat →
  IsUnit (Nat.factorial r : K) ∧ (Nat.factorial r : K) ≠ 0) ∧ (Nat.factorial lam.toNat : K) ≠ 0 ∧
  (∀ r : ℕ, r ≤ lam.toNat →
  (Nat.factorial r : K) • Reduction.Fext K (A r) = Reduction.Fext K (A 1) ^ r ∧
  (Nat.factorial r : K) • Reduction.Fext K (B r) = Reduction.Fext K (B 1) ^ r) ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B)) := by
  exact @T014 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T008 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@__connected_T012 p K instK lam V instVAdd instVModule instVFinite x y h v M A B) (@__connected_T013 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001)

private theorem __connected_T015 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    (Nat.factorial lam.toNat : K) ≠ 0 ∧ (Reduction.MatrixUnits (lam.toNat + 1) (Reduction.U K lam.toNat A B)) ∧ (∀ W : Submodule K (K ⊗[ℤ] M),
  Reduction.Stable W (Reduction.Fext K (A 1)) →
  Reduction.Stable W (Reduction.Fext K (B 1)) →
  ∀ i j : Fin (lam.toNat + 1), Reduction.Stable W (Reduction.U K lam.toNat A B i j)) := by
  exact @T015 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T014 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@YuiBasis.B004.{u, v}) (@YuiBasis.B005.{u})

private theorem __connected_T016 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M)  :
    ∀ (F : Type u) [Field F] (T : Type (max u v)) [AddCommGroup T] [Module F T]
  [FiniteDimensional F T] (n : ℕ), 0 < n → Module.finrank F T = n →
  ∀ C : Fin n → Fin n → Module.End F T, Reduction.MatrixUnits n C →
  ∀ Z : Submodule F T, (∀ i j, Reduction.Stable Z (C i j)) → Z = ⊥ ∨ Z = ⊤ := by
  exact @T016 p K instK lam V instVAdd instVModule instVFinite x y h v M A B (@YuiBasis.B002.{u, max u v})

private theorem __connected_T017 (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) :
    Nontrivial (Reduction.VK K M) ∧
  ∀ W : Submodule K (Reduction.VK K M),
    Reduction.Stable W (Reduction.originalAction K (A 1)) →
    Reduction.Stable W (Reduction.originalAction K (B 1)) →
    Reduction.Stable W (Reduction.originalAction K (A 1 * B 1 - B 1 * A 1)) →
    W = ⊥ ∨ W = ⊤ := by
  exact @T017 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001 (@__connected_T011 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@__connected_T015 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001) (@__connected_T016 p K instK lam V instVAdd instVModule instVFinite x y h v M A B)

theorem P (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_E001 : ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (ι : Type w) (f : Module.End ℂ V) (μ : ι → ℂ) (a : ι → V), Function.Injective μ → (∀ i, f.HasEigenvector (μ i) (a i)) → LinearIndependent ℂ a) (h_E002 : ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (a : Fin n → V), Module.finrank K V = n → LinearIndependent K a → Submodule.span K (Set.range a) = ⊤) (h_E003 : ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M) (K : Type u) [Field K], ∃ c : Module.Basis (Fin n) K (K ⊗[ℤ] M), ∀ i, c i = (1 : K) ⊗ₜ[ℤ] b i) (h_E004 : ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (K : Type u) [Field K], ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M), ∀ (f : Module.End ℤ M) (a : K) (m : M), Φ f (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] f m) (h_E005 : ∀ (K : Type u) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → IsUnit (Nat.factorial r : K)) (h_E006 : ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] (n : ℕ) (b : Module.Basis (Fin n) K V), Module.finrank K V = n) : Nontrivial (Reduction.VK K M) ∧
  ∀ W : Submodule K (Reduction.VK K M),
    Reduction.Stable W (Reduction.originalAction K (A 1)) →
    Reduction.Stable W (Reduction.originalAction K (B 1)) →
    Reduction.Stable W (Reduction.originalAction K (A 1 * B 1 - B 1 * A 1)) →
    W = ⊥ ∨ W = ⊤ := by
  exact @__connected_T017 p K instK lam V instVAdd instVModule instVFinite x y h v M A B h_H001

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
/- Instantiate only universes that disappear when checked E proofs replace
   premises. Public levels are inferred from the actual arguments/target.
   This elaborator builds an ordinary application, checked by Lean's kernel;
   it adds no theorem, axiom or proof dependency. -/
open Lean Elab Term in
elab "yui_assembly_declared_levels%" : term => do
  return toExpr (← getLevelNames)

-- Capture only the header's explicitly declared levels, before P introduces
-- auto-generated Type* names. Those names can shift after E is removed.
private def yuiAssemblyDeclaredLevels : List Lean.Name := yui_assembly_declared_levels%

open Lean Meta Elab Term in
elab "yui_assembly_export%" "(" args:term,* ")" : term <= expectedType => do
  let info ← getConstInfo `Translation.P
  let used ← forallTelescope info.type fun xs body => do
    let mut retained := #[]
    let omitted : Array String := #[]
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
    else if yuiAssemblyDeclaredLevels.contains name then pure (Level.param name)
    else mkFreshLevelMVar
  elabAppArgs (mkConst `Translation.P levels) #[] (args.getElems.map Arg.stx)
    expectedType (explicit := true) (ellipsis := false)

set_option Elab.async false in
theorem P (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) (h_E001 : ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (ι : Type w) (f : Module.End ℂ V) (μ : ι → ℂ) (a : ι → V), Function.Injective μ → (∀ i, f.HasEigenvector (μ i) (a i)) → LinearIndependent ℂ a) (h_E002 : ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (a : Fin n → V), Module.finrank K V = n → LinearIndependent K a → Submodule.span K (Set.range a) = ⊤) (h_E003 : ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M) (K : Type u) [Field K], ∃ c : Module.Basis (Fin n) K (K ⊗[ℤ] M), ∀ i, c i = (1 : K) ⊗ₜ[ℤ] b i) (h_E004 : ∀ (M : Type v) [AddCommGroup M] [Module ℤ M] (K : Type u) [Field K], ∃ Φ : Module.End ℤ M →ₐ[ℤ] Module.End K (K ⊗[ℤ] M), ∀ (f : Module.End ℤ M) (a : K) (m : M), Φ f (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] f m) (h_E005 : ∀ (K : Type u) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → IsUnit (Nat.factorial r : K)) (h_E006 : ∀ (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V] (n : ℕ) (b : Module.Basis (Fin n) K V), Module.finrank K V = n) : Nontrivial (Reduction.VK K M) ∧
  ∀ W : Submodule K (Reduction.VK K M),
    Reduction.Stable W (Reduction.originalAction K (A 1)) →
    Reduction.Stable W (Reduction.originalAction K (B 1)) →
    Reduction.Stable W (Reduction.originalAction K (A 1 * B 1 - B 1 * A 1)) →
    W = ⊥ ∨ W = ⊤ := by
  exact yui_assembly_export%(p, K, instK, lam, V, instVAdd, instVModule, instVFinite, x, y, h, v, M, A, B, h_H001, h_E001, h_E002, h_E003, h_E004, h_E005, h_E006)

end AuditBExport

open Lean Meta Elab Command in
run_cmd do
  let result ← liftTermElabM do
    let info ← getConstInfo `Translation.P
    forallTelescope info.type fun xs body => do
      let mut retained := #[]
      let omitted : Array String := #[]
      for x in xs do
        let decl ← getFVarLocalDecl x
        if !omitted.contains decl.userName.toString then
          retained := retained.push x
      let exported ← mkForallFVars retained body
      let used := (collectLevelParams {} exported).params.toList
      return Json.mkObj [("parameters", toJson (info.levelParams.map Name.toString)),
        ("export_used_parameters", toJson (used.map Name.toString))]
  logInfo m!"YUI_ASSEMBLY_LEVELS_JSON:{result.compress}"


namespace YuiBasis
set_option autoImplicit false

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
    let omitted : Array String := #["h_E001", "h_E002", "h_E003", "h_E004", "h_E005", "h_E006"]
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
theorem P (p : ℕ) (K : Type u) [instK : Field K] (lam : ℤ) (V : Type v) [instVAdd : AddCommGroup V] [instVModule : Module ℂ V] [instVFinite : FiniteDimensional ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (A : ℕ → Module.End ℤ M) (B : ℕ → Module.End ℤ M) (h_H001 : Reduction.Standing p K lam V x y h v M A B) : Nontrivial (Reduction.VK K M) ∧
  ∀ W : Submodule K (Reduction.VK K M),
    Reduction.Stable W (Reduction.originalAction K (A 1)) →
    Reduction.Stable W (Reduction.originalAction K (B 1)) →
    Reduction.Stable W (Reduction.originalAction K (A 1 * B 1 - B 1 * A 1)) →
    W = ⊥ ∨ W = ⊤ := by
  exact yui_basis_export%(p, K, instK, lam, V, instVAdd, instVModule, instVFinite, x, y, h, v, M, A, B, h_H001, (@YuiBasis.B001), (@YuiBasis.B002), (@YuiBasis.B003), (@YuiBasis.B004), (@YuiBasis.B005), (@YuiBasis.B006))

end YuiClosed
