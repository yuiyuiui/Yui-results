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
theorem checked (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∃ ρ : Chevalley.R p →+* K, ∀ a : ℤ, ρ (a : Chevalley.R p) = (a : K)" := by
  classical
  letI : CharP K p := h_H001.2.1
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp h_H001.1
  let S : Submonoid ℤ := {
    carrier := {b | ¬ (p : ℤ) ∣ b}
    one_mem' := hp.not_dvd_one
    mul_mem' := fun ha hb => hp.not_dvd_mul ha hb }
  have hfrac (r : Chevalley.R p) :
      ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ r * (b : Chevalley.R p) = (a : Chevalley.R p) := by
    obtain ⟨a,b,hb,hr⟩ := h_T006.1.1 (r : ℚ) |>.mp r.property
    have hb0 : (b : ℚ) ≠ 0 := by
      exact_mod_cast (fun h : b = 0 => hb (h ▸ dvd_zero _))
    refine ⟨a,b,hb,?_⟩
    apply Subtype.ext
    change (r : ℚ) * (b : ℚ) = (a : ℚ)
    rw [hr, div_mul_cancel₀ _ hb0]
  letI : IsLocalization S (Chevalley.R p) := by
    apply (isLocalization_iff S (Chevalley.R p)).2
    refine ⟨?_, ?_, ?_⟩
    · intro b
      have hb0 : (b.val : ℚ) ≠ 0 := by
        exact_mod_cast (fun h : b.val = 0 => b.property (h ▸ dvd_zero _))
      let bi : Chevalley.R p := ⟨(b.val : ℚ)⁻¹,
        Algebra.subset_adjoin ⟨b.val,b.property,rfl⟩⟩
      apply isUnit_iff_exists_inv.mpr
      refine ⟨bi, ?_⟩
      apply Subtype.ext
      exact mul_inv_cancel₀ hb0
    · intro r
      obtain ⟨a,b,hb,hr⟩ := hfrac r
      exact ⟨(a,⟨b,hb⟩),hr⟩
    · intro a b hab
      refine ⟨1, ?_⟩
      have : a = b := by
        have hq : (a : ℚ) = (b : ℚ) := congrArg Subtype.val hab
        exact_mod_cast hq
      simp [this]
  have hu (b : S) : IsUnit ((Int.castRingHom K) b.val) := by
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => b.property ((CharP.intCast_eq_zero_iff K p b.val).mp hz)
  refine ⟨IsLocalization.lift (S := Chevalley.R p) hu, ?_⟩
  intro a
  exact IsLocalization.lift_eq hu a
#check @checked
#print axioms checked
end YuiAuxiliary
