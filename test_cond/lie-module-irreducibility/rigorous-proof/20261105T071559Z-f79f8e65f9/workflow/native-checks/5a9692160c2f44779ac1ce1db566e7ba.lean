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
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (f : Module.End ℂ V) (hf : Chevalley.preserves M f) (m : M), ((Chevalley.latticeOp M f) m : V) = f m" := by
  intro f hf m
  unfold Chevalley.latticeOp
  split
  · rfl
  · contradiction

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (f : Module.End ℂ V), Chevalley.preserves M f → ∀ u : Chevalley.MR p M, Chevalley.mu p M (((Chevalley.latticeOp M f).baseChange (Chevalley.R p)) u) = f (Chevalley.mu p M u)" := by
  intro f hf u
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V := IsScalarTower.of_compHom (Chevalley.R p) ℂ V
  change (Chevalley.muR p M) (((Chevalley.latticeOp M f).baseChange (Chevalley.R p)) u) = f ((Chevalley.muR p M) u)
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change a • (((Chevalley.latticeOp M f) m : M) : V) = f (a • (m : V))
    rw [@yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 f hf m]
    exact (f.map_smul_of_tower a (m : V)).symm
  | add u w hu hw => simp [hu, hw]

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (ρ : Chevalley.R p →+* K),\n  letI := ρ.toAlgebra\n  ∀ (Φ : Chevalley.VK K M ≃ₗ[K] (K ⊗[Chevalley.R p] Chevalley.MR p M)),\n  (∀ (c : K) (m : M), Φ (c ⊗ₜ[ℤ] m) = c ⊗ₜ[Chevalley.R p] ((1 : Chevalley.R p) ⊗ₜ[ℤ] m)) →\n  ∀ (F : Module.End ℤ M) (w : Chevalley.VK K M),\n  Φ (F.baseChange K w) = ((F.baseChange (Chevalley.R p)).baseChange K) (Φ w)" := by
  intro ρ
  letI := ρ.toAlgebra
  intro Φ hΦ F w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c m => simp [hΦ]
  | add u w hu hw => simp [hu, hw]

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (ρ : Chevalley.R p →+* K),\n  letI := ρ.toAlgebra\n  ∀ (Φ : Chevalley.VK K M ≃ₗ[K] (K ⊗[Chevalley.R p] Chevalley.MR p M)),\n  (∀ (c : K) (m : M), Φ (c ⊗ₜ[ℤ] m) = c ⊗ₜ[Chevalley.R p] ((1 : Chevalley.R p) ⊗ₜ[ℤ] m)) →\n  ∀ (F : Module.End ℤ M) (u w : Chevalley.MR p M) (z : ℤ),\n  (F.baseChange (Chevalley.R p)) u = z • w →\n  F.baseChange K (Φ.symm (1 ⊗ₜ[Chevalley.R p] u)) = (z : K) • Φ.symm (1 ⊗ₜ[Chevalley.R p] w)" := by
  intro ρ
  letI := ρ.toAlgebra
  intro Φ hΦ F u w z heq
  apply Φ.injective
  rw [@yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 ρ Φ hΦ]
  simp [heq, TensorProduct.tmul_smul, Int.cast_smul_eq_zsmul]

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (ρ : Chevalley.R p →+* K),\n  letI := ρ.toAlgebra\n  ∀ (Φ : Chevalley.VK K M ≃ₗ[K] (K ⊗[Chevalley.R p] Chevalley.MR p M)),\n  (∀ (c : K) (m : M), Φ (c ⊗ₜ[ℤ] m) = c ⊗ₜ[Chevalley.R p] ((1 : Chevalley.R p) ⊗ₜ[ℤ] m)) →\n  ∀ (F : Module.End ℤ M) (u w : Chevalley.MR p M) (z : ℤ),\n  Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = (z : ℂ) • Chevalley.mu p M w →\n  F.baseChange K (Φ.symm (1 ⊗ₜ[Chevalley.R p] u)) = (z : K) • Φ.symm (1 ⊗ₜ[Chevalley.R p] w)" := by
  intro ρ
  letI := ρ.toAlgebra
  intro Φ hΦ F u w z heq
  apply @yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 ρ Φ hΦ F u w z
  apply h_T006.1.2.1
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  change Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = (Chevalley.muR p M) (z • w)
  rw [map_zsmul]
  exact heq.trans (Int.cast_smul_eq_zsmul ℂ z (Chevalley.mu p M w))

theorem yui_aux_0006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∃ β : Module.Basis (Chevalley.Index ell) K (Chevalley.VK K M),\n ∀ (F : Module.End ℤ M) (f : Module.End ℂ V),\n (∀ u : Chevalley.MR p M, Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u)) →\n ∀ (i j : Chevalley.Index ell) (z : ℤ),\n f (Chevalley.e y v i.val) = (z : ℂ) • Chevalley.e y v j.val →\n F.baseChange K (β i) = (z : K) • β j" := by
  classical
  have h12 := h_T012
  have h13 := h_T013
  rcases h12 with ⟨b, hb, hb0, hJ, him, B, hB⟩
  rcases h13 with ⟨hc, ρ, hρ, Φ, hΦ, Ψ, hΨ⟩
  letI := ρ.toAlgebra
  let β := (B.baseChange K).map Φ.symm
  refine ⟨β, ?_⟩
  intro F f hF i j z heq
  change F.baseChange K (Φ.symm ((B.baseChange K) i)) = (z : K) • Φ.symm ((B.baseChange K) j)
  simp only [Module.Basis.baseChange_apply]
  apply @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 ρ Φ hΦ F (B i) (B j) z
  rw [hF, (hB i).1, (hB j).1, map_smul, heq]
  exact smul_comm b (z : ℂ) (Chevalley.e y v j.val)

theorem yui_aux_0007 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ β : Module.Basis (Chevalley.Index ell) K (Chevalley.VK K M),\n (∀ (F : Module.End ℤ M) (f : Module.End ℂ V),\n (∀ u : Chevalley.MR p M, Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u)) →\n ∀ (i j : Chevalley.Index ell) (z : ℤ),\n f (Chevalley.e y v i.val) = (z : ℂ) • Chevalley.e y v j.val →\n F.baseChange K (β i) = (z : K) • β j) → Chevalley.stringActions ell (Chevalley.opK K M x) (Chevalley.opK K M y) (Chevalley.opK K M h) (Chevalley.basisVec β) ∧\n Chevalley.dividedActions ell (fun r => Chevalley.opK K M (Chevalley.dp x r)) (fun r => Chevalley.opK K M (Chevalley.dp y r)) (Chevalley.basisVec β)" := by
  classical
  intro β tr
  have trans (F : Module.End ℤ M) (f : Module.End ℂ V)
      (hf : ∀ u : Chevalley.MR p M, Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u))
      (i j : ℕ) (hi : i ≤ ell.toNat) (hj : j ≤ ell.toNat) (z : ℤ)
      (he : f (Chevalley.e y v i) = (z : ℂ) • Chevalley.e y v j) :
      F.baseChange K (Chevalley.basisVec β i) = (z : K) • Chevalley.basisVec β j := by
    simpa [Chevalley.basisVec, Nat.lt_succ_iff.mpr hi, Nat.lt_succ_iff.mpr hj] using
      tr F f hf ⟨i, Nat.lt_succ_iff.mpr hi⟩ ⟨j, Nat.lt_succ_iff.mpr hj⟩ z he
  have trans0 (F : Module.End ℤ M) (f : Module.End ℂ V)
      (hf : ∀ u : Chevalley.MR p M, Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u))
      (i : ℕ) (hi : i ≤ ell.toNat) (he : f (Chevalley.e y v i) = 0) :
      F.baseChange K (Chevalley.basisVec β i) = 0 := by
    simpa [Chevalley.opK] using trans F f hf i i hi hi 0 (by simpa using he)
  have hx := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 x h_T006.1.2.2.2.2.2.1
  have hy := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 y h_T006.1.2.2.2.2.2.2.1
  have hh := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 h h_T006.1.2.2.2.2.2.2.2.1
  have hd := h_T006.1.2.2.2.2.2.2.2.2
  have hs := h_T004.2.2.2.2.2.2.1
  have ha := h_T004.2.2.2.2.2.2.2
  constructor
  · intro i hi
    rcases hs i hi with ⟨hxi, hyi, hhi⟩
    refine ⟨?_, ?_, ?_⟩
    · by_cases hz : i = 0
      · simp only [hz, if_pos rfl] at hxi ⊢
        exact trans0 _ _ hx 0 (by omega) hxi
      · simp only [if_neg hz] at hxi ⊢
        exact trans _ _ hx i (i-1) hi (by omega) (ell - (i : ℤ) + 1) hxi
    · by_cases ht : i < ell.toNat
      · simp only [if_pos ht] at hyi ⊢
        simpa [Chevalley.opK] using trans _ _ hy i (i+1) hi (by omega) ((i+1 : ℕ) : ℤ) (by simpa using hyi)
      · simp only [if_neg ht] at hyi ⊢
        exact trans0 _ _ hy i hi hyi
    · exact trans _ _ hh i i hi hi (ell - 2 * (i : ℤ)) hhi
  · intro r i hi
    rcases ha r i hi with ⟨hxi, hyi⟩
    constructor
    · by_cases ht : r ≤ i
      · simp only [if_pos ht] at hxi ⊢
        simpa [Chevalley.opK] using trans _ _ (fun u => (hd r u).1) i (i-r) hi (by omega)
          ((Nat.choose (ell.toNat-i+r) r : ℕ) : ℤ) (by simpa using hxi)
      · simp only [if_neg ht] at hxi ⊢
        exact trans0 _ _ (fun u => (hd r u).1) i hi hxi
    · by_cases ht : i+r ≤ ell.toNat
      · simp only [if_pos ht] at hyi ⊢
        simpa [Chevalley.opK] using trans _ _ (fun u => (hd r u).2) i (i+r) hi ht
          ((Nat.choose (i+r) r : ℕ) : ℤ) (by simpa using hyi)
      · simp only [if_neg ht] at hyi ⊢
        exact trans0 _ _ (fun u => (hd r u).2) i hi hyi

theorem yui_aux_0008 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (F G : Module.End ℤ M),\n (∀ u : Chevalley.MR p M, Chevalley.mu p M (F.baseChange (Chevalley.R p) u) =\n   Chevalley.mu p M (G.baseChange (Chevalley.R p) u)) →\n F.baseChange K = G.baseChange K" := by
  intro F G heq
  have hfg : F.baseChange (Chevalley.R p) = G.baseChange (Chevalley.R p) := by
    apply LinearMap.ext
    intro u
    exact h_T006.1.2.1 (heq u)
  have h13 := h_T013
  rcases h13 with ⟨hc, ρ, hρ, Φ, hΦ, Ψ, hΨ⟩
  letI := ρ.toAlgebra
  apply LinearMap.ext
  intro w
  apply Φ.injective
  rw [@yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 ρ Φ hΦ,
    @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 ρ Φ hΦ, hfg]

theorem yui_aux_0009 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (F : Module.End ℤ M) (f : Module.End ℂ V),\n (∀ u : Chevalley.MR p M, Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u)) →\n ∀ (r : ℕ) (u : Chevalley.MR p M),\n Chevalley.mu p M ((F ^ r).baseChange (Chevalley.R p) u) = (f ^ r) (Chevalley.mu p M u)" := by
  intro F f hF r
  induction r with
  | zero => intro u; simp
  | succ r ih =>
    intro u
    rw [pow_succ, LinearMap.baseChange_mul]
    change Chevalley.mu p M ((F ^ r).baseChange (Chevalley.R p) (F.baseChange (Chevalley.R p) u)) = _
    rw [ih, hF]
    rfl

theorem yui_aux_0010 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (F : Module.End ℤ M) (r : ℕ),\n (F ^ r).baseChange K = (F.baseChange K) ^ r" := by
  intro F r
  exact (Module.End.baseChangeHom ℤ K M).map_pow F r

theorem yui_aux_0011 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (n : ℕ) (F : Module.End K (Chevalley.VK K M)), (n : ℤ) • F = (n : K) • F" := by
  intro n F
  rw [← Int.cast_smul_eq_zsmul K, Int.cast_natCast]

theorem yui_aux_0012 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (f : Module.End ℂ V),\n (∀ u : Chevalley.MR p M, Chevalley.mu p M ((Chevalley.latticeOp M f).baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u)) →\n (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M ((Chevalley.latticeOp M (Chevalley.dp f r)).baseChange (Chevalley.R p) u) = Chevalley.dp f r (Chevalley.mu p M u)) →\n ∀ (r : ℕ), (r.factorial : K) ≠ 0 →\n Chevalley.opK K M (Chevalley.dp f r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M f ^ r" := by
  intro f hf hd r hr
  have he : (((r.factorial : ℤ) • Chevalley.latticeOp M (Chevalley.dp f r))).baseChange K =
      ((Chevalley.latticeOp M f) ^ r).baseChange K := by
    apply @yui_aux_0008 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013
    intro u
    rw [@yui_aux_0009 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 _ f hf]
    rw [LinearMap.baseChange_smul, LinearMap.smul_apply]
    letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
    change (Chevalley.muR p M) ((r.factorial : ℤ) • _) = _
    rw [map_zsmul]
    change (r.factorial : ℤ) • Chevalley.mu p M ((Chevalley.latticeOp M (Chevalley.dp f r)).baseChange (Chevalley.R p) u) = _
    rw [hd, ← Int.cast_smul_eq_zsmul ℂ]
    simp [Chevalley.dp, smul_smul, Nat.factorial_ne_zero]
  have he' : (r.factorial : K) • Chevalley.opK K M (Chevalley.dp f r) = Chevalley.opK K M f ^ r := by
    simpa only [LinearMap.baseChange_smul,
      @yui_aux_0010 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013,
      @yui_aux_0011 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013, Chevalley.opK] using he
  rw [← he', smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem yui_aux_0013 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ r : ℕ, r ≤ ell.toNat → (r.factorial : K) ≠ 0 ∧ Chevalley.opK K M (Chevalley.dp x r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M x ^ r ∧ Chevalley.opK K M (Chevalley.dp y r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M y ^ r" := by
  intro r hr
  letI : CharP K p := h_H001.2.1
  have hn : (r.factorial : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p, h_H001.1.dvd_factorial, not_le]
    omega
  have hx := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 x h_T006.1.2.2.2.2.2.1
  have hy := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 y h_T006.1.2.2.2.2.2.2.1
  have hd := h_T006.1.2.2.2.2.2.2.2.2
  refine ⟨hn, ?_, ?_⟩
  · exact @yui_aux_0012 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 x hx (fun r u => (hd r u).1) r hn
  · exact @yui_aux_0012 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 y hy (fun r u => (hd r u).2) r hn

theorem yui_aux_0014 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ β : Module.Basis (Chevalley.Index ell) K (Chevalley.VK K M),\n (∀ (F : Module.End ℤ M) (f : Module.End ℂ V),\n (∀ u : Chevalley.MR p M, Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u)) →\n ∀ (i j : Chevalley.Index ell) (z : ℤ),\n f (Chevalley.e y v i.val) = (z : ℂ) • Chevalley.e y v j.val →\n F.baseChange K (β i) = (z : K) • β j) → ∀ i j : Chevalley.Index ell, (Nat.choose ell.toNat j.val : K) ≠ 0 ∧ Chevalley.matrixK K ell M x y i j = Chevalley.unitOp β i j" := by
  classical
  intro β tr i j
  obtain ⟨b, hb⟩ := h_T004.2.2.2.2.1
  have hunit := (h_T006.2 b hb i j).1
  have hnC : (Nat.choose ell.toNat j.val : ℂ) ≠ 0 := by
    simpa only [map_natCast] using (hunit.map (algebraMap (Chevalley.R p) ℂ)).ne_zero
  have hnK : (Nat.choose ell.toNat j.val : K) ≠ 0 := by
    obtain ⟨hc, ρ, hρ, hrest⟩ := h_T013
    simpa only [map_natCast] using (hunit.map ρ).ne_zero
  refine ⟨hnK, ?_⟩
  let F : Module.End ℤ M :=
    Chevalley.latticeOp M (Chevalley.dp x (ell.toNat - i.val)) *
      (Chevalley.latticeOp M (Chevalley.dp y ell.toNat) * Chevalley.latticeOp M (Chevalley.dp x ell.toNat)) *
        Chevalley.latticeOp M (Chevalley.dp y (ell.toNat - j.val))
  let f : Module.End ℂ V :=
    Chevalley.dp x (ell.toNat - i.val) *
      (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) *
        Chevalley.dp y (ell.toNat - j.val)
  have hdx := fun r u => (h_T006.1.2.2.2.2.2.2.2.2 r u).1
  have hdy := fun r u => (h_T006.1.2.2.2.2.2.2.2.2 r u).2
  have hinter : ∀ u : Chevalley.MR p M,
      Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = f (Chevalley.mu p M u) := by
    intro u
    simp only [F, f, LinearMap.baseChange_mul, Module.End.mul_apply, hdx, hdy]
  have hmat : f = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b i j := by
    rw [(h_T006.2 b hb i j).2.2.2.2.1, smul_smul, mul_inv_cancel₀ hnC, one_smul]
  have hFK : F.baseChange K = (Nat.choose ell.toNat j.val : K) • Chevalley.unitOp β i j := by
    apply β.ext
    intro k
    by_cases hk : k = j
    · subst k
      have he : f (Chevalley.e y v j.val) = (((Nat.choose ell.toNat j.val : ℕ) : ℤ) : ℂ) • (Chevalley.e y v i.val) := by
        rw [← hb j, ← hb i, hmat]
        simp [Chevalley.unitOp]
      have ht := tr F f hinter j i ((Nat.choose ell.toNat j.val : ℕ) : ℤ) he
      simpa [Chevalley.unitOp] using ht
    · have he : f (Chevalley.e y v k.val) = (0 : ℂ) • Chevalley.e y v i.val := by
        rw [← hb k, hmat]
        simp [Chevalley.unitOp, hk]
      have ht := tr F f hinter k i 0 (by simpa using he)
      simpa [Chevalley.unitOp, hk] using ht
  change (Nat.choose ell.toNat j.val : K)⁻¹ •
      (Chevalley.opK K M (Chevalley.dp x (ell.toNat-i.val)) *
        (Chevalley.opK K M (Chevalley.dp y ell.toNat) * Chevalley.opK K M (Chevalley.dp x ell.toNat)) *
          Chevalley.opK K M (Chevalley.dp y (ell.toNat-j.val))) = _
  have hprod : Chevalley.opK K M (Chevalley.dp x (ell.toNat-i.val)) *
        (Chevalley.opK K M (Chevalley.dp y ell.toNat) * Chevalley.opK K M (Chevalley.dp x ell.toNat)) *
          Chevalley.opK K M (Chevalley.dp y (ell.toNat-j.val)) = F.baseChange K := by
    simp only [F, Chevalley.opK, LinearMap.baseChange_mul]
  rw [hprod, hFK, smul_smul, inv_mul_cancel₀ hnK, one_smul]

theorem checked (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → ∀ i j, Chevalley.stable W (Chevalley.matrixK K ell M x y i j)" := by
  intro W hx hy
  have hp (f : Module.End K (Chevalley.VK K M)) (hf : Chevalley.stable W f) :
      ∀ r : ℕ, Chevalley.stable W (f ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w hw
      simpa using hw
    | succ r ih =>
      intro w hw
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hf _ hw)
  have hsm (a : K) (f : Module.End K (Chevalley.VK K M)) (hf : Chevalley.stable W f) :
      Chevalley.stable W (a • f) := by
    intro w hw
    exact W.smul_mem a (hf w hw)
  have hmul (f g : Module.End K (Chevalley.VK K M))
      (hf : Chevalley.stable W f) (hg : Chevalley.stable W g) : Chevalley.stable W (f*g) := by
    intro w hw
    exact hf _ (hg w hw)
  have hfact := @yui_aux_0013 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013
  have hX (r : ℕ) (hr : r ≤ ell.toNat) : Chevalley.stable W (Chevalley.opK K M (Chevalley.dp x r)) := by
    rw [(hfact r hr).2.1]
    exact hsm _ _ (hp _ hx r)
  have hY (r : ℕ) (hr : r ≤ ell.toNat) : Chevalley.stable W (Chevalley.opK K M (Chevalley.dp y r)) := by
    rw [(hfact r hr).2.2]
    exact hsm _ _ (hp _ hy r)
  intro i j
  unfold Chevalley.matrixK
  apply hsm
  apply hmul
  · exact hmul _ _ (hX _ (Nat.sub_le _ _)) (hmul _ _ (hY _ le_rfl) (hX _ le_rfl))
  · exact hY _ (Nat.sub_le _ _)
#check @checked
#print axioms checked
end YuiAuxiliary
