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

theorem checked (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ (ρ : Chevalley.R p →+* K),\n  letI := ρ.toAlgebra\n  ∀ (Φ : Chevalley.VK K M ≃ₗ[K] (K ⊗[Chevalley.R p] Chevalley.MR p M)),\n  (∀ (c : K) (m : M), Φ (c ⊗ₜ[ℤ] m) = c ⊗ₜ[Chevalley.R p] ((1 : Chevalley.R p) ⊗ₜ[ℤ] m)) →\n  ∀ (F : Module.End ℤ M) (u w : Chevalley.MR p M) (z : ℤ),\n  Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = (z : ℂ) • Chevalley.mu p M w →\n  F.baseChange K (Φ.symm (1 ⊗ₜ[Chevalley.R p] u)) = (z : K) • Φ.symm (1 ⊗ₜ[Chevalley.R p] w)" := by
  intro ρ
  letI := ρ.toAlgebra
  intro Φ hΦ F u w z heq
  apply @yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 ρ Φ hΦ F u w z
  apply h_T006.1.2.1
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  change Chevalley.mu p M (F.baseChange (Chevalley.R p) u) = (Chevalley.muR p M) (z • w)
  rw [map_zsmul]
  exact heq.trans (Int.cast_smul_eq_zsmul ℂ z (Chevalley.mu p M w))
#check @checked
#print axioms checked
end YuiAuxiliary
