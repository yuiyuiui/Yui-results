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
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) (h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ)) : yui_aux_type% "∀ (a : ℂ) (i : ℕ), a ∈ Chevalley.J p M y v i ↔ a • Chevalley.e y v i ∈ Chevalley.image p M" := by
  intro a i
  rfl

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) (h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ)) : yui_aux_type% "∀ b : ℂ, Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) → ∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)" := by
  classical
  intro b hb u
  constructor
  · intro hu
    obtain ⟨d, hd, -⟩ := (h_T010.1.2.2.2 u).mp hu
    have hcoeff : ∀ i, ∃ a : Chevalley.R p, a • b = d i := by
      intro i
      exact Submodule.mem_span_singleton.mp (hb ▸ hd.1 i)
    choose c hc using hcoeff
    refine ⟨c, hd.2.trans ?_⟩
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hc i]
    rw [← smul_assoc]
    rfl
  · rintro ⟨c, rfl⟩
    have hm : ∀ i : Chevalley.Index ell, (b • Chevalley.e y v i.val) ∈ Chevalley.image p M := by
      intro i
      apply (@yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011 b i.val).mp
      rw [h_T010.1.1 i, hb]
      exact Submodule.mem_span_singleton_self b
    letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
    change (∑ i, c i • (b • Chevalley.e y v i.val)) ∈ (Chevalley.muR p M).range
    exact Submodule.sum_mem _ fun i hi => (Chevalley.muR p M).range.smul_mem (c i) (hm i)

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) (h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ)) : yui_aux_type% "Function.Injective (algebraMap (Chevalley.R p) ℂ)" := by
  intro a b hab
  apply Subtype.ext
  apply (algebraMap ℚ ℂ).injective
  exact hab

theorem checked (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) (h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ)) : yui_aux_type% "Function.Injective (fun r : Chevalley.R p => r • (1 : ℂ))" := by
  intro a b hab
  apply (@yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011)
  change (algebraMap (Chevalley.R p) ℂ a) * 1 = (algebraMap (Chevalley.R p) ℂ b) * 1 at hab
  simpa only [mul_one] using hab
#check @checked
#print axioms checked
end YuiAuxiliary
