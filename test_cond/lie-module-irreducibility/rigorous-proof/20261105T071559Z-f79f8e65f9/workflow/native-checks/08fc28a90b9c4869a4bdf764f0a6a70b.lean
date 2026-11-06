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

namespace Translation
set_option autoImplicit false

namespace Local_T007
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∀ (i : ℕ) (c : ℂ), c ∈ Chevalley.J p M y v i ↔ c • Chevalley.e y v i ∈ Chevalley.image p M" := by
  intro i c
  rfl

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0" := by
  classical
  obtain ⟨b, hb⟩ := h_T004.2.2.2.2.1
  have bridge := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  have transport : ∀ (i j : Chevalley.Index ell) (c : ℂ),
      c ∈ Chevalley.J p M y v j.val → c ∈ Chevalley.J p M y v i.val := by
    intro i j c hc
    apply (bridge i.val c).mpr
    have hs := (h_T006.2 b hb i j).2.2.2.2.2 _ ((bridge j.val c).mp hc)
    simpa [Chevalley.unitOp, ← hb j, hb i] using hs
  intro i
  let z : Chevalley.Index ell := ⟨0, Nat.zero_lt_succ _⟩
  apply le_antisymm
  · intro c hc
    exact transport z i c hc
  · intro c hc
    exact transport i z c hc

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ); ∀ u : Chevalley.MR p M, Chevalley.muR p M u = Chevalley.mu p M u" := by
  intro u
  rfl

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "(Chevalley.J p M y v 0).FG" := by
  classical
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V := IsScalarTower.of_compHom (Chevalley.R p) ℂ V
  obtain ⟨b, hb⟩ := h_T004.2.2.2.2.1
  obtain ⟨a⟩ := h_T006.1.2.2.1
  letI : Module.Finite (Chevalley.R p) (Chevalley.MR p M) := Module.Finite.of_basis a
  let z : Chevalley.Index ell := ⟨0, Nat.zero_lt_succ _⟩
  let f : Chevalley.MR p M →ₗ[Chevalley.R p] ℂ :=
    ((b.coord z).restrictScalars (Chevalley.R p)).comp (Chevalley.muR p M)
  have bridge := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  have hmu := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  have hr : f.range = Chevalley.J p M y v 0 := by
    ext c
    constructor
    · rintro ⟨u, rfl⟩
      apply (bridge 0 (f u)).mpr
      have hu : Chevalley.mu p M u ∈ Chevalley.image p M := ⟨u, rfl⟩
      have hp := (h_T006.2 b hb z z).2.2.2.2.2 _ hu
      simpa [Chevalley.unitOp, f, hmu, ← hb z, z] using hp
    · intro hc
      obtain ⟨u, hu⟩ := (bridge 0 c).mp hc
      refine ⟨u, ?_⟩
      change b.coord z (Chevalley.muR p M u) = c
      rw [hmu, hu]
      simp [← hb z, z]
  rw [← hr]
  exact Submodule.fg_range f

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ u : V, u ∈ Chevalley.image p M → ∀ i, b.coord i u ∈ Chevalley.J p M y v 0" := by
  intro b hb u hu i
  have bridge := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  have heq := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  rw [← heq i]
  apply (bridge i.val _).mpr
  have hp := (h_T006.2 b hb i i).2.2.2.2.2 u hu
  simpa [Chevalley.unitOp, hb i] using hp

theorem yui_aux_0006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "Chevalley.J p M y v 0 ≠ ⊥" := by
  classical
  intro hzero
  obtain ⟨b, hb⟩ := h_T004.2.2.2.2.1
  have hc := @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 b hb
  have hz : ∀ u ∈ Chevalley.image p M, u = 0 := by
    intro u hu
    apply b.forall_coord_eq_zero_iff.mp
    intro i
    have hi := hc u hu i
    simpa [hzero] using hi
  have hs : Submodule.span ℂ (Chevalley.image p M) ≤ (⊥ : Submodule ℂ V) := by
    apply Submodule.span_le.mpr
    intro u hu
    exact (Submodule.mem_bot ℂ).mpr (hz u hu)
  rw [h_T006.1.2.2.2.1] at hs
  let z : Chevalley.Index ell := ⟨0, Nat.zero_lt_succ _⟩
  exact b.ne_zero z ((Submodule.mem_bot ℂ).mp (hs (Submodule.mem_top : b z ∈ (⊤ : Submodule ℂ V))))

theorem yui_aux_0007 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∀ (b : Module.Basis (Chevalley.Index ell) ℂ V) (c : Chevalley.Index ell → ℂ) (i : Chevalley.Index ell), b.coord i (∑ j, c j • b j) = c i" := by
  classical
  intro b c i
  simp [map_sum, Finsupp.single_apply, mul_ite]

end Local_T007
open Local_T007 in
theorem T007 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) :
    (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val) := by
  classical
  refine ⟨@yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006,
    @yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006,
    @yui_aux_0006 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006, ?_⟩
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V := IsScalarTower.of_compHom (Chevalley.R p) ℂ V
  obtain ⟨b, hb⟩ := h_T004.2.2.2.2.1
  have bridge := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  have heq := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  have hcoord := @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 b hb
  have hsum := @yui_aux_0007 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 b
  intro u
  constructor
  · intro hu
    refine ⟨fun i => b.coord i u, ⟨hcoord u hu, ?_⟩, ?_⟩
    · simpa only [Module.Basis.coord_apply, hb] using (b.sum_repr u).symm
    · intro c hc
      funext i
      have hi := congrArg (b.coord i) hc.2
      have hs : b.coord i u = c i := by
        simpa only [← hb, hsum] using hi
      exact hs.symm
  · rintro ⟨c, hc, _⟩
    rw [hc.2]
    change (∑ i, c i • Chevalley.e y v i.val) ∈ (Chevalley.muR p M).range
    apply Submodule.sum_mem
    intro i _
    change c i • Chevalley.e y v i.val ∈ Chevalley.image p M
    apply (bridge i.val (c i)).mp
    rw [heq i]
    exact hc.1 i

#check @T007
#print axioms T007

end Translation
