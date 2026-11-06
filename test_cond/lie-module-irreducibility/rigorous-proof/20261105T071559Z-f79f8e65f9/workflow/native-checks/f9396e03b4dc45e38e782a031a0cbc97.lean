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
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) : yui_aux_type% "∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)" := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp h_H001.1
  have h1 : ¬ (p : ℤ) ∣ 1 := hp.not_dvd_one
  intro q
  constructor
  · intro hq
    induction hq using Algebra.adjoin_induction with
    | mem q hq =>
      obtain ⟨b, hb, rfl⟩ := hq
      exact ⟨1, b, hb, by simp⟩
    | algebraMap a => exact ⟨a, 1, h1, by simp⟩
    | add q r hq hr iq ir =>
      obtain ⟨a, b, hb, rfl⟩ := iq
      obtain ⟨c, d, hd, rfl⟩ := ir
      have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 from fun h => hb (h ▸ dvd_zero _))
      have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 from fun h => hd (h ▸ dvd_zero _))
      refine ⟨a*d+c*b, b*d, fun h => (hp.dvd_mul.mp h).elim hb hd, ?_⟩
      push_cast
      field_simp
    | mul q r hq hr iq ir =>
      obtain ⟨a, b, hb, rfl⟩ := iq
      obtain ⟨c, d, hd, rfl⟩ := ir
      refine ⟨a*c, b*d, fun h => (hp.dvd_mul.mp h).elim hb hd, ?_⟩
      push_cast
      ring
  · rintro ⟨a, b, hb, rfl⟩
    rw [div_eq_mul_inv]
    exact (Chevalley.R p).mul_mem ((Chevalley.R p).algebraMap_mem a)
      (Algebra.subset_adjoin ⟨b, hb, rfl⟩)

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) : yui_aux_type% "Function.Injective (fun r : Chevalley.R p => r • (1 : ℂ))" := by
  intro a b hab
  change ((a : ℚ) : ℂ) * 1 = ((b : ℚ) : ℂ) * 1 at hab
  simp only [mul_one] at hab
  apply Subtype.ext
  exact Rat.cast_injective hab

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) : yui_aux_type% "Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤" := by
  classical
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V := IsScalarTower.of_compHom _ _ _
  obtain ⟨d, b, B, hb⟩ := h_H004.1
  have hd : d = ell.toNat + 1 := by
    have hh := Module.finrank_eq_card_basis B
    simpa [h_H002.2.1] using hh.symm
  let eqi : Fin d ≃ Chevalley.Index ell := finCongr hd
  let b' := b.reindex eqi
  let B' := B.reindex eqi
  have hb' (i : Chevalley.Index ell) : (b' i : V) = B' i := by
    simpa [b', B'] using hb (eqi.symm i)
  let c := b'.baseChange (Chevalley.R p)
  have hc (i : Chevalley.Index ell) : Chevalley.mu p M (c i) = B' i := by
    simp [c, Chevalley.mu, hb']
  have hinj : Function.Injective (fun r : Chevalley.R p => r • (1 : ℂ)) :=
    @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H004 h_T004
  have hli : LinearIndependent (Chevalley.R p) (fun i => Chevalley.mu p M (c i)) := by
    simpa only [hc] using B'.linearIndependent.restrict_scalars hinj
  have hi : Function.Injective (Chevalley.mu p M) :=
    LinearMap.injective_of_linearIndependent (f := Chevalley.muR p M) c.span_eq hli
  refine ⟨hi, ⟨c⟩, ?_⟩
  apply (Submodule.eq_top_iff_forall_basis_mem B').mpr
  intro i
  apply Submodule.subset_span
  exact ⟨c i, hc i⟩

theorem checked (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) : yui_aux_type% "∀ (f : Module.End ℂ V), Chevalley.preserves M f → ∀ u : Chevalley.MR p M, Chevalley.mu p M (((Chevalley.latticeOp M f).baseChange (Chevalley.R p)) u) = f (Chevalley.mu p M u)" := by
  classical
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V := IsScalarTower.of_compHom _ _ _
  intro f hf u
  change (Chevalley.muR p M) (((Chevalley.latticeOp M f).baseChange (Chevalley.R p)) u) =
    f ((Chevalley.muR p M) u)
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul]
    simp only [Chevalley.muR, LinearMap.liftBaseChange_tmul]
    have hm : ((Chevalley.latticeOp M f) m : V) = f m := by
      simp only [Chevalley.latticeOp, if_pos hf]
      rfl
    rw [hm]
    exact ((f.restrictScalars (Chevalley.R p)).map_smul a (m : V)).symm
  | add u w hu hw => simp only [map_add, hu, hw]
#check @checked
#print axioms checked
end YuiAuxiliary
