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

namespace Local_T001
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) : yui_aux_type% "(∀ w : V, h (y w) = y (h w) - (2 : ℂ) • y w) ∧ (∀ w : V, x (y w) = y (x w) + h w)" := by
  constructor
  · intro w
    have hw := congrArg (fun f : Module.End ℂ V => f w) h_H002.2.2.2.1
    change h (y w) - y (h w) = (-2 : ℂ) • y w at hw
    rw [neg_smul] at hw
    exact (sub_eq_iff_eq_add.mp hw).trans (by abel)
  · intro w
    have hw := congrArg (fun f : Module.End ℂ V => f w) h_H002.2.2.2.2.1
    change x (y w) - y (x w) = h w at hw
    exact (sub_eq_iff_eq_add.mp hw).trans (by abel)

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) : yui_aux_type% "∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)" := by
  have hc := (@yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003).1
  intro t
  induction t with
  | zero => simpa using h_H003.2.2
  | succ t ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [hc, ih, map_smul, ← sub_smul]
    congr 1
    push_cast
    ring

end Local_T001
open Local_T001 in
theorem T001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) :
    (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v)) := by
  have hh := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003
  have hc := (@yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003).2
  have hx : ∀ t : ℕ, x ((y ^ (t + 1)) v) = (((t : ℂ) + 1) * ((ell : ℂ) - (t : ℂ))) • ((y ^ t) v) := by
    intro t
    induction t with
    | zero => simpa [hc, h_H003.2.1, h_H003.2.2] 
    | succ t ih =>
      have hp : y ((y ^ t) v) = (y ^ (t + 1)) v := by rw [pow_succ']; rfl
      calc
        x ((y ^ (t + 1 + 1)) v) = y (x ((y ^ (t + 1)) v)) + h ((y ^ (t + 1)) v) := by
          rw [pow_succ' y (t + 1)]
          exact hc _
        _ = ((((t + 1 : ℕ) : ℂ) + 1) * ((ell : ℂ) - ((t + 1 : ℕ) : ℂ))) • ((y ^ (t + 1)) v) := by
          rw [ih, map_smul, hp, hh, ← add_smul]
          congr 1
          push_cast
          ring
  constructor
  · exact hh
  · intro t ht
    cases t with
    | zero => omega
    | succ t =>
      have hs : (ell : ℂ) - ((t + 1 : ℕ) : ℂ) + 1 = (ell : ℂ) - (t : ℂ) := by push_cast; ring
      simpa [Nat.succ_eq_add_one, hs] using hx t

#check @T001
#print axioms T001

end Translation
