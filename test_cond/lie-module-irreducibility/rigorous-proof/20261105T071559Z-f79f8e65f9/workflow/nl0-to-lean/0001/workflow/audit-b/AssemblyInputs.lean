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

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) : yui_aux_type% "∀ t : ℕ, (ell : ℂ) - ((t : ℂ) + 1) + 1 = (ell : ℂ) - (t : ℂ)" := by
  intro t
  ring

end Local_T001
open Local_T001 in
theorem T001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) :
    (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v)) := by
  have hh := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003
  have hc := (@yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003).2
  have hs := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003
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
    | succ t => simpa [Nat.succ_eq_add_one, hs] using hx t

namespace Local_T002
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "∀ n : ℕ, n + 1 ≤ ell.toNat → ((n + 1 : ℕ) : ℂ) * ((ell : ℂ) - ((n + 1 : ℕ) : ℂ) + 1) ≠ 0" := by
  intro n hn
  have hell : (ell.toNat : ℤ) = ell := Int.toNat_of_nonneg h_H001.2.2.1
  have he : ell - (n : ℤ) ≠ 0 := by omega
  have he' : (ell : ℂ) - (n : ℂ) ≠ 0 := by exact_mod_cast he
  have hh : (ell : ℂ) - ((n + 1 : ℕ) : ℂ) + 1 = (ell : ℂ) - (n : ℂ) := by push_cast; ring
  rw [hh]
  exact mul_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n)) he'

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "∀ n : ℕ, n ≤ ell.toNat → (y ^ n) v ≠ 0" := by
  intro n
  induction n with
  | zero => simpa using h_H003.1
  | succ n ih =>
    intro hn hz
    have hr := h_T001.2 (n + 1) (by omega)
    rw [hz, map_zero, Nat.add_sub_cancel] at hr
    exact ih (by omega) ((smul_eq_zero.mp hr.symm).resolve_left
      (@yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001 n hn))

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "∀ i : Chevalley.Index ell, h (Chevalley.e y v i.val) = ((ell : ℂ) - 2 * (i.val : ℂ)) • Chevalley.e y v i.val" := by
  intro i
  change h (((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v) =
    ((ell : ℂ) - 2 * (i.val : ℂ)) • (((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v)
  rw [map_smul, h_T001.1 i.val, smul_comm]

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "∀ i : Chevalley.Index ell, Chevalley.e y v i.val ≠ 0" := by
  intro i
  change ((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v ≠ 0
  have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i.val)
  exact smul_ne_zero (inv_ne_zero hf)
    (@yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001 i.val (by have := i.isLt; omega))

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "∀ (q : Polynomial ℂ) (i : Chevalley.Index ell), (Polynomial.aeval h q) (Chevalley.e y v i.val) = q.eval ((ell : ℂ) - 2 * (i.val : ℂ)) • Chevalley.e y v i.val" := by
  intro q i
  exact Module.End.aeval_apply_of_mem_apply_eq_smul (p := q)
    (@yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001 i)

theorem yui_aux_0006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "Function.Injective (fun i : Chevalley.Index ell => (ell : ℂ) - 2 * (i.val : ℂ))" := by
  intro i j he
  have hv : (i.val : ℂ) = (j.val : ℂ) := by linear_combination (-1 / 2 : ℂ) * he
  apply Fin.ext
  exact_mod_cast hv

theorem yui_aux_0007 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "∀ (q : Polynomial ℂ) (c : ℂ) (i : Chevalley.Index ell), (Polynomial.aeval h q) (c • Chevalley.e y v i.val) = (c * q.eval ((ell : ℂ) - 2 * (i.val : ℂ))) • Chevalley.e y v i.val" := by
  intro q c i
  rw [map_smul, @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001 q i]
  exact smul_smul c (q.eval ((ell : ℂ) - 2 * (i.val : ℂ))) (Chevalley.e y v i.val)

theorem yui_aux_0008 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) : yui_aux_type% "LinearIndependent ℂ (fun i : Chevalley.Index ell => Chevalley.e y v i.val)" := by
  classical
  let a : Chevalley.Index ell → V := fun i => Chevalley.e y v i.val
  let μ : Chevalley.Index ell → ℂ := fun i => (ell : ℂ) - 2 * (i.val : ℂ)
  have hμ : Function.Injective μ := @yui_aux_0006 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let q : Polynomial ℂ := ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (μ k))
  have hq : ∀ z : ℂ, q.eval z = ∏ k ∈ Finset.univ.erase j, (z - μ k) := by
    intro z
    simp only [q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hoff : ∀ i : Chevalley.Index ell, i ≠ j → q.eval (μ i) = 0 := by
    intro i hij
    rw [hq]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) (sub_self _)
  have hnon : q.eval (μ j) ≠ 0 := by
    rw [hq]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hk).1 (hμ he).symm)
  have hh := congrArg (fun w : V => (Polynomial.aeval h q) w) hc
  rw [map_sum, map_zero] at hh
  change (∑ i : Chevalley.Index ell, (Polynomial.aeval h q) (c i • a i)) = 0 at hh
  have happ : ∀ i : Chevalley.Index ell, (Polynomial.aeval h q) (c i • a i) =
      (c i * q.eval (μ i)) • a i := by
    intro i
    exact @yui_aux_0007 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001 q (c i) i
  simp_rw [happ] at hh
  have he : (c j * q.eval (μ j)) • a j = 0 := by
    rw [Finset.sum_eq_single j] at hh
    · exact hh
    · intro b hb hbj
      rw [hoff b hbj, mul_zero, zero_smul]
    · simp
  have hn : a j ≠ 0 := @yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001 j
  exact (mul_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hn)).resolve_right hnon

end Local_T002
open Local_T002 in
theorem T002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) :
    ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val := by
  classical
  letI : FiniteDimensional ℂ V := h_H002.1
  have hli : LinearIndependent ℂ (fun i : Chevalley.Index ell => Chevalley.e y v i.val) :=
    @yui_aux_0008 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001
  have hcard : Fintype.card (Chevalley.Index ell) = Module.finrank ℂ V := by
    rw [h_H002.2.1]
    exact Fintype.card_fin (ell.toNat + 1)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' (fun i : Chevalley.Index ell => Chevalley.e y v i.val) hli hcard, ?_⟩
  intro i
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank'
    (K := ℂ) (fun i : Chevalley.Index ell => Chevalley.e y v i.val) hli hcard) i

namespace Local_T003
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

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "∀ r i : ℕ, (y ^ r) (Chevalley.e y v i) = (((i+1).ascFactorial r : ℕ) : ℂ) • Chevalley.e y v (i+r)" := by
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

theorem yui_aux_0006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "∀ r i : ℕ, i ≤ ell.toNat → r ≤ i → (x ^ r) (Chevalley.e y v i) = (((ell.toNat-i+1).ascFactorial r : ℕ) : ℂ) • Chevalley.e y v (i-r)" := by
  have hg := (yui_aux_0003 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002).1
  have hn : (ell.toNat : ℂ) = (ell : ℂ) := by exact_mod_cast Int.toNat_of_nonneg h_H001.2.2.1
  intro r
  induction r with
  | zero => intro i hi hr; simp
  | succ r ih =>
    intro i hi hr
    rw [pow_succ', Module.End.mul_apply, ih i hi (by omega), map_smul]
    have he : i-r = (i-r-1)+1 := by omega
    rw [he, hg]
    have he' : i-r-1 = i-(r+1) := by omega
    rw [he', smul_smul, Nat.ascFactorial_succ, Nat.cast_mul]
    congr 1
    have hc : ((ell.toNat-i+1+r : ℕ) : ℂ) = (ell : ℂ) - ((i-(r+1) : ℕ) : ℂ) := by
      push_cast
      rw [Nat.cast_sub hi, hn, Nat.cast_sub (by omega : r+1 ≤ i)]
      push_cast
      ring
    rw [hc]
    ring

theorem yui_aux_0007 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) : yui_aux_type% "Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v)" := by
  have hx := yui_aux_0006 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002
  have hy := yui_aux_0005 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002
  have hz := yui_aux_0002 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002
  have hx0 : x (Chevalley.e y v 0) = 0 := by simpa [Chevalley.e, Chevalley.dp] using h_H003.2.1
  have hf : ∀ r : ℕ, (r.factorial : ℂ) ≠ 0 := fun r => by exact_mod_cast Nat.factorial_ne_zero r
  intro r i hi
  constructor
  · simp only [Chevalley.dp, LinearMap.smul_apply]
    by_cases hr : r ≤ i
    · rw [if_pos hr, hx r i hi hr, Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_smul]
      simp [hf r]
    · rw [if_neg hr]
      have hk : (x ^ (i+1)) (Chevalley.e y v i) = 0 := by
        rw [pow_succ', Module.End.mul_apply, hx i i hi le_rfl, Nat.sub_self, map_smul, hx0, smul_zero]
      have he : r = (r-(i+1))+(i+1) := by omega
      rw [he, pow_add, Module.End.mul_apply, hk, map_zero, smul_zero]
  · simp only [Chevalley.dp, LinearMap.smul_apply]
    rw [hy r i]
    by_cases hr : i+r ≤ ell.toNat
    · rw [if_pos hr, Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_smul]
      simp [hf r]
    · rw [if_neg hr]
      have he : Chevalley.e y v (i+r) = 0 := by
        simp only [Chevalley.e, Chevalley.dp, LinearMap.smul_apply, hz (i+r) (by omega), smul_zero]
      rw [he, smul_zero, smul_zero]

end Local_T003
open Local_T003 in
theorem T003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) :
    (∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v) := by
  exact ⟨yui_aux_0002 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002,
    yui_aux_0004 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002,
    yui_aux_0007 V K p ell x y h v M h_H001 h_H003 h_T001 h_T002⟩

theorem T004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) (h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) (h_T003 : (∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v)) :
    0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v)) := by
  refine ⟨Nat.succ_pos _, ?_, h_H002.2.1, h_T001, h_T002, h_T003⟩
  simp [Chevalley.Index]

namespace Local_T005
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

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) : yui_aux_type% "∀ (f : Module.End ℂ V), Chevalley.preserves M f → ∀ m : M, ((Chevalley.latticeOp M f) m : V) = f m" := by
  classical
  intro f hf m
  change (∀ u ∈ M, f u ∈ M) at hf
  simp only [Chevalley.latticeOp, dif_pos hf]
  rfl

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) : yui_aux_type% "∀ (f : Module.End ℂ V), Chevalley.preserves M f → ∀ u : Chevalley.MR p M, Chevalley.mu p M (((Chevalley.latticeOp M f).baseChange (Chevalley.R p)) u) = f (Chevalley.mu p M u)" := by
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
    change a • ((Chevalley.latticeOp M f) m : V) = f (a • (m : V))
    rw [@yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H004 h_T004 f hf m]
    exact ((f.restrictScalars (Chevalley.R p)).map_smul a (m : V)).symm
  | add u w hu hw => simp only [map_add, hu, hw]

end Local_T005
open Local_T005 in
theorem T005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) :
    (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u)) := by
  classical
  have hloc := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H004 h_T004
  have hb := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H004 h_T004
  have ht := @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H004 h_T004
  have hx : Chevalley.preserves M x := by
    simpa [Chevalley.dp] using (h_H004.2 1).1
  have hy : Chevalley.preserves M y := by
    simpa [Chevalley.dp] using (h_H004.2 1).2
  have hh : Chevalley.preserves M h := by
    intro w hw
    rw [← h_H002.2.2.2.2.1]
    change x (y w) - y (x w) ∈ M
    exact M.sub_mem (hx _ (hy _ hw)) (hy _ (hx _ hw))
  have him : ∀ f : Module.End ℂ V, Chevalley.preserves M f → Chevalley.inImage p M f := by
    intro f hf w hw
    obtain ⟨u, rfl⟩ := hw
    exact ⟨((Chevalley.latticeOp M f).baseChange (Chevalley.R p)) u, ht f hf u⟩
  refine ⟨hloc, hb.1, hb.2.1, hb.2.2, ?_, hx, hy, hh, ?_⟩
  · intro r
    exact ⟨him _ (h_H004.2 r).1, him _ (h_H004.2 r).2⟩
  · intro r u
    exact ⟨ht _ (h_H004.2 r).1 u, ht _ (h_H004.2 r).2 u⟩

namespace Local_T006
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ k : ℕ, k ≤ ell.toNat → (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) (Chevalley.e y v k) = if k = ell.toNat then Chevalley.e y v ell.toNat else 0" := by
  intro k hk
  have ha := h_T004.2.2.2.2.2.2.2
  change Chevalley.dp y ell.toNat (Chevalley.dp x ell.toNat (Chevalley.e y v k)) = _
  rw [(ha ell.toNat k hk).1]
  by_cases he : k = ell.toNat
  · subst k
    simp only [le_refl, ite_true, Nat.sub_self, Nat.zero_add, Nat.choose_self, Nat.cast_one, one_smul]
    rw [(ha ell.toNat 0 (Nat.zero_le _)).2]
    simp
  · have hn : ¬ ell.toNat ≤ k := by omega
    simp [hn, he]

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ j : Chevalley.Index ell, ¬ (p : ℤ) ∣ (Nat.choose ell.toNat j.val : ℤ)" := by
  intro j
  have hn : ell.toNat < p := by omega
  have hf : ¬ p ∣ ell.toNat.factorial := by
    rw [h_H001.1.dvd_factorial]
    omega
  have hc : ¬ p ∣ Nat.choose ell.toNat j.val := by
    intro hd
    apply hf
    rw [← Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ j.isLt)]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  exact_mod_cast hc

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ i : Chevalley.Index ell, Chevalley.dp x (ell.toNat - i.val) (Chevalley.e y v ell.toNat) = Chevalley.e y v i.val" := by
  intro i
  have hi : i.val ≤ ell.toNat := Nat.le_of_lt_succ i.isLt
  rw [(h_T004.2.2.2.2.2.2.2 (ell.toNat - i.val) ell.toNat (le_refl _)).1]
  simp [Nat.sub_le, Nat.sub_sub_self hi]

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat)" := by
  intro b hb
  have hbL : b (Fin.last ell.toNat) = Chevalley.e y v ell.toNat := by simpa using hb (Fin.last ell.toNat)
  apply b.ext
  intro k
  rw [hb k, yui_aux_0001 V K p ell x y h v M h_H001 h_T004 h_T005 k.val (Nat.le_of_lt_succ k.isLt)]
  by_cases hk : k = Fin.last ell.toNat
  · subst k
    simp only [Fin.val_last, ite_true]
    rw [← hbL]
    simp [Chevalley.unitOp]
  · have hkn : k.val ≠ ell.toNat := by
      intro he
      apply hk
      exact Fin.ext he
    rw [if_neg hkn]
    simp [Chevalley.unitOp, ← hb k, Ne.symm hk]

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ ∃ a : Chevalley.R p, algebraMap (Chevalley.R p) ℂ a = (Nat.choose ell.toNat j.val : ℂ)⁻¹" := by
  intro j
  have hd := yui_aux_0002 V K p ell x y h v M h_H001 h_T004 h_T005 j
  have hn : Nat.choose ell.toNat j.val ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (Nat.le_of_lt_succ j.isLt))
  have hq : (Nat.choose ell.toNat j.val : ℚ) ≠ 0 := by exact_mod_cast hn
  have hm : (Nat.choose ell.toNat j.val : ℚ)⁻¹ ∈ Chevalley.R p := by
    apply (h_T005.1 _).2
    refine ⟨1, (Nat.choose ell.toNat j.val : ℤ), hd, ?_⟩
    simp
  let a : Chevalley.R p := ⟨_, hm⟩
  have ha : algebraMap (Chevalley.R p) ℂ a = (Nat.choose ell.toNat j.val : ℂ)⁻¹ := by
    change ((↑a : ℚ) : ℂ) = _
    simp [a]
  constructor
  · refine ⟨⟨(Nat.choose ell.toNat j.val : Chevalley.R p), a, ?_, ?_⟩, rfl⟩ <;>
      apply Subtype.ext <;> change _ = (1 : ℚ) <;> simp [a, hq]
  · exact ⟨a, ha⟩

theorem yui_aux_0006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ (j : Chevalley.Index ell) (k : ℕ), k ≤ ell.toNat → ((Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) (Chevalley.e y v k) = if k = j.val then (Nat.choose ell.toNat j.val : ℂ) • Chevalley.e y v ell.toNat else 0" := by
  intro j k hk
  have hj : j.val ≤ ell.toNat := Nat.le_of_lt_succ j.isLt
  change (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) (Chevalley.dp y (ell.toNat - j.val) (Chevalley.e y v k)) = _
  rw [(h_T004.2.2.2.2.2.2.2 (ell.toNat - j.val) k hk).2]
  by_cases he : k = j.val
  · subst k
    have hs : j.val + (ell.toNat - j.val) = ell.toNat := by omega
    simp only [hs, le_refl, ite_true]
    rw [map_smul, yui_aux_0001 V K p ell x y h v M h_H001 h_T004 h_T005 _ (le_refl _)]
    simp [Nat.choose_symm hj]
  · by_cases hl : k + (ell.toNat - j.val) ≤ ell.toNat
    · rw [if_pos hl, map_smul, yui_aux_0001 V K p ell x y h v M h_H001 h_T004 h_T005 _ hl]
      have hs : k + (ell.toNat - j.val) ≠ ell.toNat := by omega
      simp [hs, he]
    · simp [hl, he]

theorem yui_aux_0007 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i : Chevalley.Index ell, Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat)" := by
  intro b hb i
  rw [yui_aux_0004 V K p ell x y h v M h_H001 h_T004 h_T005 b hb]
  have hbL : b (Fin.last ell.toNat) = Chevalley.e y v ell.toNat := by simpa using hb (Fin.last ell.toNat)
  ext w
  change Chevalley.dp x (ell.toNat - i.val) ((b.coord (Fin.last ell.toNat)) w • b (Fin.last ell.toNat)) = (b.coord (Fin.last ell.toNat)) w • b i
  rw [map_smul, hbL, yui_aux_0003 V K p ell x y h v M h_H001 h_T004 h_T005 i, hb i]

theorem yui_aux_0008 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ j : Chevalley.Index ell, (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j" := by
  intro b hb j
  have hbL : b (Fin.last ell.toNat) = Chevalley.e y v ell.toNat := by simpa using hb (Fin.last ell.toNat)
  apply b.ext
  intro k
  rw [hb k, yui_aux_0006 V K p ell x y h v M h_H001 h_T004 h_T005 j k.val (Nat.le_of_lt_succ k.isLt)]
  by_cases hk : k = j
  · subst k
    simp only [ite_true]
    rw [← hb j, ← hbL]
    simp [Chevalley.unitOp]
  · have hkj : k.val ≠ j.val := fun he => hk (Fin.ext he)
    rw [if_neg hkj, ← hb k]
    simp [Chevalley.unitOp, Ne.symm hk]

theorem yui_aux_0009 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ (a : Chevalley.R p) (u : Chevalley.MR p M), Chevalley.mu p M (a • u) = algebraMap (Chevalley.R p) ℂ a • Chevalley.mu p M u" := by
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V := IsScalarTower.of_compHom (Chevalley.R p) ℂ V
  intro a u
  change (Chevalley.muR p M) (a • u) = a • (Chevalley.muR p M) u
  exact (Chevalley.muR p M).map_smul a u

theorem yui_aux_0010 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) : yui_aux_type% "∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val))" := by
  intro b hb i j
  have hbL : b (Fin.last ell.toNat) = Chevalley.e y v ell.toNat := by simpa using hb (Fin.last ell.toNat)
  have hc : (Nat.choose ell.toNat j.val : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)))
  have hu : Chevalley.dp x (ell.toNat - i.val) * Chevalley.unitOp b (Fin.last ell.toNat) j = Chevalley.unitOp b i j := by
    ext w
    change Chevalley.dp x (ell.toNat - i.val) ((b.coord j) w • b (Fin.last ell.toNat)) = (b.coord j) w • b i
    rw [map_smul, hbL, yui_aux_0003 V K p ell x y h v M h_H001 h_T004 h_T005 i, hb i]
  rw [mul_assoc, yui_aux_0008 V K p ell x y h v M h_H001 h_T004 h_T005 b hb j, mul_smul_comm, hu, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Local_T006
open Local_T006 in
theorem T006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) :
    ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j)) := by
  refine ⟨h_T005, ?_⟩
  intro b hb i j
  have hj := yui_aux_0005 V K p ell x y h v M h_H001 h_T004 h_T005 j
  have he := yui_aux_0010 V K p ell x y h v M h_H001 h_T004 h_T005 b hb i j
  refine ⟨hj.1,
    yui_aux_0004 V K p ell x y h v M h_H001 h_T004 h_T005 b hb,
    yui_aux_0007 V K p ell x y h v M h_H001 h_T004 h_T005 b hb i,
    yui_aux_0008 V K p ell x y h v M h_H001 h_T004 h_T005 b hb j,
    he, ?_⟩
  intro w hw
  rw [he]
  change (Nat.choose ell.toNat j.val : ℂ)⁻¹ •
    Chevalley.dp x (ell.toNat - i.val)
      (Chevalley.dp y ell.toNat
        (Chevalley.dp x ell.toNat (Chevalley.dp y (ell.toNat - j.val) w))) ∈ Chevalley.image p M
  have hp := h_T005.2.2.2.2.1
  have hz : Chevalley.dp x (ell.toNat - i.val)
      (Chevalley.dp y ell.toNat
        (Chevalley.dp x ell.toNat (Chevalley.dp y (ell.toNat - j.val) w))) ∈ Chevalley.image p M :=
    (hp (ell.toNat - i.val)).1 _
      ((hp ell.toNat).2 _ ((hp ell.toNat).1 _ ((hp (ell.toNat - j.val)).2 _ hw)))
  rcases hz with ⟨u, hu⟩
  rcases hj.2 with ⟨a, ha⟩
  refine ⟨a • u, ?_⟩
  rw [yui_aux_0009 V K p ell x y h v M h_H001 h_T004 h_T005 a u, ha, hu]

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

namespace Local_T008
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) : yui_aux_type% "IsFractionRing (Chevalley.R p) ℚ" := by
  apply IsFractionRing.of_field
  intro z
  refine ⟨(z.num : Chevalley.R p), (z.den : Chevalley.R p), ?_⟩
  simpa only [map_intCast, map_natCast] using (Rat.num_div_den z).symm

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) : yui_aux_type% "∃ E : (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ≃ₗ[ℚ] (Chevalley.QJ p M y v), ∀ (q : ℚ) (c : Chevalley.J p M y v 0), (E (q ⊗ₜ[Chevalley.R p] c) : ℂ) = q • (c : ℂ)" := by
  letI : IsFractionRing (Chevalley.R p) ℚ := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T006 h_T007
  letI := IsScalarTower.of_compHom (Chevalley.R p) ℚ ℂ
  let S := nonZeroDivisors (Chevalley.R p)
  let f : ℂ →ₗ[Chevalley.R p] ℂ := LinearMap.id
  letI : IsLocalizedModule S f := isLocalizedModule_id S ℂ ℚ
  let L := (Chevalley.J p M y v 0).localized' ℚ S f
  have hL : L = Chevalley.QJ p M y v := by
    dsimp [L, Chevalley.QJ]
    rw [Submodule.localized'_eq_span]
    simp [f]
  let g := (Chevalley.J p M y v 0).toLocalized' ℚ S f
  have hg : IsBaseChange ℚ g := IsLocalizedModule.isBaseChange S ℚ g
  let E := hg.equiv.trans (LinearEquiv.ofEq L (Chevalley.QJ p M y v) hL)
  refine ⟨E, ?_⟩
  intro q c
  simp [E, IsBaseChange.equiv_tmul, g, Submodule.toLocalized', Submodule.toLocalized₀, f]
  rfl

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) : yui_aux_type% "∃ E : (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ≃ₗ[ℚ] (Chevalley.QJ p M y v), ∀ u, Chevalley.qmul p M y v u = (E u : ℂ)" := by
  obtain ⟨E, hE⟩ := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T006 h_T007
  have heq : (Chevalley.QJ p M y v).subtype.comp E.toLinearMap = Chevalley.qmul p M y v := by
    ext c
    change (E ((1 : ℚ) ⊗ₜ[Chevalley.R p] c) : ℂ) = (1 : ℚ) • (c : ℂ)
    exact hE 1 c
  exact ⟨E, fun u => (LinearMap.congr_fun heq u).symm⟩

end Local_T008
open Local_T008 in
theorem T008 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) :
    Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v) := by
  obtain ⟨E, he⟩ := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T006 h_T007
  have hi : Function.Injective (Chevalley.qmul p M y v) := by
    intro a b hab
    apply E.injective
    apply Subtype.ext
    simpa only [← he] using hab
  have hr : LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      rw [he]
      exact (E u).property
    · intro hz
      obtain ⟨u, hu⟩ := E.surjective ⟨z, hz⟩
      exact ⟨u, (he u).trans (congrArg Subtype.val hu)⟩
  letI : Module.Finite (Chevalley.R p) (Chevalley.J p M y v 0) := Module.Finite.of_fg h_T007.2.1
  have ht : FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) := inferInstance
  letI := ht
  have hq : FiniteDimensional ℚ (Chevalley.QJ p M y v) := Module.Finite.equiv E
  exact ⟨hi, hr, ht, hq⟩

namespace Local_T009
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) : yui_aux_type% "∀ c : Chevalley.Index ell → Chevalley.J p M y v 0, ∃ u : Chevalley.MR p M, Chevalley.mu p M u = ∑ i, (c i : ℂ) • Chevalley.e y v i.val" := by
  classical
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V :=
    IsScalarTower.of_compHom (Chevalley.R p) ℂ V
  intro c
  change (∑ i : Chevalley.Index ell, (c i : ℂ) • Chevalley.e y v i.val) ∈
    (Chevalley.muR p M).range
  apply Submodule.sum_mem
  intro i hi
  have hc : (c i : ℂ) ∈ Chevalley.J p M y v i.val := by
    rw [h_T007.1 i]
    exact (c i).property
  exact hc

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) : yui_aux_type% "Nonempty (Chevalley.MR p M ≃ₗ[Chevalley.R p] (Chevalley.Index ell → Chevalley.J p M y v 0))" := by
  classical
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V :=
    IsScalarTower.of_compHom (Chevalley.R p) ℂ V
  let s : (Chevalley.Index ell → Chevalley.J p M y v 0) →ₗ[Chevalley.R p] V :=
    ∑ i : Chevalley.Index ell,
      ((Chevalley.J p M y v 0).subtype.comp (LinearMap.proj i)).smulRight
        (Chevalley.e y v i.val)
  have s_apply (c : Chevalley.Index ell → Chevalley.J p M y v 0) :
      s c = ∑ i, (c i : ℂ) • Chevalley.e y v i.val := by
    simp [s, LinearMap.smulRight_apply]
  have hs (c : Chevalley.Index ell → Chevalley.J p M y v 0) :
      s c ∈ (Chevalley.muR p M).range := by
    rw [s_apply]
    exact @yui_aux_0001 V instV instCV K instK p ell x y h v M h_T004 h_T006 h_T007 c
  let sr := s.codRestrict (Chevalley.muR p M).range hs
  have hbij : Function.Bijective sr := by
    constructor
    · intro a b hab
      have hu : s a ∈ Chevalley.image p M := hs a
      obtain ⟨c, hc, huniq⟩ := (h_T007.2.2.2 (s a)).mp hu
      have ha : (fun i => (a i : ℂ)) = c := by
        apply huniq
        exact ⟨fun i => (a i).property, s_apply a⟩
      have hb : (fun i => (b i : ℂ)) = c := by
        apply huniq
        refine ⟨fun i => (b i).property, ?_⟩
        exact (congrArg Subtype.val hab).trans (s_apply b)
      funext i
      apply Subtype.ext
      exact congrFun (ha.trans hb.symm) i
    · intro u
      have hu : (u : V) ∈ Chevalley.image p M := u.property
      obtain ⟨c, hc, huniq⟩ := (h_T007.2.2.2 (u : V)).mp hu
      refine ⟨fun i => ⟨c i, hc.1 i⟩, ?_⟩
      apply Subtype.ext
      exact (s_apply _).trans hc.2.symm
  exact ⟨(LinearEquiv.ofInjective (Chevalley.muR p M) h_T006.1.2.1).trans
    (LinearEquiv.ofBijective sr hbij).symm⟩

end Local_T009
open Local_T009 in
theorem T009 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) :
    Nonempty ((ℚ ⊗[Chevalley.R p] Chevalley.MR p M) ≃ₗ[ℚ] (Chevalley.Index ell → (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)))) := by
  classical
  obtain ⟨c⟩ := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_T004 h_T006 h_T007
  exact ⟨(c.baseChange (Chevalley.R p) ℚ (Chevalley.MR p M)
    (Chevalley.Index ell → Chevalley.J p M y v 0)).trans
    (TensorProduct.piRight (Chevalley.R p) ℚ ℚ
      (fun _ : Chevalley.Index ell => Chevalley.J p M y v 0))⟩

namespace Local_T010
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) (h_T008 : Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) (h_T009 : Nonempty ((ℚ ⊗[Chevalley.R p] Chevalley.MR p M) ≃ₗ[ℚ] (Chevalley.Index ell → (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0))))) : yui_aux_type% "Module.finrank ℚ (Chevalley.Index ell → (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0))) = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0))" := by
  classical
  letI : FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) := h_T008.2.2.1
  letI : Module.Free ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) := Module.Free.of_divisionRing ℚ _
  letI : ∀ _ : Chevalley.Index ell, Module.Free ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) := fun _ => inferInstance
  letI : ∀ _ : Chevalley.Index ell, Module.Finite ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) := fun _ => h_T008.2.2.1
  have hp := Module.finrank_pi_fintype ℚ (ι := Chevalley.Index ell) (M := fun _ => ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0))
  simpa [h_T004.2.1] using hp

end Local_T010
open Local_T010 in
theorem T010 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) (h_T008 : Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) (h_T009 : Nonempty ((ℚ ⊗[Chevalley.R p] Chevalley.MR p M) ≃ₗ[ℚ] (Chevalley.Index ell → (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0))))) :
    ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1) := by
  classical
  refine ⟨h_T007, h_T008, ?_⟩
  obtain ⟨b⟩ := h_T006.1.2.2.1
  have hdim : Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 := by
    calc
      _ = Fintype.card (Chevalley.Index ell) := Module.finrank_eq_card_basis (b.baseChange ℚ)
      _ = ell.toNat + 1 := h_T004.2.1
  have hprod := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T007 h_T008 h_T009
  have heq : ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) := by
    calc
      _ = Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) := hdim.symm
      _ = Module.finrank ℚ (Chevalley.Index ell → (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0))) := h_T009.some.finrank_eq
      _ = _ := hprod
  have hone : Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 := by
    nlinarith [h_T004.1]
  refine ⟨hdim, heq, hone, ?_⟩
  rw [← h_T008.2.1]
  exact (LinearMap.finrank_range_of_inj h_T008.1).trans hone

namespace Local_T011
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ q : ℚ, q ≠ 0 → ∃ (n : ℤ) (u : ℚ), u ∈ Chevalley.R p ∧ u⁻¹ ∈ Chevalley.R p ∧ u ≠ 0 ∧ q = (p : ℚ) ^ n * u" := by
  intro q hq
  letI : Fact p.Prime := ⟨h_H001.1⟩
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  obtain ⟨a, ha, hpa⟩ := (padicValRat.finite_int_prime_iff (p := p)).mpr hn |>.exists_eq_pow_mul_and_not_dvd
  obtain ⟨b, hb, hpb⟩ := (padicValRat.finite_int_prime_iff (p := p)).mpr hd |>.exists_eq_pow_mul_and_not_dvd
  have ha0 : a ≠ 0 := by intro h; simp [h] at hpa
  have hb0 : b ≠ 0 := by intro h; simp [h] at hpb
  have hRint (z : ℤ) : (z : ℚ) ∈ Chevalley.R p := (Chevalley.R p).algebraMap_mem z
  have hRinv (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : (z : ℚ)⁻¹ ∈ Chevalley.R p :=
    Algebra.subset_adjoin ⟨z, hz, rfl⟩
  refine ⟨(multiplicity (p : ℤ) q.num : ℤ) - (multiplicity (p : ℤ) (q.den : ℤ) : ℤ),
    (a : ℚ) / b, ?_, ?_, div_ne_zero (by exact_mod_cast ha0) (by exact_mod_cast hb0), ?_⟩
  · exact (Chevalley.R p).mul_mem (hRint a) (hRinv b hpb)
  · simpa [div_eq_mul_inv, mul_comm] using (Chevalley.R p).mul_mem (hRint b) (hRinv a hpa)
  · have haq : (q.num : ℚ) = (p : ℚ) ^ multiplicity (p : ℤ) q.num * (a : ℚ) := by exact_mod_cast ha
    have hbq : (q.den : ℚ) = (p : ℚ) ^ multiplicity (p : ℤ) (q.den : ℤ) * (b : ℚ) := by exact_mod_cast hb
    rw [zpow_sub₀ (by exact_mod_cast h_H001.1.ne_zero), zpow_natCast, zpow_natCast]
    calc
      q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
      _ = _ := by rw [haq, hbq]; ring

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∃ (a : ℂ) (s : Finset ℂ), a ≠ 0 ∧ a ∈ Chevalley.J p M y v 0 ∧ s.Nonempty ∧ Submodule.span (Chevalley.R p) (s : Set ℂ) = Chevalley.J p M y v 0 ∧ ∀ z ∈ s, z ≠ 0 ∧ ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) * a = z" := by
  classical
  let J := Chevalley.J p M y v 0
  let L := Chevalley.QJ p M y v
  have hJ : J ≠ ⊥ := h_T010.1.2.2.1
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have haL : a ∈ L := Submodule.subset_span ha
  have haL0 : (⟨a, haL⟩ : L) ≠ 0 := by
    intro hh
    exact ha0 (congrArg Subtype.val hh)
  have hdim : Module.finrank ℚ L = 1 := h_T010.2.2.2.2.2
  have hline : ∀ z ∈ J, ∃ q : ℚ, (q : ℂ) * a = z := by
    intro z hz
    have hzL : z ∈ L := Submodule.subset_span hz
    obtain ⟨q, hq⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℚ) (⟨a, haL⟩ : L) haL0).mp hdim ⟨z, hzL⟩
    exact ⟨q, by simpa [Algebra.smul_def] using congrArg Subtype.val hq⟩
  obtain ⟨t, ht⟩ := h_T010.1.2.1
  let s := t.erase 0
  have hs : Submodule.span (Chevalley.R p) (s : Set ℂ) = J := by
    change Submodule.span (Chevalley.R p) ((t.erase 0 : Finset ℂ) : Set ℂ) = J
    rw [Finset.coe_erase, Submodule.span_sdiff_singleton_zero]
    exact ht
  have hsne : s.Nonempty := by
    by_contra he
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hempty] at hs
    exact hJ (by simpa using hs.symm)
  refine ⟨a, s, ha0, ha, hsne, hs, ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
  have hzJ : z ∈ J := hs ▸ Submodule.subset_span hz
  obtain ⟨q, hq⟩ := hline z hzJ
  refine ⟨hz0, q, ?_, hq⟩
  intro hq0
  apply hz0
  simpa [hq0] using hq.symm

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (r : Chevalley.R p) (b : ℂ), r • b = ((r : ℚ) : ℂ) * b" := by
  intro r b
  rfl

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (k : ℤ), 0 ≤ k → (p : ℚ) ^ k ∈ Chevalley.R p" := by
  intro k hk
  lift k to ℕ using hk
  simpa using (Chevalley.R p).pow_mem ((Chevalley.R p).algebraMap_mem (p : ℤ)) k

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (r t : ℚ) (a : ℂ), (r : ℂ) * ((t : ℂ) * a) = ((r * t : ℚ) : ℂ) * a" := by
  intro r t a
  simp only [Rat.cast_mul, mul_assoc]

theorem yui_aux_0006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (a : ℂ) (s : Finset ℂ), a ≠ 0 → s.Nonempty → (∀ z ∈ s, ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) * a = z) → ∃ b : ℂ, b ≠ 0 ∧ (∀ z ∈ s, ∃ r : Chevalley.R p, r • b = z) ∧ ∃ z ∈ s, ∃ u : ℚ, u ∈ Chevalley.R p ∧ u⁻¹ ∈ Chevalley.R p ∧ u ≠ 0 ∧ z = (u : ℂ) * b" := by
  classical
  intro a s ha hs hrep
  have hf := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T010
  have hsmul := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T010
  have hpow := @yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_T010
  choose q hq0 hqa using (fun z : s => hrep z z.property)
  choose n u hu hui hu0 hqu using (fun z : s => hf (q z) (hq0 z))
  haveI : Nonempty s := by
    obtain ⟨z, hz⟩ := hs
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image n Finset.univ_nonempty
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
  let b : ℂ := (((p : ℚ) ^ n j : ℚ) : ℂ) * a
  have hb0 : b ≠ 0 := mul_ne_zero (by exact_mod_cast zpow_ne_zero (n j) hp0) ha
  refine ⟨b, hb0, ?_, ?_⟩
  · intro z hz
    let i : s := ⟨z, hz⟩
    have hni : 0 ≤ n i - n j := sub_nonneg.mpr (hj i (Finset.mem_univ i))
    let r : Chevalley.R p := ⟨(p : ℚ) ^ (n i - n j) * u i,
      (Chevalley.R p).mul_mem (hpow _ hni) (hu i)⟩
    refine ⟨r, ?_⟩
    rw [hsmul]
    change (((p : ℚ) ^ (n i - n j) * u i : ℚ) : ℂ) *
      ((((p : ℚ) ^ n j : ℚ) : ℂ) * a) = z
    have heq : ((p : ℚ) ^ (n i - n j) * u i) * (p : ℚ) ^ n j = q i := by
      rw [hqu i, zpow_sub₀ hp0]
      field_simp
    calc
      _ = ((((p : ℚ) ^ (n i - n j) * u i) * (p : ℚ) ^ n j : ℚ) : ℂ) * a := by
        exact @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_T010 _ _ a
      _ = (q i : ℂ) * a := by rw [heq]
      _ = z := hqa i
  · refine ⟨j, j.property, u j, hu j, hui j, hu0 j, ?_⟩
    calc
      (j : ℂ) = (q j : ℂ) * a := (hqa j).symm
      _ = (u j : ℂ) * b := by
        rw [hqu j, Rat.cast_mul]
        dsimp [b]
        ring

end Local_T011
open Local_T011 in
theorem T011 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) :
    ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) := by
  classical
  obtain ⟨a, s, ha0, haJ, hsne, hs, hrep⟩ :=
    @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T010
  obtain ⟨b, hb0, hgens, z, hz, u, hu, hui, hu0, hzu⟩ :=
    @yui_aux_0006 V instV instCV K instK p ell x y h v M h_H001 h_T010
      a s ha0 hsne (fun t ht => (hrep t ht).2)
  have hsmul := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T010
  have hzJ : z ∈ Chevalley.J p M y v 0 := hs ▸ Submodule.subset_span hz
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu0
  have hrecover : (⟨u⁻¹, hui⟩ : Chevalley.R p) • z = b := by
    rw [hsmul]
    change ((u⁻¹ : ℚ) : ℂ) * z = b
    rw [hzu, Rat.cast_inv, inv_mul_cancel_left₀ huC]
  have hbJ : b ∈ Chevalley.J p M y v 0 := by
    rw [← hrecover]
    exact (Chevalley.J p M y v 0).smul_mem _ hzJ
  refine ⟨b, hbJ, hb0, le_antisymm ?_ ?_⟩
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro t ht
    obtain ⟨r, hr⟩ := hgens t ht
    rw [← hr]
    exact (Submodule.span (Chevalley.R p) ({b} : Set ℂ)).smul_mem r
      (Submodule.subset_span (Set.mem_singleton b))
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hbJ)

namespace Local_T012
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

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) (h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ)) : yui_aux_type% "Function.Injective (fun r : Chevalley.R p => r • (1 : ℂ))" := by
  intro a b hab
  apply (@yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011)
  change (algebraMap (Chevalley.R p) ℂ a) * 1 = (algebraMap (Chevalley.R p) ℂ b) * 1 at hab
  simpa only [mul_one] using hab

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) (h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ)) : yui_aux_type% "letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ); ∀ b : ℂ, b ≠ 0 → LinearIndependent (Chevalley.R p) (fun i : Chevalley.Index ell => b • Chevalley.e y v i.val)" := by
  classical
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  letI : IsScalarTower (Chevalley.R p) ℂ V := IsScalarTower.of_compHom (Chevalley.R p) ℂ V
  intro b hb
  obtain ⟨E, hE⟩ := h_T004.2.2.2.2.1
  have hli : LinearIndependent ℂ (fun i : Chevalley.Index ell => b • Chevalley.e y v i.val) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hz : ∑ j, (c j * b) • E j = 0 := by
      simpa only [hE, mul_smul] using hc
    have hi := Fintype.linearIndependent_iff.mp E.linearIndependent (fun j => c j * b) hz i
    exact (mul_eq_zero.mp hi).resolve_right hb
  exact hli.restrict_scalars (@yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011)

end Local_T012
open Local_T012 in
theorem T012 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) (h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ)) :
    ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i) := by
  classical
  have hgen := h_T011
  obtain ⟨b, hbJ, hb, hJ⟩ := hgen
  have hdec := @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011 b hJ
  refine ⟨b, hbJ, hb, hJ, hdec, ?_⟩
  letI := Module.compHom V (algebraMap (Chevalley.R p) ℂ)
  have hpre : ∀ i : Chevalley.Index ell, ∃ u : Chevalley.MR p M,
      Chevalley.muR p M u = b • Chevalley.e y v i.val := by
    intro i
    have hbi : b ∈ Chevalley.J p M y v i.val := by
      rw [h_T010.1.1 i]
      exact hbJ
    exact (@yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011 b i.val).mp hbi
  choose w hw using hpre
  have hli : LinearIndependent (Chevalley.R p) w := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hz := congrArg (Chevalley.muR p M) hc
    have hs : ∑ j, c j • (b • Chevalley.e y v j.val) = 0 := by
      simpa only [map_sum, map_smul, hw, map_zero] using hz
    exact Fintype.linearIndependent_iff.mp
      (@yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011 b hb) c hs i
  have hsp : ⊤ ≤ Submodule.span (Chevalley.R p) (Set.range w) := by
    intro u hu
    obtain ⟨c, hc⟩ := (hdec (Chevalley.mu p M u)).mp ⟨u, rfl⟩
    have heq : u = ∑ i, c i • w i := by
      apply h_T006.1.2.1
      change Chevalley.muR p M u = Chevalley.muR p M (∑ i, c i • w i)
      rw [map_sum]
      simp only [map_smul, hw]
      exact hc
    rw [heq]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  intro i
  have hi : Chevalley.mu p M ((Module.Basis.mk hli hsp) i) =
      b • Chevalley.e y v i.val := by
    rw [Module.Basis.mk_apply]
    exact hw i
  refine ⟨hi, ?_⟩
  intro u hu
  exact h_T006.1.2.1 (hu.trans hi.symm)

namespace Local_T013
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∃ ρ : Chevalley.R p →+* K, ∀ a : ℤ, ρ (a : Chevalley.R p) = (a : K)" := by
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

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∀ ρ : Chevalley.R p →+* K,\n  letI := ρ.toAlgebra\n  ∀ (r : Chevalley.R p) (c : K), (algebraMap (Chevalley.R p) K r) * c = ρ r * c" := by
  intro ρ r c
  rfl

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∀ (a : ℤ) (c : K) (u : Chevalley.MR p M),\n ((a : K) * c) ⊗ₜ[ℤ] u = c ⊗ₜ[ℤ] ((a : Chevalley.R p) • u)" := by
  intro a c u
  simpa only [zsmul_eq_mul, Int.cast_smul_eq_zsmul] using
    (TensorProduct.smul_tmul (R := ℤ) a c u)

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∀ ρ : Chevalley.R p →+* K,\n  letI := ρ.toAlgebra\n  TensorProduct.CompatibleSMul ℤ (Chevalley.R p) K (Chevalley.MR p M)" := by
  intro ρ
  letI := ρ.toAlgebra
  letI : CharP K p := h_H001.2.1
  constructor
  intro r c u
  obtain ⟨a,b,hb,hr⟩ := (h_T006.1.1 (r : ℚ)).mp r.property
  have hbQ : (b : ℚ) ≠ 0 := by
    exact_mod_cast (fun h : b = 0 => hb (h ▸ dvd_zero _))
  have hrR : (b : Chevalley.R p) * r = (a : Chevalley.R p) := by
    apply Subtype.ext
    change (b : ℚ) * (r : ℚ) = (a : ℚ)
    rw [hr, mul_div_cancel₀ _ hbQ]
  have hrK : (b : K) * ρ r = (a : K) := by
    simpa using congrArg ρ hrR
  have hbK : (b : K) ≠ 0 := fun hz => hb ((CharP.intCast_eq_zero_iff K p b).mp hz)
  apply (isUnit_iff_ne_zero.mpr hbK).smul_left_cancel.mp
  calc
    (b : K) • (((algebraMap (Chevalley.R p) K r) * c) ⊗ₜ[ℤ] u) =
        ((a : K) * c) ⊗ₜ[ℤ] u := by
      rw [TensorProduct.smul_tmul',
        @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T006 ρ r c]
      congr 1
      change (b : K) * (ρ r * c) = (a : K) * c
      rw [← mul_assoc, hrK]
    _ = c ⊗ₜ[ℤ] ((a : Chevalley.R p) • u) :=
      @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T006 a c u
    _ = (b : K) • (c ⊗ₜ[ℤ] (r • u)) := by
      rw [← hrR, mul_smul, TensorProduct.smul_tmul']
      exact (@yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T006 b c (r • u)).symm

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) : yui_aux_type% "∃ E : (ZMod p) ⊗[ℤ] (Chevalley.MR p M) ≃ₗ[ZMod p] ModN (Chevalley.MR p M) p,\n  ∀ (a : ZMod p) (u : Chevalley.MR p M), E (a ⊗ₜ[ℤ] u) = a • ModN.mkQ p u" := by
  let U := Chevalley.MR p M
  let F : (ZMod p) ⊗[ℤ] U →ₗ[ZMod p] ModN U p :=
    (ModN.mkQ p).toIntLinearMap.liftBaseChange (ZMod p)
  let j : U →+ (ZMod p) ⊗[ℤ] U :=
    (TensorProduct.mk ℤ (ZMod p) U 1).toAddMonoidHom
  have hj (u : U) : p • j u = 0 := by
    change p • ((1 : ZMod p) ⊗ₜ[ℤ] u) = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), TensorProduct.smul_tmul']
    simp
  let G : ModN U p →ₗ[ZMod p] (ZMod p) ⊗[ℤ] U :=
    ModN.liftEquiv'.symm ⟨j,hj⟩
  have hG (u : U) : G (ModN.mkQ p u) = (1 : ZMod p) ⊗ₜ[ℤ] u := rfl
  have hFG : F.comp G = LinearMap.id := by
    apply LinearMap.ext
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H u =>
      change F (G (ModN.mkQ p u)) = ModN.mkQ p u
      rw [hG]
      simp [F]
  have hGF : G.comp F = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a u
    change G (a • ModN.mkQ p u) = a ⊗ₜ[ℤ] u
    rw [map_smul, hG, TensorProduct.smul_tmul']
    simp
  refine ⟨LinearEquiv.ofLinear F G hFG hGF, ?_⟩
  intro a u
  rfl

end Local_T013
open Local_T013 in
theorem T013 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) :
    Chevalley.reductions K p M := by
  classical
  unfold Chevalley.reductions
  refine ⟨h_H001.2.1, ?_⟩
  letI : CharP K p := h_H001.2.1
  letI := ZMod.algebra K p
  obtain ⟨ρ,hρ⟩ := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T006
  refine ⟨ρ,hρ,?_⟩
  letI := ρ.toAlgebra
  let Φ : Chevalley.VK K M ≃ₗ[K] (K ⊗[Chevalley.R p] Chevalley.MR p M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (Chevalley.R p) K K M).symm
  refine ⟨Φ, ?_, ?_⟩
  · intro c m
    rfl
  · letI : TensorProduct.CompatibleSMul ℤ (Chevalley.R p) K (Chevalley.MR p M) :=
      @yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_T006 ρ
    let D : (K ⊗[Chevalley.R p] Chevalley.MR p M) ≃ₗ[K]
        (K ⊗[ℤ] Chevalley.MR p M) :=
      TensorProduct.equivOfCompatibleSMul ℤ (Chevalley.R p) K K (Chevalley.MR p M)
    obtain ⟨E,hE⟩ := @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_T006
    let Ψ : (K ⊗[Chevalley.R p] Chevalley.MR p M) ≃ₗ[K]
        (K ⊗[ZMod p] ModN (Chevalley.MR p M) p) :=
      D.trans ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        ℤ (ZMod p) K K (Chevalley.MR p M)).symm.trans
        (E.baseChange (ZMod p) K _ _))
    refine ⟨Ψ, ?_⟩
    intro c u
    change c ⊗ₜ[ZMod p] E ((1 : ZMod p) ⊗ₜ[ℤ] u) =
      c ⊗ₜ[ZMod p] ModN.mkQ p u
    rw [hE, one_smul]

namespace Local_T014
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

theorem yui_aux_0015 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) : yui_aux_type% "∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → ∀ i j, Chevalley.stable W (Chevalley.matrixK K ell M x y i j)" := by
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

end Local_T014
open Local_T014 in
theorem T014 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v))) (h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j))) (h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i)) (h_T013 : Chevalley.reductions K p M) :
    0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ (Chevalley.reductions K p M) ∧ (∃ β : Module.Basis (Chevalley.Index ell) K (Chevalley.VK K M), Chevalley.stringActions ell (Chevalley.opK K M x) (Chevalley.opK K M y) (Chevalley.opK K M h) (Chevalley.basisVec β) ∧ Chevalley.dividedActions ell (fun r => Chevalley.opK K M (Chevalley.dp x r)) (fun r => Chevalley.opK K M (Chevalley.dp y r)) (Chevalley.basisVec β) ∧ (∀ r : ℕ, r ≤ ell.toNat → (r.factorial : K) ≠ 0 ∧ Chevalley.opK K M (Chevalley.dp x r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M x ^ r ∧ Chevalley.opK K M (Chevalley.dp y r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M y ^ r) ∧ (∀ i j : Chevalley.Index ell, (Nat.choose ell.toNat j.val : K) ≠ 0 ∧ Chevalley.matrixK K ell M x y i j = Chevalley.unitOp β i j) ∧ (∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → ∀ i j, Chevalley.stable W (Chevalley.matrixK K ell M x y i j))) := by
  classical
  obtain ⟨β, hβ⟩ := @yui_aux_0006 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013
  have hactions := @yui_aux_0007 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 β hβ
  refine ⟨h_T004.1, h_T004.2.1, h_T013, β, hactions.1, hactions.2, ?_, ?_, ?_⟩
  · exact @yui_aux_0013 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013
  · exact @yui_aux_0014 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013 β hβ
  · exact @yui_aux_0015 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013

theorem T015 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T014 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ (Chevalley.reductions K p M) ∧ (∃ β : Module.Basis (Chevalley.Index ell) K (Chevalley.VK K M), Chevalley.stringActions ell (Chevalley.opK K M x) (Chevalley.opK K M y) (Chevalley.opK K M h) (Chevalley.basisVec β) ∧ Chevalley.dividedActions ell (fun r => Chevalley.opK K M (Chevalley.dp x r)) (fun r => Chevalley.opK K M (Chevalley.dp y r)) (Chevalley.basisVec β) ∧ (∀ r : ℕ, r ≤ ell.toNat → (r.factorial : K) ≠ 0 ∧ Chevalley.opK K M (Chevalley.dp x r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M x ^ r ∧ Chevalley.opK K M (Chevalley.dp y r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M y ^ r) ∧ (∀ i j : Chevalley.Index ell, (Nat.choose ell.toNat j.val : K) ≠ 0 ∧ Chevalley.matrixK K ell M x y i j = Chevalley.unitOp β i j) ∧ (∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → ∀ i j, Chevalley.stable W (Chevalley.matrixK K ell M x y i j)))) :
    Nontrivial (Chevalley.VK K M) ∧ ∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → Chevalley.stable W (Chevalley.opK K M h) → W = ⊥ ∨ W = ⊤ := by
  classical
  rcases h_T014 with ⟨hn, hcard, hred, β, hstr, hdiv, hfac, hmat, hinv⟩
  constructor
  · let i₀ : Chevalley.Index ell := ⟨0, hn⟩
    exact nontrivial_of_ne (β i₀) 0 (β.ne_zero i₀)
  · intro W hx hy hh
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      have hc : ∃ j, β.coord j w ≠ 0 := by
        by_contra hc
        apply hw0
        apply β.forall_coord_eq_zero_iff.mp
        intro j
        by_contra hj
        exact hc ⟨j, hj⟩
      obtain ⟨j, hj⟩ := hc
      apply (Submodule.eq_top_iff_forall_basis_mem β).mpr
      intro i
      have ht : Chevalley.matrixK K ell M x y i j w ∈ W :=
        hinv W hx hy i j w hw
      rw [(hmat i j).2] at ht
      have hs : β.coord j w • β i ∈ W := by
        simpa only [Chevalley.unitOp, LinearMap.smulRight_apply] using ht
      have hi := W.smul_mem (β.coord j w)⁻¹ hs
      simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using hi

set_option Elab.async false in
theorem P (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (ell : ℂ) • w) ∧ (∀ W : Submodule ℂ V, Chevalley.stable W x → Chevalley.stable W y → Chevalley.stable W h → W = ⊥ ∨ W = ⊤)) (h_H003 : v ≠ 0 ∧ x v = 0 ∧ h v = (ell : ℂ) • v) (h_H004 : (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (B : Module.Basis (Fin d) ℂ V), ∀ i, (b i : V) = B i) ∧ (∀ r : ℕ, Chevalley.preserves M (Chevalley.dp x r) ∧ Chevalley.preserves M (Chevalley.dp y r))) :
    Nontrivial (Chevalley.VK K M) ∧ ∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → Chevalley.stable W (Chevalley.opK K M h) → W = ⊥ ∨ W = ⊤ := by
  have h_T001 : (∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v)) := @T001 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003
  have h_T002 : ∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val := @T002 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H003 h_T001
  have h_T003 : (∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v) := @T003 V instV instCV K instK p ell x y h v M h_H001 h_H003 h_T001 h_T002
  have h_T004 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ Module.finrank ℂ V = ell.toNat + 1 ∧ ((∀ t : ℕ, h ((y ^ t) v) = ((ell : ℂ) - 2 * (t : ℂ)) • ((y ^ t) v)) ∧ (∀ t : ℕ, 0 < t → x ((y ^ t) v) = ((t : ℂ) * ((ell : ℂ) - (t : ℂ) + 1)) • ((y ^ (t - 1)) v))) ∧ (∃ b : Module.Basis (Chevalley.Index ell) ℂ V, ∀ i, b i = Chevalley.e y v i.val) ∧ ((∀ t : ℕ, ell.toNat < t → (y ^ t) v = 0) ∧ Chevalley.stringActions ell x y h (Chevalley.e y v) ∧ Chevalley.dividedActions ell (Chevalley.dp x) (Chevalley.dp y) (Chevalley.e y v)) := @T004 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_T001 h_T002 h_T003
  have h_T005 : (∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u)) := @T005 V instV instCV K instK p ell x y h v M h_H001 h_H002 h_H004 h_T004
  have h_T006 : ((∀ q : ℚ, q ∈ Chevalley.R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ Function.Injective (Chevalley.mu p M) ∧ Nonempty (Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M)) ∧ Submodule.span ℂ (Chevalley.image p M) = ⊤ ∧ (∀ r : ℕ, Chevalley.inImage p M (Chevalley.dp x r) ∧ Chevalley.inImage p M (Chevalley.dp y r)) ∧ Chevalley.preserves M x ∧ Chevalley.preserves M y ∧ Chevalley.preserves M h ∧ (∀ (r : ℕ) (u : Chevalley.MR p M), Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp x r)).baseChange (Chevalley.R p)) u) = Chevalley.dp x r (Chevalley.mu p M u) ∧ Chevalley.mu p M (((Chevalley.latticeOp M (Chevalley.dp y r)).baseChange (Chevalley.R p)) u) = Chevalley.dp y r (Chevalley.mu p M u))) ∧ (∀ (b : Module.Basis (Chevalley.Index ell) ℂ V), (∀ i, b i = Chevalley.e y v i.val) → ∀ i j : Chevalley.Index ell, IsUnit (Nat.choose ell.toNat j.val : Chevalley.R p) ∧ Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat = Chevalley.unitOp b (Fin.last ell.toNat) (Fin.last ell.toNat) ∧ Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) = Chevalley.unitOp b i (Fin.last ell.toNat) ∧ (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val) = (Nat.choose ell.toNat j.val : ℂ) • Chevalley.unitOp b (Fin.last ell.toNat) j ∧ Chevalley.unitOp b i j = ((Nat.choose ell.toNat j.val : ℂ)⁻¹) • (Chevalley.dp x (ell.toNat - i.val) * (Chevalley.dp y ell.toNat * Chevalley.dp x ell.toNat) * Chevalley.dp y (ell.toNat - j.val)) ∧ Chevalley.inImage p M (Chevalley.unitOp b i j)) := @T006 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T005
  have h_T007 : (∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val) := @T007 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006
  have h_T008 : Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v) := @T008 V instV instCV K instK p ell x y h v M h_H001 h_T006 h_T007
  have h_T009 : Nonempty ((ℚ ⊗[Chevalley.R p] Chevalley.MR p M) ≃ₗ[ℚ] (Chevalley.Index ell → (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)))) := @T009 V instV instCV K instK p ell x y h v M h_T004 h_T006 h_T007
  have h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1) := @T010 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T007 h_T008 h_T009
  have h_T011 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) := @T011 V instV instCV K instK p ell x y h v M h_H001 h_T010
  have h_T012 : ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃ c : Chevalley.Index ell → Chevalley.R p, u = ∑ i, (algebraMap (Chevalley.R p) ℂ (c i)) • (b • Chevalley.e y v i.val)) ∧ ∃ B : Module.Basis (Chevalley.Index ell) (Chevalley.R p) (Chevalley.MR p M), ∀ i, Chevalley.mu p M (B i) = b • Chevalley.e y v i.val ∧ (∀ u, Chevalley.mu p M u = b • Chevalley.e y v i.val → u = B i) := @T012 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T010 h_T011
  have h_T013 : Chevalley.reductions K p M := @T013 V instV instCV K instK p ell x y h v M h_H001 h_T006
  have h_T014 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ (Chevalley.reductions K p M) ∧ (∃ β : Module.Basis (Chevalley.Index ell) K (Chevalley.VK K M), Chevalley.stringActions ell (Chevalley.opK K M x) (Chevalley.opK K M y) (Chevalley.opK K M h) (Chevalley.basisVec β) ∧ Chevalley.dividedActions ell (fun r => Chevalley.opK K M (Chevalley.dp x r)) (fun r => Chevalley.opK K M (Chevalley.dp y r)) (Chevalley.basisVec β) ∧ (∀ r : ℕ, r ≤ ell.toNat → (r.factorial : K) ≠ 0 ∧ Chevalley.opK K M (Chevalley.dp x r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M x ^ r ∧ Chevalley.opK K M (Chevalley.dp y r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M y ^ r) ∧ (∀ i j : Chevalley.Index ell, (Nat.choose ell.toNat j.val : K) ≠ 0 ∧ Chevalley.matrixK K ell M x y i j = Chevalley.unitOp β i j) ∧ (∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → ∀ i j, Chevalley.stable W (Chevalley.matrixK K ell M x y i j))) := @T014 V instV instCV K instK p ell x y h v M h_H001 h_T004 h_T006 h_T012 h_T013
  have h_T015 : Nontrivial (Chevalley.VK K M) ∧ ∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → Chevalley.stable W (Chevalley.opK K M h) → W = ⊥ ∨ W = ⊤ := @T015 V instV instCV K instK p ell x y h v M h_H001 h_T014
  exact h_T015

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false

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
