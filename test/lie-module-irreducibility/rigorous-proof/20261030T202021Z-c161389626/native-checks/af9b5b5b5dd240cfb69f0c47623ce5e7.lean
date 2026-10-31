import Mathlib
open scoped TensorProduct
namespace LR
abbrev L := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ
abbrev R (p : ℕ) := Subring.closure {q : ℚ | ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b}
abbrev C (p : ℕ) := RestrictScalars (R p) ℚ ℂ
abbrev I (l : ℤ) := Fin (l.toNat + 1)
abbrev MR (p : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
abbrev VK (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Submodule ℤ V) := K ⊗[ℤ] M
noncomputable def dp {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V := ((r.factorial : ℂ)⁻¹) • f ^ r
end LR

noncomputable def LR.PhiTest (p : ℕ) (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Submodule ℤ V) (phi : LR.R p →+* K) : Prop :=
letI := phi.toAlgebra
Nonempty (LR.VK K M ≃ₗ[K] K ⊗[LR.R p] LR.MR p M)

set_option autoImplicit false
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => Module (LR.R p) (LR.C p))
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => ∀ phi : LR.R p →+* K, LR.PhiTest p K M phi)
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => ∀ (J : Submodule (LR.R p) (LR.C p)), Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1)
