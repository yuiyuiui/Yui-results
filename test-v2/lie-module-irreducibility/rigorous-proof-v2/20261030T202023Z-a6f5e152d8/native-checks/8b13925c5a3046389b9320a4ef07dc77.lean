import Mathlib
open scoped TensorProduct
noncomputable section
namespace LatticeIR
def R (p : ℕ) : Subring ℚ :=
  Subring.closure {q : ℚ | ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)}
instance ratModule (V : Type*) [AddCommGroup V] [Module ℂ V] : Module ℚ V :=
  Module.compHom V (algebraMap ℚ ℂ)
instance complexAlgebra (p : ℕ) : Algebra (R p) ℂ :=
  ((algebraMap ℚ ℂ).comp (R p).subtype).toAlgebra
instance localModule (p : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V] : Module (R p) V :=
  Module.compHom V (algebraMap (R p) ℂ)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def dp (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r
def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dp y i v
def MR (p : ℕ) (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
def mu (p : ℕ) (M : Submodule ℤ V) : MR p M →ₗ[R p] V :=
  M.subtype.liftBaseChange (R p)
def VK (K : Type*) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
end LatticeIR

set_option autoImplicit false
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) => LatticeIR.mu p M)
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) => Module (LatticeIR.R p) ℚ)
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) => IsScalarTower ℤ (LatticeIR.R p) V)
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) => IsScalarTower (LatticeIR.R p) ℚ ℂ)
