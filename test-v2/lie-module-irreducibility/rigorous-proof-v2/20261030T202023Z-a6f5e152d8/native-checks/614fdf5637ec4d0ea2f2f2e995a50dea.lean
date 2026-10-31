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
abbrev MR (p : ℕ) (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
def mu (p : ℕ) (M : Submodule ℤ V) : MR p M →ₗ[R p] V :=
  M.subtype.liftBaseChange (R p)
abbrev VK (K : Type*) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
def image (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) V :=
  LinearMap.range (mu p M)
def Ji (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) : Submodule (R p) ℂ :=
  (image p M).comap ((LinearMap.toSpanSingleton ℂ V (e y v i)).restrictScalars (R p))
def unit {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    {n : ℕ} (B : Module.Basis (Fin n) F W) (i j : Fin n) : Module.End F W :=
  (LinearMap.toSpanSingleton F W (B i)).comp (B.coord j)
def at {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    {n : ℕ} (B : Module.Basis (Fin n) F W) (i : ℕ) : W :=
  if hi : i < n then B ⟨i, hi⟩ else 0
end LatticeIR

set_option autoImplicit false
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) => LatticeIR.Ji p M y v 0)
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) => (inferInstance : IsScalarTower (LatticeIR.R p) ℂ V))
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) => (inferInstance : IsScalarTower ℤ (LatticeIR.R p) V))
#check (fun (p : ℕ) (V : Type) [vadd : AddCommGroup V] [vmod : Module ℂ V] (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) => (inferInstance : IsScalarTower (LatticeIR.R p) ℚ ℂ))
