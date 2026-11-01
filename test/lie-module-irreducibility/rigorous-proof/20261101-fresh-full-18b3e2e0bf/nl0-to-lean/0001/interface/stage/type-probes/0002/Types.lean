import Mathlib
open scoped TensorProduct
noncomputable section
namespace Reduction
def loc (p : ℕ) : Subring ℚ :=
  Subring.closure {q : ℚ | ∃ d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (d : ℚ)⁻¹}
instance locComplex (p : ℕ) : Algebra (loc p) ℂ :=
  ((Rat.castHom ℂ).comp (loc p).subtype).toAlgebra
abbrev Ind (l : ℤ) := Fin (l.toNat + 1)
abbrev MR {V : Type*} [AddCommGroup V] [Module ℂ V] (p : ℕ) (M : Submodule ℤ V) :=
  (loc p) ⊗[ℤ] M
abbrev VK {V : Type*} [AddCommGroup V] [Module ℂ V] (K : Type*) [Field K] (M : Submodule ℤ V) :=
  K ⊗[ℤ] M
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
instance locModule (p : ℕ) : Module (loc p) V := Module.compHom V (algebraMap (loc p) ℂ)
instance locTower (p : ℕ) : IsScalarTower (loc p) ℂ V := ⟨fun _ _ _ => mul_smul _ _ _⟩
def iota (p : ℕ) (M : Submodule ℤ V) : MR p M →ₗ[loc p] V :=
  LinearMap.liftBaseChange (loc p) M.subtype
end Reduction

set_option autoImplicit false
def __probe_0 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => (@Reduction.iota))
def __probe_1 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => ((Reduction.iota p M).range))
def __probe_2 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => (Module.finrank (Reduction.loc p) (Reduction.MR p M) = 1))
def __probe_3 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => ((Module.End ℂ V)))
def __probe_4 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => ((LieAlgebra.SpecialLinear.sl (Fin 2) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V))
def __probe_5 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => ((LinearMap.liftBaseChange (Reduction.loc p) (LinearMap.id : ℂ →ₗ[ℤ] ℂ))))
def __probe_6 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => (∀ (b : Basis (Fin 2) ℂ V) (i j : Fin 2), LinearMap.smulRight (b.coord j) (b i) = (0 : Module.End ℂ V)))
def __probe_7 :=
  (fun (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (K : Type) [fieldK : Field K] (p : ℕ) (M : Submodule ℤ V) => (∀ (f : Module.End ℤ M), f.baseChange K = f.baseChange K))
