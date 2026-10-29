import Mathlib

noncomputable section
namespace LR

def localRing (p : ℕ) : Subring ℚ := Subring.closure {q | ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ) / d}
abbrev R (p : ℕ) := ↥(localRing p)
noncomputable instance rRat (p : ℕ) : Algebra (R p) ℚ := (localRing p).subtype.toAlgebra
noncomputable instance rComplex (p : ℕ) : Algebra (R p) ℂ := ((algebraMap ℚ ℂ).comp (localRing p).subtype).toAlgebra
variable {V : Type} [AddCommGroup V] [Module ℂ V]
noncomputable instance rModule (p : ℕ) : Module (R p) V := Module.compHom V (algebraMap (R p) ℂ)
noncomputable instance rTower (p : ℕ) : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V

def vec (y : Module.End ℂ V) (v : V) (i : ℕ) : V := ((i.factorial : ℂ)⁻¹) • (y ^ i) v
def divided (x : Module.End ℂ V) (r : ℕ) : Module.End ℂ V := ((r.factorial : ℂ)⁻¹) • x ^ r
def MR (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) V := Submodule.span (R p) (M : Set V)
def J (p λ : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) : Submodule (R p) ℂ := (MR p M).comap ((LinearMap.toSpanSingleton ℂ V (vec y v i)).restrictScalars (R p))
def unit (λ : ℕ) (b : Module.Basis (Fin (λ+1)) ℂ V) (i j : Fin (λ+1)) : Module.End ℂ V := (b.coord j).smulRight (b i)
abbrev VK (K : Type) [Field K] (M : Submodule ℤ V) := TensorProduct ℤ K M
structure Lift (M : Submodule ℤ V) (f : Module.End ℂ V) where
  map : Module.End ℤ M
  agrees : ∀ m : M, (map m : V) = f m
structure Actions (M : Submodule ℤ V) (x y h : Module.End ℂ V) where
  x : Lift M x
  y : Lift M y
  h : Lift M h
  X : ∀ r : ℕ, Lift M (divided x r)
  Y : ∀ r : ℕ, Lift M (divided y r)
def induced (K : Type) [Field K] (M : Submodule ℤ V) (f : Module.End ℤ M) : Module.End K (VK K M) := f.baseChange K
def pMR (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) (MR p M) := LinearMap.range ((p : R p) • (LinearMap.id : Module.End (R p) (MR p M)))
abbrev QMR (p : ℕ) (M : Submodule ℤ V) := (MR p M) ⧸ pMR p M
end LR

set_option autoImplicit false
#check (fun (p : ℕ) (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (M : Submodule ℤ V) => LR.R p)
#check (fun (p : ℕ) (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (M : Submodule ℤ V) => LR.MR p M)
#check (fun (p : ℕ) (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (M : Submodule ℤ V) => Module.Basis (Fin 3) (LR.R p) (LR.MR p M))
