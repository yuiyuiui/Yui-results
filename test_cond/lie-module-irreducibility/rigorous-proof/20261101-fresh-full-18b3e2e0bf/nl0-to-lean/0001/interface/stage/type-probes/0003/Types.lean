import Mathlib
open scoped TensorProduct
open Module
attribute [local instance 100] LieRing.ofAssociativeRing
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

abbrev SL := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ
def divided (a : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • a ^ r
def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V := divided y i v
def stable {A W : Type*} [Semiring A] [AddCommMonoid W] [Module A W]
    (U : Submodule A W) (f : Module.End A W) : Prop := ∀ w ∈ U, f w ∈ U
def matrixUnit {A W ι : Type*} [Semiring A] [AddCommMonoid W] [Module A W]
    (b : Basis ι A W) (i j : ι) : Module.End A W :=
  LinearMap.smulRight (b.coord j) (b i)
def Jcoord (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) :
    Submodule (loc p) ℂ :=
  (iota p M).range.comap (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[loc p] ℂ) (e y v i))
structure IntegralOps (x y h : Module.End ℂ V) (M : Submodule ℤ V) where
  ix : Module.End ℤ M
  iy : Module.End ℤ M
  ih : Module.End ℤ M
  iX : ℕ → Module.End ℤ M
  iY : ℕ → Module.End ℤ M
  ix_spec : ∀ m : M, (ix m : V) = x m
  iy_spec : ∀ m : M, (iy m : V) = y m
  ih_spec : ∀ m : M, (ih m : V) = h m
  iX_spec : ∀ (r : ℕ) (m : M), (iX r m : V) = divided x r m
  iY_spec : ∀ (r : ℕ) (m : M), (iY r m : V) = divided y r m
def admissible (M : Submodule ℤ V) (x y : Module.End ℂ V) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (a : Basis ι ℤ M) (b : Basis ι ℂ V),
    ∀ i, (a i : V) = b i) ∧
  (∀ (r : ℕ) (m : M), divided x r m ∈ M ∧ divided y r m ∈ M)
def highestModule (l : ℤ) (act : SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x h : SL) : Prop :=
  FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l.toNat + 1 ∧ Nontrivial V ∧
  (∀ U : Submodule ℂ V, (∀ z : SL, stable U (act z)) → U = ⊥ ∨ U = ⊤) ∧
  ∃ w : V, w ≠ 0 ∧ act x w = 0 ∧ act h w = (l : ℂ) • w
def chevallley (x y h : SL) : Prop :=
  IsSl2Triple h x y ∧ Submodule.span ℂ ({x, y, h} : Set SL) = ⊤
def strings (l : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  (∀ t : ℕ, h ((y ^ t) v) = ((l : ℂ) - 2 * (t : ℂ)) • (y ^ t) v) ∧
  ∀ t : ℕ, 1 ≤ t → x ((y ^ t) v) =
    ((t : ℂ) * ((l : ℂ) - (t : ℂ) + 1)) • (y ^ (t - 1)) v
def generatorFormulas {A W : Type*} [Field A] [AddCommGroup W] [Module A W]
    (l : ℤ) (x y h : Module.End A W) (f : ℕ → W) : Prop :=
  x (f 0) = 0 ∧
  (∀ i : ℕ, i < l.toNat → x (f (i+1)) = ((l : A) - (i : A)) • f i) ∧
  (∀ i : ℕ, i < l.toNat → y (f i) = ((i : A) + 1) • f (i+1)) ∧
  y (f l.toNat) = 0 ∧
  (∀ i : ℕ, i ≤ l.toNat → h (f i) = ((l : A) - 2 * (i : A)) • f i)
def basisFacts (l : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  0 < l.toNat + 1 ∧ Fintype.card (Ind l) = l.toNat + 1 ∧
  (∃ b : Basis (Ind l) ℂ V, ∀ i, b i = e y v i.val) ∧
  strings l x y h v ∧
  (∀ t : ℕ, l.toNat + 1 ≤ t → (y ^ t) v = 0) ∧
  generatorFormulas l x y h (e y v) ∧
  (∀ (r : ℕ) (i : Ind l),
    divided x r (e y v i.val) =
      if r ≤ i.val then (Nat.choose (l.toNat - i.val + r) r : ℂ) • e y v (i.val-r) else 0) ∧
  (∀ (r : ℕ) (i : Ind l),
    divided y r (e y v i.val) =
      if i.val + r ≤ l.toNat then (Nat.choose (i.val+r) r : ℂ) • e y v (i.val+r) else 0)
end Reduction

set_option autoImplicit false
def __probe_0 :=
  (@Reduction.basisFacts)
def __probe_1 :=
  (@Reduction.Jcoord)
def __probe_2 :=
  (@Reduction.IntegralOps)
def __probe_3 :=
  (@Reduction.admissible)
def __probe_4 :=
  (@Reduction.highestModule)
