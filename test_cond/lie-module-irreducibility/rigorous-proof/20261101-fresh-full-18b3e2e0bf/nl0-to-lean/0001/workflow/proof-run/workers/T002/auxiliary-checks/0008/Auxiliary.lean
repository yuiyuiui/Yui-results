import Mathlib
universe u v
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
def chevalley (x y h : SL) : Prop :=
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
  0 ≤ l ∧ 0 < l + 1 ∧ 0 < l.toNat + 1 ∧ Fintype.card (Ind l) = l.toNat + 1 ∧
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

instance locRatComplexTower (p : ℕ) : IsScalarTower (loc p) ℚ ℂ :=
  IsScalarTower.of_algebraMap_eq' rfl
def locSpec (p : ℕ) : Prop :=
  ∀ q : ℚ, q ∈ loc p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ) / (d : ℚ)
def latticeFacts (p : ℕ) (l : ℤ) (x y h : Module.End ℂ V) (M : Submodule ℤ V) : Prop :=
  locSpec p ∧ Nonempty (IntegralOps x y h M) ∧
  (∀ A : IntegralOps x y h M,
    A.ih * A.ix - A.ix * A.ih = (2 : ℤ) • A.ix ∧
    A.ih * A.iy - A.iy * A.ih = (-2 : ℤ) • A.iy ∧
    A.ix * A.iy - A.iy * A.ix = A.ih) ∧
  Function.Injective (iota p M) ∧
  Nonempty (Basis (Ind l) (loc p) (MR p M)) ∧
  Module.finrank (loc p) (MR p M) = l.toNat + 1 ∧
  Submodule.span ℂ (Set.range (iota p M)) = ⊤ ∧
  ∀ (r : ℕ) (z : V), z ∈ (iota p M).range →
    divided x r z ∈ (iota p M).range ∧ divided y r z ∈ (iota p M).range
def matrixFacts (p : ℕ) (l : ℤ) (x y : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  ∀ b : Basis (Ind l) ℂ V, (∀ i, b i = e y v i.val) →
  ∀ i j : Ind l,
    IsUnit (Nat.choose l.toNat j.val : loc p) ∧
    (Nat.choose l.toNat j.val : ℚ)⁻¹ ∈ loc p ∧
    (∀ z ∈ (iota p M).range, matrixUnit b i j z ∈ (iota p M).range) ∧
    matrixUnit b i j = (Nat.choose l.toNat j.val : ℂ)⁻¹ •
      (divided x (l.toNat-i.val) * divided y l.toNat * divided x l.toNat * divided y (l.toNat-j.val)) ∧
    divided y l.toNat * divided x l.toNat = matrixUnit b (Fin.last l.toNat) (Fin.last l.toNat) ∧
    divided x (l.toNat-i.val) * matrixUnit b (Fin.last l.toNat) (Fin.last l.toNat) =
      matrixUnit b i (Fin.last l.toNat) ∧
    matrixUnit b (Fin.last l.toNat) (Fin.last l.toNat) * divided y (l.toNat-j.val) =
      (Nat.choose l.toNat j.val : ℂ) • matrixUnit b (Fin.last l.toNat) j
def localizationFacts (p : ℕ) (l : ℤ) (x y h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  latticeFacts p l x y h M ∧ matrixFacts p l x y v M
def coordinateFacts (p : ℕ) (l : ℤ) (y : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (∀ i : Ind l, Jcoord p M y v i.val = Jcoord p M y v 0) ∧
  Jcoord p M y v 0 ≠ ⊥ ∧ (Jcoord p M y v 0).FG ∧
  ∃ d : (Ind l → Jcoord p M y v 0) ≃ₗ[loc p] (iota p M).range,
    ∀ c, (d c : V) = ∑ i : Ind l, (c i : ℂ) • e y v i.val
def rationalMu (p : ℕ) (y : Module.End ℂ V) (v : V) (M : Submodule ℤ V) :
    ℚ ⊗[loc p] (Jcoord p M y v 0) →ₗ[ℚ] ℂ :=
  LinearMap.liftBaseChange ℚ (Jcoord p M y v 0).subtype
def rationalFacts (p : ℕ) (y : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  FiniteDimensional ℚ (ℚ ⊗[loc p] (Jcoord p M y v 0)) ∧
  Module.finrank ℚ (ℚ ⊗[loc p] (Jcoord p M y v 0)) = 1 ∧
  Function.Injective (rationalMu p y v M)
def principalFacts (p : ℕ) (l : ℤ) (y : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  ∃ b : ℂ, b ≠ 0 ∧ b ∈ Jcoord p M y v 0 ∧
    Jcoord p M y v 0 = Submodule.span (loc p) ({b} : Set ℂ) ∧
    ∃ a : Basis (Ind l) (loc p) (MR p M), ∀ i, iota p M (a i) = b • e y v i.val
def commonFacts (p : ℕ) (l : ℤ) (y : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  coordinateFacts p l y v M ∧ rationalFacts p y v M ∧ principalFacts p l y v M
def scalarFacts (p : ℕ) (K : Type*) [Field K] (M : Submodule ℤ V) : Prop :=
  ∃ (bar : loc p →+* K) (eps : ZMod p →+* K),
    (∀ (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d) (r : loc p),
      (r : ℚ) = (a : ℚ) / (d : ℚ) → bar r = (a : K) / (d : K)) ∧
    (letI : Algebra (loc p) K := bar.toAlgebra
     letI : Algebra (ZMod p) K := eps.toAlgebra
     ∃ (Phi : VK K M ≃ₗ[K] (K ⊗[loc p] MR p M))
       (Psi : (K ⊗[loc p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p)),
       (∀ (c : K) (m : M), Phi (c ⊗ₜ[ℤ] m) = c ⊗ₜ[loc p] (1 ⊗ₜ[ℤ] m)) ∧
       (∀ (c : K) (s : loc p) (m : M),
         Phi.symm (c ⊗ₜ[loc p] (s ⊗ₜ[ℤ] m)) = (c * bar s) ⊗ₜ[ℤ] m) ∧
       (∀ (c : K) (u : MR p M), Psi (c ⊗ₜ[loc p] u) = c ⊗ₜ[ZMod p] ModN.mkQ p u) ∧
       (∀ (c : K) (u : MR p M), Psi.symm (c ⊗ₜ[ZMod p] ModN.mkQ p u) = c ⊗ₜ[loc p] u) ∧
       ∀ f : Module.End ℤ M,
         Phi.toLinearMap.comp (f.baseChange K) =
           ((f.baseChange (loc p)).baseChange K).comp Phi.toLinearMap ∧
         ∃ F : Module.End (ZMod p) (ModN (MR p M) p),
           (∀ u : MR p M, F (ModN.mkQ p u) = ModN.mkQ p (f.baseChange (loc p) u)) ∧
           Psi.toLinearMap.comp ((f.baseChange (loc p)).baseChange K) =
             (F.baseChange K).comp Psi.toLinearMap)
def extendBasis {A W : Type*} [Semiring A] [AddCommMonoid W] [Module A W]
    (l : ℤ) (b : Basis (Ind l) A W) (i : ℕ) : W :=
  if hi : i < l.toNat+1 then b ⟨i,hi⟩ else 0
def reductionWitness (p : ℕ) (l : ℤ) (K : Type*) [Field K]
    {x y h : Module.End ℂ V} {M : Submodule ℤ V} (A : IntegralOps x y h M)
    (beta : Basis (Ind l) K (VK K M)) (T : Ind l → Ind l → Module.End K (VK K M)) : Prop :=
  Module.finrank K (VK K M) = l.toNat+1 ∧ 0 < l.toNat+1 ∧
  generatorFormulas l (A.ix.baseChange K) (A.iy.baseChange K) (A.ih.baseChange K) (extendBasis l beta) ∧
  (∀ i j k : Ind l, T i j (beta k) = if k = j then beta i else 0) ∧
  (∀ i j : Ind l, (Nat.choose l.toNat j.val : K) ≠ 0 ∧
    T i j = (Nat.choose l.toNat j.val : K)⁻¹ •
      ((A.iX (l.toNat-i.val)).baseChange K * (A.iY l.toNat).baseChange K *
        (A.iX l.toNat).baseChange K * (A.iY (l.toNat-j.val)).baseChange K)) ∧
  ∀ r : ℕ, r ≤ l.toNat →
    (r.factorial : K) ≠ 0 ∧
    (A.iX r).baseChange K = (r.factorial : K)⁻¹ • (A.ix.baseChange K)^r ∧
    (A.iY r).baseChange K = (r.factorial : K)⁻¹ • (A.iy.baseChange K)^r
def reductionFacts (p : ℕ) (l : ℤ) (K : Type*) [Field K]
    (x y h : Module.End ℂ V) (M : Submodule ℤ V) : Prop :=
  scalarFacts p K M ∧
  ∀ A : IntegralOps x y h M, ∃ beta T, reductionWitness p l K A beta T
def invariantFacts (p : ℕ) (l : ℤ) (K : Type*) [Field K]
    (x y h : Module.End ℂ V) (M : Submodule ℤ V) : Prop :=
  Nontrivial (VK K M) ∧
  ∀ A : IntegralOps x y h M, ∃ beta T, reductionWitness p l K A beta T ∧
    ∀ W : Submodule K (VK K M),
      stable W (A.ix.baseChange K) → stable W (A.iy.baseChange K) →
      stable W (A.ih.baseChange K) → ∀ i j : Ind l, stable W (T i j)
def endpoint (K : Type*) [Field K] (x y h : Module.End ℂ V) (M : Submodule ℤ V) : Prop :=
  ∃ A : IntegralOps x y h M, Nontrivial (VK K M) ∧
    ∀ W : Submodule K (VK K M),
      stable W (A.ix.baseChange K) → stable W (A.iy.baseChange K) →
      stable W (A.ih.baseChange K) → W = ⊥ ∨ W = ⊤
end Reduction

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "(∀ i : ℕ, (act h) (Reduction.e (act y) v0 i) = ((l : ℂ) - 2 * (i : ℂ)) • Reduction.e (act y) v0 i) ∧ (∀ i : ℕ, (act y) (Reduction.e (act y) v0 i) = ((i : ℂ) + 1) • Reduction.e (act y) v0 (i+1)) ∧ (act x) (Reduction.e (act y) v0 0) = 0 ∧ (∀ i : ℕ, (act x) (Reduction.e (act y) v0 (i+1)) = ((l : ℂ) - (i : ℂ)) • Reduction.e (act y) v0 i)" := by
  have hf (i : ℕ) : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have he (i : ℕ) : Reduction.e (act y) v0 i = (i.factorial : ℂ)⁻¹ • ((act y)^i) v0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [he, map_smul, h_T001.1 i, smul_comm]
  · intro i
    rw [he, he, map_smul, ← Module.End.mul_apply, ← pow_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_smul]
    congr 1
    field_simp
  · simpa [Reduction.e, Reduction.divided] using h_H006.2.1
  · intro i
    rw [he, map_smul, h_T001.2 (i+1) (by omega), Nat.add_sub_cancel, he]
    simp only [smul_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    congr 1
    field_simp
    <;> ring

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "(l.toNat : ℂ) = (l : ℂ)" := by
  exact_mod_cast Int.toNat_of_nonneg h_H003.1

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V) (c : Reduction.Ind l → ℂ) (i : Reduction.Ind l), b.repr (∑ j, c j • b j) i = c i" := by
  classical
  intro b c i
  simp [map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem checked (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "∃ b : Basis (Reduction.Ind l) ℂ V, (∀ i, b i = Reduction.e (act y) v0 i.val) ∧ (∀ t : ℕ, l.toNat + 1 ≤ t → ((act y)^t) v0 = 0)" := by
  classical
  have F := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  have hl : (l.toNat : ℂ) = (l : ℂ) := @yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  have hn : ∀ i : ℕ, i ≤ l.toNat → Reduction.e (act y) v0 i ≠ 0 := by
    intro i
    induction i with
    | zero => simpa [Reduction.e, Reduction.divided] using h_H006.1
    | succ i ih =>
      intro hi hz
      have hh := F.2.2.2 i
      rw [hz, map_zero] at hh
      have hc : (l : ℂ) - (i : ℂ) ≠ 0 := by
        rw [← hl, sub_ne_zero]
        exact_mod_cast (show l.toNat ≠ i by omega)
      exact (smul_ne_zero hc (ih (by omega))) hh.symm
  have hinj : Function.Injective (fun i : Reduction.Ind l => (l : ℂ) - 2 * (i.val : ℂ)) := by
    intro i j hij
    apply Fin.ext
    have : (i.val : ℂ) = (j.val : ℂ) := by linear_combination - (1/2 : ℂ) * hij
    exact_mod_cast this
  have LI : LinearIndependent ℂ (fun i : Reduction.Ind l => Reduction.e (act y) v0 i.val) :=
    (act h).eigenvectors_linearIndependent' _ hinj _ (fun i => ⟨(Module.End.mem_eigenspace_iff).2 (F.1 i.val), hn i.val (by have := i.isLt; omega)⟩)
  letI : FiniteDimensional ℂ V := h_H004.1
  let b := basisOfLinearIndependentOfCardEqFinrank LI (by simpa [Reduction.Ind] using h_H004.2.1.symm)
  have hb (i : Reduction.Ind l) : b i = Reduction.e (act y) v0 i.val := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank LI _) i
  have hz : ((act y)^(l.toNat+1)) v0 = 0 := by
    let z := ((act y)^(l.toNat+1)) v0
    have hzweight : (act h) z = ((l : ℂ) - 2 * ((l.toNat+1 : ℕ) : ℂ)) • z := h_T001.1 _
    have hd : ∀ i : Reduction.Ind l, b.repr z i = 0 := by
      intro i
      have heq := congrArg (fun w : V => b.repr w i) hzweight
      have hexp : (act h) z = ∑ j : Reduction.Ind l, (b.repr z j * ((l : ℂ) - 2 * (j.val : ℂ))) • b j := by
        conv_lhs => rw [← b.sum_repr z]
        simp only [map_sum, map_smul, hb, F.1, smul_smul]
      rw [hexp] at heq
      rw [@yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001 b _ i] at heq
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at heq
      have hc : ((l : ℂ) - 2 * (i.val : ℂ)) - ((l : ℂ) - 2 * ((l.toNat+1 : ℕ) : ℂ)) ≠ 0 := by
        intro hc
        have hh : (i.val : ℂ) = ((l.toNat+1 : ℕ) : ℂ) := by linear_combination -(1/2 : ℂ) * hc
        have hh' : i.val = l.toNat+1 := by exact_mod_cast hh
        have := i.isLt
        omega
      apply (mul_eq_zero.mp (show b.repr z i * (((l : ℂ) - 2 * (i.val : ℂ)) - ((l : ℂ) - 2 * ((l.toNat+1 : ℕ) : ℂ))) = 0 by linear_combination heq)).resolve_right hc
    apply b.repr.injective
    ext i
    simpa using hd i
  refine ⟨b, hb, ?_⟩
  intro t ht
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Nat.add_comm, pow_add, Module.End.mul_apply, hz, map_zero]
#check @checked
#print axioms checked
end YuiAuxiliary
