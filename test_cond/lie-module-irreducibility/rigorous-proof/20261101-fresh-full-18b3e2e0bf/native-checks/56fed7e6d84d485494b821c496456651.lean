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
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (F : Module.End ℂ V) (s : Reduction.loc p) (z : V), F (s • z) = s • F z" := by
  intro F s z
  change F ((algebraMap (Reduction.loc p) ℂ s) • z) = (algebraMap (Reduction.loc p) ℂ s) • F z
  exact F.map_smul _ _

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (f : Module.End ℤ M) (F : Module.End ℂ V), (∀ m : M, (f m : V) = F m) → ∀ u : Reduction.MR p M, Reduction.iota p M (f.baseChange (Reduction.loc p) u) = F (Reduction.iota p M u)" := by
  intro f F hf u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    simp only [LinearMap.baseChange_tmul, Reduction.iota, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, hf]
    exact (yui_aux_0001 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 F s m).symm
  | add u w hu hw => simp only [map_add, hu, hw]

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (bar : Reduction.loc p →+* K), letI : Algebra (Reduction.loc p) K := bar.toAlgebra; ∀ (Phi : Reduction.VK K M ≃ₗ[K] (K ⊗[Reduction.loc p] Reduction.MR p M)) (f : Module.End ℤ M), Phi.toLinearMap.comp (f.baseChange K) = ((f.baseChange (Reduction.loc p)).baseChange K).comp Phi.toLinearMap → ∀ (u w : Reduction.MR p M) (s : Reduction.loc p), f.baseChange (Reduction.loc p) u = s • w → f.baseChange K (Phi.symm (1 ⊗ₜ[Reduction.loc p] u)) = bar s • Phi.symm (1 ⊗ₜ[Reduction.loc p] w)" := by
  intro bar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  intro Phi f hf u w s hu
  apply Phi.injective
  have he := LinearMap.congr_fun hf (Phi.symm (1 ⊗ₜ[Reduction.loc p] u))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul, hu] at he
  rw [he, Phi.map_smul, Phi.apply_symm_apply]
  change (1 : K) ⊗ₜ[Reduction.loc p] (s • w) = bar s • ((1 : K) ⊗ₜ[Reduction.loc p] w)
  rw [TensorProduct.tmul_smul]
  rfl

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (bar : Reduction.loc p →+* K), letI : Algebra (Reduction.loc p) K := bar.toAlgebra; ∀ (Phi : Reduction.VK K M ≃ₗ[K] (K ⊗[Reduction.loc p] Reduction.MR p M)) (f : Module.End ℤ M) (F : Module.End ℂ V), (∀ m : M, (f m : V) = F m) → Phi.toLinearMap.comp (f.baseChange K) = ((f.baseChange (Reduction.loc p)).baseChange K).comp Phi.toLinearMap → ∀ (u w : Reduction.MR p M) (s : Reduction.loc p), F (Reduction.iota p M u) = (algebraMap (Reduction.loc p) ℂ s) • Reduction.iota p M w → f.baseChange K (Phi.symm (1 ⊗ₜ[Reduction.loc p] u)) = bar s • Phi.symm (1 ⊗ₜ[Reduction.loc p] w)" := by
  intro bar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  intro Phi f F hf hPhi u w s he
  apply yui_aux_0003 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 bar Phi f hPhi u w s
  apply h_T004.1.2.2.2.1
  rw [map_smul, yui_aux_0002 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 f F hf]
  exact he

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (bar : Reduction.loc p →+* K), letI : Algebra (Reduction.loc p) K := bar.toAlgebra; ∀ (Phi : Reduction.VK K M ≃ₗ[K] (K ⊗[Reduction.loc p] Reduction.MR p M)) (a : Basis (Reduction.Ind l) (Reduction.loc p) (Reduction.MR p M)) (b : ℂ), (∀ i, Reduction.iota p M (a i) = b • Reduction.e (act y) v0 i.val) → ∀ (f : Module.End ℤ M) (F : Module.End ℂ V), (∀ m : M, (f m : V) = F m) → Phi.toLinearMap.comp (f.baseChange K) = ((f.baseChange (Reduction.loc p)).baseChange K).comp Phi.toLinearMap → ∀ (i j : Reduction.Ind l) (z : ℤ), F (Reduction.e (act y) v0 i.val) = (z : ℂ) • Reduction.e (act y) v0 j.val → f.baseChange K (((a.baseChange K).map Phi.symm) i) = (z : K) • ((a.baseChange K).map Phi.symm) j" := by
  intro bar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  intro Phi a b ha f F hf hPhi i j z he
  simp only [Basis.map_apply, Basis.baseChange_apply]
  have ht := yui_aux_0004 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 bar Phi f F hf hPhi (a i) (a j) (z : Reduction.loc p)
  have hh : F (Reduction.iota p M (a i)) = algebraMap (Reduction.loc p) ℂ (z : Reduction.loc p) • Reduction.iota p M (a j) := by
    rw [ha, ha, map_smul, he]
    simp only [map_intCast]
    exact smul_comm _ _ _
  simpa only [map_intCast] using ht hh

theorem yui_aux_0006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (bar : Reduction.loc p →+* K), letI : Algebra (Reduction.loc p) K := bar.toAlgebra; ∀ (Phi : Reduction.VK K M ≃ₗ[K] (K ⊗[Reduction.loc p] Reduction.MR p M)), (∀ f : Module.End ℤ M, Phi.toLinearMap.comp (f.baseChange K) = ((f.baseChange (Reduction.loc p)).baseChange K).comp Phi.toLinearMap) → ∀ (A : Reduction.IntegralOps (act x) (act y) (act h) M) (a : Basis (Reduction.Ind l) (Reduction.loc p) (Reduction.MR p M)) (b : ℂ), (∀ i, Reduction.iota p M (a i) = b • Reduction.e (act y) v0 i.val) → Reduction.generatorFormulas l (A.ix.baseChange K) (A.iy.baseChange K) (A.ih.baseChange K) (Reduction.extendBasis l ((a.baseChange K).map Phi.symm))" := by
  intro bar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  intro Phi hPhi A a b ha
  let beta := (a.baseChange K).map Phi.symm
  have tr := yui_aux_0005 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 bar Phi a b ha
  have hb (i : ℕ) (hi : i < l.toNat + 1) :
      Reduction.extendBasis l beta i = beta ⟨i, hi⟩ := by simp [Reduction.extendBasis, hi]
  have hg := h_T002.2.2.2.2.2.2.2.1
  change Reduction.generatorFormulas l (A.ix.baseChange K) (A.iy.baseChange K) (A.ih.baseChange K) (Reduction.extendBasis l beta)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hb 0 (by omega)]
    simpa [beta] using tr A.ix (act x) A.ix_spec (hPhi A.ix) ⟨0, by omega⟩ ⟨0, by omega⟩ 0 (by simpa using hg.1)
  · intro i hi
    rw [hb (i+1) (by omega), hb i (by omega)]
    simpa only [Int.cast_sub, Int.cast_natCast] using
      tr A.ix (act x) A.ix_spec (hPhi A.ix) ⟨i+1, by omega⟩ ⟨i, by omega⟩ (l - (i : ℤ)) (by simpa using hg.2.1 i hi)
  · intro i hi
    rw [hb i (by omega), hb (i+1) (by omega)]
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
      tr A.iy (act y) A.iy_spec (hPhi A.iy) ⟨i, by omega⟩ ⟨i+1, by omega⟩ ((i : ℤ)+1) (by simpa using hg.2.2.1 i hi)
  · rw [hb l.toNat (by omega)]
    simpa [beta] using tr A.iy (act y) A.iy_spec (hPhi A.iy) ⟨l.toNat, by omega⟩ ⟨0, by omega⟩ 0 (by simpa using hg.2.2.2.1)
  · intro i hi
    rw [hb i (by omega)]
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
      tr A.ih (act h) A.ih_spec (hPhi A.ih) ⟨i, by omega⟩ ⟨i, by omega⟩ (l - 2 * (i : ℤ)) (by simpa using hg.2.2.2.2 i hi)

theorem yui_aux_0007 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (f : Module.End ℤ M) (F : Module.End ℂ V), (∀ m : M, (f m : V) = F m) → ∀ (n : ℕ) (m : M), ((f ^ n) m : V) = (F ^ n) (m : V)" := by
  intro f F hf n
  induction n with
  | zero => intro m; rfl
  | succ n hn =>
    intro m
    simp only [pow_succ', Module.End.mul_apply, hf, hn]

theorem yui_aux_0008 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ r : ℕ, (r.factorial : ℂ) ≠ 0" := by
  intro r
  exact_mod_cast Nat.factorial_ne_zero r

theorem yui_aux_0009 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (f g : Module.End ℤ M) (F : Module.End ℂ V) (r : ℕ), (∀ m : M, (f m : V) = F m) → (∀ m : M, (g m : V) = Reduction.divided F r m) → (r.factorial : ℤ) • g = f ^ r" := by
  intro f g F r hf hg
  ext m
  have hp := yui_aux_0007 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 f F hf r m
  simp only [LinearMap.smul_apply, SetLike.val_smul, hg, hp]
  rw [Reduction.divided, LinearMap.smul_apply]
  rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul]
  simp only [mul_inv_cancel₀ (yui_aux_0008 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 r), one_smul]

theorem yui_aux_0010 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ r : ℕ, r ≤ l.toNat → (r.factorial : K) ≠ 0" := by
  letI : CharP K p := h_H002
  intro r hr
  rw [ne_eq, CharP.cast_eq_zero_iff K p, h_H001.dvd_factorial]
  have hlp : l.toNat < p := by omega
  omega

theorem yui_aux_0011 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (g : Module.End K (Reduction.VK K M)) (n : ℤ), n • g = (n : K) • g" := by
  intro g n
  exact (algebraMap_smul K n g).symm

theorem yui_aux_0012 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (f g : Module.End ℤ M) (F : Module.End ℂ V) (r : ℕ), (∀ m : M, (f m : V) = F m) → (∀ m : M, (g m : V) = Reduction.divided F r m) → r ≤ l.toNat → g.baseChange K = (r.factorial : K)⁻¹ • (f.baseChange K)^r" := by
  intro f g F r hf hg hr
  have hn := yui_aux_0010 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 r hr
  have hi := yui_aux_0009 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 f g F r hf hg
  have he := congrArg (fun q : Module.End ℤ M => q.baseChange K) hi
  rw [LinearMap.baseChange_smul, LinearMap.baseChange_pow] at he
  rw [yui_aux_0011 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008, Int.cast_natCast] at he
  calc
    g.baseChange K = (r.factorial : K)⁻¹ • ((r.factorial : K) • g.baseChange K) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    _ = _ := congrArg (fun q => (r.factorial : K)⁻¹ • q) he

theorem checked (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ {S W : Type*} [Field S] [AddCommGroup W] [Module S W] (c : Basis (Reduction.Ind l) S W) (i j k : Reduction.Ind l), Reduction.matrixUnit c i j (c k) = if k = j then c i else 0" := by
  intro S W _ _ _ c i j k
  classical
  by_cases hk : k = j
  · subst k; simp [Reduction.matrixUnit, Basis.coord_apply]
  · simp [Reduction.matrixUnit, Basis.coord_apply, hk, Ne.symm hk]
#check @checked
#print axioms checked
end YuiAuxiliary
