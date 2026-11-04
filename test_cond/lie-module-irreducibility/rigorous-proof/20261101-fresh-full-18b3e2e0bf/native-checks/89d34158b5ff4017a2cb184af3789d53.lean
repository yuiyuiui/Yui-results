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

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) : yui_aux_type% "∀ w : V, (act h) ((act y) w) = (act y) ((act h) w) - (2 : ℂ) • (act y) w ∧ (act x) ((act y) w) = (act y) ((act x) w) + (act h) w" := by
  intro w
  have hc : act h * act y - act y * act h = -(2 • act y) := by
    rw [← LieRing.of_associative_ring_bracket, ← act.map_lie, h_H005.1.lie_h_f_nsmul, map_neg, map_nsmul]
  have xc : act x * act y - act y * act x = act h := by
    rw [← LieRing.of_associative_ring_bracket, ← act.map_lie, h_H005.1.lie_e_f]
  have hw := congrArg (fun f : Module.End ℂ V => f w) hc
  have xw := congrArg (fun f : Module.End ℂ V => f w) xc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, two_smul, LinearMap.add_apply] at hw xw
  constructor
  · calc
      act h (act y w) = (act h (act y w) - act y (act h w)) + act y (act h w) := by abel
      _ = -(act y w + act y w) + act y (act h w) := by rw [hw]
      _ = act y (act h w) - (2 : ℂ) • act y w := by rw [two_smul]; abel
  · exact (sub_eq_iff_eq_add.mp xw).trans (add_comm _ _)

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) : yui_aux_type% "∀ t : ℕ, (act h) (((act y) ^ t) v0) = ((l : ℂ) - 2 * (t : ℂ)) • ((act y) ^ t) v0" := by
  have comm := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H005 h_H006
  intro t
  induction t with
  | zero => simpa using h_H006.2.2
  | succ t ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [(comm _).1, ih, map_smul, ← sub_smul]
    congr 1
    push_cast
    ring

end Local_T001
open Local_T001 in
theorem T001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) :
    Reduction.strings l (act x) (act y) (act h) v0 := by
  have comm := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H005 h_H006
  have hw := @yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H005 h_H006
  change (∀ t : ℕ, _) ∧ (∀ t : ℕ, 1 ≤ t → _)
  refine ⟨hw, ?_⟩
  intro t
  induction t with
  | zero => intro ht; omega
  | succ t ih =>
    intro ht
    by_cases hz : t = 0
    · subst t
      simpa [h_H006.2.1, h_H006.2.2] using (comm v0).2
    · have htpos : 1 ≤ t := by omega
      have yprev : act y ((act y ^ (t - 1)) v0) = (act y ^ t) v0 := by
        rw [← Module.End.mul_apply, ← pow_succ']
        congr 2
        omega
      calc
        act x ((act y ^ (t + 1)) v0) =
            act y (act x ((act y ^ t) v0)) + act h ((act y ^ t) v0) := by
              rw [pow_succ', Module.End.mul_apply, (comm _).2]
        _ = ((t : ℂ) * ((l : ℂ) - (t : ℂ) + 1) + ((l : ℂ) - 2 * (t : ℂ))) •
            ((act y ^ t) v0) := by
              rw [ih htpos, hw t, map_smul, yprev, add_smul]
        _ = ((↑(t + 1) : ℂ) * ((l : ℂ) - ↑(t + 1) + 1)) •
            ((act y ^ (t + 1 - 1)) v0) := by
              simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
              congr 1
              ring

namespace Local_T002
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

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "∃ b : Basis (Reduction.Ind l) ℂ V, (∀ i, b i = Reduction.e (act y) v0 i.val) ∧ (∀ t : ℕ, l.toNat + 1 ≤ t → ((act y)^t) v0 = 0)" := by
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

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "(∀ (r i : ℕ), i ≤ l.toNat → r ≤ i → ((act x)^r) (Reduction.e (act y) v0 i) = ((l.toNat-i+1).ascFactorial r : ℂ) • Reduction.e (act y) v0 (i-r)) ∧ (∀ (r i : ℕ), i ≤ l.toNat → i < r → ((act x)^r) (Reduction.e (act y) v0 i) = 0) ∧ (∀ (r i : ℕ), ((act y)^r) (Reduction.e (act y) v0 i) = ((i+1).ascFactorial r : ℂ) • Reduction.e (act y) v0 (i+r))" := by
  have F := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  have hl := @yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  have HX : ∀ (r i : ℕ), i ≤ l.toNat → r ≤ i → ((act x)^r) (Reduction.e (act y) v0 i) = ((l.toNat-i+1).ascFactorial r : ℂ) • Reduction.e (act y) v0 (i-r) := by
    intro r
    induction r with
    | zero => intro i hi hr; simp
    | succ r ih =>
      intro i hi hr
      have he : i-r = (i-r-1)+1 := by omega
      rw [pow_succ', Module.End.mul_apply, ih i hi (by omega), map_smul, he, F.2.2.2, smul_smul, Nat.ascFactorial_succ, Nat.cast_mul]
      have hiC : (i : ℂ) = (i-r-1 : ℕ) + (r : ℂ) + 1 := by
        have hh : i = (i-r-1) + r + 1 := by omega
        exact_mod_cast hh
      have hliC : (l.toNat-i : ℕ) + (i : ℂ) = (l : ℂ) := by
        rw [← hl, ← Nat.cast_add, Nat.sub_add_cancel hi]
      have hc : (l : ℂ) - (i-r-1 : ℕ) = ((l.toNat-i+1+r : ℕ) : ℂ) := by
        push_cast
        linear_combination -hliC + hiC
      rw [hc]
      have he' : i-r-1 = i-(r+1) := by omega
      rw [he']
      congr 1
      ring
  refine ⟨HX, ?_, ?_⟩
  · intro r i hi hr
    have hz : ((act x)^(i+1)) (Reduction.e (act y) v0 i) = 0 := by
      rw [pow_succ', Module.End.mul_apply, HX i i hi le_rfl, Nat.sub_self, map_smul, F.2.2.1, smul_zero]
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le (show i+1 ≤ r by omega)
    rw [hs, Nat.add_comm, pow_add, Module.End.mul_apply, hz, map_zero]
  · intro r i
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, F.2.1, smul_smul, Nat.ascFactorial_succ, Nat.cast_mul]
      rw [show i+(r+1) = (i+r)+1 by omega]
      congr 1
      push_cast
      ring

theorem yui_aux_0006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "∀ (w : Reduction.Ind l → V) (μ : Reduction.Ind l → ℂ), Function.Injective μ → (∀ i, w i ≠ 0) → (∀ i, (act h) (w i) = μ i • w i) → LinearIndependent ℂ w" := by
  classical
  intro w μ hμ hw he
  apply linearIndependent_iff'.2
  intro s c hsum j hj
  let q : Polynomial ℂ := ∏ k ∈ s.erase j, (Polynomial.X - Polynomial.C (μ k))
  have hq (i : Reduction.Ind l) : q.eval (μ i) = ∏ k ∈ s.erase j, (μ i - μ k) := by
    simp only [q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hkill (i : Reduction.Ind l) (hi : i ∈ s) (hij : i ≠ j) : q.eval (μ i) = 0 := by
    rw [hq]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, hi⟩)
    simp
  have hnon : q.eval (μ j) ≠ 0 := by
    rw [hq]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro hh
    exact (Finset.mem_erase.mp hk).1 (hμ hh).symm
  have ha (i : Reduction.Ind l) : (Polynomial.aeval (act h) q) (w i) = q.eval (μ i) • w i :=
    Module.End.aeval_apply_of_mem_apply_eq_smul (he i)
  have hh := congrArg (fun z : V => (Polynomial.aeval (act h) q) z) hsum
  simp only [map_sum, map_smul, map_zero, ha, smul_smul] at hh
  have hsingle : ∑ i ∈ s, (c i * q.eval (μ i)) • w i = (c j * q.eval (μ j)) • w j := by
    apply Finset.sum_eq_single j
    · intro i hi hij
      rw [hkill i hi hij, mul_zero, zero_smul]
    · exact fun h => (h hj).elim
  rw [hsingle] at hh
  exact (mul_eq_zero.mp ((smul_eq_zero.mp hh).resolve_right (hw j))).resolve_right hnon

theorem yui_aux_0007 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) : yui_aux_type% "∃ b : Basis (Reduction.Ind l) ℂ V, (∀ i, b i = Reduction.e (act y) v0 i.val) ∧ (∀ t : ℕ, l.toNat + 1 ≤ t → ((act y)^t) v0 = 0)" := by
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
    @yui_aux_0006 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001 _ _ hinj (fun i => hn i.val (by have := i.isLt; omega)) (fun i => F.1 i.val)
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

end Local_T002
open Local_T002 in
theorem T002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_T001 : Reduction.strings l (act x) (act y) (act h) v0) :
    Reduction.basisFacts l (act x) (act y) (act h) v0 := by
  classical
  have F := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  obtain ⟨b, hb, hz⟩ := @yui_aux_0007 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  have P := @yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hezero (t : ℕ) (ht : l.toNat+1 ≤ t) : Reduction.e (act y) v0 t = 0 := by
    change (t.factorial : ℂ)⁻¹ • ((act y)^t) v0 = 0
    rw [hz t ht, smul_zero]
  refine ⟨h_H003.1, by omega, by omega, by simp [Reduction.Ind], ⟨b, hb⟩, h_T001, hz, ?_, ?_, ?_⟩
  · refine ⟨F.2.2.1, fun i _ => F.2.2.2 i, fun i _ => F.2.1 i, ?_, fun i _ => F.1 i⟩
    rw [F.2.1, hezero (l.toNat+1) le_rfl, smul_zero]
  · intro r i
    have hi : i.val ≤ l.toNat := by have := i.isLt; omega
    change (r.factorial : ℂ)⁻¹ • ((act x)^r) (Reduction.e (act y) v0 i.val) = _
    split_ifs with hr
    · rw [P.1 r i.val hi hr, smul_smul, Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, inv_mul_cancel_left₀ (hf r)]
    · rw [P.2.1 r i.val hi (by omega), smul_zero]
  · intro r i
    change (r.factorial : ℂ)⁻¹ • ((act y)^r) (Reduction.e (act y) v0 i.val) = _
    rw [P.2.2 r i.val, smul_smul, Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, inv_mul_cancel_left₀ (hf r)]
    split_ifs with hr
    · rfl
    · rw [hezero (i.val+r) (by omega), smul_zero]

namespace Local_T003
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "∀ d : ℤ, ¬ (p : ℤ) ∣ d → (d : ℚ) ≠ 0" := by
  intro d hd
  have hd0 : d ≠ 0 := by intro h; apply hd; rw [h]; exact dvd_zero _
  exact_mod_cast hd0

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "Reduction.locSpec p" := by
  classical
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using h_H001)
  have hm : ∀ a b : ℤ, ¬ (p : ℤ) ∣ a → ¬ (p : ℤ) ∣ b → ¬ (p : ℤ) ∣ a*b :=
    fun a b ha hb hab => (hp.dvd_mul.mp hab).elim ha hb
  intro q
  constructor
  · intro hq
    induction hq using Subring.closure_induction with
    | mem q hq =>
      obtain ⟨d, hd, rfl⟩ := hq
      exact ⟨1, d, hd, by simp⟩
    | zero => exact ⟨0, 1, hp.not_dvd_one, by simp⟩
    | one => exact ⟨1, 1, hp.not_dvd_one, by simp⟩
    | add q s hq hs iq is =>
      obtain ⟨a,d,hd,rfl⟩ := iq
      obtain ⟨b,e,he,rfl⟩ := is
      refine ⟨a*e+b*d, d*e, hm d e hd he, ?_⟩
      have hd0 : (d : ℚ) ≠ 0 := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002 d hd
      have he0 : (e : ℚ) ≠ 0 := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002 e he
      push_cast
      field_simp
      <;> ring
    | neg q hq iq =>
      obtain ⟨a,d,hd,rfl⟩ := iq
      exact ⟨-a,d,hd,by push_cast; ring⟩
    | mul q s hq hs iq is =>
      obtain ⟨a,d,hd,rfl⟩ := iq
      obtain ⟨b,e,he,rfl⟩ := is
      exact ⟨a*b,d*e,hm d e hd he,by push_cast; ring⟩
  · rintro ⟨a,d,hd,rfl⟩
    rw [div_eq_mul_inv]
    exact (Reduction.loc p).mul_mem (intCast_mem (Reduction.loc p) a)
      (Subring.subset_closure ⟨d,hd,rfl⟩)

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "act h * act x - act x * act h = (2 : ℤ) • act x ∧\n act h * act y - act y * act h = (-2 : ℤ) • act y ∧\n act x * act y - act y * act x = act h" := by
  constructor
  · have hh := congrArg act h_H005.1.lie_h_e_nsmul
    simpa [act.map_lie, LieRing.of_associative_ring_bracket] using hh
  constructor
  · have hh := congrArg act h_H005.1.lie_h_f_nsmul
    simpa [act.map_lie, LieRing.of_associative_ring_bracket] using hh
  · have hh := congrArg act h_H005.1.lie_e_f
    simpa [act.map_lie, LieRing.of_associative_ring_bracket] using hh

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "Nonempty (Reduction.IntegralOps (act x) (act y) (act h) M)" := by
  have hc := @yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
  have hx : ∀ z ∈ M, act x z ∈ M := by
    intro z hz
    simpa [Reduction.divided] using (h_H007.2 1 ⟨z,hz⟩).1
  have hy : ∀ z ∈ M, act y z ∈ M := by
    intro z hz
    simpa [Reduction.divided] using (h_H007.2 1 ⟨z,hz⟩).2
  have hh : ∀ z ∈ M, act h z ∈ M := by
    intro z hz
    rw [← hc.2.2]
    exact M.sub_mem (hx _ (hy _ hz)) (hy _ (hx _ hz))
  exact ⟨{
    ix := ((act x).restrictScalars ℤ).restrict hx
    iy := ((act y).restrictScalars ℤ).restrict hy
    ih := ((act h).restrictScalars ℤ).restrict hh
    iX := fun r => ((Reduction.divided (act x) r).restrictScalars ℤ).restrict (fun z hz => (h_H007.2 r ⟨z,hz⟩).1)
    iY := fun r => ((Reduction.divided (act y) r).restrictScalars ℤ).restrict (fun z hz => (h_H007.2 r ⟨z,hz⟩).2)
    ix_spec := fun _ => rfl
    iy_spec := fun _ => rfl
    ih_spec := fun _ => rfl
    iX_spec := fun _ _ => rfl
    iY_spec := fun _ _ => rfl
  }⟩

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "∀ A : Reduction.IntegralOps (act x) (act y) (act h) M,\n A.ih * A.ix - A.ix * A.ih = (2 : ℤ) • A.ix ∧\n A.ih * A.iy - A.iy * A.ih = (-2 : ℤ) • A.iy ∧\n A.ix * A.iy - A.iy * A.ix = A.ih" := by
  intro A
  have hc := @yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
  refine ⟨?_, ?_, ?_⟩
  · ext m
    have hh := DFunLike.congr_fun hc.1 (m : V)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Submodule.coe_sub, SetLike.val_smul, A.ix_spec, A.ih_spec] using hh
  · ext m
    have hh := DFunLike.congr_fun hc.2.1 (m : V)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Submodule.coe_sub, SetLike.val_smul, A.iy_spec, A.ih_spec] using hh
  · ext m
    have hh := DFunLike.congr_fun hc.2.2 (m : V)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub,
      A.ix_spec, A.iy_spec, A.ih_spec] using hh

theorem yui_aux_0006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "Function.Injective (algebraMap (Reduction.loc p) ℂ)" := by
  intro r s hs
  apply Subtype.ext
  apply Rat.cast_injective (α := ℂ)
  exact hs

theorem yui_aux_0007 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "∃ (a : Basis (Reduction.Ind l) ℤ M) (b : Basis (Reduction.Ind l) ℂ V),\n  ∀ i, (a i : V) = b i" := by
  classical
  obtain ⟨ι, fi, a, b, hab⟩ := h_H007.1
  letI := fi
  obtain ⟨b0, hb0⟩ := h_T002.2.2.2.2.1
  let eqi : ι ≃ Reduction.Ind l := b.indexEquiv b0
  exact ⟨a.reindex eqi, b.reindex eqi, fun i => by simpa using hab (eqi.symm i)⟩

theorem yui_aux_0008 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "∀ b : Basis (Reduction.Ind l) ℂ V, LinearIndependent (Reduction.loc p) b" := by
  intro b
  have ht : IsScalarTower (Reduction.loc p) ℂ V := Reduction.locTower p
  have hi := @yui_aux_0006 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
  exact @LinearIndependent.restrict_scalars (Reduction.Ind l) (Reduction.loc p) ℂ V b
    _ _ _ _ (inferInstance : SMulWithZero (Reduction.loc p) ℂ) _ ht
    (by
      intro r s hrs
      apply hi
      change algebraMap (Reduction.loc p) ℂ r * 1 = algebraMap (Reduction.loc p) ℂ s * 1 at hrs
      simpa only [mul_one] using hrs)
    b.linearIndependent

theorem yui_aux_0009 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "Function.Injective (Reduction.iota p M) ∧\n Nonempty (Basis (Reduction.Ind l) (Reduction.loc p) (Reduction.MR p M)) ∧\n Module.finrank (Reduction.loc p) (Reduction.MR p M) = l.toNat + 1 ∧\n Submodule.span ℂ (Set.range (Reduction.iota p M)) = ⊤" := by
  classical
  obtain ⟨a,b,hab⟩ := @yui_aux_0007 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
  let ar : Basis (Reduction.Ind l) (Reduction.loc p) (Reduction.MR p M) := a.baseChange (Reduction.loc p)
  have har : ∀ i, Reduction.iota p M (ar i) = b i := by
    intro i
    simpa [ar, Reduction.iota] using hab i
  have hli : LinearIndependent (Reduction.loc p) b :=
    @yui_aux_0008 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002 b
  have hli' : LinearIndependent (Reduction.loc p) ((Reduction.iota p M) ∘ ar) := by
    simpa only [Function.comp_def, har] using hli
  refine ⟨LinearMap.injective_of_linearIndependent ar.span_eq hli', ⟨ar⟩, ?_, ?_⟩
  · simpa [Reduction.Ind] using Module.finrank_eq_card_basis ar
  · apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
    intro i
    apply Submodule.subset_span
    exact ⟨ar i, har i⟩

theorem yui_aux_0010 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "∀ f : Module.End ℂ V, (∀ m : M, f m ∈ M) →\n ∀ z : V, z ∈ (Reduction.iota p M).range → f z ∈ (Reduction.iota p M).range" := by
  intro f hf z hz
  obtain ⟨u,rfl⟩ := hz
  induction u using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (Reduction.iota p M).range.zero_mem
  | tmul s m =>
    refine ⟨s ⊗ₜ[ℤ] (⟨f m, hf m⟩ : M), ?_⟩
    change algebraMap (Reduction.loc p) ℂ s • f (m : V) =
      f (algebraMap (Reduction.loc p) ℂ s • (m : V))
    exact (f.map_smul _ _).symm
  | add u w hu hw =>
    simpa only [map_add] using (Reduction.iota p M).range.add_mem hu hw

end Local_T003
open Local_T003 in
theorem T003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) :
    Reduction.latticeFacts p l (act x) (act y) (act h) M := by
  have hb := @yui_aux_0009 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
  refine ⟨@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002,
    @yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002,
    @yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002,
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, ?_⟩
  intro r z hz
  constructor
  · exact @yui_aux_0010 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
      (Reduction.divided (act x) r) (fun m => (h_H007.2 r m).1) z hz
  · exact @yui_aux_0010 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
      (Reduction.divided (act y) r) (fun m => (h_H007.2 r m).2) z hz

namespace Local_T004
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) : yui_aux_type% "∀ j : Reduction.Ind l, IsUnit (Nat.choose l.toNat j.val : Reduction.loc p) ∧ (Nat.choose l.toNat j.val : ℚ)⁻¹ ∈ Reduction.loc p" := by
  intro j
  have hj : j.val ≤ l.toNat := Nat.le_of_lt_succ j.isLt
  have hlp : l.toNat < p := by omega
  have hn : ¬ p ∣ Nat.choose l.toNat j.val := by
    intro hd
    have hf : p ∣ l.toNat.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hj]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
    exact (not_le_of_gt hlp) (h_H001.dvd_factorial.mp hf)
  have hnZ : ¬ (p : ℤ) ∣ (Nat.choose l.toNat j.val : ℤ) := by
    exact_mod_cast hn
  have hinv : (Nat.choose l.toNat j.val : ℚ)⁻¹ ∈ Reduction.loc p := by
    apply Subring.subset_closure
    exact ⟨(Nat.choose l.toNat j.val : ℤ), hnZ, by simp⟩
  have hne : Nat.choose l.toNat j.val ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hj)
  refine ⟨?_, hinv⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨_, hinv⟩, ?_⟩
  apply Subtype.ext
  change (Nat.choose l.toNat j.val : ℚ) * (Nat.choose l.toNat j.val : ℚ)⁻¹ = 1
  exact mul_inv_cancel₀ (by exact_mod_cast hne)

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) : yui_aux_type% "∀ b : Basis (Reduction.Ind l) ℂ V,\n (∀ i j k, Reduction.matrixUnit b i j (b k) = if k = j then b i else 0) ∧\n (∀ i j, Reduction.matrixUnit b i (Fin.last l.toNat) * Reduction.matrixUnit b (Fin.last l.toNat) j = Reduction.matrixUnit b i j)" := by
  classical
  intro b
  have ha : ∀ i j k, Reduction.matrixUnit b i j (b k) = if k = j then b i else 0 := by
    intro i j k
    by_cases hk : k = j <;> simp [Reduction.matrixUnit, Basis.coord, Finsupp.single_apply, hk]
  refine ⟨ha, ?_⟩
  intro i j
  apply b.ext
  intro k
  by_cases hk : k = j <;> simp [Module.End.mul_apply, ha, hk]

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V), (∀ i, b i = Reduction.e (act y) v0 i.val) →\n Reduction.divided (act y) l.toNat * Reduction.divided (act x) l.toNat =\n Reduction.matrixUnit b (Fin.last l.toNat) (Fin.last l.toNat)" := by
  classical
  intro b hb
  rcases h_T002 with ⟨hl, hp, hn, hc, he, hs, hk, hg, hX, hY⟩
  have ha := (@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 ⟨hl, hp, hn, hc, he, hs, hk, hg, hX, hY⟩ h_T003 b).1
  apply b.ext
  intro k
  rw [Module.End.mul_apply, ha]
  by_cases hkl : k = Fin.last l.toNat
  · subst k
    rw [hb, hX]
    simp only [Fin.val_last, le_refl, ite_true, Nat.sub_self, zero_add, Nat.choose_self, Nat.cast_one, one_smul]
    have hz := hY l.toNat (⟨0, by omega⟩ : Reduction.Ind l)
    simp only [Fin.val_zero, zero_add, le_refl, ite_true, Nat.choose_self, Nat.cast_one, one_smul] at hz
    simpa [hb] using hz
  · have hlt : k.val < l.toNat := by
      have hne : k.val ≠ l.toNat := by
        intro hv
        apply hkl
        exact Fin.ext hv
      omega
    rw [hb, hX]
    simp [show ¬ l.toNat ≤ k.val by omega, hkl]

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V), (∀ i, b i = Reduction.e (act y) v0 i.val) →\n ∀ i : Reduction.Ind l,\n Reduction.divided (act x) (l.toNat-i.val) * Reduction.matrixUnit b (Fin.last l.toNat) (Fin.last l.toNat) =\n Reduction.matrixUnit b i (Fin.last l.toNat)" := by
  classical
  intro b hb i
  have ha := (@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b).1
  have hX := h_T002.2.2.2.2.2.2.2.2.1
  apply b.ext
  intro k
  rw [Module.End.mul_apply, ha, ha]
  by_cases hkl : k = Fin.last l.toNat
  · simp only [hkl, ite_true]
    rw [hb, hX]
    have hi : i.val ≤ l.toNat := Nat.le_of_lt_succ i.isLt
    have heq : l.toNat - (l.toNat - i.val) = i.val := by omega
    simp [Fin.val_last, heq, hb, Nat.sub_le]
  · simp [hkl]

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V), (∀ i, b i = Reduction.e (act y) v0 i.val) →\n ∀ j : Reduction.Ind l,\n Reduction.matrixUnit b (Fin.last l.toNat) (Fin.last l.toNat) * Reduction.divided (act y) (l.toNat-j.val) =\n (Nat.choose l.toNat j.val : ℂ) • Reduction.matrixUnit b (Fin.last l.toNat) j" := by
  classical
  intro b hb j
  have ha := (@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b).1
  have hY := h_T002.2.2.2.2.2.2.2.2.2
  have hj : j.val ≤ l.toNat := Nat.le_of_lt_succ j.isLt
  apply b.ext
  intro k
  rw [Module.End.mul_apply, LinearMap.smul_apply, ha, hb k, hY]
  by_cases hsum : k.val + (l.toNat-j.val) ≤ l.toNat
  · rw [if_pos hsum, map_smul]
    let t : Reduction.Ind l := ⟨k.val + (l.toNat-j.val), by omega⟩
    have ht : Reduction.e (act y) v0 (k.val + (l.toNat-j.val)) = b t := (hb t).symm
    rw [ht, ha]
    by_cases hkj : k = j
    · subst k
      have hsumEq : j.val + (l.toNat-j.val) = l.toNat := by omega
      have htlast : t = Fin.last l.toNat := Fin.ext hsumEq
      simp [htlast, hsumEq, Nat.choose_symm hj]
    · have htlast : t ≠ Fin.last l.toNat := by
        intro ht
        have htval := congrArg Fin.val ht
        have hkval : k.val = j.val := by
          change k.val + (l.toNat-j.val) = l.toNat at htval
          omega
        exact hkj (Fin.ext hkval)
      simp [htlast, hkj]
  · rw [if_neg hsum, map_zero]
    have hkj : k ≠ j := by
      intro hk
      subst k
      omega
    simp [hkj]

theorem yui_aux_0006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V), (∀ i, b i = Reduction.e (act y) v0 i.val) →\n∀ i j : Reduction.Ind l, Reduction.matrixUnit b i j =\n(Nat.choose l.toNat j.val : ℂ)⁻¹ •\n(Reduction.divided (act x) (l.toNat-i.val) * Reduction.divided (act y) l.toNat *\n Reduction.divided (act x) l.toNat * Reduction.divided (act y) (l.toNat-j.val))" := by
  classical
  intro b hb i j
  have hmu := (@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b).2
  have hQ := @yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b hb
  have hXQ := @yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b hb i
  have hQY := @yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b hb j
  let Q := Reduction.matrixUnit b (Fin.last l.toNat) (Fin.last l.toNat)
  let X := Reduction.divided (act x) (l.toNat-i.val)
  let Y := Reduction.divided (act y) (l.toNat-j.val)
  have hid : Q * Q = Q := hmu _ _
  have hprod :
   Reduction.divided (act x) (l.toNat-i.val) * Reduction.divided (act y) l.toNat *
   Reduction.divided (act x) l.toNat * Reduction.divided (act y) (l.toNat-j.val) =
   (Nat.choose l.toNat j.val : ℂ) • Reduction.matrixUnit b i j := by
    calc
      _ = X * Q * Y := by dsimp [X, Q, Y]; rw [← hQ]; simp only [mul_assoc]
      _ = X * (Q * Q) * Y := by rw [hid]
      _ = (X * Q) * (Q * Y) := by simp only [mul_assoc]
      _ = (Nat.choose l.toNat j.val : ℂ) • Reduction.matrixUnit b i j := by
        rw [hXQ, hQY, mul_smul_comm, hmu]
  rw [hprod, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)))

theorem yui_aux_0007 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) : yui_aux_type% "∀ j : Reduction.Ind l, ∃ r : Reduction.loc p, ∀ z : V, r • z = (Nat.choose l.toNat j.val : ℂ)⁻¹ • z" := by
  intro j
  have hinv := (@yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 j).2
  let r : Reduction.loc p := ⟨(Nat.choose l.toNat j.val : ℚ)⁻¹, hinv⟩
  refine ⟨r, ?_⟩
  intro z
  change (((Nat.choose l.toNat j.val : ℚ)⁻¹ : ℚ) : ℂ) • z = _
  simp

end Local_T004
open Local_T004 in
theorem T004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M) :
    Reduction.localizationFacts p l (act x) (act y) (act h) v0 M := by
  classical
  refine ⟨h_T003, ?_⟩
  intro b hb i j
  have harith := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 j
  have hf := @yui_aux_0006 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b hb i j
  refine ⟨harith.1, harith.2, ?_, hf,
    @yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b hb,
    @yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b hb i,
    @yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 b hb j⟩
  intro z hz
  have hstab := h_T003.2.2.2.2.2.2.2
  have hz₁ := (hstab (l.toNat-j.val) z hz).2
  have hz₂ := (hstab l.toNat _ hz₁).1
  have hz₃ := (hstab l.toNat _ hz₂).2
  have hz₄ := (hstab (l.toNat-i.val) _ hz₃).1
  obtain ⟨r, hr⟩ := @yui_aux_0007 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003 j
  rw [hf, LinearMap.smul_apply]
  simp only [Module.End.mul_apply]
  rw [← hr]
  exact (Reduction.iota p M).range.smul_mem r hz₄

namespace Local_T005
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V), (∀ i, b i = Reduction.e (act y) v0 i.val) → (∀ i : Reduction.Ind l, Reduction.Jcoord p M (act y) v0 i.val = Reduction.Jcoord p M (act y) v0 0) ∧ ∀ z ∈ (Reduction.iota p M).range, ∀ i : Reduction.Ind l, b.repr z i ∈ Reduction.Jcoord p M (act y) v0 0" := by
  classical
  intro b hb
  have hp := h_T004.2 b hb
  have hmem (i : Reduction.Ind l) (c : ℂ) :
      c ∈ Reduction.Jcoord p M (act y) v0 i.val ↔
      c • b i ∈ (Reduction.iota p M).range := by
    simp [Reduction.Jcoord, hb]
  have htrans (i j : Reduction.Ind l) :
      Reduction.Jcoord p M (act y) v0 j.val ≤ Reduction.Jcoord p M (act y) v0 i.val := by
    intro c hc
    apply (hmem i c).2
    have hh := (hp i j).2.2.1 (c • b j) ((hmem j c).1 hc)
    simpa [Reduction.matrixUnit, Basis.coord_apply] using hh
  let iz : Reduction.Ind l := ⟨0, Nat.zero_lt_succ _⟩
  have heq (i : Reduction.Ind l) :
      Reduction.Jcoord p M (act y) v0 i.val = Reduction.Jcoord p M (act y) v0 0 :=
    le_antisymm (htrans iz i) (htrans i iz)
  refine ⟨heq, ?_⟩
  intro z hz i
  rw [← heq i]
  apply (hmem i _).2
  have hh := (hp i i).2.2.1 z hz
  simpa [Reduction.matrixUnit, Basis.coord_apply] using hh

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V), (∀ i, b i = Reduction.e (act y) v0 i.val) → ∀ c : ℂ, c ∈ Reduction.Jcoord p M (act y) v0 0 ↔ c • b ⟨0, Nat.zero_lt_succ _⟩ ∈ (Reduction.iota p M).range" := by
  intro b hb c
  rw [hb]
  rfl

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "(Reduction.Jcoord p M (act y) v0 0).FG ∧ Reduction.Jcoord p M (act y) v0 0 ≠ ⊥" := by
  classical
  obtain ⟨b, hb⟩ := h_T002.2.2.2.2.1
  obtain ⟨heq, hc⟩ := (@yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004) b hb
  let iz : Reduction.Ind l := ⟨0, Nat.zero_lt_succ _⟩
  let f : Reduction.MR p M →ₗ[Reduction.loc p] ℂ :=
    ((b.coord iz).restrictScalars (Reduction.loc p)).comp (Reduction.iota p M)
  have hfr : f.range = Reduction.Jcoord p M (act y) v0 0 := by
    ext c
    constructor
    · rintro ⟨u, rfl⟩
      exact hc _ ⟨u, rfl⟩ iz
    · intro hc'
      have hh : c • b iz ∈ (Reduction.iota p M).range := by
        exact ((@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004) b hb c).mp hc'
      obtain ⟨u, hu⟩ := hh
      refine ⟨u, ?_⟩
      change b.coord iz (Reduction.iota p M u) = c
      rw [hu]
      simp [Basis.coord_apply]
  have hfg : (Reduction.Jcoord p M (act y) v0 0).FG := by
    obtain ⟨a⟩ := h_T004.1.2.2.2.2.1
    letI : Module.Finite (Reduction.loc p) (Reduction.MR p M) := Module.Finite.of_basis a
    rw [← hfr]
    exact Submodule.fg_range f
  refine ⟨hfg, ?_⟩
  intro hzero
  have hall : ∀ z ∈ (Reduction.iota p M).range, z = 0 := by
    intro z hz
    apply b.repr.injective
    ext i
    have hz' := hc z hz i
    rw [hzero] at hz'
    simpa using hz'
  have hspanle : Submodule.span ℂ (Set.range (Reduction.iota p M)) ≤ (⊥ : Submodule ℂ V) := by
    apply Submodule.span_le.mpr
    rintro z ⟨u, rfl⟩
    exact hall _ ⟨u, rfl⟩
  have hspan := h_T004.1.2.2.2.2.2.2.1
  rw [hspan] at hspanle
  have hbzero : b iz = 0 := hspanle (Submodule.mem_top)
  have hh := congrArg (fun z => b.repr z iz) hbzero
  simpa using hh

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V) (c : Reduction.Ind l → ℂ) (j : Reduction.Ind l), b.repr (∑ i, c i • b i) j = c j" := by
  classical
  intro b c j
  simp [map_sum, map_smul, Finsupp.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ (b : Basis (Reduction.Ind l) ℂ V) (r : Reduction.loc p) (c : Reduction.Ind l → Reduction.Jcoord p M (act y) v0 0), (∑ i, ((r • c) i : ℂ) • b i) = r • ∑ i, (c i : ℂ) • b i" := by
  intro b r c
  simp [Pi.smul_apply, Finset.smul_sum, smul_assoc]

end Local_T005
open Local_T005 in
theorem T005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) :
    Reduction.coordinateFacts p l (act y) v0 M := by
  classical
  obtain ⟨b, hb⟩ := h_T002.2.2.2.2.1
  obtain ⟨heq, hc⟩ :=
    (@yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004) b hb
  obtain ⟨hfg, hne⟩ :=
    @yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004
  refine ⟨heq, hne, hfg, ?_⟩
  have hterm (c : Reduction.Ind l → Reduction.Jcoord p M (act y) v0 0)
      (i : Reduction.Ind l) :
      (c i : ℂ) • b i ∈ (Reduction.iota p M).range := by
    rw [hb i]
    change (c i : ℂ) ∈ Reduction.Jcoord p M (act y) v0 i.val
    rw [heq i]
    exact (c i).property
  let d : (Reduction.Ind l → Reduction.Jcoord p M (act y) v0 0) ≃ₗ[Reduction.loc p]
      (Reduction.iota p M).range :=
    { toFun := fun c => ⟨∑ i, (c i : ℂ) • b i,
          (Reduction.iota p M).range.sum_mem (fun i _ => hterm c i)⟩
      invFun := fun z i => ⟨b.repr (z : V) i, hc (z : V) z.property i⟩
      left_inv := by
        intro c
        funext i
        apply Subtype.ext
        exact (@yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004)
          b (fun j => (c j : ℂ)) i
      right_inv := by
        intro z
        apply Subtype.ext
        exact b.sum_repr (z : V)
      map_add' := by
        intro c c'
        apply Subtype.ext
        simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        apply Subtype.ext
        exact (@yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004)
          b r c }
  refine ⟨d, ?_⟩
  intro c
  change (∑ i, (c i : ℂ) • b i) = _
  simp_rw [hb]

namespace Local_T006
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) : yui_aux_type% "∀ (q : ℚ) (c : Reduction.Jcoord p M (act y) v0 0), q.den • (q ⊗ₜ[Reduction.loc p] c) = (1 : ℚ) ⊗ₜ[Reduction.loc p] (q.num • c)" := by
  intro q c
  rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, mul_one]

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) : yui_aux_type% "∀ z : ℚ ⊗[Reduction.loc p] (Reduction.Jcoord p M (act y) v0 0), ∃ d : ℕ, d ≠ 0 ∧ ∃ c : Reduction.Jcoord p M (act y) v0 0, d • z = (1 : ℚ) ⊗ₜ[Reduction.loc p] c" := by
  intro z
  induction z with
  | zero => exact ⟨1, by omega, 0, by simp⟩
  | tmul q c =>
    exact ⟨q.den, q.den_nz, q.num • c,
      (@yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005) q c⟩
  | add z w hz hw =>
    obtain ⟨d, hd, c, hc⟩ := hz
    obtain ⟨d', hd', c', hc'⟩ := hw
    refine ⟨d * d', Nat.mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_comm d d', mul_smul, hc, mul_comm d' d, mul_smul, hc']
    simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul]

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) : yui_aux_type% "∀ (d : ℕ) (z : ℚ ⊗[Reduction.loc p] (Reduction.Jcoord p M (act y) v0 0)) (c : Reduction.Jcoord p M (act y) v0 0), Reduction.rationalMu p (act y) v0 M z = 0 → d • z = (1 : ℚ) ⊗ₜ[Reduction.loc p] c → (c : ℂ) = 0" := by
  intro d z c hz hc
  have hh := congrArg (Reduction.rationalMu p (act y) v0 M) hc
  rw [map_nsmul, hz, smul_zero] at hh
  simpa only [Reduction.rationalMu, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, one_smul] using hh.symm

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) : yui_aux_type% "Function.Injective (Reduction.rationalMu p (act y) v0 M)" := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨d, hd, c, hc⟩ := (@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005) z
  have hc0 : (c : ℂ) = 0 :=
    (@yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005) d z c hz hc
  have hc' : c = 0 := Subtype.ext hc0
  have hz' : (d : ℚ) • z = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul ℚ, hc', TensorProduct.tmul_zero] using hc
  exact (smul_eq_zero.mp hz').resolve_left (by exact_mod_cast hd)

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) : yui_aux_type% "FiniteDimensional ℚ (ℚ ⊗[Reduction.loc p] (Reduction.Jcoord p M (act y) v0 0))" := by
  haveI : Module.Finite (Reduction.loc p) (Reduction.Jcoord p M (act y) v0 0) :=
    Module.Finite.iff_fg.mpr h_T005.2.2.1
  infer_instance

theorem yui_aux_0006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) : yui_aux_type% "Module.finrank ℚ (ℚ ⊗[Reduction.loc p] (Reduction.Jcoord p M (act y) v0 0)) = 1" := by
  classical
  let R := Reduction.loc p
  let J := Reduction.Jcoord p M (act y) v0 0
  let T := ℚ ⊗[R] J
  haveI : FiniteDimensional ℚ T :=
    @yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005
  obtain ⟨b⟩ := h_T004.1.2.2.2.2.1
  haveI : Module.Free R (Reduction.MR p M) := Module.Free.of_basis b
  haveI : Module.Finite R (Reduction.MR p M) := Module.Finite.of_basis b
  obtain ⟨d, hd⟩ := h_T005.2.2.2
  let er : Reduction.MR p M ≃ₗ[R] (Reduction.iota p M).range :=
    LinearEquiv.ofInjective (Reduction.iota p M) h_T004.1.2.2.2.1
  let ec : Reduction.MR p M ≃ₗ[R] (Reduction.Ind l → J) := er.trans d.symm
  let et : (ℚ ⊗[R] Reduction.MR p M) ≃ₗ[ℚ] (Reduction.Ind l → T) :=
    (ec.baseChange R ℚ _ _).trans (TensorProduct.piRight R ℚ ℚ (fun _ : Reduction.Ind l => J))
  have hn : Module.finrank ℚ (ℚ ⊗[R] Reduction.MR p M) = l.toNat + 1 := by
    rw [Module.finrank_baseChange (R := ℚ) (S := R) (M' := Reduction.MR p M)]
    exact h_T004.1.2.2.2.2.2.1
  have hp : Module.finrank ℚ (Reduction.Ind l → T) =
      (l.toNat + 1) * Module.finrank ℚ T := by
    rw [Module.finrank_pi_fintype ℚ]
    simp [Reduction.Ind]
  have heq : l.toNat + 1 = (l.toNat + 1) * Module.finrank ℚ T :=
    hn.symm.trans (et.finrank_eq.trans hp)
  have hpos : 0 < l.toNat + 1 := h_T002.2.2.1
  nlinarith

end Local_T006
open Local_T006 in
theorem T006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) :
    Reduction.rationalFacts p (act y) v0 M := by
  exact ⟨@yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005,
    @yui_aux_0006 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005,
    @yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005⟩

namespace Local_T007
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∀ (d : ℤ) (t : ℕ), (qden : ℕ) → (qden : ℤ) = (p : ℤ)^t * d → (qden : ℚ) = (p : ℚ)^t * d" := by
  intro d t qden hd
  simpa only [Int.cast_natCast, Int.cast_mul, Int.cast_pow] using congrArg (fun z : ℤ => (z : ℚ)) hd

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∀ q : ℚ, q ≠ 0 → ∃ (η : ℤ) (u : ℚ), u ≠ 0 ∧ u ∈ Reduction.loc p ∧ u⁻¹ ∈ Reduction.loc p ∧ q = (p : ℚ) ^ η * u" := by
  intro q hq
  have hs := h_T004.1.1
  have hn := (Int.finiteMultiplicity_iff.mpr (show (p : ℤ).natAbs ≠ 1 ∧ q.num ≠ 0 from ⟨by simpa using h_H001.ne_one, Rat.num_ne_zero.mpr hq⟩)).exists_eq_pow_mul_and_not_dvd
  have hd := (Int.finiteMultiplicity_iff.mpr (show (p : ℤ).natAbs ≠ 1 ∧ (q.den : ℤ) ≠ 0 from ⟨by simpa using h_H001.ne_one, by exact_mod_cast q.den_ne_zero⟩)).exists_eq_pow_mul_and_not_dvd
  obtain ⟨a, ha, hpa⟩ := hn
  obtain ⟨d, hd, hpd⟩ := hd
  have ha0 : a ≠ 0 := by rintro rfl; simp_all
  have hd0 : d ≠ 0 := by rintro rfl; simp_all
  let s := multiplicity (p : ℤ) q.num
  let t := multiplicity (p : ℤ) (q.den : ℤ)
  refine ⟨(s : ℤ) - t, (a : ℚ) / d, div_ne_zero (by exact_mod_cast ha0) (by exact_mod_cast hd0), (hs _).mpr ⟨a, d, hpd, rfl⟩, ?_, ?_⟩
  · rw [inv_div]
    exact (hs _).mpr ⟨d, a, hpa, rfl⟩
  · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.ne_zero
    have han : (q.num : ℚ) = (p : ℚ)^s * a := by exact_mod_cast ha
    have hdn : (q.den : ℚ) = (p : ℚ)^t * d := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006 d t q.den hd
    rw [← Rat.num_div_den q, han, hdn, zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
    field_simp

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∃ a : ℂ, a ≠ 0 ∧ a ∈ Reduction.Jcoord p M (act y) v0 0 ∧ ∀ z : ℂ, z ∈ Reduction.Jcoord p M (act y) v0 0 → ∃ q : ℚ, (q : ℂ) * a = z" := by
  classical
  let J := Reduction.Jcoord p M (act y) v0 0
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_T005.2.1
  refine ⟨a, ha0, ha, ?_⟩
  letI := h_T006.1
  let A : ℚ ⊗[Reduction.loc p] J := 1 ⊗ₜ[Reduction.loc p] (⟨a, ha⟩ : J)
  have hA : A ≠ 0 := by
    intro hz
    have hh := congrArg (Reduction.rationalMu p (act y) v0 M) hz
    simp [A, Reduction.rationalMu, LinearMap.liftBaseChange_tmul] at hh
    exact ha0 hh
  intro z hz
  obtain ⟨q, hq⟩ := (finrank_eq_one_iff_of_nonzero' A hA).mp h_T006.2.1 (1 ⊗ₜ[Reduction.loc p] (⟨z,hz⟩ : J))
  refine ⟨q, ?_⟩
  have hh := congrArg (Reduction.rationalMu p (act y) v0 M) hq
  simpa [A, Reduction.rationalMu, LinearMap.liftBaseChange_tmul, Algebra.smul_def] using hh

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∀ (r : Reduction.loc p) (z : ℂ), r • z = ((r : ℚ) : ℂ) * z" := by
  intro r z
  rfl

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∀ (η ν : ℤ) (u : ℚ) (a : ℂ), ν ≤ η → u ∈ Reduction.loc p → ∃ r : Reduction.loc p, r • ((((p : ℚ)^ν : ℚ) : ℂ) * a) = (((((p : ℚ)^η * u) : ℚ) : ℂ) * a)" := by
  intro η ν u a hle hmem
  have hnon : 0 ≤ η - ν := sub_nonneg.mpr hle
  let r : Reduction.loc p := (p : Reduction.loc p) ^ (η - ν).toNat * ⟨u, hmem⟩
  have hr : (r : ℚ) = (p : ℚ) ^ (η - ν) * u := by
    change (p : ℚ) ^ (η - ν).toNat * u = _
    rw [← zpow_natCast, Int.toNat_of_nonneg hnon]
  refine ⟨r, ?_⟩
  rw [@yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006, hr]
  push_cast
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast h_H001.ne_zero
  have hh : (p : ℂ)^(η-ν) * (p : ℂ)^ν = (p : ℂ)^η := by
    rw [← zpow_add₀ hp0]
    congr 1
    omega
  calc
    _ = ((p : ℂ)^(η-ν) * (p : ℂ)^ν) * ((u : ℂ) * a) := by ring
    _ = _ := by rw [hh]; ring

theorem yui_aux_0006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∃ b : ℂ, b ≠ 0 ∧ b ∈ Reduction.Jcoord p M (act y) v0 0 ∧ Reduction.Jcoord p M (act y) v0 0 = Submodule.span (Reduction.loc p) ({b} : Set ℂ)" := by
  classical
  let J := Reduction.Jcoord p M (act y) v0 0
  obtain ⟨a, ha0, ha, hline⟩ := @yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006
  obtain ⟨s, hs⟩ := h_T005.2.2.1
  change Submodule.span (Reduction.loc p) (s : Set ℂ) = J at hs
  let t := s.erase 0
  have ht : Submodule.span (Reduction.loc p) (t : Set ℂ) = J := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro z hz
      rw [← hs]
      exact Submodule.subset_span (Finset.mem_of_mem_erase hz)
    · rw [← hs]
      apply Submodule.span_le.mpr
      intro z hz
      by_cases hz0 : z = 0
      · simp [hz0]
      · exact Submodule.subset_span (Finset.mem_erase.mpr ⟨hz0, hz⟩)
  have htne : t.Nonempty := by
    by_contra hh
    have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    have hb : J = ⊥ := by simpa [he] using ht.symm
    exact h_T005.2.1 hb
  letI : Nonempty t := ⟨⟨htne.choose, htne.choose_spec⟩⟩
  have hzJ (z : t) : (z : ℂ) ∈ J := by
    rw [← ht]
    exact Submodule.subset_span z.property
  choose q hq using fun z : t => hline z (hzJ z)
  have hq0 (z : t) : q z ≠ 0 := by
    intro hh
    have hz0 : (z : ℂ) ≠ 0 := (Finset.mem_erase.mp z.property).1
    apply hz0
    simpa [hh] using (hq z).symm
  choose η u hu0 hu hui heq using fun z : t => @yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006 (q z) (hq0 z)
  obtain ⟨z₀, _, hmin⟩ := Finset.univ.exists_min_image η Finset.univ_nonempty
  let ν := η z₀
  let b : ℂ := (((p : ℚ) ^ ν : ℚ) : ℂ) * a
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.ne_zero
  have hb0 : b ≠ 0 := mul_ne_zero (Rat.cast_ne_zero.mpr (zpow_ne_zero _ hp0)) ha0
  have hcoeff (z : t) : ∃ r : Reduction.loc p, r • b = (z : ℂ) := by
    obtain ⟨r, hr⟩ := @yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006 (η z) ν (u z) a (hmin z (Finset.mem_univ _)) (hu z)
    refine ⟨r, ?_⟩
    change r • ((((p : ℚ)^ν : ℚ) : ℂ) * a) = (z : ℂ)
    rw [hr, ← heq z]
    exact hq z
  have hbJ : b ∈ J := by
    let r : Reduction.loc p := ⟨(u z₀)⁻¹, hui z₀⟩
    have hz : (z₀ : ℂ) = (u z₀ : ℂ) * b := by
      rw [← hq z₀, heq z₀]
      dsimp [b, ν]
      push_cast
      ring
    have hh := J.smul_mem r (hzJ z₀)
    have hid : r • (z₀ : ℂ) = b := by
      rw [@yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006, hz]
      change (((u z₀)⁻¹ : ℚ) : ℂ) * ((u z₀ : ℂ) * b) = b
      rw [Rat.cast_inv, inv_mul_cancel_left₀ (Rat.cast_ne_zero.mpr (hu0 z₀))]
    rwa [hid] at hh
  refine ⟨b, hb0, hbJ, le_antisymm ?_ (Submodule.span_le.mpr ?_)⟩
  · change J ≤ Submodule.span (Reduction.loc p) ({b} : Set ℂ)
    rw [← ht]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨r, hr⟩ := hcoeff ⟨z,hz⟩
    change r • b = z at hr
    rw [← hr]
    exact Submodule.smul_mem _ r (Submodule.subset_span (Set.mem_singleton b))
  · intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hbJ

theorem yui_aux_0007 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∀ b : ℂ, b ≠ 0 → b ∈ Reduction.Jcoord p M (act y) v0 0 → Reduction.Jcoord p M (act y) v0 0 = Submodule.span (Reduction.loc p) ({b} : Set ℂ) → ∃ a : Basis (Reduction.Ind l) (Reduction.loc p) (Reduction.MR p M), ∀ i, Reduction.iota p M (a i) = b • Reduction.e (act y) v0 i.val" := by
  classical
  intro b hb0 hbJ hbspan
  let R := Reduction.loc p
  let J := Reduction.Jcoord p M (act y) v0 0
  let f : R →ₗ[R] J := LinearMap.smulRight (LinearMap.id : R →ₗ[R] R) (⟨b,hbJ⟩ : J)
  have hfval (r : R) : (f r : ℂ) = ((r : ℚ) : ℂ) * b := by
    change r • b = _
    exact @yui_aux_0004 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006 r b
  have hfinj : Function.Injective f := by
    intro r s hrs
    have hh := congrArg (fun z : J => (z : ℂ)) hrs
    rw [hfval, hfval] at hh
    apply Subtype.ext
    exact Rat.cast_injective (mul_right_cancel₀ hb0 hh)
  have hfsurj : Function.Surjective f := by
    intro z
    have hz : (z : ℂ) ∈ Submodule.span R ({b} : Set ℂ) := by
      rw [← hbspan]
      exact z.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hr
  let g : R ≃ₗ[R] J := LinearEquiv.ofBijective f ⟨hfinj,hfsurj⟩
  obtain ⟨d, hd⟩ := h_T005.2.2.2
  let P : (Reduction.Ind l → R) ≃ₗ[R] (Reduction.Ind l → J) := LinearEquiv.piCongrRight (fun _ => g)
  have hinj : Function.Injective (Reduction.iota p M) := h_T004.1.2.2.2.1
  let j : Reduction.MR p M ≃ₗ[R] (Reduction.iota p M).range := LinearEquiv.ofInjective (Reduction.iota p M) hinj
  let E : (Reduction.Ind l → R) ≃ₗ[R] Reduction.MR p M := (P.trans d).trans j.symm
  let B : Basis (Reduction.Ind l) R (Reduction.MR p M) := (Pi.basisFun R (Reduction.Ind l)).map E
  refine ⟨B, ?_⟩
  intro i
  have hj (z : (Reduction.iota p M).range) : Reduction.iota p M (j.symm z) = (z : V) :=
    LinearEquiv.ofInjective_symm_apply (Reduction.iota p M) z
  change Reduction.iota p M (j.symm (d (P ((Pi.basisFun R (Reduction.Ind l)) i)))) = _
  rw [hj, hd]
  have hP (k : Reduction.Ind l) : (P ((Pi.basisFun R (Reduction.Ind l)) i) k : ℂ) = if k = i then b else 0 := by
    simp only [P, LinearEquiv.piCongrRight_apply, Pi.basisFun_apply]
    by_cases hk : k = i
    · subst k
      simp [Pi.single_apply, g, f]
    · simp [Pi.single_apply, hk, Ne.symm hk, g, f]
  rw [show (∑ k : Reduction.Ind l, (P ((Pi.basisFun R (Reduction.Ind l)) i) k : ℂ) • Reduction.e (act y) v0 k.val) =
    ∑ k : Reduction.Ind l, (if k = i then b else 0) • Reduction.e (act y) v0 k.val by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hP]]
  simp

end Local_T007
open Local_T007 in
theorem T007 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) :
    Reduction.commonFacts p l (act y) v0 M := by
  refine ⟨h_T005, h_T006, ?_⟩
  obtain ⟨b, hb0, hbJ, hbspan⟩ := @yui_aux_0006 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006
  refine ⟨b, hb0, hbJ, hbspan, ?_⟩
  exact @yui_aux_0007 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006 b hb0 hbJ hbspan

namespace Local_T008
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∃ red : Reduction.loc p →+* ZMod p, ∀ (a d : ℤ), ¬ (p : ℤ) ∣ d → ∀ r : Reduction.loc p, (r : ℚ) = (a : ℚ) / (d : ℚ) → red r * (d : ZMod p) = (a : ZMod p)" := by
  classical
  letI : Fact p.Prime := ⟨h_H001⟩
  let D : Submonoid ℤ :=
    { carrier := {d | ¬ (p : ℤ) ∣ d}
      one_mem' := by
        change ¬ (p : ℤ) ∣ ((1 : ℕ) : ℤ)
        simpa only [Int.natCast_dvd_natCast, Nat.dvd_one] using h_H001.ne_one
      mul_mem' := by
        intro a b ha hb hab
        exact (Int.prime_iff_natAbs_prime.mpr (by simpa using h_H001)).dvd_mul.mp hab |>.elim ha hb }
  have hs : Reduction.locSpec p := h_T004.1.1
  letI : IsLocalization D (Reduction.loc p) := (isLocalization_iff D _).mpr (by
    refine ⟨?_, ?_, ?_⟩
    · intro d
      have hd : (d.val : ℚ) ≠ 0 := by
        exact_mod_cast (show d.val ≠ 0 from fun hz => d.property (hz ▸ dvd_zero _))
      let t : Reduction.loc p := ⟨(d.val : ℚ)⁻¹, Subring.subset_closure ⟨d.val, d.property, rfl⟩⟩
      exact isUnit_iff_exists_inv.mpr ⟨t, Subtype.ext (by simpa [t] using mul_inv_cancel₀ hd)⟩
    · intro r
      obtain ⟨a,d,hd,he⟩ := (hs r.val).mp r.property
      refine ⟨⟨a, ⟨d,hd⟩⟩, Subtype.ext ?_⟩
      change (r : ℚ) * (d : ℚ) = (a : ℚ)
      rw [he, div_mul_cancel₀]
      exact_mod_cast (show d ≠ 0 from fun hz => hd (hz ▸ dvd_zero _))
    · intro a b he
      refine ⟨1, ?_⟩
      simpa using (Int.cast_injective (congrArg (fun z : Reduction.loc p => (z : ℚ)) he)))
  have hu : ∀ d : D, IsUnit ((Int.castRingHom (ZMod p)) d) := by
    intro d
    apply isUnit_iff_ne_zero.mpr
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd d.val p).not.mpr d.property
  let red : Reduction.loc p →+* ZMod p := IsLocalization.lift (M := D) hu
  refine ⟨red, ?_⟩
  intro a d hd r he
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 from fun hz => hd (hz ▸ dvd_zero _))
  have hr : r * (d : Reduction.loc p) = (a : Reduction.loc p) := by
    apply Subtype.ext
    change (r : ℚ) * (d : ℚ) = (a : ℚ)
    rw [he, div_mul_cancel₀ _ hd0]
  simpa using congrArg red hr

theorem yui_aux_0002 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ d : ℤ, ¬ (p : ℤ) ∣ d →\n  Function.Injective (fun u : ModN (Reduction.MR p M) p => (d : ZMod p) • u)" := by
  intro d hd
  letI : Fact p.Prime := ⟨h_H001⟩
  exact smul_right_injective (ModN (Reduction.MR p M) p)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).not.mpr hd)

theorem yui_aux_0003 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ (a : ℤ) (u : Reduction.MR p M),\n (ModN.mkQ p) ((a : Reduction.loc p) • u) =\n (a : ZMod p) • (ModN.mkQ p) u" := by
  intro a u
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem yui_aux_0004 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ red : Reduction.loc p →+* ZMod p,\n  (∀ (a d : ℤ), ¬ (p : ℤ) ∣ d → ∀ r : Reduction.loc p,\n    (r : ℚ) = (a : ℚ) / (d : ℚ) → red r * (d : ZMod p) = (a : ZMod p)) →\n  ∀ (r : Reduction.loc p) (u : Reduction.MR p M),\n    ModN.mkQ p (r • u) = red r • ModN.mkQ p u" := by
  intro red hred r u
  obtain ⟨a,d,hd,he⟩ := (h_T004.1.1 r.val).mp r.property
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 from fun hz => hd (hz ▸ dvd_zero _))
  have hr : (d : Reduction.loc p) * r = (a : Reduction.loc p) := by
    apply Subtype.ext
    change (d : ℚ) * (r : ℚ) = (a : ℚ)
    rw [he, mul_div_cancel₀ _ hd0]
  apply (@yui_aux_0002 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004 d hd)
  dsimp only
  rw [smul_smul, mul_comm (d : ZMod p), hred a d hd r he]
  calc
    (d : ZMod p) • ModN.mkQ p (r • u) =
        ModN.mkQ p ((d : Reduction.loc p) • (r • u)) := by
          exact (@yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004 d (r • u)).symm
    _ = ModN.mkQ p ((a : Reduction.loc p) • u) := by
      congr 1
      rw [smul_smul, hr]
    _ = (a : ZMod p) • ModN.mkQ p u :=
      @yui_aux_0003 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004 a u

theorem yui_aux_0005 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ f : Module.End ℤ M, ∃ F : Module.End (ZMod p) (ModN (Reduction.MR p M) p),\n ∀ u : Reduction.MR p M, F (ModN.mkQ p u) = ModN.mkQ p (f.baseChange (Reduction.loc p) u)" := by
  intro f
  let g : Reduction.MR p M →+ ModN (Reduction.MR p M) p :=
    (ModN.mkQ p).comp (f.baseChange (Reduction.loc p)).toAddMonoidHom
  have hg : ∀ u, p • g u = 0 := by
    intro u
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), CharP.cast_eq_zero (ZMod p) p, zero_smul]
  let F : Module.End (ZMod p) (ModN (Reduction.MR p M) p) :=
    ModN.liftEquiv'.symm ⟨g, hg⟩
  exact ⟨F, fun u => rfl⟩

theorem yui_aux_0006 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ (red : Reduction.loc p →+* ZMod p) (eps : ZMod p →+* K),\n letI : Algebra (Reduction.loc p) K := (eps.comp red).toAlgebra\n letI : Algebra (ZMod p) K := eps.toAlgebra\n ∀ (fw : (K ⊗[Reduction.loc p] Reduction.MR p M) →ₗ[K]\n       (K ⊗[ZMod p] ModN (Reduction.MR p M) p))\n   (bw : (K ⊗[ZMod p] ModN (Reduction.MR p M) p) →ₗ[K]\n       (K ⊗[Reduction.loc p] Reduction.MR p M)),\n fw.comp bw = LinearMap.id → bw.comp fw = LinearMap.id →\n ∃ Psi : (K ⊗[Reduction.loc p] Reduction.MR p M) ≃ₗ[K]\n       (K ⊗[ZMod p] ModN (Reduction.MR p M) p),\n Psi.toLinearMap = fw ∧ Psi.symm.toLinearMap = bw" := by
  intro red eps
  letI : Algebra (Reduction.loc p) K := (eps.comp red).toAlgebra
  letI : Algebra (ZMod p) K := eps.toAlgebra
  intro fw bw hfb hbf
  let Psi : (K ⊗[Reduction.loc p] Reduction.MR p M) ≃ₗ[K]
      (K ⊗[ZMod p] ModN (Reduction.MR p M) p) :=
    LinearEquiv.ofLinear fw bw hfb hbf
  exact ⟨Psi, rfl, rfl⟩

theorem yui_aux_0007 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ (red : Reduction.loc p →+* ZMod p)\n (eps : ZMod p →+* K),\n (∀ (r : Reduction.loc p) (u : Reduction.MR p M),\n    ModN.mkQ p (r • u) = red r • ModN.mkQ p u) →\n letI : Algebra (Reduction.loc p) K := (eps.comp red).toAlgebra\n letI : Algebra (ZMod p) K := eps.toAlgebra\n ∃ Psi : (K ⊗[Reduction.loc p] Reduction.MR p M) ≃ₗ[K]\n    (K ⊗[ZMod p] ModN (Reduction.MR p M) p),\n (∀ (c : K) (u : Reduction.MR p M),\n    Psi (c ⊗ₜ[Reduction.loc p] u) = c ⊗ₜ[ZMod p] ModN.mkQ p u) ∧\n (∀ (c : K) (u : Reduction.MR p M),\n    Psi.symm (c ⊗ₜ[ZMod p] ModN.mkQ p u) = c ⊗ₜ[Reduction.loc p] u)" := by
  intro red eps hq
  letI : Algebra (Reduction.loc p) K := (eps.comp red).toAlgebra
  letI : Algebra (ZMod p) K := eps.toAlgebra
  let q : Reduction.MR p M →ₗ[Reduction.loc p]
      (K ⊗[ZMod p] ModN (Reduction.MR p M) p) :=
    { toFun := fun u => 1 ⊗ₜ[ZMod p] ModN.mkQ p u
      map_add' := by intro u v; simp [TensorProduct.tmul_add]
      map_smul' := by
        intro r u
        dsimp
        rw [hq, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
        rfl }
  let fw := q.liftBaseChange K
  let g : Reduction.MR p M →+ (K ⊗[Reduction.loc p] Reduction.MR p M) :=
    (TensorProduct.mk (Reduction.loc p) K (Reduction.MR p M) 1).toAddMonoidHom
  have hg : ∀ u, p • g u = 0 := by
    intro u
    rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]
  let t : ModN (Reduction.MR p M) p →ₗ[ZMod p]
      (K ⊗[Reduction.loc p] Reduction.MR p M) :=
    ModN.liftEquiv'.symm ⟨g,hg⟩
  have ht : ∀ u, t (ModN.mkQ p u) = 1 ⊗ₜ[Reduction.loc p] u := fun u => rfl
  let bw := t.liftBaseChange K
  have hfw : ∀ c u, fw (c ⊗ₜ[Reduction.loc p] u) =
      c ⊗ₜ[ZMod p] ModN.mkQ p u := by
    intro c u
    simp [fw, q, TensorProduct.smul_tmul']
  have hbw : ∀ c u, bw (c ⊗ₜ[ZMod p] ModN.mkQ p u) =
      c ⊗ₜ[Reduction.loc p] u := by
    intro c u
    simp [bw, ht, TensorProduct.smul_tmul']
  have hbf : bw.comp fw = LinearMap.id := by
    ext c u
    simp [LinearMap.comp_apply, hfw, hbw]
  have hfb : fw.comp bw = LinearMap.id := by
    ext u
    induction u using QuotientAddGroup.induction_on with
    | H u =>
      change fw (bw (1 ⊗ₜ[ZMod p] ModN.mkQ p u)) = 1 ⊗ₜ[ZMod p] ModN.mkQ p u
      rw [hbw, hfw]
  obtain ⟨Psi, hPsi, hPsis⟩ :=
    @yui_aux_0006 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004
      red eps fw bw hfb hbf
  refine ⟨Psi, ?_, ?_⟩
  · intro c u
    change Psi.toLinearMap _ = _
    rw [hPsi, hfw]
  · intro c u
    change Psi.symm.toLinearMap _ = _
    rw [hPsis, hbw]

theorem yui_aux_0008 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ bar : Reduction.loc p →+* K,\n letI : Algebra (Reduction.loc p) K := bar.toAlgebra\n ∀ (s : Reduction.loc p) (c : K), s • c = bar s * c" := by
  intro bar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  intro s c
  rfl

theorem yui_aux_0009 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) : yui_aux_type% "∀ bar : Reduction.loc p →+* K,\n letI : Algebra (Reduction.loc p) K := bar.toAlgebra\n ∃ Phi : Reduction.VK K M ≃ₗ[K] (K ⊗[Reduction.loc p] Reduction.MR p M),\n (∀ (c : K) (m : M), Phi (c ⊗ₜ[ℤ] m) = c ⊗ₜ[Reduction.loc p] (1 ⊗ₜ[ℤ] m)) ∧\n (∀ (c : K) (s : Reduction.loc p) (m : M),\n   Phi.symm (c ⊗ₜ[Reduction.loc p] (s ⊗ₜ[ℤ] m)) = (c * bar s) ⊗ₜ[ℤ] m)" := by
  intro bar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  let Phi : Reduction.VK K M ≃ₗ[K] (K ⊗[Reduction.loc p] Reduction.MR p M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (Reduction.loc p) K K M).symm
  refine ⟨Phi, ?_, ?_⟩
  · intro c m
    rfl
  · intro c s m
    change (s • c) ⊗ₜ[ℤ] m = (c * bar s) ⊗ₜ[ℤ] m
    rw [@yui_aux_0008 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004 bar s c, mul_comm]

end Local_T008
open Local_T008 in
theorem T008 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) :
    Reduction.scalarFacts p K M := by
  classical
  letI : CharP K p := h_H002
  obtain ⟨red, hred⟩ :=
    @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004
  let eps : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  let bar : Reduction.loc p →+* K := eps.comp red
  refine ⟨bar, eps, ?_, ?_⟩
  · intro a d hd r he
    have hdK : (d : K) ≠ 0 := (CharP.intCast_eq_zero_iff K p d).not.mpr hd
    apply (eq_div_iff hdK).mpr
    simpa [bar, RingHom.comp_apply] using congrArg eps (hred a d hd r he)
  · letI : Algebra (Reduction.loc p) K := bar.toAlgebra
    letI : Algebra (ZMod p) K := eps.toAlgebra
    obtain ⟨Phi, hPhi, hPhis⟩ :=
      @yui_aux_0009 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004 bar
    have hq := @yui_aux_0004 p l K fieldK V addV modV act x y h v0 M
      h_H001 h_H002 h_H003 h_T004 red hred
    obtain ⟨Psi, hPsi, hPsis⟩ :=
      @yui_aux_0007 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004 red eps hq
    refine ⟨Phi, Psi, hPhi, hPhis, hPsi, hPsis, ?_⟩
    intro f
    constructor
    · apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c m => simp [LinearMap.comp_apply, hPhi]
      | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
    · obtain ⟨F, hF⟩ :=
        @yui_aux_0005 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004 f
      refine ⟨F, hF, ?_⟩
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c u => simp [LinearMap.comp_apply, hPsi, hF]
      | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

namespace Local_T009
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

theorem yui_aux_0013 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ {S W : Type*} [Field S] [AddCommGroup W] [Module S W] (c : Basis (Reduction.Ind l) S W) (i j k : Reduction.Ind l), Reduction.matrixUnit c i j (c k) = if k = j then c i else 0" := by
  intro S W _ _ _ c i j k
  classical
  by_cases hk : k = j
  · subst k; simp [Reduction.matrixUnit, Basis.coord_apply]
  · simp [Reduction.matrixUnit, Basis.coord_apply, hk, Ne.symm hk]

theorem yui_aux_0014 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) : yui_aux_type% "∀ (bar : Reduction.loc p →+* K), letI : Algebra (Reduction.loc p) K := bar.toAlgebra; ∀ (Phi : Reduction.VK K M ≃ₗ[K] (K ⊗[Reduction.loc p] Reduction.MR p M)), (∀ f : Module.End ℤ M, Phi.toLinearMap.comp (f.baseChange K) = ((f.baseChange (Reduction.loc p)).baseChange K).comp Phi.toLinearMap) → ∀ (A : Reduction.IntegralOps (act x) (act y) (act h) M) (a : Basis (Reduction.Ind l) (Reduction.loc p) (Reduction.MR p M)) (b : ℂ), (∀ i, Reduction.iota p M (a i) = b • Reduction.e (act y) v0 i.val) → ∀ i j : Reduction.Ind l, (Nat.choose l.toNat j.val : K) ≠ 0 ∧ Reduction.matrixUnit ((a.baseChange K).map Phi.symm) i j = (Nat.choose l.toNat j.val : K)⁻¹ • ((A.iX (l.toNat-i.val)).baseChange K * (A.iY l.toNat).baseChange K * (A.iX l.toNat).baseChange K * (A.iY (l.toNat-j.val)).baseChange K)" := by
  intro bar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  intro Phi hPhi A a b ha i j
  classical
  let beta := (a.baseChange K).map Phi.symm
  obtain ⟨c, hc⟩ := h_T002.2.2.2.2.1
  have hm := h_T004.2 c hc i j
  have hnK : (Nat.choose l.toNat j.val : K) ≠ 0 := by
    have hu : IsUnit (Nat.choose l.toNat j.val : K) := by
      simpa only [map_natCast] using hm.1.map bar
    exact hu.ne_zero
  have hnC : (Nat.choose l.toNat j.val : ℂ) ≠ 0 := by
    have hu : IsUnit (Nat.choose l.toNat j.val : ℂ) := by
      simpa only [map_natCast] using hm.1.map (algebraMap (Reduction.loc p) ℂ)
    exact hu.ne_zero
  refine ⟨hnK, ?_⟩
  let f : Module.End ℤ M := A.iX (l.toNat-i.val) * A.iY l.toNat * A.iX l.toNat * A.iY (l.toNat-j.val)
  let F : Module.End ℂ V := Reduction.divided (act x) (l.toNat-i.val) * Reduction.divided (act y) l.toNat * Reduction.divided (act x) l.toNat * Reduction.divided (act y) (l.toNat-j.val)
  have hf : ∀ m : M, (f m : V) = F m := by
    intro m
    simp only [f, F, Module.End.mul_apply, A.iX_spec, A.iY_spec]
  have hF : F = (Nat.choose l.toNat j.val : ℂ) • Reduction.matrixUnit c i j := by
    calc
      F = (Nat.choose l.toNat j.val : ℂ) • ((Nat.choose l.toNat j.val : ℂ)⁻¹ • F) := by
        rw [smul_smul, mul_inv_cancel₀ hnC, one_smul]
      _ = _ := congrArg (fun q => (Nat.choose l.toNat j.val : ℂ) • q) hm.2.2.2.1.symm
  have hact (k : Reduction.Ind l) :
      f.baseChange K (beta k) = (Nat.choose l.toNat j.val : K) • (if k = j then beta i else 0) := by
    have ht := yui_aux_0005 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 bar Phi a b ha f F hf (hPhi f)
    have he : F (Reduction.e (act y) v0 k.val) =
        (Nat.choose l.toNat j.val : ℂ) • (if k = j then Reduction.e (act y) v0 i.val else 0) := by
      rw [hF, LinearMap.smul_apply, ← hc k, yui_aux_0013 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 c i j k]
      simp only [hc]
    by_cases hk : k = j
    · subst k
      simpa [beta] using ht j i (Nat.choose l.toNat j.val : ℤ) (by simpa using he)
    · have hz := ht k i 0 (by simpa [hk] using he)
      simpa [hk, beta] using hz
  apply beta.ext
  intro k
  simp only [LinearMap.smul_apply]
  have hb : ((A.iX (l.toNat-i.val)).baseChange K * (A.iY l.toNat).baseChange K * (A.iX l.toNat).baseChange K * (A.iY (l.toNat-j.val)).baseChange K) = f.baseChange K := by
    simp only [f, LinearMap.baseChange_mul]
  rw [hb, hact, yui_aux_0013 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 beta i j k]
  rw [smul_smul, inv_mul_cancel₀ hnK, one_smul]

end Local_T009
open Local_T009 in
theorem T009 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T007 : Reduction.commonFacts p l (act y) v0 M) (h_T008 : Reduction.scalarFacts p K M) :
    Reduction.reductionFacts p l K (act x) (act y) (act h) M := by
  classical
  refine ⟨h_T008, ?_⟩
  intro A
  obtain ⟨b, hb0, hbmem, hbspan, a, ha⟩ := h_T007.2.2
  have hscalar := h_T008
  obtain ⟨bar, eps, hbar, hbridges⟩ := hscalar
  letI : Algebra (Reduction.loc p) K := bar.toAlgebra
  letI : Algebra (ZMod p) K := eps.toAlgebra
  obtain ⟨Phi, Psi, hPhi, hPhiInv, hPsi, hPsiInv, hcompat⟩ := hbridges
  have htransport (f : Module.End ℤ M) :
      Phi.toLinearMap.comp (f.baseChange K) =
        ((f.baseChange (Reduction.loc p)).baseChange K).comp Phi.toLinearMap :=
    (hcompat f).1
  let beta : Basis (Reduction.Ind l) K (Reduction.VK K M) := (a.baseChange K).map Phi.symm
  refine ⟨beta, Reduction.matrixUnit beta, ?_⟩
  refine ⟨?_, h_T002.2.2.1, ?_, ?_, ?_, ?_⟩
  · simpa only [Reduction.Ind, Fintype.card_fin] using Module.finrank_eq_card_basis beta
  · exact yui_aux_0006 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 bar Phi htransport A a b ha
  · intro i j k
    exact yui_aux_0013 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 beta i j k
  · exact yui_aux_0014 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 bar Phi htransport A a b ha
  · intro r hr
    exact ⟨yui_aux_0010 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 r hr,
      yui_aux_0012 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 A.ix (A.iX r) (act x) r A.ix_spec (A.iX_spec r) hr,
      yui_aux_0012 p l K V act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008 A.iy (A.iY r) (act y) r A.iy_spec (A.iY_spec r) hr⟩

namespace Local_T010
theorem yui_aux_0001 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T009 : Reduction.reductionFacts p l K (act x) (act y) (act h) M) : yui_aux_type% "∀ (W : Submodule K (Reduction.VK K M)) (f g : Module.End K (Reduction.VK K M)), (Reduction.stable W f → Reduction.stable W g → Reduction.stable W (f * g)) ∧ (Reduction.stable W f → ∀ c : K, Reduction.stable W (c • f)) ∧ (Reduction.stable W f → ∀ r : ℕ, Reduction.stable W (f ^ r))" := by
  intro W f g
  have hmul : ∀ (a b : Module.End K (Reduction.VK K M)), Reduction.stable W a → Reduction.stable W b → Reduction.stable W (a * b) := by
    intro a b ha hb w hw
    exact ha (b w) (hb w hw)
  refine ⟨hmul f g, ?_, ?_⟩
  · intro hf c w hw
    exact W.smul_mem c (hf w hw)
  · intro hf r
    induction r with
    | zero =>
        intro w hw
        simpa only [pow_zero, Module.End.one_apply] using hw
    | succ r ih =>
        rw [pow_succ]
        exact hmul (f ^ r) f ih hf

end Local_T010
open Local_T010 in
theorem T010 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T009 : Reduction.reductionFacts p l K (act x) (act y) (act h) M) :
    Reduction.invariantFacts p l K (act x) (act y) (act h) M := by
  classical
  have hclosure := @yui_aux_0001 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T009
  obtain ⟨A0⟩ := h_T004.1.2.1
  obtain ⟨beta0, T0, hr0⟩ := h_T009.2 A0
  refine ⟨?_, ?_⟩
  · apply Module.nontrivial_of_finrank_pos (R := K)
    rw [hr0.1]
    exact hr0.2.1
  · intro A
    obtain ⟨beta, T, hr⟩ := h_T009.2 A
    refine ⟨beta, T, hr, ?_⟩
    intro W hx hy hh
    have hmul (f g : Module.End K (Reduction.VK K M))
        (hf : Reduction.stable W f) (hg : Reduction.stable W g) :
        Reduction.stable W (f * g) := (hclosure W f g).1 hf hg
    have hsmul (f : Module.End K (Reduction.VK K M)) (c : K)
        (hf : Reduction.stable W f) : Reduction.stable W (c • f) :=
      (hclosure W f f).2.1 hf c
    have hpow (f : Module.End K (Reduction.VK K M))
        (hf : Reduction.stable W f) (r : ℕ) : Reduction.stable W (f ^ r) :=
      (hclosure W f f).2.2 hf r
    have hX (r : ℕ) (hrange : r ≤ l.toNat) :
        Reduction.stable W ((A.iX r).baseChange K) := by
      rw [(hr.2.2.2.2.2 r hrange).2.1]
      exact hsmul _ _ (hpow _ hx r)
    have hY (r : ℕ) (hrange : r ≤ l.toNat) :
        Reduction.stable W ((A.iY r).baseChange K) := by
      rw [(hr.2.2.2.2.2 r hrange).2.2]
      exact hsmul _ _ (hpow _ hy r)
    intro i j
    rw [(hr.2.2.2.2.1 i j).2]
    exact hsmul _ _ (hmul _ _
      (hmul _ _
        (hmul _ _ (hX _ (Nat.sub_le _ _)) (hY _ le_rfl))
        (hX _ le_rfl))
      (hY _ (Nat.sub_le _ _)))

theorem T011 (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T009 : Reduction.reductionFacts p l K (act x) (act y) (act h) M) (h_T010 : Reduction.invariantFacts p l K (act x) (act y) (act h) M) :
    Reduction.endpoint K (act x) (act y) (act h) M := by
  classical
  rcases h_T004.1.2.1 with ⟨A⟩
  rcases h_T010 with ⟨hnt, hInv⟩
  rcases hInv A with ⟨beta, T, hred, hstable⟩
  refine ⟨A, hnt, ?_⟩
  intro W hx hy hh
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hj : ∃ j : Reduction.Ind l, beta.repr w j ≠ 0 := by
      by_contra! hn
      apply hw0
      rw [← beta.sum_repr w]
      simp [hn]
    obtain ⟨j, hj⟩ := hj
    have hT := hred.2.2.2.1
    have hb : ∀ i : Reduction.Ind l, beta i ∈ W := by
      intro i
      have haction : T i j w = beta.repr w j • beta i := by
        conv_lhs => rw [← beta.sum_repr w]
        rw [map_sum]
        simp [map_smul, hT]
      have hmem : beta.repr w j • beta i ∈ W := by
        rw [← haction]
        exact hstable W hx hy hh i j w hw
      have hdiv := W.smul_mem ((beta.repr w j)⁻¹) hmem
      simpa [smul_smul, hj] using hdiv
    apply top_unique
    intro z hz
    rw [← beta.sum_repr z]
    exact W.sum_mem fun i hi => W.smul_mem _ (hb i)

set_option Elab.async false in
theorem P (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_H007 : Reduction.admissible M (act x) (act y)) :
    Reduction.endpoint K (act x) (act y) (act h) M := by
  have h_T001 : Reduction.strings l (act x) (act y) (act h) v0 := @T001 p l K fieldK V addV modV act x y h v0 M h_H005 h_H006
  have h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0 := @T002 p l K fieldK V addV modV act x y h v0 M h_H003 h_H004 h_H005 h_H006 h_T001
  have h_T003 : Reduction.latticeFacts p l (act x) (act y) (act h) M := @T003 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
  have h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M := @T004 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_T002 h_T003
  have h_T005 : Reduction.coordinateFacts p l (act y) v0 M := @T005 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004
  have h_T006 : Reduction.rationalFacts p (act y) v0 M := @T006 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005
  have h_T007 : Reduction.commonFacts p l (act y) v0 M := @T007 p l K fieldK V addV modV act x y h v0 M h_H001 h_T002 h_T004 h_T005 h_T006
  have h_T008 : Reduction.scalarFacts p K M := @T008 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_T004
  have h_T009 : Reduction.reductionFacts p l K (act x) (act y) (act h) M := @T009 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T007 h_T008
  have h_T010 : Reduction.invariantFacts p l K (act x) (act y) (act h) M := @T010 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T009
  have h_T011 : Reduction.endpoint K (act x) (act y) (act h) M := @T011 p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_H005 h_T002 h_T004 h_T009 h_T010
  exact h_T011

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_H007 : Reduction.admissible M (act x) (act y)) : Reduction.endpoint K (act x) (act y) (act h) M := by
  exact @Translation.P.{_, _} p l K fieldK V addV modV act x y h v0 M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 h_H007

#check @P
#print axioms P
end AuditBExport

/- Trusted inspector appended after the generated proof, never a worker tool.
   Its only substitution is an array of escaped (id, selector, expected type) strings. -/
namespace NL2LeanAuditProbe
open Lean Meta Elab Command Term

private def nameOf (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def showType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def binderInventory (type : Expr) : MetaM Json :=
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    for x in xs do
      let d ← getFVarLocalDecl x
      rows := rows.push <| Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← showType d.type)), ("proof_valued", toJson (← isProp d.type))]
    return Json.mkObj [("binders", toJson rows), ("result", toJson (← showType body))]

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
    ("type", toJson (← showType info.type)),
    ("signature", ← binderInventory info.type),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("direct_constants", toJson ((info.getUsedConstantsAsSet.toArray.qsort Name.lt).map Name.toString)),
    ("axioms", toJson ((← collectAxioms name).map Name.toString))]

private def inspect (roots : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    rows := rows.push (← record name)
    if !(← getEnv).isImportedConst name then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
  return Json.mkObj [("declarations", toJson rows), ("truncated", toJson (!pending.isEmpty))]

private def actualType (selector : String) (parts : Array String) : TermElabM Expr := do
  if selector.startsWith "decl:" then
    return (← getConstInfo (nameOf parts)).type
  if selector.startsWith "premise:" then
    let wanted := "h_" ++ (selector.drop 8).toString
    let root ← getConstInfo `AuditBExport.P
    return ← forallTelescope root.type fun xs _ => do
      let mut context : Array Expr := #[]
      for x in xs do
        let binder ← getFVarLocalDecl x
        if binder.userName.toString == wanted then
          return ← mkForallFVars context binder.type
        context := context.push x
      throwError "Missing actual root premise {wanted}"
  throwError "Unsupported selector {selector}"

/- Universe parameter names belong to each declaration's binder scope.
   Rename them bijectively, retaining repetitions and all level expressions.
   This is alpha-equivalence, not a proof of logical equivalence. -/
private def sameSignature (actual expected : Expr) : MetaM (Bool × String) := do
  if ← withoutModifyingState <| isDefEq actual expected then
    return (true, "definitional")
  let actualParams := (collectLevelParams {} actual).params.toList
  let expectedParams := (collectLevelParams {} expected).params.toList
  if actualParams.length != expectedParams.length then
    return (false, "different_universe_binders")
  let levels := (List.range actualParams.length).map fun i =>
    Level.param (Name.mkSimple ("_yuiAuditLevel" ++ toString i))
  let equal ← withoutModifyingState <| isDefEq
    (actual.instantiateLevelParams actualParams levels)
    (expected.instantiateLevelParams expectedParams levels)
  return (equal, "bijective_universe_renaming")

elab "#nl2lean_audit_probe" : command => do
  let result ← liftTermElabM <| withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
    let checks : Array (String × String × String × Array String) := #[("P", "decl:AuditBExport.P", "∀ (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_H007 : Reduction.admissible M (act x) (act y)), Reduction.endpoint K (act x) (act y) (act h) M", #["AuditBExport", "P"]), ("__frozen__P", "decl:AuditBExport.P", "∀ (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H004 : Reduction.highestModule l act x h) (h_H005 : Reduction.chevalley x y h) (h_H006 : v0 ≠ 0 ∧ act x v0 = 0 ∧ act h v0 = (l : ℂ) • v0) (h_H007 : Reduction.admissible M (act x) (act y)), Reduction.endpoint K (act x) (act y) (act h) M", #["AuditBExport", "P"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`AuditBExport.P]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      let row := Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if id.startsWith "__frozen__" then
        frozenComparisons := frozenComparisons.push row
      else
        comparisons := comparisons.push row
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons),
      ("frozen_comparisons", toJson frozenComparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

#nl2lean_audit_probe
end NL2LeanAuditProbe
