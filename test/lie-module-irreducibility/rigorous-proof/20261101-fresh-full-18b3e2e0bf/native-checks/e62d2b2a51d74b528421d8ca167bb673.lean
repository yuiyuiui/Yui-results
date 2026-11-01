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

theorem checked (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H003 : 0 ≤ l ∧ l < (p : ℤ)) (h_H005 : Reduction.chevalley x y h) (h_H007 : Reduction.admissible M (act x) (act y)) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) : yui_aux_type% "∀ b : Basis (Reduction.Ind l) ℂ V, LinearIndependent (Reduction.loc p) b" := by
  intro b
  have ht : IsScalarTower (Reduction.loc p) ℂ V := Reduction.locTower p
  have hi := @yui_aux_0006 p l K fieldK V addV modV act x y h v0 M h_H001 h_H003 h_H005 h_H007 h_T002
  exact @LinearIndependent.restrict_scalars (Reduction.Ind l) (Reduction.loc p) V
    _ _ _ b ℂ _ (inferInstance : SMulWithZero (Reduction.loc p) ℂ) _ ht
    (by intro r s hrs; apply hi; simpa only [Algebra.smul_def, mul_one] using hrs)
    b.linearIndependent
#check @checked
#print axioms checked
end YuiAuxiliary
