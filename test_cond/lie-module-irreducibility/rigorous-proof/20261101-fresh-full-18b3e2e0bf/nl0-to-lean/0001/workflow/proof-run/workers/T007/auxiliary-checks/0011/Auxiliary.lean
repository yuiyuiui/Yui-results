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

theorem checked (p : ℕ) (l : ℤ) (K : Type v) [fieldK : Field K] (V : Type u) [addV : AddCommGroup V] [modV : Module ℂ V] (act : Reduction.SL →ₗ⁅ℂ⁆ Module.End ℂ V) (x : Reduction.SL) (y : Reduction.SL) (h : Reduction.SL) (v0 : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_T002 : Reduction.basisFacts l (act x) (act y) (act h) v0) (h_T004 : Reduction.localizationFacts p l (act x) (act y) (act h) v0 M) (h_T005 : Reduction.coordinateFacts p l (act y) v0 M) (h_T006 : Reduction.rationalFacts p (act y) v0 M) : yui_aux_type% "∃ b : ℂ, b ≠ 0 ∧ b ∈ Reduction.Jcoord p M (act y) v0 0 ∧ Reduction.Jcoord p M (act y) v0 0 = Submodule.span (Reduction.loc p) ({b} : Set ℂ)" := by
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
#check @checked
#print axioms checked
end YuiAuxiliary
