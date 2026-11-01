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

#check @T008
#print axioms T008

end Translation
