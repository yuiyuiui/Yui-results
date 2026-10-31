import Mathlib
open scoped TensorProduct
noncomputable section
namespace SL2Reduction
abbrev Index (lam : ℤ) := Fin (lam.toNat + 1)
def localRing (p : ℕ) : Subalgebra ℤ ℚ :=
  Algebra.adjoin ℤ {q : ℚ | ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)}
abbrev R (p : ℕ) := ↥(localRing p)
instance complexAlgebra (p : ℕ) : Algebra (R p) ℂ :=
  ((algebraMap ℚ ℂ).comp (localRing p).val.toRingHom).toAlgebra
instance ratComplexTower (p : ℕ) : IsScalarTower (R p) ℚ ℂ :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
instance (priority := 50) localModule (p : ℕ) : Module (R p) V := Module.restrictScalars (R p) ℂ V
instance (priority := 50) localTower (p : ℕ) : IsScalarTower (R p) ℂ V := IsScalarTower.restrictScalars (R p) ℂ V
def divided (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r
def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V := divided y i v
abbrev MR (p : ℕ) (M : Submodule ℤ V) := R p ⊗[ℤ] M
abbrev VK (K : Type*) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
def iota (p : ℕ) (M : Submodule ℤ V) : MR p M →ₗ[R p] V :=
  M.subtype.liftBaseChange (R p)
def localizedImage (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) V :=
  (iota p M).range
def Ji (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) : Submodule (R p) ℂ :=
  (localizedImage p M).comap ((LinearMap.toSpanSingleton ℂ V (e y v i)).restrictScalars (R p))
def J (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) := Ji p M y v 0
def qmul (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) :
  (ℚ ⊗[R p] J p M y v) →ₗ[ℚ] ℂ :=
  (J p M y v).subtype.liftBaseChange ℚ

def Preserves (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ m : M, f (m : V) ∈ M
def RPreserves (p : ℕ) (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ u ∈ localizedImage p M, f u ∈ localizedImage p M
structure LatticeOps (M : Submodule ℤ V) where
  x : Module.End ℤ M
  y : Module.End ℤ M
  h : Module.End ℤ M
  X : ℕ → Module.End ℤ M
  Y : ℕ → Module.End ℤ M
def Agrees (M : Submodule ℤ V) (x y h : Module.End ℂ V) (a : LatticeOps M) : Prop :=
  (∀ m : M, (a.x m : V) = x (m : V)) ∧
  (∀ m : M, (a.y m : V) = y (m : V)) ∧
  (∀ m : M, (a.h m : V) = h (m : V)) ∧
  (∀ r (m : M), (a.X r m : V) = divided x r (m : V)) ∧
  (∀ r (m : M), (a.Y r m : V) = divided y r (m : V))
def Invariant {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (W : Submodule F U) (f : Module.End F U) : Prop :=
  ∀ u ∈ W, f u ∈ W
def Simple {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (x y h : Module.End F U) : Prop :=
  Nontrivial U ∧ ∀ W : Submodule F U,
    Invariant W x → Invariant W y → Invariant W h → W = ⊥ ∨ W = ⊤
def Highest (lam : ℤ) (x h : Module.End ℂ V) : Prop :=
  ∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lam : ℂ) • w
def Admissible (M : Submodule ℤ V) (x y : Module.End ℂ V) : Prop :=
  (∃ (d : ℕ) (b : Module.Basis (Fin d) ℤ M) (c : Module.Basis (Fin d) ℂ V),
    ∀ i, (b i : V) = c i) ∧
  ∀ r : ℕ, Preserves M (divided x r) ∧ Preserves M (divided y r)
def extendFamily {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (b : Index lam → U) (i : ℕ) : U :=
  if hi : i < lam.toNat + 1 then b ⟨i, hi⟩ else 0
def GeneratorFormulas {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (b : Index lam → U) (x y h : Module.End F U) : Prop :=
  ∀ i : Index lam,
    x (b i) = (if i.val = 0 then 0 else
      (((lam - (i.val : ℤ) + 1 : ℤ) : F) • extendFamily (F := F) lam b (i.val - 1))) ∧
    y (b i) = ((i.val + 1 : ℕ) : F) • extendFamily (F := F) lam b (i.val + 1) ∧
    h (b i) = (((lam - 2 * (i.val : ℤ) : ℤ) : F) • b i)
def DividedFormulas {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (b : Index lam → U) (X Y : ℕ → Module.End F U) : Prop :=
  ∀ (i : Index lam) (r : ℕ),
    X r (b i) = (if r ≤ i.val then
      ((Nat.choose (lam.toNat - i.val + r) r : ℕ) : F) • extendFamily (F := F) lam b (i.val - r)
      else 0) ∧
    Y r (b i) = ((Nat.choose (i.val + r) r : ℕ) : F) • extendFamily (F := F) lam b (i.val + r)
def E (lam : ℤ) (b : Module.Basis (Index lam) ℂ V) (i j : Index lam) : Module.End ℂ V :=
  (b.coord j).smulRight (b i)
def MatrixWord {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (lam : ℤ) (X Y : ℕ → Module.End F U) (i j : Index lam) : Module.End F U :=
  ((Nat.choose lam.toNat j.val : F)⁻¹) •
    (X (lam.toNat - i.val) * (Y lam.toNat * X lam.toNat) * Y (lam.toNat - j.val))
def BasisLift (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop :=
  ∃ c : Module.Basis (Index lam) (R p) (MR p M),
    ∀ i, iota p M (c i) = b • e y v i.val
def Principal (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop :=
  b ≠ 0 ∧ J p M y v = Submodule.span (R p) {b}
def Target (K : Type*) [Field K] (M : Submodule ℤ V) (x y h : Module.End ℂ V) : Prop :=
  ∃ a : LatticeOps M, Agrees M x y h a ∧
    Simple (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K)


def Lowering (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  ∀ t : ℕ,
    h ((y ^ t) v) = (((lam - 2 * (t : ℤ) : ℤ) : ℂ) • (y ^ t) v) ∧
    x ((y ^ (t + 1)) v) =
      (((((t + 1 : ℕ) : ℤ) * (lam - (t : ℤ)) : ℤ) : ℂ) • (y ^ t) v)
def CoordinateCore (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  (∃ b : Module.Basis (Index lam) ℂ V, ∀ i, b i = e y v i.val) ∧
  (∀ t : ℕ, lam.toNat < t → (y ^ t) v = 0) ∧
  GeneratorFormulas lam (fun i : Index lam => e y v i.val) x y h
def Coordinates (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  ((lam.toNat + 1 : ℕ) : ℤ) = lam + 1 ∧
  0 < lam.toNat + 1 ∧ Fintype.card (Index lam) = lam.toNat + 1 ∧
  Lowering lam x y h v ∧
  (∀ i : Index lam, e y v i.val ≠ 0) ∧
  CoordinateCore lam x y h v ∧
  DividedFormulas lam (fun i : Index lam => e y v i.val) (divided x) (divided y)
def LocalLattice (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (x y h : Module.End ℂ V) : Prop :=
  Function.Injective (iota p M) ∧
  (iota p M).range = Submodule.span (R p) (M : Set V) ∧
  Nonempty (Module.Basis (Index lam) (R p) (MR p M)) ∧
  Submodule.span ℂ (localizedImage p M : Set V) = ⊤ ∧
  (∀ r, Preserves M (divided x r) ∧ Preserves M (divided y r) ∧
    RPreserves p M (divided x r) ∧ RPreserves p M (divided y r)) ∧
  Preserves M x ∧ Preserves M y ∧ Preserves M h ∧
  RPreserves p M x ∧ RPreserves p M y ∧ RPreserves p M h ∧
  ∃ a : LatticeOps M, Agrees M x y h a
def MatrixIdentities (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (x y : Module.End ℂ V) (v : V) : Prop :=
  ∀ b : Module.Basis (Index lam) ℂ V, (∀ i, b i = e y v i.val) →
  ∀ i j : Index lam,
    (divided y lam.toNat * divided x lam.toNat) =
      E lam b (Fin.last lam.toNat) (Fin.last lam.toNat) ∧
    divided x (lam.toNat - i.val) * (divided y lam.toNat * divided x lam.toNat) =
      E lam b i (Fin.last lam.toNat) ∧
    (divided y lam.toNat * divided x lam.toNat) * divided y (lam.toNat - j.val) =
      (Nat.choose lam.toNat j.val : ℂ) • E lam b (Fin.last lam.toNat) j ∧
    (∃ c : R p, (c : ℚ) = (Nat.choose lam.toNat j.val : ℚ) ∧ IsUnit c) ∧
    E lam b i j = MatrixWord lam (divided x) (divided y) i j ∧
    RPreserves p M (E lam b i j)
def CommonModule (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (y : Module.End ℂ V) (v : V) : Prop :=
  (∀ i : Index lam, Ji p M y v i.val = J p M y v) ∧
  Nontrivial (J p M y v) ∧ Module.Finite (R p) (J p M y v) ∧
  ∃ c : (Index lam → J p M y v) ≃ₗ[R p] MR p M,
    ∀ g, iota p M (c g) = ∑ i : Index lam, (g i : ℂ) • e y v i.val
def RationalLine (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  Function.Injective (qmul p M y v) ∧
  (qmul p M y v).range = Submodule.span ℚ (J p M y v : Set ℂ) ∧
  Module.Finite ℚ (ℚ ⊗[R p] J p M y v) ∧
  Module.finrank ℚ (ℚ ⊗[R p] J p M y v) = 1
def PrincipalLattice (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (y : Module.End ℂ V) (v : V) : Prop :=
  RationalLine p M y v ∧ (∃ b : ℂ, Principal p M y v b) ∧
  ∀ b : ℂ, Principal p M y v b → BasisLift p lam M y v b
def TensorMaps (p : ℕ) (K : Type*) [Field K] (hp : CharP K p) (M : Submodule ℤ V)
    (kap : R p →+* K) : Prop :=
  letI : CharP K p := hp
  letI : Algebra (R p) K := kap.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  ∃ (phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M))
    (psi : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p)),
    (∀ (c : K) (m : M), phi (c ⊗ₜ[ℤ] m) = c ⊗ₜ[R p] (1 ⊗ₜ[ℤ] m)) ∧
    (∀ (c : K) (u : MR p M), psi (c ⊗ₜ[R p] u) =
      c ⊗ₜ[ZMod p] (ModN.mkQ p u)) ∧
    (∀ (f : Module.End ℤ M) (z : VK K M),
      phi (f.baseChange K z) = (f.baseChange (R p)).baseChange K (phi z)) ∧
    (∀ f : Module.End (R p) (MR p M),
      ∃ fbar : Module.End (ZMod p) (ModN (MR p M) p),
        (∀ u, fbar (ModN.mkQ p u) = ModN.mkQ p (f u)) ∧
        ∀ z, psi (f.baseChange K z) = fbar.baseChange K (psi z))
def ScalarReduction (p : ℕ) (K : Type*) [Field K] (M : Submodule ℤ V) : Prop :=
  ∃ (hp : CharP K p) (kap : R p →+* K),
    (∀ (r : R p) (a b : ℤ), b ≠ 0 → ¬ (p : ℤ) ∣ b →
      (r : ℚ) = (a : ℚ) / (b : ℚ) → kap r = (a : K) / (b : K)) ∧
    TensorMaps p K hp M kap
def ReducedBasis (p : ℕ) (lam : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (x y h : Module.End ℂ V) (v : V) : Prop :=
  ∀ a : LatticeOps M, Agrees M x y h a →
  ∃ (beta : Module.Basis (Index lam) K (VK K M)) (b : ℂ),
    Principal p M y v b ∧
    (∃ (kap : R p →+* K),
      letI : Algebra (R p) K := kap.toAlgebra
      ∃ (phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M))
        (c : Module.Basis (Index lam) (R p) (MR p M)),
        (∀ (s : K) (m : M), phi (s ⊗ₜ[ℤ] m) = s ⊗ₜ[R p] (1 ⊗ₜ[ℤ] m)) ∧
        (∀ i, iota p M (c i) = b • e y v i.val) ∧
        ∀ i, phi (beta i) = 1 ⊗ₜ[R p] (c i)) ∧
    Module.finrank K (VK K M) = lam.toNat + 1 ∧
    GeneratorFormulas lam (fun i => beta i) (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K)
def ReducedUnits (lam : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (x y h : Module.End ℂ V) : Prop :=
  (∀ r : ℕ, r ≤ lam.toNat → (r.factorial : K) ≠ 0) ∧
  (∀ j : Index lam, (Nat.choose lam.toNat j.val : K) ≠ 0) ∧
  ∀ a : LatticeOps M, Agrees M x y h a →
    (∀ r : ℕ, r ≤ lam.toNat →
      (a.X r).baseChange K = (r.factorial : K)⁻¹ • (a.x.baseChange K) ^ r ∧
      (a.Y r).baseChange K = (r.factorial : K)⁻¹ • (a.y.baseChange K) ^ r) ∧
    ∀ beta : Module.Basis (Index lam) K (VK K M),
      GeneratorFormulas lam (fun i => beta i) (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) →
      ∀ i j k : Index lam,
        MatrixWord lam (fun r => (a.X r).baseChange K) (fun r => (a.Y r).baseChange K) i j (beta k) =
          if j = k then beta i else 0

end SL2Reduction
open SL2Reduction

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = (lam + 1).toNat ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧ Highest lam x h ∧ Simple x y h) (h_T001 : Lowering lam x y h v) (h_T002 : ∀ i : Index lam, e y v i.val ≠ 0 ∧ h (e y v i.val) = (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) • e y v i.val)) : yui_aux_type% "LinearIndependent ℂ (fun i : Index lam => e y v i.val)" := by
  classical
  let μ : Index lam → ℂ := fun i => ((lam - 2 * (i.val : ℤ) : ℤ) : ℂ)
  have hinj : Function.Injective μ := by
    intro i j hij
    have hij' : lam - 2 * (i.val : ℤ) = lam - 2 * (j.val : ℤ) := by
      dsimp [μ] at hij
      exact_mod_cast hij
    apply Fin.ext
    omega
  have hprod : ∀ s : Finset (Index lam), ∃ P : Module.End ℂ V,
      ∀ i, P (e y v i.val) = (∏ k ∈ s, (μ i - μ k)) • e y v i.val := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | @insert k s hk ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨(h - μ k • 1) * P, ?_⟩
      intro i
      simp only [Module.End.mul_apply, hP, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, (h_T002 i).2,
        Finset.prod_insert hk]
      dsimp [μ]
      module
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  obtain ⟨P, hP⟩ := hprod (Finset.univ.erase j)
  have hp := congrArg P hc
  simp only [map_sum, map_smul, hP, map_zero, smul_smul] at hp
  have hzero : ∀ i : Index lam, i ≠ j →
      ∏ k ∈ Finset.univ.erase j, (μ i - μ k) = 0 := by
    intro i hij
    exact Finset.prod_eq_zero_iff.mpr ⟨i, by simp [hij], sub_self _⟩
  have hsingle : (∑ i : Index lam,
      (c i * ∏ k ∈ Finset.univ.erase j, (μ i - μ k)) • e y v i.val) =
      (c j * ∏ k ∈ Finset.univ.erase j, (μ j - μ k)) • e y v j.val := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      rw [hzero i hij, mul_zero, zero_smul]
    · simp
  rw [hsingle] at hp
  have hn : (∏ k ∈ Finset.univ.erase j, (μ j - μ k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hk).1 (hinj he).symm)
  exact (mul_eq_zero.mp ((smul_eq_zero.mp hp).resolve_right (h_T002 j).1)).resolve_right hn
#check @checked
#print axioms checked
end YuiAuxiliary
