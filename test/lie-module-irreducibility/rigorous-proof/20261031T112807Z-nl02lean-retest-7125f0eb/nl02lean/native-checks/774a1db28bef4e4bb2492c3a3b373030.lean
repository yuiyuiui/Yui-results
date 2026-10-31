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

namespace Translation
set_option autoImplicit false

theorem T016 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T007 : LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v) (h_T013 : PrincipalLattice p lam M y v) (h_T014 : ScalarReduction p K M) (h_T015 : ReducedBasis p lam K M x y h v) :
    ScalarReduction p K M ∧ ReducedBasis p lam K M x y h v ∧ ReducedUnits lam K M x y h ∧ ∃ a : LatticeOps M, Agrees M x y h a := by
  classical
  have hn : (∀ r : ℕ, r ≤ lam.toNat → (r.factorial : K) ≠ 0) ∧
      (∀ j : Index lam, (Nat.choose lam.toNat j.val : K) ≠ 0) := by
    letI : CharP K p := h_H001.2
    have hlt : lam.toNat < p := by omega
    have hf : ∀ r : ℕ, r ≤ lam.toNat → (r.factorial : K) ≠ 0 := by
      intro r hr hz
      have hd := (CharP.cast_eq_zero_iff K p r.factorial).mp hz
      have := (h_H001.1.dvd_factorial).mp hd
      omega
    refine ⟨hf, ?_⟩
    intro j hj
    have he : (Nat.choose lam.toNat j.val : K) * (j.val.factorial : K) *
        ((lam.toNat - j.val).factorial : K) = (lam.toNat.factorial : K) := by
      simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : K))
        (Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ j.isLt))
    rw [hj, zero_mul, zero_mul] at he
    exact hf lam.toNat le_rfl he.symm
  have hdiv : ∀ a : LatticeOps M, Agrees M x y h a →
   (∀ r : ℕ, r ≤ lam.toNat →
   (a.X r).baseChange K = (r.factorial : K)⁻¹ • (a.x.baseChange K) ^ r ∧
   (a.Y r).baseChange K = (r.factorial : K)⁻¹ • (a.y.baseChange K) ^ r) := by
    have hfac : ∀ (f : Module.End ℤ M) (F : Module.End ℂ V) (D : ℕ → Module.End ℤ M),
     (∀ m : M, (f m : V) = F (m : V)) →
     (∀ r (m : M), (D r m : V) = divided F r (m : V)) →
     ∀ r, (r.factorial : K) • (D r).baseChange K = (f.baseChange K) ^ r := by
     intro f F D hf hD r
     have hp : ∀ n (m : M), ((f ^ n) m : V) = (F ^ n) (m : V) := by
       intro n
       induction n with
       | zero => intro m; rfl
       | succ n ih =>
         intro m
         simpa only [pow_succ', Module.End.mul_apply] using
           (hf ((f ^ n) m)).trans (congrArg F (ih m))
     have he : (r.factorial : ℤ) • D r = f ^ r := by
       ext m
       change (r.factorial : ℤ) • (D r m : V) = ((f ^ r) m : V)
       rw [hD, hp]
       simp [divided, LinearMap.smul_apply, smul_smul,
         ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℤ,
         Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)]
     have hk := congrArg (fun f : Module.End ℤ M => f.baseChange K) he
     simp only [LinearMap.baseChange_smul, LinearMap.baseChange_pow] at hk
     have hk' : (r.factorial : K) • (D r).baseChange K = (f.baseChange K) ^ r := by
       simpa only [Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul,
         natCast_zsmul] using hk
     exact hk'
    intro a ha r hr
    constructor
    · have he := congrArg (fun z : Module.End K (VK K M) => (r.factorial : K)⁻¹ • z)
        (hfac a.x x a.X ha.1 ha.2.2.2.1 r)
      simpa only [smul_smul, inv_mul_cancel₀ (hn.1 r hr), one_smul] using he
    · have he := congrArg (fun z : Module.End K (VK K M) => (r.factorial : K)⁻¹ • z)
        (hfac a.y y a.Y ha.2.1 ha.2.2.2.2 r)
      simpa only [smul_smul, inv_mul_cancel₀ (hn.1 r hr), one_smul] using he
  have hcanonical : ∀ a : LatticeOps M, Agrees M x y h a →
   ∃ beta : Module.Basis (Index lam) K (VK K M),
   GeneratorFormulas lam (fun i => beta i) (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) ∧
   ∀ i j k : Index lam,
   (a.X (lam.toNat - i.val) * (a.Y lam.toNat * a.X lam.toNat) *
     a.Y (lam.toNat - j.val)).baseChange K (beta k) =
   (Nat.choose lam.toNat j.val : K) • (if j = k then beta i else 0) := by
    classical
    have hlift : ∀ (f : Module.End ℤ M) (F : Module.End ℂ V),
     (∀ m : M, (f m : V) = F (m : V)) →
     ∀ u : MR p M, iota p M (f.baseChange (R p) u) = F (iota p M u) := by
     intro f F hf u
     induction u using TensorProduct.induction_on with
     | zero => simp
     | tmul r m =>
       change r • (f m : V) = F (r • (m : V))
       rw [hf]
       exact ((F.restrictScalars (R p)).map_smul r (m : V)).symm
     | add u w hu hw => simp only [map_add, hu, hw]
    intro a ha
    obtain ⟨beta, b, hb, ⟨kap, phi, c, hphi, hc, hbeta⟩, hdim, hgen⟩ := h_T015 a ha
    letI : Algebra (R p) K := kap.toAlgebra
    have hcomm : ∀ (f : Module.End ℤ M) (z : VK K M),
     phi (f.baseChange K z) = (f.baseChange (R p)).baseChange K (phi z) := by
     intro f z
     induction z using TensorProduct.induction_on with
     | zero => simp
     | tmul s m => simp only [LinearMap.baseChange_tmul, hphi]
     | add z w hz hw => simp only [map_add, hz, hw]
    obtain ⟨bC, hbC⟩ := h_T004.2.2.2.2.2.1.1
    refine ⟨beta, hgen, ?_⟩
    intro i j k
    let W : Module.End ℤ M := a.X (lam.toNat - i.val) *
     (a.Y lam.toNat * a.X lam.toNat) * a.Y (lam.toNat - j.val)
    let WC : Module.End ℂ V := divided x (lam.toNat - i.val) *
     (divided y lam.toNat * divided x lam.toNat) * divided y (lam.toNat - j.val)
    have hW : ∀ m : M, (W m : V) = WC (m : V) := by
     intro m
     simp only [W, WC, Module.End.mul_apply, ha.2.2.2.1, ha.2.2.2.2]
    have hWC : WC = (Nat.choose lam.toNat j.val : ℂ) • E lam bC i j := by
     have he := (h_T007.2 bC hbC i j).2.2.2.2.1
     have hn : (Nat.choose lam.toNat j.val : ℂ) ≠ 0 :=
       Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)))
     change E lam bC i j = (Nat.choose lam.toNat j.val : ℂ)⁻¹ • WC at he
     rw [he, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have haction : W.baseChange (R p) (c k) =
     (Nat.choose lam.toNat j.val : R p) • (if j = k then c i else 0) := by
     apply h_T007.1.1
     rw [hlift W WC hW, hc]
     rw [WC.map_smul, hWC]
     have he : E lam bC i j (e y v k.val) = if j = k then e y v i.val else 0 := by
       rw [← hbC k]
       simp only [E, LinearMap.smulRight_apply, Module.Basis.coord_apply,
         Module.Basis.repr_self, Finsupp.single_apply]
       by_cases hj : j = k
       · subst k; simp [hbC]
       · simp [hj, Ne.symm hj]
     simp only [LinearMap.smul_apply, he]
     split_ifs with hj
     · subst k
       rw [map_smul, hc]
       change b • ((Nat.choose lam.toNat j.val : ℂ) • e y v i.val) =
         (Nat.choose lam.toNat j.val : R p) • (b • e y v i.val)
       rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_comm]
       rfl
     · simp
    apply phi.injective
    rw [hcomm W, hbeta]
    simp only [LinearMap.baseChange_tmul, haction]
    rw [map_smul]
    split_ifs with hj
    · subst k
      rw [hbeta]
      simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
      simp only [Nat.cast_smul_eq_nsmul]
    · simp
  have htransport : ∀ (b0 b1 : Module.Basis (Index lam) K (VK K M))
   (X Y H : Module.End K (VK K M)),
   GeneratorFormulas lam (fun i => b0 i) X Y H →
   GeneratorFormulas lam (fun i => b1 i) X Y H →
   ∃ T : VK K M ≃ₗ[K] VK K M,
   (∀ i, T (b0 i) = b1 i) ∧
   (∀ u, T (X u) = X (T u)) ∧ (∀ u, T (Y u) = Y (T u)) := by
    classical
    intro b0 b1 X Y H h0 h1
    let T := b0.equiv b1 (Equiv.refl (Index lam))
    have hT : ∀ i, T (b0 i) = b1 i := by intro i; simp [T]
    have hext : ∀ n, T (extendFamily (F := K) lam (fun i => b0 i) n) =
     extendFamily (F := K) lam (fun i => b1 i) n := by
     intro n
     unfold extendFamily
     split_ifs <;> simp [hT]
    have hx : T.toLinearMap.comp X = X.comp T.toLinearMap := by
     apply b0.ext
     intro i
     change T (X (b0 i)) = X (T (b0 i))
     rw [(h0 i).1, hT, (h1 i).1]
     split_ifs <;> simp [hext]
    have hy : T.toLinearMap.comp Y = Y.comp T.toLinearMap := by
     apply b0.ext
     intro i
     change T (Y (b0 i)) = Y (T (b0 i))
     rw [(h0 i).2.1, hT, (h1 i).2.1, map_smul, hext]
    exact ⟨T, hT, (fun u => LinearMap.congr_fun hx u),
     (fun u => LinearMap.congr_fun hy u)⟩
  refine ⟨h_T014, h_T015, ?_, ?_⟩
  · refine ⟨hn.1, hn.2, ?_⟩
    intro a ha
    refine ⟨hdiv a ha, ?_⟩
    intro beta hgen
    obtain ⟨b0, hgen0, hact⟩ := hcanonical a ha
    have hdelta : ∀ i j k : Index lam,
        MatrixWord lam (fun r => (a.X r).baseChange K)
          (fun r => (a.Y r).baseChange K) i j (b0 k) =
        if j = k then b0 i else 0 := by
      intro i j k
      have he := hact i j k
      simp only [LinearMap.baseChange_mul] at he
      unfold MatrixWord
      rw [LinearMap.smul_apply, he, smul_smul, inv_mul_cancel₀ (hn.2 j), one_smul]
    obtain ⟨T, hT, hx, hy⟩ :=
      htransport b0 beta (a.x.baseChange K) (a.y.baseChange K) (a.h.baseChange K) hgen0 hgen
    have hpow : ∀ F : Module.End K (VK K M),
        (∀ u, T (F u) = F (T u)) →
        ∀ n u, T ((F ^ n) u) = (F ^ n) (T u) := by
      intro F hF n
      induction n with
      | zero => intro u; rfl
      | succ n ih =>
        intro u
        simp only [pow_succ', Module.End.mul_apply, hF, ih]
    have hX : ∀ r, r ≤ lam.toNat → ∀ u,
        T ((a.X r).baseChange K u) = (a.X r).baseChange K (T u) := by
      intro r hr u
      rw [(hdiv a ha r hr).1]
      simp only [LinearMap.smul_apply, map_smul, hpow _ hx]
    have hY : ∀ r, r ≤ lam.toNat → ∀ u,
        T ((a.Y r).baseChange K u) = (a.Y r).baseChange K (T u) := by
      intro r hr u
      rw [(hdiv a ha r hr).2]
      simp only [LinearMap.smul_apply, map_smul, hpow _ hy]
    intro i j k
    have hW : ∀ u,
        T (MatrixWord lam (fun r => (a.X r).baseChange K)
          (fun r => (a.Y r).baseChange K) i j u) =
        MatrixWord lam (fun r => (a.X r).baseChange K)
          (fun r => (a.Y r).baseChange K) i j (T u) := by
      intro u
      simp only [MatrixWord, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
        hX _ (Nat.sub_le _ _), hY _ (Nat.sub_le _ _), hX _ le_rfl, hY _ le_rfl]
    have he := congrArg T (hdelta i j k)
    rw [hW, hT] at he
    simpa only [apply_ite T, hT, map_zero] using he
  · rcases h_T007.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, ha⟩
    exact ha

#check @T016
#print axioms T016

end Translation
