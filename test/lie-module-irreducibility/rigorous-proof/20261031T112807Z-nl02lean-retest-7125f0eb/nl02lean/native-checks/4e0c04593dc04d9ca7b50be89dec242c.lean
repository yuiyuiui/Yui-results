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

theorem T007 {V : Type} [instVAdd : AddCommGroup V] [instVMod : Module ℂ V] (p : ℕ) (lam : ℤ) (K : Type) [instK : Field K] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : Coordinates lam x y h v) (h_T005 : (∀ q : ℚ, q ∈ localRing p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ IsFractionRing (R p) ℚ) (h_T006 : LocalLattice p lam M x y h) :
    LocalLattice p lam M x y h ∧ MatrixIdentities p lam M x y v := by
  classical
  have hEdges : ∀ (b : Module.Basis (Index lam) ℂ V), (∀ i, b i = e y v i.val) → ∀ i j : Index lam, (divided y lam.toNat * divided x lam.toNat = E lam b (Fin.last lam.toNat) (Fin.last lam.toNat)) ∧ (divided x (lam.toNat - i.val) * (divided y lam.toNat * divided x lam.toNat) = E lam b i (Fin.last lam.toNat)) ∧ ((divided y lam.toNat * divided x lam.toNat) * divided y (lam.toNat - j.val) = (Nat.choose lam.toNat j.val : ℂ) • E lam b (Fin.last lam.toNat) j) := by
    classical
    intro b hb
    have hf : (fun i : Index lam => e y v i.val) = (fun i => b i) := funext (fun i => (hb i).symm)
    have hd := h_T004.2.2.2.2.2.2
    rw [hf] at hd
    have hext (k : Index lam) : extendFamily (F := ℂ) lam (fun i => b i) k.val = b k := by
      simp [extendFamily, k.isLt]
    have hx (k : Index lam) :
        divided x lam.toNat (b k) = if k = Fin.last lam.toNat then b ⟨0, by omega⟩ else 0 := by
      rw [(hd k lam.toNat).1]
      by_cases hk : k = Fin.last lam.toNat
      · subst k
        simp [extendFamily]
      · have hk' : k.val < lam.toNat := by
          have := k.isLt
          have : k.val ≠ lam.toNat := fun hh => hk (Fin.ext hh)
          omega
        simp [Nat.not_le.mpr hk', hk]
    have hy : divided y lam.toNat (b ⟨0, by omega⟩) = b (Fin.last lam.toNat) := by
      rw [(hd ⟨0, by omega⟩ lam.toNat).2]
      simp [extendFamily, Fin.last]
    have hp : divided y lam.toNat * divided x lam.toNat =
        E lam b (Fin.last lam.toNat) (Fin.last lam.toNat) := by
      apply b.ext
      intro k
      simp only [Module.End.mul_apply, hx]
      split_ifs with hk
      · subst k
        simpa [E] using hy
      · simp [E, hk, Ne.symm hk]
    have hxi (i : Index lam) :
        divided x (lam.toNat - i.val) (b (Fin.last lam.toNat)) = b i := by
      rw [(hd (Fin.last lam.toNat) (lam.toNat - i.val)).1]
      have hi : i.val ≤ lam.toNat := by have := i.isLt; omega
      have hn : lam.toNat - (lam.toNat - i.val) = i.val := by omega
      simp [hi, hn, extendFamily, i.isLt]
    intro i j
    refine ⟨hp, ?_, ?_⟩
    · rw [hp]
      apply b.ext
      intro k
      by_cases hk : k = Fin.last lam.toNat
      · subst k
        simpa [E] using hxi i
      · simp [Module.End.mul_apply, E, hk, Ne.symm hk]
    · apply b.ext
      intro k
      rw [Module.End.mul_apply, (hd k (lam.toNat - j.val)).2, map_smul, hp]
      by_cases hkj : k = j
      · subst k
        have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
        have hn : j.val + (lam.toNat - j.val) = lam.toNat := by omega
        simp [hn, extendFamily, E, Fin.last, Nat.choose_symm hj]
      · by_cases hlt : k.val + (lam.toNat - j.val) < lam.toNat + 1
        · let a : Index lam := ⟨k.val + (lam.toNat - j.val), hlt⟩
          have ha : a ≠ Fin.last lam.toNat := by
            intro ha
            have hv := congrArg Fin.val ha
            have hj := j.isLt
            have hk := k.isLt
            apply hkj
            apply Fin.ext
            dsimp [a] at hv
            omega
          simp [extendFamily, hlt, E, hkj, Ne.symm hkj, show (⟨k.val + (lam.toNat - j.val), hlt⟩ : Index lam) ≠ Fin.last lam.toNat from ha, Ne.symm ha]
        · simp [extendFamily, hlt, E, hkj, Ne.symm hkj]
  have hUnits : ∀ j : Index lam, ∃ (c d : R p), (c : ℚ) = (Nat.choose lam.toNat j.val : ℚ) ∧ IsUnit c ∧ (algebraMap (R p) ℂ d) = (Nat.choose lam.toNat j.val : ℂ)⁻¹ := by
    intro j
    have hn : lam.toNat < p := by
      have hl : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg h_H002.1
      omega
    have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
    have hnd : ¬ p ∣ Nat.choose lam.toNat j.val := by
      intro hh
      have hd : p ∣ lam.toNat.factorial := by
        rw [← Nat.choose_mul_factorial_mul_factorial hj]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hh _) _
      exact (not_le_of_gt hn) ((h_H001.1.dvd_factorial).mp hd)
    have hci : ¬ (p : ℤ) ∣ (Nat.choose lam.toNat j.val : ℤ) := by
      exact_mod_cast hnd
    have hc0 : Nat.choose lam.toNat j.val ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hj)
    have hq0 : (Nat.choose lam.toNat j.val : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hmem : (Nat.choose lam.toNat j.val : ℚ)⁻¹ ∈ localRing p := by
      apply (h_T005.1 _).2
      refine ⟨1, (Nat.choose lam.toNat j.val : ℤ), ?_, hci, ?_⟩
      · exact_mod_cast hc0
      · simp
    let c : R p := (Nat.choose lam.toNat j.val : R p)
    let d : R p := ⟨(Nat.choose lam.toNat j.val : ℚ)⁻¹, hmem⟩
    have hcd : c * d = 1 := by
      apply Subtype.ext
      change (Nat.choose lam.toNat j.val : ℚ) * (Nat.choose lam.toNat j.val : ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ hq0
    refine ⟨c, d, ?_, isUnit_iff_exists_inv.mpr ⟨d, hcd⟩, ?_⟩
    · simp [c]
    · change algebraMap ℚ ℂ ((Nat.choose lam.toNat j.val : ℚ)⁻¹) = _
      simp
  refine ⟨h_T006, ?_⟩
  intro b hb i j
  obtain ⟨hp, hl, hr⟩ := hEdges b hb i j
  obtain ⟨c, d, hc, hcu, hd⟩ := hUnits j
  have hcoef : (Nat.choose lam.toNat j.val : ℂ) ≠ 0 := by
    have hj : j.val ≤ lam.toNat := by have := j.isLt; omega
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hj))
  have hxe : divided x (lam.toNat - i.val) * E lam b (Fin.last lam.toNat) j = E lam b i j := by
    apply b.ext
    intro k
    by_cases hk : k = j
    · subst k
      have hv := congrArg (fun f : Module.End ℂ V => f (b (Fin.last lam.toNat))) hl
      simpa [Module.End.mul_apply, hp, E] using hv
    · simp [Module.End.mul_apply, E, hk, Ne.symm hk]
  have hraw :
      divided x (lam.toNat - i.val) * (divided y lam.toNat * divided x lam.toNat) *
          divided y (lam.toNat - j.val) =
        (Nat.choose lam.toNat j.val : ℂ) • E lam b i j := by
    rw [mul_assoc, hr, mul_smul_comm, hxe]
  have hw : E lam b i j = MatrixWord lam (divided x) (divided y) i j := by
    unfold MatrixWord
    rw [hraw, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
  refine ⟨hp, hl, hr, ⟨c, hc, hcu⟩, hw, ?_⟩
  intro u hu
  rw [hw]
  have hpres := h_T006.2.2.2.2.1
  have hu1 := (hpres (lam.toNat - j.val)).2.2.2 u hu
  have hu2 := (hpres lam.toNat).2.2.1 _ hu1
  have hu3 := (hpres lam.toNat).2.2.2 _ hu2
  have hu4 := (hpres (lam.toNat - i.val)).2.2.1 _ hu3
  have hsmul : d • (divided x (lam.toNat - i.val) (divided y lam.toNat (divided x lam.toNat (divided y (lam.toNat - j.val) u)))) =
      (Nat.choose lam.toNat j.val : ℂ)⁻¹ • (divided x (lam.toNat - i.val) (divided y lam.toNat (divided x lam.toNat (divided y (lam.toNat - j.val) u)))) := by
    change (algebraMap (R p) ℂ d) • _ = _
    rw [hd]
  simpa only [MatrixWord, LinearMap.smul_apply, Module.End.mul_apply, ← hsmul] using
    (localizedImage p M).smul_mem d hu4

#check @T007
#print axioms T007

end Translation
