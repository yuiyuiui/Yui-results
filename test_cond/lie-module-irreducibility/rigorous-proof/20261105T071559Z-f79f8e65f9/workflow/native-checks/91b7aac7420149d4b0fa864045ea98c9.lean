import Mathlib
open scoped TensorProduct
noncomputable section
namespace Chevalley
def R (p : ℕ) : Subalgebra ℤ ℚ :=
  Algebra.adjoin ℤ {q : ℚ | ∃ b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (b : ℚ)⁻¹}
instance rComplex (p : ℕ) : Algebra (R p) ℂ :=
  Algebra.compHom ℂ (algebraMap (R p) ℚ)
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def dp (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r
def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dp y i v
abbrev MR (p : ℕ) (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
def mu (p : ℕ) (M : Submodule ℤ V) : MR p M → V :=
  letI := Module.compHom V (algebraMap (R p) ℂ)
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  M.subtype.liftBaseChange (R p)
def image (p : ℕ) (M : Submodule ℤ V) : Set V := Set.range (mu p M)
def latticeOp (M : Submodule ℤ V) (f : Module.End ℂ V) : Module.End ℤ M :=
  letI := Classical.propDecidable
  if hf : ∀ u ∈ M, f u ∈ M then (f.restrictScalars ℤ).restrict hf else 0
abbrev VK (K : Type) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
def opK (K : Type) [Field K] (M : Submodule ℤ V) (f : Module.End ℂ V) :
    Module.End K (VK K M) := (latticeOp M f).baseChange K
def unitOp {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {ι : Type} (b : Module.Basis ι F W) (i j : ι) : Module.End F W :=
  (b.coord j).smulRight (b i)
def muR (p : ℕ) (M : Submodule ℤ V) :
    letI := Module.compHom V (algebraMap (R p) ℂ)
    MR p M →ₗ[R p] V :=
  letI := Module.compHom V (algebraMap (R p) ℂ)
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  M.subtype.liftBaseChange (R p)
def J (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) :
    Submodule (R p) ℂ :=
  letI := Module.compHom V (algebraMap (R p) ℂ)
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  (muR p M).range.comap (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[R p] ℂ) (e y v i))
def QJ (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) :
    Submodule ℚ ℂ := Submodule.span ℚ (J p M y v 0 : Set ℂ)
def qmul (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) :
    ℚ ⊗[R p] (J p M y v 0) →ₗ[ℚ] ℂ :=
  letI := IsScalarTower.of_compHom (R p) ℚ ℂ
  (J p M y v 0).subtype.liftBaseChange ℚ
abbrev Index (ell : ℤ) := Fin (ell.toNat + 1)
def stable {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (U : Submodule F W) (f : Module.End F W) : Prop := ∀ w ∈ U, f w ∈ U
def inImage (p : ℕ) (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ w ∈ image p M, f w ∈ image p M
def preserves (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ w ∈ M, f w ∈ M
def reductions (K : Type) [Field K] (p : ℕ) (M : Submodule ℤ V) : Prop :=
  ∃ hc : CharP K p,
  letI := hc
  letI := ZMod.algebra K p
  ∃ ρ : R p →+* K,
  (∀ a : ℤ, ρ (a : R p) = (a : K)) ∧
  letI := ρ.toAlgebra
  ∃ Φ : VK K M ≃ₗ[K] (K ⊗[R p] MR p M),
    (∀ (c : K) (m : M), Φ (c ⊗ₜ[ℤ] m) = c ⊗ₜ[R p] ((1 : R p) ⊗ₜ[ℤ] m)) ∧
    ∃ Ψ : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p),
      ∀ (c : K) (u : MR p M), Ψ (c ⊗ₜ[R p] u) = c ⊗ₜ[ZMod p] ModN.mkQ p u
def basisVec {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {n : ℕ} (b : Module.Basis (Fin n) F W) (i : ℕ) : W :=
  if hi : i < n then b ⟨i, hi⟩ else 0
def stringActions {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (ell : ℤ) (x y h : Module.End F W) (a : ℕ → W) : Prop :=
  ∀ i : ℕ, i ≤ ell.toNat →
    x (a i) = (if i = 0 then 0 else ((ell - (i : ℤ) + 1 : ℤ) : F) • a (i - 1)) ∧
    y (a i) = (if i < ell.toNat then ((i + 1 : ℕ) : F) • a (i + 1) else 0) ∧
    h (a i) = ((ell - 2 * (i : ℤ) : ℤ) : F) • a i
def dividedActions {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (ell : ℤ) (X Y : ℕ → Module.End F W) (a : ℕ → W) : Prop :=
  ∀ (r i : ℕ), i ≤ ell.toNat →
    X r (a i) = (if r ≤ i then ((Nat.choose (ell.toNat - i + r) r : ℕ) : F) • a (i - r) else 0) ∧
    Y r (a i) = (if i + r ≤ ell.toNat then ((Nat.choose (i + r) r : ℕ) : F) • a (i + r) else 0)
def matrixK (K : Type) [Field K] (ell : ℤ) (M : Submodule ℤ V)
    (x y : Module.End ℂ V) (i j : Index ell) : Module.End K (VK K M) :=
  ((Nat.choose ell.toNat j.val : K)⁻¹) •
    (opK K M (dp x (ell.toNat - i.val)) *
      (opK K M (dp y ell.toNat) * opK K M (dp x ell.toNat)) *
        opK K M (dp y (ell.toNat - j.val)))
end Chevalley

namespace Translation
set_option autoImplicit false

theorem T015 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T014 : 0 < ell.toNat + 1 ∧ Fintype.card (Chevalley.Index ell) = ell.toNat + 1 ∧ (Chevalley.reductions K p M) ∧ (∃ β : Module.Basis (Chevalley.Index ell) K (Chevalley.VK K M), Chevalley.stringActions ell (Chevalley.opK K M x) (Chevalley.opK K M y) (Chevalley.opK K M h) (Chevalley.basisVec β) ∧ Chevalley.dividedActions ell (fun r => Chevalley.opK K M (Chevalley.dp x r)) (fun r => Chevalley.opK K M (Chevalley.dp y r)) (Chevalley.basisVec β) ∧ (∀ r : ℕ, r ≤ ell.toNat → (r.factorial : K) ≠ 0 ∧ Chevalley.opK K M (Chevalley.dp x r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M x ^ r ∧ Chevalley.opK K M (Chevalley.dp y r) = ((r.factorial : K)⁻¹) • Chevalley.opK K M y ^ r) ∧ (∀ i j : Chevalley.Index ell, (Nat.choose ell.toNat j.val : K) ≠ 0 ∧ Chevalley.matrixK K ell M x y i j = Chevalley.unitOp β i j) ∧ (∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → ∀ i j, Chevalley.stable W (Chevalley.matrixK K ell M x y i j)))) :
    Nontrivial (Chevalley.VK K M) ∧ ∀ W : Submodule K (Chevalley.VK K M), Chevalley.stable W (Chevalley.opK K M x) → Chevalley.stable W (Chevalley.opK K M y) → Chevalley.stable W (Chevalley.opK K M h) → W = ⊥ ∨ W = ⊤ := by
  classical
  rcases h_T014 with ⟨hn, hcard, hred, β, hstr, hdiv, hfac, hmat, hinv⟩
  constructor
  · let i₀ : Chevalley.Index ell := ⟨0, hn⟩
    exact nontrivial_of_ne (β i₀) 0 (β.ne_zero i₀)
  · intro W hx hy hh
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      have hc : ∃ j, β.coord j w ≠ 0 := by
        by_contra hc
        apply hw0
        apply β.forall_coord_eq_zero_iff.mp
        intro j
        by_contra hj
        exact hc ⟨j, hj⟩
      obtain ⟨j, hj⟩ := hc
      apply (Submodule.eq_top_iff_forall_basis_mem β).mpr
      intro i
      have ht : Chevalley.matrixK K ell M x y i j w ∈ W :=
        hinv W hx hy i j w hw
      rw [(hmat i j).2] at ht
      have hs : β.coord j w • β i ∈ W := by
        simpa only [Chevalley.unitOp, LinearMap.smulRight_apply] using ht
      have hi := W.smul_mem (β.coord j w)⁻¹ hs
      simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using hi

#check @T015
#print axioms T015

end Translation
