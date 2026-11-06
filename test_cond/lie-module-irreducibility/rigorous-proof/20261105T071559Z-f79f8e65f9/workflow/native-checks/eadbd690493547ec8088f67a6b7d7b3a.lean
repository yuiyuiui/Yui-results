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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T011
theorem yui_aux_0001 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ q : ℚ, q ≠ 0 → ∃ (n : ℤ) (u : ℚ), u ∈ Chevalley.R p ∧ u⁻¹ ∈ Chevalley.R p ∧ u ≠ 0 ∧ q = (p : ℚ) ^ n * u" := by
  intro q hq
  letI : Fact p.Prime := ⟨h_H001.1⟩
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  obtain ⟨a, ha, hpa⟩ := (padicValRat.finite_int_prime_iff (p := p)).mpr hn |>.exists_eq_pow_mul_and_not_dvd
  obtain ⟨b, hb, hpb⟩ := (padicValRat.finite_int_prime_iff (p := p)).mpr hd |>.exists_eq_pow_mul_and_not_dvd
  have ha0 : a ≠ 0 := by intro h; simp [h] at hpa
  have hb0 : b ≠ 0 := by intro h; simp [h] at hpb
  have hRint (z : ℤ) : (z : ℚ) ∈ Chevalley.R p := (Chevalley.R p).algebraMap_mem z
  have hRinv (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : (z : ℚ)⁻¹ ∈ Chevalley.R p :=
    Algebra.subset_adjoin ⟨z, hz, rfl⟩
  refine ⟨(multiplicity (p : ℤ) q.num : ℤ) - (multiplicity (p : ℤ) (q.den : ℤ) : ℤ),
    (a : ℚ) / b, ?_, ?_, div_ne_zero (by exact_mod_cast ha0) (by exact_mod_cast hb0), ?_⟩
  · exact (Chevalley.R p).mul_mem (hRint a) (hRinv b hpb)
  · simpa [div_eq_mul_inv, mul_comm] using (Chevalley.R p).mul_mem (hRint b) (hRinv a hpa)
  · have haq : (q.num : ℚ) = (p : ℚ) ^ multiplicity (p : ℤ) q.num * (a : ℚ) := by exact_mod_cast ha
    have hbq : (q.den : ℚ) = (p : ℚ) ^ multiplicity (p : ℤ) (q.den : ℤ) * (b : ℚ) := by exact_mod_cast hb
    rw [zpow_sub₀ (by exact_mod_cast h_H001.1.ne_zero), zpow_natCast, zpow_natCast]
    calc
      q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
      _ = _ := by rw [haq, hbq]; ring

theorem yui_aux_0002 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∃ (a : ℂ) (s : Finset ℂ), a ≠ 0 ∧ a ∈ Chevalley.J p M y v 0 ∧ s.Nonempty ∧ Submodule.span (Chevalley.R p) (s : Set ℂ) = Chevalley.J p M y v 0 ∧ ∀ z ∈ s, z ≠ 0 ∧ ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) * a = z" := by
  classical
  let J := Chevalley.J p M y v 0
  let L := Chevalley.QJ p M y v
  have hJ : J ≠ ⊥ := h_T010.1.2.2.1
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have haL : a ∈ L := Submodule.subset_span ha
  have haL0 : (⟨a, haL⟩ : L) ≠ 0 := by
    intro hh
    exact ha0 (congrArg Subtype.val hh)
  have hdim : Module.finrank ℚ L = 1 := h_T010.2.2.2.2.2
  have hline : ∀ z ∈ J, ∃ q : ℚ, (q : ℂ) * a = z := by
    intro z hz
    have hzL : z ∈ L := Submodule.subset_span hz
    obtain ⟨q, hq⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℚ) (⟨a, haL⟩ : L) haL0).mp hdim ⟨z, hzL⟩
    exact ⟨q, by simpa [Algebra.smul_def] using congrArg Subtype.val hq⟩
  obtain ⟨t, ht⟩ := h_T010.1.2.1
  let s := t.erase 0
  have hs : Submodule.span (Chevalley.R p) (s : Set ℂ) = J := by
    change Submodule.span (Chevalley.R p) ((t.erase 0 : Finset ℂ) : Set ℂ) = J
    rw [Finset.coe_erase, Submodule.span_sdiff_singleton_zero]
    exact ht
  have hsne : s.Nonempty := by
    by_contra he
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hempty] at hs
    exact hJ (by simpa using hs.symm)
  refine ⟨a, s, ha0, ha, hsne, hs, ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
  have hzJ : z ∈ J := hs ▸ Submodule.subset_span hz
  obtain ⟨q, hq⟩ := hline z hzJ
  refine ⟨hz0, q, ?_, hq⟩
  intro hq0
  apply hz0
  simpa [hq0] using hq.symm

theorem yui_aux_0003 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (r : Chevalley.R p) (b : ℂ), r • b = ((r : ℚ) : ℂ) * b" := by
  intro r b
  rfl

theorem yui_aux_0004 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (k : ℤ), 0 ≤ k → (p : ℚ) ^ k ∈ Chevalley.R p" := by
  intro k hk
  lift k to ℕ using hk
  simpa using (Chevalley.R p).pow_mem ((Chevalley.R p).algebraMap_mem (p : ℤ)) k

theorem yui_aux_0005 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (r t : ℚ) (a : ℂ), (r : ℂ) * ((t : ℂ) * a) = ((r * t : ℚ) : ℂ) * a" := by
  intro r t a
  simp only [Rat.cast_mul, mul_assoc]

theorem yui_aux_0006 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) : yui_aux_type% "∀ (a : ℂ) (s : Finset ℂ), a ≠ 0 → s.Nonempty → (∀ z ∈ s, ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) * a = z) → ∃ b : ℂ, b ≠ 0 ∧ (∀ z ∈ s, ∃ r : Chevalley.R p, r • b = z) ∧ ∃ z ∈ s, ∃ u : ℚ, u ∈ Chevalley.R p ∧ u⁻¹ ∈ Chevalley.R p ∧ u ≠ 0 ∧ z = (u : ℂ) * b" := by
  classical
  intro a s ha hs hrep
  have hf := @yui_aux_0001 V instV instCV K instK p ell x y h v M h_H001 h_T010
  have hsmul := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T010
  have hpow := @yui_aux_0004 V instV instCV K instK p ell x y h v M h_H001 h_T010
  choose q hq0 hqa using (fun z : s => hrep z z.property)
  choose n u hu hui hu0 hqu using (fun z : s => hf (q z) (hq0 z))
  haveI : Nonempty s := by
    obtain ⟨z, hz⟩ := hs
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image n Finset.univ_nonempty
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
  let b : ℂ := (((p : ℚ) ^ n j : ℚ) : ℂ) * a
  have hb0 : b ≠ 0 := mul_ne_zero (by exact_mod_cast zpow_ne_zero (n j) hp0) ha
  refine ⟨b, hb0, ?_, ?_⟩
  · intro z hz
    let i : s := ⟨z, hz⟩
    have hni : 0 ≤ n i - n j := sub_nonneg.mpr (hj i (Finset.mem_univ i))
    let r : Chevalley.R p := ⟨(p : ℚ) ^ (n i - n j) * u i,
      (Chevalley.R p).mul_mem (hpow _ hni) (hu i)⟩
    refine ⟨r, ?_⟩
    rw [hsmul]
    change (((p : ℚ) ^ (n i - n j) * u i : ℚ) : ℂ) *
      ((((p : ℚ) ^ n j : ℚ) : ℂ) * a) = z
    have heq : ((p : ℚ) ^ (n i - n j) * u i) * (p : ℚ) ^ n j = q i := by
      rw [hqu i, zpow_sub₀ hp0]
      field_simp
    calc
      _ = ((((p : ℚ) ^ (n i - n j) * u i) * (p : ℚ) ^ n j : ℚ) : ℂ) * a := by
        exact @yui_aux_0005 V instV instCV K instK p ell x y h v M h_H001 h_T010 _ _ a
      _ = (q i : ℂ) * a := by rw [heq]
      _ = z := hqa i
  · refine ⟨j, j.property, u j, hu j, hui j, hu0 j, ?_⟩
    calc
      (j : ℂ) = (q j : ℂ) * a := (hqa j).symm
      _ = (u j : ℂ) * b := by
        rw [hqu j, Rat.cast_mul]
        dsimp [b]
        ring

end Local_T011
open Local_T011 in
theorem T011 (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (K : Type) [instK : Field K] (p : ℕ) (ell : ℤ) (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ ell ∧ ell < (p : ℤ)) (h_T010 : ((∀ i : Chevalley.Index ell, Chevalley.J p M y v i.val = Chevalley.J p M y v 0) ∧ (Chevalley.J p M y v 0).FG ∧ Chevalley.J p M y v 0 ≠ ⊥ ∧ (∀ u : V, u ∈ Chevalley.image p M ↔ ∃! c : Chevalley.Index ell → ℂ, (∀ i, c i ∈ Chevalley.J p M y v 0) ∧ u = ∑ i, c i • Chevalley.e y v i.val)) ∧ (Function.Injective (Chevalley.qmul p M y v) ∧ LinearMap.range (Chevalley.qmul p M y v) = Chevalley.QJ p M y v ∧ FiniteDimensional ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ FiniteDimensional ℚ (Chevalley.QJ p M y v)) ∧ (Module.finrank ℚ (ℚ ⊗[Chevalley.R p] Chevalley.MR p M) = ell.toNat + 1 ∧ ell.toNat + 1 = (ell.toNat + 1) * Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) ∧ Module.finrank ℚ (ℚ ⊗[Chevalley.R p] (Chevalley.J p M y v 0)) = 1 ∧ Module.finrank ℚ (Chevalley.QJ p M y v) = 1)) :
    ∃ b : ℂ, b ∈ Chevalley.J p M y v 0 ∧ b ≠ 0 ∧ Chevalley.J p M y v 0 = Submodule.span (Chevalley.R p) ({b} : Set ℂ) := by
  classical
  obtain ⟨a, s, ha0, haJ, hsne, hs, hrep⟩ :=
    @yui_aux_0002 V instV instCV K instK p ell x y h v M h_H001 h_T010
  obtain ⟨b, hb0, hgens, z, hz, u, hu, hui, hu0, hzu⟩ :=
    @yui_aux_0006 V instV instCV K instK p ell x y h v M h_H001 h_T010
      a s ha0 hsne (fun t ht => (hrep t ht).2)
  have hsmul := @yui_aux_0003 V instV instCV K instK p ell x y h v M h_H001 h_T010
  have hzJ : z ∈ Chevalley.J p M y v 0 := hs ▸ Submodule.subset_span hz
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu0
  have hrecover : (⟨u⁻¹, hui⟩ : Chevalley.R p) • z = b := by
    rw [hsmul]
    change ((u⁻¹ : ℚ) : ℂ) * z = b
    rw [hzu, Rat.cast_inv, inv_mul_cancel_left₀ huC]
  have hbJ : b ∈ Chevalley.J p M y v 0 := by
    rw [← hrecover]
    exact (Chevalley.J p M y v 0).smul_mem _ hzJ
  refine ⟨b, hbJ, hb0, le_antisymm ?_ ?_⟩
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro t ht
    obtain ⟨r, hr⟩ := hgens t ht
    rw [← hr]
    exact (Submodule.span (Chevalley.R p) ({b} : Set ℂ)).smul_mem r
      (Submodule.subset_span (Set.mem_singleton b))
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hbJ)

#check @T011
#print axioms T011

end Translation
