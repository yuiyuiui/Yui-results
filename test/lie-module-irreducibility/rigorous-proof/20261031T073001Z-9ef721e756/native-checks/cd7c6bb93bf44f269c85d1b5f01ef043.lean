import Mathlib
noncomputable section
open scoped TensorProduct
namespace LatticeSL2
def scalarRing (p : ℕ) : Subring ℚ :=
  Subring.closure {q | ∃ b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (b : ℚ)⁻¹}
abbrev R (p : ℕ) := ↥(scalarRing p)
instance (p : ℕ) : Algebra (R p) ℂ :=
  ((algebraMap ℚ ℂ).comp (scalarRing p).subtype).toAlgebra
instance (p : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V] : Module (R p) V :=
  Module.compHom V (algebraMap (R p) ℂ)
def divided {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • a ^ r
def ev {V : Type*} [AddCommGroup V] [Module ℂ V]
    (y : Module.End ℂ V) (v : V) (i : ℕ) : V := divided y i v
abbrev Ix (l : ℤ) := Fin (l.toNat + 1)
def Stable {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (W : Submodule F U) (a : Module.End F U) : Prop :=
  ∀ u ∈ W, a u ∈ W
def SimpleTriple {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (x y h : Module.End F U) : Prop :=
  Nontrivial U ∧ ∀ W : Submodule F U,
    Stable W x → Stable W y → Stable W h → W = ⊥ ∨ W = ⊤
def Preserves {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : Submodule ℤ V) (a : Module.End ℂ V) : Prop :=
  ∀ m : M, a (m : V) ∈ M
abbrev MR {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) (M : Submodule ℤ V) := R p ⊗[ℤ] M
abbrev VK {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : Type*) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
def LiftOf {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : Submodule ℤ V) (a : Module.End ℂ V) (f : Module.End ℤ M) : Prop :=
  ∀ m : M, (f m : V) = a (m : V)
instance (p : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V] :
    IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
def L {V : Type*} [AddCommGroup V] [Module ℂ V] (p : ℕ)
    (M : Submodule ℤ V) : Submodule (R p) V :=
  Submodule.span (R p) (M : Set V)
def J {V : Type*} [AddCommGroup V] [Module ℂ V] (p : ℕ)
    (M : Submodule ℤ V) (e : V) : Submodule (R p) ℂ :=
  (L p M).comap ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight e |>.restrictScalars (R p))
def pPart {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) (MR p M) :=
  Submodule.span (R p) (Set.range (fun u : MR p M => (p : ℤ) • u))
abbrev Red {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) (M : Submodule ℤ V) := ZMod p ⊗[ℤ] MR p M
abbrev RK {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : ℕ} {K : Type*} [Field K] (κ : R p →+* K) (M : Submodule ℤ V) :=
  letI := κ.toAlgebra
  K ⊗[R p] MR p M
abbrev FK {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) (K : Type*) [Field K] [CharP K p] (M : Submodule ℤ V) :=
  letI := ZMod.algebra K p
  K ⊗[ZMod p] Red p M
def throughR {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : ℕ} {K : Type*} [Field K] (κ : R p →+* K)
    {M : Submodule ℤ V} (f : Module.End ℤ M) : Module.End K (RK κ M) :=
  letI := κ.toAlgebra
  (f.baseChange (R p)).baseChange K
def throughF {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) (K : Type*) [Field K] [CharP K p]
    {M : Submodule ℤ V} (f : Module.End ℤ M) : Module.End K (FK p K M) :=
  letI := ZMod.algebra K p
  (((f.baseChange (R p)).restrictScalars ℤ).baseChange (ZMod p)).baseChange K
def matrixUnit {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    {l : ℤ} (B : Module.Basis (Ix l) F U) (i j : Ix l) : Module.End F U :=
  (B.coord j).smulRight (B i)
def genFormulas {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
    (l : ℤ) (x y h : Module.End F U) (b : Ix l → U) : Prop :=
  (∀ i : Ix l, x (b i) = if hi : 0 < i.val then
      ((l - (i.val : ℤ) + 1 : ℤ) : F) • b ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
      else 0) ∧
  (∀ i : Ix l, y (b i) = if hi : i.val + 1 < l.toNat + 1 then
      ((i.val + 1 : ℕ) : F) • b ⟨i.val + 1, hi⟩ else 0) ∧
  (∀ i : Ix l, h (b i) = ((l - 2 * (i.val : ℤ) : ℤ) : F) • b i)
def iotaSpec {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) (M : Submodule ℤ V) (f : MR p M →ₗ[R p] V) : Prop :=
  ∀ (r : R p) (m : M), f (r ⊗ₜ[ℤ] m) = (algebraMap (R p) ℂ r) • (m : V)
def canonicalR {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : ℕ} {K : Type*} [Field K] (κ : R p →+* K)
    (M : Submodule ℤ V) (C : RK κ M ≃ₗ[K] VK K M) : Prop :=
  letI := κ.toAlgebra
  ∀ (c : K) (r : R p) (m : M),
    C (c ⊗ₜ[R p] (r ⊗ₜ[ℤ] m)) = (κ r * c) ⊗ₜ[ℤ] m
def pureR {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : ℕ} {K : Type*} [Field K] (κ : R p →+* K)
    {M : Submodule ℤ V} (c : K) (u : MR p M) : RK κ M :=
  letI := κ.toAlgebra
  c ⊗ₜ[R p] u
def canonicalF {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : ℕ} {K : Type*} [Field K] [CharP K p]
    (κ : R p →+* K) (M : Submodule ℤ V)
    (D : FK p K M ≃ₗ[K] VK K M) : Prop :=
  letI := ZMod.algebra K p
  ∀ (c : K) (a : ZMod p) (r : R p) (m : M),
    D (c ⊗ₜ[ZMod p] (a ⊗ₜ[ℤ] (r ⊗ₜ[ℤ] m))) =
      ((ZMod.cast a : K) * κ r * c) ⊗ₜ[ℤ] m
def basisOrigin {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : ℕ} {K : Type*} [Field K] {l : ℤ}
    (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V)
    (β : Module.Basis (Ix l) K (VK K M)) : Prop :=
  ∃ b : ℂ, b ∈ J p M (ev y v 0) ∧ b ≠ 0 ∧
  ∃ ι : MR p M →ₗ[R p] V, iotaSpec p M ι ∧ Function.Injective ι ∧
  ∃ B : Module.Basis (Ix l) (R p) (MR p M),
    (∀ i, ι (B i) = b • ev y v i.val) ∧
  ∃ κ : R p →+* K, ∃ C : RK κ M ≃ₗ[K] VK K M,
    canonicalR κ M C ∧ ∀ i, β i = C (pureR κ 1 (B i))
end LatticeSL2
open LatticeSL2

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_T008 : (∀ q : ℚ, q ∈ scalarRing p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ (((∃ ι : MR p M →ₗ[R p] V, iotaSpec p M ι ∧ Function.Injective ι ∧ LinearMap.range ι = L p M) ∧
Nonempty (Module.Basis (Ix l) (R p) (MR p M)) ∧
Submodule.span ℂ (M : Set V) = ⊤ ∧
(∀ r : ℕ, Preserves M (divided x r) ∧ Preserves M (divided y r)) ∧
Preserves M x ∧ Preserves M y ∧ Preserves M h ∧
(∀ r : ℕ, (∀ u ∈ L p M, divided x r u ∈ L p M) ∧ (∀ u ∈ L p M, divided y r u ∈ L p M)) ∧
(∀ u ∈ L p M, x u ∈ L p M ∧ y u ∈ L p M ∧ h u ∈ L p M) ∧
(∃ fx fy fh : Module.End ℤ M, LiftOf M x fx ∧ LiftOf M y fy ∧ LiftOf M h fh) ∧
(∃ DX DY : ℕ → Module.End ℤ M, ∀ r, LiftOf M (divided x r) (DX r) ∧ LiftOf M (divided y r) (DY r))) ∧ (∀ (B : Module.Basis (Ix l) ℂ V), (∀ i, B i = ev y v i.val) →
  (divided y l.toNat * divided x l.toNat = matrixUnit B (Fin.last l.toNat) (Fin.last l.toNat)) ∧
  (∀ i : Ix l, divided x (l.toNat - i.val) * (divided y l.toNat * divided x l.toNat) = matrixUnit B i (Fin.last l.toNat)) ∧
  (∀ j : Ix l, (divided y l.toNat * divided x l.toNat) * divided y (l.toNat - j.val) =
    ((Nat.choose l.toNat j.val : ℕ) : ℂ) • matrixUnit B (Fin.last l.toNat) j) ∧
  (∀ j : Ix l, IsUnit ((Nat.choose l.toNat j.val : ℕ) : R p))) ∧ (∀ (B : Module.Basis (Ix l) ℂ V), (∀ i, B i = ev y v i.val) →
  ∀ i j : Ix l,
  matrixUnit B i j = (((Nat.choose l.toNat j.val : ℕ) : ℂ)⁻¹) •
    (divided x (l.toNat - i.val) * (divided y l.toNat * divided x l.toNat) * divided y (l.toNat - j.val)) ∧
  ∀ u ∈ L p M, matrixUnit B i j u ∈ L p M))) : yui_aux_type% "∀ [hc : CharP K p], ∃ κ : R p →+* K, (∀ (a b : ℤ) (r : R p), (r : ℚ) = (a : ℚ) / (b : ℚ) → ¬ (p : ℤ) ∣ b → κ r = (a : K) * (b : K)⁻¹) ∧ ∃ S : Submonoid ℤ, IsLocalization S (R p)" := by
  intro hc
  classical
  let S : Submonoid ℤ := (IsUnit.submonoid K).comap (Int.castRingHom K)
  have hS (b : ℤ) : b ∈ S ↔ ¬ (p : ℤ) ∣ b := by
    change IsUnit (b : K) ↔ _
    rw [isUnit_iff_ne_zero, ne_eq, CharP.intCast_eq_zero_iff K p]
  have hb0 (b : ℤ) (hb : b ∈ S) : (b : ℚ) ≠ 0 := by
    exact_mod_cast (fun hz : b = 0 => (hS b).mp hb (hz ▸ dvd_zero _))
  letI : IsLocalization S (R p) := by
    refine (isLocalization_iff S (R p)).mpr ⟨?_, ?_, ?_⟩
    · intro b
      let t : R p := ⟨(b.val : ℚ)⁻¹, Subring.subset_closure ⟨b.val, (hS b.val).mp b.property, rfl⟩⟩
      apply isUnit_iff_exists_inv.mpr
      refine ⟨t, ?_⟩
      apply Subtype.ext
      change (b.val : ℚ) * (b.val : ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ (hb0 b.val b.property)
    · intro r
      obtain ⟨a, b, hb, hr⟩ := (h_T008.1 (r : ℚ)).mp r.property
      refine ⟨(a, ⟨b, (hS b).mpr hb⟩), ?_⟩
      apply Subtype.ext
      change (r : ℚ) * (b : ℚ) = (a : ℚ)
      rw [hr, div_mul_cancel₀ _ (hb0 b ((hS b).mpr hb))]
    · intro a b hab
      refine ⟨1, ?_⟩
      have he : a = b := by
        have heq := congrArg (fun r : R p => (r : ℚ)) hab
        exact_mod_cast heq
      simp [he]
  have hu : ∀ b : S, IsUnit (Int.castRingHom K b) := fun b => b.property
  let κ : R p →+* K := IsLocalization.lift hu
  refine ⟨κ, ?_, S, inferInstance⟩
  intro a b r hr hb
  have hbr : r * (b : R p) = (a : R p) := by
    apply Subtype.ext
    change (r : ℚ) * (b : ℚ) = (a : ℚ)
    rw [hr, div_mul_cancel₀ _ (hb0 b ((hS b).mpr hb))]
  have hk : κ r * (b : K) = (a : K) := by
    simpa using congrArg κ hbr
  exact (eq_mul_inv_iff₀ (by simpa [CharP.intCast_eq_zero_iff K p] using hb)).mpr hk
#check @checked
#print axioms checked
end YuiAuxiliary
