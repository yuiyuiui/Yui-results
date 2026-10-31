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

namespace Translation
set_option autoImplicit false

theorem T007 (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : (((l.toNat : ℤ) = l) ∧
(∀ i : Ix l, 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ l) ∧
(∀ i : ℤ, 0 ≤ i → i ≤ l → ∃ j : Ix l, (j.val : ℤ) = i) ∧
((0 < l.toNat + 1 ∧ Fintype.card (Ix l) = l.toNat + 1) ∧
(∀ t : ℕ, h ((y ^ t) v) = ((l - 2 * (t : ℤ) : ℤ) : ℂ) • ((y ^ t) v)) ∧
(∀ t : ℕ, 0 < t → x ((y ^ t) v) = (((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ) • ((y ^ (t - 1)) v)))) ∧ (∀ i : Ix l, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((l - 2 * (i.val : ℤ) : ℤ) : ℂ) • ev y v i.val) ∧ (∃ B : Module.Basis (Ix l) ℂ V, ∀ i, B i = ev y v i.val) ∧ ((∀ t : ℕ, l.toNat + 1 ≤ t → (y ^ t) v = 0) ∧ genFormulas l x y h (fun i : Ix l => ev y v i.val)) ∧ ((∀ (i : Ix l) (r : ℕ), divided x r (ev y v i.val) =
  if r ≤ i.val then ((Nat.choose (l.toNat - i.val + r) r : ℕ) : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (i : Ix l) (r : ℕ), divided y r (ev y v i.val) =
  if i.val + r ≤ l.toNat then ((Nat.choose (i.val + r) r : ℕ) : ℂ) • ev y v (i.val + r) else 0))) :
    ∀ (B : Module.Basis (Ix l) ℂ V), (∀ i, B i = ev y v i.val) →
  (divided y l.toNat * divided x l.toNat = matrixUnit B (Fin.last l.toNat) (Fin.last l.toNat)) ∧
  (∀ i : Ix l, divided x (l.toNat - i.val) * (divided y l.toNat * divided x l.toNat) = matrixUnit B i (Fin.last l.toNat)) ∧
  (∀ j : Ix l, (divided y l.toNat * divided x l.toNat) * divided y (l.toNat - j.val) =
    ((Nat.choose l.toNat j.val : ℕ) : ℂ) • matrixUnit B (Fin.last l.toNat) j) ∧
  (∀ j : Ix l, IsUnit ((Nat.choose l.toNat j.val : ℕ) : R p)) := by
  classical
  intro B hB
  have hx := h_T005.2.2.2.2.1
  have hy := h_T005.2.2.2.2.2
  have hxtop (k : Ix l) :
      divided x l.toNat (B k) =
        if k = Fin.last l.toNat then ev y v 0 else 0 := by
    rw [hB k, hx k l.toNat]
    by_cases hk : k = Fin.last l.toNat
    · subst k
      simp
    · have hklt : k.val < l.toNat := by
        have := k.isLt
        have hne : k.val ≠ l.toNat := by
          intro he
          exact hk (Fin.ext he)
        omega
      simp [hk, Nat.not_le.mpr hklt]
  have hyzero : divided y l.toNat (ev y v 0) = ev y v l.toNat := by
    have hh := hy (⟨0, by omega⟩ : Ix l) l.toNat
    simpa using hh
  have hpi (k : Ix l) :
      (divided y l.toNat * divided x l.toNat) (B k) =
        if k = Fin.last l.toNat then B (Fin.last l.toNat) else 0 := by
    change divided y l.toNat (divided x l.toNat (B k)) = _
    rw [hxtop]
    split_ifs with hk
    · rw [hyzero, hB]
      rfl
    · exact map_zero _
  have hmu (i j k : Ix l) :
      matrixUnit B i j (B k) = if k = j then B i else 0 := by
    simp [matrixUnit, Module.Basis.coord_apply, Finsupp.single_apply]
  have hfirst : divided y l.toNat * divided x l.toNat =
      matrixUnit B (Fin.last l.toNat) (Fin.last l.toNat) := by
    apply B.ext
    intro k
    rw [hpi, hmu]
  have hxlast (i : Ix l) :
      divided x (l.toNat - i.val) (B (Fin.last l.toNat)) = B i := by
    rw [hB, hx]
    have hi : i.val ≤ l.toNat := Nat.le_of_lt_succ i.isLt
    simp [Nat.sub_sub_self hi, ← hB i]
  refine ⟨hfirst, ?_, ?_, ?_⟩
  · intro i
    apply B.ext
    intro k
    change divided x (l.toNat - i.val)
      ((divided y l.toNat * divided x l.toNat) (B k)) = _
    rw [hpi, hmu]
    split_ifs
    · exact hxlast i
    · exact map_zero _
  · intro j
    apply B.ext
    intro k
    have hj : j.val ≤ l.toNat := Nat.le_of_lt_succ j.isLt
    change (divided y l.toNat * divided x l.toNat)
      (divided y (l.toNat - j.val) (B k)) =
      (Nat.choose l.toNat j.val : ℂ) • (matrixUnit B (Fin.last l.toNat) j (B k))
    rw [hmu, hB k, hy]
    by_cases hk : k.val + (l.toNat - j.val) ≤ l.toNat
    · rw [if_pos hk]
      let t : Ix l := ⟨k.val + (l.toNat - j.val), by omega⟩
      have het : ev y v (k.val + (l.toNat - j.val)) = B t := (hB t).symm
      rw [het, map_smul, hpi]
      by_cases hkj : k = j
      · subst k
        have hsum : j.val + (l.toNat - j.val) = l.toNat := by omega
        have htlast : t = Fin.last l.toNat := Fin.ext (by dsimp [t]; omega)
        simp [htlast, hsum, Nat.choose_symm hj]
      · have htlast : t ≠ Fin.last l.toNat := by
          intro he
          have hv := congrArg Fin.val he
          have hne : k.val ≠ j.val := fun hh => hkj (Fin.ext hh)
          dsimp [t] at hv
          omega
        simp [htlast, hkj]
    · rw [if_neg hk, map_zero]
      have hkj : k ≠ j := by
        intro he
        subst k
        omega
      simp [hkj]
  · intro j
    have hj : j.val ≤ l.toNat := Nat.le_of_lt_succ j.isLt
    have hnp : l.toNat < p := by
      have hn := h_T005.1.1
      omega
    have hfac : ¬ p ∣ l.toNat.factorial := by
      rw [h_H001.1.dvd_factorial]
      omega
    have hc : ¬ p ∣ Nat.choose l.toNat j.val := by
      intro hd
      apply hfac
      rw [← Nat.choose_mul_factorial_mul_factorial hj]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
    have hcZ : ¬ (p : ℤ) ∣ (Nat.choose l.toNat j.val : ℤ) := by
      simpa only [Int.natCast_dvd_natCast] using hc
    have hcQ : (Nat.choose l.toNat j.val : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj).ne'
    have hinv : (Nat.choose l.toNat j.val : ℚ)⁻¹ ∈ scalarRing p := by
      apply Subring.subset_closure
      exact ⟨(Nat.choose l.toNat j.val : ℤ), hcZ, by simp⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(Nat.choose l.toNat j.val : ℚ)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    change (Nat.choose l.toNat j.val : ℚ) * (Nat.choose l.toNat j.val : ℚ)⁻¹ = 1
    exact mul_inv_cancel₀ hcQ

#check @T007
#print axioms T007

end Translation
