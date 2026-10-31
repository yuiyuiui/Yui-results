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

theorem T005 (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ l ∧ l < (p : ℤ)) (h_T001 : ((l.toNat : ℤ) = l) ∧
(∀ i : Ix l, 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ l) ∧
(∀ i : ℤ, 0 ≤ i → i ≤ l → ∃ j : Ix l, (j.val : ℤ) = i) ∧
((0 < l.toNat + 1 ∧ Fintype.card (Ix l) = l.toNat + 1) ∧
(∀ t : ℕ, h ((y ^ t) v) = ((l - 2 * (t : ℤ) : ℤ) : ℂ) • ((y ^ t) v)) ∧
(∀ t : ℕ, 0 < t → x ((y ^ t) v) = (((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ) • ((y ^ (t - 1)) v)))) (h_T002 : ∀ i : Ix l, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((l - 2 * (i.val : ℤ) : ℤ) : ℂ) • ev y v i.val) (h_T003 : ∃ B : Module.Basis (Ix l) ℂ V, ∀ i, B i = ev y v i.val) (h_T004 : (∀ t : ℕ, l.toNat + 1 ≤ t → (y ^ t) v = 0) ∧ genFormulas l x y h (fun i : Ix l => ev y v i.val)) :
    (((l.toNat : ℤ) = l) ∧
(∀ i : Ix l, 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ l) ∧
(∀ i : ℤ, 0 ≤ i → i ≤ l → ∃ j : Ix l, (j.val : ℤ) = i) ∧
((0 < l.toNat + 1 ∧ Fintype.card (Ix l) = l.toNat + 1) ∧
(∀ t : ℕ, h ((y ^ t) v) = ((l - 2 * (t : ℤ) : ℤ) : ℂ) • ((y ^ t) v)) ∧
(∀ t : ℕ, 0 < t → x ((y ^ t) v) = (((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ) • ((y ^ (t - 1)) v)))) ∧ (∀ i : Ix l, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((l - 2 * (i.val : ℤ) : ℤ) : ℂ) • ev y v i.val) ∧ (∃ B : Module.Basis (Ix l) ℂ V, ∀ i, B i = ev y v i.val) ∧ ((∀ t : ℕ, l.toNat + 1 ≤ t → (y ^ t) v = 0) ∧ genFormulas l x y h (fun i : Ix l => ev y v i.val)) ∧ ((∀ (i : Ix l) (r : ℕ), divided x r (ev y v i.val) =
  if r ≤ i.val then ((Nat.choose (l.toNat - i.val + r) r : ℕ) : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (i : Ix l) (r : ℕ), divided y r (ev y v i.val) =
  if i.val + r ≤ l.toNat then ((Nat.choose (i.val + r) r : ℕ) : ℂ) • ev y v (i.val + r) else 0)) := by
  have hx : ∀ j : ℕ, j ≤ l.toNat → x (ev y v j) = if j = 0 then 0 else ((l.toNat - j + 1 : ℕ) : ℂ) • ev y v (j - 1) := by
    intro j hj
    have hg := h_T004.2.1 ⟨j, by omega⟩
    dsimp only at hg
    by_cases hz : j = 0
    · simpa [hz] using hg
    · have hp : 0 < j := by omega
      have hc : ((l - (j : ℤ) + 1 : ℤ) : ℂ) = ((l.toNat - j + 1 : ℕ) : ℂ) := by
        have hl : (l : ℂ) = (l.toNat : ℂ) := by exact_mod_cast h_T001.1.symm
        push_cast
        rw [Nat.cast_sub hj, hl]
      simpa [hp, hz, hc] using hg
  have hy : ∀ j : ℕ, j ≤ l.toNat → y (ev y v j) = if j < l.toNat then ((j + 1 : ℕ) : ℂ) • ev y v (j + 1) else 0 := by
    intro j hj
    have hg := h_T004.2.2.1 ⟨j, by omega⟩
    dsimp only at hg
    by_cases hp : j < l.toNat
    · simpa [show j + 1 < l.toNat + 1 by omega, hp] using hg
    · simpa [show ¬ j + 1 < l.toNat + 1 by omega, hp] using hg
  have px : ∀ (r j : ℕ), j ≤ l.toNat →
      (x ^ r) (ev y v j) =
        if r ≤ j then (((r.factorial * (l.toNat - j + r).choose r : ℕ) : ℂ)) • ev y v (j-r) else 0 := by
    intro r
    induction r with
    | zero => intro j hj; simp
    | succ r ih =>
      intro j hj
      rw [pow_succ', Module.End.mul_apply, ih j hj]
      by_cases hr : r ≤ j
      · rw [if_pos hr, map_smul]
        rw [hx (j-r) (by omega)]
        by_cases he : r = j
        · subst j
          simp
        · have hp : j-r ≠ 0 := by omega
          have hrs : r+1 ≤ j := by omega
          rw [if_neg hp, if_pos hrs, smul_smul]
          have heq : j-r-1 = j-(r+1) := by omega
          rw [heq]
          congr 1
          have hn : l.toNat - (j-r) + 1 = (l.toNat-j+r)+1 := by omega
          rw [hn]
          have hb := Nat.add_one_mul_choose_eq (l.toNat-j+r) r
          have hc : ((l.toNat-j+r+1 : ℕ) : ℂ) * (((l.toNat-j+r).choose r : ℕ) : ℂ) =
            (((l.toNat-j+r+1).choose (r+1) : ℕ) : ℂ) * ((r+1 : ℕ) : ℂ) := by exact_mod_cast hb
          simp only [Nat.factorial_succ, Nat.cast_mul]
          have hn' : l.toNat-j+(r+1) = l.toNat-j+r+1 := by omega
          rw [hn']
          linear_combination (r.factorial : ℂ) * hc
      · have hrs : ¬ r+1 ≤ j := by omega
        simp [hr, hrs]
  have py : ∀ (r j : ℕ), j ≤ l.toNat →
      (y ^ r) (ev y v j) =
        if j+r ≤ l.toNat then (((r.factorial * (j+r).choose r : ℕ) : ℂ)) • ev y v (j+r) else 0 := by
    intro r
    induction r with
    | zero => intro j hj; simp [hj]
    | succ r ih =>
      intro j hj
      rw [pow_succ', Module.End.mul_apply, ih j hj]
      by_cases hr : j+r ≤ l.toNat
      · rw [if_pos hr, map_smul, hy (j+r) hr]
        by_cases hp : j+r < l.toNat
        · have hrs : j+(r+1) ≤ l.toNat := by omega
          rw [if_pos hp, if_pos hrs, smul_smul]
          have heq : j+r+1 = j+(r+1) := by omega
          rw [← heq]
          congr 1
          have hb := Nat.add_one_mul_choose_eq (j+r) r
          have hc : ((j+r+1 : ℕ) : ℂ) * (((j+r).choose r : ℕ) : ℂ) =
            (((j+r+1).choose (r+1) : ℕ) : ℂ) * ((r+1 : ℕ) : ℂ) := by exact_mod_cast hb
          simp only [Nat.factorial_succ, Nat.cast_mul]
          linear_combination (r.factorial : ℂ) * hc
        · have hrs : ¬ j+(r+1) ≤ l.toNat := by omega
          simp [hp, hrs]
      · have hrs : ¬ j+(r+1) ≤ l.toNat := by omega
        simp [hr, hrs]
  refine ⟨h_T001, h_T002, h_T003, h_T004, ?_, ?_⟩
  · intro i r
    have hi : i.val ≤ l.toNat := by have := i.isLt; omega
    have hf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    change (r.factorial : ℂ)⁻¹ • (x ^ r) (ev y v i.val) = _
    rw [px r i.val hi]
    split_ifs with hr
    · simp only [Nat.cast_mul, smul_smul]
      rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
    · simp
  · intro i r
    have hi : i.val ≤ l.toNat := by have := i.isLt; omega
    have hf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    change (r.factorial : ℂ)⁻¹ • (y ^ r) (ev y v i.val) = _
    rw [py r i.val hi]
    split_ifs with hr
    · simp only [Nat.cast_mul, smul_smul]
      rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
    · simp

#check @T005
#print axioms T005

end Translation
