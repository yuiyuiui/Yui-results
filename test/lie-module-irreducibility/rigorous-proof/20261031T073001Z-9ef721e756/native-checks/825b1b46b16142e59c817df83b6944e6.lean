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

theorem T015 (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ l ∧ l < (p : ℤ)) (h_T008 : (∀ q : ℚ, q ∈ scalarRing p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ (((∃ ι : MR p M →ₗ[R p] V, iotaSpec p M ι ∧ Function.Injective ι ∧ LinearMap.range ι = L p M) ∧
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
  ∀ u ∈ L p M, matrixUnit B i j u ∈ L p M))) (h_T011 : (∀ i : Ix l, J p M (ev y v i.val) = J p M (ev y v 0)) ∧ (∃ s : (Ix l → J p M (ev y v 0)) ≃ₗ[R p] L p M,
  ∀ c, (s c : V) = ∑ i : Ix l, (c i : ℂ) • ev y v i.val) ∧ ((J p M (ev y v 0)).FG ∧ J p M (ev y v 0) ≠ ⊥)) (h_T014 : ∃ a : ℂ, a ∈ J p M (ev y v 0) ∧ a ≠ 0 ∧
 ∃ k : ℕ, 0 < k ∧ ∃ g : Fin k → ℂ,
 (∀ j, g j ≠ 0 ∧ ∃ q : ℚ, q ≠ 0 ∧ g j = (q : ℂ) * a) ∧
 Submodule.span (R p) (Set.range g) = J p M (ev y v 0)) :
    ∃ b : ℂ, b ∈ J p M (ev y v 0) ∧ b ≠ 0 ∧ J p M (ev y v 0) = Submodule.span (R p) {b} := by
  classical
  have factor : ∀ q : ℚ, q ≠ 0 → ∃ e : ℤ, ∃ u : ℚ, q = (p : ℚ) ^ e * u ∧ u ∈ scalarRing p ∧ u⁻¹ ∈ scalarRing p := by
    intro q hq
    have strip : ∀ z : ℤ, z ≠ 0 → ∃ n : ℕ, ∃ c : ℤ, z = (p : ℤ)^n * c ∧ ¬ (p : ℤ) ∣ c := by
      intro z hz
      have hf : FiniteMultiplicity (p : ℤ) z :=
        Int.finiteMultiplicity_iff.mpr ⟨by simpa using h_H001.1.ne_one, hz⟩
      obtain ⟨c, hc, hpc⟩ := hf.exists_eq_pow_mul_and_not_dvd
      exact ⟨_, c, hc, hpc⟩
    obtain ⟨n, c, hc, hpc⟩ := strip q.num (Rat.num_ne_zero.mpr hq)
    obtain ⟨m, d, hd, hpd⟩ := strip (q.den : ℤ) (by exact_mod_cast q.den_ne_zero)
    refine ⟨(n : ℤ) - m, (c : ℚ) / d, ?_, ?_, ?_⟩
    · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
      rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
      have hcn : (q.num : ℚ) = (p : ℚ)^n * c := by exact_mod_cast hc
      have hdn : (q.den : ℚ) = (p : ℚ)^m * d := by exact_mod_cast hd
      calc
        q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
        _ = ((p : ℚ)^n * c) / ((p : ℚ)^m * d) := by rw [hcn, hdn]
        _ = (p : ℚ)^n / (p : ℚ)^m * ((c : ℚ) / d) := by ring
    · exact (h_T008.1 _).mpr ⟨c, d, hpd, rfl⟩
    · rw [inv_div]
      exact (h_T008.1 _).mpr ⟨d, c, hpc, rfl⟩
  have rsmul : ∀ (r : R p) (z : ℂ), r • z = ((r : ℚ) : ℂ) * z := by
    intro r z
    rfl
  obtain ⟨a, haJ, ha0, k, hk, g, hg, hspan⟩ := h_T014
  choose q hq hgq using fun j => (hg j).2
  choose e u he hu hui using fun j => factor (q j) (hq j)
  have hu0 : ∀ j, u j ≠ 0 := by
    intro j hj
    have hz : q j = 0 := by simpa [hj] using he j
    exact hq j hz
  have gform : ∀ j, g j = (p : ℂ) ^ (e j) * (u j : ℂ) * a := by
    intro j
    rw [hgq j]
    have hc : (q j : ℂ) = (p : ℂ) ^ (e j) * (u j : ℂ) := by
      simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_natCast] using
        congrArg (fun t : ℚ => (t : ℂ)) (he j)
    rw [hc]
  obtain ⟨j₀, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin k)) e
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hmin' : ∀ j, e j₀ ≤ e j := fun j => hmin j (Finset.mem_univ j)
  let b : ℂ := (p : ℂ) ^ (e j₀) * a
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
  have hb0 : b ≠ 0 := mul_ne_zero (zpow_ne_zero _ hp0) ha0
  have hbJ : b ∈ J p M (ev y v 0) := by
    have hgj : g j₀ ∈ J p M (ev y v 0) := by
      rw [← hspan]
      exact Submodule.subset_span (Set.mem_range_self j₀)
    have hsm := (J p M (ev y v 0)).smul_mem
      (⟨(u j₀)⁻¹, hui j₀⟩ : R p) hgj
    have hb_eq : (⟨(u j₀)⁻¹, hui j₀⟩ : R p) • g j₀ = b := by
      rw [rsmul, gform, Rat.cast_inv]
      change (u j₀ : ℂ)⁻¹ * ((p : ℂ) ^ e j₀ * (u j₀ : ℂ) * a) =
        (p : ℂ) ^ e j₀ * a
      have huC : (u j₀ : ℂ) ≠ 0 := by exact_mod_cast hu0 j₀
      field_simp
    exact hb_eq ▸ hsm
  refine ⟨b, hbJ, hb0, le_antisymm ?_ ?_⟩
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    have hd : 0 ≤ e j - e j₀ := sub_nonneg.mpr (hmin' j)
    let n : ℕ := (e j - e j₀).toNat
    have hn : (n : ℤ) = e j - e j₀ := Int.toNat_of_nonneg hd
    have hcoeff : (p : ℚ)^n * u j ∈ scalarRing p :=
      (scalarRing p).mul_mem
        ((scalarRing p).pow_mem (natCast_mem (scalarRing p) p) n) (hu j)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨⟨(p : ℚ)^n * u j, hcoeff⟩, ?_⟩
    rw [rsmul]
    change (((p : ℚ)^n * u j : ℚ) : ℂ) * ((p : ℂ)^e j₀ * a) = g j
    rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, gform]
    have hpowers : (p : ℂ)^n * (p : ℂ)^e j₀ = (p : ℂ)^e j := by
      rw [← zpow_natCast, ← zpow_add₀ hp0, hn, sub_add_cancel]
    calc
      (p : ℂ)^n * (u j : ℂ) * ((p : ℂ)^e j₀ * a) =
          ((p : ℂ)^n * (p : ℂ)^e j₀) * (u j : ℂ) * a := by ring
      _ = (p : ℂ)^e j * (u j : ℂ) * a := by rw [hpowers]
  · exact (Submodule.span_singleton_le_iff_mem b _).mpr hbJ

#check @T015
#print axioms T015

end Translation
