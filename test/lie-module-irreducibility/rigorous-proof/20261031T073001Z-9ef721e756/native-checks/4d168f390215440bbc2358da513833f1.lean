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

theorem T019 (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : (((l.toNat : ℤ) = l) ∧
(∀ i : Ix l, 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ l) ∧
(∀ i : ℤ, 0 ≤ i → i ≤ l → ∃ j : Ix l, (j.val : ℤ) = i) ∧
((0 < l.toNat + 1 ∧ Fintype.card (Ix l) = l.toNat + 1) ∧
(∀ t : ℕ, h ((y ^ t) v) = ((l - 2 * (t : ℤ) : ℤ) : ℂ) • ((y ^ t) v)) ∧
(∀ t : ℕ, 0 < t → x ((y ^ t) v) = (((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ) • ((y ^ (t - 1)) v)))) ∧ (∀ i : Ix l, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((l - 2 * (i.val : ℤ) : ℤ) : ℂ) • ev y v i.val) ∧ (∃ B : Module.Basis (Ix l) ℂ V, ∀ i, B i = ev y v i.val) ∧ ((∀ t : ℕ, l.toNat + 1 ≤ t → (y ^ t) v = 0) ∧ genFormulas l x y h (fun i : Ix l => ev y v i.val)) ∧ ((∀ (i : Ix l) (r : ℕ), divided x r (ev y v i.val) =
  if r ≤ i.val then ((Nat.choose (l.toNat - i.val + r) r : ℕ) : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (i : Ix l) (r : ℕ), divided y r (ev y v i.val) =
  if i.val + r ≤ l.toNat then ((Nat.choose (i.val + r) r : ℕ) : ℂ) • ev y v (i.val + r) else 0))) (h_T008 : (∀ q : ℚ, q ∈ scalarRing p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ (((∃ ι : MR p M →ₗ[R p] V, iotaSpec p M ι ∧ Function.Injective ι ∧ LinearMap.range ι = L p M) ∧
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
  ∀ u ∈ L p M, matrixUnit B i j u ∈ L p M))) (h_T016 : (∃ μ : (ℚ ⊗[R p] J p M (ev y v 0)) →ₗ[ℚ] ℂ,
  (∀ (q : ℚ) (c : J p M (ev y v 0)), μ (q ⊗ₜ[R p] c) = (q : ℂ) * (c : ℂ)) ∧
  Function.Injective μ ∧ LinearMap.range μ = Submodule.span ℚ (J p M (ev y v 0) : Set ℂ)) ∧ (Module.finrank ℚ (ℚ ⊗[R p] J p M (ev y v 0)) = 1) ∧ (∃ b : ℂ, b ∈ J p M (ev y v 0) ∧ b ≠ 0 ∧ J p M (ev y v 0) = Submodule.span (R p) {b}) ∧ (∀ b : ℂ, b ∈ J p M (ev y v 0) → b ≠ 0 →
  J p M (ev y v 0) = Submodule.span (R p) {b} →
  ∃ B : Module.Basis (Ix l) (R p) (L p M), ∀ i, (B i : V) = b • ev y v i.val)) (h_T017 : ∀ [hc : CharP K p], ∃ κ : R p →+* K,
 (∀ (a b : ℤ) (r : R p), (r : ℚ) = (a : ℚ) / (b : ℚ) → ¬ (p : ℤ) ∣ b →
    κ r = (a : K) * (b : K)⁻¹) ∧
 ∃ C : RK κ M ≃ₗ[K] VK K M, canonicalR κ M C ∧
 (∀ (f : Module.End ℤ M) (w : RK κ M),
    C (throughR κ f w) = f.baseChange K (C w)) ∧
 ∃ D : FK p K M ≃ₗ[K] VK K M, canonicalF κ M D ∧
 (∀ (f : Module.End ℤ M) (w : FK p K M),
    D (throughF p K f w) = f.baseChange K (D w))) :
    (∀ fx fy fh : Module.End ℤ M,
 LiftOf M x fx → LiftOf M y fy → LiftOf M h fh → ∃ β : Module.Basis (Ix l) K (VK K M),
 basisOrigin M y v β ∧ genFormulas l (fx.baseChange K) (fy.baseChange K) (fh.baseChange K) β) ∧ Module.finrank K (VK K M) = l.toNat + 1 ∧ Nontrivial (VK K M) := by
  classical
  letI : CharP K p := h_H001.2
  obtain ⟨b, hbJ, hb0, hbspan⟩ := h_T016.2.2.1
  obtain ⟨BL, hBL⟩ := h_T016.2.2.2 b hbJ hb0 hbspan
  obtain ⟨ι, hι, hιinj, hιrange⟩ := h_T008.2.1.1
  let E : MR p M ≃ₗ[R p] L p M :=
    (LinearEquiv.ofInjective ι hιinj).trans
      (LinearEquiv.ofEq _ _ hιrange)
  let B : Module.Basis (Ix l) (R p) (MR p M) := BL.map E.symm
  have hE (u : MR p M) : (E u : V) = ι u := rfl
  have hB (i : Ix l) : ι (B i) = b • ev y v i.val := by
    rw [← hE]
    change (E (E.symm (BL i)) : V) = _
    rw [E.apply_symm_apply, hBL]
  obtain ⟨κ, hκ, C, hC, hCf, hD⟩ := h_T017
  letI := κ.toAlgebra
  let β : Module.Basis (Ix l) K (VK K M) := (B.baseChange K).map C
  have hβ (i : Ix l) : β i = C (pureR κ 1 (B i)) := by
    simp [β, pureR]
  have horigin : basisOrigin M y v β :=
    ⟨b, hbJ, hb0, ι, hι, hιinj, B, hB, κ, C, hC, hβ⟩
  have compat (f : Module.End ℤ M) (a : Module.End ℂ V)
      (hf : LiftOf M a f) (u : MR p M) :
      ι (f.baseChange (R p) u) = a (ι u) := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [LinearMap.baseChange_tmul, hι r (f m), hι r m]
      rw [hf m, map_smul]
    | add u w hu hw =>
      simp only [map_add, hu, hw]
  have red (f : Module.End ℤ M) (u : MR p M) :
      f.baseChange K (C (pureR κ 1 u)) =
        C (pureR κ 1 (f.baseChange (R p) u)) := by
    rw [← hCf]
    rfl
  have transfer (f : Module.End ℤ M) (a : Module.End ℂ V)
      (hf : LiftOf M a f) (i j : Ix l) (z : ℤ)
      (he : a (ev y v i.val) = z • ev y v j.val) :
      f.baseChange K (β i) = z • β j := by
    have hr : f.baseChange (R p) (B i) = z • B j := by
      apply hιinj
      rw [compat f a hf, hB, map_smul, he, map_zsmul, hB, smul_comm]
    rw [hβ, red, hr, hβ]
    simp only [pureR, TensorProduct.tmul_smul, map_zsmul]
  have transfer0 (f : Module.End ℤ M) (a : Module.End ℂ V)
      (hf : LiftOf M a f) (i : Ix l)
      (he : a (ev y v i.val) = 0) :
      f.baseChange K (β i) = 0 := by
    have hr : f.baseChange (R p) (B i) = 0 := by
      apply hιinj
      rw [compat f a hf, hB, map_smul, he, smul_zero, map_zero]
    rw [hβ, red, hr]
    simp [pureR]
  have hgen := h_T005.2.2.2.1.2
  have hall : ∀ fx fy fh : Module.End ℤ M,
      LiftOf M x fx → LiftOf M y fy → LiftOf M h fh →
        genFormulas l (fx.baseChange K) (fy.baseChange K) (fh.baseChange K) β := by
    intro fx fy fh hfx hfy hfh
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hi : 0 < i.val
      · simp only [dif_pos hi]
        apply (transfer fx x hfx i _ (l - (i.val : ℤ) + 1) ?_).trans
        · simpa only [genFormulas, dif_pos hi, Int.cast_smul_eq_zsmul] using hgen.1 i
        · simp only [Int.cast_smul_eq_zsmul]
      · simp only [dif_neg hi]
        apply transfer0 fx x hfx i
        simpa only [dif_neg hi] using hgen.1 i
    · intro i
      by_cases hi : i.val + 1 < l.toNat + 1
      · simp only [dif_pos hi]
        apply (transfer fy y hfy i _ (i.val + 1 : ℕ) ?_).trans
        · simpa only [dif_pos hi, Nat.cast_smul_eq_nsmul, Int.natCast_zsmul] using hgen.2.1 i
        · simp only [Int.natCast_zsmul, Nat.cast_smul_eq_nsmul]
      · simp only [dif_neg hi]
        apply transfer0 fy y hfy i
        simpa only [dif_neg hi] using hgen.2.1 i
    · intro i
      apply (transfer fh h hfh i i (l - 2 * (i.val : ℤ)) ?_).trans
      · simpa only [Int.cast_smul_eq_zsmul] using hgen.2.2 i
      · simp only [Int.cast_smul_eq_zsmul]
  refine ⟨?_, ?_, ?_⟩
  · intro fx fy fh hfx hfy hfh
    exact ⟨β, horigin, hall fx fy fh hfx hfy hfh⟩
  · simpa only [Ix, Fintype.card_fin] using Module.finrank_eq_card_basis β
  · exact ⟨⟨β ⟨0, Nat.zero_lt_succ _⟩, 0, β.ne_zero _⟩⟩

#check @T019
#print axioms T019

end Translation
