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

theorem T006 (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p ∧ CharP K p) (h_H002 : 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = l.toNat + 1 ∧ SimpleTriple x y h ∧
 h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧
 ∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w) (h_H005 : (∃ d : ℕ, ∃ b : Module.Basis (Fin d) ℤ M, ∃ B : Module.Basis (Fin d) ℂ V, ∀ i, (b i : V) = B i) ∧
 ∀ r : ℕ, Preserves M (divided x r) ∧ Preserves M (divided y r)) (h_T005 : (((l.toNat : ℤ) = l) ∧
(∀ i : Ix l, 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ l) ∧
(∀ i : ℤ, 0 ≤ i → i ≤ l → ∃ j : Ix l, (j.val : ℤ) = i) ∧
((0 < l.toNat + 1 ∧ Fintype.card (Ix l) = l.toNat + 1) ∧
(∀ t : ℕ, h ((y ^ t) v) = ((l - 2 * (t : ℤ) : ℤ) : ℂ) • ((y ^ t) v)) ∧
(∀ t : ℕ, 0 < t → x ((y ^ t) v) = (((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ) • ((y ^ (t - 1)) v)))) ∧ (∀ i : Ix l, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((l - 2 * (i.val : ℤ) : ℤ) : ℂ) • ev y v i.val) ∧ (∃ B : Module.Basis (Ix l) ℂ V, ∀ i, B i = ev y v i.val) ∧ ((∀ t : ℕ, l.toNat + 1 ≤ t → (y ^ t) v = 0) ∧ genFormulas l x y h (fun i : Ix l => ev y v i.val)) ∧ ((∀ (i : Ix l) (r : ℕ), divided x r (ev y v i.val) =
  if r ≤ i.val then ((Nat.choose (l.toNat - i.val + r) r : ℕ) : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (i : Ix l) (r : ℕ), divided y r (ev y v i.val) =
  if i.val + r ≤ l.toNat then ((Nat.choose (i.val + r) r : ℕ) : ℂ) • ev y v (i.val + r) else 0))) :
    (∀ q : ℚ, q ∈ scalarRing p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)) ∧ ((∃ ι : MR p M →ₗ[R p] V, iotaSpec p M ι ∧ Function.Injective ι ∧ LinearMap.range ι = L p M) ∧
Nonempty (Module.Basis (Ix l) (R p) (MR p M)) ∧
Submodule.span ℂ (M : Set V) = ⊤ ∧
(∀ r : ℕ, Preserves M (divided x r) ∧ Preserves M (divided y r)) ∧
Preserves M x ∧ Preserves M y ∧ Preserves M h ∧
(∀ r : ℕ, (∀ u ∈ L p M, divided x r u ∈ L p M) ∧ (∀ u ∈ L p M, divided y r u ∈ L p M)) ∧
(∀ u ∈ L p M, x u ∈ L p M ∧ y u ∈ L p M ∧ h u ∈ L p M) ∧
(∃ fx fy fh : Module.End ℤ M, LiftOf M x fx ∧ LiftOf M y fy ∧ LiftOf M h fh) ∧
(∃ DX DY : ℕ → Module.End ℤ M, ∀ r, LiftOf M (divided x r) (DX r) ∧ LiftOf M (divided y r) (DY r))) := by
  constructor
  ·
    have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using h_H001.1)
    have hb0 : ∀ b : ℤ, ¬ (p : ℤ) ∣ b → (b : ℚ) ≠ 0 := by
      intro b hb
      exact_mod_cast (show b ≠ 0 from fun he => hb (he ▸ dvd_zero _))
    intro q
    constructor
    · intro hq
      induction hq using Subring.closure_induction with
      | mem q hq =>
        obtain ⟨b, hb, rfl⟩ := hq
        exact ⟨1, b, hb, by simp⟩
      | zero => exact ⟨0, 1, hp.not_dvd_one, by simp⟩
      | one => exact ⟨1, 1, hp.not_dvd_one, by simp⟩
      | add q r hq hr iq ir =>
        obtain ⟨a, b, hb, rfl⟩ := iq
        obtain ⟨c, d, hd, rfl⟩ := ir
        refine ⟨a*d+c*b, b*d, ?_, ?_⟩
        · exact fun hh => (hp.dvd_mul.mp hh).elim hb hd
        · push_cast
          simpa [mul_comm] using (div_add_div (a : ℚ) (c : ℚ) (hb0 b hb) (hb0 d hd))
      | neg q hq iq =>
        obtain ⟨a, b, hb, rfl⟩ := iq
        exact ⟨-a, b, hb, by push_cast; ring⟩
      | mul q r hq hr iq ir =>
        obtain ⟨a, b, hb, rfl⟩ := iq
        obtain ⟨c, d, hd, rfl⟩ := ir
        refine ⟨a*c, b*d, ?_, ?_⟩
        · exact fun hh => (hp.dvd_mul.mp hh).elim hb hd
        · push_cast; ring
    · rintro ⟨a, b, hb, rfl⟩
      exact (scalarRing p).mul_mem (intCast_mem (scalarRing p) a)
        (Subring.subset_closure ⟨b, hb, rfl⟩)
  ·
    have hbasis : (∃ ι : MR p M →ₗ[R p] V, iotaSpec p M ι ∧ Function.Injective ι ∧ LinearMap.range ι = L p M) ∧
        Nonempty (Module.Basis (Ix l) (R p) (MR p M)) ∧ Submodule.span ℂ (M : Set V) = ⊤ := by
      classical
      obtain ⟨d, b, B, hb⟩ := h_H005.1
      let bR : Module.Basis (Fin d) (R p) (MR p M) := b.baseChange (R p)
      let ι : MR p M →ₗ[R p] V := M.subtype.liftBaseChange (R p)
      have hi : iotaSpec p M ι := by
        intro r m
        rfl
      have hiB : ∀ i, ι (bR i) = B i := by
        intro i
        simpa [bR, ι] using hb i
      have hri : Function.Injective (algebraMap (R p) ℂ) := by
        intro a b hab
        apply Subtype.ext
        change (algebraMap ℚ ℂ) (a : ℚ) = (algebraMap ℚ ℂ) (b : ℚ) at hab
        exact (algebraMap ℚ ℂ).injective hab
      have hli : LinearIndependent (R p) (fun i => B i) := by
        rw [linearIndependent_iff']
        intro s g hg i hi
        have hc : ∑ j ∈ s, (algebraMap (R p) ℂ (g j)) • B j = 0 := hg
        have he := (linearIndependent_iff'.mp B.linearIndependent) s
          (fun j => algebraMap (R p) ℂ (g j)) hc i hi
        apply hri
        simpa only [map_zero] using he
      have hinj : Function.Injective ι := by
        apply LinearMap.injective_of_linearIndependent bR.span_eq
        simpa only [Function.comp_def, hiB] using hli
      have hrange : LinearMap.range ι = L p M := by
        change LinearMap.range (M.subtype.liftBaseChange (R p)) = _
        rw [LinearMap.range_liftBaseChange]
        simp [L]
      have hd : d = l.toNat + 1 := by
        have hh := Module.finrank_eq_card_basis B
        simpa only [Fintype.card_fin, h_H003.2.1] using hh.symm
      have he : Fin d ≃ Ix l := finCongr hd
      refine ⟨⟨ι, hi, hinj, hrange⟩, ⟨bR.reindex he⟩, ?_⟩
      apply top_unique
      rw [← B.span_eq]
      apply Submodule.span_mono
      rintro u ⟨i, rfl⟩
      rw [← hb i]
      exact (b i).property
    refine ⟨hbasis.1, hbasis.2.1, hbasis.2.2, ?_⟩
    classical
    have extend : ∀ a : Module.End ℂ V, Preserves M a →
        (∀ u ∈ L p M, a u ∈ L p M) ∧ ∃ f : Module.End ℤ M, LiftOf M a f := by
      intro a ha
      constructor
      · intro u hu
        change u ∈ Submodule.span (R p) (M : Set V) at hu
        induction hu using Submodule.span_induction with
        | mem u hu => exact Submodule.subset_span (ha ⟨u, hu⟩)
        | zero => simpa using (L p M).zero_mem
        | add u v hu hv iu iv =>
          simpa only [map_add] using (L p M).add_mem iu iv
        | smul r u hu iu =>
          change a ((algebraMap (R p) ℂ r) • u) ∈ L p M
          rw [map_smul]
          exact (L p M).smul_mem r iu
      · refine ⟨LinearMap.codRestrict M ((a.restrictScalars ℤ).domRestrict M) ha, ?_⟩
        intro m
        rfl
    have hx : Preserves M x := by simpa [divided] using (h_H005.2 1).1
    have hy : Preserves M y := by simpa [divided] using (h_H005.2 1).2
    have hh : Preserves M h := by
      intro m
      rw [← h_H003.2.2.2.2.2.1]
      change x (y (m : V)) - y (x (m : V)) ∈ M
      exact M.sub_mem (hx ⟨y (m : V), hy m⟩) (hy ⟨x (m : V), hx m⟩)
    obtain ⟨fx, hfx⟩ := (extend x hx).2
    obtain ⟨fy, hfy⟩ := (extend y hy).2
    obtain ⟨fh, hfh⟩ := (extend h hh).2
    choose DX hDX using fun r => (extend (divided x r) (h_H005.2 r).1).2
    choose DY hDY using fun r => (extend (divided y r) (h_H005.2 r).2).2
    refine ⟨h_H005.2, hx, hy, hh, ?_, ?_, ⟨fx, fy, fh, hfx, hfy, hfh⟩, ?_⟩
    · intro r
      exact ⟨(extend (divided x r) (h_H005.2 r).1).1,
        (extend (divided y r) (h_H005.2 r).2).1⟩
    · intro u hu
      exact ⟨(extend x hx).1 u hu, (extend y hy).1 u hu, (extend h hh).1 u hu⟩
    · exact ⟨DX, DY, fun r => ⟨hDX r, hDY r⟩⟩

#check @T006
#print axioms T006

end Translation
