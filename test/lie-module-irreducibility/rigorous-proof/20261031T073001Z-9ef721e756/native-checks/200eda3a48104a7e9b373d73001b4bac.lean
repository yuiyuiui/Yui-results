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

theorem T001 (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : Module.Finite ℂ V ∧ Module.finrank ℂ V = l.toNat + 1 ∧ SimpleTriple x y h ∧
 h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h ∧
 ∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (l : ℂ) • w) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (l : ℂ) • v) :
    ((l.toNat : ℤ) = l) ∧
(∀ i : Ix l, 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ l) ∧
(∀ i : ℤ, 0 ≤ i → i ≤ l → ∃ j : Ix l, (j.val : ℤ) = i) ∧
((0 < l.toNat + 1 ∧ Fintype.card (Ix l) = l.toNat + 1) ∧
(∀ t : ℕ, h ((y ^ t) v) = ((l - 2 * (t : ℤ) : ℤ) : ℂ) • ((y ^ t) v)) ∧
(∀ t : ℕ, 0 < t → x ((y ^ t) v) = (((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ) • ((y ^ (t - 1)) v))) := by
  have hl : (l.toNat : ℤ) = l := by omega
  have hi : ∀ i : Ix l, 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ l := by
    intro i
    have hib := i.isLt
    constructor <;> omega
  have hj : ∀ i : ℤ, 0 ≤ i → i ≤ l → ∃ j : Ix l, (j.val : ℤ) = i := by
    intro i hi0 hil
    refine ⟨⟨i.toNat, ?_⟩, ?_⟩
    · omega
    · change (i.toNat : ℤ) = i
      omega
  have hn : 0 < l.toNat + 1 ∧ Fintype.card (Ix l) = l.toNat + 1 := by
    constructor
    · omega
    · simp [Ix]
  rcases h_H003 with ⟨_, _, _, _, hhy, hxy, _⟩
  have hh : ∀ u : V, h (y u) = y (h u) + (-2 : ℂ) • y u := by
    intro u
    have hu := congrArg (fun f : Module.End ℂ V => f u) hhy
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hu
    exact (sub_eq_iff_eq_add.mp hu).trans (add_comm _ _)
  have hx : ∀ u : V, x (y u) = y (x u) + h u := by
    intro u
    have hu := congrArg (fun f : Module.End ℂ V => f u) hxy
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hu
    exact (sub_eq_iff_eq_add.mp hu).trans (add_comm _ _)
  have hp (t : ℕ) : (y ^ (t + 1)) v = y ((y ^ t) v) := by
    rw [pow_succ', Module.End.mul_apply]
  have hind : ∀ t : ℕ,
      (h ((y ^ t) v) = ((l - 2 * (t : ℤ) : ℤ) : ℂ) • ((y ^ t) v)) ∧
      (x ((y ^ t) v) = (((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ) • ((y ^ (t - 1)) v)) := by
    intro t
    induction t with
    | zero =>
        constructor
        · simpa using h_H004.2.2
        · simpa using h_H004.2.1
    | succ t ih =>
        constructor
        · rw [hp, hh, ih.1, map_smul, ← add_smul]
          congr 1
          push_cast
          ring
        · have hyx : y (x ((y ^ t) v)) =
              ((((t : ℤ) * (l - (t : ℤ) + 1) : ℤ) : ℂ)) • ((y ^ t) v) := by
            cases t with
            | zero => simp [h_H004.2.1]
            | succ s =>
                rw [ih.2]
                simp only [Nat.add_sub_cancel, map_smul]
                rw [← hp s]
          rw [hp, hx, hyx, ih.1, ← add_smul]
          simp only [Nat.succ_sub_one]
          congr 1
          push_cast
          ring
  exact ⟨hl, hi, hj, hn, (fun t => (hind t).1), (fun t _ => (hind t).2)⟩

#check @T001
#print axioms T001

end Translation
