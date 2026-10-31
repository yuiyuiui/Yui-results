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

theorem T021 (p : ℕ) (K : Type) [instK : Field K] (l : ℤ) (V : Type) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H002 : 0 ≤ l ∧ l < (p : ℤ)) (h_T020 : ((∃ fx fy fh : Module.End ℤ M, LiftOf M x fx ∧ LiftOf M y fy ∧ LiftOf M h fh) ∧
(∃ DX DY : ℕ → Module.End ℤ M, ∀ r, LiftOf M (divided x r) (DX r) ∧ LiftOf M (divided y r) (DY r))) ∧ ((∀ [hc : CharP K p], ∃ κ : R p →+* K,
 (∀ (a b : ℤ) (r : R p), (r : ℚ) = (a : ℚ) / (b : ℚ) → ¬ (p : ℤ) ∣ b →
    κ r = (a : K) * (b : K)⁻¹) ∧
 ∃ C : RK κ M ≃ₗ[K] VK K M, canonicalR κ M C ∧
 (∀ (f : Module.End ℤ M) (w : RK κ M),
    C (throughR κ f w) = f.baseChange K (C w)) ∧
 ∃ D : FK p K M ≃ₗ[K] VK K M, canonicalF κ M D ∧
 (∀ (f : Module.End ℤ M) (w : FK p K M),
    D (throughF p K f w) = f.baseChange K (D w))) ∧ (∃ q : MR p M →ₗ[ℤ] Red p M,
 (∀ u, q u = (1 : ZMod p) ⊗ₜ[ℤ] u) ∧
 Function.Surjective q ∧ LinearMap.ker q = (pPart p M).restrictScalars ℤ) ∧ ((∀ fx fy fh : Module.End ℤ M,
 LiftOf M x fx → LiftOf M y fy → LiftOf M h fh → ∃ β : Module.Basis (Ix l) K (VK K M),
 basisOrigin M y v β ∧ genFormulas l (fx.baseChange K) (fy.baseChange K) (fh.baseChange K) β) ∧ Module.finrank K (VK K M) = l.toNat + 1 ∧ Nontrivial (VK K M)) ∧ (∀ fx fy fh : Module.End ℤ M,
 LiftOf M x fx → LiftOf M y fy → LiftOf M h fh →
 ∀ DX DY : ℕ → Module.End ℤ M,
 (∀ r, LiftOf M (divided x r) (DX r) ∧ LiftOf M (divided y r) (DY r)) →
 ∃ β : Module.Basis (Ix l) K (VK K M),
 basisOrigin M y v β ∧ genFormulas l (fx.baseChange K) (fy.baseChange K) (fh.baseChange K) β ∧
 (∀ r : ℕ, r ≤ l.toNat → (r.factorial : K) ≠ 0 ∧
   (DX r).baseChange K = (r.factorial : K)⁻¹ • (fx.baseChange K)^r ∧
   (DY r).baseChange K = (r.factorial : K)⁻¹ • (fy.baseChange K)^r) ∧
 (∀ j : Ix l, ((Nat.choose l.toNat j.val : ℕ) : K) ≠ 0) ∧
 (∀ i j : Ix l, matrixUnit β i j =
  (((Nat.choose l.toNat j.val : ℕ) : K)⁻¹) •
  ((DX (l.toNat - i.val)).baseChange K *
    ((DY l.toNat).baseChange K * (DX l.toNat).baseChange K) *
    (DY (l.toNat - j.val)).baseChange K)) ∧
 (∀ i j k : Ix l, matrixUnit β i j (β k) = if j = k then β i else 0)))) :
    ∀ fx fy fh : Module.End ℤ M,
 LiftOf M x fx → LiftOf M y fy → LiftOf M h fh → ∀ DX DY : ℕ → Module.End ℤ M,
 (∀ r, LiftOf M (divided x r) (DX r) ∧ LiftOf M (divided y r) (DY r)) →
 ∀ β : Module.Basis (Ix l) K (VK K M),
 (∀ i j : Ix l, matrixUnit β i j =
  (((Nat.choose l.toNat j.val : ℕ) : K)⁻¹) •
   ((DX (l.toNat - i.val)).baseChange K * ((DY l.toNat).baseChange K * (DX l.toNat).baseChange K) * (DY (l.toNat - j.val)).baseChange K)) →
 (∀ r : ℕ, r ≤ l.toNat →
   (DX r).baseChange K = (r.factorial : K)⁻¹ • (fx.baseChange K)^r ∧
   (DY r).baseChange K = (r.factorial : K)⁻¹ • (fy.baseChange K)^r) →
 ∀ W : Submodule K (VK K M),
 Stable W (fx.baseChange K) → Stable W (fy.baseChange K) → Stable W (fh.baseChange K) →
 ∀ i j : Ix l, Stable W (matrixUnit β i j) := by
  intro fx fy fh hfx hfy hfh DX DY hD β hmatrix hdiv W hx hy hh
  have hmul (a b : Module.End K (VK K M))
      (ha : Stable W a) (hb : Stable W b) : Stable W (a * b) := by
    intro u hu
    change a (b u) ∈ W
    exact ha (b u) (hb u hu)
  have hsmul (c : K) (a : Module.End K (VK K M))
      (ha : Stable W a) : Stable W (c • a) := by
    intro u hu
    change c • a u ∈ W
    exact W.smul_mem c (ha u hu)
  have hpow (a : Module.End K (VK K M)) (ha : Stable W a)
      (r : ℕ) : Stable W (a ^ r) := by
    induction r with
    | zero =>
        intro u hu
        simpa using hu
    | succ r ih =>
        rw [pow_succ]
        exact hmul (a ^ r) a ih ha
  have hDX (r : ℕ) (hr : r ≤ l.toNat) : Stable W ((DX r).baseChange K) := by
    rw [(hdiv r hr).1]
    exact hsmul _ _ (hpow _ hx r)
  have hDY (r : ℕ) (hr : r ≤ l.toNat) : Stable W ((DY r).baseChange K) := by
    rw [(hdiv r hr).2]
    exact hsmul _ _ (hpow _ hy r)
  intro i j
  rw [hmatrix i j]
  apply hsmul
  apply hmul
  · apply hmul
    · exact hDX (l.toNat - i.val) (Nat.sub_le _ _)
    · exact hmul _ _ (hDY l.toNat le_rfl) (hDX l.toNat le_rfl)
  · exact hDY (l.toNat - j.val) (Nat.sub_le _ _)

#check @T021
#print axioms T021

end Translation
