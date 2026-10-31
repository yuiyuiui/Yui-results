import Mathlib
open scoped TensorProduct
namespace LR
abbrev L := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ
abbrev R (p : ℕ) := Subring.closure {q : ℚ | ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b}
abbrev C (p : ℕ) := RestrictScalars (R p) ℚ ℂ
abbrev I (l : ℤ) := Fin (l.toNat + 1)
abbrev MR (p : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
abbrev VK (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Submodule ℤ V) := K ⊗[ℤ] M
noncomputable def dp {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V := ((r.factorial : ℂ)⁻¹) • f ^ r

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
noncomputable def eNat (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dp y i v
def Stable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] (W : Submodule F A) (f : Module.End F A) : Prop := ∀ w ∈ W, f w ∈ W
def ComplexHyp (l : ℤ) (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) : Prop :=
  IsSl2Triple h x y ∧ Submodule.span ℂ ({x,y,h} : Set L) = ⊤ ∧
  (∀ s t : L, rho ⁅s,t⁆ = rho s * rho t - rho t * rho s) ∧
  FiniteDimensional ℂ V ∧ Module.finrank ℂ V = l.toNat + 1 ∧
  Nontrivial V ∧
  (∀ W : Submodule ℂ V, (∀ t : L, Stable W (rho t)) → W = ⊥ ∨ W = ⊤) ∧
  (∃ w : V, w ≠ 0 ∧ rho x w = 0 ∧ rho h w = (l : ℂ) • w)
def Admissible (rho : L →ₗ[ℂ] Module.End ℂ V) (x y : L) (M : Submodule ℤ V) : Prop :=
  (∃ (ι : Type) (b : Module.Basis ι ℤ M) (bc : Module.Basis ι ℂ V), ∀ i, (b i : V) = bc i) ∧
  (∀ r : ℕ, ∀ m ∈ M, dp (rho x) r m ∈ M ∧ dp (rho y) r m ∈ M)
def Strings (l : ℤ) (a d t : Module.End ℂ V) (v : V) : Prop :=
  (∀ r : ℕ, t ((d ^ r) v) = ((l : ℂ) - 2 * (r : ℂ)) • (d ^ r) v) ∧
  (∀ r : ℕ, 0 < r → a ((d ^ r) v) = ((r : ℂ) * ((l : ℂ) - (r : ℂ) + 1)) • (d ^ (r-1)) v)
def BasisString (l : ℤ) (d : Module.End ℂ V) (v : V) : Prop :=
  ∃ b : Module.Basis (I l) ℂ V, (∀ i, b i = eNat d v i.val) ∧
    (∀ r : ℕ, l.toNat < r → (d ^ r) v = 0)
def Matrices {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
    (l : ℤ) (a d t : Module.End F A) (e : ℕ → A) : Prop :=
  a (e 0) = 0 ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ l.toNat → a (e i) = ((l : F) - (i : F) + 1) • e (i-1)) ∧
  (∀ i : ℕ, i < l.toNat → d (e i) = ((i : F)+1) • e (i+1)) ∧
  d (e l.toNat) = 0 ∧
  (∀ i : ℕ, i ≤ l.toNat → t (e i) = ((l : F) - 2*(i : F)) • e i)
def DividedMatrices (l : ℤ) (a d : Module.End ℂ V) (v : V) : Prop :=
  ∀ r i : ℕ, i ≤ l.toNat →
    dp a r (eNat d v i) =
      (if r ≤ i then (Nat.choose (l.toNat-i+r) r : ℂ) • eNat d v (i-r) else 0) ∧
    dp d r (eNat d v i) =
      (if i+r ≤ l.toNat then (Nat.choose (i+r) r : ℂ) • eNat d v (i+r) else 0)
def N1 (l : ℤ) (a d t : Module.End ℂ V) (v : V) : Prop :=
  0 < l+1 ∧ Fintype.card (I l) = (l+1).toNat ∧ Strings l a d t v ∧
  BasisString l d v ∧ Matrices l a d t (eNat d v) ∧ DividedMatrices l a d v
noncomputable def unit (l : ℤ) (b : Module.Basis (I l) ℂ V) (i j : I l) : Module.End ℂ V :=
  (b.coord j).smulRight (b i)
def BasisSpec (l : ℤ) (d : Module.End ℂ V) (v : V) (b : Module.Basis (I l) ℂ V) : Prop :=
  ∀ i, b i = eNat d v i.val
def LocalRingSpec (p : ℕ) : Prop :=
  (∀ q : ℚ, q ∈ R p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b) ∧
  (∀ b : ℤ, ¬ (p : ℤ) ∣ b → IsUnit (b : R p))
def SmallUnits (p : ℕ) (l : ℤ) : Prop :=
  (∀ r : ℕ, r ≤ l.toNat → ¬ p ∣ r.factorial ∧ IsUnit (r.factorial : R p)) ∧
  (∀ j : I l, IsUnit (Nat.choose l.toNat j.val : R p))
def IotaSpec (p : ℕ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V) : Prop :=
  (∀ (r : R p) (m : M), f (r ⊗ₜ[ℤ] m) = (((r : ℚ) : ℂ)) • (m : V)) ∧
  (∀ (r : R p) (z : MR p M), f (r • z) = (((r : ℚ) : ℂ)) • f z)
def LocalBasis (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V) : Prop :=
  Function.Injective f ∧
  Nonempty (Module.Basis (I l) (R p) (MR p M)) ∧
  Submodule.span ℂ (Set.range f) = ⊤
def Preserved (p : ℕ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V) (a d : Module.End ℂ V) : Prop :=
  (∀ r : ℕ, ∀ m ∈ M, dp a r m ∈ M ∧ dp d r m ∈ M) ∧
  (∀ r : ℕ, ∀ z : MR p M, dp a r (f z) ∈ Set.range f ∧ dp d r (f z) ∈ Set.range f)
def UnitIdentities (l : ℤ) (a d : Module.End ℂ V) (b : Module.Basis (I l) ℂ V) : Prop :=
  ∀ i j : I l,
    dp d l.toNat * dp a l.toNat = unit l b (Fin.last l.toNat) (Fin.last l.toNat) ∧
    dp a (l.toNat-i.val) * (dp d l.toNat * dp a l.toNat) = unit l b i (Fin.last l.toNat) ∧
    (dp d l.toNat * dp a l.toNat) * dp d (l.toNat-j.val) = (Nat.choose l.toNat j.val : ℂ) • unit l b (Fin.last l.toNat) j
def AllUnits (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (f : MR p M →ₗ[ℤ] V)
    (a d : Module.End ℂ V) (b : Module.Basis (I l) ℂ V) : Prop :=
  ∀ i j : I l,
    unit l b i j = ((Nat.choose l.toNat j.val : ℂ)⁻¹) •
      (dp a (l.toNat-i.val) * (dp d l.toNat * dp a l.toNat) * dp d (l.toNat-j.val)) ∧
    (∀ z : MR p M, unit l b i j (f z) ∈ Set.range f)

abbrev LZ (x y h : L) := Submodule.span ℤ ({x,y,h} : Set L)
def Lift (K : Type*) [Field K] (M : Submodule ℤ V) (f : Module.End ℂ V) (g : Module.End K (VK K M)) : Prop :=
  ∃ fm : Module.End ℤ M, (∀ m : M, (fm m : V) = f (m : V)) ∧
    (∀ (c : K) (m : M), g (c ⊗ₜ[ℤ] m) = c ⊗ₜ[ℤ] (fm m))
structure Action (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) where
  onM : LZ x y h →ₗ[ℤ] Module.End ℤ M
  onM_spec : ∀ s : LZ x y h, ∀ m : M, (onM s m : V) = rho (s : L) (m : V)
  bracket_mem : ∀ s t : LZ x y h, ⁅(s : L),(t : L)⁆ ∈ LZ x y h
  red : K ⊗[ℤ] LZ x y h →ₗ[K] Module.End K (VK K M)
  red_spec : ∀ (c d : K) (s : LZ x y h) (m : M),
    red (c ⊗ₜ[ℤ] s) (d ⊗ₜ[ℤ] m) = (c*d) ⊗ₜ[ℤ] onM s m
  red_lie : ∀ s t u : LZ x y h, (u : L) = ⁅(s : L),(t : L)⁆ → ∀ c d : K,
    red ((c*d) ⊗ₜ[ℤ] u) = red (c ⊗ₜ[ℤ] s) * red (d ⊗ₜ[ℤ] t) - red (d ⊗ₜ[ℤ] t) * red (c ⊗ₜ[ℤ] s)
  a : Module.End K (VK K M)
  d : Module.End K (VK K M)
  t : Module.End K (VK K M)
  a_spec : Lift K M (rho x) a
  d_spec : Lift K M (rho y) d
  t_spec : Lift K M (rho h) t
  gen_spec : ∀ (s : LZ x y h),
    ((s : L) = x → red (1 ⊗ₜ[ℤ] s) = a) ∧
    ((s : L) = y → red (1 ⊗ₜ[ℤ] s) = d) ∧
    ((s : L) = h → red (1 ⊗ₜ[ℤ] s) = t)
def N2 (p : ℕ) (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) (v : V) : Prop :=
  LocalRingSpec p ∧ SmallUnits p l ∧ Nonempty (Action K M rho x y h) ∧
  ∃ f : MR p M →ₗ[ℤ] V, IotaSpec p M f ∧ LocalBasis p l M f ∧
    Preserved p M f (rho x) (rho y) ∧
    (∀ b : Module.Basis (I l) ℂ V, BasisSpec l (rho y) v b →
      UnitIdentities l (rho x) (rho y) b ∧ AllUnits p l M f (rho x) (rho y) b)
def CoeffSpec (p : ℕ) (l : ℤ) (d : Module.End ℂ V) (v : V) (M : Submodule ℤ V)
    (f : MR p M →ₗ[ℤ] V) (J : Submodule (R p) (C p)) : Prop :=
  (∀ (i : I l) (c : ℂ), c ∈ J ↔ c • eNat d v i.val ∈ Set.range f) ∧
  J.FG ∧ J ≠ ⊥ ∧
  ∃ D : (I l → J) ≃ₗ[R p] MR p M, ∀ g : I l → J, f (D g) = ∑ i, ((g i : C p) : ℂ) • eNat d v i.val
def MuSpec (p : ℕ) (J : Submodule (R p) (C p)) (mu : ℚ ⊗[R p] J →ₗ[ℚ] ℂ) : Prop :=
  ∀ (q : ℚ) (c : J), mu (q ⊗ₜ[R p] c) = (q : ℂ) * ((c : C p) : ℂ)
def RationalEmbedding (p : ℕ) (J : Submodule (R p) (C p)) : Prop :=
  FiniteDimensional ℚ (ℚ ⊗[R p] J) ∧
  ∃ mu : ℚ ⊗[R p] J →ₗ[ℚ] ℂ, MuSpec p J mu ∧ Function.Injective mu ∧
    LinearMap.range mu = Submodule.span ℚ (J : Set ℂ)
def ScaledBasis (p : ℕ) (l : ℤ) (d : Module.End ℂ V) (v : V) (M : Submodule ℤ V)
    (f : MR p M →ₗ[ℤ] V) (b : ℂ) : Prop :=
  ∃ B : Module.Basis (I l) (R p) (MR p M), ∀ i, f (B i) = b • eNat d v i.val
def CyclicSpec (p : ℕ) (l : ℤ) (d : Module.End ℂ V) (v : V) (M : Submodule ℤ V)
    (f : MR p M →ₗ[ℤ] V) (J : Submodule (R p) (C p)) : Prop :=
  (∃ b : ℂ, b ∈ J ∧ b ≠ 0 ∧ J = Submodule.span (R p) {b}) ∧
  (∀ b : ℂ, b ∈ J → b ≠ 0 → J = Submodule.span (R p) {b} → ScaledBasis p l d v M f b)
def N3 (p : ℕ) (l : ℤ) (d : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  ∀ f : MR p M →ₗ[ℤ] V, IotaSpec p M f →
    ∃ J : Submodule (R p) (C p), CoeffSpec p l d v M f J ∧ RationalEmbedding p J ∧
      Module.finrank ℚ (ℚ ⊗[R p] J) = 1 ∧ CyclicSpec p l d v M f J
def RationalMultiples (p : ℕ) (J : Submodule (R p) (C p)) : Prop :=
  ∀ a : ℂ, a ∈ J → a ≠ 0 → ∀ c : ℂ, c ∈ J → ∃ q : ℚ, c = (q : ℂ) * a
def PDecomposition (p : ℕ) : Prop :=
  ∀ q : ℚ, q ≠ 0 → ∃ (nu : ℤ) (u : (R p)ˣ), q = (p : ℚ)^nu * (u.val : ℚ)
def Target (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) : Prop :=
  Nontrivial (VK K M) ∧
  ∃ A : Action K M rho x y h, ∀ W : Submodule K (VK K M),
    Stable W A.a → Stable W A.d → Stable W A.t → W = ⊥ ∨ W = ⊤
end LR

set_option autoImplicit false
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => LR.N2 p l K M rho x y h v)
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => LR.N3 p l (rho y) v M)
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => LR.Target K M rho x y h)
#check (fun (K : Type) [fieldK : Field K] (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) => LR.PDecomposition p)
