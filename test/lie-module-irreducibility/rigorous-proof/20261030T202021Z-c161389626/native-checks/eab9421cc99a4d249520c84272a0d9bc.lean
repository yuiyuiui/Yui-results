import Mathlib
open scoped TensorProduct
namespace LR
abbrev L := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ
abbrev R (p : ℕ) := Subring.closure {q : ℚ | ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b}
abbrev C (p : ℕ) := RestrictScalars (R p) ℚ ℂ
def cv (p : ℕ) : C p ≃+ ℂ := RestrictScalars.addEquiv (R p) ℚ ℂ
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
  (∀ (i : I l) (c : ℂ), (cv p).symm c ∈ J ↔ c • eNat d v i.val ∈ Set.range f) ∧
  J.FG ∧ J ≠ ⊥ ∧
  ∃ D : (I l → J) ≃ₗ[R p] MR p M, ∀ g : I l → J, f (D g) = ∑ i, cv p (g i : C p) • eNat d v i.val
def MuSpec (p : ℕ) (J : Submodule (R p) (C p)) (mu : ℚ ⊗[R p] J →ₗ[ℚ] ℂ) : Prop :=
  ∀ (q : ℚ) (c : J), mu (q ⊗ₜ[R p] c) = (q : ℂ) * cv p (c : C p)
def RationalEmbedding (p : ℕ) (J : Submodule (R p) (C p)) : Prop :=
  FiniteDimensional ℚ (ℚ ⊗[R p] J) ∧
  ∃ mu : ℚ ⊗[R p] J →ₗ[ℚ] ℂ, MuSpec p J mu ∧ Function.Injective mu ∧
    LinearMap.range mu = Submodule.span ℚ ((cv p) '' (J : Set (C p)))
def ScaledBasis (p : ℕ) (l : ℤ) (d : Module.End ℂ V) (v : V) (M : Submodule ℤ V)
    (f : MR p M →ₗ[ℤ] V) (b : ℂ) : Prop :=
  ∃ B : Module.Basis (I l) (R p) (MR p M), ∀ i, f (B i) = b • eNat d v i.val
def CyclicSpec (p : ℕ) (l : ℤ) (d : Module.End ℂ V) (v : V) (M : Submodule ℤ V)
    (f : MR p M →ₗ[ℤ] V) (J : Submodule (R p) (C p)) : Prop :=
  (∃ b : ℂ, (cv p).symm b ∈ J ∧ b ≠ 0 ∧ J = Submodule.span (R p) {(cv p).symm b}) ∧
  (∀ b : ℂ, (cv p).symm b ∈ J → b ≠ 0 → J = Submodule.span (R p) {(cv p).symm b} → ScaledBasis p l d v M f b)
def N3 (p : ℕ) (l : ℤ) (d : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  ∀ f : MR p M →ₗ[ℤ] V, IotaSpec p M f →
    ∃ J : Submodule (R p) (C p), CoeffSpec p l d v M f J ∧ RationalEmbedding p J ∧
      Module.finrank ℚ (ℚ ⊗[R p] J) = 1 ∧ CyclicSpec p l d v M f J
def RationalMultiples (p : ℕ) (J : Submodule (R p) (C p)) : Prop :=
  ∀ a : ℂ, (cv p).symm a ∈ J → a ≠ 0 → ∀ c : ℂ, (cv p).symm c ∈ J → ∃ q : ℚ, c = (q : ℂ) * a
def PDecomposition (p : ℕ) : Prop :=
  ∀ q : ℚ, q ≠ 0 → ∃ (nu : ℤ) (u : (R p)ˣ), q = (p : ℚ)^nu * (u.val : ℚ)
def Target (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) : Prop :=
  Nontrivial (VK K M) ∧
  ∃ A : Action K M rho x y h, ∀ W : Submodule K (VK K M),
    Stable W A.a → Stable W A.d → Stable W A.t → W = ⊥ ∨ W = ⊤

structure Residue (p : ℕ) (K : Type*) [Field K] where
  phi : R p →+* K
  psi : R p →+* ZMod p
  kappa : ZMod p →+* K
  phi_fraction : ∀ (a b : ℤ) (r : R p), b ≠ 0 → ¬ (p : ℤ) ∣ b →
    (r : ℚ) = (a : ℚ) / b → phi r = (a : K) * (b : K)⁻¹
  psi_fraction : ∀ (a b : ℤ) (r : R p), b ≠ 0 → ¬ (p : ℤ) ∣ b →
    (r : ℚ) = (a : ℚ) / b → psi r = (a : ZMod p) * (b : ZMod p)⁻¹
  kappa_int : ∀ a : ℤ, kappa (a : ZMod p) = (a : K)
  compatible : phi = kappa.comp psi
  psi_surjective : Function.Surjective psi
  psi_kernel : RingHom.ker psi = Ideal.span {(p : R p)}
  eps : (R p) ⧸ Ideal.span {(p : R p)} ≃+* ZMod p
  eps_spec : ∀ r : R p, eps (Ideal.Quotient.mk (Ideal.span {(p : R p)}) r) = psi r
  units_nonzero : ∀ u : (R p)ˣ, phi u.val ≠ 0
def GammaPure (p : ℕ) (K : Type*) [Field K] [Algebra (R p) K] (M : Submodule ℤ V)
    (phi : R p →+* K) (G : VK K M ≃ₗ[K] K ⊗[R p] MR p M) : Prop :=
  (∀ (c : K) (m : M), G (c ⊗ₜ[ℤ] m) = c ⊗ₜ[R p] (1 ⊗ₜ[ℤ] m)) ∧
  (∀ (c : K) (r : R p) (m : M), G.symm (c ⊗ₜ[R p] (r ⊗ₜ[ℤ] m)) = (phi r*c) ⊗ₜ[ℤ] m)
def DeltaPure (p : ℕ) (K : Type*) [Field K] [Algebra (R p) K] [Algebra (ZMod p) K]
    (M : Submodule ℤ V) (D : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p)) : Prop :=
  (∀ (c : K) (z : MR p M), D (c ⊗ₜ[R p] z) = c ⊗ₜ[ZMod p] ModN.mkQ p z) ∧
  (∀ (c : K) (z : MR p M), D.symm (c ⊗ₜ[ZMod p] ModN.mkQ p z) = c ⊗ₜ[R p] z)
def Bridge (p : ℕ) (K : Type*) [Field K] (M : Submodule ℤ V) (Q : Residue p K) : Prop :=
  letI := Q.phi.toAlgebra
  letI := Q.kappa.toAlgebra
  ∃ (G : VK K M ≃ₗ[K] K ⊗[R p] MR p M)
    (D : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] ModN (MR p M) p)),
    GammaPure p K M Q.phi G ∧ DeltaPure p K M D ∧
    (∀ (F : Module.End ℤ M) (z : VK K M),
      G (F.baseChange K z) = ((F.baseChange (R p)).baseChange K) (G z)) ∧
    (∀ F : Module.End (R p) (MR p M),
      ∃ Fb : Module.End (ZMod p) (ModN (MR p M) p),
        (∀ z : MR p M, Fb (ModN.mkQ p z) = ModN.mkQ p (F z)) ∧
        (∀ z : K ⊗[R p] MR p M, D (F.baseChange K z) = Fb.baseChange K (D z)))
noncomputable def extend {F A : Type*} [Field F] [AddCommGroup A] [Module F A] (l : ℤ)
    (b : Module.Basis (I l) F A) (k : ℕ) : A :=
  if hk : k < l.toNat+1 then b ⟨k,hk⟩ else 0
def polynomial {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
    (l : ℤ) (a d : Module.End F A) (i j : I l) : Module.End F A :=
  (Nat.choose l.toNat j.val : F)⁻¹ •
    (((((l.toNat-i.val).factorial : F)⁻¹) • a^(l.toNat-i.val)) *
    (((l.toNat.factorial : F)⁻¹) • d^l.toNat) *
    (((l.toNat.factorial : F)⁻¹) • a^l.toNat) *
    (((((l.toNat-j.val).factorial : F)⁻¹) • d^(l.toNat-j.val))))
def ReducedBasisSpec (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) (A : Action K M rho x y h)
    (beta : Module.Basis (I l) K (VK K M)) : Prop :=
  Module.finrank K (VK K M) = l.toNat+1 ∧
  Matrices l A.a A.d A.t (extend l beta) ∧
  (∀ r : ℕ, r ≤ l.toNat →
    (r.factorial : K) ≠ 0 ∧
    Lift K M (dp (rho x) r) (((r.factorial : K)⁻¹) • A.a^r) ∧
    Lift K M (dp (rho y) r) (((r.factorial : K)⁻¹) • A.d^r)) ∧
  (∀ i j : I l, (Nat.choose l.toNat j.val : K) ≠ 0 ∧
    ∀ k : I l, polynomial l A.a A.d i j (beta k) = if k = j then beta i else 0)
def Transfer (p : ℕ) (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (d : Module.End ℂ V) (v : V) (Q : Residue p K) : Prop :=
  letI := Q.phi.toAlgebra
  ∀ (f : MR p M →ₗ[ℤ] V) (b : ℂ), IotaSpec p M f → ScaledBasis p l d v M f b →
    ∃ (G : VK K M ≃ₗ[K] K ⊗[R p] MR p M)
      (B : Module.Basis (I l) (R p) (MR p M)) (beta : Module.Basis (I l) K (VK K M)),
      GammaPure p K M Q.phi G ∧
      (∀ i, f (B i) = b • eNat d v i.val) ∧
      (∀ i, beta i = G.symm (1 ⊗ₜ[R p] B i)) ∧
      Module.finrank K (VK K M) = l.toNat+1
def ReducedPackage (p : ℕ) (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) (v : V) (Q : Residue p K) : Prop :=
  letI := Q.phi.toAlgebra
  ∀ A : Action K M rho x y h,
    ∃ (f : MR p M →ₗ[ℤ] V) (J : Submodule (R p) (C p)) (b : ℂ)
      (G : VK K M ≃ₗ[K] K ⊗[R p] MR p M)
      (B : Module.Basis (I l) (R p) (MR p M)) (beta : Module.Basis (I l) K (VK K M)),
      IotaSpec p M f ∧ Function.Injective f ∧ CoeffSpec p l (rho y) v M f J ∧
      (cv p).symm b ∈ J ∧ b ≠ 0 ∧ J = Submodule.span (R p) {(cv p).symm b} ∧
      GammaPure p K M Q.phi G ∧
      (∀ i, f (B i) = b • eNat (rho y) v i.val) ∧
      (∀ i, beta i = G.symm (1 ⊗ₜ[R p] B i)) ∧
      ReducedBasisSpec l K M rho x y h A beta
def N4 (p : ℕ) (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) (v : V) : Prop :=
  ∃ Q : Residue p K, Bridge p K M Q ∧ ReducedPackage p l K M rho x y h v Q

def DividedLiftMatrices (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (a d : Module.End ℂ V) (beta : Module.Basis (I l) K (VK K M)) : Prop :=
  ∀ r : ℕ, ∃ xr yr : Module.End K (VK K M), Lift K M (dp a r) xr ∧ Lift K M (dp d r) yr ∧
    ∀ i : I l,
      xr (beta i) = (if r ≤ i.val then (Nat.choose (l.toNat-i.val+r) r : K) • extend l beta (i.val-r) else 0) ∧
      yr (beta i) = (if i.val+r ≤ l.toNat then (Nat.choose (i.val+r) r : K) • extend l beta (i.val+r) else 0)
def MatrixTransport (p : ℕ) (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) (v : V) (Q : Residue p K) : Prop :=
  letI := Q.phi.toAlgebra
  ∀ (A : Action K M rho x y h) (f : MR p M →ₗ[ℤ] V) (b : ℂ)
    (G : VK K M ≃ₗ[K] K ⊗[R p] MR p M)
    (B : Module.Basis (I l) (R p) (MR p M)) (beta : Module.Basis (I l) K (VK K M)),
    IotaSpec p M f → Function.Injective f → b ≠ 0 → GammaPure p K M Q.phi G →
    (∀ i, f (B i) = b • eNat (rho y) v i.val) →
    (∀ i, beta i = G.symm (1 ⊗ₜ[R p] B i)) →
    Matrices l A.a A.d A.t (extend l beta) ∧ DividedLiftMatrices l K M (rho x) (rho y) beta
def SmallPowers (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) : Prop :=
  ∀ (A : Action K M rho x y h) (r : ℕ), r ≤ l.toNat →
    (r.factorial : K) ≠ 0 ∧ Lift K M (dp (rho x) r) (((r.factorial : K)⁻¹) • A.a^r) ∧
    Lift K M (dp (rho y) r) (((r.factorial : K)⁻¹) • A.d^r)
def PolynomialTransport (p : ℕ) (l : ℤ) (K : Type*) [Field K] (M : Submodule ℤ V)
    (rho : L →ₗ[ℂ] Module.End ℂ V) (x y h : L) (v : V) (Q : Residue p K) : Prop :=
  letI := Q.phi.toAlgebra
  ∀ (A : Action K M rho x y h) (f : MR p M →ₗ[ℤ] V) (b : ℂ)
    (G : VK K M ≃ₗ[K] K ⊗[R p] MR p M)
    (B : Module.Basis (I l) (R p) (MR p M)) (beta : Module.Basis (I l) K (VK K M)),
    IotaSpec p M f → Function.Injective f → b ≠ 0 → GammaPure p K M Q.phi G →
    (∀ i, f (B i) = b • eNat (rho y) v i.val) →
    (∀ i, beta i = G.symm (1 ⊗ₜ[R p] B i)) →
    ∀ i j : I l, (Nat.choose l.toNat j.val : K) ≠ 0 ∧
      ∀ k : I l, polynomial l A.a A.d i j (beta k) = if k = j then beta i else 0
end LR

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) (h_T010 : LR.N2 p l K M rho x y h v) (h_T022 : ∀ Q : LR.Residue p K, LR.MatrixTransport p l K M rho x y h v Q) (h_T023 : LR.SmallPowers l K M rho x y h) : yui_aux_type% "∀ (Q : LR.Residue p K), letI := Q.phi.toAlgebra\n  ∀ (f : LR.MR p M →ₗ[ℤ] V)\n    (G : LR.VK K M ≃ₗ[K] K ⊗[LR.R p] LR.MR p M),\n    LR.IotaSpec p M f → LR.GammaPure p K M Q.phi G →\n    ∀ (s : Module.End ℂ V) (u : Module.End K (LR.VK K M)), LR.Lift K M s u →\n    ∃ F : Module.End (LR.R p) (LR.MR p M),\n      (∀ z, f (F z) = s (f z)) ∧\n      (∀ z, u (G.symm (1 ⊗ₜ[LR.R p] z)) =\n        G.symm (1 ⊗ₜ[LR.R p] F z))" := by
  intro Q
  letI := Q.phi.toAlgebra
  intro f G hf hG s u hu
  rcases hu with ⟨fm, hm, hu⟩
  refine ⟨fm.baseChange (LR.R p), ?_, ?_⟩
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [LinearMap.baseChange_tmul, hf.1, hm, map_smul]
    | add z w hz hw => simp only [map_add, hz, hw]
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [LinearMap.baseChange_tmul, hG.2, hG.2, hu]
    | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
#check @checked
#print axioms checked
end YuiAuxiliary
