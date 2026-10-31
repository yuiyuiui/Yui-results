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

namespace Translation
set_option autoImplicit false

theorem T001 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : LR.ComplexHyp l rho x y h) (h_H003 : v ≠ 0 ∧ rho x v = 0 ∧ rho h v = (l : ℂ) • v) :
    LR.Strings l (rho x) (rho y) (rho h) v := by
  have hcomm : ∀ w : V, rho h (rho y w) = rho y (rho h w) - (2 : ℂ) • rho y w := by
    intro w
    have hc := congrArg (fun F : Module.End ℂ V => F w) (h_H002.2.2.1 h y)
    rw [h_H002.1.lie_h_f_nsmul] at hc
    have hc' : -(rho y w + rho y w) = rho h (rho y w) - rho y (rho h w) := by simpa [two_smul, Module.End.mul_apply] using hc
    rw [show (2 : ℂ) • rho y w = rho y w + rho y w by simp [two_smul]]
    calc
      rho h (rho y w) = (rho h (rho y w) - rho y (rho h w)) + rho y (rho h w) := by abel
      _ = -(rho y w + rho y w) + rho y (rho h w) := by rw [← hc']
      _ = _ := by abel
  have xcomm : ∀ w : V, rho x (rho y w) = rho y (rho x w) + rho h w := by
    intro w
    have hc := congrArg (fun F : Module.End ℂ V => F w) (h_H002.2.2.1 x y)
    rw [h_H002.1.lie_e_f] at hc
    have hc' : rho h w = rho x (rho y w) - rho y (rho x w) := by simpa [Module.End.mul_apply] using hc
    rw [hc']
    abel
  have yp (n : ℕ) : (rho y ^ (n+1)) v = rho y ((rho y ^ n) v) := by
    rw [pow_succ', Module.End.mul_apply]
  have hs : ∀ n : ℕ,
      rho h ((rho y ^ n) v) = ((l : ℂ) - 2 * (n : ℂ)) • (rho y ^ n) v ∧
      rho x ((rho y ^ n) v) = ((n : ℂ) * ((l : ℂ) - (n : ℂ) + 1)) • (rho y ^ (n-1)) v := by
    intro n
    induction n with
    | zero => simpa using And.intro h_H003.2.2 h_H003.2.1
    | succ n ih =>
      constructor
      · rw [yp, hcomm, ih.1, map_smul, ← sub_smul]
        rw [← yp]
        congr 1
        push_cast
        ring
      · rw [yp, xcomm, ih.1]
        cases n with
        | zero => simp [h_H003.2.1]
        | succ k =>
          rw [ih.2, map_smul]
          simp only [Nat.succ_sub_one]
          rw [← yp, ← add_smul]
          congr 1
          push_cast
          ring
  exact ⟨fun n => (hs n).1, fun n _ => (hs n).2⟩

theorem T002 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : v ≠ 0 ∧ rho x v = 0 ∧ rho h v = (l : ℂ) • v) (h_T001 : LR.Strings l (rho x) (rho y) (rho h) v) :
    (∀ i : LR.I l, LR.eNat (rho y) v i.val ≠ 0) ∧ LinearIndependent ℂ (fun i : LR.I l => LR.eNat (rho y) v i.val) := by
  classical
  have hraw : ∀ r : ℕ, r ≤ l.toNat → ((rho y)^r) v ≠ 0 := by
    intro r hr
    induction r with
    | zero => simpa using h_H003.1
    | succ r ih =>
      have hrle : r ≤ l.toNat := by omega
      have hv := ih hrle
      have hrint : (r : ℤ) < l := by
        have he : (l.toNat : ℤ) = l := Int.toNat_of_nonneg h_H001.2.2.1
        omega
      have hpos : (l : ℂ) - (r : ℂ) ≠ 0 := by
        have hz : l - (r : ℤ) ≠ 0 := by omega
        exact_mod_cast hz
      have hc : ((r+1 : ℕ) : ℂ) * ((l : ℂ) - ((r+1 : ℕ) : ℂ) + 1) ≠ 0 := by
        have hn : ((r+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero r)
        apply mul_ne_zero hn
        convert hpos using 1 <;> push_cast <;> ring
      intro hz
      have hx := h_T001.2 (r+1) (by omega)
      rw [hz, map_zero] at hx
      have hs : (((r+1 : ℕ) : ℂ) * ((l : ℂ) - ((r+1 : ℕ) : ℂ) + 1)) •
          ((rho y)^r) v = 0 := by simpa using hx.symm
      exact (smul_ne_zero hc hv) hs
  have hconv : (∀ i : LR.I l, LR.eNat (rho y) v i.val ≠ 0) ∧
      (∀ i : LR.I l, rho h (LR.eNat (rho y) v i.val) =
        ((l : ℂ) - 2 * (i.val : ℂ)) • LR.eNat (rho y) v i.val) := by
    have hn := hraw
    constructor
    · intro i
      have hraw : ((rho y)^i.val) v ≠ 0 := hn i.val (by have := i.isLt; omega)
      have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i.val)
      simpa only [LR.eNat, LR.dp, LinearMap.smul_apply] using smul_ne_zero (inv_ne_zero hf) hraw
    · intro i
      dsimp [LR.eNat, LR.dp]
      rw [map_smul, h_T001.1 i.val]
      exact smul_comm _ _ _
  refine ⟨hconv.1, ?_⟩
  let e : LR.I l → V := fun i => LR.eNat (rho y) v i.val
  have hn : ∀ i, e i ≠ 0 := hconv.1
  have he : ∀ i, rho h (e i) = ((l : ℂ) - 2 * (i.val : ℂ)) • e i := hconv.2
  change LinearIndependent ℂ e
  let w : LR.I l → ℂ := fun i => (l : ℂ) - 2 * (i.val : ℂ)
  have hw : Function.Injective w := by
    intro i j hij
    apply Fin.ext
    have heq : (i.val : ℂ) = (j.val : ℂ) := by dsimp [w] at hij; linear_combination (-1/2 : ℂ) * hij
    exact_mod_cast heq
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let P : Polynomial ℂ := ∏ k ∈ (Finset.univ.erase j), (Polynomial.X - Polynomial.C (w k))
  have hp : ∀ i : LR.I l, P.eval (w i) = ∏ k ∈ (Finset.univ.erase j), (w i - w k) := by
    intro i
    simp [P, Polynomial.eval_prod]
  have hz : ∀ i : LR.I l, i ≠ j → P.eval (w i) = 0 := by
    intro i hij
    rw [hp]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) (sub_self (w i))
  have hnj : P.eval (w j) ≠ 0 := by
    rw [hp]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hk).1 (hw heq).symm
  have happ : ∀ i : LR.I l,
      (Polynomial.aeval (rho h) P) (e i) = P.eval (w i) • e i := by
    intro i
    exact Module.End.aeval_apply_of_mem_apply_eq_smul (he i)
  have ht := congrArg (fun z : V => (Polynomial.aeval (rho h) P) z) hc
  simp only [map_sum, map_smul, map_zero, happ] at ht
  have hsum : (∑ i : LR.I l, c i • (P.eval (w i) • e i)) =
      c j • (P.eval (w j) • e j) := by
    apply Finset.sum_eq_single j
    · intro i hi hij
      rw [hz i hij]
      simp
    · simp
  rw [hsum] at ht
  exact (smul_eq_zero.mp ht).resolve_right (smul_ne_zero hnj (hn j))

theorem T003 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : LR.ComplexHyp l rho x y h) (h_T001 : LR.Strings l (rho x) (rho y) (rho h) v) (h_T002 : (∀ i : LR.I l, LR.eNat (rho y) v i.val ≠ 0) ∧ LinearIndependent ℂ (fun i : LR.I l => LR.eNat (rho y) v i.val)) :
    LR.BasisString l (rho y) v := by
  classical
  letI : FiniteDimensional ℂ V := h_H002.2.2.2.1
  have hc : Fintype.card (LR.I l) = Module.finrank ℂ V := by
    simpa [LR.I] using h_H002.2.2.2.2.1.symm
  let b := basisOfLinearIndependentOfCardEqFinrank h_T002.2 hc
  have hb : ∀ i, b i = LR.eNat (rho y) v i.val := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank h_T002.2 hc) i
  have ht : ∀ i : LR.I l, rho h (b i) = ((l : ℂ) - 2 * (i.val : ℂ)) • b i := by
    intro i
    rw [hb]
    unfold LR.eNat LR.dp
    simp only [LinearMap.smul_apply, map_smul, h_T001.1]
    rw [smul_smul, smul_smul, mul_comm]
  have hcoord : ∀ z i, b.repr (rho h z) i =
      ((l : ℂ) - 2 * (i.val : ℂ)) * b.repr z i := by
    intro z i
    have hh := congrArg (fun z => b.coord i (rho h z)) (b.sum_repr z)
    simp only [map_sum, map_smul, ht] at hh
    simpa [Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      Finsupp.single_apply, mul_comm, mul_left_comm, mul_assoc] using hh.symm
  have hz : ((rho y) ^ (l.toNat + 1)) v = 0 := by
    apply b.ext_elem
    intro i
    have he := congrArg (fun z => b.coord i z) (h_T001.1 (l.toNat + 1))
    simp only [map_smul, Module.Basis.coord_apply, smul_eq_mul] at he
    rw [hcoord] at he
    have hne : ((l : ℂ) - 2 * (i.val : ℂ)) ≠
        ((l : ℂ) - 2 * ((l.toNat+1 : ℕ) : ℂ)) := by
      intro hEq
      have hi : i.val < l.toNat + 1 := i.isLt
      have heq : (i.val : ℂ) = ((l.toNat + 1 : ℕ) : ℂ) := by
        linear_combination (-1 / 2 : ℂ) * hEq
      have hn : i.val = l.toNat + 1 := by exact_mod_cast heq
      omega
    have he0 : (((l : ℂ) - 2 * (i.val : ℂ)) -
        ((l : ℂ) - 2 * ((l.toNat+1 : ℕ) : ℂ))) *
        b.repr (((rho y) ^ (l.toNat + 1)) v) i = 0 := by
      linear_combination he
    simpa using (mul_eq_zero.mp he0).resolve_left (sub_ne_zero.mpr hne)
  refine ⟨b, hb, ?_⟩
  intro r hr
  have hn : l.toNat + 1 ≤ r := by omega
  rw [← Nat.sub_add_cancel hn, pow_add, Module.End.mul_apply, hz, map_zero]

theorem T004 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H003 : v ≠ 0 ∧ rho x v = 0 ∧ rho h v = (l : ℂ) • v) (h_T001 : LR.Strings l (rho x) (rho y) (rho h) v) (h_T003 : LR.BasisString l (rho y) v) :
    LR.Matrices l (rho x) (rho y) (rho h) (LR.eNat (rho y) v) := by
  have hf : ∀ n : ℕ, (n.factorial : ℂ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  have hstep : ∀ n : ℕ, ((n.factorial : ℂ)⁻¹) =
      ((n : ℂ) + 1) * (((n+1).factorial : ℂ)⁻¹) := by
    intro n
    have hn := hf n
    have hs : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have hy : ∀ n : ℕ, rho y (LR.eNat (rho y) v n) =
      ((n : ℂ)+1) • LR.eNat (rho y) v (n+1) := by
    intro n
    simp only [LR.eNat, LR.dp, LinearMap.smul_apply, map_smul]
    rw [pow_succ', Module.End.mul_apply, smul_smul, hstep]
  rcases h_T001 with ⟨ht, ha⟩
  rcases h_T003 with ⟨b, hb, hz⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [LR.eNat, LR.dp] using h_H003.2.1
  · intro i hi hil
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hx := ha (n+1) (by omega)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hx ⊢
    simp only [LR.eNat, LR.dp, LinearMap.smul_apply, map_smul]
    rw [hx, smul_smul, smul_smul]
    congr 1
    have hn := hf n
    have hs : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  · intro i hi
    exact hy i
  · rw [hy]
    simp only [LR.eNat, LR.dp, LinearMap.smul_apply]
    rw [hz (l.toNat+1) (by omega), smul_zero, smul_zero]
  · intro i hi
    simp only [LR.eNat, LR.dp, LinearMap.smul_apply, map_smul]
    rw [ht i, smul_smul, smul_smul, mul_comm]

theorem T005 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T001 : LR.Strings l (rho x) (rho y) (rho h) v) (h_T003 : LR.BasisString l (rho y) v) (h_T004 : LR.Matrices l (rho x) (rho y) (rho h) (LR.eNat (rho y) v)) :
    LR.N1 l (rho x) (rho y) (rho h) v := by
   have hxp : ∀ r i : ℕ, i ≤ l.toNat →
  ((rho x)^r) (LR.eNat (rho y) v i) =
  if r ≤ i then (((l.toNat-i+1).ascFactorial r : ℕ) : ℂ) • LR.eNat (rho y) v (i-r) else 0 := by
     have hl : (l.toNat : ℂ) = (l : ℂ) := by
       exact_mod_cast Int.toNat_of_nonneg h_H001.2.2.1
     rcases h_T004 with ⟨hx0, hx, hy, hy0, ht⟩
     intro r
     induction r with
     | zero => intro i hi; simp
     | succ r ih =>
       intro i hi
       rw [pow_succ', Module.End.mul_apply, ih i hi]
       by_cases hr : r ≤ i
       · rw [if_pos hr, map_smul]
         by_cases hrs : r+1 ≤ i
         · rw [if_pos hrs, hx (i-r) (by omega) (by omega)]
           have hind : i-r-1 = i-(r+1) := by omega
           rw [hind, smul_smul, Nat.ascFactorial_succ, Nat.cast_mul]
           congr 1
           have hc : (l : ℂ) - ((i-r : ℕ) : ℂ) + 1 =
               ((l.toNat-i+1+r : ℕ) : ℂ) := by
             rw [Nat.cast_sub hr, Nat.cast_add, Nat.cast_add, Nat.cast_sub hi, hl]
             push_cast
             ring
           rw [hc]
           ring
         · have hir : i-r = 0 := by omega
           rw [if_neg (by omega), hir, hx0, smul_zero]
       · rw [if_neg hr, map_zero, if_neg (by omega)]

   have hyp : ∀ r i : ℕ, i ≤ l.toNat →
  ((rho y)^r) (LR.eNat (rho y) v i) =
  if i+r ≤ l.toNat then (((i+1).ascFactorial r : ℕ) : ℂ) • LR.eNat (rho y) v (i+r) else 0 := by
     rcases h_T004 with ⟨hx0, hx, hy, hy0, ht⟩
     intro r
     induction r with
     | zero => intro i hi; simp [hi]
     | succ r ih =>
       intro i hi
       rw [pow_succ', Module.End.mul_apply, ih i hi]
       by_cases hr : i+r ≤ l.toNat
       · rw [if_pos hr, map_smul]
         by_cases hrs : i+(r+1) ≤ l.toNat
         · rw [if_pos hrs, hy (i+r) (by omega), smul_smul,
               Nat.ascFactorial_succ, Nat.cast_mul]
           have hind : i+r+1 = i+(r+1) := by omega
           rw [hind]
           congr 1
           push_cast
           ring
         · have hir : i+r = l.toNat := by omega
           rw [if_neg hrs, hir, hy0, smul_zero]
       · rw [if_neg hr, map_zero, if_neg (by omega)]

   have hcoeff : ∀ n r : ℕ, (r.factorial : ℂ)⁻¹ * (((n+1).ascFactorial r : ℕ) : ℂ) = (Nat.choose (n+r) r : ℂ) := by
     intro n r
     have hf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
     rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
       inv_mul_cancel₀ hf, one_mul]

   refine ⟨by omega, ?_, h_T001, h_T003, h_T004, ?_⟩
   · simp only [LR.I, Fintype.card_fin]
     omega
   · intro r i hi
     constructor
     · change (r.factorial : ℂ)⁻¹ • ((rho x)^r) (LR.eNat (rho y) v i) = _
       rw [hxp r i hi]
       by_cases hr : r ≤ i
       · rw [if_pos hr, if_pos hr, smul_smul, hcoeff (l.toNat-i) r]
       · rw [if_neg hr, if_neg hr, smul_zero]
     · change (r.factorial : ℂ)⁻¹ • ((rho y)^r) (LR.eNat (rho y) v i) = _
       rw [hyp r i hi]
       by_cases hr : i+r ≤ l.toNat
       · rw [if_pos hr, if_pos hr, smul_smul, hcoeff i r]
       · rw [if_neg hr, if_neg hr, smul_zero]

theorem T006 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : LR.ComplexHyp l rho x y h) (h_H004 : LR.Admissible rho x y M) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) :
    LR.LocalRingSpec p ∧ ∃ (m : Module.Basis (LR.I l) ℤ M) (bc : Module.Basis (LR.I l) ℂ V), ∀ i, (m i : V) = bc i := by
  constructor
  · classical
    have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using h_H001.1)
    have hOne : ¬ (p : ℤ) ∣ 1 := hp.not_dvd_one
    have hmul : ∀ b d : ℤ, ¬ (p : ℤ) ∣ b → ¬ (p : ℤ) ∣ d → ¬ (p : ℤ) ∣ b*d := by
      intro b d hb hd hbd
      exact (Int.Prime.dvd_mul' h_H001.1 hbd).elim hb hd
    let S : Subring ℚ :=
      { carrier := {q : ℚ | ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b}
        zero_mem' := by exact ⟨0, 1, one_ne_zero, hOne, by norm_num⟩
        one_mem' := by exact ⟨1, 1, one_ne_zero, hOne, by norm_num⟩
        add_mem' := by
          rintro q r ⟨a, b, hb, hpb, rfl⟩ ⟨c, d, hd, hpd, rfl⟩
          refine ⟨a*d+c*b, b*d, mul_ne_zero hb hd, hmul b d hpb hpd, ?_⟩
          push_cast
          have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
          have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
          simpa only [mul_comm (b : ℚ) (c : ℚ)] using div_add_div (a : ℚ) (c : ℚ) hbq hdq
        neg_mem' := by
          rintro q ⟨a, b, hb, hpb, rfl⟩
          exact ⟨-a, b, hb, hpb, by push_cast; ring⟩
        mul_mem' := by
          rintro q r ⟨a, b, hb, hpb, rfl⟩ ⟨c, d, hd, hpd, rfl⟩
          refine ⟨a*c, b*d, mul_ne_zero hb hd, hmul b d hpb hpd, ?_⟩
          push_cast
          exact div_mul_div_comm _ _ _ _ }
    have hRS : LR.R p = S := by
      apply le_antisymm
      · exact Subring.closure_le.mpr (fun q hq => hq)
      · intro q hq
        exact Subring.subset_closure hq
    have hmem : ∀ q : ℚ, q ∈ LR.R p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / b := by
      intro q
      rw [hRS]
      rfl
    refine ⟨hmem, ?_⟩
    intro b hpb
    have hb : b ≠ 0 := by
      intro h
      apply hpb
      simp [h]
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    let c : LR.R p := ⟨1 / (b : ℚ), (hmem _).mpr ⟨1, b, hb, hpb, by norm_num⟩⟩
    refine ⟨⟨(b : LR.R p), c, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (b : ℚ) * (1 / (b : ℚ)) = 1
      field_simp
    · apply Subtype.ext
      change (1 / (b : ℚ)) * (b : ℚ) = 1
      field_simp

  · classical
    letI : FiniteDimensional ℂ V := h_H002.2.2.2.1
    rcases h_H004.1 with ⟨ι, m, bc, hmb⟩
    letI : Finite ι := Module.Finite.finite_basis bc
    letI : Fintype ι := Fintype.ofFinite ι
    have hc : Fintype.card ι = Fintype.card (LR.I l) := by
      rw [← Module.finrank_eq_card_basis bc, h_H002.2.2.2.2.1]
      simp [LR.I]
    obtain ⟨e⟩ := Fintype.card_eq.mp hc
    refine ⟨m.reindex e, bc.reindex e, ?_⟩
    intro i
    simpa only [Module.Basis.reindex_apply] using hmb (e.symm i)

theorem T007 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H002 : LR.ComplexHyp l rho x y h) (h_H004 : LR.Admissible rho x y M) (h_T006 : LR.LocalRingSpec p ∧ ∃ (m : Module.Basis (LR.I l) ℤ M) (bc : Module.Basis (LR.I l) ℂ V), ∀ i, (m i : V) = bc i) :
    Nonempty (LR.Action K M rho x y h) ∧ ∃ f : LR.MR p M →ₗ[ℤ] V, LR.IotaSpec p M f ∧ LR.LocalBasis p l M f ∧ LR.Preserved p M f (rho x) (rho y) := by
  classical
    constructor
    ·
      have ht := h_H002.1
      have hr := h_H002.2.2.1
      have hxy : ∀ m : V, m ∈ M → rho x m ∈ M ∧ rho y m ∈ M := by
        as_aux_lemma =>
          intro m hm
          simpa [LR.dp] using h_H004.2 1 m hm
      have hh : ∀ m : V, m ∈ M → rho h m ∈ M := by
        as_aux_lemma =>
          intro m hm
          rw [← ht.lie_e_f, hr]
          exact M.sub_mem (hxy _ (hxy m hm).2).1 (hxy _ (hxy m hm).1).2
      have hs : ∀ s ∈ LR.LZ x y h, ∀ m : V, m ∈ M → rho s m ∈ M := by
        as_aux_lemma =>
          intro s hs
          induction hs using Submodule.span_induction with
          | mem s hs =>
            rcases Set.mem_insert_iff.mp hs with rfl | hs
            · exact fun m hm => (hxy m hm).1
            rcases Set.mem_insert_iff.mp hs with rfl | hs
            · exact fun m hm => (hxy m hm).2
            have : s = h := Set.mem_singleton_iff.mp hs
            subst s
            exact hh
          | zero => simp
          | add s t _ _ ihs iht =>
            intro m hm
            simpa using M.add_mem (ihs m hm) (iht m hm)
          | smul n s _ ih =>
            intro m hm
            simpa using M.smul_mem n (ih m hm)
      have hxmem : x ∈ LR.LZ x y h := Submodule.subset_span (by simp)
      have hymem : y ∈ LR.LZ x y h := Submodule.subset_span (by simp)
      have hhmem : h ∈ LR.LZ x y h := Submodule.subset_span (by simp)
      have hb : ∀ s t : LR.LZ x y h, ⁅(s : LR.L), (t : LR.L)⁆ ∈ LR.LZ x y h := by
        as_aux_lemma =>
          intro s t
          refine Submodule.span_induction₂ (p := fun a b _ _ => ⁅a,b⁆ ∈ LR.LZ x y h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ s.property t.property
          · intro a b ha hb
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
            rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb]
            · simpa using (LR.LZ x y h).zero_mem
            · simpa [ht.lie_e_f] using hhmem
            · rw [← lie_skew x h, ht.lie_h_e_nsmul]
              simpa [two_smul] using (LR.LZ x y h).neg_mem ((LR.LZ x y h).add_mem hxmem hxmem)
            · rw [← lie_skew y x, ht.lie_e_f]
              exact (LR.LZ x y h).neg_mem hhmem
            · simpa using (LR.LZ x y h).zero_mem
            · rw [← lie_skew y h, ht.lie_h_f_nsmul, neg_neg]
              simpa [two_smul] using (LR.LZ x y h).add_mem hymem hymem
            · rw [ht.lie_h_e_nsmul]
              simpa [two_smul] using (LR.LZ x y h).add_mem hxmem hxmem
            · rw [ht.lie_h_f_nsmul]
              simpa [two_smul] using (LR.LZ x y h).neg_mem ((LR.LZ x y h).add_mem hymem hymem)
            · simpa using (LR.LZ x y h).zero_mem
          · intro b hb; simpa using (LR.LZ x y h).zero_mem
          · intro a ha; simpa using (LR.LZ x y h).zero_mem
          · intro a b c ha hb hc ih₁ ih₂
            simpa [add_lie] using (LR.LZ x y h).add_mem ih₁ ih₂
          · intro a b c ha hb hc ih₁ ih₂
            simpa [lie_add] using (LR.LZ x y h).add_mem ih₁ ih₂
          · intro n a b ha hb ih
            simpa using (LR.LZ x y h).smul_mem n ih
          · intro n a b ha hb ih
            simpa using (LR.LZ x y h).smul_mem n ih
      let onM : LR.LZ x y h →ₗ[ℤ] Module.End ℤ M :=
        { toFun := fun s => ((rho (s : LR.L)).restrictScalars ℤ).restrict (hs s s.property)
          map_add' := by intros; apply LinearMap.ext; intro m; apply Subtype.ext; simp
          map_smul' := by intros; apply LinearMap.ext; intro m; apply Subtype.ext; simp }
      have onM_spec : ∀ (s : LR.LZ x y h) (m : M), (onM s m : V) = rho (s : LR.L) (m : V) := by
        dsimp only [onM]
        as_aux_lemma =>
          intros; rfl
      let red : K ⊗[ℤ] LR.LZ x y h →ₗ[K] Module.End K (LR.VK K M) :=
        ((LinearMap.baseChangeHom ℤ K M M).comp onM).liftBaseChange K
      have redspec : ∀ (c d : K) (s : LR.LZ x y h) (m : M),
          red (c ⊗ₜ[ℤ] s) (d ⊗ₜ[ℤ] m) = (c*d) ⊗ₜ[ℤ] onM s m := by
        as_aux_lemma =>
          intros; simp [red, TensorProduct.smul_tmul']
      have rlie : ∀ s t u : LR.LZ x y h, (u : LR.L) = ⁅(s : LR.L), (t : LR.L)⁆ → ∀ c d : K,
          red ((c*d) ⊗ₜ[ℤ] u) = red (c ⊗ₜ[ℤ] s) * red (d ⊗ₜ[ℤ] t) -
            red (d ⊗ₜ[ℤ] t) * red (c ⊗ₜ[ℤ] s) := by
        as_aux_lemma =>
          intro s t u hu c d
          have he : onM u = onM s * onM t - onM t * onM s := by
            as_aux_lemma =>
              apply LinearMap.ext
              intro m
              apply Subtype.ext
              simp only [onM_spec, Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub]
              rw [hu, hr]
              rfl
          apply TensorProduct.AlgebraTensorModule.ext
          intro e m
          simp only [Module.End.mul_apply, LinearMap.sub_apply, redspec]
          rw [he]
          simp [TensorProduct.tmul_sub, mul_assoc, mul_left_comm]
      let sx : LR.LZ x y h := ⟨x, hxmem⟩
      let sy : LR.LZ x y h := ⟨y, hymem⟩
      let sh : LR.LZ x y h := ⟨h, hhmem⟩
      refine ⟨{
        onM := onM, onM_spec := onM_spec, bracket_mem := hb,
        red := red, red_spec := redspec, red_lie := rlie,
        a := (onM sx).baseChange K, d := (onM sy).baseChange K, t := (onM sh).baseChange K,
        a_spec := ?_, d_spec := ?_, t_spec := ?_, gen_spec := ?_ }⟩
      · exact ⟨onM sx, fun m => rfl, fun c m => rfl⟩
      · exact ⟨onM sy, fun m => rfl, fun c m => rfl⟩
      · exact ⟨onM sh, fun m => rfl, fun c m => rfl⟩
      · intro s
        refine ⟨?_, ?_, ?_⟩
        · intro he
          have hes : s = sx := Subtype.ext he
          rw [hes]
          simp [red]
        · intro he
          have hes : s = sy := Subtype.ext he
          rw [hes]
          simp [red]
        · intro he
          have hes : s = sh := Subtype.ext he
          rw [hes]
          simp [red]
    ·
      let j : LR.R p →+* ℂ := (Rat.castHom ℂ).comp (LR.R p).subtype
      have jval (r : LR.R p) : j r = (((r : ℚ) : ℂ)) := rfl
      let bil : LR.R p →ₗ[ℤ] M →ₗ[ℤ] V :=
        { toFun := fun r => (j r) • M.subtype
          map_add' := by
            as_aux_lemma =>
              intro r s
              apply LinearMap.ext
              intro m
              simp [add_smul]
          map_smul' := by
            as_aux_lemma =>
              intro n r
              apply LinearMap.ext
              intro m
              simp [mul_smul, Int.cast_smul_eq_zsmul] }
      let f : LR.MR p M →ₗ[ℤ] V := TensorProduct.lift bil
      have fpure (r : LR.R p) (m : M) : f (r ⊗ₜ[ℤ] m) = j r • (m : V) := rfl
      have fsmul (r : LR.R p) (z : LR.MR p M) : f (r • z) = j r • f z := by
        as_aux_lemma =>
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul s m => simp [TensorProduct.smul_tmul', fpure, smul_smul]
          | add z w hz hw => simp [smul_add, hz, hw]
      obtain ⟨m, bc, hmb⟩ := h_T006.2
      let B : Module.Basis (LR.I l) (LR.R p) (LR.MR p M) := m.baseChange (LR.R p)
      have fb (i : LR.I l) : f (B i) = bc i := by
        as_aux_lemma =>
          simp [B, fpure, hmb]
      have fexpand (z : LR.MR p M) :
          f z = ∑ i : LR.I l, j (B.repr z i) • bc i := by
        as_aux_lemma =>
          conv_lhs => rw [← B.sum_repr z]
          simp only [map_sum, fsmul, fb]
      have coord (z : LR.MR p M) (i : LR.I l) :
          bc.repr (f z) i = j (B.repr z i) := by
        as_aux_lemma =>
          rw [fexpand z]
          exact congrFun (bc.repr_sum_self (fun i => j (B.repr z i))) i
      have finj : Function.Injective f := by
        as_aux_lemma =>
          intro z w he
          apply B.repr.injective
          apply Finsupp.ext
          intro i
          apply Subtype.ext
          apply Rat.cast_injective (α := ℂ)
          change j (B.repr z i) = j (B.repr w i)
          rw [← coord z i, ← coord w i, he]
      have fspan : Submodule.span ℂ (Set.range f) = ⊤ := by
        as_aux_lemma =>
          apply (Submodule.eq_top_iff_forall_basis_mem bc).mpr
          intro i
          exact Submodule.subset_span ⟨B i, fb i⟩
      have preserve (g : Module.End ℂ V) (hg : ∀ m ∈ M, g m ∈ M)
          (z : LR.MR p M) : g (f z) ∈ Set.range f := by
        as_aux_lemma =>
          let gm : Module.End ℤ M := (g.restrictScalars ℤ).restrict hg
          refine ⟨gm.baseChange (LR.R p) z, ?_⟩
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul r m => simp [fpure, gm]
          | add z w hz hw => simp [hz, hw]
      refine ⟨f, ⟨fpure, fsmul⟩, ⟨finj, ⟨B⟩, fspan⟩, h_H004.2, ?_⟩
      intro r z
      exact ⟨preserve (LR.dp (rho x) r) (fun m hm => (h_H004.2 r m hm).1) z,
        preserve (LR.dp (rho y) r) (fun m hm => (h_H004.2 r m hm).2) z⟩

theorem T008 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T006 : LR.LocalRingSpec p ∧ ∃ (m : Module.Basis (LR.I l) ℤ M) (bc : Module.Basis (LR.I l) ℂ V), ∀ i, (m i : V) = bc i) :
    LR.SmallUnits p l := by
  have hlp : l.toNat < p := by omega
  have hncast : ∀ n : ℕ, ¬ p ∣ n → ¬ (p : ℤ) ∣ (n : ℤ) := by
    intro n hn hd
    apply hn
    exact_mod_cast hd
  have hfac : ∀ r : ℕ, r ≤ l.toNat →
      ¬ p ∣ r.factorial ∧ IsUnit (r.factorial : LR.R p) := by
    intro r hr
    have hnd : ¬ p ∣ r.factorial := by
      rw [h_H001.1.dvd_factorial]
      omega
    refine ⟨hnd, ?_⟩
    have hu := h_T006.1.2 (r.factorial : ℤ) (hncast _ hnd)
    simpa only [Int.cast_natCast] using hu
  refine ⟨hfac, ?_⟩
  intro j
  have hj : j.val ≤ l.toNat := by have := j.isLt; omega
  have hdenZ : ¬ (p : ℤ) ∣ (l.toNat.factorial : ℤ) :=
    hncast _ (hfac l.toNat le_rfl).1
  let q : ℚ := ((j.val.factorial * (l.toNat - j.val).factorial : ℕ) : ℚ) /
    (l.toNat.factorial : ℚ)
  have hqmem : q ∈ LR.R p := by
    apply (h_T006.1.1 q).2
    refine ⟨((j.val.factorial * (l.toNat - j.val).factorial : ℕ) : ℤ),
      (l.toNat.factorial : ℤ), ?_, hdenZ, ?_⟩
    · positivity
    · simp only [Int.cast_natCast]
      rfl
  have hden : (l.toNat.factorial : ℚ) ≠ 0 := by positivity
  have hid : (Nat.choose l.toNat j.val : ℚ) * (j.val.factorial : ℚ) *
      ((l.toNat - j.val).factorial : ℚ) = (l.toNat.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨q, hqmem⟩, ?_⟩
  apply Subtype.ext
  change (Nat.choose l.toNat j.val : ℚ) * q = 1
  dsimp [q]
  push_cast
  calc
    (Nat.choose l.toNat j.val : ℚ) *
        ((j.val.factorial : ℚ) * ((l.toNat - j.val).factorial : ℚ) /
          (l.toNat.factorial : ℚ)) =
        ((Nat.choose l.toNat j.val : ℚ) * (j.val.factorial : ℚ) *
          ((l.toNat - j.val).factorial : ℚ)) / (l.toNat.factorial : ℚ) := by ring
    _ = 1 := by rw [hid, div_self hden]

theorem T009 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) :
    ∀ b : Module.Basis (LR.I l) ℂ V, LR.BasisSpec l (rho y) v b → LR.UnitIdentities l (rho x) (rho y) b := by
  classical
  intro b hb
  let n := l.toNat
  let e : ℕ → V := LR.eNat (rho y) v
  let P := LR.dp (rho y) n * LR.dp (rho x) n
  have hd : LR.DividedMatrices l (rho x) (rho y) v := h_T005.2.2.2.2.2
  have hx (r k : ℕ) (hk : k ≤ n) :
      LR.dp (rho x) r (e k) =
        if r ≤ k then (Nat.choose (n-k+r) r : ℂ) • e (k-r) else 0 :=
    (hd r k hk).1
  have hy (r k : ℕ) (hk : k ≤ n) :
      LR.dp (rho y) r (e k) =
        if k+r ≤ n then (Nat.choose (k+r) r : ℂ) • e (k+r) else 0 :=
    (hd r k hk).2
  have hPi (k : ℕ) (hk : k ≤ n) :
      P (e k) = if k = n then e n else 0 := by
    change LR.dp (rho y) n (LR.dp (rho x) n (e k)) = _
    by_cases he : k = n
    · subst k
      simp [hx n n (by omega), hy n 0 (by omega)]
    · have hn : ¬ n ≤ k := by omega
      simp [hx n k hk, hn, he]
  have htop (i : LR.I l) : LR.dp (rho x) (n-i.val) (e n) = e i.val := by
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have he : n - (n-i.val) = i.val := by omega
    simp [hx (n-i.val) n (by omega), he]
  have hu (i j k : LR.I l) :
      LR.unit l b i j (b k) = if k = j then b i else 0 := by
    simp [LR.unit, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      Finsupp.single_apply, eq_comm]
  have hP : P = LR.unit l b (Fin.last n) (Fin.last n) := by
    apply b.ext
    intro k
    rw [hu, hb k]
    change P (e k.val) = if k = Fin.last n then b (Fin.last n) else 0
    rw [hPi k.val (Nat.le_of_lt_succ k.isLt)]
    have he : k = Fin.last n ↔ k.val = n := by
      constructor
      · intro h; subst k; rfl
      · intro h; exact Fin.ext h
    simp only [he]
    rw [hb (Fin.last n)]
    rfl
  intro i j
  refine ⟨hP, ?_, ?_⟩
  · change LR.dp (rho x) (n-i.val) * P = LR.unit l b i (Fin.last n)
    apply b.ext
    intro k
    rw [Module.End.mul_apply, hu, hb k]
    change LR.dp (rho x) (n-i.val) (P (e k.val)) =
      if k = Fin.last n then b i else 0
    rw [hPi k.val (Nat.le_of_lt_succ k.isLt)]
    by_cases he : k = Fin.last n
    · subst k
      simp only [Fin.val_last, if_true]
      rw [htop, hb i]
    · have hv : k.val ≠ n := fun h => he (Fin.ext h)
      simp [hv, he]
  · change P * LR.dp (rho y) (n-j.val) =
      (Nat.choose n j.val : ℂ) • LR.unit l b (Fin.last n) j
    apply b.ext
    intro k
    rw [Module.End.mul_apply, LinearMap.smul_apply, hu, hb k]
    change P (LR.dp (rho y) (n-j.val) (e k.val)) =
      (Nat.choose n j.val : ℂ) • (if k = j then b (Fin.last n) else 0)
    rw [hy (n-j.val) k.val (Nat.le_of_lt_succ k.isLt)]
    have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    by_cases he : k = j
    · subst k
      have hs : j.val + (n-j.val) = n := by omega
      simp only [hs, le_refl, if_true]
      rw [map_smul, hPi n (by omega), if_pos rfl, Nat.choose_symm hj]
      rw [hb (Fin.last n)]
      rfl
    · by_cases hle : k.val + (n-j.val) ≤ n
      · have hne : k.val + (n-j.val) ≠ n := by
          intro h
          apply he
          apply Fin.ext
          omega
        simp [hle, map_smul, hPi _ hle, hne, he]
      · simp [hle, he]

theorem T010 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) (h_T006 : LR.LocalRingSpec p ∧ ∃ (m : Module.Basis (LR.I l) ℤ M) (bc : Module.Basis (LR.I l) ℂ V), ∀ i, (m i : V) = bc i) (h_T007 : Nonempty (LR.Action K M rho x y h) ∧ ∃ f : LR.MR p M →ₗ[ℤ] V, LR.IotaSpec p M f ∧ LR.LocalBasis p l M f ∧ LR.Preserved p M f (rho x) (rho y)) (h_T008 : LR.SmallUnits p l) (h_T009 : ∀ b : Module.Basis (LR.I l) ℂ V, LR.BasisSpec l (rho y) v b → LR.UnitIdentities l (rho x) (rho y) b) :
    LR.N2 p l K M rho x y h v := by
  classical
  rcases h_T007 with ⟨hact, f, hf, hb, hp⟩
  refine ⟨h_T006.1, h_T008, hact, f, hf, hb, hp, ?_⟩
  intro b hbs
  have hid := h_T009 b hbs
  refine ⟨hid, ?_⟩
  have hinv : ∀ j : LR.I l, ∃ r : LR.R p, (((r : ℚ) : ℂ)) = (Nat.choose l.toNat j.val : ℂ)⁻¹ ∧ (Nat.choose l.toNat j.val : ℂ) ≠ 0 := by
    as_aux_lemma =>
      intro j
      rcases h_T008.2 j with ⟨u, hu⟩
      let s : LR.R p →+* ℂ := (algebraMap ℚ ℂ).comp (LR.R p).subtype
      have hconv (r : LR.R p) : s r = (((r : ℚ) : ℂ)) := by simp [s]
      have hs : s (u : LR.R p) * s ((u⁻¹ : (LR.R p)ˣ) : LR.R p) = 1 := by
        as_aux_lemma =>
          rw [← map_mul]
          simp
      rw [hu, map_natCast, hconv] at hs
      refine ⟨↑(u⁻¹), ?_, ?_⟩
      · exact eq_inv_of_mul_eq_one_right hs
      · intro hz
        rw [hz, zero_mul] at hs
        exact zero_ne_one hs
  intro i j
  rcases hinv j with ⟨r, hr, hc⟩
  have hunit (s t : LR.I l) :
      LR.unit l b s (Fin.last l.toNat) * LR.unit l b (Fin.last l.toNat) t = LR.unit l b s t := by
    as_aux_lemma =>
      ext w
      simp [LR.unit, Module.End.mul_apply, Module.Basis.coord_apply]
  have hrow : LR.unit l b i (Fin.last l.toNat) *
      (LR.dp (rho y) l.toNat * LR.dp (rho x) l.toNat) =
      LR.unit l b i (Fin.last l.toNat) := by
    as_aux_lemma =>
      rw [(hid i j).1]
      exact hunit i (Fin.last l.toNat)
  have hprod :
      LR.dp (rho x) (l.toNat-i.val) *
        (LR.dp (rho y) l.toNat * LR.dp (rho x) l.toNat) *
        LR.dp (rho y) (l.toNat-j.val) =
      (Nat.choose l.toNat j.val : ℂ) • LR.unit l b i j := by
    as_aux_lemma =>
      calc
        _ = LR.unit l b i (Fin.last l.toNat) * LR.dp (rho y) (l.toNat-j.val) := by
          as_aux_lemma =>
            rw [(hid i j).2.1]
        _ = (LR.unit l b i (Fin.last l.toNat) *
            (LR.dp (rho y) l.toNat * LR.dp (rho x) l.toNat)) *
            LR.dp (rho y) (l.toNat-j.val) := by rw [hrow]
        _ = LR.unit l b i (Fin.last l.toNat) *
            ((LR.dp (rho y) l.toNat * LR.dp (rho x) l.toNat) *
            LR.dp (rho y) (l.toNat-j.val)) := mul_assoc _ _ _
        _ = LR.unit l b i (Fin.last l.toNat) *
            ((Nat.choose l.toNat j.val : ℂ) • LR.unit l b (Fin.last l.toNat) j) := by
          as_aux_lemma =>
            rw [(hid i j).2.2]
        _ = (Nat.choose l.toNat j.val : ℂ) •
            (LR.unit l b i (Fin.last l.toNat) * LR.unit l b (Fin.last l.toNat) j) :=
          mul_smul_comm _ _ _
        _ = _ := by rw [hunit]
  have heq : LR.unit l b i j = (Nat.choose l.toNat j.val : ℂ)⁻¹ •
      (LR.dp (rho x) (l.toNat-i.val) *
        (LR.dp (rho y) l.toNat * LR.dp (rho x) l.toNat) *
        LR.dp (rho y) (l.toNat-j.val)) := by
    as_aux_lemma =>
      rw [hprod, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨heq, ?_⟩
  intro z
  have hpres (n : ℕ) (w : V) (hw : w ∈ Set.range f) :
      LR.dp (rho x) n w ∈ Set.range f ∧ LR.dp (rho y) n w ∈ Set.range f := by
    as_aux_lemma =>
      rcases hw with ⟨z', rfl⟩
      exact hp.2 n z'
  have hz : f z ∈ Set.range f := ⟨z, rfl⟩
  have hz1 := (hpres (l.toNat-j.val) (f z) hz).2
  have hz2 := (hpres l.toNat _ hz1).1
  have hz3 := (hpres l.toNat _ hz2).2
  have hz4 := (hpres (l.toNat-i.val) _ hz3).1
  rcases hz4 with ⟨w, hw⟩
  refine ⟨r • w, ?_⟩
  rw [hf.2, hr, hw, heq]
  simp only [LinearMap.smul_apply, Module.End.mul_apply]

theorem T011 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V)  :
    ∀ (r : LR.R p) (c : LR.C p), LR.cv p (r • c) = (((r : ℚ) : ℂ)) * LR.cv p c := by
  intro r c
  change (RestrictScalars.addEquiv (LR.R p) ℚ ℂ) (r • c) = _
  rw [RestrictScalars.smul_def, AddEquiv.apply_symm_apply]
  change (r : ℚ) • LR.cv p c = _
  exact Rat.smul_def (r : ℚ) (LR.cv p c)

theorem T012 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) (h_T010 : LR.N2 p l K M rho x y h v) (h_T011 : ∀ (r : LR.R p) (c : LR.C p), LR.cv p (r • c) = (((r : ℚ) : ℂ)) * LR.cv p c) :
    ∀ f : LR.MR p M →ₗ[ℤ] V, LR.IotaSpec p M f → ∃ J : Submodule (LR.R p) (LR.C p), LR.CoeffSpec p l (rho y) v M f J := by
  classical
  intro f hf
  rcases h_T010 with ⟨hlocal, hsmall, hact, f₀, hf₀, hbase, hpres, hunits⟩
  have heq : f = f₀ := by
    as_aux_lemma =>
      apply TensorProduct.ext'
      intro r m
      exact (hf.1 r m).trans (hf₀.1 r m).symm
  subst f₀
  rcases hbase with ⟨hfinj, ⟨m⟩, hspan⟩
  rcases h_T005.2.2.2.1 with ⟨b, hb, hnil⟩
  have hu := (hunits b hb).2
  have hp (i j : LR.I l) (z : LR.MR p M) :
      b.coord j (f z) • b i ∈ Set.range f := by
    as_aux_lemma =>
      simpa [LR.unit] using (hu i j).2 z
  let c : LR.I l → LR.MR p M →ₗ[LR.R p] LR.C p := fun i =>
    { toFun := fun z => (LR.cv p).symm (b.coord i (f z))
      map_add' := by
        as_aux_lemma =>
          intro z w
          simp only [map_add]
      map_smul' := by
        as_aux_lemma =>
          intro r z
          apply (LR.cv p).injective
          simp only [h_T011, AddEquiv.apply_symm_apply]
          rw [hf.2, map_smul]
          rfl }
  have hc (i : LR.I l) (z : LR.MR p M) :
      LR.cv p (c i z) = b.coord i (f z) := (LR.cv p).apply_symm_apply _
  let o : LR.I l := ⟨0, Nat.zero_lt_succ _⟩
  let J : Submodule (LR.R p) (LR.C p) := (c o).range
  have hcoord (i : LR.I l) (z : LR.MR p M) : c i z ∈ J := by
    as_aux_lemma =>
      obtain ⟨w, hw⟩ := hp o i z
      refine ⟨w, ?_⟩
      apply (LR.cv p).injective
      rw [hc, hc, hw]
      simp [Module.Basis.coord_apply]
  have hmem (i : LR.I l) (a : ℂ) :
      (LR.cv p).symm a ∈ J ↔ a • b i ∈ Set.range f := by
    as_aux_lemma =>
      constructor
      · rintro ⟨z, hz⟩
        have hz' : b.coord o (f z) = a := by
          as_aux_lemma =>
            simpa only [hc, AddEquiv.apply_symm_apply] using congrArg (LR.cv p) hz
        simpa only [hz'] using hp i o z
      · rintro ⟨z, hz⟩
        have hciz : c i z = (LR.cv p).symm a := by
          as_aux_lemma =>
            apply (LR.cv p).injective
            rw [hc, hz, AddEquiv.apply_symm_apply]
            simp [Module.Basis.coord_apply]
        exact hciz ▸ hcoord i z
  have hfg : J.FG := by
    dsimp only [J]
    as_aux_lemma =>
      letI : Module.Finite (LR.R p) (LR.MR p M) := Module.Finite.of_basis m
      exact Submodule.fg_range (c o)
  have hnzero : J ≠ ⊥ := by
    as_aux_lemma =>
      intro hJ
      have hfzero (z : LR.MR p M) : f z = 0 := by
        as_aux_lemma =>
          apply b.forall_coord_eq_zero_iff.mp
          intro i
          have hi : c i z = 0 := by
            as_aux_lemma =>
              have := hcoord i z
              simpa only [hJ, Submodule.mem_bot] using this
          simpa only [hc, map_zero] using congrArg (LR.cv p) hi
      have hle : Submodule.span ℂ (Set.range f) ≤ ⊥ := by
        as_aux_lemma =>
          apply Submodule.span_le.mpr
          rintro w ⟨z, rfl⟩
          change f z = 0
          exact hfzero z
      have hz : b o ∈ (⊥ : Submodule ℂ V) := hle (by rw [hspan]; trivial)
      exact b.ne_zero o (by simpa only [Submodule.mem_bot] using hz)
  let E : LR.MR p M →ₗ[LR.R p] (LR.I l → J) :=
    { toFun := fun z i => ⟨c i z, hcoord i z⟩
      map_add' := by
        as_aux_lemma =>
          intro z w
          funext i
          apply Subtype.ext
          exact (c i).map_add z w
      map_smul' := by
        as_aux_lemma =>
          intro r z
          funext i
          apply Subtype.ext
          exact (c i).map_smul r z }
  have hsum (z : LR.MR p M) :
      f z = ∑ i, LR.cv p ((E z i : J) : LR.C p) • b i := by
    as_aux_lemma =>
      change f z = ∑ i, LR.cv p (c i z) • b i
      simp_rw [hc, Module.Basis.coord_apply]
      exact (b.sum_repr (f z)).symm
  have hEinj : Function.Injective E := by
    as_aux_lemma =>
      intro z w hzw
      apply hfinj
      rw [hsum z, hsum w, hzw]
  have hEsurj : Function.Surjective E := by
    as_aux_lemma =>
      intro g
      have hg (i : LR.I l) :
          LR.cv p (g i : LR.C p) • b i ∈ Set.range f := by
        as_aux_lemma =>
          apply (hmem i _).mp
          simpa only [AddEquiv.symm_apply_apply] using (g i).property
      choose z hz using hg
      refine ⟨∑ i, z i, ?_⟩
      have hfs : f (∑ i, z i) = ∑ i, LR.cv p (g i : LR.C p) • b i := by
        as_aux_lemma =>
          rw [map_sum]
          exact Finset.sum_congr rfl (fun i _ => hz i)
      funext i
      apply Subtype.ext
      apply (LR.cv p).injective
      change LR.cv p (c i (∑ j, z j)) = LR.cv p (g i : LR.C p)
      rw [hc, hfs]
      change b.repr (∑ j, LR.cv p (g j : LR.C p) • b j) i = _
      exact congrFun (b.repr_sum_self (fun j => LR.cv p (g j : LR.C p))) i
  let e : LR.MR p M ≃ₗ[LR.R p] (LR.I l → J) :=
    LinearEquiv.ofBijective E ⟨hEinj, hEsurj⟩
  refine ⟨J, ?_, hfg, hnzero, e.symm, ?_⟩
  · intro i a
    simpa only [hb i] using hmem i a
  · intro g
    have hs := hsum (e.symm g)
    have he : E (e.symm g) = g := e.apply_symm_apply g
    rw [he] at hs
    simpa only [hb] using hs

theorem T013 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_T011 : ∀ (r : LR.R p) (c : LR.C p), LR.cv p (r • c) = (((r : ℚ) : ℂ)) * LR.cv p c) :
    ∀ J : Submodule (LR.R p) (LR.C p), J.FG → LR.RationalEmbedding p J := by
  classical
  intro J hJ
  letI : Module.Finite (LR.R p) J := Module.Finite.of_fg hJ
  have hfin : FiniteDimensional ℚ (ℚ ⊗[LR.R p] J) := inferInstance
  let j : J →ₗ[LR.R p] ℂ :=
    { toFun := fun c => LR.cv p (c : LR.C p)
      map_add' := fun c d => (LR.cv p).map_add _ _
      map_smul' := by
        as_aux_lemma =>
          intro r c
          exact h_T011 r (c : LR.C p) }
  let bil : ℚ →ₗ[ℚ] (J →ₗ[LR.R p] ℂ) :=
    { toFun := fun q => q • j
      map_add' := fun q r => add_smul q r j
      map_smul' := fun q r => mul_smul q r j }
  let mu : ℚ ⊗[LR.R p] J →ₗ[ℚ] ℂ := TensorProduct.AlgebraTensorModule.lift bil
  have hmu : LR.MuSpec p J mu := by
    as_aux_lemma =>
      intro q c
      change q • LR.cv p (c : LR.C p) = _
      simp only [Rat.smul_def]
  have hden : ∀ z : ℚ ⊗[LR.R p] J,
      ∃ D : ℕ, D ≠ 0 ∧ ∃ c : J, (D : ℚ) • z = (1 : ℚ) ⊗ₜ[LR.R p] c := by
    as_aux_lemma =>
      intro z
      have ht (n : ℤ) (c : J) :
          (n : ℚ) • ((1 : ℚ) ⊗ₜ[LR.R p] c) =
            (1 : ℚ) ⊗ₜ[LR.R p] ((n : LR.R p) • c) := by
        as_aux_lemma =>
          rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
          congr 1
      have htn (n : ℕ) (c : J) :
          (n : ℚ) • ((1 : ℚ) ⊗ₜ[LR.R p] c) =
            (1 : ℚ) ⊗ₜ[LR.R p] ((n : LR.R p) • c) := by
        as_aux_lemma =>
          rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
          congr 1
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
      | tmul q c =>
        refine ⟨q.den, q.den_nz, (q.num : LR.R p) • c, ?_⟩
        rw [TensorProduct.smul_tmul']
        change ((q.den : ℚ) * q) ⊗ₜ[LR.R p] c = _
        rw [Rat.den_mul_eq_num, ← ht, TensorProduct.smul_tmul']
        simp
      | add z w hz hw =>
        obtain ⟨D, hD, c, hc⟩ := hz
        obtain ⟨E, hE, d, hd⟩ := hw
        refine ⟨D*E, Nat.mul_ne_zero hD hE,
          (E : LR.R p) • c + (D : LR.R p) • d, ?_⟩
        rw [Nat.cast_mul, smul_add, TensorProduct.tmul_add]
        congr 1
        · rw [mul_comm, mul_smul, hc, htn]
        · rw [mul_smul, hd, htn]

  have hmu_one (c : J) : mu ((1 : ℚ) ⊗ₜ[LR.R p] c) = LR.cv p (c : LR.C p) := by
    as_aux_lemma =>
      simpa only [Rat.cast_one, one_mul] using hmu 1 c
  have hzero : ∀ z, mu z = 0 → z = 0 := by
    as_aux_lemma =>
      intro z hz
      obtain ⟨D, hD, c, hc⟩ := hden z
      have hcimage : LR.cv p (c : LR.C p) = 0 := by
        as_aux_lemma =>
          have hh := congrArg mu hc
          simpa only [map_smul, hz, smul_zero, hmu_one] using hh.symm
      have hc0 : c = 0 := by
        as_aux_lemma =>
          apply Subtype.ext
          apply (LR.cv p).injective
          change LR.cv p (c : LR.C p) = LR.cv p (0 : LR.C p)
          exact hcimage.trans (map_zero (LR.cv p)).symm
      rw [hc0, TensorProduct.tmul_zero] at hc
      exact (smul_eq_zero.mp hc).resolve_left (by exact_mod_cast hD)
  refine ⟨hfin, mu, hmu, LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hzero), ?_⟩
  apply le_antisymm
  · rintro w ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simpa using (Submodule.zero_mem (Submodule.span ℚ ((LR.cv p) '' (J : Set (LR.C p)))))
    | tmul q c =>
      rw [hmu]
      change q • LR.cv p (c : LR.C p) ∈ _
      exact Submodule.smul_mem _ q (Submodule.subset_span ⟨(c : LR.C p), c.property, rfl⟩)
    | add z w hz hw =>
      simpa only [map_add] using Submodule.add_mem _ hz hw
  · apply Submodule.span_le.mpr
    rintro w ⟨c, hc, rfl⟩
    refine ⟨(1 : ℚ) ⊗ₜ[LR.R p] (⟨c, hc⟩ : J), ?_⟩
    exact hmu_one ⟨c, hc⟩

theorem T014 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_T010 : LR.N2 p l K M rho x y h v) :
    Module.finrank ℚ (ℚ ⊗[LR.R p] LR.MR p M) = l.toNat+1 := by
  classical
  rcases h_T010 with ⟨_, _, _, f, _, hlocal, _⟩
  obtain ⟨b⟩ := hlocal.2.1
  let bQ : Module.Basis (LR.I l) ℚ (ℚ ⊗[LR.R p] LR.MR p M) := b.baseChange ℚ
  simpa [LR.I] using Module.finrank_eq_card_basis bQ

theorem T015 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T013 : ∀ J : Submodule (LR.R p) (LR.C p), J.FG → LR.RationalEmbedding p J) (h_T014 : Module.finrank ℚ (ℚ ⊗[LR.R p] LR.MR p M) = l.toNat+1) :
    ∀ (f : LR.MR p M →ₗ[ℤ] V) (J : Submodule (LR.R p) (LR.C p)), LR.IotaSpec p M f → LR.CoeffSpec p l (rho y) v M f J → Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1 := by
  classical
  intro f J hf hJ
  rcases hJ with ⟨hcoeff, hfg, hne, D, hD⟩
  have hrat := h_T013 J hfg
  letI : FiniteDimensional ℚ (ℚ ⊗[LR.R p] J) := hrat.1
  let E : (ℚ ⊗[LR.R p] LR.MR p M) ≃ₗ[ℚ]
      (LR.I l → (ℚ ⊗[LR.R p] J)) :=
    (D.symm.baseChange (LR.R p) ℚ _ _).trans
      (TensorProduct.piRight (LR.R p) ℚ ℚ (fun _ : LR.I l => J))
  have hdim : l.toNat + 1 =
      (l.toNat + 1) * Module.finrank ℚ (ℚ ⊗[LR.R p] J) := by
    as_aux_lemma =>
      calc
        l.toNat + 1 = Module.finrank ℚ (ℚ ⊗[LR.R p] LR.MR p M) := h_T014.symm
        _ = Module.finrank ℚ (LR.I l → (ℚ ⊗[LR.R p] J)) := E.finrank_eq
        _ = (l.toNat + 1) * Module.finrank ℚ (ℚ ⊗[LR.R p] J) := by
          as_aux_lemma =>
            simp [Module.finrank_pi_fintype, LR.I]
  nlinarith

theorem T016 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V)  :
    ∀ J : Submodule (LR.R p) (LR.C p), LR.RationalEmbedding p J → Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1 → LR.RationalMultiples p J := by
  intro J hEmb hdim
  rcases hEmb with ⟨hfinite, mu, hmu, hinj, hrange⟩
  letI : FiniteDimensional ℚ (ℚ ⊗[LR.R p] J) := hfinite
  intro a ha hane c hc
  let ja : J := ⟨(LR.cv p).symm a, ha⟩
  let jc : J := ⟨(LR.cv p).symm c, hc⟩
  have hma : mu ((1 : ℚ) ⊗ₜ[LR.R p] ja) = a := by
    simpa [ja] using hmu 1 ja
  have hmc : mu ((1 : ℚ) ⊗ₜ[LR.R p] jc) = c := by
    simpa [jc] using hmu 1 jc
  have hta : ((1 : ℚ) ⊗ₜ[LR.R p] ja) ≠ 0 := by
    intro hz
    apply hane
    rw [← hma, hz, map_zero]
  obtain ⟨q, hq⟩ := (finrank_eq_one_iff_of_nonzero' ((1 : ℚ) ⊗ₜ[LR.R p] ja) hta).mp hdim ((1 : ℚ) ⊗ₜ[LR.R p] jc)
  refine ⟨q, ?_⟩
  have heq : q • a = c := by
    have hh := congrArg mu hq
    simpa only [map_smul, hma, hmc] using hh
  calc
    c = q • a := heq.symm
    _ = (q : ℂ) * a := Algebra.smul_def q a

theorem T017 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T010 : LR.N2 p l K M rho x y h v) :
    LR.PDecomposition p := by
  classical
  have factor_int : ∀ a : ℤ, a ≠ 0 →
      ∃ (e : ℕ) (b : ℤ), ¬ (p : ℤ) ∣ b ∧ a = (p : ℤ)^e * b := by
    as_aux_lemma =>
      intro a ha
      obtain ⟨e, n, hn, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd
        (show a.natAbs ≠ 0 by simpa using ha) p h_H001.1.ne_one
      refine ⟨e, a.sign * (n : ℤ), ?_, ?_⟩
      · rw [Int.natCast_dvd]
        simpa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero ha] using hn
      · calc
          a = a.sign * (a.natAbs : ℤ) := (Int.sign_mul_natAbs a).symm
          _ = a.sign * ((p : ℤ)^e * (n : ℤ)) := by rw [he]; push_cast; rfl
          _ = (p : ℤ)^e * (a.sign * (n : ℤ)) := by ring
  have fraction_unit : ∀ (b : ℤ) (d : ℕ),
      ¬ (p : ℤ) ∣ b → ¬ p ∣ d →
      ∃ u : (LR.R p)ˣ, (u.val : ℚ) = (b : ℚ) / (d : ℚ) := by
    as_aux_lemma =>
      intro b d hb hd
      have hb0 : b ≠ 0 := by
        as_aux_lemma =>
          intro hz
          exact hb (hz ▸ dvd_zero _)
      have hd0 : d ≠ 0 := by
        as_aux_lemma =>
          intro hz
          exact hd (hz ▸ dvd_zero _)
      have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
      have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
      have hx : (b : ℚ) / (d : ℚ) ∈ LR.R p := by
        as_aux_lemma =>
          apply (h_T010.1.1 _).2
          refine ⟨b, (d : ℤ), ?_, ?_, ?_⟩
          · exact_mod_cast hd0
          · exact_mod_cast hd
          · simp
      have hy : (d : ℚ) / (b : ℚ) ∈ LR.R p := by
        as_aux_lemma =>
          apply (h_T010.1.1 _).2
          refine ⟨(d : ℤ), b, hb0, hb, ?_⟩
          simp
      let xx : LR.R p := ⟨(b : ℚ) / (d : ℚ), hx⟩
      let yy : LR.R p := ⟨(d : ℚ) / (b : ℚ), hy⟩
      have hxy : xx * yy = 1 := by
        as_aux_lemma =>
          apply Subtype.ext
          change (b : ℚ) / (d : ℚ) * ((d : ℚ) / (b : ℚ)) = 1
          field_simp
      exact ⟨Units.mkOfMulEqOne xx yy hxy, rfl⟩
  intro q hq
  obtain ⟨eN, b, hb, heN⟩ := factor_int q.num (Rat.num_ne_zero.mpr hq)
  obtain ⟨eD, d, hd, heD⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd q.den_ne_zero p h_H001.1.ne_one
  obtain ⟨u, hu⟩ := fraction_unit b d hb hd
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
  have hN : (q.num : ℚ) = (p : ℚ)^eN * (b : ℚ) := by exact_mod_cast heN
  have hD : (q.den : ℚ) = (p : ℚ)^eD * (d : ℚ) := by exact_mod_cast heD
  refine ⟨(eN : ℤ) - (eD : ℤ), u, ?_⟩
  rw [hu, zpow_sub₀ hpQ, zpow_natCast, zpow_natCast]
  calc
    q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    _ = (p : ℚ)^eN / (p : ℚ)^eD * ((b : ℚ) / (d : ℚ)) := by
      as_aux_lemma =>
        rw [hN, hD]
        ring

theorem T018 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) (h_T010 : LR.N2 p l K M rho x y h v) (h_T012 : ∀ f : LR.MR p M →ₗ[ℤ] V, LR.IotaSpec p M f → ∃ J : Submodule (LR.R p) (LR.C p), LR.CoeffSpec p l (rho y) v M f J) (h_T013 : ∀ J : Submodule (LR.R p) (LR.C p), J.FG → LR.RationalEmbedding p J) (h_T015 : ∀ (f : LR.MR p M →ₗ[ℤ] V) (J : Submodule (LR.R p) (LR.C p)), LR.IotaSpec p M f → LR.CoeffSpec p l (rho y) v M f J → Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1) (h_T016 : ∀ J : Submodule (LR.R p) (LR.C p), LR.RationalEmbedding p J → Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1 → LR.RationalMultiples p J) (h_T017 : LR.PDecomposition p) :
    LR.N3 p l (rho y) v M := by
  classical
    have cyclic : ∀ J : Submodule (LR.R p) (LR.C p), J.FG → J ≠ ⊥ → LR.RationalMultiples p J →
  ∃ b : ℂ, (LR.cv p).symm b ∈ J ∧ b ≠ 0 ∧ J = Submodule.span (LR.R p) {(LR.cv p).symm b} := by
      as_aux_lemma =>
        classical
          intro J hfg hJ0 hrat
          have sc : ∀ (r : LR.R p) (c : LR.C p),
              LR.cv p (r • c) = ((r : ℚ) : ℂ) * LR.cv p c := by
            as_aux_lemma =>
              intro r c
              change (r : ℚ) • LR.cv p c = _
              exact Rat.smul_def _ _
          obtain ⟨a', ha', ha'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
          let a : ℂ := LR.cv p a'
          have ha : a ≠ 0 := by
            as_aux_lemma =>
              intro hz
              apply ha'0
              exact (LR.cv p).injective (by simpa [a] using hz)
          obtain ⟨s, hs⟩ := hfg
          let t := s.filter (fun g => g ≠ 0)
          have ht : t.Nonempty := by
            as_aux_lemma =>
              by_contra hn
              apply hJ0
              rw [← hs]
              apply le_antisymm _ bot_le
              apply Submodule.span_le.mpr
              intro g hg
              have : g = 0 := by
                as_aux_lemma =>
                  by_contra h
                  exact hn ⟨g, Finset.mem_filter.mpr ⟨hg, h⟩⟩
              simpa [this]
          let G := {g : LR.C p // g ∈ t}
          have hdec : ∀ g : G, ∃ (nu : ℤ) (u : (LR.R p)ˣ),
              LR.cv p g.val = (((p : ℚ)^nu * (u.val : ℚ) : ℚ) : ℂ) * a := by
            as_aux_lemma =>
              intro g
              have hgJ : g.val ∈ J := by
                as_aux_lemma =>
                  rw [← hs]
                  exact Submodule.subset_span (Finset.mem_filter.mp g.property).1
              obtain ⟨q, hq⟩ := hrat a (by simpa [a] using ha') ha (LR.cv p g.val) (by simpa using hgJ)
              have hq0 : q ≠ 0 := by
                as_aux_lemma =>
                  intro hz
                  have : LR.cv p g.val = 0 := by simpa [hz] using hq
                  exact (Finset.mem_filter.mp g.property).2 ((LR.cv p).injective (by simpa using this))
              obtain ⟨nu, u, hu⟩ := h_T017 q hq0
              exact ⟨nu, u, by rw [hq, hu]⟩
          choose nu u hu using hdec
          haveI : Nonempty G := ⟨⟨ht.choose, ht.choose_spec⟩⟩
          obtain ⟨g0, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset G) nu Finset.univ_nonempty
          let b : ℂ := (((p : ℚ) ^ nu g0 : ℚ) : ℂ) * a
          have hp : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
          have hb : b ≠ 0 := mul_ne_zero (by exact_mod_cast (zpow_ne_zero (nu g0) hp)) ha
          have hg0 : g0.val ∈ J := by
            as_aux_lemma =>
              rw [← hs]
              exact Submodule.subset_span (Finset.mem_filter.mp g0.property).1
          have hgb : ∀ g : G, ∃ r : LR.R p, LR.cv p g.val = ((r : ℚ) : ℂ) * b := by
            as_aux_lemma =>
              intro g
              have hn : 0 ≤ nu g - nu g0 := sub_nonneg.mpr (hmin g (Finset.mem_univ g))
              let r : LR.R p := (p : LR.R p) ^ (nu g - nu g0).toNat * (u g).val
              refine ⟨r, ?_⟩
              have he : (r : ℚ) * (p : ℚ) ^ nu g0 = (p : ℚ) ^ nu g * ((u g).val : ℚ) := by
                as_aux_lemma =>
                  change ((p : ℚ) ^ (nu g - nu g0).toNat * ((u g).val : ℚ)) * (p : ℚ) ^ nu g0 = _
                  rw [← zpow_natCast, Int.toNat_of_nonneg hn]
                  calc
                    _ = ((p : ℚ) ^ (nu g - nu g0) * (p : ℚ) ^ nu g0) * ((u g).val : ℚ) := by ring
                    _ = _ := by rw [← zpow_add₀ hp, sub_add_cancel]
              rw [hu g]
              dsimp [b]
              rw [← mul_assoc, ← Rat.cast_mul, he]
          have hbJ : (LR.cv p).symm b ∈ J := by
            as_aux_lemma =>
              have he : (u g0).val • (LR.cv p).symm b = g0.val := by
                as_aux_lemma =>
                  apply (LR.cv p).injective
                  rw [sc, (LR.cv p).apply_symm_apply, hu g0]
                  dsimp [b]
                  push_cast
                  ring
              have hh := J.smul_mem ((u g0)⁻¹).val hg0
              rw [← he, smul_smul] at hh
              simpa using hh
          refine ⟨b, hbJ, hb, le_antisymm ?_ (Submodule.span_le.mpr (by simpa using hbJ))⟩
          rw [← hs]
          apply Submodule.span_le.mpr
          intro g hg
          by_cases hz : g = 0
          · simp [hz]
          · let gg : G := ⟨g, Finset.mem_filter.mpr ⟨hg, hz⟩⟩
            obtain ⟨r, hr⟩ := hgb gg
            apply Submodule.mem_span_singleton.mpr
            refine ⟨r, ?_⟩
            apply (LR.cv p).injective
            simpa [sc, gg] using hr.symm
    have scaled : ∀ (f : LR.MR p M →ₗ[ℤ] V) (J : Submodule (LR.R p) (LR.C p)),
  LR.CoeffSpec p l (rho y) v M f J →
  ∀ b : ℂ, (LR.cv p).symm b ∈ J → b ≠ 0 →
  J = Submodule.span (LR.R p) {(LR.cv p).symm b} →
  LR.ScaledBasis p l (rho y) v M f b := by
      as_aux_lemma =>
        classical
          intro f J hc b hbJ hb hspan
          have sc : ∀ (r : LR.R p) (c : LR.C p),
              LR.cv p (r • c) = ((r : ℚ) : ℂ) * LR.cv p c := by
            as_aux_lemma =>
              intro r c
              change (r : ℚ) • LR.cv p c = _
              exact Rat.smul_def _ _
          let bj : J := ⟨(LR.cv p).symm b, hbJ⟩
          let T : LR.R p →ₗ[LR.R p] J := (LinearMap.id : LR.R p →ₗ[LR.R p] LR.R p).smulRight bj
          have hT : Function.Bijective T := by
            as_aux_lemma =>
              constructor
              · intro r s hrs
                have hh := congrArg (fun z : J => LR.cv p (z : LR.C p)) hrs
                change LR.cv p (r • (LR.cv p).symm b) = LR.cv p (s • (LR.cv p).symm b) at hh
                simp only [sc, (LR.cv p).apply_symm_apply] at hh
                have hr : ((r : ℚ) : ℂ) = ((s : ℚ) : ℂ) := mul_right_cancel₀ hb hh
                apply Subtype.ext
                exact_mod_cast hr
              · intro z
                have hz : (z : LR.C p) ∈ Submodule.span (LR.R p) {(LR.cv p).symm b} := by
                  as_aux_lemma =>
                    rw [← hspan]; exact z.property
                obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz
                exact ⟨r, Subtype.ext hr⟩
          let E : LR.R p ≃ₗ[LR.R p] J := LinearEquiv.ofBijective T hT
          obtain ⟨D, hD⟩ := hc.2.2.2
          let P : (LR.I l → LR.R p) ≃ₗ[LR.R p] (LR.I l → J) := LinearEquiv.piCongrRight (fun _ => E)
          let B : Module.Basis (LR.I l) (LR.R p) (LR.MR p M) :=
            (Pi.basisFun (LR.R p) (LR.I l)).map (P.trans D)
          refine ⟨B, ?_⟩
          intro i
          change f (D (P ((Pi.basisFun (LR.R p) (LR.I l)) i))) = _
          rw [hD]
          have hh : ∀ k : LR.I l,
              LR.cv p ((P ((Pi.basisFun (LR.R p) (LR.I l)) i) k : J) : LR.C p) =
              if k = i then b else 0 := by
            as_aux_lemma =>
              intro k
              change LR.cv p (T ((Pi.basisFun (LR.R p) (LR.I l)) i k) : LR.C p) = _
              change LR.cv p ((((Pi.basisFun (LR.R p) (LR.I l)) i k) : LR.R p) • (LR.cv p).symm b) = _
              rw [sc]
              by_cases hk : i = k
              · subst k; simp [Pi.basisFun_apply]
              · simp [Pi.basisFun_apply, Pi.single_apply, hk, Ne.symm hk]
          simp_rw [hh]
          simp
    intro f hf
    obtain ⟨J, hc⟩ := h_T012 f hf
    have he : LR.RationalEmbedding p J := h_T013 J hc.2.1
    have hr : Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1 := h_T015 f J hf hc
    have hm : LR.RationalMultiples p J := h_T016 J he hr
    refine ⟨J, hc, he, hr, ?_⟩
    constructor
    · exact cyclic J hc.2.1 hc.2.2.1 hm
    · exact scaled f J hc

theorem T019 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T010 : LR.N2 p l K M rho x y h v) :
    Nonempty (LR.Residue p K) := by
  classical
  letI : Fact p.Prime := ⟨h_H001.1⟩
  letI : CharP K p := h_H001.2.1
  have hR : LR.LocalRingSpec p := h_T010.1
  have hpsiExists : ∃ psi : LR.R p →+* ZMod p, ∀ (a b : ℤ) (r : LR.R p), b ≠ 0 → ¬ (p : ℤ) ∣ b → (r : ℚ) = (a : ℚ) / b → psi r = (a : ZMod p) * (b : ZMod p)⁻¹ := by
      as_aux_lemma =>
        classical
        letI : Fact p.Prime := ⟨h_H001.1⟩
        have hR : LR.LocalRingSpec p := h_T010.1
        have repr : ∀ r : LR.R p, ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ (r : ℚ) = (a : ℚ) / b :=
          fun r => (hR.1 (r : ℚ)).mp r.property
        choose A B hB hpB hval using repr
        have nz : ∀ b : ℤ, ¬ (p : ℤ) ∣ b → (b : ZMod p) ≠ 0 := by
          as_aux_lemma =>
            intro b hb
            exact fun hz => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hz)
        have frac : ∀ a b c d : ℤ, b ≠ 0 → d ≠ 0 →
            ¬ (p : ℤ) ∣ b → ¬ (p : ℤ) ∣ d →
            (a : ℚ) / b = (c : ℚ) / d →
            (a : ZMod p) / b = (c : ZMod p) / d := by
          as_aux_lemma =>
            intro a b c d hb hd hpb hpd he
            have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
            have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
            have hi : a * d = c * b := by
              as_aux_lemma =>
                exact_mod_cast (div_eq_div_iff hbq hdq).mp he
            apply (div_eq_div_iff (nz b hpb) (nz d hpd)).mpr
            have hc := congrArg (fun z : ℤ => (z : ZMod p)) hi
            simpa only [Int.cast_mul] using hc
        let g : LR.R p → ZMod p := fun r => (A r : ZMod p) / B r
        have gs : ∀ (a b : ℤ) (r : LR.R p), b ≠ 0 → ¬ (p : ℤ) ∣ b →
            (r : ℚ) = (a : ℚ) / b → g r = (a : ZMod p) / b := by
          dsimp only [g]
          as_aux_lemma =>
            intro a b r hb hpb hr
            exact frac (A r) (B r) a b (hB r) hb (hpB r) hpb ((hval r).symm.trans hr)
        have prod : ∀ r s : LR.R p, ¬ (p : ℤ) ∣ B r * B s := by
          as_aux_lemma =>
            intro r s hh
            have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (B r * B s) p).mpr hh
            have hn : (B r : ZMod p) * (B s : ZMod p) ≠ 0 := mul_ne_zero (nz _ (hpB r)) (nz _ (hpB s))
            exact hn (by simpa using hz)
        have hnotone : ¬ (p : ℤ) ∣ 1 := by
          as_aux_lemma =>
            intro hh
            have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 p).mpr hh
            simpa using hz
        let psi : LR.R p →+* ZMod p :=
          { toFun := g
            map_zero' := by simpa using gs 0 1 0 (by norm_num) hnotone (by norm_num)
            map_one' := by simpa using gs 1 1 1 (by norm_num) hnotone (by norm_num)
            map_add' := by
              as_aux_lemma =>
                intro r s
                rw [gs (A r * B s + B r * A s) (B r * B s) (r+s)
                  (mul_ne_zero (hB r) (hB s)) (prod r s) (by
                    change (r : ℚ) + (s : ℚ) = _
                    rw [hval r, hval s]
                    push_cast
                    exact div_add_div (A r : ℚ) (A s : ℚ) (by exact_mod_cast hB r) (by exact_mod_cast hB s))]
                dsimp [g]
                push_cast
                exact (div_add_div _ _ (nz _ (hpB r)) (nz _ (hpB s))).symm
            map_mul' := by
              as_aux_lemma =>
                intro r s
                rw [gs (A r * A s) (B r * B s) (r*s)
                  (mul_ne_zero (hB r) (hB s)) (prod r s) (by
                    change (r : ℚ) * (s : ℚ) = _
                    rw [hval r, hval s]
                    push_cast
                    exact div_mul_div_comm _ _ _ _)]
                dsimp [g]
                push_cast
                exact (div_mul_div_comm _ _ _ _).symm }
        refine ⟨psi, ?_⟩
        intro a b r hb hpb hr
        exact gs a b r hb hpb hr

  obtain ⟨psi, hpsi⟩ := hpsiExists
  let kappa : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  let phi : LR.R p →+* K := kappa.comp psi
  have hsurj : Function.Surjective psi := by
    as_aux_lemma =>
      intro z
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
      exact ⟨(a : LR.R p), by simp⟩
  have hker : RingHom.ker psi = Ideal.span {(p : LR.R p)} := by
    as_aux_lemma =>
      ext r
      constructor
      · intro hz
        have hz' : psi r = 0 := hz
        obtain ⟨a, b, hb, hpb, hr⟩ := (hR.1 (r : ℚ)).mp r.property
        have hbz : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
        rw [hpsi a b r hb hpb hr] at hz'
        have haz : (a : ZMod p) = 0 :=
          (mul_eq_zero.mp hz').resolve_right (inv_ne_zero hbz)
        obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp haz
        have hs : (t : ℚ) / b ∈ LR.R p := (hR.1 _).mpr ⟨t, b, hb, hpb, rfl⟩
        let s : LR.R p := ⟨(t : ℚ) / b, hs⟩
        apply Ideal.mem_span_singleton.mpr
        refine ⟨s, ?_⟩
        apply Subtype.ext
        change (r : ℚ) = (p : ℚ) * ((t : ℚ) / b)
        rw [hr, ht]
        push_cast
        ring
      · intro hr
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
        change psi r = 0
        rw [hs, map_mul]
        simp
  have heps : ∃ e : (LR.R p) ⧸ RingHom.ker psi ≃+* ZMod p,
      ∀ r : LR.R p, e (Ideal.Quotient.mk (RingHom.ker psi) r) = psi r := by
    as_aux_lemma =>
      exact ⟨psi.quotientKerEquivOfSurjective hsurj, fun r => rfl⟩
  rw [hker] at heps
  obtain ⟨eps, heps⟩ := heps
  refine ⟨{
    phi := phi
    psi := psi
    kappa := kappa
    phi_fraction := ?_
    psi_fraction := hpsi
    kappa_int := ?_
    compatible := rfl
    psi_surjective := hsurj
    psi_kernel := hker
    eps := eps
    eps_spec := heps
    units_nonzero := ?_
  }⟩
  · intro a b r hb hpb hr
    change kappa (psi r) = _
    rw [hpsi a b r hb hpb hr]
    simp
  · intro a
    exact map_intCast kappa a
  · intro u
    exact (u.isUnit.map phi).ne_zero

theorem T020 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) :
    ∀ Q : LR.Residue p K, LR.Bridge p K M Q := by
  intro Q
  letI := Q.phi.toAlgebra
  letI := Q.kappa.toAlgebra
  letI : CharP K p := h_H001.2.1
  have hmk : ∀ (r : LR.R p) (z : LR.MR p M), ModN.mkQ p (r • z) = Q.psi r • ModN.mkQ p z := by
    as_aux_lemma =>
      have hpz : ∀ z : LR.MR p M, p • ModN.mkQ p z = 0 := by
        as_aux_lemma =>
          intro z
          have hz := (ModN.liftEquiv (AddMonoidHom.id (ModN (LR.MR p M) p))).property z
          exact hz
      intro r z
      obtain ⟨a, ha⟩ := ZMod.intCast_surjective (Q.psi r)
      have hmem : r - (a : LR.R p) ∈ Ideal.span {(p : LR.R p)} := by
        as_aux_lemma =>
          rw [← Q.psi_kernel, RingHom.mem_ker]
          simp [ha]
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hmem
      have hr : r = (a : LR.R p) + (p : LR.R p) * s := by
        as_aux_lemma =>
          rw [← hs]; ring
      rw [hr, add_smul, map_add, mul_smul]
      have hk : ModN.mkQ p ((p : LR.R p) • s • z) = 0 := by
        as_aux_lemma =>
          simpa only [Nat.cast_smul_eq_nsmul, map_nsmul] using hpz (s • z)
      rw [hk, add_zero, ← hr, ← ha]
      simp only [Int.cast_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]

  let T := K ⊗[LR.R p] LR.MR p M
  let U := K ⊗[ZMod p] ModN (LR.MR p M) p
  have hpT : ∀ z : T, p • z = 0 := by
    as_aux_lemma =>
      intro z
      rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]
  let iq : ModN (LR.MR p M) p →ₗ[ZMod p] T :=
    ModN.liftEquiv'.symm ⟨(TensorProduct.mk (LR.R p) K (LR.MR p M) 1).toAddMonoidHom, fun z => hpT _⟩
  have hiq (z : LR.MR p M) : iq (ModN.mkQ p z) = 1 ⊗ₜ[LR.R p] z := by rfl
  let di : U →ₗ[K] T := iq.liftBaseChange K
  have hdi (c : K) (z : LR.MR p M) : di (c ⊗ₜ[ZMod p] ModN.mkQ p z) = c ⊗ₜ[LR.R p] z := by
    as_aux_lemma =>
      change iq.liftBaseChange K (c ⊗ₜ[ZMod p] ModN.mkQ p z) = _
      rw [LinearMap.liftBaseChange_tmul, hiq]
      change (c * 1) ⊗ₜ[LR.R p] z = _
      rw [mul_one]
  let fq : LR.MR p M →ₗ[LR.R p] U :=
    { toFun := fun z => 1 ⊗ₜ[ZMod p] ModN.mkQ p z
      map_add' := by intro z w; simp [TensorProduct.tmul_add]
      map_smul' := by
        as_aux_lemma =>
          intro r z
          dsimp
          rw [hmk, ← TensorProduct.smul_tmul]
          change (Q.kappa (Q.psi r) * 1) ⊗ₜ[ZMod p] ModN.mkQ p z =
            (Q.phi r * 1) ⊗ₜ[ZMod p] ModN.mkQ p z
          rw [Q.compatible]
          rfl }
  let df : T →ₗ[K] U := fq.liftBaseChange K
  have hdf (c : K) (z : LR.MR p M) : df (c ⊗ₜ[LR.R p] z) = c ⊗ₜ[ZMod p] ModN.mkQ p z := by
    as_aux_lemma =>
      change fq.liftBaseChange K (c ⊗ₜ[LR.R p] z) = _
      rw [LinearMap.liftBaseChange_tmul]
      change (c * 1) ⊗ₜ[ZMod p] ModN.mkQ p z = _
      rw [mul_one]

  have hid : di.comp df = LinearMap.id := by
    as_aux_lemma =>
      apply LinearMap.ext
      intro w
      change di (df w) = w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul c z => rw [hdf, hdi]
      | add z w hz hw => rw [map_add, map_add, hz, hw]
  have hfd : df.comp di = LinearMap.id := by
    as_aux_lemma =>
      apply LinearMap.ext
      intro w
      change df (di w) = w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul c q =>
        obtain ⟨z, hz⟩ := (Submodule.mkQ_surjective (LinearMap.range (LinearMap.lsmul ℤ (LR.MR p M) p))) q
        change ModN.mkQ p z = q at hz
        rw [← hz, hdi, hdf]
      | add z w hz hw => rw [map_add, map_add, hz, hw]
  let D : T ≃ₗ[K] U := LinearEquiv.ofLinear df di hfd hid
  have hD : LR.DeltaPure p K M D := ⟨hdf, hdi⟩
  let G : LR.VK K M ≃ₗ[K] K ⊗[LR.R p] LR.MR p M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (LR.R p) K K M).symm
  refine ⟨G, D, ⟨?_, ?_⟩, hD, ?_, ?_⟩
  · intro c m
    exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul _ _ _ _ _
  · intro c r m
    change (r • c) ⊗ₜ[ℤ] m = _
    rfl
  · intro F z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp [G]
    | add z w hz hw => simp [hz, hw]
  · intro F
    have hpz : ∀ z : LR.MR p M, p • ModN.mkQ p z = 0 := by
      as_aux_lemma =>
        intro z
        exact (ModN.liftEquiv (AddMonoidHom.id (ModN (LR.MR p M) p))).property z
    let Fb : Module.End (ZMod p) (ModN (LR.MR p M) p) :=
      ModN.liftEquiv'.symm ⟨(ModN.mkQ p).comp F.toAddMonoidHom, fun z => hpz (F z)⟩
    have hFb (z : LR.MR p M) : Fb (ModN.mkQ p z) = ModN.mkQ p (F z) := by rfl
    refine ⟨Fb, hFb, ?_⟩
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c w =>
      change df (F.baseChange K (c ⊗ₜ[LR.R p] w)) =
        Fb.baseChange K (df (c ⊗ₜ[LR.R p] w))
      rw [LinearMap.baseChange_tmul, hdf, hdf, LinearMap.baseChange_tmul, hFb]
    | add z w hz hw => simp [hz, hw]

theorem T021 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_T020 : ∀ Q : LR.Residue p K, LR.Bridge p K M Q) :
    ∀ Q : LR.Residue p K, LR.Transfer p l K M (rho y) v Q := by
  intro Q
  letI := Q.phi.toAlgebra
  letI := Q.kappa.toAlgebra
  rcases h_T020 Q with ⟨G, D, hG, hD, hFG, hFD⟩
  dsimp only [LR.Transfer]
  intro f b hf hB
  rcases hB with ⟨B, hB⟩
  let beta : Module.Basis (LR.I l) K (LR.VK K M) := (B.baseChange K).map G.symm
  refine ⟨G, B, beta, hG, hB, ?_, ?_⟩
  · intro i
    simp only [beta, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  · simpa only [LR.I, Fintype.card_fin] using Module.finrank_eq_card_basis beta

theorem T022 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) (h_T010 : LR.N2 p l K M rho x y h v) :
    ∀ Q : LR.Residue p K, LR.MatrixTransport p l K M rho x y h v Q := by
  classical
  intro Q
  letI := Q.phi.toAlgebra
  intro A f b G B beta hf hinj hb hG hB hbeta
  have transport : ∀ (F : Module.End ℂ V) (g : Module.End K (LR.VK K M)),
      LR.Lift K M F g → ∀ (z w : LR.MR p M) (c : ℤ),
      F (f z) = (c : ℂ) • f w →
      g (G.symm (1 ⊗ₜ[LR.R p] z)) = (c : K) • G.symm (1 ⊗ₜ[LR.R p] w) := by
    as_aux_lemma =>
      intro F g hg z w c he
      rcases hg with ⟨fm, hfm, hgm⟩
      let FR : Module.End (LR.R p) (LR.MR p M) := fm.baseChange (LR.R p)
      have hFR : ∀ z : LR.MR p M, f (FR z) = F (f z) := by
        as_aux_lemma =>
          intro z
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul r m =>
            simp only [FR, LinearMap.baseChange_tmul, hf.1, hfm, map_smul]
          | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
      have hcomm : ∀ z : LR.MR p M, g (G.symm (1 ⊗ₜ[LR.R p] z)) = G.symm (1 ⊗ₜ[LR.R p] FR z) := by
        as_aux_lemma =>
          intro z
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul r m => simp only [FR, LinearMap.baseChange_tmul, hG.2, mul_one, hgm]
          | add z w hz hw => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hw
      have hz : FR z = c • w := hinj (by rw [hFR, he]; simp [Int.cast_smul_eq_zsmul])
      rw [hcomm, hz]
      simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_zsmul, Int.cast_smul_eq_zsmul]
  have ht : ∀ (F : Module.End ℂ V) (g : Module.End K (LR.VK K M)),
      LR.Lift K M F g → ∀ (i j : LR.I l) (c : ℤ),
      F (LR.eNat (rho y) v i.val) = (c : ℂ) • LR.eNat (rho y) v j.val →
      g (beta i) = (c : K) • beta j := by
    as_aux_lemma =>
      intro F g hg i j c he
      rw [hbeta i, hbeta j]
      apply transport F g hg (B i) (B j) c
      rw [hB i, hB j, map_smul, he, smul_comm]
  have ht0 : ∀ (F : Module.End ℂ V) (g : Module.End K (LR.VK K M)),
      LR.Lift K M F g → ∀ i : LR.I l,
      F (LR.eNat (rho y) v i.val) = 0 → g (beta i) = 0 := by
    as_aux_lemma =>
      intro F g hg i he
      simpa using ht F g hg i i 0 (by simpa using he)
  have hext : ∀ (i : ℕ) (hi : i ≤ l.toNat),
      LR.extend l beta i = beta ⟨i, by omega⟩ := by
    as_aux_lemma =>
      intro i hi
      simp [LR.extend, show i < l.toNat+1 by omega]
  have hm := h_T005.2.2.2.2.1
  have matrices : LR.Matrices l A.a A.d A.t (LR.extend l beta) := by
    as_aux_lemma =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hext 0 (Nat.zero_le _)]
        exact ht0 _ _ A.a_spec ⟨0, by omega⟩ hm.1
      · intro i hi hil
        rw [hext i hil, hext (i-1) (by omega)]
        convert ht _ _ A.a_spec ⟨i, by omega⟩ ⟨i-1, by omega⟩ (l - (i : ℤ) + 1) (by
          simpa only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one] using hm.2.1 i hi hil) using 1 <;> push_cast <;> rfl
      · intro i hi
        rw [hext i (by omega), hext (i+1) (by omega)]
        convert ht _ _ A.d_spec ⟨i, by omega⟩ ⟨i+1, by omega⟩ ((i : ℤ)+1) (by
          simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hm.2.2.1 i hi) using 1 <;> push_cast <;> rfl
      · rw [hext l.toNat (le_refl _)]
        exact ht0 _ _ A.d_spec ⟨l.toNat, by omega⟩ hm.2.2.2.1
      · intro i hi
        rw [hext i hi]
        convert ht _ _ A.t_spec ⟨i, by omega⟩ ⟨i, by omega⟩ (l - 2*(i : ℤ)) (by
          simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hm.2.2.2.2 i hi) using 1 <;> push_cast <;> rfl
  have mkLift : ∀ (F : Module.End ℂ V), (∀ m ∈ M, F m ∈ M) →
      ∃ g : Module.End K (LR.VK K M), LR.Lift K M F g := by
    as_aux_lemma =>
      intro F hF
      let fm : Module.End ℤ M := (F.restrictScalars ℤ).restrict hF
      exact ⟨fm.baseChange K, fm, (fun _ => rfl), (fun _ _ => rfl)⟩
  rcases h_T010.2.2.2 with ⟨f0, hf0, hl0, hp0, hu0⟩
  have divided : LR.DividedLiftMatrices l K M (rho x) (rho y) beta := by
    as_aux_lemma =>
      intro r
      obtain ⟨xr, hxr⟩ := mkLift (LR.dp (rho x) r) (fun m hm => (hp0.1 r m hm).1)
      obtain ⟨yr, hyr⟩ := mkLift (LR.dp (rho y) r) (fun m hm => (hp0.1 r m hm).2)
      refine ⟨xr, yr, hxr, hyr, ?_⟩
      intro i
      have hi : i.val ≤ l.toNat := by have := i.isLt; omega
      obtain ⟨hx, hy⟩ := h_T005.2.2.2.2.2 r i.val hi
      constructor
      · by_cases hr : r ≤ i.val
        · rw [if_pos hr, hext (i.val-r) (by omega)]
          simpa only [Int.cast_natCast] using
            ht _ _ hxr i ⟨i.val-r, by omega⟩ (Nat.choose (l.toNat-i.val+r) r : ℤ)
              (by simpa only [if_pos hr, Int.cast_natCast] using hx)
        · rw [if_neg hr]
          apply ht0 _ _ hxr i
          simpa only [if_neg hr] using hx
      · by_cases hr : i.val+r ≤ l.toNat
        · rw [if_pos hr, hext (i.val+r) hr]
          simpa only [Int.cast_natCast] using
            ht _ _ hyr i ⟨i.val+r, by omega⟩ (Nat.choose (i.val+r) r : ℤ)
              (by simpa only [if_pos hr, Int.cast_natCast] using hy)
        · rw [if_neg hr]
          apply ht0 _ _ hyr i
          simpa only [if_neg hr] using hy
  exact ⟨matrices, divided⟩

theorem T023 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T010 : LR.N2 p l K M rho x y h v) (h_T019 : Nonempty (LR.Residue p K)) :
    LR.SmallPowers l K M rho x y h := by
  classical
  have lift_divided : ∀ (f : Module.End ℂ V) (g : Module.End K (LR.VK K M)) (r : ℕ), LR.Lift K M f g → (∀ m ∈ M, LR.dp f r m ∈ M) → (r.factorial : K) ≠ 0 → LR.Lift K M (LR.dp f r) (((r.factorial : K)⁻¹) • g^r) := by
    as_aux_lemma =>
      intro f g r hg hp hn
      rcases hg with ⟨fm, hfm, hgm⟩
      let F : Module.End ℤ M :=
        LinearMap.codRestrict M (((LR.dp f r).restrictScalars ℤ).comp M.subtype)
          (fun m => hp m m.property)
      have hF : ∀ m : M, (F m : V) = LR.dp f r (m : V) := fun m => rfl
      have hpow : ∀ (n : ℕ) (m : M), ((fm ^ n) m : V) = (f ^ n) (m : V) := by
        as_aux_lemma =>
          intro n
          induction n with
          | zero => intro m; rfl
          | succ n ih =>
            intro m
            simp only [pow_succ', Module.End.mul_apply]
            rw [hfm, ih]
      have hfact : (r.factorial : ℤ) • F = fm ^ r := by
        as_aux_lemma =>
          apply LinearMap.ext
          intro m
          apply Subtype.ext
          change (r.factorial : ℤ) • (F m : V) = ((fm ^ r) m : V)
          rw [hF, hpow]
          simp [LR.dp, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)]
      have hbase : fm.baseChange K = g := by
        as_aux_lemma =>
          ext m
          exact (hgm 1 m).symm
      have hbc : (r.factorial : K) • F.baseChange K = g ^ r := by
        as_aux_lemma =>
          have he := congrArg (fun u : Module.End ℤ M => u.baseChange K) hfact
          rw [LinearMap.baseChange_smul, LinearMap.baseChange_pow, hbase] at he
          simpa only [Nat.cast_smul_eq_nsmul] using he
      have heq : F.baseChange K = ((r.factorial : K)⁻¹) • g ^ r := by
        as_aux_lemma =>
          rw [← hbc, smul_smul, inv_mul_cancel₀ hn, one_smul]
      refine ⟨F, hF, ?_⟩
      intro c m
      rw [← heq]
      exact LinearMap.baseChange_tmul F c m
  intro A r hr
  rcases h_T019 with ⟨Q⟩
  have hu : IsUnit (r.factorial : LR.R p) := (h_T010.2.1.1 r hr).2
  have hk : IsUnit (r.factorial : K) := by
    as_aux_lemma =>
      simpa using hu.map Q.phi
  have hn : (r.factorial : K) ≠ 0 := hk.ne_zero
  rcases h_T010.2.2.2 with ⟨f, hf, hb, hp, hunit⟩
  refine ⟨hn, ?_, ?_⟩
  · exact lift_divided (rho x) A.a r A.a_spec
      (fun m hm => (hp.1 r m hm).1) hn
  · exact lift_divided (rho y) A.d r A.d_spec
      (fun m hm => (hp.1 r m hm).2) hn

theorem T024 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) (h_T010 : LR.N2 p l K M rho x y h v) (h_T022 : ∀ Q : LR.Residue p K, LR.MatrixTransport p l K M rho x y h v Q) (h_T023 : LR.SmallPowers l K M rho x y h) :
    ∀ Q : LR.Residue p K, LR.PolynomialTransport p l K M rho x y h v Q := by
  classical
  have hcomplex : ∀ (b0 : Module.Basis (LR.I l) ℂ V), LR.BasisSpec l (rho y) v b0 →
  ∀ i j k : LR.I l,
   (LR.dp (rho x) (l.toNat-i.val) * LR.dp (rho y) l.toNat *
    LR.dp (rho x) l.toNat * LR.dp (rho y) (l.toNat-j.val)) (LR.eNat (rho y) v k.val) =
   (Nat.choose l.toNat j.val : ℂ) • (if k = j then LR.eNat (rho y) v i.val else 0) := by
    as_aux_lemma =>
      classical
      intro b0 hb i j k
      rcases h_T010 with ⟨_, _, _, f0, hf0, hloc, hpres, hall⟩
      have hunit := (hall b0 hb).2 i j |>.1
      have hc : (Nat.choose l.toNat j.val : ℂ) ≠ 0 := by
        as_aux_lemma =>
          exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)).ne'
      have hp :
        LR.dp (rho x) (l.toNat-i.val) * LR.dp (rho y) l.toNat *
        LR.dp (rho x) l.toNat * LR.dp (rho y) (l.toNat-j.val) =
        (Nat.choose l.toNat j.val : ℂ) • LR.unit l b0 i j := by
        as_aux_lemma =>
          rw [hunit, smul_smul, mul_inv_cancel₀ hc, one_smul]
          simp only [mul_assoc]
      rw [hp, LinearMap.smul_apply, ← hb k]
      congr 1
      by_cases hk : k = j
      · subst k
        simpa [LR.unit] using hb i
      · simp [LR.unit, hk, Ne.symm hk]
  intro Q
  letI := Q.phi.toAlgebra
  intro A f b G B beta hf hfinj hb hG hB hbeta
  have htransport : ∀ (s : Module.End ℂ V) (u : Module.End K (LR.VK K M)), LR.Lift K M s u →
      ∃ F : Module.End (LR.R p) (LR.MR p M),
        (∀ z, f (F z) = s (f z)) ∧
        (∀ z, u (G.symm (1 ⊗ₜ[LR.R p] z)) =
          G.symm (1 ⊗ₜ[LR.R p] F z)) := by
    as_aux_lemma =>
      intro s u hu
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
  rcases h_T005.2.2.2.1 with ⟨b0, hb0, _⟩
  intro i j
  have hc : (Nat.choose l.toNat j.val : K) ≠ 0 := by
    as_aux_lemma =>
      rcases h_T010.2.1.2 j with ⟨u, hu⟩
      have hn := Q.units_nonzero u
      rw [hu] at hn
      simpa using hn
  refine ⟨hc, ?_⟩
  intro k
  obtain ⟨Fi, hfi, hgi⟩ := htransport _ _ (h_T023 A (l.toNat-i.val) (Nat.sub_le _ _)).2.1
  obtain ⟨Fd, hfd, hgd⟩ := htransport _ _ (h_T023 A l.toNat le_rfl).2.2
  obtain ⟨Fa, hfa, hga⟩ := htransport _ _ (h_T023 A l.toNat le_rfl).2.1
  obtain ⟨Fj, hfj, hgj⟩ := htransport _ _ (h_T023 A (l.toNat-j.val) (Nat.sub_le _ _)).2.2
  have hlocal : Fi (Fd (Fa (Fj (B k)))) =
      (Nat.choose l.toNat j.val) • (if k = j then B i else 0) := by
    as_aux_lemma =>
      apply hfinj
      calc
        f (Fi (Fd (Fa (Fj (B k))))) =
            (LR.dp (rho x) (l.toNat-i.val) * LR.dp (rho y) l.toNat *
              LR.dp (rho x) l.toNat * LR.dp (rho y) (l.toNat-j.val)) (f (B k)) := by
          as_aux_lemma =>
            simp only [hfi, hfd, hfa, hfj, Module.End.mul_apply]
        _ = b • ((Nat.choose l.toNat j.val : ℂ) •
            (if k = j then LR.eNat (rho y) v i.val else 0)) := by
          as_aux_lemma =>
            rw [hB, map_smul, hcomplex b0 hb0 i j k]
        _ = f ((Nat.choose l.toNat j.val) • (if k = j then B i else 0)) := by
          as_aux_lemma =>
            by_cases hk : k = j
            · simp only [if_pos hk, map_nsmul, hB, ← Nat.cast_smul_eq_nsmul ℂ]
              exact smul_comm _ _ _
            · simp only [if_neg hk, smul_zero, map_zero]
  have hred :
      (((((l.toNat-i.val).factorial : K)⁻¹) • A.a^(l.toNat-i.val)) *
        (((l.toNat.factorial : K)⁻¹) • A.d^l.toNat) *
        (((l.toNat.factorial : K)⁻¹) • A.a^l.toNat) *
        (((((l.toNat-j.val).factorial : K)⁻¹) • A.d^(l.toNat-j.val)))) (beta k) =
      (Nat.choose l.toNat j.val : K) • (if k = j then beta i else 0) := by
    as_aux_lemma =>
      rw [hbeta k]
      simp only [Module.End.mul_apply, hgj, hga, hgd, hgi]
      rw [hlocal]
      by_cases hk : k = j <;>
        simp [hk, hbeta i, TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul]
  change (Nat.choose l.toNat j.val : K)⁻¹ •
      (((((l.toNat-i.val).factorial : K)⁻¹) • A.a^(l.toNat-i.val)) *
        (((l.toNat.factorial : K)⁻¹) • A.d^l.toNat) *
        (((l.toNat.factorial : K)⁻¹) • A.a^l.toNat) *
        (((((l.toNat-j.val).factorial : K)⁻¹) • A.d^(l.toNat-j.val)))) (beta k) = _
  rw [hred, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem T025 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T010 : LR.N2 p l K M rho x y h v) (h_T018 : LR.N3 p l (rho y) v M) (h_T019 : Nonempty (LR.Residue p K)) (h_T020 : ∀ Q : LR.Residue p K, LR.Bridge p K M Q) (h_T021 : ∀ Q : LR.Residue p K, LR.Transfer p l K M (rho y) v Q) (h_T022 : ∀ Q : LR.Residue p K, LR.MatrixTransport p l K M rho x y h v Q) (h_T023 : LR.SmallPowers l K M rho x y h) (h_T024 : ∀ Q : LR.Residue p K, LR.PolynomialTransport p l K M rho x y h v Q) :
    LR.N4 p l K M rho x y h v := by
  classical
  rcases h_T019 with ⟨Q⟩
  refine ⟨Q, h_T020 Q, ?_⟩
  letI := Q.phi.toAlgebra
  intro A
  rcases h_T010 with ⟨hlocal, hsmall, hact, f, hf, hfb, hpres, hunits⟩
  rcases h_T018 f hf with ⟨J, hcoeff, hrat, hrank, hcyclic⟩
  rcases hcyclic.1 with ⟨b, hbJ, hb, hJ⟩
  have hscaled := hcyclic.2 b hbJ hb hJ
  rcases h_T021 Q f b hf hscaled with ⟨G, B, beta, hG, hB, hbeta, hdim⟩
  have hmat := (h_T022 Q A f b G B beta hf hfb.1 hb hG hB hbeta).1
  have hpoly := h_T024 Q A f b G B beta hf hfb.1 hb hG hB hbeta
  refine ⟨f, J, b, G, B, beta, hf, hfb.1, hcoeff, hbJ, hb, hJ, hG, hB, hbeta, ?_⟩
  exact ⟨hdim, hmat, h_T023 A, hpoly⟩

theorem T026 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V)  :
    ∀ (A : LR.Action K M rho x y h) (W : Submodule K (LR.VK K M)), LR.Stable W A.a → LR.Stable W A.d → ∀ i j : LR.I l, LR.Stable W (LR.polynomial l A.a A.d i j) := by
  intro A W ha hd
  have hmul (f g : Module.End K (LR.VK K M))
      (hf : LR.Stable W f) (hg : LR.Stable W g) : LR.Stable W (f * g) := by
    intro w hw
    exact hf (g w) (hg w hw)
  have hsmul (c : K) (f : Module.End K (LR.VK K M))
      (hf : LR.Stable W f) : LR.Stable W (c • f) := by
    intro w hw
    exact W.smul_mem c (hf w hw)
  have hpow (f : Module.End K (LR.VK K M)) (hf : LR.Stable W f)
      (n : ℕ) : LR.Stable W (f ^ n) := by
    induction n with
    | zero =>
        intro w hw
        simpa using hw
    | succ n ih =>
        rw [pow_succ]
        exact hmul (f ^ n) f ih hf
  intro i j
  unfold LR.polynomial
  apply hsmul
  apply hmul
  · apply hmul
    · apply hmul
      · exact hsmul _ _ (hpow A.a ha _)
      · exact hsmul _ _ (hpow A.d hd _)
    · exact hsmul _ _ (hpow A.a ha _)
  · exact hsmul _ _ (hpow A.d hd _)

theorem T027 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V)  :
    ∀ (beta : Module.Basis (LR.I l) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), W ≠ ⊥ → ∃ (w : LR.VK K M) (c : LR.I l → K) (j : LR.I l), w ∈ W ∧ w ≠ 0 ∧ w = ∑ i, c i • beta i ∧ c j ≠ 0 := by
  classical
  intro beta W hW
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hexp : w = ∑ i, beta.repr w i • beta i := (beta.sum_repr w).symm
  have hcoeff : ∃ j : LR.I l, beta.repr w j ≠ 0 := by
    by_contra hn
    have hz : ∀ i : LR.I l, beta.repr w i = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    apply hw0
    simpa only [hz, zero_smul, Finset.sum_const_zero] using hexp
  obtain ⟨j, hj⟩ := hcoeff
  exact ⟨w, (fun i => beta.repr w i), j, hwW, hw0, hexp, hj⟩

theorem T028 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_T027 : ∀ (beta : Module.Basis (LR.I l) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), W ≠ ⊥ → ∃ (w : LR.VK K M) (c : LR.I l → K) (j : LR.I l), w ∈ W ∧ w ≠ 0 ∧ w = ∑ i, c i • beta i ∧ c j ≠ 0) :
    ∀ (A : LR.Action K M rho x y h) (beta : Module.Basis (LR.I l) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), (∀ i j k : LR.I l, LR.polynomial l A.a A.d i j (beta k) = if k = j then beta i else 0) → (∀ i j : LR.I l, LR.Stable W (LR.polynomial l A.a A.d i j)) → W ≠ ⊥ → W = ⊤ := by
  classical
  intro A beta W hmatrix hstable hW
  obtain ⟨w, c, j, hw, hw0, hwexp, hcj⟩ := h_T027 beta W hW
  apply (Submodule.eq_top_iff_forall_basis_mem beta).2
  intro i
  have hcalc : LR.polynomial l A.a A.d i j w = c j • beta i := by
    rw [hwexp, map_sum]
    simp only [map_smul, hmatrix]
    simp
  have hmem : c j • beta i ∈ W := by
    rw [← hcalc]
    exact hstable i j w hw
  have hcancel := W.smul_mem (c j)⁻¹ hmem
  simpa only [smul_smul, inv_mul_cancel₀ hcj, one_smul] using hcancel

theorem T029 (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_T005 : LR.N1 l (rho x) (rho y) (rho h) v) (h_T010 : LR.N2 p l K M rho x y h v) (h_T025 : LR.N4 p l K M rho x y h v) (h_T026 : ∀ (A : LR.Action K M rho x y h) (W : Submodule K (LR.VK K M)), LR.Stable W A.a → LR.Stable W A.d → ∀ i j : LR.I l, LR.Stable W (LR.polynomial l A.a A.d i j)) (h_T028 : ∀ (A : LR.Action K M rho x y h) (beta : Module.Basis (LR.I l) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), (∀ i j k : LR.I l, LR.polynomial l A.a A.d i j (beta k) = if k = j then beta i else 0) → (∀ i j : LR.I l, LR.Stable W (LR.polynomial l A.a A.d i j)) → W ≠ ⊥ → W = ⊤) :
    LR.Target K M rho x y h := by
  classical
  obtain ⟨A⟩ := h_T010.2.2.1
  rcases h_T025 with ⟨Q, hbridge, hpackage⟩
  letI := Q.phi.toAlgebra
  rcases hpackage A with
    ⟨f, J, b, G, B, beta, hf, hinj, hcoeff, hbmem, hb, hJ, hG, hB, hbeta, hspec⟩
  refine ⟨?_, A, ?_⟩
  · exact ⟨⟨beta (Fin.last l.toNat), 0, beta.ne_zero (Fin.last l.toNat)⟩⟩
  · intro W ha hd ht
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · exact Or.inr (h_T028 A beta W
        (fun i j k => (hspec.2.2.2 i j).2 k)
        (h_T026 A W ha hd) hW)

set_option Elab.async false in
theorem P (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : LR.ComplexHyp l rho x y h) (h_H003 : v ≠ 0 ∧ rho x v = 0 ∧ rho h v = (l : ℂ) • v) (h_H004 : LR.Admissible rho x y M) :
    LR.Target K M rho x y h := by
  have h_T001 : LR.Strings l (rho x) (rho y) (rho h) v := @T001 K fieldK V addV modV p l M rho x y h v h_H001 h_H002 h_H003
  have h_T002 : (∀ i : LR.I l, LR.eNat (rho y) v i.val ≠ 0) ∧ LinearIndependent ℂ (fun i : LR.I l => LR.eNat (rho y) v i.val) := @T002 K fieldK V addV modV p l M rho x y h v h_H001 h_H003 h_T001
  have h_T003 : LR.BasisString l (rho y) v := @T003 K fieldK V addV modV p l M rho x y h v h_H001 h_H002 h_T001 h_T002
  have h_T004 : LR.Matrices l (rho x) (rho y) (rho h) (LR.eNat (rho y) v) := @T004 K fieldK V addV modV p l M rho x y h v h_H001 h_H003 h_T001 h_T003
  have h_T005 : LR.N1 l (rho x) (rho y) (rho h) v := @T005 K fieldK V addV modV p l M rho x y h v h_H001 h_T001 h_T003 h_T004
  have h_T006 : LR.LocalRingSpec p ∧ ∃ (m : Module.Basis (LR.I l) ℤ M) (bc : Module.Basis (LR.I l) ℂ V), ∀ i, (m i : V) = bc i := @T006 K fieldK V addV modV p l M rho x y h v h_H001 h_H002 h_H004 h_T005
  have h_T007 : Nonempty (LR.Action K M rho x y h) ∧ ∃ f : LR.MR p M →ₗ[ℤ] V, LR.IotaSpec p M f ∧ LR.LocalBasis p l M f ∧ LR.Preserved p M f (rho x) (rho y) := @T007 K fieldK V addV modV p l M rho x y h v h_H002 h_H004 h_T006
  have h_T008 : LR.SmallUnits p l := @T008 K fieldK V addV modV p l M rho x y h v h_H001 h_T006
  have h_T009 : ∀ b : Module.Basis (LR.I l) ℂ V, LR.BasisSpec l (rho y) v b → LR.UnitIdentities l (rho x) (rho y) b := @T009 K fieldK V addV modV p l M rho x y h v h_H001 h_T005
  have h_T010 : LR.N2 p l K M rho x y h v := @T010 K fieldK V addV modV p l M rho x y h v h_H001 h_T005 h_T006 h_T007 h_T008 h_T009
  have h_T011 : ∀ (r : LR.R p) (c : LR.C p), LR.cv p (r • c) = (((r : ℚ) : ℂ)) * LR.cv p c := @T011 K fieldK V addV modV p l M rho x y h v 
  have h_T012 : ∀ f : LR.MR p M →ₗ[ℤ] V, LR.IotaSpec p M f → ∃ J : Submodule (LR.R p) (LR.C p), LR.CoeffSpec p l (rho y) v M f J := @T012 K fieldK V addV modV p l M rho x y h v h_H001 h_T005 h_T010 h_T011
  have h_T013 : ∀ J : Submodule (LR.R p) (LR.C p), J.FG → LR.RationalEmbedding p J := @T013 K fieldK V addV modV p l M rho x y h v h_T011
  have h_T014 : Module.finrank ℚ (ℚ ⊗[LR.R p] LR.MR p M) = l.toNat+1 := @T014 K fieldK V addV modV p l M rho x y h v h_T010
  have h_T015 : ∀ (f : LR.MR p M →ₗ[ℤ] V) (J : Submodule (LR.R p) (LR.C p)), LR.IotaSpec p M f → LR.CoeffSpec p l (rho y) v M f J → Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1 := @T015 K fieldK V addV modV p l M rho x y h v h_H001 h_T013 h_T014
  have h_T016 : ∀ J : Submodule (LR.R p) (LR.C p), LR.RationalEmbedding p J → Module.finrank ℚ (ℚ ⊗[LR.R p] J) = 1 → LR.RationalMultiples p J := @T016 K fieldK V addV modV p l M rho x y h v 
  have h_T017 : LR.PDecomposition p := @T017 K fieldK V addV modV p l M rho x y h v h_H001 h_T010
  have h_T018 : LR.N3 p l (rho y) v M := @T018 K fieldK V addV modV p l M rho x y h v h_H001 h_T005 h_T010 h_T012 h_T013 h_T015 h_T016 h_T017
  have h_T019 : Nonempty (LR.Residue p K) := @T019 K fieldK V addV modV p l M rho x y h v h_H001 h_T010
  have h_T020 : ∀ Q : LR.Residue p K, LR.Bridge p K M Q := @T020 K fieldK V addV modV p l M rho x y h v h_H001
  have h_T021 : ∀ Q : LR.Residue p K, LR.Transfer p l K M (rho y) v Q := @T021 K fieldK V addV modV p l M rho x y h v h_T020
  have h_T022 : ∀ Q : LR.Residue p K, LR.MatrixTransport p l K M rho x y h v Q := @T022 K fieldK V addV modV p l M rho x y h v h_H001 h_T005 h_T010
  have h_T023 : LR.SmallPowers l K M rho x y h := @T023 K fieldK V addV modV p l M rho x y h v h_H001 h_T010 h_T019
  have h_T024 : ∀ Q : LR.Residue p K, LR.PolynomialTransport p l K M rho x y h v Q := @T024 K fieldK V addV modV p l M rho x y h v h_H001 h_T005 h_T010 h_T022 h_T023
  have h_T025 : LR.N4 p l K M rho x y h v := @T025 K fieldK V addV modV p l M rho x y h v h_H001 h_T010 h_T018 h_T019 h_T020 h_T021 h_T022 h_T023 h_T024
  have h_T026 : ∀ (A : LR.Action K M rho x y h) (W : Submodule K (LR.VK K M)), LR.Stable W A.a → LR.Stable W A.d → ∀ i j : LR.I l, LR.Stable W (LR.polynomial l A.a A.d i j) := @T026 K fieldK V addV modV p l M rho x y h v 
  have h_T027 : ∀ (beta : Module.Basis (LR.I l) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), W ≠ ⊥ → ∃ (w : LR.VK K M) (c : LR.I l → K) (j : LR.I l), w ∈ W ∧ w ≠ 0 ∧ w = ∑ i, c i • beta i ∧ c j ≠ 0 := @T027 K fieldK V addV modV p l M rho x y h v 
  have h_T028 : ∀ (A : LR.Action K M rho x y h) (beta : Module.Basis (LR.I l) K (LR.VK K M)) (W : Submodule K (LR.VK K M)), (∀ i j k : LR.I l, LR.polynomial l A.a A.d i j (beta k) = if k = j then beta i else 0) → (∀ i j : LR.I l, LR.Stable W (LR.polynomial l A.a A.d i j)) → W ≠ ⊥ → W = ⊤ := @T028 K fieldK V addV modV p l M rho x y h v h_T027
  have h_T029 : LR.Target K M rho x y h := @T029 K fieldK V addV modV p l M rho x y h v h_H001 h_T005 h_T010 h_T025 h_T026 h_T028
  exact h_T029

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : LR.ComplexHyp l rho x y h) (h_H003 : v ≠ 0 ∧ rho x v = 0 ∧ rho h v = (l : ℂ) • v) (h_H004 : LR.Admissible rho x y M) : LR.Target K M rho x y h := by
  exact @Translation.P.{_, _} K fieldK V addV modV p l M rho x y h v h_H001 h_H002 h_H003 h_H004

#check @P
#print axioms P
end AuditBExport

/- Trusted inspector appended after the generated proof, never a worker tool.
   Its only substitution is an array of escaped (id, selector, expected type) strings. -/
namespace NL2LeanAuditProbe
open Lean Meta Elab Command Term

private def nameOf (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def showType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def binderInventory (type : Expr) : MetaM Json :=
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    for x in xs do
      let d ← getFVarLocalDecl x
      rows := rows.push <| Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← showType d.type)), ("proof_valued", toJson (← isProp d.type))]
    return Json.mkObj [("binders", toJson rows), ("result", toJson (← showType body))]

private def mergeUses (a b : NameSet × NameSet) : NameSet × NameSet := Id.run do
  let mut result := a
  for name in b.1.toArray do result := (result.1.insert name, result.2)
  for name in b.2.toArray do result := (result.1, result.2.insert name)
  return result

/- Distinguish actual proof use from canonical typeclass evidence inserted as
   an instance argument. Never infer this distinction from a name prefix. -/
private partial def proofUses (e : Expr) (insideInstance := false) : MetaM (NameSet × NameSet) := do
  match e with
  | .const name _ =>
    let info ← getConstInfo name
    if ← isProp info.type then
      if insideInstance then return ({}, ({} : NameSet).insert name)
      else return (({} : NameSet).insert name, {})
    return ({}, {})
  | .app .. =>
    let fn := e.getAppFn
    let mut result ← proofUses fn insideInstance
    let mut type ← inferType fn
    for arg in e.getAppArgs do
      if !type.isForall then type ← whnf type
      match type with
      | .forallE _ _ body bi =>
        result := mergeUses result (← proofUses arg (insideInstance || bi == .instImplicit))
        type := body.instantiate1 arg
      | _ => throwError "Application has no function binder in dependency inspection"
    return result
  | .lam name type body bi | .forallE name type body bi =>
    let before ← proofUses type insideInstance
    let after ← withLocalDecl name bi type fun x => proofUses (body.instantiate1 x) insideInstance
    return mergeUses before after
  | .letE name type value body _ =>
    let before := mergeUses (← proofUses type insideInstance) (← proofUses value insideInstance)
    let after ← withLetDecl name type value fun x => proofUses (body.instantiate1 x) insideInstance
    return mergeUses before after
  | .mdata _ value | .proj _ _ value => proofUses value insideInstance
  | _ => return ({}, {})

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let uses ← if imported then pure (({} : NameSet), ({} : NameSet))
    else match info.value? (allowOpaque := true) with
      | some value => proofUses value
      | none => pure (({} : NameSet), ({} : NameSet))
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
    ("proof_uses", Json.mkObj [
      ("ordinary", toJson (uses.1.toArray.map Name.toString)),
      ("instance_argument", toJson (uses.2.toArray.map Name.toString))]),
    ("type", toJson (← showType info.type)),
    ("signature", ← binderInventory info.type),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("direct_constants", toJson ((info.getUsedConstantsAsSet.toArray.qsort Name.lt).map Name.toString)),
    ("axioms", toJson ((← collectAxioms name).map Name.toString))]

private def inspect (roots : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    rows := rows.push (← record name)
    if !(← getEnv).isImportedConst name then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
  return Json.mkObj [("declarations", toJson rows), ("truncated", toJson (!pending.isEmpty))]

private def actualType (selector : String) (parts : Array String) : TermElabM Expr := do
  if selector.startsWith "decl:" then
    return (← getConstInfo (nameOf parts)).type
  if selector.startsWith "premise:" then
    let wanted := "h_" ++ (selector.drop 8).toString
    let root ← getConstInfo `AuditBExport.P
    return ← forallTelescope root.type fun xs _ => do
      let mut context : Array Expr := #[]
      for x in xs do
        let binder ← getFVarLocalDecl x
        if binder.userName.toString == wanted then
          return ← mkForallFVars context binder.type
        context := context.push x
      throwError "Missing actual root premise {wanted}"
  throwError "Unsupported selector {selector}"

/- Universe parameter names belong to each declaration's binder scope.
   Rename them bijectively, retaining repetitions and all level expressions.
   This is alpha-equivalence, not a proof of logical equivalence. -/
private def sameSignature (actual expected : Expr) : MetaM (Bool × String) := do
  if ← withoutModifyingState <| isDefEq actual expected then
    return (true, "definitional")
  let actualParams := (collectLevelParams {} actual).params.toList
  let expectedParams := (collectLevelParams {} expected).params.toList
  if actualParams.length != expectedParams.length then
    return (false, "different_universe_binders")
  let levels := (List.range actualParams.length).map fun i =>
    Level.param (Name.mkSimple ("_yuiAuditLevel" ++ toString i))
  let equal ← withoutModifyingState <| isDefEq
    (actual.instantiateLevelParams actualParams levels)
    (expected.instantiateLevelParams expectedParams levels)
  return (equal, "bijective_universe_renaming")

elab "#nl2lean_audit_probe" : command => do
  let result ← liftTermElabM <| withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
    let checks : Array (String × String × String × Array String) := #[("P", "decl:AuditBExport.P", "∀ (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : LR.ComplexHyp l rho x y h) (h_H003 : v ≠ 0 ∧ rho x v = 0 ∧ rho h v = (l : ℂ) • v) (h_H004 : LR.Admissible rho x y M), LR.Target K M rho x y h", #["AuditBExport", "P"]), ("__frozen__P", "decl:AuditBExport.P", "∀ (K : Type*) [fieldK : Field K] (V : Type*) [addV : AddCommGroup V] [modV : Module ℂ V] (p : ℕ) (l : ℤ) (M : Submodule ℤ V) (rho : LR.L →ₗ[ℂ] Module.End ℂ V) (x : LR.L) (y : LR.L) (h : LR.L) (v : V) (h_H001 : Nat.Prime p ∧ CharP K p ∧ 0 ≤ l ∧ l < (p : ℤ)) (h_H002 : LR.ComplexHyp l rho x y h) (h_H003 : v ≠ 0 ∧ rho x v = 0 ∧ rho h v = (l : ℂ) • v) (h_H004 : LR.Admissible rho x y M), LR.Target K M rho x y h", #["AuditBExport", "P"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`AuditBExport.P]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      let row := Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if id.startsWith "__frozen__" then
        frozenComparisons := frozenComparisons.push row
      else
        comparisons := comparisons.push row
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons),
      ("frozen_comparisons", toJson frozenComparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

set_option maxHeartbeats 0 in
#nl2lean_audit_probe
end NL2LeanAuditProbe
