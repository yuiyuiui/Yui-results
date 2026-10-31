import Mathlib
open scoped TensorProduct
noncomputable section
universe uK uV
namespace LatticeIR
def R (p : ℕ) : Subring ℚ :=
  Subring.closure {q : ℚ | ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)}
instance ratModule (V : Type*) [AddCommGroup V] [Module ℂ V] : Module ℚ V :=
  Module.compHom V (algebraMap ℚ ℂ)
instance complexAlgebra (p : ℕ) : Algebra (R p) ℂ :=
  ((algebraMap ℚ ℂ).comp (R p).subtype).toAlgebra
instance localModule (p : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V] : Module (R p) V :=
  Module.compHom V (algebraMap (R p) ℂ)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def dp (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r
def e (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dp y i v
abbrev MR (p : ℕ) (M : Submodule ℤ V) := (R p) ⊗[ℤ] M
def mu (p : ℕ) (M : Submodule ℤ V) : MR p M →ₗ[R p] V :=
  M.subtype.liftBaseChange (R p)
abbrev VK (K : Type*) [Field K] (M : Submodule ℤ V) := K ⊗[ℤ] M
def image (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) V :=
  LinearMap.range (mu p M)
def Ji (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) : Submodule (R p) ℂ :=
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  letI : IsScalarTower (R p) ℂ ℂ := IsScalarTower.of_compHom (R p) ℂ ℂ
  (image p M).comap ((LinearMap.toSpanSingleton ℂ V (e y v i)).restrictScalars (R p))
def unit {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    {n : ℕ} (B : Module.Basis (Fin n) F W) (i j : Fin n) : Module.End F W :=
  (LinearMap.toSpanSingleton F W (B i)).comp (B.coord j)
def basisAt {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    {n : ℕ} (B : Module.Basis (Fin n) F W) (i : ℕ) : W :=
  if hi : i < n then B ⟨i, hi⟩ else 0
def Stable (M : Submodule ℤ V) (f : Module.End ℂ V) : Prop :=
  ∀ w ∈ M, f w ∈ M
def latticeOp (M : Submodule ℤ V) (f : Module.End ℂ V) : Module.End ℤ M :=
  letI := Classical.propDecidable
  if hf : Stable M f then (f.restrictScalars ℤ).restrict hf else 0
def kop (K : Type*) [Field K] (M : Submodule ℤ V) (f : Module.End ℂ V) : Module.End K (VK K M) :=
  (latticeOp M f).baseChange K
def kdp {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (f : Module.End K W) (r : ℕ) : Module.End K W :=
  ((r.factorial : K)⁻¹) • f ^ r
def Coordinates (lam : ℤ) (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ B : Module.Basis (Fin (lam.toNat + 1)) ℂ V, ∀ i, B i = e y v i.val
def rop (p : ℕ) (M : Submodule ℤ V) (f : Module.End ℂ V) : Module.End (R p) (MR p M) :=
  (latticeOp M f).baseChange (R p)
def pSub (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) (MR p M) :=
  Submodule.span (R p) (Set.range (fun z : MR p M => (p : R p) • z))
abbrev QuotMR (p : ℕ) (M : Submodule ℤ V) := MR p M ⧸ pSub p M
def Inv {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (W' : Submodule F W) (f : Module.End F W) : Prop :=
  ∀ w ∈ W', f w ∈ W'
def Actions {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (lam : ℤ) (a b c : Module.End F W) (B : Module.Basis (Fin (lam.toNat + 1)) F W) : Prop :=
  (∀ i, a (B i) = if i.val = 0 then 0 else
    ((lam - (i.val : ℤ) + 1 : ℤ) : F) • basisAt B (i.val - 1)) ∧
  (∀ i, b (B i) = if i.val < lam.toNat then
    ((i.val + 1 : ℕ) : F) • basisAt B (i.val + 1) else 0) ∧
  (∀ i, c (B i) = ((lam - 2 * (i.val : ℤ) : ℤ) : F) • B i)
def Strings (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  (∀ d : ℕ, h ((y ^ d) v) = ((lam - 2 * (d : ℤ) : ℤ) : ℂ) • (y ^ d) v) ∧
  (∀ d : ℕ, 1 ≤ d → x ((y ^ d) v) =
    (((d : ℤ) * (lam - (d : ℤ) + 1) : ℤ) : ℂ) • (y ^ (d - 1)) v)
def ComplexOutput (lam : ℤ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  0 < lam + 1 ∧ Fintype.card (Fin (lam.toNat + 1)) = lam.toNat + 1 ∧
  Coordinates lam y v ∧ Strings lam x y h v ∧
  (∀ d : ℕ, lam < (d : ℤ) → (y ^ d) v = 0) ∧
  (∀ B : Module.Basis (Fin (lam.toNat + 1)) ℂ V,
    (∀ i, B i = e y v i.val) → Actions lam x y h B) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)),
    dp x r (e y v i.val) =
      if r ≤ i.val then ((Nat.choose (lam.toNat - i.val + r) r : ℕ) : ℂ) • e y v (i.val - r) else 0) ∧
  (∀ (r : ℕ) (i : Fin (lam.toNat + 1)),
    dp y r (e y v i.val) =
      if i.val + r ≤ lam.toNat then ((Nat.choose (i.val + r) r : ℕ) : ℂ) • e y v (i.val + r) else 0)
def RingCarrier (p : ℕ) : Prop :=
  ∀ q : ℚ, q ∈ R p ↔ ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)
def LocalBasics (p : ℕ) (lam : ℤ) (M : Submodule ℤ V) (x y : Module.End ℂ V) : Prop :=
  RingCarrier p ∧ Function.Injective (mu p M) ∧
  Nonempty (Module.Basis (Fin (lam.toNat + 1)) (R p) (MR p M)) ∧
  Submodule.span ℂ (image p M : Set V) = ⊤ ∧
  (∀ r : ℕ, (∀ z, mu p M (rop p M (dp x r) z) = dp x r (mu p M z)) ∧
    (∀ z, mu p M (rop p M (dp y r) z) = dp y r (mu p M z))) ∧
  (∀ (r : ℕ) (w : V), w ∈ image p M → dp x r w ∈ image p M ∧ dp y r w ∈ image p M)
def MatrixOutput (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (x y : Module.End ℂ V) (v : V) : Prop :=
  LocalBasics p lam M x y ∧
  (∀ j : Fin (lam.toNat + 1), IsUnit (Nat.choose lam.toNat j.val : R p)) ∧
  (∀ B : Module.Basis (Fin (lam.toNat + 1)) ℂ V,
    (∀ i, B i = e y v i.val) → ∀ i j,
    unit B i j =
      ((Nat.choose lam.toNat j.val : ℂ)⁻¹) •
      (dp x (lam.toNat - i.val) * dp y lam.toNat * dp x lam.toNat * dp y (lam.toNat - j.val)) ∧
    ∀ w ∈ image p M, unit B i j w ∈ image p M)
def CommonOutput (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (x y : Module.End ℂ V) (v : V) : Prop :=
  0 < lam + 1 ∧ Coordinates lam y v ∧ LocalBasics p lam M x y ∧
  (∀ i : Fin (lam.toNat + 1), Ji p M y v i.val = Ji p M y v 0) ∧
  (Ji p M y v 0).FG ∧ Ji p M y v 0 ≠ ⊥ ∧
  (∃ F : ((Fin (lam.toNat + 1)) → Ji p M y v 0) ≃ₗ[R p] MR p M,
    ∀ c, mu p M (F c) = ∑ i, ((c i : Ji p M y v 0) : ℂ) • e y v i.val)
def PrincipalOutput (p : ℕ) (lam : ℤ) (M : Submodule ℤ V)
    (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ b : ℂ, b ∈ Ji p M y v 0 ∧ b ≠ 0 ∧
    Ji p M y v 0 = Submodule.span (R p) {b} ∧
    ∃ B : Module.Basis (Fin (lam.toNat + 1)) (R p) (MR p M),
      ∀ i, mu p M (B i) = b • e y v i.val
def ReducedOutput (K : Type*) [Field K] (lam : ℤ) (M : Submodule ℤ V)
    (x y h : Module.End ℂ V) : Prop :=
  0 < lam + 1 ∧ Stable M x ∧ Stable M y ∧ Stable M h ∧
  kop K M h = kop K M x * kop K M y - kop K M y * kop K M x ∧
  kop K M h * kop K M x - kop K M x * kop K M h = (2 : K) • kop K M x ∧
  kop K M h * kop K M y - kop K M y * kop K M h = (-2 : K) • kop K M y ∧
  ∃ B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M),
    Actions lam (kop K M x) (kop K M y) (kop K M h) B ∧
    (∀ r : ℕ, r ≤ lam.toNat → (r.factorial : K) ≠ 0 ∧
      (latticeOp M (dp x r)).baseChange K = kdp (kop K M x) r ∧
      (latticeOp M (dp y r)).baseChange K = kdp (kop K M y) r) ∧
    (∀ i j : Fin (lam.toNat + 1), (Nat.choose lam.toNat j.val : K) ≠ 0 ∧
      unit B i j = ((Nat.choose lam.toNat j.val : K)⁻¹) •
        (kdp (kop K M x) (lam.toNat - i.val) * kdp (kop K M y) lam.toNat *
         kdp (kop K M x) lam.toNat * kdp (kop K M y) (lam.toNat - j.val)))
def Target (K : Type*) [Field K] (M : Submodule ℤ V) (x y h : Module.End ℂ V) : Prop :=
  Nontrivial (VK K M) ∧ ∀ W : Submodule K (VK K M),
    Inv W (kop K M x) → Inv W (kop K M y) → Inv W (kop K M h) → W = ⊥ ∨ W = ⊤
def FractionData (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  let J := Ji p M y v 0;
    (∃ theta : (ℚ ⊗[R p] J) →ₗ[ℚ] ℂ,
      (∀ (q : ℚ) (c : J), theta (TensorProduct.tmul (R p) q c) = (q : ℂ) * (c : ℂ)) ∧
      Function.Injective theta) ∧ FiniteDimensional ℚ (ℚ ⊗[R p] J)
def RationalLine (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  let J := Ji p M y v 0;
    Module.finrank ℚ (ℚ ⊗[R p] J) = 1 ∧
    ∀ a : ℂ, a ∈ J → a ≠ 0 → ∀ c : ℂ, c ∈ J → ∃! q : ℚ, c = (q : ℂ) * a
def ScalarExtensionData (p : ℕ) (K : Type*) [Field K] (M : Submodule ℤ V) : Prop :=
  ∀ hc : CharP K p,
    letI : CharP K p := hc
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    ∃ rho : R p →+* K,
      RingHom.ker rho = Ideal.span {(p : R p)} ∧
      (∀ (r : R p) (a b : ℤ), ¬ (p : ℤ) ∣ b →
        (r : ℚ) = (a : ℚ) / (b : ℚ) → rho r = (a : K) / (b : K)) ∧
      letI : Algebra (R p) K := rho.toAlgebra
      ∃ phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M),
        (∀ (c : K) (m : M), phi (TensorProduct.tmul ℤ c m) =
          TensorProduct.tmul (R p) c (TensorProduct.tmul ℤ (1 : R p) m)) ∧
        (∀ f : Module.End ℂ V, Stable M f → ∀ z,
          phi (kop K M f z) = ((latticeOp M f).baseChange (R p)).baseChange K (phi z)) ∧
        ∃ qmod : Module (ZMod p) (QuotMR p M),
          letI : Module (ZMod p) (QuotMR p M) := qmod
          ∃ eta : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] QuotMR p M),
            ∀ (c : K) (z : MR p M), eta (TensorProduct.tmul (R p) c z) =
              TensorProduct.tmul (ZMod p) c (Submodule.Quotient.mk z)
def ReducedBasisData (p : ℕ) (K : Type*) [Field K] (lam : ℤ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (v : V) : Prop :=
  ∃ rho : R p →+* K,
    letI : Algebra (R p) K := rho.toAlgebra
    ∃ phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M),
      (∀ (c : K) (m : M), phi (TensorProduct.tmul ℤ c m) =
        TensorProduct.tmul (R p) c (TensorProduct.tmul ℤ (1 : R p) m)) ∧
      (∀ f : Module.End ℂ V, Stable M f → ∀ z,
        phi (kop K M f z) = ((latticeOp M f).baseChange (R p)).baseChange K (phi z)) ∧
      ∃ b : ℂ, b ≠ 0 ∧
        ∃ BR : Module.Basis (Fin (lam.toNat + 1)) (R p) (MR p M),
          (∀ i, mu p M (BR i) = b • e y v i.val) ∧
          ∃ B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M),
            (∀ i, phi (B i) = TensorProduct.tmul (R p) (1 : K) (BR i)) ∧
            Actions lam (kop K M x) (kop K M y) (kop K M h) B
end LatticeIR
open LatticeIR

namespace Translation
set_option autoImplicit false

theorem T011 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
    ∃ bC : Module.Basis (Fin d) ℂ V, ∀ i, bC i = (bZ i : V)) ∧
  ∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r)) (h_T006 : MatrixOutput p lam M x y v) :
    ScalarExtensionData p K M := by
  classical
  have hphiData : ∀ rho : R p →+* K, letI : Algebra (R p) K := rho.toAlgebra
    ∃ phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M),
      (∀ (c : K) (m : M), phi (TensorProduct.tmul ℤ c m) =
        TensorProduct.tmul (R p) c (TensorProduct.tmul ℤ (1 : R p) m)) ∧
      (∀ f : Module.End ℂ V, Stable M f → ∀ z,
        phi (kop K M f z) = ((latticeOp M f).baseChange (R p)).baseChange K (phi z)) := by
    intro rho
    letI : Algebra (R p) K := rho.toAlgebra
    let phi : VK K M ≃ₗ[K] (K ⊗[R p] MR p M) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (R p) K K M).symm
    refine ⟨phi, ?_, ?_⟩
    · intro c m
      exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul ℤ (R p) K c m
    · intro f hf z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c m => simp [phi, kop, LinearMap.baseChange_tmul]
      | add z w hz hw => simpa only [map_add, hz, hw]
  have hetaData : ∀ s : R p →+* ZMod p, RingHom.ker s = Ideal.span {(p : R p)} →
    Function.Surjective s →
    ∀ hc : CharP K p,
    letI : CharP K p := hc
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    let rho := (algebraMap (ZMod p) K).comp s
    letI : Algebra (R p) K := rho.toAlgebra
    ∃ qmod : Module (ZMod p) (QuotMR p M),
      letI : Module (ZMod p) (QuotMR p M) := qmod
      ∃ eta : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] QuotMR p M),
      ∀ (c : K) (z : MR p M), eta (TensorProduct.tmul (R p) c z) =
        TensorProduct.tmul (ZMod p) c (Submodule.Quotient.mk z) := by
    classical
    intro s hs hsur hc
    letI : CharP K p := hc
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    let rho := (algebraMap (ZMod p) K).comp s
    letI : Algebra (R p) K := rho.toAlgebra
    letI : Algebra (R p) (ZMod p) := s.toAlgebra
    letI : IsScalarTower (R p) (ZMod p) K :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hpSub : (RingHom.ker s) • (⊤ : Submodule (R p) (MR p M)) = pSub p M := by
      rw [hs, Submodule.ideal_span_singleton_smul]
      apply le_antisymm
      · intro z hz
        obtain ⟨w,hw,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
        exact Submodule.subset_span ⟨w,rfl⟩
      · apply Submodule.span_le.mpr
        rintro _ ⟨w,rfl⟩
        exact Submodule.smul_mem_pointwise_smul w (p : R p) ⊤ (by trivial)
    have hkill : ∀ z : QuotMR p M, p • z = 0 := by
      intro z
      obtain ⟨w,rfl⟩ := Submodule.Quotient.mk_surjective _ z
      change (pSub p M).mkQ (p • w) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨w, by simp only [Nat.cast_smul_eq_nsmul]⟩
    have qmod : Module (ZMod p) (QuotMR p M) := AddCommGroup.zmodModule hkill
    letI : Module (ZMod p) (QuotMR p M) := qmod
    let es : (R p ⧸ RingHom.ker s) ≃ₐ[R p] ZMod p :=
      { s.quotientKerEquivOfSurjective hsur with
        commutes' := fun r => by
          exact RingHom.quotientKerEquivOfSurjective_apply_mk hsur r }
    let eR : (ZMod p ⊗[R p] MR p M) ≃ₗ[R p] QuotMR p M :=
      (es.symm.toLinearEquiv.rTensor (MR p M)) ≪≫ₗ
        TensorProduct.quotTensorEquivQuotSMul (MR p M) (RingHom.ker s) ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hpSub
    let eZ : (ZMod p ⊗[R p] MR p M) ≃ₗ[ZMod p] QuotMR p M :=
      { eR.toAddEquiv with
        map_smul' := fun a z => ZMod.map_smul eR.toAddMonoidHom a z }
    have he : ∀ z : MR p M, eZ (TensorProduct.tmul (R p) (1 : ZMod p) z) =
        Submodule.Quotient.mk z := by
      intro z
      simp [eZ, eR]
    let eta : (K ⊗[R p] MR p M) ≃ₗ[K] (K ⊗[ZMod p] QuotMR p M) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (R p) (ZMod p) K K (MR p M)).symm ≪≫ₗ
        eZ.baseChange (ZMod p) K (ZMod p ⊗[R p] MR p M) (QuotMR p M)
    refine ⟨qmod,eta, ?_⟩
    intro c z
    simp [eta,he]

  have hres : letI : Fact p.Prime := ⟨h_H001.1⟩; ∃ f : R p →+* (ZMod p), RingHom.ker f = Ideal.span {(p : R p)} ∧
    (∀ (r : R p) (a b : ℤ), ¬ (p : ℤ) ∣ b →
      (r : ℚ) = (a : ℚ) / (b : ℚ) → f r = (a : (ZMod p)) / (b : (ZMod p))) := by
    letI : Fact p.Prime := ⟨h_H001.1⟩
    classical
    obtain ⟨S,hS,hLoc⟩ : ∃ S : Submonoid ℤ, (∀ b : ℤ, b ∈ S ↔ ¬ (p : ℤ) ∣ b) ∧ IsLocalization S (R p) := by
      classical
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp h_H001.1
      let S : Submonoid ℤ :=
        { carrier := {b | ¬ (p : ℤ) ∣ b}
          one_mem' := hp.not_dvd_one
          mul_mem' := fun ha hb h => (hp.dvd_mul.mp h).elim ha hb }
      refine ⟨S, fun b => Iff.rfl, ?_⟩
      rw [isLocalization_iff]
      have hc : RingCarrier p := h_T006.1.1
      have bn : ∀ b : S, (b.val : ℚ) ≠ 0 := by
        intro b hb
        have : b.val = 0 := by exact_mod_cast hb
        exact b.property (this ▸ dvd_zero _)
      refine ⟨?_, ?_, ?_⟩
      · intro b
        let t : R p := ⟨(1 : ℚ) / b.val, (hc _).2 ⟨1, b.val, b.property, by simp⟩⟩
        apply isUnit_iff_exists_inv.mpr
        refine ⟨t, ?_⟩
        apply Subtype.ext
        change (b.val : ℚ) * (1 / b.val) = 1
        exact mul_one_div_cancel (bn b)
      · intro z
        obtain ⟨a,b,hb,he⟩ := (hc z.val).1 z.property
        refine ⟨(a, ⟨b,hb⟩), ?_⟩
        apply Subtype.ext
        change z.val * (b : ℚ) = (a : ℚ)
        rw [he]
        exact div_mul_cancel₀ _ (bn ⟨b,hb⟩)
      · intro a b hab
        refine ⟨1, ?_⟩
        have : a = b := by
          have he := congrArg (fun z : R p => (z : ℚ)) hab
          exact_mod_cast he
        simpa [this]
    letI : IsLocalization S (R p) := hLoc
    letI : CharP (ZMod p) p := inferInstance
    have hc : RingCarrier p := h_T006.1.1
    have hn : ∀ b : ℤ, ¬ (p : ℤ) ∣ b → (b : (ZMod p)) ≠ 0 :=
      fun b hb => fun hz => hb ((CharP.intCast_eq_zero_iff (ZMod p) p b).1 hz)
    let f : R p →+* (ZMod p) := IsLocalization.lift (M := S)
      (g := Int.castRingHom (ZMod p)) (fun b => isUnit_iff_ne_zero.mpr (hn b.val ((hS _).1 b.property)))
    have hf : ∀ (r : R p) (a b : ℤ), ¬ (p : ℤ) ∣ b →
        (r : ℚ) = (a : ℚ) / (b : ℚ) → f r = (a : (ZMod p)) / (b : (ZMod p)) := by
      intro r a b hb hr
      have bz : (b : ℚ) ≠ 0 := by
        exact_mod_cast (show b ≠ 0 from fun h => hb (h ▸ dvd_zero _))
      have eqr : r * (b : R p) = (a : R p) := by
        apply Subtype.ext
        change (r : ℚ) * (b : ℚ) = (a : ℚ)
        rw [hr, div_mul_cancel₀ _ bz]
      have he := congrArg f eqr
      have hi : ∀ a : ℤ, f (a : R p) = (a : (ZMod p)) := fun a => map_intCast f a
      rw [map_mul, hi, hi] at he
      exact (eq_div_iff (hn b hb)).2 he
    refine ⟨f, ?_, hf⟩
    ext r
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro hr
      obtain ⟨a,b,hb,he⟩ := (hc r.val).1 r.property
      have ha : (p : ℤ) ∣ a := by
        apply (CharP.intCast_eq_zero_iff (ZMod p) p a).1
        have hz : (a : (ZMod p)) / (b : (ZMod p)) = 0 := (hf r a b hb he).symm.trans hr
        exact (div_eq_zero_iff).1 hz |>.resolve_right (hn b hb)
      obtain ⟨t,ht⟩ := ha
      let s : R p := ⟨(t : ℚ) / (b : ℚ), (hc _).2 ⟨t,b,hb,rfl⟩⟩
      refine ⟨s, ?_⟩
      apply Subtype.ext
      change (r : ℚ) = (p : ℚ) * ((t : ℚ) / (b : ℚ))
      rw [he,ht]
      push_cast
      ring
    · rintro ⟨s,hs⟩
      rw [hs, map_mul]
      simp [f, show (p : (ZMod p)) = 0 from CharP.cast_eq_zero (ZMod p) p]
  intro hc
  letI : CharP K p := hc
  letI : Fact p.Prime := ⟨h_H001.1⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  obtain ⟨s,hs,hsfrac⟩ := hres
  let rho : R p →+* K := (algebraMap (ZMod p) K).comp s
  refine ⟨rho, ?_, ?_, ?_⟩
  · change RingHom.ker ((algebraMap (ZMod p) K).comp s) = _
    rw [RingHom.ker_comp_of_injective s (ZMod.castHom_injective K), hs]
  · intro r a b hb hr
    change algebraMap (ZMod p) K (s r) = _
    rw [hsfrac r a b hb hr, map_div₀, map_intCast, map_intCast]
  · letI : Algebra (R p) K := rho.toAlgebra
    obtain ⟨phi,hphi,hnat⟩ := hphiData rho
    refine ⟨phi,hphi,hnat,?_⟩
    exact hetaData s hs (ZMod.ringHom_surjective s) hc

#check @T011
#print axioms T011

end Translation
