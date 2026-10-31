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

theorem T001 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) :
    Strings lam x y h v := by
  have hy : ∀ w : V, h (y w) = y (h w) + (-2 : ℂ) • y w := by
    intro w
    have hw := congrArg (fun f : Module.End ℂ V => f w) h_H003.2.1
    change h (y w) - y (h w) = (-2 : ℂ) • y w at hw
    exact (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)
  have hxy : ∀ w : V, x (y w) = y (x w) + h w := by
    intro w
    have hw := congrArg (fun f : Module.End ℂ V => f w) h_H003.2.2
    change x (y w) - y (x w) = h w at hw
    exact (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)
  have ypow (d : ℕ) : (y ^ (d + 1)) v = y ((y ^ d) v) := by
    rw [pow_succ', Module.End.mul_apply]
  have hh : ∀ d : ℕ, h ((y ^ d) v) =
      ((lam - 2 * (d : ℤ) : ℤ) : ℂ) • (y ^ d) v := by
    intro d
    induction d with
    | zero => simpa using h_H004.2.2
    | succ d ih =>
      rw [ypow, hy, ih, map_smul, ← add_smul]
      congr 1
      push_cast
      ring
  have hx : ∀ n : ℕ, x ((y ^ (n + 1)) v) =
      (((n + 1 : ℕ) : ℂ) * ((lam : ℂ) - (n : ℂ))) • (y ^ n) v := by
    intro n
    induction n with
    | zero =>
      rw [ypow, hxy, pow_zero, Module.End.one_apply, h_H004.2.1,
        map_zero, zero_add, h_H004.2.2]
      simp
    | succ n ih =>
      rw [ypow (n + 1), hxy, ih, map_smul, hh, ← ypow n, ← add_smul]
      congr 1
      push_cast
      ring
  constructor
  · exact hh
  · intro d hd
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 := ⟨d - 1, by omega⟩
    rw [hx]
    congr 1
    push_cast
    ring

theorem T002 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lam.toNat + 1 ∧ Nontrivial V ∧
  (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤) ∧
  (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lam : ℂ) • w)) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) (h_T001 : Strings lam x y h v) :
    Coordinates lam y v := by
  classical
  letI : FiniteDimensional ℂ V := h_H002.1
  have hpow : ∀ d : ℕ, d ≤ lam.toNat → (y ^ d) v ≠ 0 := by
    intro d
    induction d with
    | zero => simpa using h_H004.1
    | succ d ih =>
      intro hd
      have hd' : d ≤ lam.toNat := by omega
      have hbound : ((d + 1 : ℕ) : ℤ) ≤ lam := by
        have hh : ((d + 1 : ℕ) : ℤ) ≤ (lam.toNat : ℤ) := by exact_mod_cast hd
        rwa [Int.toNat_of_nonneg h_H001.2.2.1] at hh
      have hcZ : ((d + 1 : ℕ) : ℤ) * (lam - ((d + 1 : ℕ) : ℤ) + 1) ≠ 0 := by
        apply mul_ne_zero <;> omega
      have hc : ((((d + 1 : ℕ) : ℤ) * (lam - ((d + 1 : ℕ) : ℤ) + 1) : ℤ) : ℂ) ≠ 0 := by
        exact_mod_cast hcZ
      intro hz
      have he := h_T001.2 (d + 1) (by omega)
      rw [hz, map_zero, Nat.add_sub_cancel] at he
      exact (smul_ne_zero hc (ih hd')) he.symm
  let E : Fin (lam.toNat + 1) → V := fun i => e y v i.val
  let ev : Fin (lam.toNat + 1) → ℂ := fun i => ((lam - 2 * (i.val : ℤ) : ℤ) : ℂ)
  have hE : ∀ i, E i ≠ 0 := by
    intro i
    have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    exact smul_ne_zero (inv_ne_zero hf) (hpow i.val (by omega))
  have heig : ∀ i, h (E i) = ev i • E i := by
    intro i
    change h (((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v) =
      ev i • (((i.val.factorial : ℂ)⁻¹) • (y ^ i.val) v)
    rw [map_smul, h_T001.1 i.val, smul_comm]
  have hev : Function.Injective ev := by
    intro i j hij
    have hz : lam - 2 * (i.val : ℤ) = lam - 2 * (j.val : ℤ) := by
      exact Int.cast_injective (α := ℂ) hij
    apply Fin.ext
    omega
  have hli : LinearIndependent ℂ E := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha j
    let P : Polynomial ℂ :=
      ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (ev k))
    have hPeval : ∀ i, P.eval (ev i) =
        ∏ k ∈ Finset.univ.erase j, (ev i - ev k) := by
      intro i
      simp [P, Polynomial.eval_prod]
    have hother : ∀ i, i ≠ j → P.eval (ev i) = 0 := by
      intro i hij
      rw [hPeval]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) (sub_self _)
    have hjnonzero : P.eval (ev j) ≠ 0 := by
      rw [hPeval]
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      apply sub_ne_zero.mpr
      intro hh
      have hjk : j = k := hev hh
      exact (Finset.mem_erase.mp hk).1 hjk.symm
    have happ : ∀ i, (Polynomial.aeval h P) (E i) = P.eval (ev i) • E i := by
      intro i
      exact Module.End.aeval_apply_of_mem_apply_eq_smul (p := P) (heig i)
    have hrel := congrArg (fun w : V => (Polynomial.aeval h P) w) ha
    simp only [map_sum, map_smul, map_zero, happ, smul_smul] at hrel
    have hone : (∑ i, (a i * P.eval (ev i)) • E i) =
        (a j * P.eval (ev j)) • E j := by
      apply Finset.sum_eq_single j
      · intro i hi hij
        simp [hother i hij]
      · simp
    rw [hone] at hrel
    have hz : a j * P.eval (ev j) = 0 := (smul_eq_zero.mp hrel).resolve_right (hE j)
    exact (mul_eq_zero.mp hz).resolve_right hjnonzero
  have hcard : Fintype.card (Fin (lam.toNat + 1)) = Module.finrank ℂ V := by
    simpa using h_H002.2.1.symm
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
  intro i
  change (basisOfLinearIndependentOfCardEqFinrank hli hcard) i = E i
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

theorem T003 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_T001 : Strings lam x y h v) (h_T002 : Coordinates lam y v) :
    ∀ d : ℕ, lam < (d : ℤ) → (y ^ d) v = 0 := by
  classical
  obtain ⟨B, hB⟩ := h_T002
  have hn : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg h_H001.2.2.1
  have he (j : Fin (lam.toNat + 1)) :
      h (B j) = ((lam - 2 * (j.val : ℤ) : ℤ) : ℂ) • B j := by
    rw [hB j]
    simp only [e, dp, LinearMap.smul_apply, map_smul, h_T001.1 j.val]
    simp only [smul_smul, mul_comm]
  have hc (w : V) (i : Fin (lam.toNat + 1)) :
      B.coord i (h w) = ((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) * B.coord i w := by
    have hm : (B.coord i).comp h =
        ((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) • B.coord i := by
      apply B.ext
      intro j
      by_cases hji : j = i
      · subst j
        simp [LinearMap.comp_apply, he, Module.Basis.coord_apply]
      · simp [LinearMap.comp_apply, he, Module.Basis.coord_apply, hji]
    have hh := congrArg (fun f : V →ₗ[ℂ] ℂ => f w) hm
    simpa using hh
  have hz : (y ^ (lam.toNat + 1)) v = 0 := by
    apply B.ext_elem
    intro i
    have hi : (i.val : ℤ) < (lam.toNat : ℤ) + 1 := by
      exact_mod_cast i.isLt
    have hneZ : (lam - 2 * (i.val : ℤ)) -
        (lam - 2 * ((lam.toNat + 1 : ℕ) : ℤ)) ≠ 0 := by omega
    have hne : ((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) -
        ((lam - 2 * ((lam.toNat + 1 : ℕ) : ℤ) : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast hneZ
    have hh := congrArg (B.coord i) (h_T001.1 (lam.toNat + 1))
    rw [hc, map_smul, smul_eq_mul] at hh
    have hm : (((lam - 2 * (i.val : ℤ) : ℤ) : ℂ) -
        ((lam - 2 * ((lam.toNat + 1 : ℕ) : ℤ) : ℤ) : ℂ)) *
        B.coord i ((y ^ (lam.toNat + 1)) v) = 0 := by
      rw [sub_mul, hh, sub_self]
    have hzero := (mul_eq_zero.mp hm).resolve_left hne
    simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using hzero
  intro d hd
  have hle : lam.toNat + 1 ≤ d := by omega
  have hd' : d = (d - (lam.toNat + 1)) + (lam.toNat + 1) := by omega
  rw [hd', pow_add, Module.End.mul_apply, hz, map_zero]

theorem T004 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) (h_T001 : Strings lam x y h v) (h_T002 : Coordinates lam y v) (h_T003 : ∀ d : ℕ, lam < (d : ℤ) → (y ^ d) v = 0) :
    ComplexOutput lam x y h v := by
  have hf (i : ℕ) : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hxS : ∀ i : ℕ, x (e y v (i+1)) = ((lam - (i : ℤ) : ℤ) : ℂ) • e y v i := by
    intro i
    simp only [e, dp, LinearMap.smul_apply, map_smul]
    rw [h_T001.2 (i+1) (by omega)]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.factorial_succ, Nat.cast_mul, smul_smul]
    congr 1
    field_simp
    <;> ring
  have hx0 : x (e y v 0) = 0 := by
    simpa [e, dp] using h_H004.2.1
  have hyS : ∀ i : ℕ, y (e y v i) = ((i+1 : ℕ) : ℂ) • e y v (i+1) := by
    intro i
    simp only [e, dp, LinearMap.smul_apply, map_smul]
    rw [← Module.End.mul_apply, ← pow_succ']
    simp only [Nat.factorial_succ, Nat.cast_mul, smul_smul]
    congr 1
    field_simp
  have hh : ∀ i : ℕ, h (e y v i) = ((lam - 2*(i:ℤ) : ℤ) : ℂ) • e y v i := by
    intro i
    simp only [e, dp, LinearMap.smul_apply, map_smul]
    rw [h_T001.1]
    simp [smul_smul, mul_comm]
  have hn : (lam.toNat : ℤ) = lam := Int.toNat_of_nonneg h_H001.2.2.1
  have hxpow : ∀ r i : ℕ, i ≤ lam.toNat →
      (x^r) (e y v i) =
        if r ≤ i then (((lam.toNat-i+1).ascFactorial r : ℕ) : ℂ) • e y v (i-r) else 0 := by
    intro r
    induction r with
    | zero => intro i hi; simp
    | succ r ih =>
      intro i hi
      rw [pow_succ', Module.End.mul_apply, ih i hi]
      by_cases hr : r+1 ≤ i
      · rw [if_pos (by omega : r ≤ i), if_pos hr, map_smul]
        have hind : i-r = (i-(r+1))+1 := by omega
        rw [hind, hxS]
        have hc : lam - ((i-(r+1) : ℕ) : ℤ) = ((lam.toNat-i+1+r : ℕ) : ℤ) := by omega
        rw [hc, Int.cast_natCast]
        simp only [Nat.ascFactorial_succ, Nat.cast_mul, smul_smul]
        congr 1
        ring
      · rw [if_neg hr]
        by_cases hr' : r ≤ i
        · have heq : r = i := by omega
          simp [if_pos hr', heq, map_smul, hx0]
        · simp [if_neg hr', map_zero]
  have hypow : ∀ r i : ℕ, (y^r) (e y v i) =
      (((i+1).ascFactorial r : ℕ) : ℂ) • e y v (i+r) := by
    intro r
    induction r with
    | zero => intro i; simp
    | succ r ih =>
      intro i
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hyS]
      simp only [Nat.ascFactorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_smul]
      rw [show i + (r+1) = i+r+1 by omega]
      congr 1
      ring
  have hezero : ∀ i : ℕ, lam.toNat < i → e y v i = 0 := by
    intro i hi
    simp only [e, dp, LinearMap.smul_apply, h_T003 i (by omega), smul_zero]
  have hdx : ∀ (r : ℕ) (i : Fin (lam.toNat+1)),
      dp x r (e y v i.val) =
        if r ≤ i.val then ((Nat.choose (lam.toNat-i.val+r) r : ℕ) : ℂ) • e y v (i.val-r) else 0 := by
    intro r i
    simp only [dp, LinearMap.smul_apply, hxpow r i.val (by omega)]
    by_cases hr : r ≤ i.val
    · rw [if_pos hr, if_pos hr, Nat.ascFactorial_eq_factorial_mul_choose]
      simp [Nat.cast_mul, smul_smul, ← mul_assoc, hf]
    · simp [hr]
  have hdyall : ∀ r i : ℕ, dp y r (e y v i) =
      ((Nat.choose (i+r) r : ℕ) : ℂ) • e y v (i+r) := by
    intro r i
    simp only [dp, LinearMap.smul_apply, hypow, Nat.ascFactorial_eq_factorial_mul_choose]
    simp [Nat.cast_mul, smul_smul, ← mul_assoc, hf]
  have hdy : ∀ (r : ℕ) (i : Fin (lam.toNat+1)),
      dp y r (e y v i.val) =
        if i.val+r ≤ lam.toNat then ((Nat.choose (i.val+r) r : ℕ) : ℂ) • e y v (i.val+r) else 0 := by
    intro r i
    rw [hdyall]
    split_ifs with hr
    · rfl
    · rw [hezero _ (by omega), smul_zero]
  have hactions : ∀ B : Module.Basis (Fin (lam.toNat+1)) ℂ V,
      (∀ i, B i = e y v i.val) → Actions lam x y h B := by
    intro B hB
    have hat (j : ℕ) (hj : j < lam.toNat+1) : basisAt B j = e y v j := by
      rw [basisAt, dif_pos hj]
      exact hB ⟨j,hj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [hB i]
      by_cases hi : i.val = 0
      · simp [hi, hx0]
      · rw [if_neg hi, hat _ (by omega)]
        have hind : i.val-1+1 = i.val := by omega
        have hc : lam - ((i.val-1 : ℕ) : ℤ) = lam - (i.val : ℤ) + 1 := by omega
        simpa only [hind, hc] using hxS (i.val-1)
    · intro i
      rw [hB i]
      by_cases hi : i.val < lam.toNat
      · rw [if_pos hi, hat _ (by omega)]
        exact hyS i.val
      · rw [if_neg hi, hyS, hezero _ (by omega), smul_zero]
    · intro i
      rw [hB i]
      exact hh i.val
  exact ⟨by omega, Fintype.card_fin _, h_T002, h_T001, h_T003, hactions, hdx, hdy⟩

theorem T005 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
    ∃ bC : Module.Basis (Fin d) ℂ V, ∀ i, bC i = (bZ i : V)) ∧
  ∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r)) (h_T004 : ComplexOutput lam x y h v) :
    LocalBasics p lam M x y := by
  classical
    have hRing : RingCarrier p := by
      classical
        have hp1 : ¬ (p : ℤ) ∣ 1 := by
          intro hh
          apply h_H001.1.not_dvd_one
          exact_mod_cast hh
        have hmul : ∀ {b d : ℤ}, ¬ (p : ℤ) ∣ b → ¬ (p : ℤ) ∣ d → ¬ (p : ℤ) ∣ b * d := by
          intro b d hb hd hh
          exact (Int.Prime.dvd_mul' h_H001.1 hh).elim hb hd
        intro q
        constructor
        · intro hq
          induction hq using Subring.closure_induction with
          | mem q hq => exact hq
          | zero => exact ⟨0, 1, hp1, by simp⟩
          | one => exact ⟨1, 1, hp1, by simp⟩
          | add q r hq hr iq ir =>
            obtain ⟨a, b, hb, rfl⟩ := iq
            obtain ⟨c, d, hd, rfl⟩ := ir
            refine ⟨a*d+c*b, b*d, hmul hb hd, ?_⟩
            have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by intro h; apply hb; simp [h])
            have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by intro h; apply hd; simp [h])
            push_cast
            field_simp
            <;> ring
          | neg q hq iq =>
            obtain ⟨a,b,hb,rfl⟩ := iq
            exact ⟨-a,b,hb,by push_cast; ring⟩
          | mul q r hq hr iq ir =>
            obtain ⟨a,b,hb,rfl⟩ := iq
            obtain ⟨c,d,hd,rfl⟩ := ir
            refine ⟨a*c,b*d,hmul hb hd,?_⟩
            push_cast
            ring
        · intro hq
          exact Subring.subset_closure (s := {q : ℚ | ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ q = (a : ℚ) / (b : ℚ)}) hq
    have hInj : Function.Injective (mu p M) := by
      classical
        have hc (a : R p) : algebraMap (R p) ℂ a = ((a : ℚ) : ℂ) := rfl
        have hcast : Function.Injective (fun r : R p => algebraMap (R p) ℂ r) := by
          intro a b hab
          apply Subtype.ext
          exact Rat.cast_injective (by simpa only [hc] using hab)
        letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
        obtain ⟨d, bZ, bC, hb⟩ := h_H005.1
        letI : SMulWithZero (R p) ℂ :=
          { smul := fun a z => algebraMap (R p) ℂ a * z
            smul_zero := by intro a; exact mul_zero _
            zero_smul := by intro z; change algebraMap (R p) ℂ 0 * z = 0; rw [map_zero, zero_mul] }
        have hli : LinearIndependent (R p) bC :=
          bC.linearIndependent.restrict_scalars (R := R p) (K := ℂ)
            (by simpa only [Algebra.smul_def, mul_one] using hcast)
        have hfun : (mu p M) ∘ (bZ.baseChange (R p)) = (fun i => bC i) := by
          funext i
          simp only [Function.comp_apply, Module.Basis.baseChange_apply, mu,
            LinearMap.liftBaseChange_tmul, one_smul, hb]
          rfl
        apply LinearMap.injective_of_linearIndependent (bZ.baseChange (R p)).span_eq
        rw [hfun]
        exact hli
    have hBS : Nonempty (Module.Basis (Fin (lam.toNat + 1)) (R p) (MR p M)) ∧ Submodule.span ℂ (image p M : Set V) = ⊤ := by
      classical
        obtain ⟨d, bZ, bC, hb⟩ := h_H005.1
        obtain ⟨B, hB⟩ := h_T004.2.2.1
        have hd : d = lam.toNat + 1 := by
          simpa only [Fintype.card_fin] using
            (Module.finrank_eq_card_basis bC).symm.trans (Module.finrank_eq_card_basis B)
        constructor
        · subst d
          exact ⟨bZ.baseChange (R p)⟩
        · apply top_unique
          rw [← bC.span_eq]
          apply Submodule.span_le.mpr
          rintro w ⟨i, rfl⟩
          apply Submodule.subset_span
          change ∃ z, mu p M z = bC i
          refine ⟨TensorProduct.tmul ℤ (1 : R p) (bZ i), ?_⟩
          simp only [mu, LinearMap.liftBaseChange_tmul, one_smul, hb]
          rfl
    have hcomm : ∀ (f : Module.End ℂ V), Stable M f → ∀ z, mu p M (rop p M f z) = f (mu p M z) := by
      classical
        letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
        intro f hf z
        have hop (m : M) : (latticeOp M f m : V) = f m := by
          simp only [latticeOp, dif_pos hf, LinearMap.restrict_apply,
            LinearMap.restrictScalars_apply]
        have hsmul (a : R p) (w : V) : f (a • w) = a • f w := by
          change f (algebraMap (R p) ℂ a • w) = algebraMap (R p) ℂ a • f w
          exact f.map_smul _ _
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul a m =>
          simp only [rop, LinearMap.baseChange_tmul, mu, LinearMap.liftBaseChange_tmul,
            Submodule.subtype_apply, hop, hsmul]
        | add z w hz hw => simp only [map_add, hz, hw]
    refine ⟨hRing, hInj, hBS.1, hBS.2, ?_, ?_⟩
    · intro r
      exact ⟨hcomm (dp x r) (h_H005.2 r).1,
        hcomm (dp y r) (h_H005.2 r).2⟩
    · intro r w hw
      obtain ⟨z, rfl⟩ := hw
      constructor
      · exact ⟨rop p M (dp x r) z, hcomm (dp x r) (h_H005.2 r).1 z⟩
      · exact ⟨rop p M (dp y r) z, hcomm (dp y r) (h_H005.2 r).2 z⟩

theorem T006 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : ComplexOutput lam x y h v) (h_T005 : LocalBasics p lam M x y) :
    MatrixOutput p lam M x y v := by
  classical
  have hu : ∀ j : Fin (lam.toNat + 1), IsUnit (Nat.choose lam.toNat j.val : R p) ∧ ∃ a : R p, algebraMap (R p) ℂ a = (Nat.choose lam.toNat j.val : ℂ)⁻¹ := by
    intro j
    have hn : lam.toNat < p := by omega
    have hj : j.val ≤ lam.toNat := by omega
    have hnd : ¬ p ∣ Nat.choose lam.toNat j.val := by
      intro hd
      have hfac : p ∣ lam.toNat.factorial := by
        rw [← Nat.choose_mul_factorial_mul_factorial hj]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
      exact (not_le_of_gt hn) ((h_H001.1.dvd_factorial).mp hfac)
    have hnz : (Nat.choose lam.toNat j.val : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj).ne'
    have hin : (Nat.choose lam.toNat j.val : ℚ)⁻¹ ∈ R p := by
      apply h_T005.1 _ |>.mpr
      refine ⟨1, (Nat.choose lam.toNat j.val : ℤ), ?_, ?_⟩
      · simpa only [Int.natCast_dvd_natCast] using hnd
      · simp
    let a : R p := ⟨_, hin⟩
    have ha : (Nat.choose lam.toNat j.val : R p) * a = 1 := by
      apply Subtype.ext
      change (Nat.choose lam.toNat j.val : ℚ) * (Nat.choose lam.toNat j.val : ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ hnz
    refine ⟨?_, a, ?_⟩
    · exact isUnit_iff_exists_inv.mpr ⟨a, ha⟩
    · change algebraMap ℚ ℂ ((Nat.choose lam.toNat j.val : ℚ)⁻¹) = _
      simp
  have hm : ∀ (B : Module.Basis (Fin (lam.toNat + 1)) ℂ V), (∀ i, B i = e y v i.val) → ∀ i j, unit B i j = ((Nat.choose lam.toNat j.val : ℂ)⁻¹) • (dp x (lam.toNat - i.val) * dp y lam.toNat * dp x lam.toNat * dp y (lam.toNat - j.val)) := by
    classical
    rcases h_T004 with ⟨hpos, hcard, hcoords, hstrings, hkill, hact, hx, hy⟩
    let top : Fin (lam.toNat + 1) := ⟨lam.toNat, by omega⟩
    let bot : Fin (lam.toNat + 1) := ⟨0, by omega⟩
    have hX (k : Fin (lam.toNat + 1)) :
        dp x lam.toNat (e y v k.val) = if k.val = lam.toNat then e y v 0 else 0 := by
      rw [hx]
      by_cases hk : k.val = lam.toNat
      · simp [hk]
      · have hlt : k.val < lam.toNat := by omega
        simp [Nat.not_le.mpr hlt, hk]
    have hY : dp y lam.toNat (e y v 0) = e y v lam.toNat := by
      simpa [bot] using hy lam.toNat bot
    have hXi (i : Fin (lam.toNat + 1)) :
        dp x (lam.toNat - i.val) (e y v lam.toNat) = e y v i.val := by
      have hi : i.val ≤ lam.toNat := by omega
      have heq : lam.toNat - (lam.toNat - i.val) = i.val := by omega
      have heq' : lam.toNat - lam.toNat + (lam.toNat - i.val) = lam.toNat - i.val := by omega
      simpa [top, Nat.sub_le, heq, heq'] using hx (lam.toNat - i.val) top
    let Q := dp y lam.toNat * dp x lam.toNat
    have hQ (k : Fin (lam.toNat + 1)) :
        Q (e y v k.val) = if k.val = lam.toNat then e y v lam.toNat else 0 := by
      change dp y lam.toNat (dp x lam.toNat (e y v k.val)) = _
      rw [hX]
      split_ifs <;> simp_all only [map_zero]
    have hQY (j k : Fin (lam.toNat + 1)) :
        Q (dp y (lam.toNat - j.val) (e y v k.val)) =
          if k = j then (Nat.choose lam.toNat j.val : ℂ) • e y v lam.toNat else 0 := by
      rw [hy]
      by_cases hkj : k = j
      · subst k
        have hj : j.val ≤ lam.toNat := by omega
        have hs : j.val + (lam.toNat - j.val) = lam.toNat := by omega
        simp only [hs, le_refl, ↓reduceIte, map_smul]
        rw [show e y v lam.toNat = e y v top.val from rfl, hQ]
        simp only [top, ↓reduceIte]
        rw [Nat.choose_symm hj]
      · by_cases hle : k.val + (lam.toNat - j.val) ≤ lam.toNat
        · let l : Fin (lam.toNat + 1) := ⟨k.val + (lam.toNat - j.val), by omega⟩
          have hne : l.val ≠ lam.toNat := by
            have hv : k.val ≠ j.val := fun hh => hkj (Fin.ext hh)
            dsimp [l]
            omega
          simp only [hle, ↓reduceIte, map_smul]
          rw [show e y v (k.val + (lam.toNat - j.val)) = e y v l.val from rfl, hQ]
          simp [hne, hkj]
        · simp [hle, hkj]
    intro B hB i j
    have hc : (Nat.choose lam.toNat j.val : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (show j.val ≤ lam.toNat by omega)).ne'
    apply B.ext
    intro k
    change unit B i j (B k) = _
    rw [hB k]
    change unit B i j (e y v k.val) =
      (Nat.choose lam.toNat j.val : ℂ)⁻¹ •
        dp x (lam.toNat - i.val) (Q (dp y (lam.toNat - j.val) (e y v k.val)))
    rw [hQY]
    by_cases hk : k = j
    · subst k
      simp only [↓reduceIte, map_smul, hXi, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [← hB j]
      simp [unit, hB i]
    · simp only [hk, ↓reduceIte, map_zero, smul_zero]
      rw [← hB k]
      simp [unit, Ne.symm hk]
  refine ⟨h_T005, fun j => (hu j).1, ?_⟩
  intro B hB i j
  refine ⟨hm B hB i j, ?_⟩
  intro w hw
  rw [hm B hB i j]
  obtain ⟨a, ha⟩ := (hu j).2
  have hz : (dp x (lam.toNat - i.val) * dp y lam.toNat * dp x lam.toNat *
      dp y (lam.toNat - j.val)) w ∈ image p M := by
    simp only [Module.End.mul_apply]
    have hs := h_T005.2.2.2.2.2
    exact (hs _ _ ((hs _ _ ((hs _ _ ((hs _ _ hw).2)).1)).2)).1
  change (Nat.choose lam.toNat j.val : ℂ)⁻¹ •
      ((dp x (lam.toNat - i.val) * dp y lam.toNat * dp x lam.toNat *
      dp y (lam.toNat - j.val)) w) ∈ image p M
  rw [← ha]
  exact (image p M).smul_mem a hz

theorem T007 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_T004 : ComplexOutput lam x y h v) (h_T006 : MatrixOutput p lam M x y v) :
    CommonOutput p lam M x y v := by
  classical
  letI : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V
  letI : IsScalarTower (R p) ℂ ℂ := IsScalarTower.of_compHom (R p) ℂ ℂ
  have hbas : LocalBasics p lam M x y := h_T006.1
  obtain ⟨B, hB⟩ := h_T004.2.2.1
  let I := Fin (lam.toNat + 1)
  let i0 : I := ⟨0, Nat.zero_lt_succ _⟩
  have hmem : ∀ (i : I) (c : ℂ), c ∈ Ji p M y v i.val ↔ c • B i ∈ image p M := by
    intro i c
    change c • e y v i.val ∈ image p M ↔ _
    rw [hB i]
  have hu : ∀ (i j : I) (w : V), unit B i j w = (B.coord j w) • B i := by
    intro i j w
    rfl
  have hstable : ∀ (i j : I) (w : V), w ∈ image p M → unit B i j w ∈ image p M :=
    fun i j w hw => (h_T006.2.2 B hB i j).2 w hw
  have hinc : ∀ (i j : I), Ji p M y v j.val ≤ Ji p M y v i.val := by
    intro i j c hc
    apply (hmem i c).2
    have ht := hstable i j (c • B j) ((hmem j c).1 hc)
    simpa [hu, Module.Basis.coord_apply] using ht
  have heq : ∀ i : I, Ji p M y v i.val = Ji p M y v 0 := by
    intro i
    exact le_antisymm (hinc i0 i) (hinc i i0)
  let C : I → MR p M →ₗ[R p] ℂ :=
    fun i => ((B.coord i).restrictScalars (R p)).comp (mu p M)
  have hC : ∀ (i : I) (z : MR p M), C i z = B.coord i (mu p M z) := by
    intros
    rfl
  have hcoord : ∀ (i : I) (w : V), w ∈ image p M → B.coord i w ∈ Ji p M y v i.val := by
    intro i w hw
    apply (hmem i _).2
    rw [← hu i i w]
    exact hstable i i w hw
  have hrange : ∀ i : I, LinearMap.range (C i) = Ji p M y v i.val := by
    intro i
    ext c
    constructor
    · rintro ⟨z, rfl⟩
      exact hcoord i _ ⟨z, rfl⟩
    · intro hc
      obtain ⟨z, hz⟩ := (hmem i c).1 hc
      refine ⟨z, ?_⟩
      rw [hC, hz]
      simp [Module.Basis.coord_apply]

  obtain ⟨BR⟩ := hbas.2.2.1
  letI : Module.Finite (R p) (MR p M) := Module.Finite.of_basis BR
  have hfg : (Ji p M y v 0).FG := by
    rw [← hrange i0]
    exact Submodule.fg_range (C i0)
  have hne : Ji p M y v 0 ≠ ⊥ := by
    intro hj
    have hz : image p M = ⊥ := by
      apply le_antisymm
      · intro w hw
        have hw0 : w = 0 := by
          apply B.forall_coord_eq_zero_iff.mp
          intro i
          have hc := hcoord i w hw
          rw [heq i, hj] at hc
          exact hc
        simpa only [Submodule.mem_bot] using hw0
      · exact bot_le
    have ht : (⊤ : Submodule ℂ V) = ⊥ := by
      rw [← hbas.2.2.2.1, hz]
      simp
    have hb0 : B i0 = 0 := by
      have hm : B i0 ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
      rw [ht] at hm
      exact hm
    exact B.ne_zero i0 hb0

  let J := Ji p M y v 0
  have hCJ : ∀ (i : I) (z : MR p M), C i z ∈ J := by
    intro i z
    change C i z ∈ Ji p M y v 0
    rw [← heq i, ← hrange i]
    exact ⟨z, rfl⟩
  let G : MR p M →ₗ[R p] (I → J) :=
    { toFun := fun z i => ⟨C i z, hCJ i z⟩
      map_add' := by
        intro z z'
        funext i
        apply Subtype.ext
        exact (C i).map_add z z'
      map_smul' := by
        intro a z
        funext i
        apply Subtype.ext
        exact (C i).map_smul a z }
  have hbij : Function.Bijective G := by
    constructor
    · intro z z' hzz
      apply hbas.2.1
      apply B.ext_elem
      intro i
      exact congrArg (fun c : I → J => (c i : ℂ)) hzz
    · intro c
      have hw : (∑ i : I, (c i : ℂ) • B i) ∈ image p M := by
        apply Submodule.sum_mem
        intro i _
        apply (hmem i _).1
        rw [heq i]
        exact (c i).property
      obtain ⟨z, hz⟩ := hw
      refine ⟨z, ?_⟩
      funext i
      apply Subtype.ext
      change C i z = (c i : ℂ)
      rw [hC, hz]
      simp only [map_sum, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simpa only [Finset.mem_univ, if_true] using
        (Finset.sum_ite_eq' Finset.univ i (fun j => (c j : ℂ)))
  let F : (I → J) ≃ₗ[R p] MR p M := (LinearEquiv.ofBijective G hbij).symm
  refine ⟨h_T004.1, ⟨B, hB⟩, hbas, heq, hfg, hne, F, ?_⟩
  intro c
  have hg : G (F c) = c := LinearEquiv.apply_ofBijective_symm_apply G (h := hbij) c
  calc
    mu p M (F c) = ∑ i : I, B.coord i (mu p M (F c)) • B i :=
      (B.sum_repr _).symm
    _ = ∑ i, (c i : ℂ) • e y v i.val := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := congrArg (fun d : I → J => (d i : ℂ)) hg
      change B.coord i (mu p M (F c)) = (c i : ℂ) at hi
      rw [hi, hB i]

theorem T008 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_T007 : CommonOutput p lam M x y v) :
    FractionData p M y v := by
  let J := Ji p M y v 0
  letI : IsFractionRing (R p) ℚ := by
    apply IsFractionRing.of_field
    intro q
    refine ⟨(q.num : R p), (q.den : R p), ?_⟩
    simpa using (Rat.num_div_den q).symm
  letI tw : IsScalarTower (R p) ℚ ℂ :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  let theta : (ℚ ⊗[R p] J) →ₗ[ℚ] ℂ :=
    @LinearMap.liftBaseChange (R p) J ℂ ℚ _ _ _ _ _ _ _ _ tw J.subtype
  have htheta : ∀ (q : ℚ) (c : J),
      theta (TensorProduct.tmul (R p) q c) = (q : ℂ) * (c : ℂ) := by
    intro q c
    rfl
  have hker : ∀ z, theta z = 0 → z = 0 := by
    intro z hz
    obtain ⟨⟨c, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors (R p))
      (TensorProduct.mk (R p) ℚ J 1) z
    have hsQ : ((s.val : R p) : ℚ) • z = TensorProduct.tmul (R p) (1 : ℚ) c :=
      (IsScalarTower.algebraMap_smul ℚ s.val z).trans hs
    have hc : (c : ℂ) = 0 := by
      have hm := congrArg theta hsQ
      rw [map_smul, hz, smul_zero, htheta] at hm
      simpa only [Rat.cast_one, one_mul] using hm.symm
    have hc0 : c = 0 := Subtype.ext hc
    have hs0 : ((s.val : R p) : ℚ) • z = 0 := by
      simpa only [hc0, TensorProduct.tmul_zero] using hsQ
    have hsne : ((s.val : R p) : ℚ) ≠ 0 :=
      Subtype.coe_injective.ne (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
    exact (smul_eq_zero.mp hs0).resolve_left hsne
  have hinj : Function.Injective theta := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hab, sub_self]
  have hfg : J.FG := h_T007.2.2.2.2.1
  letI : Module.Finite (R p) J := Module.Finite.iff_fg.mpr hfg
  change (∃ theta : (ℚ ⊗[R p] J) →ₗ[ℚ] ℂ,
    (∀ (q : ℚ) (c : J), theta (TensorProduct.tmul (R p) q c) =
      (q : ℂ) * (c : ℂ)) ∧ Function.Injective theta) ∧
    FiniteDimensional ℚ (ℚ ⊗[R p] J)
  exact ⟨⟨theta, htheta, hinj⟩, inferInstance⟩

theorem T009 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_T007 : CommonOutput p lam M x y v) (h_T008 : FractionData p M y v) :
    RationalLine p M y v := by
  classical
  let J := Ji p M y v 0
  let T := ℚ ⊗[R p] J
  obtain ⟨⟨theta, ht, hinj⟩, hfinite⟩ := h_T008
  letI : FiniteDimensional ℚ T := hfinite
  obtain ⟨F, hF⟩ := h_T007.2.2.2.2.2.2
  obtain ⟨BR⟩ := h_T007.2.2.1.2.2.1
  let E : (ℚ ⊗[R p] MR p M) ≃ₗ[ℚ] (Fin (lam.toNat + 1) → T) :=
    (F.symm.baseChange (R p) ℚ _ _).trans
      (TensorProduct.piRight (R p) ℚ ℚ (fun _ : Fin (lam.toNat + 1) => J))
  have hd : Module.finrank ℚ (ℚ ⊗[R p] MR p M) = lam.toNat + 1 := by
    simpa using Module.finrank_eq_card_basis (BR.baseChange ℚ)
  have hp : Module.finrank ℚ (Fin (lam.toNat + 1) → T) =
      (lam.toNat + 1) * Module.finrank ℚ T := by
    simpa using (Module.finrank_pi_fintype ℚ (M := fun _ : Fin (lam.toNat + 1) => T))
  have he : (lam.toNat + 1) * Module.finrank ℚ T = lam.toNat + 1 := by
    rw [← hp, ← E.finrank_eq, hd]
  have hrank : Module.finrank ℚ T = 1 := by nlinarith
  change Module.finrank ℚ T = 1 ∧ _
  refine ⟨hrank, ?_⟩
  intro a ha ha0 c hc
  let A : T := TensorProduct.tmul (R p) (1 : ℚ) ⟨a, ha⟩
  let C : T := TensorProduct.tmul (R p) (1 : ℚ) ⟨c, hc⟩
  have hA : theta A = a := by simp [A, ht]
  have hC : theta C = c := by simp [C, ht]
  have hA0 : A ≠ 0 := by
    intro hz
    apply ha0
    rw [← hA, hz, map_zero]
  have hs (q : ℚ) : theta (q • A) = (q : ℂ) * a := by
    rw [map_smul, hA]
    simp [Algebra.smul_def]
  obtain ⟨q, hq⟩ := (finrank_eq_one_iff_of_nonzero' A hA0).mp hrank C
  have hqc : c = (q : ℂ) * a := by rw [← hC, ← hq, hs]
  refine ⟨q, hqc, ?_⟩
  intro r hr
  have heq : r • A = q • A := hinj (by rw [hs, hs, ← hr, ← hqc])
  exact smul_left_injective ℚ hA0 heq

theorem T010 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_T007 : CommonOutput p lam M x y v) (h_T009 : RationalLine p M y v) :
    PrincipalOutput p lam M y v := by
  classical
  have hprincipal : ∃ b : ℂ, b ∈ Ji p M y v 0 ∧ b ≠ 0 ∧ Ji p M y v 0 = Submodule.span (R p) {b} := by
    classical
    have hfactor : ∀ q : ℚ, q ≠ 0 → ∃ (d : ℤ) (u : ℚ), q = (p : ℚ) ^ d * u ∧ u ∈ R p ∧ u⁻¹ ∈ R p := by
      classical
      intro q hq
      have hp := h_H001.1
      have hcarrier := h_T007.2.2.1.1
      letI : Fact p.Prime := ⟨hp⟩
      have hfinA : FiniteMultiplicity (p : ℤ) q.num := (padicValRat.finite_int_prime_iff (p := p)).mpr (Rat.num_ne_zero.mpr hq)
      have hfinB : FiniteMultiplicity (p : ℤ) (q.den : ℤ) := (padicValRat.finite_int_prime_iff (p := p)).mpr (by exact_mod_cast q.den_ne_zero)
      obtain ⟨a, ha, hpa⟩ := hfinA.exists_eq_pow_mul_and_not_dvd
      obtain ⟨b, hb, hpb⟩ := hfinB.exists_eq_pow_mul_and_not_dvd
      refine ⟨(multiplicity (p : ℤ) q.num : ℤ) - (multiplicity (p : ℤ) (q.den : ℤ) : ℤ), (a : ℚ) / b, ?_, ?_, ?_⟩
      · have hnum : (q.num : ℚ) = (p : ℚ) ^ multiplicity (p : ℤ) q.num * a := by exact_mod_cast ha
        have hden : (q.den : ℚ) = (p : ℚ) ^ multiplicity (p : ℤ) (q.den : ℤ) * b := by exact_mod_cast hb
        rw [zpow_sub₀ (by exact_mod_cast hp.ne_zero), zpow_natCast, zpow_natCast]
        calc
          q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
          _ = _ := by rw [hnum, hden]; ring
      · exact (hcarrier _).mpr ⟨a, b, hpb, rfl⟩
      · apply (hcarrier _).mpr
        refine ⟨b, a, hpa, ?_⟩
        simp [inv_div]
    let J := Ji p M y v 0
    have hfg : J.FG := h_T007.2.2.2.2.1
    have hne : J ≠ ⊥ := h_T007.2.2.2.2.2.1
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := hfg
    have hsJ : ∀ g ∈ s, g ∈ J := by
      intro g hg
      rw [← hs]
      exact Submodule.subset_span hg
    let t := s.filter (fun g => g ≠ 0)
    have ht : t.Nonempty := by
      by_contra hh
      have hzero : J = ⊥ := by
        rw [← hs]
        apply le_antisymm
        · apply Submodule.span_le.mpr
          intro g hg
          have : g = 0 := by
            by_contra hg0
            exact hh ⟨g, Finset.mem_filter.mpr ⟨hg, hg0⟩⟩
          simp [this]
        · exact bot_le
      exact hne hzero
    have hdata : ∀ g : t, ∃ (d : ℤ) (u : ℚ), (g : ℂ) = (((p : ℚ) ^ d * u : ℚ) : ℂ) * a ∧ u ∈ R p ∧ u⁻¹ ∈ R p := by
      intro g
      have hg := Finset.mem_filter.mp g.property
      obtain ⟨q, hq, _⟩ := h_T009.2 a ha ha0 g (hsJ g hg.1)
      have hq0 : q ≠ 0 := by
        intro hh
        apply hg.2
        simp [hh] at hq
        exact hq
      obtain ⟨d, u, hu, huR, huiR⟩ := hfactor q hq0
      exact ⟨d, u, hu ▸ hq, huR, huiR⟩
    choose d u hgu huR huiR using hdata
    haveI : Nonempty t := ⟨⟨ht.choose, ht.choose_spec⟩⟩
    obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image d Finset.univ_nonempty
    let b : ℂ := (((p : ℚ) ^ d j : ℚ) : ℂ) * a
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast h_H001.1.ne_zero
    have hb0 : b ≠ 0 := mul_ne_zero (by exact_mod_cast zpow_ne_zero (d j) hp0) ha0
    have hu0 : u j ≠ 0 := by
      intro hh
      have hg0 := (Finset.mem_filter.mp j.property).2
      apply hg0
      simpa [hh] using hgu j
    have hbJ : b ∈ J := by
      have hgj : (j : ℂ) ∈ J := hsJ j (Finset.mem_filter.mp j.property).1
      have heq : (⟨(u j)⁻¹, huiR j⟩ : R p) • (j : ℂ) = b := by
        change (((u j)⁻¹ : ℚ) : ℂ) * (j : ℂ) = b
        rw [hgu j]
        dsimp [b]
        push_cast
        field_simp
      rw [← heq]
      exact J.smul_mem _ hgj
    have hspan : J = Submodule.span (R p) {b} := by
      apply le_antisymm
      · rw [← hs]
        apply Submodule.span_le.mpr
        intro g hg
        by_cases hg0 : g = 0
        · simp [hg0]
        let k : t := ⟨g, Finset.mem_filter.mpr ⟨hg, hg0⟩⟩
        have hle : d j ≤ d k := hj k (Finset.mem_univ _)
        have hpowR : (p : ℚ) ^ (d k - d j) ∈ R p := by
          have he : (d k - d j) = ((d k - d j).toNat : ℤ) := (Int.toNat_of_nonneg (sub_nonneg.mpr hle)).symm
          rw [he, zpow_natCast]
          exact (R p).pow_mem (natCast_mem (R p) p) _
        refine Submodule.mem_span_singleton.mpr ⟨⟨(p : ℚ) ^ (d k - d j) * u k, (R p).mul_mem hpowR (huR k)⟩, ?_⟩
        change ((((p : ℚ) ^ (d k - d j) * u k : ℚ) : ℂ)) * b = g
        have hz : (p : ℚ) ^ (d k - d j) * (p : ℚ) ^ d j = (p : ℚ) ^ d k := by
          rw [← zpow_add₀ hp0]
          congr 1
          omega
        calc
          _ = ((((p : ℚ) ^ (d k - d j) * (p : ℚ) ^ d j) * u k : ℚ) : ℂ) * a := by
            dsimp [b]
            push_cast
            ring
          _ = g := by rw [hz]; exact (hgu k).symm
      · exact (Submodule.span_singleton_le_iff_mem b J).mpr hbJ
    exact ⟨b, hbJ, hb0, hspan⟩
  obtain ⟨b, hb, hb0, hspan⟩ := hprincipal
  refine ⟨b, hb, hb0, hspan, ?_⟩
  let J := Ji p M y v 0
  let f : R p →ₗ[R p] J :=
    (LinearMap.toSpanSingleton (R p) ℂ b).codRestrict J (fun r => J.smul_mem r hb)
  have hfi : Function.Injective f := by
    intro r s hrs
    have heq : ((r : ℚ) : ℂ) * b = ((s : ℚ) : ℂ) * b := congrArg Subtype.val hrs
    have hrq : (r : ℚ) = (s : ℚ) := Rat.cast_injective (mul_right_cancel₀ hb0 heq)
    exact Subtype.ext hrq
  have hfs : Function.Surjective f := by
    intro c
    have hc : (c : ℂ) ∈ Submodule.span (R p) {b} := hspan ▸ c.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hc
    exact ⟨r, Subtype.ext hr⟩
  let E : R p ≃ₗ[R p] J := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  have hE : ∀ r : R p, ((E r : J) : ℂ) = ((r : ℚ) : ℂ) * b := fun r => rfl
  obtain ⟨F, hF⟩ := h_T007.2.2.2.2.2.2
  let G : (Fin (lam.toNat + 1) → R p) ≃ₗ[R p] MR p M :=
    (LinearEquiv.piCongrRight (fun _ : Fin (lam.toNat + 1) => E)).trans F
  let B := (Pi.basisFun (R p) (Fin (lam.toNat + 1))).map G
  refine ⟨B, ?_⟩
  intro i
  change mu p M (G (Pi.basisFun (R p) (Fin (lam.toNat + 1)) i)) = _
  rw [LinearEquiv.trans_apply, hF]
  simp [Pi.basisFun_apply, LinearEquiv.piCongrRight_apply, hE, Pi.single_apply, apply_ite, ite_mul, ite_smul]

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
    have hinj : Function.Injective (algebraMap (ZMod p) K) := ZMod.castHom_injective K
    exact (RingHom.ker_comp_of_injective s hinj).trans hs
  · intro r a b hb hr
    change algebraMap (ZMod p) K (s r) = _
    rw [hsfrac r a b hb hr, map_div₀, map_intCast, map_intCast]
  · letI : Algebra (R p) K := rho.toAlgebra
    obtain ⟨phi,hphi,hnat⟩ := hphiData rho
    refine ⟨phi,hphi,hnat,?_⟩
    exact hetaData s hs (ZMod.ringHom_surjective s) hc

theorem T012 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
    ∃ bC : Module.Basis (Fin d) ℂ V, ∀ i, bC i = (bZ i : V)) ∧
  ∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r)) (h_T004 : ComplexOutput lam x y h v) (h_T006 : MatrixOutput p lam M x y v) (h_T010 : PrincipalOutput p lam M y v) (h_T011 : ScalarExtensionData p K M) :
    ReducedBasisData p K lam M x y h v := by
  classical
  have hx : Stable M x := by simpa [dp] using (h_H005.2 1).1
  have hy : Stable M y := by simpa [dp] using (h_H005.2 1).2
  have hh : Stable M h := by
    intro w hw
    rw [← h_H003.2.2]
    change x (y w) - y (x w) ∈ M
    exact M.sub_mem (hx _ (hy _ hw)) (hy _ (hx _ hw))
  have hmu : ∀ (f : Module.End ℂ V), Stable M f →
      ∀ z : MR p M, mu p M (rop p M f z) = f (mu p M z) := by
    intro f hf z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [rop, LinearMap.baseChange_tmul, mu, LinearMap.liftBaseChange_tmul]
      change r • ((latticeOp M f m : M) : V) = f (r • (m : V))
      have hm : ((latticeOp M f m : M) : V) = f (m : V) := by
        simp [latticeOp, hf]
      rw [hm]
      change (algebraMap (R p) ℂ r) • f (m : V) =
        f ((algebraMap (R p) ℂ r) • (m : V))
      exact (f.map_smul _ _).symm
    | add a b ha hb => simp only [map_add, ha, hb]
  have hinj : Function.Injective (mu p M) := h_T006.1.2.1
  rcases h_T010 with ⟨b, hbmem, hbne, hbspan, BR, hBR⟩
  letI : CharP K p := h_H001.2.1
  rcases h_T011 h_H001.2.1 with ⟨rho, hrhoker, hrho, phi, hphi_tmul, hphi, hrest⟩
  letI : Algebra (R p) K := rho.toAlgebra
  let B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M) :=
    (BR.baseChange K).map phi.symm
  have hB (i : Fin (lam.toNat + 1)) :
      phi (B i) = TensorProduct.tmul (R p) (1 : K) (BR i) := by
    simp [B]
  have htransport (f : Module.End ℂ V) (hf : Stable M f)
      (z w : MR p M) (he : f (mu p M z) = mu p M w) :
      kop K M f (phi.symm (TensorProduct.tmul (R p) (1 : K) z)) =
        phi.symm (TensorProduct.tmul (R p) (1 : K) w) := by
    apply phi.injective
    rw [hphi f hf, phi.apply_symm_apply, LinearMap.baseChange_tmul]
    have hz : rop p M f z = w := hinj ((hmu f hf z).trans he)
    change TensorProduct.tmul (R p) (1 : K) (rop p M f z) = _
    rw [hz, phi.apply_symm_apply]
  have hcoeff (f : Module.End ℂ V) (hf : Stable M f)
      (i j : Fin (lam.toNat + 1)) (a : ℤ)
      (he : f (e y v i.val) = (a : ℂ) • e y v j.val) :
      kop K M f (B i) = (a : K) • B j := by
    have he' : f (mu p M (BR i)) = mu p M (a • BR j) := by
      rw [hBR, f.map_smul, he, map_zsmul, hBR]
      rw [← Int.cast_smul_eq_zsmul ℂ a]
      exact smul_comm b (a : ℂ) (e y v j.val)
    have ht := htransport f hf (BR i) (a • BR j) he'
    simpa [B, ← Int.cast_smul_eq_zsmul K] using ht
  have hzero (f : Module.End ℂ V) (hf : Stable M f)
      (i : Fin (lam.toNat + 1)) (he : f (e y v i.val) = 0) :
      kop K M f (B i) = 0 := by
    have he' : f (mu p M (BR i)) = mu p M 0 := by
      rw [hBR, f.map_smul, he, smul_zero, map_zero]
    have ht := htransport f hf (BR i) 0 he'
    simpa [B] using ht
  rcases h_T004.2.2.1 with ⟨BC, hBC⟩
  have hac : Actions lam x y h BC := h_T004.2.2.2.2.2.1 BC hBC
  refine ⟨rho, phi, hphi_tmul, hphi, b, hbne, BR, hBR, B, hB, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val = 0
    · rw [if_pos hi]
      apply hzero x hx i
      have ht := hac.1 i
      simpa [hBC, hi] using ht
    · rw [if_neg hi]
      have hj : i.val - 1 < lam.toNat + 1 := by omega
      let j : Fin (lam.toNat + 1) := ⟨i.val - 1, hj⟩
      have he : x (e y v i.val) =
          ((lam - (i.val : ℤ) + 1 : ℤ) : ℂ) • e y v j.val := by
        have ht := hac.1 i
        simpa [hBC, hi, basisAt, hj, j] using ht
      simpa [basisAt, hj, j] using hcoeff x hx i j (lam - (i.val : ℤ) + 1) he
  · intro i
    by_cases hi : i.val < lam.toNat
    · rw [if_pos hi]
      have hj : i.val + 1 < lam.toNat + 1 := by omega
      let j : Fin (lam.toNat + 1) := ⟨i.val + 1, hj⟩
      have he : y (e y v i.val) = ((i.val + 1 : ℕ) : ℂ) • e y v j.val := by
        have ht := hac.2.1 i
        simpa [hBC, hi, basisAt, hj, j] using ht
      have ht := hcoeff y hy i j (Int.ofNat (i.val + 1)) (by simpa using he)
      simpa [basisAt, hj, j] using ht
    · rw [if_neg hi]
      apply hzero y hy i
      have ht := hac.2.1 i
      simpa [hBC, hi] using ht
  · intro i
    apply hcoeff h hh i i (lam - 2 * (i.val : ℤ))
    simpa [hBC] using hac.2.2 i

theorem T013 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
    ∃ bC : Module.Basis (Fin d) ℂ V, ∀ i, bC i = (bZ i : V)) ∧
  ∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r)) (h_T004 : ComplexOutput lam x y h v) (h_T006 : MatrixOutput p lam M x y v) (h_T010 : PrincipalOutput p lam M y v) (h_T011 : ScalarExtensionData p K M) (h_T012 : ReducedBasisData p K lam M x y h v) :
    ReducedOutput K lam M x y h := by
  classical
  have happ (f : Module.End ℂ V) (hf : Stable M f) (w : M) :
      ((latticeOp M f w : M) : V) = f w := by
    rw [latticeOp, dif_pos hf]
    rfl
  have hx : Stable M x := by simpa [dp] using (h_H005.2 1).1
  have hy : Stable M y := by simpa [dp] using (h_H005.2 1).2
  have hh : Stable M h := by
    intro w hw
    rw [← h_H003.2.2]
    exact M.sub_mem (hx _ (hy w hw)) (hy _ (hx w hw))
  have hpw (f : Module.End ℂ V) (hf : Stable M f) (r : ℕ) (w : M) :
      (((latticeOp M f) ^ r) w : V) = (f ^ r) w := by
    induction r generalizing w with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', pow_succ']
      change ((latticeOp M f (((latticeOp M f) ^ r) w)) : V) = f ((f ^ r) w)
      rw [happ f hf, ih]
  let G : Module.End ℤ M →+* Module.End K (VK K M) :=
    (Module.End.baseChangeHom ℤ K M).toRingHom
  have hG (f : Module.End ℂ V) : G (latticeOp M f) = kop K M f := rfl
  have hGsub (a b : Module.End ℤ M) : G (a - b) = G a - G b :=
    map_sub G a b
  have hGmul (a b : Module.End ℤ M) : G (a*b) = G a * G b := map_mul G a b
  have hGz (n : ℤ) (a : Module.End ℤ M) : G (n • a) = n • G a :=
    map_zsmul G n a
  have hGn (n : ℕ) (a : Module.End ℤ M) : G (n • a) = n • G a :=
    map_nsmul G n a
  have hGp (a : Module.End ℤ M) (r : ℕ) : G (a^r) = G a ^ r := map_pow G a r
  have hxyZ : latticeOp M x * latticeOp M y - latticeOp M y * latticeOp M x = latticeOp M h := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ((latticeOp M x (latticeOp M y w) : M) : V) -
      ((latticeOp M y (latticeOp M x w) : M) : V) = ((latticeOp M h w : M) : V)
    rw [happ x hx, happ y hy, happ y hy, happ x hx, happ h hh]
    exact congrArg (fun f : Module.End ℂ V => f (w : V)) h_H003.2.2
  have hhxZ : latticeOp M h * latticeOp M x - latticeOp M x * latticeOp M h =
      (2 : ℤ) • latticeOp M x := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ((latticeOp M h (latticeOp M x w) : M) : V) -
      ((latticeOp M x (latticeOp M h w) : M) : V) = (2 : ℤ) • ((latticeOp M x w : M) : V)
    rw [happ h hh, happ x hx, happ x hx, happ h hh]
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      ← Int.cast_smul_eq_zsmul ℂ, Int.cast_ofNat] using
      congrArg (fun f : Module.End ℂ V => f (w : V)) h_H003.1
  have hhyZ : latticeOp M h * latticeOp M y - latticeOp M y * latticeOp M h =
      (-2 : ℤ) • latticeOp M y := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ((latticeOp M h (latticeOp M y w) : M) : V) -
      ((latticeOp M y (latticeOp M h w) : M) : V) = (-2 : ℤ) • ((latticeOp M y w : M) : V)
    rw [happ h hh, happ y hy, happ y hy, happ h hh]
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      ← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg, Int.cast_ofNat] using
      congrArg (fun f : Module.End ℂ V => f (w : V)) h_H003.2.1
  have hbr1 : kop K M h = kop K M x * kop K M y - kop K M y * kop K M x := by
    have eqn := (congrArg G hxyZ).symm
    rw [hGsub, hGmul, hGmul, hG, hG, hG] at eqn
    exact eqn
  have hbr2 : kop K M h * kop K M x - kop K M x * kop K M h = (2 : K) • kop K M x := by
    have eqn := congrArg G hhxZ
    rw [hGsub, hGmul, hGmul, hGz, hG, hG] at eqn
    simpa only [← Int.cast_smul_eq_zsmul K, Int.cast_ofNat] using eqn
  have hbr3 : kop K M h * kop K M y - kop K M y * kop K M h = (-2 : K) • kop K M y := by
    have eqn := congrArg G hhyZ
    rw [hGsub, hGmul, hGmul, hGz, hG, hG] at eqn
    simpa only [← Int.cast_smul_eq_zsmul K, Int.cast_neg, Int.cast_ofNat] using eqn
  letI : CharP K p := h_H001.2.1
  have hlp : lam.toNat < p := by omega
  have hfac (r : ℕ) (hr : r ≤ lam.toNat) : (r.factorial : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p, h_H001.1.dvd_factorial]
    omega
  have hdiv (f : Module.End ℂ V) (hf : Stable M f) (r : ℕ)
      (hd : Stable M (dp f r)) (hr : r ≤ lam.toNat) :
      (latticeOp M (dp f r)).baseChange K = kdp (kop K M f) r := by
    have heq : r.factorial • latticeOp M (dp f r) = latticeOp M f ^ r := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      change r.factorial • ((latticeOp M (dp f r) w : M) : V) =
        (((latticeOp M f) ^ r) w : V)
      rw [happ (dp f r) hd, hpw f hf, ← Nat.cast_smul_eq_nsmul ℂ]
      simp only [dp, LinearMap.smul_apply, smul_smul,
        mul_inv_cancel₀ (show (r.factorial : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)), one_smul]
    have eqn := congrArg G heq
    rw [hGn, hGp, hG, hG] at eqn
    have heqK : (r.factorial : K) • kop K M (dp f r) = kop K M f ^ r := by
      simpa only [Nat.cast_smul_eq_nsmul] using eqn
    change kop K M (dp f r) = _
    calc
      _ = (r.factorial : K)⁻¹ • ((r.factorial : K) • kop K M (dp f r)) :=
        (inv_smul_smul₀ (hfac r hr) _).symm
      _ = _ := by rw [heqK]; rfl
  have hdx (r : ℕ) (hr : r ≤ lam.toNat) :
      (latticeOp M (dp x r)).baseChange K = kdp (kop K M x) r :=
    hdiv x hx r (h_H005.2 r).1 hr
  have hdy (r : ℕ) (hr : r ≤ lam.toNat) :
      (latticeOp M (dp y r)).baseChange K = kdp (kop K M y) r :=
    hdiv y hy r (h_H005.2 r).2 hr
  have hdivs := fun r hr => And.intro (hfac r hr) (And.intro (hdx r hr) (hdy r hr))
  have hzero (c : ℂ) (n : ℕ) :
      (n : ℂ) • (c • (0 : V)) = n • mu p M (0 : MR p M) := by
    rw [smul_zero c, smul_zero (n : ℂ), (mu p M).map_zero, nsmul_zero]

  rcases h_T012 with ⟨rho, hdata⟩
  letI : Algebra (R p) K := rho.toAlgebra
  rcases hdata with ⟨phi, hphi0, hphi, b, hb, BR, hBR, B, hB, hAct⟩
  let T : Module.End (R p) (MR p M) →+* Module.End K (VK K M) :=
    (phi.symm.conjRingEquiv.toRingHom).comp
      (Module.End.baseChangeHom (R p) K (MR p M)).toRingHom
  have hT (f : Module.End (R p) (MR p M)) (z : VK K M) :
      phi (T f z) = f.baseChange K (phi z) := by
    change phi (phi.symm (f.baseChange K (phi z))) = _
    exact phi.apply_symm_apply _
  have hTx (r : ℕ) (hr : r ≤ lam.toNat) :
      T (rop p M (dp x r)) = kdp (kop K M x) r := by
    rw [← hdx r hr]
    change T (rop p M (dp x r)) = kop K M (dp x r)
    apply LinearMap.ext
    intro z
    apply phi.injective
    rw [hT, hphi _ (h_H005.2 r).1]
    rfl
  have hTy (r : ℕ) (hr : r ≤ lam.toNat) :
      T (rop p M (dp y r)) = kdp (kop K M y) r := by
    rw [← hdy r hr]
    change T (rop p M (dp y r)) = kop K M (dp y r)
    apply LinearMap.ext
    intro z
    apply phi.injective
    rw [hT, hphi _ (h_H005.2 r).2]
    rfl
  have hTmul (f g : Module.End (R p) (MR p M)) : T (f*g) = T f * T g :=
    map_mul T f g
  rcases h_T004.2.2.1 with ⟨BC, hBC⟩
  have hcompat := h_T006.1.2.2.2.2.1
  have hmuX (r : ℕ) (z : MR p M) :
      mu p M (rop p M (dp x r) z) = dp x r (mu p M z) := (hcompat r).1 z
  have hmuY (r : ℕ) (z : MR p M) :
      mu p M (rop p M (dp y r) z) = dp y r (mu p M z) := (hcompat r).2 z
  have hBR' (k : Fin (lam.toNat + 1)) : mu p M (BR k) = b • BC k := by
    rw [hBR, hBC]

  let D (i j : Fin (lam.toNat + 1)) : Module.End (R p) (MR p M) :=
    rop p M (dp x (lam.toNat - i.val)) * rop p M (dp y lam.toNat) *
      rop p M (dp x lam.toNat) * rop p M (dp y (lam.toNat - j.val))
  have hDR (i j k : Fin (lam.toNat + 1)) :
      D i j (BR k) = (Nat.choose lam.toNat j.val) •
        (if k = j then BR i else 0) := by
    let n := Nat.choose lam.toNat j.val
    let DC : Module.End ℂ V :=
      dp x (lam.toNat - i.val) * dp y lam.toNat *
        dp x lam.toNat * dp y (lam.toNat - j.val)
    have hn : (n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)))
    have hMC : unit BC i j = (n : ℂ)⁻¹ • DC :=
      (h_T006.2.2 BC hBC i j).1
    have hDC : DC = (n : ℂ) • unit BC i j := by
      rw [hMC, smul_smul, mul_inv_cancel₀ hn, one_smul]
    apply h_T006.1.2.1
    change mu p M (D i j (BR k)) = mu p M (n • (if k = j then BR i else 0))
    rw [map_nsmul (G := MR p M) (H := V) (mu p M) n (if k = j then BR i else 0)]
    have hleft : mu p M (D i j (BR k)) = DC (b • BC k) := by
      simp only [D, Module.End.mul_apply, hmuX, hmuY, hBR', DC]
    rw [hleft, hDC, LinearMap.smul_apply]
    have huc : unit BC i j (b • BC k) =
        b • (if k = j then BC i else 0) := by
      simp only [unit, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_smul,
        Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      by_cases hk : k = j
      · subst k; simp
      · simp [hk]
    rw [huc]
    by_cases hk : k = j
    · subst k
      rw [if_pos rfl, if_pos rfl, hBR']
      exact Nat.cast_smul_eq_nsmul ℂ n (b • BC i)
    · rw [if_neg hk, if_neg hk]
      exact hzero b n

  have hDK (i j : Fin (lam.toNat + 1)) :
      T (D i j) = (Nat.choose lam.toNat j.val : K) • unit B i j := by
    apply B.ext
    intro k
    apply phi.injective
    rw [hT, hB, LinearMap.baseChange_tmul, hDR, LinearMap.smul_apply]
    have huk : unit B i j (B k) = if k = j then B i else 0 := by
      simp only [unit, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      by_cases hk : k = j
      · subst k; simp
      · simp [hk]
    rw [huk]
    by_cases hk : k = j
    · subst k
      rw [if_pos rfl, if_pos rfl, phi.map_smul, hB,
        Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul]
    · rw [if_neg hk, if_neg hk, nsmul_zero, smul_zero,
        TensorProduct.tmul_zero, phi.map_zero]

  refine ⟨h_T004.1, hx, hy, hh, hbr1, hbr2, hbr3, B, hAct, hdivs, ?_⟩
  intro i j
  have hunit : IsUnit (Nat.choose lam.toNat j.val : K) := by
    simpa only [map_natCast] using (h_T006.2.1 j).map rho
  have hn : (Nat.choose lam.toNat j.val : K) ≠ 0 := hunit.ne_zero
  refine ⟨hn, ?_⟩
  have hd : T (D i j) =
      kdp (kop K M x) (lam.toNat - i.val) * kdp (kop K M y) lam.toNat *
        kdp (kop K M x) lam.toNat * kdp (kop K M y) (lam.toNat - j.val) := by
    dsimp only [D]
    rw [hTmul, hTmul, hTmul,
      hTx _ (Nat.sub_le _ _), hTy _ le_rfl, hTx _ le_rfl, hTy _ (Nat.sub_le _ _)]
  calc
    unit B i j =
        (Nat.choose lam.toNat j.val : K)⁻¹ •
          ((Nat.choose lam.toNat j.val : K) • unit B i j) :=
      (inv_smul_smul₀ hn _).symm
    _ = (Nat.choose lam.toNat j.val : K)⁻¹ • T (D i j) := by rw [hDK]
    _ = _ := by rw [hd]

theorem T014 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_T013 : ReducedOutput K lam M x y h) :
    Nontrivial (VK K M) ∧
  ∀ (B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M)),
    (∀ i j : Fin (lam.toNat + 1), (Nat.choose lam.toNat j.val : K) ≠ 0 ∧
      unit B i j = ((Nat.choose lam.toNat j.val : K)⁻¹) •
        (kdp (kop K M x) (lam.toNat - i.val) * kdp (kop K M y) lam.toNat *
         kdp (kop K M x) lam.toNat * kdp (kop K M y) (lam.toNat - j.val))) →
    ∀ W : Submodule K (VK K M), Inv W (kop K M x) → Inv W (kop K M y) →
      Inv W (kop K M h) → ∀ i j, Inv W (unit B i j) := by
  classical
  rcases h_T013 with ⟨hpos, hstableX, hstableY, hstableH, hbr, hbrX, hbrY, B₀, hactions, hfactorials, hunits₀⟩
  constructor
  · exact ⟨⟨B₀ ⟨0, Nat.zero_lt_succ _⟩, 0, B₀.ne_zero _⟩⟩
  · intro B hunits W hWX hWY hWH
    have hpow (f : Module.End K (VK K M)) (hf : Inv W f) :
        ∀ r : ℕ, Inv W (f ^ r) := by
      intro r
      induction r with
      | zero =>
          intro w hw
          simpa only [pow_zero, Module.End.one_apply] using hw
      | succ r ih =>
          intro w hw
          simpa only [pow_succ, Module.End.mul_apply] using ih (f w) (hf w hw)
    have hdiv (f : Module.End K (VK K M)) (hf : Inv W f) (r : ℕ) :
        Inv W (kdp f r) := by
      intro w hw
      change ((r.factorial : K)⁻¹) • (f ^ r) w ∈ W
      exact W.smul_mem _ (hpow f hf r w hw)
    have hmul (f g : Module.End K (VK K M))
        (hf : Inv W f) (hg : Inv W g) : Inv W (f * g) := by
      intro w hw
      exact hf (g w) (hg w hw)
    intro i j
    rw [(hunits i j).2]
    intro w hw
    change (Nat.choose lam.toNat j.val : K)⁻¹ •
      (kdp (kop K M x) (lam.toNat - i.val) * kdp (kop K M y) lam.toNat *
        kdp (kop K M x) lam.toNat * kdp (kop K M y) (lam.toNat - j.val)) w ∈ W
    apply W.smul_mem
    exact hmul _ _
      (hmul _ _
        (hmul _ _ (hdiv _ hWX _) (hdiv _ hWY _))
        (hdiv _ hWX _))
      (hdiv _ hWY _) w hw

theorem T015 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T013 : ReducedOutput K lam M x y h) :
    ∀ (B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M))
  (W : Submodule K (VK K M)), W ≠ ⊥ →
  ∃ w : VK K M, w ∈ W ∧ w ≠ 0 ∧ ∃ j : Fin (lam.toNat + 1), B.repr w j ≠ 0 := by
  intro B W hW
  classical
  obtain ⟨w, hwW, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨w, hwW, hw, ?_⟩
  by_contra hn
  apply hw
  apply B.repr.injective
  have hc : ∀ j, B.repr w j = 0 := by
    simpa only [not_exists, not_not] using hn
  simpa using (show B.repr w = 0 from Finsupp.ext hc)

theorem T016 (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
    ∃ bC : Module.Basis (Fin d) ℂ V, ∀ i, bC i = (bZ i : V)) ∧
  ∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r)) (h_T013 : ReducedOutput K lam M x y h) (h_T014 : Nontrivial (VK K M) ∧
  ∀ (B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M)),
    (∀ i j : Fin (lam.toNat + 1), (Nat.choose lam.toNat j.val : K) ≠ 0 ∧
      unit B i j = ((Nat.choose lam.toNat j.val : K)⁻¹) •
        (kdp (kop K M x) (lam.toNat - i.val) * kdp (kop K M y) lam.toNat *
         kdp (kop K M x) lam.toNat * kdp (kop K M y) (lam.toNat - j.val))) →
    ∀ W : Submodule K (VK K M), Inv W (kop K M x) → Inv W (kop K M y) →
      Inv W (kop K M h) → ∀ i j, Inv W (unit B i j)) (h_T015 : ∀ (B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M))
  (W : Submodule K (VK K M)), W ≠ ⊥ →
  ∃ w : VK K M, w ∈ W ∧ w ≠ 0 ∧ ∃ j : Fin (lam.toNat + 1), B.repr w j ≠ 0) :
    Target K M x y h := by
  classical
  rcases h_T013 with ⟨_, _, _, _, _, _, _, B, _, _, hmat⟩
  refine ⟨h_T014.1, ?_⟩
  intro W hx hy hh
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    have hinv : ∀ i j, Inv W (unit B i j) := h_T014.2 B hmat W hx hy hh
    rcases h_T015 B W hW with ⟨w, hw, _, j, hj⟩
    apply (Submodule.eq_top_iff_forall_basis_mem B).2
    intro i
    have hunit : unit B i j w = (B.repr w j) • B i := rfl
    have hmem : (B.repr w j) • B i ∈ W := by
      rw [← hunit]
      exact hinv i j w hw
    have hscaled := W.smul_mem (B.repr w j)⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using hscaled

set_option Elab.async false in
theorem P (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lam.toNat + 1 ∧ Nontrivial V ∧
  (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤) ∧
  (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lam : ℂ) • w)) (h_H003 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
    ∃ bC : Module.Basis (Fin d) ℂ V, ∀ i, bC i = (bZ i : V)) ∧
  ∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r)) :
    Target K M x y h := by
  have h_T001 : Strings lam x y h v := @T001 p K fieldK lam V addV moduleV x y h v M h_H003 h_H004
  have h_T002 : Coordinates lam y v := @T002 p K fieldK lam V addV moduleV x y h v M h_H001 h_H002 h_H004 h_T001
  have h_T003 : ∀ d : ℕ, lam < (d : ℤ) → (y ^ d) v = 0 := @T003 p K fieldK lam V addV moduleV x y h v M h_H001 h_T001 h_T002
  have h_T004 : ComplexOutput lam x y h v := @T004 p K fieldK lam V addV moduleV x y h v M h_H001 h_H004 h_T001 h_T002 h_T003
  have h_T005 : LocalBasics p lam M x y := @T005 p K fieldK lam V addV moduleV x y h v M h_H001 h_H005 h_T004
  have h_T006 : MatrixOutput p lam M x y v := @T006 p K fieldK lam V addV moduleV x y h v M h_H001 h_T004 h_T005
  have h_T007 : CommonOutput p lam M x y v := @T007 p K fieldK lam V addV moduleV x y h v M h_H001 h_T004 h_T006
  have h_T008 : FractionData p M y v := @T008 p K fieldK lam V addV moduleV x y h v M h_H001 h_T007
  have h_T009 : RationalLine p M y v := @T009 p K fieldK lam V addV moduleV x y h v M h_H001 h_T007 h_T008
  have h_T010 : PrincipalOutput p lam M y v := @T010 p K fieldK lam V addV moduleV x y h v M h_H001 h_T007 h_T009
  have h_T011 : ScalarExtensionData p K M := @T011 p K fieldK lam V addV moduleV x y h v M h_H001 h_H005 h_T006
  have h_T012 : ReducedBasisData p K lam M x y h v := @T012 p K fieldK lam V addV moduleV x y h v M h_H001 h_H003 h_H005 h_T004 h_T006 h_T010 h_T011
  have h_T013 : ReducedOutput K lam M x y h := @T013 p K fieldK lam V addV moduleV x y h v M h_H001 h_H003 h_H005 h_T004 h_T006 h_T010 h_T011 h_T012
  have h_T014 : Nontrivial (VK K M) ∧
  ∀ (B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M)),
    (∀ i j : Fin (lam.toNat + 1), (Nat.choose lam.toNat j.val : K) ≠ 0 ∧
      unit B i j = ((Nat.choose lam.toNat j.val : K)⁻¹) •
        (kdp (kop K M x) (lam.toNat - i.val) * kdp (kop K M y) lam.toNat *
         kdp (kop K M x) lam.toNat * kdp (kop K M y) (lam.toNat - j.val))) →
    ∀ W : Submodule K (VK K M), Inv W (kop K M x) → Inv W (kop K M y) →
      Inv W (kop K M h) → ∀ i j, Inv W (unit B i j) := @T014 p K fieldK lam V addV moduleV x y h v M h_H001 h_T013
  have h_T015 : ∀ (B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M))
  (W : Submodule K (VK K M)), W ≠ ⊥ →
  ∃ w : VK K M, w ∈ W ∧ w ≠ 0 ∧ ∃ j : Fin (lam.toNat + 1), B.repr w j ≠ 0 := @T015 p K fieldK lam V addV moduleV x y h v M h_T013
  have h_T016 : Target K M x y h := @T016 p K fieldK lam V addV moduleV x y h v M h_H001 h_H003 h_H005 h_T013 h_T014 h_T015
  exact h_T016

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H002 : FiniteDimensional ℂ V ∧ Module.finrank ℂ V = lam.toNat + 1 ∧ Nontrivial V ∧
  (∀ W : Submodule ℂ V, Inv W x → Inv W y → Inv W h → W = ⊥ ∨ W = ⊤) ∧
  (∃ w : V, w ≠ 0 ∧ x w = 0 ∧ h w = (lam : ℂ) • w)) (h_H003 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H004 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
    ∃ bC : Module.Basis (Fin d) ℂ V, ∀ i, bC i = (bZ i : V)) ∧
  ∀ r : ℕ, Stable M (dp x r) ∧ Stable M (dp y r)) : Target K M x y h := by
  exact @Translation.P.{_, _} p K fieldK lam V addV moduleV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005

#check @P
#print axioms P
end AuditBExport
