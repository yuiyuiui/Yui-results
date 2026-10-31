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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (p : ℕ) (K : Type uK) [fieldK : Field K] (lam : ℤ) (V : Type uV) [addV : AddCommGroup V] [moduleV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : p.Prime ∧ CharP K p ∧ 0 ≤ lam ∧ lam < (p : ℤ)) (h_H003 : h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H005 : (∃ d : ℕ, ∃ bZ : Module.Basis (Fin d) ℤ M,
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
  ∃ w : VK K M, w ∈ W ∧ w ≠ 0 ∧ ∃ j : Fin (lam.toNat + 1), B.repr w j ≠ 0) : yui_aux_type% "∀ (B : Module.Basis (Fin (lam.toNat + 1)) K (VK K M)) (i j : Fin (lam.toNat + 1)) (w : VK K M), unit B i j w = (B.repr w j) • B i" := by
  intro B i j w
  rfl
#check @checked
#print axioms checked
end YuiAuxiliary
