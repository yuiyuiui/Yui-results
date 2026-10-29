import Mathlib

noncomputable section
namespace LR

def localRing (p : ℕ) : Subring ℚ := Subring.closure {q | ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ) / d}
abbrev R (p : ℕ) := ↥(localRing p)
noncomputable instance rRat (p : ℕ) : Algebra (R p) ℚ := (localRing p).subtype.toAlgebra
noncomputable instance rComplex (p : ℕ) : Algebra (R p) ℂ := ((algebraMap ℚ ℂ).comp (localRing p).subtype).toAlgebra
variable {V : Type} [AddCommGroup V] [Module ℂ V]
noncomputable instance rModule (p : ℕ) : Module (R p) V := Module.compHom V (algebraMap (R p) ℂ)
noncomputable instance rTower (p : ℕ) : IsScalarTower (R p) ℂ V := IsScalarTower.of_compHom (R p) ℂ V

def vec (y : Module.End ℂ V) (v : V) (i : ℕ) : V := ((i.factorial : ℂ)⁻¹) • (y ^ i) v
def divided (x : Module.End ℂ V) (r : ℕ) : Module.End ℂ V := ((r.factorial : ℂ)⁻¹) • x ^ r
def MR (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) V := Submodule.span (R p) (M : Set V)
def embed (p : ℕ) (M : Submodule ℤ V) (m : M) : MR p M := ⟨m, Submodule.subset_span m.property⟩
def J (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (i : ℕ) : Submodule (R p) ℂ := (MR p M).comap ((LinearMap.toSpanSingleton ℂ V (vec y v i)).restrictScalars (R p))
def unit {F W : Type} [Field F] [AddCommGroup W] [Module F W] (l : ℕ) (b : Module.Basis (Fin (l+1)) F W) (i j : Fin (l+1)) : Module.End F W := (b.coord j).smulRight (b i)
abbrev VK (K : Type) [Field K] (M : Submodule ℤ V) := TensorProduct ℤ K M
structure Lift (M : Submodule ℤ V) (f : Module.End ℂ V) where
  map : Module.End ℤ M
  agrees : ∀ m : M, (map m : V) = f m
structure Actions (M : Submodule ℤ V) (x y h : Module.End ℂ V) where
  lx : Lift M x
  ly : Lift M y
  lh : Lift M h
  dX : ∀ r : ℕ, Lift M (divided x r)
  dY : ∀ r : ℕ, Lift M (divided y r)
def induced (K : Type) [Field K] (M : Submodule ℤ V) (f : Module.End ℤ M) : Module.End K (VK K M) := f.baseChange K
def inv {F W : Type} [Field F] [AddCommGroup W] [Module F W] (W' : Submodule F W) (f : Module.End F W) : Prop := ∀ w ∈ W', f w ∈ W'
def pMR (p : ℕ) (M : Submodule ℤ V) : Submodule (R p) (MR p M) := LinearMap.range ((p : R p) • (LinearMap.id : Module.End (R p) (MR p M)))
abbrev QMR (p : ℕ) (M : Submodule ℤ V) := (MR p M) ⧸ pMR p M

def Strings (l : ℕ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  (∀ t : ℕ, h ((y^t) v) = ((l : ℂ)-2*(t : ℂ)) • (y^t) v) ∧
  (∀ t : ℕ, 1 ≤ t → x ((y^t) v) = ((t : ℂ)*((l : ℂ)-(t : ℂ)+1)) • (y^(t-1)) v) ∧
  (∀ i : ℕ, i ≤ l → vec y v i ≠ 0)
def CBasis (l : ℕ) (y : Module.End ℂ V) (v : V) : Prop :=
  (∃ b : Module.Basis (Fin (l+1)) ℂ V, ∀ i, b i = vec y v i.val) ∧ (∀ t : ℕ, l < t → (y^t) v = 0)
def BasicMatrices (l : ℕ) (x y h : Module.End ℂ V) (v : V) : Prop :=
  x (vec y v 0) = 0 ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ l → x (vec y v i) = ((l-i+1 : ℕ) : ℂ) • vec y v (i-1)) ∧
  (∀ i : ℕ, i < l → y (vec y v i) = ((i+1 : ℕ) : ℂ) • vec y v (i+1)) ∧
  y (vec y v l) = 0 ∧
  (∀ i : ℕ, i ≤ l → h (vec y v i) = ((l : ℂ)-2*(i : ℂ)) • vec y v i)
def DivMatrices (l : ℕ) (x y : Module.End ℂ V) (v : V) : Prop :=
  (∀ r i : ℕ, i ≤ l → divided x r (vec y v i) = if r ≤ i then ((Nat.choose (l-i+r) r : ℕ) : ℂ) • vec y v (i-r) else 0) ∧
  (∀ r i : ℕ, i ≤ l → divided y r (vec y v i) = if i+r ≤ l then ((Nat.choose (i+r) r : ℕ) : ℂ) • vec y v (i+r) else 0)
def N1 (l : ℕ) (x y h : Module.End ℂ V) (v : V) : Prop := Strings l x y h v ∧ CBasis l y v ∧ BasicMatrices l x y h v ∧ DivMatrices l x y v

def LocalBasis (p l : ℕ) (M : Submodule ℤ V) : Prop :=
  (∃ f : TensorProduct ℤ (R p) M ≃ₗ[R p] MR p M, ∀ r m, (f (TensorProduct.tmul ℤ r m) : V) = r • (m : V)) ∧
  Nonempty (Module.Basis (Fin (l+1)) (R p) (MR p M)) ∧ Submodule.span ℂ (MR p M : Set V) = ⊤
def LocalStable (p : ℕ) (M : Submodule ℤ V) (x y : Module.End ℂ V) : Prop :=
  ∀ r : ℕ, (∀ w ∈ MR p M, divided x r w ∈ MR p M) ∧ (∀ w ∈ MR p M, divided y r w ∈ MR p M)
def PartialUnits (l : ℕ) (x y : Module.End ℂ V) (b : Module.Basis (Fin (l+1)) ℂ V) : Prop :=
  divided y l * divided x l = unit l b ⟨l, Nat.lt_succ_self l⟩ ⟨l, Nat.lt_succ_self l⟩ ∧
  (∀ i, divided x (l-i.val) * unit l b ⟨l, Nat.lt_succ_self l⟩ ⟨l, Nat.lt_succ_self l⟩ = unit l b i ⟨l, Nat.lt_succ_self l⟩) ∧
  (∀ j, unit l b ⟨l, Nat.lt_succ_self l⟩ ⟨l, Nat.lt_succ_self l⟩ * divided y (l-j.val) = ((Nat.choose l j.val : ℕ) : ℂ) • unit l b ⟨l, Nat.lt_succ_self l⟩ j)
def AllUnits (p l : ℕ) (M : Submodule ℤ V) (x y : Module.End ℂ V) (b : Module.Basis (Fin (l+1)) ℂ V) : Prop :=
  (∀ j : Fin (l+1), IsUnit ((Nat.choose l j.val : ℕ) : R p)) ∧
  (∀ i j, unit l b i j = (((Nat.choose l j.val : ℕ) : ℂ)⁻¹) • (divided x (l-i.val) * (divided y l * divided x l) * divided y (l-j.val))) ∧
  (∀ i j w, w ∈ MR p M → unit l b i j w ∈ MR p M)
def N2 (p l : ℕ) (M : Submodule ℤ V) (x y : Module.End ℂ V) (v : V) : Prop :=
  LocalBasis p l M ∧ LocalStable p M x y ∧ ∀ b : Module.Basis (Fin (l+1)) ℂ V, (∀ i, b i = vec y v i.val) → PartialUnits l x y b ∧ AllUnits p l M x y b

def Decomposition (p l : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  (∀ i : Fin (l+1), J p M y v i.val = J p M y v 0) ∧
  J p M y v 0 ≠ ⊥ ∧ Module.Finite (R p) (J p M y v 0) ∧
  (∀ w : V, w ∈ MR p M ↔ ∃ c : Fin (l+1) → ℂ, (∀ i, c i ∈ J p M y v 0) ∧ w = ∑ i, c i • vec y v i.val) ∧
  (∀ c : Fin (l+1) → ℂ, (∑ i, c i • vec y v i.val) = 0 → ∀ i, c i = 0)
def TensorLine (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ mu : TensorProduct (R p) ℚ (J p M y v 0) →ₗ[ℚ] ℂ,
    (∀ q c, mu (TensorProduct.tmul (R p) q c) = q • (c : ℂ)) ∧ Function.Injective mu ∧
    LinearMap.range mu = Submodule.span ℚ (J p M y v 0 : Set ℂ) ∧ Module.Finite ℚ (TensorProduct (R p) ℚ (J p M y v 0))
def RankOne (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop := Module.finrank ℚ (TensorProduct (R p) ℚ (J p M y v 0)) = 1
def Generators (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ a : ℂ, a ∈ J p M y v 0 ∧ a ≠ 0 ∧ ∃ k : ℕ, 0 < k ∧ ∃ q : Fin k → ℚ,
    (∀ j, q j ≠ 0) ∧ J p M y v 0 = Submodule.span (R p) (Set.range (fun j => (q j : ℂ) * a))
def Valuations (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  ∃ a : ℂ, a ∈ J p M y v 0 ∧ a ≠ 0 ∧ ∃ k : ℕ, 0 < k ∧ ∃ (nu : Fin k → ℤ) (u : Fin k → (R p)ˣ),
    J p M y v 0 = Submodule.span (R p) (Set.range (fun j => (((p : ℚ) ^ nu j * ((u j : R p) : ℚ) : ℚ) : ℂ) * a))
def Generates (p : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop := b ∈ J p M y v 0 ∧ b ≠ 0 ∧ J p M y v 0 = Submodule.span (R p) {b}
def ScaledBasis (p l : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) (b : ℂ) : Prop :=
  ∃ d : Module.Basis (Fin (l+1)) (R p) (MR p M), ∀ i, (d i : V) = b • vec y v i.val
def N3 (p l : ℕ) (M : Submodule ℤ V) (y : Module.End ℂ V) (v : V) : Prop :=
  Decomposition p l M y v ∧ TensorLine p M y v ∧ RankOne p M y v ∧ (∃ b, Generates p M y v b) ∧
  (∀ b, Generates p M y v b → ScaledBasis p l M y v b)

variable (K : Type) [Field K]
def ResidueMaps (p : ℕ) (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) : Prop :=
  letI : CharP K p := c
  (∀ (q : R p) (a d : ℤ), ¬ (p : ℤ) ∣ d → (q : ℚ) = (a : ℚ)/d → rho q = (a : K)/(d : K)) ∧
  RingHom.ker rho = Ideal.span {(p : R p)} ∧
  Function.Surjective sigma ∧ RingHom.ker sigma = Ideal.span {(p : R p)} ∧
  (∃ eta : (R p ⧸ Ideal.span {(p : R p)}) ≃+* ZMod p, ∀ r, eta (Ideal.Quotient.mk _ r) = sigma r) ∧
  rho = (ZMod.castHom (dvd_refl p) K).comp sigma
structure TransportData (p : ℕ) (M : Submodule ℤ V) [Algebra (R p) K] [Algebra (ZMod p) K] [Module (ZMod p) (QMR p M)] where
  first : VK K M ≃ₗ[K] TensorProduct (R p) K (MR p M)
  first_pure : ∀ k m, first (TensorProduct.tmul ℤ k m) = TensorProduct.tmul (R p) k (embed p M m)
  second : TensorProduct (R p) K (MR p M) ≃ₗ[K] TensorProduct (ZMod p) K (QMR p M)
  second_pure : ∀ k m, second (TensorProduct.tmul (R p) k m) = TensorProduct.tmul (ZMod p) k ((pMR p M).mkQ m)
  first_intertwines : ∀ (a : Module.End ℤ M) (aR : Module.End (R p) (MR p M)), (∀ m, aR (embed p M m) = embed p M (a m)) → ∀ z, first (induced K M a z) = aR.baseChange K (first z)
  second_intertwines : ∀ (aR : Module.End (R p) (MR p M)) (aQ : Module.End (ZMod p) (QMR p M)), (∀ m, (pMR p M).mkQ (aR m) = aQ ((pMR p M).mkQ m)) → ∀ z, second (aR.baseChange K z) = aQ.baseChange K (second z)
def Transport (p : ℕ) (M : Submodule ℤ V) (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) : Prop :=
  letI : CharP K p := c
  letI : Algebra (R p) K := rho.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  ∃ s : Module (ZMod p) (QMR p M),
    letI : Module (ZMod p) (QMR p M) := s
    (∀ (r : R p) (z : QMR p M), r • z = sigma r • z) ∧ Nonempty (TransportData K p M)
def ReducedMatrices (l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (A : Actions M x y h) (beta : Module.Basis (Fin (l+1)) K (VK K M)) : Prop :=
  induced K M A.lx.map (beta 0) = 0 ∧
  (∀ i j : Fin (l+1), j.val+1 = i.val → induced K M A.lx.map (beta i) = ((l-i.val+1 : ℕ) : K) • beta j) ∧
  (∀ i j : Fin (l+1), j.val = i.val+1 → induced K M A.ly.map (beta i) = ((i.val+1 : ℕ) : K) • beta j) ∧
  induced K M A.ly.map (beta ⟨l, Nat.lt_succ_self l⟩) = 0 ∧
  (∀ i, induced K M A.lh.map (beta i) = ((l : K)-2*(i.val : K)) • beta i)
def Reduction (p l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (v : V) (A : Actions M x y h) (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) : Prop :=
  letI : CharP K p := c
  letI : Algebra (R p) K := rho.toAlgebra
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  ∃ s : Module (ZMod p) (QMR p M),
    letI : Module (ZMod p) (QMR p M) := s
    (∀ (r : R p) (z : QMR p M), r • z = sigma r • z) ∧
    ∃ t : TransportData K p M, ∀ b : ℂ, Generates p M y v b →
      ∀ d : Module.Basis (Fin (l+1)) (R p) (MR p M), (∀ i, (d i : V) = b • vec y v i.val) →
      ∃ (beta : Module.Basis (Fin (l+1)) K (VK K M)) (gamma : Module.Basis (Fin (l+1)) (ZMod p) (QMR p M)),
        (∀ i, t.first (beta i) = TensorProduct.tmul (R p) 1 (d i)) ∧
        (∀ i, gamma i = (pMR p M).mkQ (d i)) ∧
        (∀ i, t.second (t.first (beta i)) = TensorProduct.tmul (ZMod p) 1 (gamma i)) ∧
        ReducedMatrices K l M x y h A beta ∧
        (∀ (ec : Module.Basis (Fin (l+1)) ℂ V), (∀ i, ec i = vec y v i.val) →
          ∀ i j (aR : Module.End (R p) (MR p M)), (∀ m, (aR m : V) = unit l ec i j m) →
          ∀ z, t.first (unit l beta i j z) = aR.baseChange K (t.first z))
def ModularUnits (l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (A : Actions M x y h) : Prop :=
  (∀ r : ℕ, r ≤ l → (r.factorial : K) ≠ 0 ∧ induced K M (A.dX r).map = (r.factorial : K)⁻¹ • (induced K M A.lx.map)^r ∧ induced K M (A.dY r).map = (r.factorial : K)⁻¹ • (induced K M A.ly.map)^r) ∧
  (∀ j : Fin (l+1), ((Nat.choose l j.val : ℕ) : K) ≠ 0) ∧
  ∀ beta : Module.Basis (Fin (l+1)) K (VK K M), ReducedMatrices K l M x y h A beta →
    (∀ i j, unit l beta i j = (((Nat.choose l j.val : ℕ) : K)⁻¹) • (induced K M (A.dX (l-i.val)).map * (induced K M (A.dY l).map * induced K M (A.dX l).map) * induced K M (A.dY (l-j.val)).map)) ∧
    (∀ W : Submodule K (VK K M), inv W (induced K M A.lx.map) → inv W (induced K M A.ly.map) → ∀ i j, inv W (unit l beta i j))
def N4 (p l : ℕ) (M : Submodule ℤ V) (x y h : Module.End ℂ V) (v : V) : Prop :=
  ∃ (c : CharP K p) (rho : R p →+* K) (sigma : R p →+* ZMod p) (A : Actions M x y h),
    ResidueMaps K p c rho sigma ∧ Reduction K p l M x y h v A c rho sigma ∧ ModularUnits K l M x y h A
end LR

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (p : ℕ) (K : Type) [fieldK : Field K] (l : ℕ) (V : Type) [addV : AddCommGroup V] [modV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : LR.N2 p l M x y v ∧ (∀ q : ℚ, q ∈ LR.localRing p ↔ ∃ a d : ℤ, ¬ (p : ℤ) ∣ d ∧ q = (a : ℚ)/d)) : yui_aux_type% "∀ (c : CharP K p) (rho : LR.R p →+* K), letI := c; letI := rho.toAlgebra; ∃ f : LR.VK K M ≃ₗ[K] TensorProduct (LR.R p) K (LR.MR p M), ∀ k m, f (TensorProduct.tmul ℤ k m) = TensorProduct.tmul (LR.R p) k (LR.embed p M m)" := by
  intro c rho
  letI := c
  letI := rho.toAlgebra
  obtain ⟨e, he⟩ := h_T007.1.1.1
  let f := (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (LR.R p) K K M).symm.trans (e.baseChange (LR.R p) K _ _)
  refine ⟨f, ?_⟩
  intro k m
  have hem : e (TensorProduct.tmul ℤ (1 : LR.R p) m) = LR.embed p M m := by
    exact Subtype.ext (by simpa using he 1 m)
  simpa [f, hem]
#check @checked
#print axioms checked
end YuiAuxiliary
