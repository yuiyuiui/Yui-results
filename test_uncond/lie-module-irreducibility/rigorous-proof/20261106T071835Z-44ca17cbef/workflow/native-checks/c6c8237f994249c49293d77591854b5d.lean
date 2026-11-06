import Mathlib

namespace YuiObjects

noncomputable def dividedPower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((Nat.factorial r : ℂ)⁻¹) • (a ^ r)

def stable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (a : Module.End F V) (W : Submodule F V) : Prop :=
  ∀ w ∈ W, a w ∈ W

def highestWeightData {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℕ) (h x y : Module.End ℂ V) (v : V) : Prop :=
  v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧
  h * x - x * h = (2 : ℂ) • x ∧
  h * y - y * h = (-2 : ℂ) • y ∧
  x * y - y * x = h ∧ Module.finrank ℂ V = lam + 1

def admissibleLattice {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℕ) (x y : Module.End ℂ V) (M : Submodule ℤ V) : Prop :=
  (∃ (b : Module.Basis (Fin (lam + 1)) ℤ M)
      (e : Module.Basis (Fin (lam + 1)) ℂ V), ∀ i, (b i : V) = e i) ∧
  (∀ (r : ℕ) (m : M), dividedPower x r (m : V) ∈ M) ∧
  (∀ (r : ℕ) (m : M), dividedPower y r (m : V) ∈ M)

def matrixUnits {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype I] [DecidableEq I] (f : I → I → Module.End F V) : Prop :=
  (∀ i j k l, f i j * f k l = if j = k then f i l else 0) ∧
  (∑ i, f i i) = 1

end YuiObjects

namespace YuiObjects
noncomputable def latticeEnd {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M : Submodule ℤ V) (f : Module.End ℂ V) : Module.End ℤ M :=
  @dite (Module.End ℤ M) (∀ z ∈ M, f z ∈ M)
    (Classical.propDecidable _) (fun hs => (f.restrictScalars ℤ).restrict hs) (fun _ => 0)
end YuiObjects

universe uK uV
namespace YuiObjects
abbrev ell (lam : ℤ) : ℕ := lam.toNat
abbrev Idx (lam : ℤ) := Fin (ell lam + 1)
noncomputable def ev {V : Type*} [AddCommGroup V] [Module ℂ V]
    (y : Module.End ℂ V) (v : V) (i : ℕ) : V := dividedPower y i v
def coeff (lam : ℤ) (j : Idx lam) : ℕ := Nat.choose (ell lam) j.val
def coeffProd (lam : ℤ) : ℕ := ∏ j : Idx lam, coeff lam j
def coeffOmit (lam : ℤ) (i : Idx lam) : ℕ :=
  ∏ j ∈ (Finset.univ.erase i), coeff lam j
noncomputable def projector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (x y : Module.End ℂ V) : Module.End ℂ V :=
  dividedPower y (ell lam) * dividedPower x (ell lam)
noncomputable def integralMatrix {V : Type*} [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (x y : Module.End ℂ V) (i j : Idx lam) : Module.End ℂ V :=
  dividedPower x (ell lam - i.val) * projector lam x y *
    dividedPower y (ell lam - j.val)
abbrev TensorLeft (K M : Type*) [Field K] [AddCommGroup M] := TensorProduct ℤ K M
abbrev TensorRight (K M : Type*) [Field K] [AddCommGroup M] := TensorProduct ℤ M K
noncomputable instance rightTensorModule (K M : Type*) [Field K] [AddCommGroup M] :
    Module K (TensorRight K M) :=
  (TensorProduct.comm ℤ M K).toAddEquiv.module K
noncomputable def tensorSwap (K M : Type*) [Field K] [AddCommGroup M] :
    TensorRight K M ≃ₗ[K] TensorLeft K M :=
  (TensorProduct.comm ℤ M K).toAddEquiv.linearEquiv K
noncomputable def hat {K M : Type*} [Field K] [AddCommGroup M]
    (f : Module.End ℤ M) : Module.End K (TensorLeft K M) := f.baseChange K
noncomputable def induced {K M : Type*} [Field K] [AddCommGroup M]
    (f : Module.End ℤ M) : Module.End K (TensorRight K M) :=
  (tensorSwap K M).symm.toLinearMap.comp ((hat (K := K) f).comp (tensorSwap K M).toLinearMap)
noncomputable def scaledMatrix {K V : Type*} [Field K] [AddCommGroup V] [Module ℂ V]
    (lam : ℤ) (x y : Module.End ℂ V) (M : Submodule ℤ V)
    (i j : Idx lam) : Module.End K (TensorLeft K M) :=
  ((coeff lam j : K)⁻¹) • hat (K := K) (latticeEnd M (integralMatrix lam x y i j))
end YuiObjects
open YuiObjects
namespace YuiPortTypes
abbrev T001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)
abbrev T002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))
abbrev T003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)
abbrev T004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a)
abbrev T005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  ∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤
abbrev T007 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))
abbrev T008 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)
abbrev T009 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))
abbrev T010 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0
abbrev T011 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) : Prop :=
  (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))
end YuiPortTypes

open Lean Elab Term
elab "yui_use_term% " text:str : term <= expectedType => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  let located := parsed.rewriteBottomUp fun node => node.setInfo text.raw.getHeadInfo
  Term.elabTerm located expectedType

open Lean Elab Command in
run_cmd do
  let specs : List (Name × List String × String) := [(`YuiPortTypes.T001, [], "T002 <- T001"), (`YuiPortTypes.T002, [], "T003, T004 <- T002"), (`YuiPortTypes.T003, [], "T004 <- T003"), (`YuiPortTypes.T004, [], "T006 <- T004"), (`YuiPortTypes.T005, [], "T006 <- T005"), (`YuiPortTypes.T007, [], "T008, T001 <- T007"), (`YuiPortTypes.T008, [], "T001 <- T008"), (`YuiPortTypes.T009, [], "T003 <- T009"), (`YuiPortTypes.T010, [], "T003 <- T010"), (`YuiPortTypes.T011, [], "T004 <- T011")]
  for (name, declared, label) in specs do
    let info ← getConstInfo name
    let publicLevels := (collectLevelParams {} info.type).params.toList
    let missing := info.levelParams.filter fun l => !publicLevels.contains l && !declared.contains l.toString
    unless missing.isEmpty do
      throwError "{label}: undeclared internal universes {missing}; name them in universe_params and supply input_instances"

namespace Translation
set_option autoImplicit false

def __signature_T007 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h), ((ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))))
private theorem __preflight_T007 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v)) := False.elim __yui_preflight
def __signature_T008 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h), ((∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)))
private theorem __preflight_T008 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (__yui_preflight : False) :
    (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) := False.elim __yui_preflight
def __signature_T001 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h), ((ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)))
private theorem __preflight_T001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T007 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v))) (h_T008 : (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val)) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0) := False.elim __yui_preflight
def __signature_T002 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M), ((∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))))
private theorem __preflight_T002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T001 : (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val)) := False.elim __yui_preflight
def __signature_T009 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M), ((ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))))
private theorem __preflight_T009 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) := False.elim __yui_preflight
def __signature_T010 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)), ((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0))
private theorem __preflight_T010 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (__yui_preflight : False) :
    (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0 := False.elim __yui_preflight
def __signature_T003 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M), ((ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)))
private theorem __preflight_T003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T009 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)))) (h_T010 : (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x) := False.elim __yui_preflight
def __signature_T011 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V), ((∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))))
private theorem __preflight_T011 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  (__yui_preflight : False) :
    (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u)) := False.elim __yui_preflight
def __signature_T004 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T003 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)) (h_T011 : (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M), (Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a)))
private theorem __preflight_T004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T002 : (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val))) (h_T003 : (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x)) (h_T011 : (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u))) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) := False.elim __yui_preflight
def __signature_T005 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V), (∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤))
private theorem __preflight_T005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  (__yui_preflight : False) :
    ∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤ := False.elim __yui_preflight
def __signature_T006 : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T004 : Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a)) (h_T005 : @YuiPortTypes.T005 p K instK lam V instV instCV x y h v M) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M), (Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤))
-- YUI-USE T006 <- T005 (h_T005, use 1)
noncomputable def __use_T006_h_T005_1 :=
  (fun (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T004 : Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a)) (h_T005 : @YuiPortTypes.T005 p K instK lam V instV instCV x y h v M) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) => (((h_T005 (yui_use_term% "K")) (yui_use_term% "TensorRight K M"))))
-- YUI-END-USE
private theorem __preflight_T006 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_T004 : Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a)) (h_T005 : @YuiPortTypes.T005 p K instK lam V instV instCV x y h v M) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤ := False.elim __yui_preflight
def __signature_P : Prop :=
  (∀ (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M), (Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤))
private theorem __connected_T007 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∀ r : ℕ, h ((y ^ r) v) = ((ell lam : ℂ) - 2 * (r : ℂ)) • ((y ^ r) v)) ∧
(∀ r : ℕ, x ((y ^ (r+1)) v) = (((r+1 : ℕ) : ℂ) * ((ell lam : ℂ) - (r : ℂ))) • ((y ^ r) v)) := by
  exact @__preflight_T007 p K instK lam V instV instCV x y h v M h_H003 h_H005 __yui_preflight

private theorem __connected_T008 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (__yui_preflight : False) :
    (∀ i : Idx lam, ev y v i.val ≠ 0 ∧ h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
Function.Injective (fun i : Idx lam => (ell lam : ℂ) - 2 * (i.val : ℂ)) ∧
LinearIndependent ℂ (fun i : Idx lam => ev y v i.val) ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) := by
  exact @__preflight_T008 p K instK lam V instV instCV x y h v M (@__connected_T007 p K instK lam V instV instCV x y h v M h_H003 h_H005 __yui_preflight) h_H004 h_H005 __yui_preflight

private theorem __connected_T001 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℂ V, ∀ i, b i = ev y v i.val) ∧
(∀ r : ℕ, ell lam < r → (y ^ r) v = 0) ∧
x (ev y v 0) = 0 ∧
(∀ i : Idx lam, 0 < i.val → x (ev y v i.val) = ((ell lam - i.val + 1 : ℕ) : ℂ) • ev y v (i.val - 1)) ∧
(∀ i : Idx lam, i.val < ell lam → y (ev y v i.val) = ((i.val + 1 : ℕ) : ℂ) • ev y v (i.val + 1)) ∧
y (ev y v (ell lam)) = 0 ∧
(∀ i : Idx lam, h (ev y v i.val) = ((ell lam : ℂ) - 2 * (i.val : ℂ)) • ev y v i.val) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower x r (ev y v i.val) =
  if r ≤ i.val then (Nat.choose (ell lam - i.val + r) r : ℂ) • ev y v (i.val - r) else 0) ∧
(∀ (r : ℕ) (i : Idx lam), dividedPower y r (ev y v i.val) =
  if i.val + r ≤ ell lam then (Nat.choose (i.val+r) r : ℂ) • ev y v (i.val+r) else 0) := by
  exact @__preflight_T001 p K instK lam V instV instCV x y h v M (@__connected_T007 p K instK lam V instV instCV x y h v M h_H003 h_H005 __yui_preflight) (@__connected_T008 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005 __yui_preflight) h_H003 h_H004 h_H005 __yui_preflight

private theorem __connected_T002 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    (∀ j : Idx lam, 0 < coeff lam j ∧ coeff lam j * j.val.factorial * (ell lam - j.val).factorial = (ell lam).factorial ∧ Nat.choose (ell lam) (ell lam - j.val) = coeff lam j) ∧
projector lam x y (ev y v (ell lam)) = ev y v (ell lam) ∧
(∀ k : ℕ, k < ell lam → projector lam x y (ev y v k) = 0) ∧
(∀ i j k : Idx lam, (integralMatrix lam x y) i j (ev y v k.val) = if k = j then (coeff lam j : ℂ) • ev y v i.val else 0) ∧
(∀ (i j : Idx lam) (m : M), (integralMatrix lam x y) i j (m : V) ∈ M ∧ ((fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j m : V) = (integralMatrix lam x y) i j (m : V)) ∧
(∀ i j k l : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j * (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) k l = if j = k then (coeff lam j : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i l else 0) ∧
(∑ i : Idx lam, (coeffOmit lam i : ℤ) • (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i i) = (coeffProd lam : ℤ) • (1 : Module.End ℤ M) ∧
(∀ i : Idx lam, coeffProd lam = coeff lam i * coeffOmit lam i) ∧
(∀ r : ℕ, (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower x r)) r = (latticeEnd M x) ^ r ∧ (r.factorial : ℤ) • (fun r : ℕ => latticeEnd M (dividedPower y r)) r = (latticeEnd M y) ^ r) ∧
(∀ (r : ℕ) (m : M), ((fun r : ℕ => latticeEnd M (dividedPower x r)) r m : V) = dividedPower x r (m : V) ∧ ((fun r : ℕ => latticeEnd M (dividedPower y r)) r m : V) = dividedPower y r (m : V)) ∧
(∀ m : M, x (m : V) ∈ M ∧ y (m : V) ∈ M ∧ h (m : V) ∈ M ∧
 ((latticeEnd M x) m : V) = x (m : V) ∧ ((latticeEnd M y) m : V) = y (m : V) ∧ ((latticeEnd M h) m : V) = h (m : V)) ∧
(latticeEnd M h) = (latticeEnd M x) * (latticeEnd M y) - (latticeEnd M y) * (latticeEnd M x) ∧
(∀ i j : Idx lam, (fun i j : Idx lam => latticeEnd M (integralMatrix lam x y i j)) i j = (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam-i.val) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower x r)) (ell lam) * (fun r : ℕ => latticeEnd M (dividedPower y r)) (ell lam-j.val)) := by
  exact @__preflight_T002 p K instK lam V instV instCV x y h v M (@__connected_T001 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005 __yui_preflight) h_H005 h_H006 __yui_preflight

private theorem __connected_T009 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
(∃ b : Module.Basis (Idx lam) ℤ M, ∃ beta : Module.Basis (Idx lam) K (TensorLeft K M),
 ∀ i, beta i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) := by
  exact @__preflight_T009 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H006 __yui_preflight

private theorem __connected_T010 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (__yui_preflight : False) :
    (∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0 := by
  exact @__preflight_T010 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 __yui_preflight

private theorem __connected_T003 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    (ell lam : ℤ) = lam ∧ ell lam < p ∧ 0 < ell lam + 1 ∧
Nontrivial (TensorLeft K M) ∧ FiniteDimensional K (TensorLeft K M) ∧
Module.finrank K (TensorLeft K M) = ell lam + 1 ∧
((∀ r : ℕ, r ≤ ell lam → (r.factorial : K) ≠ 0) ∧
(∀ j : Idx lam, (coeff lam j : K) ≠ 0) ∧ (coeffProd lam : K) ≠ 0) ∧
matrixUnits (scaledMatrix (K := K) lam x y M) ∧
((∀ (f g : Module.End ℤ M), hat (K := K) (f+g) = hat f + hat g ∧ hat (K := K) (f*g) = hat f * hat g) ∧
(∀ (z : ℤ) (f : Module.End ℤ M), hat (K := K) (z • f) = (z : K) • hat f) ∧
hat (K := K) (1 : Module.End ℤ M) = 1 ∧
(∀ (q : ℕ) (fs : Fin q → Module.End ℤ M), hat (K := K) (∑ i, fs i) = ∑ i, hat (K := K) (fs i)) ∧
(∀ (f : Module.End ℤ M) (r : ℕ), hat (K := K) (f ^ r) = (hat (K := K) f) ^ r) ∧
(∀ (f : Module.End ℤ M) (a : K) (m : M), hat (K := K) f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m))) ∧
(∀ r : ℕ, r ≤ ell lam →
 hat (K := K) (latticeEnd M (dividedPower x r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M x)) ^ r ∧
 hat (K := K) (latticeEnd M (dividedPower y r)) = (r.factorial : K)⁻¹ • (hat (K := K) (latticeEnd M y)) ^ r) ∧
hat (K := K) (latticeEnd M h) = hat (K := K) (latticeEnd M x) * hat (K := K) (latticeEnd M y) - hat (K := K) (latticeEnd M y) * hat (K := K) (latticeEnd M x) := by
  exact @__preflight_T003 p K instK lam V instV instCV x y h v M (@__connected_T002 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005 h_H006 __yui_preflight) (@__connected_T009 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H006 __yui_preflight) (@__connected_T010 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 __yui_preflight) h_H001 h_H002 h_H003 h_H004 h_H006 __yui_preflight

private theorem __connected_T011 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  (__yui_preflight : False) :
    (∀ (m : M) (a : K), tensorSwap K M (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ a m) ∧
(∀ (a b : K) (m : M), a • TensorProduct.tmul ℤ m b = TensorProduct.tmul ℤ m (a*b)) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K), induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) ∧
(∀ (f : Module.End ℤ M) (u : TensorRight K M), tensorSwap K M (induced (K := K) f u) = hat (K := K) f (tensorSwap K M u)) := by
  exact @__preflight_T011 p K instK lam V instV instCV x y h v M __yui_preflight

private theorem __connected_T004 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    Nontrivial (TensorRight K M) ∧ FiniteDimensional K (TensorRight K M) ∧
Module.finrank K (TensorRight K M) = ell lam + 1 ∧ 0 < ell lam + 1 ∧
(∃ G : Idx lam → Idx lam → Module.End K (TensorRight K M),
 matrixUnits G ∧
 ∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 ∀ i j, stable (G i j) W) ∧
induced (K := K) (latticeEnd M h) =
 induced (K := K) (latticeEnd M x) * induced (K := K) (latticeEnd M y) -
 induced (K := K) (latticeEnd M y) * induced (K := K) (latticeEnd M x) ∧
(∀ (f : Module.End ℤ M) (m : M) (a : K),
 induced (K := K) f (TensorProduct.tmul ℤ m a) = TensorProduct.tmul ℤ (f m) a) := by
  exact @__preflight_T004 p K instK lam V instV instCV x y h v M (@__connected_T002 p K instK lam V instV instCV x y h v M h_H003 h_H004 h_H005 h_H006 __yui_preflight) (@__connected_T003 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 __yui_preflight) (@__connected_T011 p K instK lam V instV instCV x y h v M __yui_preflight) h_H005 h_H006 __yui_preflight

private theorem __connected_T005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  (__yui_preflight : False) :
    ∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤ := by
  exact @__preflight_T005 p K instK lam V instV instCV x y h v M __yui_preflight

private theorem __connected_T006 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) :
    Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤ := by
  exact @__preflight_T006 p K instK lam V instV instCV x y h v M (@__connected_T004 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 __yui_preflight) (@__connected_T005 p K instK lam V instV instCV x y h v M __yui_preflight) h_H003 h_H005 h_H006 __yui_preflight

private theorem __preflight_P (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V) (h_H001 : Nat.Prime p) (h_H002 : CharP K p) (h_H003 : 0 ≤ lam ∧ lam < (p : ℤ)) (h_H004 : FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℤ) = lam + 1 ∧ (∀ W : Submodule ℂ V, stable x W → stable y W → stable h W → W = ⊥ ∨ W = ⊤)) (h_H005 : v ≠ 0 ∧ x v = 0 ∧ h v = (lam : ℂ) • v ∧ h * x - x * h = (2 : ℂ) • x ∧ h * y - y * h = (-2 : ℂ) • y ∧ x * y - y * x = h) (h_H006 : admissibleLattice (ell lam) x y M) (__yui_preflight : False) : Nontrivial (TensorRight K M) ∧
∀ W : Submodule K (TensorRight K M),
 stable (induced (K := K) (latticeEnd M x)) W →
 stable (induced (K := K) (latticeEnd M y)) W →
 stable (induced (K := K) (latticeEnd M h)) W → W = ⊥ ∨ W = ⊤ := by
  exact @__connected_T006 p K instK lam V instV instCV x y h v M h_H001 h_H002 h_H003 h_H004 h_H005 h_H006 __yui_preflight

end Translation
