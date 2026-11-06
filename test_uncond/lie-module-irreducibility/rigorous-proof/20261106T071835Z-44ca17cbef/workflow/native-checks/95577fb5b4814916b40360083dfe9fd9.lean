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

namespace Translation
set_option autoImplicit false

theorem T005 (p : ℕ) (K : Type uK) [instK : Field K] (lam : ℤ) (V : Type uV) [instV : AddCommGroup V] [instCV : Module ℂ V] (x : Module.End ℂ V) (y : Module.End ℂ V) (h : Module.End ℂ V) (v : V) (M : Submodule ℤ V)  :
    ∀ (F : Type uK) (U0 : Type (max uK uV)) [Field F] [AddCommGroup U0] [Module F U0]
(n0 : ℕ) [FiniteDimensional F U0] (G : Fin n0 → Fin n0 → Module.End F U0),
0 < n0 → Module.finrank F U0 = n0 → matrixUnits G →
∀ W : Submodule F U0, (∀ i j, stable (G i j) W) → W = ⊥ ∨ W = ⊤ := by
  classical
  intro F U0 _ _ _ n0 _ G hn hdim hG W hW
  rcases hG with ⟨hmul, hsum⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hsumw : ∑ j, G j j w = w := by
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using congrArg (fun f : Module.End F U0 => f w) hsum
  have hex : ∃ j, G j j w ≠ 0 := by
    by_contra he
    have hz : ∀ j, G j j w = 0 := by simpa using he
    have : w = 0 := by simpa [hz] using hsumw.symm
    exact hw0 this
  obtain ⟨j, hj⟩ := hex
  let u : U0 := G j j w
  have huW : u ∈ W := hW j j w hwW
  have hu0 : u ≠ 0 := hj
  have hju : G j j u = u := by
    change (G j j * G j j) w = G j j w
    rw [hmul j j j j, if_pos rfl]
  let z : Fin n0 → U0 := fun i => G i j u
  have hzW : ∀ i, z i ∈ W := fun i => hW i j u huW
  have hact : ∀ k i, G j k (z i) = if k = i then u else 0 := by
    intro k i
    change (G j k * G i j) u = _
    rw [hmul j k i j]
    by_cases hki : k = i
    · simp [hki, hju]
    · simp [hki]
  have hli : LinearIndependent F z := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc k
    have hk := congrArg (fun a : U0 => G j k a) hc
    have hck : c k • u = 0 := by
      simpa [map_sum, hact] using hk
    exact (smul_eq_zero.mp hck).resolve_right hu0
  have hspan : Submodule.span F (Set.range z) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simpa using hdim.symm)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro a ⟨i, rfl⟩
  exact hzW i

#check @T005
#print axioms T005

end Translation
