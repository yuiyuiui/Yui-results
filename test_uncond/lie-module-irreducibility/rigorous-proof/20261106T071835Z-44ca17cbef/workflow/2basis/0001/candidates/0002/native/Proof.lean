import Mathlib

namespace YuiObjects

noncomputable def dividedPower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((Nat.factorial r : ℂ)⁻¹) • (a ^ r)

def stable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (a : Module.End F V) (W : Submodule F V) : Prop :=
  ∀ w ∈ W, a w ∈ W

def highestWeightData {V : Type*} [AddCommGroup V] [Module ℂ V]
    (λ : ℕ) (h x y : Module.End ℂ V) (v : V) : Prop :=
  v ≠ 0 ∧ x v = 0 ∧ h v = (λ : ℂ) • v ∧
  h * x - x * h = (2 : ℂ) • x ∧
  h * y - y * h = (-2 : ℂ) • y ∧
  x * y - y * x = h ∧ Module.finrank ℂ V = λ + 1

def admissibleLattice {V : Type*} [AddCommGroup V] [Module ℂ V]
    (λ : ℕ) (x y : Module.End ℂ V) (M : Submodule ℤ V) : Prop :=
  (∃ (b : Module.Basis (Fin (λ + 1)) ℤ M)
      (e : Module.Basis (Fin (λ + 1)) ℂ V), ∀ i, (b i : V) = e i) ∧
  (∀ (r : ℕ) (m : M), dividedPower x r (m : V) ∈ M) ∧
  (∀ (r : ℕ) (m : M), dividedPower y r (m : V) ∈ M)

def matrixUnits {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype I] [DecidableEq I] (f : I → I → Module.End F V) : Prop :=
  (∀ i j k l, f i j * f k l = if j = k then f i l else 0) ∧
  (∑ i, f i i) = 1

end YuiObjects

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (F V I : Type*) [Field F] [AddCommGroup V] [Module F V] (f : Module.End F V) (μ : I → F) (z : I → V), Function.Injective μ → (∀ i, f.HasEigenvector (μ i) (z i)) → LinearIndependent F z := by
  intro F V I _ _ _ f μ z hμ hz
  exact f.eigenvectors_linearIndependent' μ hμ z hz
set_option Elab.async false in
theorem B002 : ∀ (F V I : Type*) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype I] (z : I → V), LinearIndependent F z → Fintype.card I = Module.finrank F V → Submodule.span F (Set.range z) = ⊤ := by
  intro F V I _ _ _ _ _ z hz hc
  exact hz.span_eq_top_of_card_eq_finrank' hc
set_option Elab.async false in
theorem B003 : ∀ (K M I : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (b : Module.Basis I ℤ M), ∃ β : Module.Basis I K (TensorProduct ℤ K M), ∀ i, β i = TensorProduct.tmul ℤ (1 : K) (b i) := by
  intro K M I _ _ _ b
  exact ⟨b.baseChange K, fun i => b.baseChange_apply K i⟩
set_option Elab.async false in
theorem B004 : ∀ (K : Type*) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → IsUnit (Nat.factorial r : K) := by
  intro K _ p _ _ r hr
  exact (IsUnit.natCast_factorial_iff_of_charP (A := K) p).2 hr
set_option Elab.async false in
theorem B005 : ∀ (n k : ℕ), k ≤ n → Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n := by
  intro n k hk
  exact Nat.choose_mul_factorial_mul_factorial hk
set_option Elab.async false in
theorem B006 : ∀ (F V I : Type*) [Field F] [AddCommGroup V] [Module F V] [Fintype I] (b : Module.Basis I F V), Module.finrank F V = Fintype.card I := by
  intro F V I _ _ _ _ b
  exact Module.finrank_eq_card_basis b
set_option Elab.async false in
theorem B007 : ∀ (K M N : Type*) [Field K] [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] (f : M →ₗ[ℤ] N), ∃ g : TensorProduct ℤ K M →ₗ[K] TensorProduct ℤ K N, ∀ (c : K) (m : M), g (TensorProduct.tmul ℤ c m) = TensorProduct.tmul ℤ c (f m) := by
  intro K M N _ _ _ _ _ f
  exact ⟨f.baseChange K, fun c m => f.baseChange_tmul K c m⟩

end YuiBasis
