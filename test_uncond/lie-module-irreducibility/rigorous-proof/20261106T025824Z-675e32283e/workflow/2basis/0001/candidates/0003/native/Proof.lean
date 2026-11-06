import Mathlib

namespace YuiBasisObjects

noncomputable def dividedPower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r

def Stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (f : Module.End K V) : Prop :=
  ∀ w, w ∈ W → f w ∈ W

structure AdmissibleLattice (n : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (x y : Module.End ℂ V) where
  carrier : Submodule ℤ V
  zBasis : Module.Basis (Fin n) ℤ carrier
  cBasis : Module.Basis (Fin n) ℂ V
  coe_basis : ∀ i, (zBasis i : V) = cBasis i
  stableX : ∀ (r : ℕ) (m : V), m ∈ carrier → dividedPower x r m ∈ carrier
  stableY : ∀ (r : ℕ) (m : V), m ∈ carrier → dividedPower y r m ∈ carrier

end YuiBasisObjects

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] [FiniteDimensional F U] (b : I → U), LinearIndependent F b → Fintype.card I = Module.finrank F U → Submodule.span F (Set.range b) = ⊤ := by
  intro F U I _ _ _ _ _ b hb hc
  exact hb.span_eq_top_of_card_eq_finrank' hc
set_option Elab.async false in
theorem B002 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M), ∃ c : Module.Basis (Fin n) K (TensorProduct ℤ K M), (∀ i, c i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧ Module.finrank K (TensorProduct ℤ K M) = n := by
  intro K M _ _ _ n b
  refine ⟨b.baseChange K, ?_, ?_⟩
  · intro i
    simp
  · simpa using Module.finrank_eq_card_basis (b.baseChange K)
set_option Elab.async false in
theorem B003 : ∀ (K : Type*) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → (r.factorial : K) ≠ 0 := by
  intro K _ p _ _ r hr
  exact ((IsUnit.natCast_factorial_iff_of_charP (A := K) p).2 hr).ne_zero
set_option Elab.async false in
theorem B004 : ∀ (n j : ℕ), j ≤ n → Nat.choose n j * j.factorial * (n - j).factorial = n.factorial := by
  intro n j hj
  exact Nat.choose_mul_factorial_mul_factorial hj
set_option Elab.async false in
theorem B005 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m) := by
  intro K M _ _ _
  let F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M) :=
    { toFun := fun f => f.baseChange K
      map_one' := LinearMap.baseChange_one ℤ M
      map_mul' := fun f g => LinearMap.baseChange_mul f g
      map_zero' := LinearMap.baseChange_zero
      map_add' := fun f g => LinearMap.baseChange_add f g }
  refine ⟨F, ?_⟩
  intro f a m
  rfl
set_option Elab.async false in
theorem B006 : ∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] (b : Module.Basis I F U), (∀ u, ∑ i, b.repr u i • b i = u) ∧ (∀ f g : Module.End F U, (∀ i, f (b i) = g (b i)) → f = g) := by
  intro F U I _ _ _ _ b
  refine ⟨b.sum_repr, ?_⟩
  intro f g h
  exact b.ext h

end YuiBasis
