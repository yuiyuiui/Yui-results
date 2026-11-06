import Mathlib

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (n : ℕ) (b : Fin n → V), LinearIndependent F b → Module.finrank F V = n → Submodule.span F (Set.range b) = ⊤ := by
  intro F _ V _ _ _ n b hb hd
  exact hb.span_eq_top_of_card_eq_finrank' (by simpa using hd.symm)
set_option Elab.async false in
theorem B002 : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (K : Type) [Field K] (n : ℕ) (b : Module.Basis (Fin n) ℤ M), ∃ c : Module.Basis (Fin n) K (TensorProduct ℤ K M), ∀ i, c i = TensorProduct.tmul ℤ (1 : K) (b i) := by
  intro M _ _ K _ n b
  refine ⟨b.baseChange K, ?_⟩
  intro i
  simp
set_option Elab.async false in
theorem B003 : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (K : Type) [Field K], ∃ F : Module.End ℤ M →ₐ[ℤ] Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m) := by
  intro M _ _ K _
  refine ⟨Module.End.baseChangeHom ℤ K M, ?_⟩
  intro f a m
  rfl
set_option Elab.async false in
theorem B004 : ∀ (K : Type) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → IsUnit (Nat.factorial r : K) := by
  intro K _ p _ _ r hr
  exact (IsUnit.natCast_factorial_iff_of_charP p).2 hr
set_option Elab.async false in
theorem B005 : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] (n : ℕ) (b : Module.Basis (Fin n) F V), Module.finrank F V = n := by
  intro F _ V _ _ n b
  simpa using Module.finrank_eq_card_basis b

end YuiBasis
