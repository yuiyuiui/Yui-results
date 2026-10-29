import ResidualForcingAlgebra
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem dynamic_small_first_bound (externalTrilinear : LiWuTrilinearEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b τ A B : ℝ, 0 ≤ a → a ≤ b → b - a ≤ τ → τ ≤ 1 →
      0 ≤ τ → 0 ≤ A → 0 ≤ B →
      ∀ Y Z V : ℝ → Sobolev 0, ∀ dY dZ dV : ℝ → Sobolev (-pStar),
      MemLp Y ∞ (volume.restrict (Set.Icc a b)) →
      MemLp Z ∞ (volume.restrict (Set.Icc a b)) →
      MemLp V ∞ (volume.restrict (Set.Icc a b)) →
      MemLp dY ∞ (volume.restrict (Set.Icc a b)) →
      MemLp dZ ∞ (volume.restrict (Set.Icc a b)) →
      MemLp dV ∞ (volume.restrict (Set.Icc a b)) →
      WeakTimeDerivative a b (fun t => (Y t).val) (fun t => (dY t).val) →
      WeakTimeDerivative a b (fun t => (Z t).val) (fun t => (dZ t).val) →
      WeakTimeDerivative a b (fun t => (V t).val) (fun t => (dV t).val) →
      timeXNorm a b Y dY ≤ A → timeXNorm a b Z dZ ≤ B → timeXNorm a b V dV ≤ B →
      timeLInfinity a b (fun t => inclusionMap (-pStar) 0 (by norm_num [pStar]) (Y t)) ≤ τ * A →
      InSobolev 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) ∧
      hNorm 0 (CIntegral a b (fun t => (Y t).val) (fun t => (Z t).val) (fun t => (V t).val)) ≤ C * τ * A * B ^ 2 := by
  obtain ⟨C, hC, hd⟩ := dynamic_small_input_bound externalTrilinear
  refine ⟨C, hC, ?_⟩
  intro a b τ A B ha hab hlen hτ1 hτ hA hB Y Z V dY dZ dV hY hZ hV hdY hdZ hdV hwY hwZ hwV hxY hxZ hxV hnY
  exact hd a b τ A B ha hab hlen hτ1 hτ hA hB ![Y,Z,V] ![dY,dZ,dV]
    (by intro j; fin_cases j <;> first | exact hY | exact hZ | exact hV)
    (by intro j; fin_cases j <;> first | exact hdY | exact hdZ | exact hdV)
    (by intro j; fin_cases j <;> first | exact hwY | exact hwZ | exact hwV)
    0 hxY (by intro j hj; fin_cases j; exact (hj rfl).elim; exact hxZ; exact hxV) hnY

end KdV
