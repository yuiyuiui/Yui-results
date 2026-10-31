import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_H002 : IsCompact E) : yui_aux_type% "∀ (s δ : ℝ) (T : Finset (GPEucl n)), 0 < s → (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) → (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) → GPcontent s δ E < ⊤" := by
  classical
  intro s δ T hs hT hd
  let N := Fintype.card T
  let e : T ≃ Fin N := Fintype.equivFin T
  let U : ℕ → Set (GPEucl n) := fun i => if hi : i < N then Metric.ball (e.symm ⟨i, hi⟩).val (δ / 2) else ∅
  have hcover : GPcover E δ U := by
    constructor
    · intro y hy
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hT hy)
      let t : T := ⟨x, hx⟩
      refine Set.mem_iUnion.mpr ⟨(e t).val, ?_⟩
      simpa only [U, dif_pos (e t).isLt, Fin.eta, Equiv.symm_apply_apply] using hyx
    · intro i
      dsimp [U]
      split_ifs with hi
      · exact hd _ (e.symm ⟨i, hi⟩).property
      · simp
  have hcost : GPcost s U < ⊤ := by
    unfold GPcost
    rw [tsum_eq_sum (s := Finset.range N) (fun i hi => ?_)]
    · refine ENNReal.sum_lt_top.mpr fun i hi => ?_
      exact ENNReal.rpow_lt_top_of_nonneg hs.le (ne_of_lt (lt_of_le_of_lt (hcover.2 i) ENNReal.ofReal_lt_top))
    · have hi' : ¬ i < N := by simpa only [Finset.mem_range] using hi
      simp only [U, dif_neg hi', Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]
  exact lt_of_le_of_lt (iInf_le_of_le U (iInf_le_of_le hcover le_rfl)) hcost
#check @checked
#print axioms checked
end YuiAuxiliary
