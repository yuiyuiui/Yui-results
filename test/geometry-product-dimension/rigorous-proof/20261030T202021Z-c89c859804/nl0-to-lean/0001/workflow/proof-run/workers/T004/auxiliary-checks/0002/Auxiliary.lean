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
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_H002 : IsCompact E) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → 0 < δ → ∃ T : Finset (GPEucl n), (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧ (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧ (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)" := by
  classical
  intro s δ hs hδ
  have hrad : 0 < δ / 2 := by positivity
  obtain ⟨T, hT⟩ := h_H002.elim_finite_subcover (fun x : GPEucl n => Metric.ball x (δ / 2)) (fun _ => Metric.isOpen_ball) (fun x hx => Set.mem_iUnion.mpr ⟨x, by simpa using hrad⟩)
  have hd : ∀ x : GPEucl n, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ := by
    intro x
    apply Metric.ediam_le_of_forall_dist_le
    intro y hy z hz
    have hy' : dist y x < δ / 2 := hy
    have hz' : dist x z < δ / 2 := by simpa only [dist_comm] using hz
    have ht := dist_triangle y x z
    linarith
  refine ⟨T, hT, fun x _ => hd x, ?_⟩
  exact ENNReal.sum_lt_top.mpr fun x hx => ENNReal.rpow_lt_top_of_nonneg hs.le (ne_of_lt (lt_of_le_of_lt (hd x) ENNReal.ofReal_lt_top))
#check @checked
#print axioms checked
end YuiAuxiliary
