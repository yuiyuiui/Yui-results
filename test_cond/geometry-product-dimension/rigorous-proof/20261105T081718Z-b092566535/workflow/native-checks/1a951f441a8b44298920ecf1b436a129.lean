import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_H003 : IsCompact E) (h_T004 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) : yui_aux_type% "∀ (δ : ℝ), 0 < δ → ∃ (U : ℕ → Set (YuiEucl n)) (N : ℕ), YuiCover δ E U ∧ (∀ i, N ≤ i → U i = ∅)" := by
  classical
  intro δ hδ
  have hr : 0 < δ / 4 := by positivity
  obtain ⟨t, ht⟩ := h_H003.elim_finite_subcover
    (fun x : E => Metric.ball (x : YuiEucl n) (δ / 4))
    (fun _ => Metric.isOpen_ball)
    (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hr⟩)
  let e : t ≃ Fin t.card := t.equivFin
  let U : ℕ → Set (YuiEucl n) := fun i =>
    if h : i < t.card then Metric.ball ((e.symm ⟨i, h⟩).val : YuiEucl n) (δ / 4)
    else ∅
  have hb (x : YuiEucl n) :
      Metric.ediam (Metric.ball x (δ / 4)) ≤ ENNReal.ofReal (δ / 2) := by
    apply Metric.ediam_le_of_forall_dist_le
    intro y hy z hz
    have hy' : dist y x < δ / 4 := Metric.mem_ball.mp hy
    have hz' : dist x z < δ / 4 := by
      simpa only [dist_comm] using (Metric.mem_ball.mp hz)
    have := dist_triangle y x z
    linarith
  refine ⟨U, t.card, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    let j : Fin t.card := e ⟨y, hy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j.val, ?_⟩
    simpa [U, j] using hxy
  · intro i
    dsimp [U]
    split_ifs with hi
    · exact (hb _).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · simp
  · intro i hi
    simp [U, not_lt.mpr hi]
#check @checked
#print axioms checked
end YuiAuxiliary
