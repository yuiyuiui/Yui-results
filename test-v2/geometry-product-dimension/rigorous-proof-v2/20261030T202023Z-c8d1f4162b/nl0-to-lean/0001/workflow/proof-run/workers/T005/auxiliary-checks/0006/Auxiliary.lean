import Mathlib
open scoped ENNReal NNReal
noncomputable section
abbrev YEucl (m : ℕ) := EuclideanSpace ℝ (Fin m)
def YI : Set ℝ := Set.Icc 0 1
def YJoin {m : ℕ} (x : YEucl m) (t : ℝ) : YEucl (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YBase {m : ℕ} (z : YEucl (m + 1)) : YEucl m :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def YLast {m : ℕ} (z : YEucl (m + 1)) : ℝ := z (Fin.last m)
def YF {m : ℕ} (A : Set (YEucl m)) : Set (YEucl (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ YI, z = YJoin x t}
def YLine (t : ℝ) : YEucl 1 := WithLp.toLp 2 (fun _ => t)
def YCover {X : Type*} [PseudoEMetricSpace X]
    (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def YCost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s
def YContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YCover δ A U), YCost s U
def YHaus {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A
def YCritical {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) : Prop :=
  0 ≤ dimH A ∧ ∀ s : ℝ, 0 < s →
    YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → YHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → YHaus s A = ⊤) ∧
    (YHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (YHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEucl n)) (h_H002 : IsCompact E) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤" := by
  classical
  intro s δ hs hδ
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hc : E ⊆ ⋃ a : E, Metric.ball a.val (δ / 2) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hδ2⟩
  obtain ⟨t, ht⟩ := h_H002.elim_finite_subcover
    (fun a : E => Metric.ball a.val (δ / 2)) (fun a => Metric.isOpen_ball) hc
  let e : t ≃ Fin t.card := t.equivFin
  let U : ℕ → Set (YEucl n) := fun j =>
    if hj : j < t.card then Metric.ball (e.symm ⟨j, hj⟩).val.val (δ / 2) else ∅
  have hcov : E ⊆ ⋃ j, U j := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    let a' : t := ⟨a, ha⟩
    let j : Fin t.card := e a'
    have hU : U j.val = Metric.ball a.val (δ / 2) := by
      dsimp only [U]
      rw [dif_pos j.isLt]
      change Metric.ball (e.symm (e a')).val.val (δ / 2) = _
      rw [e.symm_apply_apply]
    exact Set.mem_iUnion.mpr ⟨j.val, by rw [hU]; exact hxa⟩
  have hb : ∀ c : YEucl n, Metric.ediam (Metric.ball c (δ / 2)) ≤ ENNReal.ofReal δ := by
    intro c
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' : dist x c < δ / 2 := Metric.mem_ball.mp hx
    have hy' : dist c y < δ / 2 := by simpa only [dist_comm] using Metric.mem_ball.mp hy
    have htri : dist x y ≤ dist x c + dist c y := dist_triangle x c y
    linarith
  have hd : ∀ j, Metric.ediam (U j) ≤ ENNReal.ofReal δ := by
    intro j
    dsimp only [U]
    split_ifs with hj
    · exact hb _
    · simp only [Metric.ediam_empty]; exact zero_le _
  have hcover : YCover δ E U := ⟨hcov, hd⟩
  have hzero : ∀ j, j ∉ Finset.range t.card → (Metric.ediam (U j)) ^ s = 0 := by
    intro j hj
    have hj' : ¬ j < t.card := by simpa only [Finset.mem_range] using hj
    simp only [U, dif_neg hj', Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]
  have hcost : YCost s U < ⊤ := by
    unfold YCost
    rw [tsum_eq_sum hzero]
    apply ENNReal.sum_lt_top.mpr
    intro j hj
    apply (ENNReal.rpow_lt_top_iff_of_pos hs).mpr
    exact (hd j).trans_lt ENNReal.ofReal_lt_top
  have hle : YContent s δ E ≤ YCost s U := by
    unfold YContent
    exact iInf_le_of_le U (iInf_le_of_le hcover le_rfl)
  exact hle.trans_lt hcost
#check @checked
#print axioms checked
end YuiAuxiliary
