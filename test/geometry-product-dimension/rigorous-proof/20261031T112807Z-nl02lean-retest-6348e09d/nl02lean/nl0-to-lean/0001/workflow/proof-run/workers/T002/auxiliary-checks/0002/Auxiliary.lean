import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤" := by
  classical
  intro s δ hs hδ
  obtain ⟨t, htE, htfin, htcover⟩ := h_H003.finite_cover_balls (half_pos hδ)
  letI : Fintype t := htfin.fintype
  let e := Fintype.equivFin t
  let U : ℕ → Set (YEuclid n) := fun i => if hi : i < Fintype.card t then Metric.ball (e.symm ⟨i, hi⟩).val (δ/2) else ∅
  have hc : E ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (htcover hx)
    let j := e ⟨y, hy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j.val, ?_⟩
    simpa [U, j] using hxy
  have hd : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ := by
    intro i
    dsimp [U]
    split_ifs with hi
    · rw [← Metric.eball_ofReal]
      calc
        Metric.ediam _ ≤ 2 * ENNReal.ofReal (δ/2) := Metric.ediam_eball_le
        _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_natCast 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    · simp
  have hfin : (∑' i, Metric.ediam (U i) ^ s) < ⊤ := by
    rw [tsum_eq_sum (s := Finset.range (Fintype.card t)) (fun i hi => ?_)]
    · exact ENNReal.sum_lt_top.mpr (fun i hi => ENNReal.rpow_lt_top_of_nonneg hs.le (lt_of_le_of_lt (hd i) ENNReal.ofReal_lt_top).ne)
    · have hi' : ¬ i < Fintype.card t := by simpa only [Finset.mem_range] using hi
      simp [U, hi', ENNReal.zero_rpow_of_pos hs]
  exact lt_of_le_of_lt (iInf_le_of_le U (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))) hfin
#check @checked
#print axioms checked
end YuiAuxiliary
