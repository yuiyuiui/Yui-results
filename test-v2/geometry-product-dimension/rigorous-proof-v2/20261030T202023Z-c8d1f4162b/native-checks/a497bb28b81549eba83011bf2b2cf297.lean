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
theorem checked (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T005 : (∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, |x i| ≤ L) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) : yui_aux_type% "∀ (A : Set (YEucl n)), A.Subsingleton → ∀ s : ℝ, 0 < s → YHaus s A = 0" := by
  intro A hA s hs
  apply le_antisymm _ (zero_le _)
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  let U : ℕ → Set (YEucl n) := fun _ => A
  have hcov : YCover δ A U := by
    constructor
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    · intro i
      change Metric.ediam A ≤ ENNReal.ofReal δ
      rw [Metric.ediam_subsingleton hA]
      exact zero_le _
  change YContent s δ A ≤ 0
  calc
    YContent s δ A ≤ YCost s U := iInf_le_of_le U (iInf_le _ hcov)
    _ = 0 := by
      simp [YCost, U, Metric.ediam_subsingleton hA, ENNReal.zero_rpow_of_pos hs]
#check @checked
#print axioms checked
end YuiAuxiliary
