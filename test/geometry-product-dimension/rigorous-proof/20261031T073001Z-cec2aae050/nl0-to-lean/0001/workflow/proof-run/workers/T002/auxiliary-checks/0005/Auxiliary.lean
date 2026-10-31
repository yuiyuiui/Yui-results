import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → 0 < δ → ∃ (ι : Type) (_ : Fintype ι) (V : ι → Set (GP.Space n)), E ⊆ ⋃ i, V i ∧ (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧ (∑ i, ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s) < ⊤" := by
  classical
  intro s δ hs hδ
  obtain ⟨t, htE, ht, hcov⟩ := h_H003.finite_cover_balls (half_pos hδ)
  letI : Fintype t := ht.fintype
  let V : t → Set (GP.Space n) := fun x => Metric.ball x.1 (δ / 2)
  have hd : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ := by
    intro i
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' : dist x i.1 < δ / 2 := hx
    have hy' : dist y i.1 < δ / 2 := hy
    exact (dist_triangle_right x y i.1).trans (by linarith)
  refine ⟨t, inferInstance, V, ?_, hd, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion₂.mp (hcov hx) with ⟨y, hy, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  · apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact lt_of_le_of_lt (iSup_le fun _ => ENNReal.rpow_le_rpow (hd i) hs.le) (ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofReal_ne_top)
#check @checked
#print axioms checked
end YuiAuxiliary
