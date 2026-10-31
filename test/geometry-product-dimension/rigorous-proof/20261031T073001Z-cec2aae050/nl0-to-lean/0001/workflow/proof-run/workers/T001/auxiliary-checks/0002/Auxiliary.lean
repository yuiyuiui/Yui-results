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
theorem checked (n : ℕ) (E : Set (GP.Space n))  : yui_aux_type% "∀ (m : ℕ) (A : Set (GP.Space m)) (s : ℝ) (hs : 0 < s), let d : ℝ≥0 := ⟨s, hs.le⟩; (d : ℝ≥0∞) = ENNReal.ofReal s ∧ (dimH A < ENNReal.ofReal s → MeasureTheory.Measure.hausdorffMeasure s A = 0) ∧ (ENNReal.ofReal s < dimH A → MeasureTheory.Measure.hausdorffMeasure s A = ⊤) ∧ (MeasureTheory.Measure.hausdorffMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧ (MeasureTheory.Measure.hausdorffMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)" := by
  intro m A s hs d
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal s :=
    ENNReal.coe_nnreal_eq d
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hausdorffMeasure_of_dimH_lt (d := d) (hd.symm ▸ h)
  · intro h
    exact hausdorffMeasure_of_lt_dimH (d := d) (hd.symm ▸ h)
  · intro h
    rw [← hd]
    apply dimH_le_of_hausdorffMeasure_ne_top (d := d)
    change MeasureTheory.Measure.hausdorffMeasure s A ≠ ⊤
    rw [h]
    exact zero_ne_top
  · intro h
    rw [← hd]
    exact le_dimH_of_hausdorffMeasure_eq_top (d := d) h
#check @checked
#print axioms checked
end YuiAuxiliary
