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
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ {X : Type} [MetricSpace X] {ι : Type} [Encodable ι]\n    (s δ : ℝ) (A : Set X) (V : ι → Set X),\n    A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →\n    GP.content s δ A ≤ ∑' i, (Metric.ediam (V i)) ^ s" := by
  intro X _ ι _ s δ A V hcov hdiam
  classical
  let U : ℕ → Set X := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
  have hU : GP.Cover A δ U := by
    constructor
    · simpa only [U, Encodable.iUnion_decode₂] using hcov
    · intro j
      dsimp [U]
      rw [Metric.ediam_iUnion_mem_option]
      exact iSup_le fun b => iSup_le fun _ => hdiam b
  calc
    GP.content s δ A ≤ GP.cost s U := iInf_le_of_le U (iInf_le _ hU)
    _ = ∑' i, ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s := by
      exact tsum_iUnion_decode₂ (fun t : Set X => ⨆ (_ : t.Nonempty), Metric.ediam t ^ s)
        (by simp) V
    _ ≤ ∑' i, Metric.ediam (V i) ^ s := ENNReal.tsum_le_tsum (fun i => iSup_le fun _ => le_rfl)
#check @checked
#print axioms checked
end YuiAuxiliary
