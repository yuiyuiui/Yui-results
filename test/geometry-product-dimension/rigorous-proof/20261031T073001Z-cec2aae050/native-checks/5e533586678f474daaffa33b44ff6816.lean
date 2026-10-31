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
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_H002 : E.Nonempty) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T003 : dimH GP.unitInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤)) : yui_aux_type% "∀ (r : ℝ≥0), 0 < r → (r : ℝ≥0∞) < 1 → 0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧ ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞)" := by
  intro r hr hr1
  constructor
  · exact_mod_cast hr
  constructor
  · exact_mod_cast hr1
  · exact ENNReal.ofReal_coe_nnreal
#check @checked
#print axioms checked
end YuiAuxiliary
