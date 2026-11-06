import Mathlib
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
namespace YuiBasis
noncomputable def Content {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ δ),
    ∑' i, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ s
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
noncomputable def appendCoord (n : ℕ) (p : Ambient n × ℝ) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
end YuiBasis

open YuiBasis
namespace YuiPlan
noncomputable def H {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  hausdorffMeasure s A
noncomputable def C {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  YuiBasis.Content s (ENNReal.ofReal δ) A
end YuiPlan
open YuiPlan
namespace YuiPortTypes
abbrev T006.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval)
abbrev T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)
end YuiPortTypes
universe u

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), dimH A ≠ ⊤ → 0 < s → s < (dimH A).toReal → H s A = ⊤" := by
  intro X instX A s hf hs hsd
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have hc : ENNReal.ofReal s < dimH A := (ENNReal.ofReal_lt_iff_lt_toReal hs.le hf).2 hsd
  have hcoe : ((⟨s, hs.le⟩ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal s := ENNReal.coe_nnreal_eq _
  have hm : hausdorffMeasure (s : ℝ) A = ⊤ := by
    exact hausdorffMeasure_of_lt_dimH (d := (⟨s, hs.le⟩ : ℝ≥0)) (hcoe.symm ▸ hc)
  change hausdorffMeasure s A = ⊤
  exact hm
#check @checked
#print axioms checked
end YuiAuxiliary
