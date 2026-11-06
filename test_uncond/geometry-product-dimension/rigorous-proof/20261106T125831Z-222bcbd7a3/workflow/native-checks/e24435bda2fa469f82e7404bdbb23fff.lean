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
universe u

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (s : ℝ), 0 < s → ∀ B : Set X, (⨆ (_ : B.Nonempty), Metric.ediam B ^ s) = Metric.ediam B ^ s" := by
  intro X _ s hs B
  by_cases hB : B.Nonempty
  · simp [hB]
  · have hE : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    simp [hE, ENNReal.zero_rpow_of_pos hs]

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ) (r₁ r₂ : ℝ≥0∞), r₁ ≤ r₂ → YuiBasis.Content s r₂ A ≤ YuiBasis.Content s r₁ A" := by
  intro X _ A s r₁ r₂ hr
  unfold YuiBasis.Content
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
  exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le (fun i => (hd i).trans hr) le_rfl))

theorem checked (n : ℕ) (E : Set (YuiBasis.Ambient n))  : yui_aux_type% "∀ r : ℝ≥0∞, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r" := by
  intro r hr
  by_cases ht : r = ∞
  · exact ⟨1, zero_lt_one, by simp [ht]⟩
  · refine ⟨r.toReal / 2, half_pos (ENNReal.toReal_pos (ne_of_gt hr) ht), ?_⟩
    have hhalf : r.toReal / 2 ≤ r.toReal := by linarith [ENNReal.toReal_nonneg (a := r)]
    calc
      ENNReal.ofReal (r.toReal / 2) ≤ ENNReal.ofReal r.toReal := ENNReal.ofReal_le_ofReal hhalf
      _ = r := ENNReal.ofReal_toReal ht
#check @checked
#print axioms checked
end YuiAuxiliary
