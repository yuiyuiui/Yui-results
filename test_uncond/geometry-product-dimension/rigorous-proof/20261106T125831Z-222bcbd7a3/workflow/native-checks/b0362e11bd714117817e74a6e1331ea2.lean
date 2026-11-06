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
abbrev T003.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A
end YuiPortTypes
universe u

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) : yui_aux_type% "∀ (s d r e : ℝ), 0 ≤ s → 0 ≤ d → d < r → 0 < e → ∃ a : ℝ, d < a ∧ a < r ∧ a ^ s < d ^ s + e" := by
  intro s d r e hs hd hdr he
  have hc : ContinuousAt (fun x : ℝ => x ^ s) d := (Real.continuous_rpow_const hs).continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc e he
  let η : ℝ := min δ (r - d) / 2
  have hη : 0 < η := half_pos (lt_min hδ (sub_pos.mpr hdr))
  have hηδ : η < δ := lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_left δ (r-d)) (by norm_num : (0:ℝ) ≤ 2)) (by linarith)
  have hηr : η < r - d := lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_right δ (r-d)) (by norm_num : (0:ℝ) ≤ 2)) (by linarith)
  refine ⟨d + η, by linarith, by linarith, ?_⟩
  have hdist : dist (d + η) d < δ := by rw [Real.dist_eq]; simpa [abs_of_pos hη] using hηδ
  have hp := hclose hdist
  rw [Real.dist_eq] at hp
  have := (abs_lt.mp hp).2
  linarith
#check @checked
#print axioms checked
end YuiAuxiliary
