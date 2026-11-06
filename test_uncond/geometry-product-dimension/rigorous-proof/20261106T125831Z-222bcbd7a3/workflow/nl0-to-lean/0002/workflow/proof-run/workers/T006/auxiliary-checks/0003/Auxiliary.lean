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
abbrev T004.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧
  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →
    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧
      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)
abbrev T005.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i))
end YuiPortTypes
universe u

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s δ : ℝ), 0 < s → 0 < δ → ∀ (W : ℕ → Set X), (A ⊆ ⋃ i, W i) → (∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal δ) → C s δ A ≤ ∑' i, Metric.ediam (W i) ^ s" := by
  intro X _ A s δ hs hδ W hc hd
  rw [(h_T004 X A s hs).1 δ hδ]
  exact iInf_le_of_le W (iInf_le_of_le hc (iInf_le_of_le hd (le_refl (∑' i, Metric.ediam (W i) ^ s))))
#check @checked
#print axioms checked
end YuiAuxiliary
