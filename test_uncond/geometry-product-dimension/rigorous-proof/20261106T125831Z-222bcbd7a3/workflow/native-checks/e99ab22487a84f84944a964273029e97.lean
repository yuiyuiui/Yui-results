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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "Function.Bijective (appendCoord n)" := by
  let g : Ambient (n + 1) → Ambient n × ℝ :=
    fun y => (WithLp.toLp 2 (fun i : Fin n => y i.castSucc), y (Fin.last n))
  have hleft : ∀ p : Ambient n × ℝ, g (appendCoord n p) = p := by
    intro p
    apply Prod.ext
    · apply PiLp.ext
      intro i
      simp [g, appendCoord]
    · simp [g, appendCoord]
  have hright : ∀ y : Ambient (n + 1), appendCoord n (g y) = y := by
    intro y
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [g, appendCoord]
    · simp [g, appendCoord]
  constructor
  · intro p q h
    calc
      p = g (appendCoord n p) := (hleft p).symm
      _ = g (appendCoord n q) := congrArg g h
      _ = q := hleft q
  · intro y
    exact ⟨g y, hright y⟩

theorem checked (n : ℕ) (E : Set (YuiBasis.Ambient n))  : yui_aux_type% "∀ p q : Ambient n × ℝ, dist (appendCoord n p) (appendCoord n q) ^ 2 = dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2" := by
  intro p q
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc, EuclideanSpace.dist_sq_eq]
  simp [appendCoord]
#check @checked
#print axioms checked
end YuiAuxiliary
