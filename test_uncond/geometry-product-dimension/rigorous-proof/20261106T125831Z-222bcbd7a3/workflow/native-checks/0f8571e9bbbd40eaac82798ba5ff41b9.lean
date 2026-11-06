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

namespace Translation
set_option autoImplicit false

section
universe u
namespace Local_T003
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

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ r : ℝ≥0∞, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r" := by
  intro r hr
  by_cases ht : r = ∞
  · exact ⟨1, zero_lt_one, by simp [ht]⟩
  · refine ⟨r.toReal / 2, half_pos (ENNReal.toReal_pos (ne_of_gt hr) ht), ?_⟩
    have hhalf : r.toReal / 2 ≤ r.toReal := by linarith [ENNReal.toReal_nonneg (a := r)]
    calc
      ENNReal.ofReal (r.toReal / 2) ≤ ENNReal.ofReal r.toReal := ENNReal.ofReal_le_ofReal hhalf
      _ = r := ENNReal.ofReal_toReal ht

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := by
  intro X inst A s hs
  have hcost := @yui_aux_0001 n E X inst s hs
  have hmono := @yui_aux_0002 n E X inst A s
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ
    unfold C YuiBasis.Content
    simp_rw [hcost]
  · intro δ₁ δ₂ hδ₁ hδ
    exact hmono (ENNReal.ofReal δ₁) (ENNReal.ofReal δ₂) (ENNReal.ofReal_le_ofReal hδ)
  · have hH : H s A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), YuiBasis.Content s r A := by
      letI : MeasurableSpace X := borel X
      letI : BorelSpace X := ⟨rfl⟩
      exact hausdorffMeasure_apply s A
    rw [hH]
    apply le_antisymm
    · refine iSup₂_le fun r hr => ?_
      rcases @yui_aux_0003 n E r hr with ⟨δ, hδ, hδr⟩
      calc
        YuiBasis.Content s r A ≤ C s δ A := hmono (ENNReal.ofReal δ) r hδr
        _ ≤ ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := le_iSup₂_of_le δ hδ le_rfl
    · refine iSup₂_le fun δ hδ => ?_
      exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl

end
#check @T003
#print axioms T003

end Translation
