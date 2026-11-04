import Mathlib
open scoped ENNReal NNReal BigOperators
noncomputable section

abbrev GDVec (m : ℕ) := EuclideanSpace ℝ (Fin m)

def GDLine (t : ℝ) : GDVec 1 :=
  WithLp.toLp 2 (fun _ => t)

def GDInterval : Set ℝ := Set.Icc 0 1

def GDPoint {m : ℕ} (x : GDVec m) (t : ℝ) : GDVec (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)

def GDProduct {m : ℕ} (A : Set (GDVec m)) : Set (GDVec (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ GDInterval, z = GDPoint x t}

def GDCost {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (_ : A.Nonempty), (Metric.ediam A) ^ s

def GDContent {X : Type*} [PseudoEMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, GDCost s (U i)

def GDMeasure {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GDContent s δ A

def GDPositiveCover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (q r ε : ℝ) : Prop :=
  ∃ (K : Set ℕ) (U : K → Set X),
    A ⊆ ⋃ i, U i ∧
    (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧
    (∑' i, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal ε

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ r : ℝ≥0∞, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r" := by
  intro r hr
  by_cases ht : r = ⊤
  · exact ⟨1, zero_lt_one, by simp [ht]⟩
  · exact ⟨r.toReal, ENNReal.toReal_pos (ne_of_gt hr) ht, ENNReal.ofReal_toReal_le⟩

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (E : Set (GDVec n))  :
    ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A := by
  intro m A s hs
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  let C : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (U : ℕ → Set (GDVec m)) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, GDCost s (U i)
  have hC : Antitone C := by
    intro r t hrt
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    exact iInf_le_of_le U (iInf_le_of_le hU
      (iInf_le_of_le (fun i => (hd i).trans hrt) le_rfl))
  change (⨆ δ : ℝ, ⨆ _ : 0 < δ, C (ENNReal.ofReal δ)) =
    ⨆ r : ℝ≥0∞, ⨆ _ : 0 < r, C r
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨δ, hδ, hδr⟩ := yui_aux_0001 n E r hr
    exact (hC hδr).trans (le_iSup₂_of_le δ hδ le_rfl)

#check @T001
#print axioms T001

end Translation
