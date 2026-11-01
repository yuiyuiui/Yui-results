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

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T001 : ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A) : yui_aux_type% "∀ (s : ℝ) (hs : 0 < s), (let d : NNReal := ⟨s, hs.le⟩; (d : ENNReal) = ENNReal.ofReal s)" := by
  intro s hs
  exact ENNReal.coe_nnreal_eq (⟨s, hs.le⟩ : NNReal)

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (E : Set (GDVec n)) (h_T001 : ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A) :
    ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A) := by
  intro m A
  refine ⟨bot_le, ?_⟩
  intro s hs
  let d : NNReal := ⟨s, hs.le⟩
  have hd : (d : ENNReal) = ENNReal.ofReal s := @yui_aux_0001 n E h_T001 s hs
  rw [h_T001 m A s hs]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : (d : ENNReal) < dimH A := by rw [hd]; exact h
    exact hausdorffMeasure_of_lt_dimH (s := A) (d := d) h'
  · intro h
    have h' : dimH A < (d : ENNReal) := by rw [hd]; exact h
    exact hausdorffMeasure_of_dimH_lt (s := A) (d := d) h'
  · intro h
    have h' : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ := ne_of_lt h
    have hdim := dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := d) h'
    simpa only [hd] using hdim
  · intro h
    have h' : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ := by
      rw [show (d : ℝ) = s from rfl, h]
      exact ENNReal.zero_ne_top
    have hdim := dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := d) h'
    simpa only [hd] using hdim
  · intro h
    have h' : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ := h
    have hdim := le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := d) h'
    simpa only [hd] using hdim

#check @T002
#print axioms T002

end Translation
