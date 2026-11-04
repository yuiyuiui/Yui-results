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

namespace Local_T016
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T015 : dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E)) : yui_aux_type% "∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < 1 → 0 < (q : ℝ) ∧ (q : ℝ) < 1 ∧ ENNReal.ofReal (q : ℝ) = (q : ℝ≥0∞)" := by
  intro q hq hq1
  constructor
  · exact_mod_cast hq
  constructor
  · exact_mod_cast hq1
  · simp

end Local_T016
open Local_T016 in
theorem T016 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T015 : dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E)) :
    dimH E = 0 →
  (1 : ℝ≥0∞) ≤ dimH (GDProduct E) ∧
  (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hE
  have hdim : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH (GDProduct E) := by
    intro s hs hs1
    have hm : GDMeasure s GDInterval ≤ GDMeasure s (GDProduct E) := by
      unfold GDMeasure
      exact iSup_mono fun δ => iSup_mono fun hδ => h_T015 hE s δ hs hδ
    have hi : GDMeasure s GDInterval = ⊤ := h_T007.2.2.2 s hs hs1
    have hp : GDMeasure s (GDProduct E) = ⊤ := by
      rw [hi] at hm
      exact top_unique hm
    exact ((h_T002 (n + 1) (GDProduct E)).2 s hs).2.2.2.2.2 hp
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro q hq hq1
    obtain ⟨hqpos, hqone, hqcoe⟩ := (@yui_aux_0001 n E h_T002 h_T007 h_T015) q hq hq1
    rw [← hqcoe]
    exact hdim (q : ℝ) hqpos hqone
  · simp [hE]

#check @T016
#print axioms T016

end Translation
