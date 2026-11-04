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

namespace Local_T014
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤) : yui_aux_type% "∀ (d : ℝ) (Q : ℝ≥0∞), 0 < d → (∀ s : ℝ, 0 < s → s < d → ENNReal.ofReal (s + 1) ≤ Q) → ENNReal.ofReal (d + 1) ≤ Q" := by
  intro d Q hd h
  by_cases hQ : Q = ⊤
  · simp [hQ]
  by_contra hn
  have hlt : Q.toReal < d + 1 := by
    by_contra hh
    exact hn (ENNReal.ofReal_le_of_le_toReal (le_of_not_gt hh))
  let a : ℝ := max 0 (Q.toReal - 1)
  have had : a < d := max_lt hd (by linarith)
  let s : ℝ := (a + d) / 2
  have ha0 : 0 ≤ a := le_max_left _ _
  have has : a < s := by dsimp [s]; linarith
  have hs0 : 0 < s := lt_of_le_of_lt ha0 has
  have hsd : s < d := by dsimp [s]; linarith
  have hb : ENNReal.ofReal (s + 1) ≤ Q := h s hs0 hsd
  have hb' : s + 1 ≤ Q.toReal := by
    have ht := ENNReal.toReal_mono hQ hb
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ s + 1)] using ht
  have hqa : Q.toReal - 1 ≤ a := le_max_right _ _
  linarith

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤) : yui_aux_type% "∀ s : ℝ, 0 ≤ s → s < (dimH E).toReal → ENNReal.ofReal s < dimH E" := by
  intro s hs hsd
  have hD : dimH E ≠ ⊤ := h_T004.2.2.2.1.ne
  apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hD).mp
  simpa only [ENNReal.toReal_ofReal hs] using hsd

end Local_T014
open Local_T014 in
theorem T014 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤) :
    0 < dimH E → dimH E + 1 ≤ dimH (GDProduct E) := by
  intro hpos
  have hfinite : dimH E < ⊤ := h_T004.2.2.2.1
  have hdpos : 0 < (dimH E).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hpos, hfinite⟩
  have hend : ENNReal.ofReal ((dimH E).toReal + 1) ≤ dimH (GDProduct E) := by
    apply (@yui_aux_0001 n E h_T002 h_T004 h_T013) (dimH E).toReal (dimH (GDProduct E)) hdpos
    intro s hs hsd
    have hsD : ENNReal.ofReal s < dimH E :=
      (@yui_aux_0002 n E h_T002 h_T004 h_T013) s hs.le hsd
    have hsp : 0 < s + 1 := by linarith
    exact (h_T002 (n + 1) (GDProduct E)).2 (s + 1) hsp |>.2.2.2.2.2 (h_T013 s hs hsD)
  have hconvert : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add hdpos.le (by norm_num), ENNReal.ofReal_toReal hfinite.ne]
    simp
  rw [hconvert] at hend
  exact hend

#check @T014
#print axioms T014

end Translation
