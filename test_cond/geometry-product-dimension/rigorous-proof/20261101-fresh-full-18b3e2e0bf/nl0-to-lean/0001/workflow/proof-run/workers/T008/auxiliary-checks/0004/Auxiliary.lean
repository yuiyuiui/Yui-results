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

namespace YuiAuxiliary
set_option autoImplicit false
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
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → 0 < ε → 0 < q ∧ ∃ W : ℕ → Set (GDVec n), E ⊆ ⋃ i, W i ∧ (∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal r) ∧ (∑' i, GDCost q (W i)) < ENNReal.ofReal (ε / 2)" := by
  intro q r ε hq hr hε
  have hqp : 0 < q := by
    by_contra h
    have : ENNReal.ofReal q = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h)
    rw [this] at hq
    exact (not_lt_of_ge bot_le hq)
  have hm : GDMeasure q E = 0 := ((h_T002 n E).2 q hqp).2.2.1 hq
  have hc : GDContent q r E = 0 := by
    apply le_antisymm _ bot_le
    calc
      GDContent q r E ≤ GDMeasure q E := le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      _ = 0 := hm
  have ht : GDContent q r E < ENNReal.ofReal (ε / 2) := by rw [hc]; positivity
  simp only [GDContent, iInf_lt_iff] at ht
  rcases ht with ⟨W, hW, hd, hs⟩
  exact ⟨hqp, W, hW, hd, hs⟩

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
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "1 ≤ n → ∀ (x : GDVec n) (d : ℝ), 0 < d → (Metric.ball x (d / 2)).Nonempty ∧ Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal d" := by
  intro hn x d hd
  letI : NeZero n := ⟨by omega⟩
  constructor
  · exact ⟨x, Metric.mem_ball_self (by positivity)⟩
  · have hb : Metric.ediam (Metric.ball x (d / 2)) ≠ ⊤ := Metric.isBounded_ball.ediam_ne_top
    calc
      Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal (Metric.diam (Metric.ball x (d / 2))) := (ENNReal.ofReal_toReal hb).symm
      _ = ENNReal.ofReal d := by rw [Metric.diam_ball_eq x (by positivity)]; congr 1; ring

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
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
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ q r a : ℝ, 0 < q → 0 < r → 0 < a → 0 < min r (a ^ (1 / q)) ∧ min r (a ^ (1 / q)) ≤ r ∧ (ENNReal.ofReal (min r (a ^ (1 / q)))) ^ q ≤ ENNReal.ofReal a" := by
  intro q r a hq hr ha
  have hp : 0 < a ^ (1 / q) := Real.rpow_pos_of_pos ha _
  have hd : 0 < min r (a ^ (1 / q)) := lt_min hr hp
  refine ⟨hd, min_le_left _ _, ?_⟩
  rw [ENNReal.ofReal_rpow_of_pos hd]
  apply ENNReal.ofReal_le_ofReal
  calc
    (min r (a ^ (1 / q))) ^ q ≤ (a ^ (1 / q)) ^ q := Real.rpow_le_rpow hd.le (min_le_right _ _) hq.le
    _ = a := by rw [one_div, Real.rpow_inv_rpow ha.le hq.ne']
#check @checked
#print axioms checked
end YuiAuxiliary
