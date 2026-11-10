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
theorem checked (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ N : ℕ, GDInterval ⊆ ⋃ i : Fin (N + 1), Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ))" := by
  intro N x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hN : (0 : ℝ) < N + 1 := by positivity
  apply Set.mem_iUnion.mpr
  by_cases he : x = 1
  · refine ⟨⟨N, Nat.lt_succ_self N⟩, ?_⟩
    simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
    subst x
    constructor
    · apply (div_le_iff₀ hN).mpr
      linarith
    · rw [div_self (ne_of_gt hN)]
  · have hlt : x < 1 := lt_of_le_of_ne hx1 he
    have hmul : 0 ≤ x * (N + 1 : ℝ) := mul_nonneg hx0 hN.le
    have hf : ⌊x * (N + 1 : ℝ)⌋₊ < N + 1 := by
      apply (Nat.floor_lt hmul).mpr
      push_cast
      nlinarith
    refine ⟨⟨⌊x * (N + 1 : ℝ)⌋₊, hf⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ hN).mpr
      exact Nat.floor_le hmul
    · apply (le_div_iff₀ hN).mpr
      exact (Nat.lt_floor_add_one _).le
#check @checked
#print axioms checked
end YuiAuxiliary
