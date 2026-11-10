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
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (ε : ℝ≥0), 0 < ε → 0 < (ε : ℝ) ∧ ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞)" := by
  intro ε hε
  exact ⟨by exact_mod_cast hε, ENNReal.ofReal_coe_nnreal⟩

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (q : ℝ) (U : ℕ → Set (GDVec (n + 1))), (∑' i : {j : ℕ | (U j).Nonempty}, (Metric.ediam (U i)) ^ q) = ∑' i, GDCost q (U i)" := by
  classical
  intro q U
  have hcost (i : {j : ℕ | (U j).Nonempty}) : GDCost q (U i) = (Metric.ediam (U i)) ^ q := by
    simp [GDCost, i.property]
  calc
    (∑' i : {j : ℕ | (U j).Nonempty}, (Metric.ediam (U i)) ^ q) = ∑' i : {j : ℕ | (U j).Nonempty}, GDCost q (U i) := tsum_congr fun i => (hcost i).symm
    _ = ∑' i, GDCost q (U i) := by
      apply tsum_subtype_eq_of_support_subset
      intro i hi
      change (U i).Nonempty
      by_contra hempty
      have hz : GDCost q (U i) = 0 := by simp [GDCost, hempty]
      exact hi hz
#check @checked
#print axioms checked
end YuiAuxiliary
