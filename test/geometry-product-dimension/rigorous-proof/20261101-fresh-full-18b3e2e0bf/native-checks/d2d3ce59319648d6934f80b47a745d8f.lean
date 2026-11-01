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
theorem checked (n : ℕ) (E : Set (GDVec n))  : yui_aux_type% "∀ (V : Set ℝ), Bornology.IsBounded V → V.Nonempty → ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ V ⊆ J ∧ MeasureTheory.volume J = Metric.ediam V + ENNReal.ofReal (2 * η)" := by
  intro V hV hne η hη
  refine ⟨Set.Ioo (sInf V - η) (sSup V + η), isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    have hx' := hV.subset_Icc_sInf_sSup hx
    exact ⟨by dsimp at *; linarith [hx'.1], by dsimp at *; linarith [hx'.2]⟩
  · rw [Real.volume_Ioo, Real.ediam_eq hV]
    have hnonneg : 0 ≤ sSup V - sInf V := sub_nonneg.mpr (Real.sInf_le_sSup V hV.bddBelow hV.bddAbove)
    rw [← ENNReal.ofReal_add hnonneg (by positivity)]
    congr 1
    ring
#check @checked
#print axioms checked
end YuiAuxiliary
