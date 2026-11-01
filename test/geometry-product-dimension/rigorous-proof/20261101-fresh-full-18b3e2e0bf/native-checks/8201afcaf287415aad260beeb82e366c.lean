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
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ x0 : GDVec n, Isometry (fun t : ℝ => GDPoint x0 t)" := by
  intro x0
  apply Isometry.of_dist_eq
  intro t u
  rw [h_T009.1 x0 x0 t u, dist_self]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_sq_eq_abs, abs_abs]
  exact Real.dist_eq t u |>.symm

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (x0 : GDVec n) (U : Set (GDVec (n + 1))), Metric.ediam (GDInterval ∩ (fun t : ℝ => GDPoint x0 t) ⁻¹' U) ≤ Metric.ediam U" := by
  intro x0 U
  have hf : Isometry (fun t : ℝ => GDPoint x0 t) := yui_aux_0001 n E h_H001 h_T009 x0
  rw [← hf.ediam_image (GDInterval ∩ (fun t : ℝ => GDPoint x0 t) ⁻¹' U)]
  apply Metric.ediam_mono
  rintro z ⟨t, ht, rfl⟩
  exact ht.2

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (s : ℝ) (a b : ℝ≥0∞), 0 ≤ s → a ≤ b → a ^ s ≤ b ^ s" := by
  intro s a b hs hab
  exact ENNReal.rpow_le_rpow hab hs
#check @checked
#print axioms checked
end YuiAuxiliary
