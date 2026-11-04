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

namespace Local_T015
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

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (s : ℝ) (a b : ℝ≥0∞), 0 ≤ s → a ≤ b → a ^ s ≤ b ^ s" := by
  intro s a b hs hab
  exact ENNReal.rpow_le_rpow hab hs

end Local_T015
open Local_T015 in
theorem T015 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) :
    dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E) := by
  intro hD s δ hs hδ
  obtain ⟨x0, hx0⟩ := h_H001
  have hE : E.Nonempty := ⟨x0, hx0⟩
  unfold GDContent
  refine le_iInf fun U => le_iInf fun hcover => le_iInf fun hscale => ?_
  let V : ℕ → Set ℝ := fun i => GDInterval ∩ (fun t : ℝ => GDPoint x0 t) ⁻¹' U i
  have hVcover : GDInterval ⊆ ⋃ i, V i := by
    intro t ht
    have hpt : GDPoint x0 t ∈ GDProduct E := ⟨x0, hx0, t, ht, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hpt)
    exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩
  have hVdiam : ∀ i, Metric.ediam (V i) ≤ Metric.ediam (U i) := by
    intro i
    exact yui_aux_0002 n E hE h_T009 x0 (U i)
  have hVscale : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ :=
    fun i => (hVdiam i).trans (hscale i)
  refine le_trans (iInf_le_of_le V (iInf_le_of_le hVcover (iInf_le_of_le hVscale le_rfl))) ?_
  apply ENNReal.tsum_le_tsum
  intro i
  unfold GDCost
  refine iSup_le fun hVi => ?_
  have hUi : (U i).Nonempty := by
    obtain ⟨t, ht⟩ := hVi
    exact ⟨GDPoint x0 t, ht.2⟩
  refine le_iSup_of_le hUi ?_
  exact yui_aux_0003 n E hE h_T009 s (Metric.ediam (V i)) (Metric.ediam (U i)) hs.le (hVdiam i)

#check @T015
#print axioms T015

end Translation
