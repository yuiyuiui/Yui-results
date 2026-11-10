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
theorem checked (n : ℕ) (E : Set (GDVec n)) (h_H002 : IsCompact E) (h_T003 : Bornology.IsBounded E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤" := by
  classical
  intro s δ hs hδ
  have hcover : E ⊆ ⋃ x : E, Metric.ball (x : GDVec n) (δ / 2) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using (half_pos hδ)⟩
  obtain ⟨t, ht⟩ := h_H002.elim_finite_subcover
    (fun x : E => Metric.ball (x : GDVec n) (δ / 2))
    (fun _ => Metric.isOpen_ball) hcover
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let U : ℕ → Set (GDVec n) := fun i =>
    if hi : i < Fintype.card t then
      Metric.ball (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) (δ / 2)
    else ∅
  have hUcover : E ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    let j : t := ⟨y, hy⟩
    refine Set.mem_iUnion.mpr ⟨(e j).val, ?_⟩
    simpa [U, (e j).isLt, j] using hxy
  have hUdiam : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ := by
    intro i
    dsimp [U]
    split_ifs with hi
    · apply Metric.ediam_le_of_forall_dist_le
      intro x hx y hy
      have hx' : dist x (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) < δ / 2 := hx
      have hy' : dist y (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) < δ / 2 := hy
      calc
        dist x y ≤ dist x (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) +
          dist y (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) := dist_triangle_right _ _ _
        _ ≤ δ := by linarith
    · simp
  have hcost : ∀ i, GDCost s (U i) < ⊤ := by
    intro i
    have hd : Metric.ediam (U i) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hUdiam i)
    by_cases hi : (U i).Nonempty
    · simpa [GDCost, hi] using ENNReal.rpow_lt_top_of_nonneg hs.le hd
    · simp [GDCost, hi]
  have hsum : (∑' i, GDCost s (U i)) < ⊤ := by
    rw [tsum_eq_sum (s := Finset.range (Fintype.card t)) (fun i hi => ?_)]
    · exact ENNReal.sum_lt_top.mpr (fun i _ => hcost i)
    · have hi' : ¬ i < Fintype.card t := by simpa using hi
      simp [U, hi', GDCost]
  exact lt_of_le_of_lt
    (iInf_le_of_le U (iInf_le_of_le hUcover (iInf_le_of_le hUdiam le_rfl))) hsum
#check @checked
#print axioms checked
end YuiAuxiliary
