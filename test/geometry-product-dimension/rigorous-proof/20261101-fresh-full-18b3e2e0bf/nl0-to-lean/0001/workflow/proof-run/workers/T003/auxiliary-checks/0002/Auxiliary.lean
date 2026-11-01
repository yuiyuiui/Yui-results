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
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (l : Fin n → ℝ) (h : ℝ), 0 ≤ h → Metric.ediam {x : GDVec n | ∀ j, l j ≤ x j ∧ x j ≤ l j + h} ≤ (n : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal h" := by
  intro l h hh
  apply Metric.ediam_le
  intro x hx y hy
  rw [PiLp.edist_eq_sum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  norm_num only [ENNReal.toReal_ofNat]
  calc
    (∑ i : Fin n, edist (x i) (y i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∑ i : Fin n, (ENNReal.ofReal h) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      gcongr with i
      rw [edist_dist, Real.dist_eq]
      apply ENNReal.ofReal_le_ofReal
      exact abs_le.mpr ⟨by linarith [(hx i).1, (hy i).2], by linarith [(hy i).1, (hx i).2]⟩
    _ = (n : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal h := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.rpow_mul]
      norm_num

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (B : ℕ), (∀ x ∈ E, ∀ j : Fin n, |x j| ≤ B) → ∀ (k : ℕ), 0 < k → ∃ t : (Fin n → Fin ((2 * B + 2) * k)) → Set (GDVec n), E ⊆ ⋃ i, t i ∧ ∀ i, Metric.ediam (t i) ≤ (n : ℝ≥0∞) ^ (1 / 2 : ℝ) * (1 / (k : ℝ≥0∞))" := by
  intro B hB k hk
  have kp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let t : (Fin n → Fin ((2 * B + 2) * k)) → Set (GDVec n) := fun f =>
    {x | ∀ j, -(B : ℝ) + (f j : ℝ) / k ≤ x j ∧ x j ≤ -(B : ℝ) + (f j : ℝ) / k + 1 / k}
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    have bounds : ∀ j, -(B : ℝ) ≤ x j ∧ x j ≤ B := fun j => abs_le.mp (hB x hx j)
    have nonneg : ∀ j, 0 ≤ (x j + B) * k := fun j => mul_nonneg (by linarith [(bounds j).1]) kp.le
    let f : Fin n → Fin ((2 * B + 2) * k) := fun j =>
      ⟨⌊(x j + B) * k⌋₊, by
        apply (Nat.floor_lt (by positivity : (0 : ℕ) < (2 * B + 2) * k)).mpr
        push_cast
        nlinarith [(bounds j).2]⟩
    apply Set.mem_iUnion.mpr
    refine ⟨f, fun j => ⟨?_, ?_⟩⟩
    · have hf := Nat.floor_le (nonneg j)
      change -(B : ℝ) + (⌊(x j + B) * k⌋₊ : ℝ) / k ≤ x j
      apply (le_sub_iff_add_le.mp ?_)
      have hdiv : (⌊(x j + B) * k⌋₊ : ℝ) / k ≤ x j + B := (div_le_iff₀ kp).mpr hf
      linarith
    · have hf := (Nat.lt_floor_add_one ((x j + B) * k)).le
      change x j ≤ -(B : ℝ) + (⌊(x j + B) * k⌋₊ : ℝ) / k + 1 / k
      have hdiv : x j + B ≤ ((⌊(x j + B) * k⌋₊ : ℝ) + 1) / k := (le_div_iff₀ kp).mpr hf
      rw [add_div] at hdiv
      linarith
  · intro f
    have hd := (@yui_aux_0001 n E h_H001 h_H002 h_T002) (fun j => -(B : ℝ) + (f j : ℝ) / k) (1 / (k : ℝ)) (by positivity)
    simpa only [ENNReal.ofReal_div_of_pos kp, ENNReal.ofReal_one, ENNReal.ofReal_natCast] using hd
#check @checked
#print axioms checked
end YuiAuxiliary
