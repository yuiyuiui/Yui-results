import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "(∃ b : ℝ, 0 < b ∧ ∀ x ∈ E, ∀ i : Fin n, -b < x i ∧ x i < b) ∧ LipschitzWith ⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩ (WithLp.toLp 2 : (Fin n → ℝ) → GP.Space n)" := by
  constructor
  · obtain ⟨b, hb, hEb⟩ := h_H003.isBounded.subset_ball_lt 0 (0 : GP.Space n)
    refine ⟨b, hb, fun x hx i => ?_⟩
    have hi : dist (x i) 0 < b := by
      simpa using (PiLp.dist_apply_le x (0 : GP.Space n) i).trans_lt (hEb hx)
    simpa only [Real.dist_eq, sub_zero, abs_lt] using hi
  · have h := PiLp.lipschitzWith_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n => ℝ)
    have heq : ((Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) = (⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩ : ℝ≥0) := by
      apply NNReal.eq
      simp only [NNReal.coe_rpow, NNReal.coe_natCast, Fintype.card_fin]
      norm_num
      exact (Real.sqrt_eq_rpow _).symm
    rwa [heq] at h
#check @checked
#print axioms checked
end YuiAuxiliary
