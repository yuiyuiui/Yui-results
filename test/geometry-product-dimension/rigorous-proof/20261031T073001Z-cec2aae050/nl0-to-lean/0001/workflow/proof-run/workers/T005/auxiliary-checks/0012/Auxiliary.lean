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
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ (q r : ℝ) (N : ℕ), 0 < r → (N : ℝ) ≤ 2 / r →\n  (N : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 2 * r) ^ (q+1) ≤\n    ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal (r^q)" := by
  intro q r N hr hN
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hNr : (N : ℝ) * r ≤ 2 := (le_div_iff₀ hr).mp hN
  have heq : (Real.sqrt 2 * r) ^ (q+1) = (Real.sqrt 2) ^ (q+1) * r^q * r := by
    rw [Real.mul_rpow hs.le hr.le, Real.rpow_add hr, Real.rpow_one]
    ring
  have hreal : (N : ℝ) * (Real.sqrt 2 * r) ^ (q+1) ≤
      (2 * (Real.sqrt 2) ^ (q+1)) * r^q := by
    rw [heq]
    calc (N : ℝ) * ((Real.sqrt 2)^(q+1) * r^q * r) =
        ((N : ℝ)*r) * ((Real.sqrt 2)^(q+1) * r^q) := by ring
         _ ≤ 2 * ((Real.sqrt 2)^(q+1) * r^q) :=
           mul_le_mul_of_nonneg_right hNr (by positivity)
         _ = _ := by ring
  have hcast : (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by simp
  rw [hcast, ENNReal.ofReal_rpow_of_pos (mul_pos hs hr),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal
#check @checked
#print axioms checked
end YuiAuxiliary
