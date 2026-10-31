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
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ (q r ε : ℝ), 0 < q → 0 < r → 0 < ε →\n  ∃ b : ℕ → ℝ, (∀ i, 0 < b i ∧ b i ≤ r ∧ (b i) ^ q ≤ ε / 8 * ((1:ℝ)/2)^i) ∧\n    (∑' i, ENNReal.ofReal (ε / 8 * ((1:ℝ)/2)^i)) = ENNReal.ofReal (ε / 4)" := by
  intro q r ε hq hr hε
  let a : ℕ → ℝ := fun i => ε / 8 * ((1:ℝ)/2)^i
  let b : ℕ → ℝ := fun i => min (r/2) ((a i) ^ q⁻¹)
  have ha : ∀ i, 0 < a i := fun i => by dsimp [a]; positivity
  refine ⟨b, ?_, ?_⟩
  · intro i
    have hb : 0 < b i := lt_min (half_pos hr) (Real.rpow_pos_of_pos (ha i) _)
    refine ⟨hb, (min_le_left _ _).trans (by linarith), ?_⟩
    calc (b i) ^ q ≤ ((a i) ^ q⁻¹) ^ q :=
          Real.rpow_le_rpow hb.le (min_le_right _ _) hq.le
         _ = a i := Real.rpow_inv_rpow (ha i).le hq.ne'
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (ha i).le)
      (summable_geometric_two.mul_left (ε/8)), tsum_mul_left, tsum_geometric_two]
    congr 1
    ring
#check @checked
#print axioms checked
end YuiAuxiliary
