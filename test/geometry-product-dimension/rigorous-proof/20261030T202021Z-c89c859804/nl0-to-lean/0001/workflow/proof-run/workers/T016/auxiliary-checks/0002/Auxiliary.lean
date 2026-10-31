import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T014 : dimH GPI ≤ 1 ∧ ∀ a : ℝ, 1 < a → GPmass a GPI = 0) (h_T015 : ∀ (δ : ℝ) (U : ℕ → Set ℝ), 0 < δ →
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i)) : yui_aux_type% "∀ (s δ ρ : ℝ), 0 < s → s < 1 → 0 < δ → 0 ≤ ρ → ρ ≤ δ → δ ^ (s - 1) * ρ ≤ ρ ^ s" := by
  intro s δ ρ hs hs1 hδ hρ hρδ
  by_cases hzero : ρ = 0
  · subst ρ
    simp [Real.zero_rpow (ne_of_gt hs)]
  · have hpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hzero)
    calc
      δ ^ (s - 1) * ρ ≤ ρ ^ (s - 1) * ρ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hpos hρδ (by linarith)) hρ
      _ = ρ ^ s := by simpa using (Real.rpow_add hpos (s - 1) 1).symm
#check @checked
#print axioms checked
end YuiAuxiliary
