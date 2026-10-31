import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEuclid n))  : yui_aux_type% "∀ (B : Set ℝ), Bornology.IsBounded B → ∀ (w : ℝ), 0 < w → ∃ J : Set ℝ, IsOpen J ∧ B ⊆ J ∧ volume J ≤ Metric.ediam B + ENNReal.ofReal w" := by
  intro B hB w hw
  classical
  by_cases he : B = ∅
  · subst B
    exact ⟨∅, isOpen_empty, Subset.rfl, by simp⟩
  · let J := Set.Ioo (sInf B - w / 2) (sSup B + w / 2)
    refine ⟨J, isOpen_Ioo, ?_, ?_⟩
    · intro x hx
      have hx' := hB.subset_Icc_sInf_sSup hx
      change sInf B - w / 2 < x ∧ x < sSup B + w / 2
      constructor <;> linarith [hx'.1, hx'.2]
    · have hlen : 0 ≤ sSup B - sInf B :=
        sub_nonneg.mpr (Real.sInf_le_sSup B hB.bddBelow hB.bddAbove)
      change volume (Set.Ioo _ _) ≤ _
      rw [Real.volume_Ioo, Real.ediam_eq hB]
      have heq : sSup B + w / 2 - (sInf B - w / 2) = (sSup B - sInf B) + w := by ring
      rw [heq, ENNReal.ofReal_add hlen hw.le]
#check @checked
#print axioms checked
end YuiAuxiliary
