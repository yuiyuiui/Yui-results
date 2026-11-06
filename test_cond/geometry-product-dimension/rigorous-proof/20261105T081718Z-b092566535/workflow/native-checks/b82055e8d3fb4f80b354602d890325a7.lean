import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ r : ℝ≥0∞, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r" := by
  intro r hr
  by_cases htop : r = ⊤
  · exact ⟨1, zero_lt_one, by simp [htop]⟩
  · exact ⟨r.toReal, ENNReal.toReal_pos (ne_of_gt hr) htop, ENNReal.ofReal_toReal_le⟩

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A := by
  intro X instMetric instMeas instBorel A a ha
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  unfold YuiMeasure YuiContent YuiCost
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    refine le_trans ?_ (le_iSup₂ (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ))
    refine le_iInf fun U => le_iInf fun hA => le_iInf fun hdiam => ?_
    exact iInf₂_le_of_le U ⟨hA, hdiam⟩ le_rfl
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨δ, hδ, hδr⟩ := yui_aux_0001 n E r hr
    refine le_trans ?_ (le_iSup₂ δ hδ)
    refine le_iInf fun U => le_iInf fun hU => ?_
    refine iInf₂_le_of_le U hU.1 ?_
    exact iInf_le_of_le (fun i => (hU.2 i).trans hδr) le_rfl

#check @T001
#print axioms T001

end Translation
