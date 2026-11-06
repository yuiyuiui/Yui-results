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

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YuiEucl n))  : yui_aux_type% "∀ (S : Set ℝ), Bornology.IsBounded S → S.Nonempty → ∀ (ε : ℝ), 0 < ε → ∀ i : ℕ, S ⊆ Set.Ioo (sInf S - ε / 4 / 2 ^ i) (sSup S + ε / 4 / 2 ^ i) ∧ MeasureTheory.volume (Set.Ioo (sInf S - ε / 4 / 2 ^ i) (sSup S + ε / 4 / 2 ^ i)) = Metric.ediam S + ENNReal.ofReal (ε / 2 / 2 ^ i)" := by
  intro S hb hn ε hε i
  have hh : 0 < ε / 4 / (2 : ℝ) ^ i := by positivity
  have hend : 0 ≤ sSup S - sInf S := sub_nonneg.mpr (Real.sInf_le_sSup S hb.bddBelow hb.bddAbove)
  constructor
  · intro x hx
    have hx' := hb.subset_Icc_sInf_sSup hx
    constructor <;> linarith [hx'.1, hx'.2]
  · rw [Real.volume_Ioo, Real.ediam_eq hb, ← ENNReal.ofReal_add hend (by positivity : 0 ≤ ε / 2 / (2 : ℝ) ^ i)]
    congr 1
    ring
#check @checked
#print axioms checked
end YuiAuxiliary
