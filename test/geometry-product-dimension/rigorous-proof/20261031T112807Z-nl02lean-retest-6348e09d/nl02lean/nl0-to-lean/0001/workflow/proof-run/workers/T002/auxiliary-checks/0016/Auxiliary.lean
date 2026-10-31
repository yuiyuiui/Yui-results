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
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) : yui_aux_type% "n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0" := by
  classical
  intro hn
  subst n
  obtain ⟨x, hx⟩ := h_H002
  have he : E = {x} := by
    ext y
    constructor
    · intro _; exact Set.mem_singleton_iff.mpr (Subsingleton.elim y x)
    · intro hy; simpa only [Set.mem_singleton_iff.mp hy] using hx
  have hu : E = Set.univ := by
    ext y
    simp only [he, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim y x
  have hy : ∀ s : ℝ, 0 < s → yHaus s E = 0 := by
    intro s hs
    unfold yHaus
    refine le_antisymm (iSup₂_le fun δ hδ => ?_) bot_le
    let U : ℕ → Set (YEuclid 0) := fun _ => {x}
    have hc : E ⊆ ⋃ i, U i := by
      rw [he]
      exact Set.subset_iUnion U 0
    have hd : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ := by
      intro i; simp only [U, Metric.ediam_singleton, zero_le]
    have hcost : (∑' i, Metric.ediam (U i) ^ s) = 0 := by
      simp only [U, Metric.ediam_singleton, ENNReal.zero_rpow_of_pos hs, tsum_zero]
    have hle : yContent s δ E ≤ ∑' i, Metric.ediam (U i) ^ s := by
      unfold yContent
      exact iInf_le_of_le U (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))
    exact hle.trans_eq hcost
  have hdz : dimH E = 0 := by
    apply le_antisymm _ ((h_T001.1 0).1 E)
    by_contra! hpos
    obtain ⟨a, ha, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
    have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hd := ((h_T001.1 0).2 E a har).2.2.2.1 (hy a har)
    rw [ENNReal.ofReal_coe_nnreal] at hd
    exact (not_lt_of_ge hd) had
  exact ⟨hu, ⟨x, he⟩, hdz⟩
#check @checked
#print axioms checked
end YuiAuxiliary
