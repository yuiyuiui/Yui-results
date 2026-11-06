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
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "ENNReal.ofReal ((dimH E).toReal) = dimH E ∧ ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1" := by
  have hfin : dimH E ≠ ⊤ := ne_of_lt h_T005.1.2.2
  have hD : ENNReal.ofReal ((dimH E).toReal) = dimH E := ENNReal.ofReal_toReal hfin
  refine ⟨hD, ?_⟩
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1), hD]
  simp

theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ δ : ℝ, 0 < δ → YuiContent (q + 1) δ (YuiCylinder E) = 0" := by
  intro hn q hq δ hδ
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  let r : ℝ := min 1 (δ / Real.sqrt 2)
  have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hs)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrs : Real.sqrt 2 * r ≤ δ := by
    have h : r ≤ δ / Real.sqrt 2 := min_le_right _ _
    have := (le_div_iff₀ hs).1 h
    nlinarith
  let C : ℝ := 2 * (Real.sqrt 2) ^ (q + 1)
  have hC : 0 < C := mul_pos (by norm_num) (Real.rpow_pos_of_pos hs _)
  have hbound : ∀ j : ℕ,
      YuiContent (q + 1) δ (YuiCylinder E) ≤
        ENNReal.ofReal (C * (1 / ((j : ℝ) + 1))) := by
    intro j
    obtain ⟨W, hW, hcost⟩ := h_T008 hn q hq r (1 / ((j : ℝ) + 1)) hr hr1 (by positivity)
    have hcover : YuiCover δ (YuiCylinder E) W := by
      refine ⟨hW.1, fun i => (hW.2 i).trans ?_⟩
      exact ENNReal.ofReal_le_ofReal hrs
    exact (iInf_le_of_le W (iInf_le_of_le hcover le_rfl)).trans hcost.le
  have hlimR : Filter.Tendsto (fun j : ℕ => C * (1 / ((j : ℝ) + 1)))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := C)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (C * (1 / ((j : ℝ) + 1))))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlimR
  exact le_antisymm (ge_of_tendsto' hlim hbound) (zero_le _)
#check @checked
#print axioms checked
end YuiAuxiliary
