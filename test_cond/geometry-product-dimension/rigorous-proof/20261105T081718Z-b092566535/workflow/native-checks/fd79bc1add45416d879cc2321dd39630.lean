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

namespace Local_T012
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) : yui_aux_type% "∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E → ENNReal.ofReal (s + 1) ≤ dimH (YuiCylinder E)" := by
  intro s hs hsD
  have hE : YuiMeasure s E = ⊤ := (h_T002.1 n E s hs).2.2.1 hsD
  have hle : YuiMeasure s E ≤ YuiMeasure (s + 1) (YuiCylinder E) := by
    unfold YuiMeasure
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (h_T011 s δ hs hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hF : YuiMeasure (s + 1) (YuiCylinder E) = ⊤ := top_unique (hE ▸ hle)
  exact (h_T002.1 (n + 1) (YuiCylinder E) (s + 1) (by linarith)).2.2.2.2 hF

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < (dimH E).toReal → ENNReal.ofReal s < dimH E" := by
  intro s hs hsD
  have hd : 0 < (dimH E).toReal := hs.trans hsD
  have hc : ENNReal.ofReal s < ENNReal.ofReal (dimH E).toReal :=
    ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hsD, hd⟩
  exact hc.trans_eq (ENNReal.ofReal_toReal h_T005.1.2.2.ne)

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) : yui_aux_type% "0 < dimH E → (∀ j : ℕ, 2 ≤ j → 0 < (dimH E).toReal * (1 - 1 / (j : ℝ)) ∧ ENNReal.ofReal ((dimH E).toReal * (1 - 1 / (j : ℝ))) < dimH E) ∧ Filter.Tendsto (fun j : ℕ => ENNReal.ofReal ((dimH E).toReal * (1 - 1 / (j : ℝ)) + 1)) Filter.atTop (nhds (dimH E + 1))" := by
  intro hD
  have hfin : dimH E ≠ ⊤ := h_T005.1.2.2.ne
  have hd : 0 < (dimH E).toReal := ENNReal.toReal_pos hD.ne' hfin
  have hconv : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add hd.le (by norm_num), ENNReal.ofReal_toReal hfin, ENNReal.ofReal_one]
  constructor
  · intro j hj
    have hj' : (1 : ℝ) < (j : ℝ) := by exact_mod_cast (show 1 < j by omega)
    have hjpos : (0 : ℝ) < j := by linarith
    have hi : 0 < 1 / (j : ℝ) := div_pos (by norm_num) hjpos
    have hi' : 1 / (j : ℝ) < 1 := (div_lt_iff₀ hjpos).2 (by linarith)
    have hs : 0 < (dimH E).toReal * (1 - 1 / (j : ℝ)) := mul_pos hd (by linarith)
    refine ⟨hs, @yui_aux_0002 n E h_T002 h_T005 h_T011 _ hs ?_⟩
    nlinarith [mul_pos hd hi]
  · have ht : Filter.Tendsto (fun j : ℕ => (dimH E).toReal * (1 - 1 / (j : ℝ)) + 1) Filter.atTop (nhds ((dimH E).toReal + 1)) := by
      convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))).add tendsto_const_nhds using 1 <;> simp
    rw [← hconv]
    exact ENNReal.tendsto_ofReal ht

end Local_T012
open Local_T012 in
theorem T012 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (YuiCylinder E) := by
  intro hD
  obtain ⟨hseq, hlim⟩ := @yui_aux_0003 n E h_T002 h_T005 h_T011 hD
  apply le_of_tendsto hlim
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro j hj
  obtain ⟨hs, hsD⟩ := hseq j hj
  exact @yui_aux_0001 n E h_T002 h_T005 h_T011
    ((dimH E).toReal * (1 - 1 / (j : ℝ))) hs hsD

#check @T012
#print axioms T012

end Translation
