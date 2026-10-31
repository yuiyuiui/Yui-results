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
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i)) : yui_aux_type% "∀ (s : ℝ), s < 1 → (∀ δ : ℝ, 0 < δ → ENNReal.ofReal (δ ^ (s - 1)) ≤ GPmass s GPI) → GPmass s GPI = ⊤" := by
  intro s hs hbound
  have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ (s - 1))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (⊤ : ENNReal)) :=
    ENNReal.tendsto_ofReal_atTop.comp (tendsto_rpow_neg_nhdsGT_zero (by linarith : s - 1 < 0))
  apply top_unique
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hbound δ hδ
#check @checked
#print axioms checked
end YuiAuxiliary
