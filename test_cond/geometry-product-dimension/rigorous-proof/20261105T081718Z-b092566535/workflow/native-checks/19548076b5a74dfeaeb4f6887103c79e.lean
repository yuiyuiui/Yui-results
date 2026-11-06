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

namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T010 : ∀ s δ : ℝ, 0 < s → 0 < δ → ∀ V : ℕ → Set (YuiEucl (n + 1)), YuiCover δ (YuiCylinder E) V → ∀ ε : ℝ, 0 < ε → YuiContent s δ E ≤ YuiCost (s + 1) V + ENNReal.ofReal ε) : yui_aux_type% "∀ (a b : ℝ≥0∞), (∀ ε : ℝ, 0 < ε → a ≤ b + ENNReal.ofReal ε) → a ≤ b" := by
  intro a b h
  apply ENNReal.le_of_forall_pos_le_add (a := a) (b := b)
  intro ε hε hb
  have hεreal : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hcoe : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  simpa only [hcoe] using h (ε : ℝ) hεreal

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (E : Set (YuiEucl n)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T010 : ∀ s δ : ℝ, 0 < s → 0 < δ → ∀ V : ℕ → Set (YuiEucl (n + 1)), YuiCover δ (YuiCylinder E) V → ∀ ε : ℝ, 0 < ε → YuiContent s δ E ≤ YuiCost (s + 1) V + ENNReal.ofReal ε) :
    ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E) := by
  intro s δ hs hδ
  unfold YuiContent
  refine le_iInf fun V => le_iInf fun hV => ?_
  exact yui_aux_0001 n E h_T005 h_T010 (YuiContent s δ E) (YuiCost (s + 1) V)
    (fun ε hε => h_T010 s δ hs hδ V hV ε hε)

#check @T011
#print axioms T011

end Translation
