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
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ (q δ ε : ℝ), dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε →\n  ∃ (r : ℝ) (W : ℕ → Set (GP.Space n)),\n    0 < q ∧ 0 < r ∧ r ≤ 1 ∧ Real.sqrt 2 * r ≤ δ ∧\n      GP.Cover E r W ∧ GP.cost q W < ENNReal.ofReal (ε/2)" := by
  intro q δ ε hdim hδ hε
  have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hdim)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let r : ℝ := min 1 (δ / Real.sqrt 2)
  have hr : 0 < r := lt_min zero_lt_one (div_pos hδ hs)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : Real.sqrt 2 * r ≤ δ := by
    have h := (le_div_iff₀ hs).mp (min_le_right 1 (δ / Real.sqrt 2))
    simpa only [mul_comm] using h
  have hH : GP.hausdorff q E = 0 := (h_T001.1 n E).2 q hq |>.2.1 hdim
  have hzero : GP.content q r E = 0 := by
    apply le_antisymm _ bot_le
    calc GP.content q r E ≤ GP.hausdorff q E :=
           le_iSup_of_le r (le_iSup_of_le hr le_rfl)
         _ = 0 := hH
  have hex : GP.content q r E < ENNReal.ofReal (ε/2) := by
    rw [hzero]
    exact ENNReal.ofReal_pos.mpr (half_pos hε)
  simp only [GP.content, iInf_lt_iff, exists_prop] at hex
  obtain ⟨W, hW, hc⟩ := hex
  exact ⟨r, W, hq, hr, hr1, hrδ, hW, hc⟩
#check @checked
#print axioms checked
end YuiAuxiliary
