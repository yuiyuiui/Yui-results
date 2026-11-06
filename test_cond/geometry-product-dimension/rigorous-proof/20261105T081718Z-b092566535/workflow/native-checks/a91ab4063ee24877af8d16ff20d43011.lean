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
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (a p : ℝ), 0 ≤ a → 0 ≤ p → (ENNReal.ofReal a) ^ p = ENNReal.ofReal (a ^ p)" := by
  intro a p ha hp
  exact ENNReal.ofReal_rpow_of_nonneg ha hp

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (hn : 1 ≤ n) (q r η : ℝ), 0 < q → 0 < r → 0 < η → ∀ x : YuiEucl n, ∃ B : Set (YuiEucl n), x ∈ B ∧ B.Nonempty ∧ 0 < Metric.ediam B ∧ Metric.ediam B ≤ ENNReal.ofReal r ∧ (Metric.ediam B) ^ q < ENNReal.ofReal η" := by
  intro hn q r η hq hr hη x
  letI : NeZero n := ⟨by omega⟩
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let ρ : ℝ := min r (η ^ q⁻¹) / 4
  have ha : 0 < η ^ q⁻¹ := Real.rpow_pos_of_pos hη _
  have hρ : 0 < ρ := div_pos (lt_min hr ha) (by norm_num)
  have hρr : 2 * ρ ≤ r := by dsimp [ρ]; linarith [min_le_left r (η ^ q⁻¹)]
  have hρa : 2 * ρ < η ^ q⁻¹ := by dsimp [ρ]; linarith [min_le_right r (η ^ q⁻¹)]
  have hd : Metric.ediam (Metric.closedBall x ρ) = ENNReal.ofReal (2 * ρ) := by
    calc
      _ = ENNReal.ofReal (Metric.diam (Metric.closedBall x ρ)) :=
        (ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top).symm
      _ = _ := by rw [Metric.diam_closedBall_eq x hρ.le]
  have hp : (2 * ρ) ^ q < η := by
    calc
      _ < (η ^ q⁻¹) ^ q := Real.rpow_lt_rpow (by positivity) hρa hq
      _ = η := Real.rpow_inv_rpow hη.le hq.ne'
  refine ⟨Metric.closedBall x ρ, Metric.mem_closedBall_self hρ.le,
    ⟨x, Metric.mem_closedBall_self hρ.le⟩, ?_, ?_, ?_⟩
  · rw [hd]; exact ENNReal.ofReal_pos.mpr (by positivity)
  · rw [hd]; exact ENNReal.ofReal_le_ofReal hρr
  · rw [hd, yui_aux_0001 n E h_H002 h_T002 h_T005 (2 * ρ) q (by positivity) hq.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hη).mpr hp

theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (q r ε : ℝ), dimH E < ENNReal.ofReal q → 0 < r → 0 < ε → 0 < q ∧ ∃ V : ℕ → Set (YuiEucl n), YuiCover r E V ∧ YuiCost q V < ENNReal.ofReal ε" := by
  intro q r ε hD hr hε
  have hq : 0 < q := ENNReal.ofReal_pos.mp ((h_T005.1.1).trans_lt hD)
  have hm : YuiMeasure q E = 0 := (h_T002.1 n E q hq).2.1 hD
  have hc : YuiContent q r E = 0 := by
    apply le_antisymm _ (zero_le _)
    calc
      _ ≤ YuiMeasure q E := le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      _ = 0 := hm
  have hi : (⨅ (V : ℕ → Set (YuiEucl n)) (_ : YuiCover r E V), YuiCost q V) <
      ENNReal.ofReal ε := by
    change YuiContent q r E < _
    rw [hc]
    exact ENNReal.ofReal_pos.mpr hε
  rcases (iInf_lt_iff.mp hi) with ⟨V, hV⟩
  rcases (iInf_lt_iff.mp hV) with ⟨hcov, hcost⟩
  exact ⟨hq, V, hcov, hcost⟩
#check @checked
#print axioms checked
end YuiAuxiliary
