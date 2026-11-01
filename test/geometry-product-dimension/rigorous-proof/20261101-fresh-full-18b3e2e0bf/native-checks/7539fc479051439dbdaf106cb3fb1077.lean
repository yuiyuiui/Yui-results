import Mathlib
open scoped ENNReal NNReal BigOperators
noncomputable section

abbrev GDVec (m : ℕ) := EuclideanSpace ℝ (Fin m)

def GDLine (t : ℝ) : GDVec 1 :=
  WithLp.toLp 2 (fun _ => t)

def GDInterval : Set ℝ := Set.Icc 0 1

def GDPoint {m : ℕ} (x : GDVec m) (t : ℝ) : GDVec (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)

def GDProduct {m : ℕ} (A : Set (GDVec m)) : Set (GDVec (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ GDInterval, z = GDPoint x t}

def GDCost {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (_ : A.Nonempty), (Metric.ediam A) ^ s

def GDContent {X : Type*} [PseudoEMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, GDCost s (U i)

def GDMeasure {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GDContent s δ A

def GDPositiveCover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (q r ε : ℝ) : Prop :=
  ∃ (K : Set ℕ) (U : K → Set X),
    A ⊆ ⋃ i, U i ∧
    (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧
    (∑' i, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal ε

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → 0 < ε → 0 < q ∧ ∃ W : ℕ → Set (GDVec n), E ⊆ ⋃ i, W i ∧ (∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal r) ∧ (∑' i, GDCost q (W i)) < ENNReal.ofReal (ε / 2)" := by
  intro q r ε hq hr hε
  have hqp : 0 < q := by
    by_contra h
    have : ENNReal.ofReal q = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h)
    rw [this] at hq
    exact (not_lt_of_ge bot_le hq)
  have hm : GDMeasure q E = 0 := ((h_T002 n E).2 q hqp).2.2.1 hq
  have hc : GDContent q r E = 0 := by
    apply le_antisymm _ bot_le
    calc
      GDContent q r E ≤ GDMeasure q E := le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      _ = 0 := hm
  have ht : GDContent q r E < ENNReal.ofReal (ε / 2) := by rw [hc]; positivity
  simp only [GDContent, iInf_lt_iff] at ht
  rcases ht with ⟨W, hW, hd, hs⟩
  exact ⟨hqp, W, hW, hd, hs⟩

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "1 ≤ n → ∀ (x : GDVec n) (d : ℝ), 0 < d → (Metric.ball x (d / 2)).Nonempty ∧ Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal d" := by
  intro hn x d hd
  letI : NeZero n := ⟨by omega⟩
  constructor
  · exact ⟨x, Metric.mem_ball_self (by positivity)⟩
  · have hb : Metric.ediam (Metric.ball x (d / 2)) ≠ ⊤ := Metric.isBounded_ball.ediam_ne_top
    calc
      Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal (Metric.diam (Metric.ball x (d / 2))) := (ENNReal.ofReal_toReal hb).symm
      _ = ENNReal.ofReal d := by rw [Metric.diam_ball_eq x (by positivity)]; congr 1; ring

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ q r a : ℝ, 0 < q → 0 < r → 0 < a → 0 < min r (a ^ (1 / q)) ∧ min r (a ^ (1 / q)) ≤ r ∧ (ENNReal.ofReal (min r (a ^ (1 / q)))) ^ q ≤ ENNReal.ofReal a" := by
  intro q r a hq hr ha
  have hp : 0 < a ^ (1 / q) := Real.rpow_pos_of_pos ha _
  have hd : 0 < min r (a ^ (1 / q)) := lt_min hr hp
  refine ⟨hd, min_le_left _ _, ?_⟩
  rw [ENNReal.ofReal_rpow_of_pos hd]
  apply ENNReal.ofReal_le_ofReal
  calc
    (min r (a ^ (1 / q))) ^ q ≤ (a ^ (1 / q)) ^ q := Real.rpow_le_rpow hd.le (min_le_right _ _) hq.le
    _ = a := by rw [one_div, Real.rpow_inv_rpow ha.le hq.ne']

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ ε : ℝ, 0 < ε → (∀ i : ℕ, 0 < ε / 4 / 2 / (2 : ℝ) ^ i) ∧ (∑' i : ℕ, ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ i)) = ENNReal.ofReal (ε / 4)" := by
  intro ε hε
  constructor
  · intro i; positivity
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' (ε / 4)), tsum_geometric_two']

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "1 ≤ n → ∀ (q r a : ℝ) (W : Set (GDVec n)), 0 < q → 0 < r → 0 < a → W.Nonempty → Metric.ediam W ≤ ENNReal.ofReal r → ∃ U : Set (GDVec n), W ⊆ U ∧ U.Nonempty ∧ 0 < Metric.ediam U ∧ Metric.ediam U ≤ ENNReal.ofReal r ∧ (Metric.ediam U) ^ q ≤ GDCost q W + ENNReal.ofReal a" := by
  intro hn q r a W hq hr ha hW hWr
  classical
  by_cases hz : Metric.ediam W = 0
  · obtain ⟨x, hx⟩ := hW
    let d : ℝ := min r (a ^ (1 / q))
    have hd := @yui_aux_0003 n E h_T002 h_T004 q r a hq hr ha
    have hb := @yui_aux_0002 n E h_T002 h_T004 hn x d hd.1
    refine ⟨Metric.ball x (d / 2), ?_, hb.1, ?_, ?_, ?_⟩
    · intro y hy
      have hyx : y = x := (Metric.ediam_eq_zero_iff.mp hz) hy hx
      subst y
      exact Metric.mem_ball_self (by dsimp [d]; positivity)
    · rw [hb.2]; exact ENNReal.ofReal_pos.mpr hd.1
    · rw [hb.2]; exact ENNReal.ofReal_le_ofReal hd.2.1
    · rw [hb.2]
      exact hd.2.2.trans (le_add_left le_rfl)
  · refine ⟨W, Set.Subset.rfl, hW, pos_iff_ne_zero.mpr hz, hWr, ?_⟩
    have hc : GDCost q W = (Metric.ediam W) ^ q := by simp [GDCost, hW]
    rw [hc]
    exact le_add_right le_rfl

theorem yui_aux_0006 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ a b c : ℝ≥0∞, a ≤ b → a + c ≤ b + c" := by
  intro a b c h
  exact add_le_add h le_rfl

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ (ε : ℝ) (K : Set ℕ) (a : ℕ → ℝ≥0∞) (b : K → ℝ≥0∞), 0 < ε → (∑' i, a i) < ENNReal.ofReal (ε / 2) → (∀ i, b i ≤ a i + ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ (i : ℕ))) → (∑' i, b i) < ENNReal.ofReal ε" := by
  intro ε K a b hε ha hb
  have hsum := (@yui_aux_0004 n E h_T002 h_T004 ε hε).2
  calc
    (∑' i, b i) ≤ ∑' i : K, (a i + ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ (i : ℕ))) := ENNReal.tsum_le_tsum hb
    _ ≤ ∑' i : ℕ, (a i + ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ i)) := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = (∑' i, a i) + ENNReal.ofReal (ε / 4) := by rw [ENNReal.tsum_add, hsum]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) := @yui_aux_0006 n E h_T002 h_T004 _ _ _ ha.le
    _ = ENNReal.ofReal (ε / 2 + ε / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
#check @checked
#print axioms checked
end YuiAuxiliary
