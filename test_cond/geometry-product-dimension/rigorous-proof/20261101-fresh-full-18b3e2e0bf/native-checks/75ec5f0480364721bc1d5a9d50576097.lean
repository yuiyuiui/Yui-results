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

namespace Translation
set_option autoImplicit false

namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ M < δ ^ (s - 1)" := by
  intro s hs hs1 M
  have ht : Filter.Tendsto (fun δ : ℝ => δ ^ (s - 1)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hlarge : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), M < δ ^ (s - 1) := ht.eventually (Filter.eventually_gt_atTop M)
  have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  exact (hpos.and hlarge).exists

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤" := by
  intro s hs hs1
  by_contra hfinite
  obtain ⟨δ, hδ, hlarge⟩ := (@yui_aux_0001 n E h_T002 h_T005 h_T006 h_T018) s hs hs1 (GDMeasure s GDInterval).toReal
  have hstrict : GDMeasure s GDInterval < ENNReal.ofReal (δ ^ (s - 1)) := (ENNReal.lt_ofReal_iff_toReal_lt hfinite).2 hlarge
  have hbound : ENNReal.ofReal (δ ^ (s - 1)) ≤ GDMeasure s GDInterval := by
    exact (h_T006 s δ hs hs1 hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  exact (not_lt_of_ge hbound) hstrict

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH GDInterval" := by
  intro s hs hs1
  have hm : GDMeasure s (GDLine '' GDInterval) = ⊤ := by
    rw [(h_T018.2.2 GDInterval).2.2 s hs]
    exact (@yui_aux_0002 n E h_T002 h_T005 h_T006 h_T018) s hs hs1
  have hd : ENNReal.ofReal s ≤ dimH (GDLine '' GDInterval) := ((h_T002 1 (GDLine '' GDInterval)).2 s hs).2.2.2.2.2 hm
  rwa [(h_T018.2.2 GDInterval).1] at hd

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) :
    dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤) := by
  have hfinite : dimH GDInterval ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h_T005.2
  have hlowerReal : (1 : ℝ) ≤ (dimH GDInterval).toReal := by
    by_contra h
    have ht : (dimH GDInterval).toReal < 1 := lt_of_not_ge h
    have hn : 0 ≤ (dimH GDInterval).toReal := ENNReal.toReal_nonneg
    let s : ℝ := ((dimH GDInterval).toReal + 1) / 2
    have hs : 0 < s := by dsimp [s]; linarith
    have hs1 : s < 1 := by dsimp [s]; linarith
    have hsd : ENNReal.ofReal s ≤ dimH GDInterval := (@yui_aux_0003 n E h_T002 h_T005 h_T006 h_T018) s hs hs1
    have hsr : s ≤ (dimH GDInterval).toReal := (ENNReal.ofReal_le_iff_le_toReal hfinite).1 hsd
    dsimp [s] at hsr
    linarith
  have hlower : (1 : ℝ≥0∞) ≤ dimH GDInterval := by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_iff_le_toReal hfinite).2 hlowerReal
  exact ⟨le_antisymm h_T005.2 hlower, h_T005.1, h_T006, @yui_aux_0002 n E h_T002 h_T005 h_T006 h_T018⟩

#check @T007
#print axioms T007

end Translation
