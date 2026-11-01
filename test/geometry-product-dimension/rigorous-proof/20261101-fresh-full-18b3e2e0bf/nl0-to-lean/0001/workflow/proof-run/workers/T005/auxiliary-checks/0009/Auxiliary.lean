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
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ N : ℕ, GDInterval ⊆ ⋃ i : Fin (N + 1), Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ))" := by
  intro N x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hN : (0 : ℝ) < N + 1 := by positivity
  apply Set.mem_iUnion.mpr
  by_cases he : x = 1
  · refine ⟨⟨N, Nat.lt_succ_self N⟩, ?_⟩
    simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
    subst x
    constructor
    · apply (div_le_iff₀ hN).mpr
      linarith
    · rw [div_self (ne_of_gt hN)]
  · have hlt : x < 1 := lt_of_le_of_ne hx1 he
    have hmul : 0 ≤ x * (N + 1 : ℝ) := mul_nonneg hx0 hN.le
    have hf : ⌊x * (N + 1 : ℝ)⌋₊ < N + 1 := by
      apply (Nat.floor_lt hmul).mpr
      push_cast
      nlinarith
    refine ⟨⟨⌊x * (N + 1 : ℝ)⌋₊, hf⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ hN).mpr
      exact Nat.floor_le hmul
    · apply (le_div_iff₀ hN).mpr
      exact (Nat.lt_floor_add_one _).le

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ (a : ℝ) (N : ℕ), (∑ i : Fin (N + 1), (Metric.ediam (Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ)))) ^ a) = ENNReal.ofReal ((N + 1 : ℝ) ^ (1 - a))" := by
  intro a N
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hd : ∀ i : Fin (N + 1), Metric.ediam (Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ))) = ENNReal.ofReal (1 / (N + 1 : ℝ)) := by
    intro i
    rw [Real.ediam_Icc]
    congr 1
    ring
  simp_rw [hd, ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hN)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (N + 1))]
  congr 1
  push_cast
  rw [Real.rpow_sub hN, Real.rpow_one, Real.div_rpow zero_le_one hN.le, Real.one_rpow]
  ring

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "Filter.Tendsto (fun N : ℕ => (N + 1 : ℝ)) Filter.atTop Filter.atTop" := by
  have ht : Filter.Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  simpa only [Nat.cast_add, Nat.cast_one] using ht

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ a : ℝ, 1 < a → Filter.Tendsto (fun N : ℕ => ENNReal.ofReal ((N + 1 : ℝ) ^ (1 - a))) Filter.atTop (nhds 0)" := by
  intro a ha
  have hr : Filter.Tendsto (fun N : ℕ => (N + 1 : ℝ) ^ (1 - a)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_sub] using (tendsto_rpow_neg_atTop (by linarith : 0 < a - 1)).comp (@yui_aux_0003 n E h_T002 h_T018)
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hr

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ (a : ℝ) (r : ℕ → ℝ≥0∞) (t : (N : ℕ) → Fin (N + 1) → Set (GDVec 1)), Filter.Tendsto r Filter.atTop (nhds 0) → (∀ᶠ N : ℕ in Filter.atTop, ∀ i, Metric.ediam (t N i) ≤ r N) → (∀ᶠ N : ℕ in Filter.atTop, GDLine '' GDInterval ⊆ ⋃ i, t N i) → MeasureTheory.Measure.hausdorffMeasure a (GDLine '' GDInterval) ≤ Filter.liminf (fun N => ∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) Filter.atTop" := by
  intro a r t hr ht hc
  exact MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum a (GDLine '' GDInterval) r hr t ht hc

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ a : ℝ, 1 < a → MeasureTheory.Measure.hausdorffMeasure a (GDLine '' GDInterval) = 0" := by
  intro a ha
  let t : (N : ℕ) → Fin (N + 1) → Set (GDVec 1) := fun N i => GDLine '' Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ))
  have hd : ∀ N (i : Fin (N + 1)), Metric.ediam (t N i) = ENNReal.ofReal (1 / (N + 1 : ℝ)) := by
    intro N i
    dsimp only [t]
    rw [h_T018.1.ediam_image, Real.ediam_Icc]
    congr 1
    ring
  have hrR : Filter.Tendsto (fun N : ℕ => 1 / (N + 1 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp (@yui_aux_0003 n E h_T002 h_T018)
  have hr : Filter.Tendsto (fun N : ℕ => ENNReal.ofReal (1 / (N + 1 : ℝ))) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hrR
  have ht : ∀ᶠ N : ℕ in Filter.atTop, ∀ i, Metric.ediam (t N i) ≤ ENNReal.ofReal (1 / (N + 1 : ℝ)) := Filter.Eventually.of_forall (fun N i => (hd N i).le)
  have hcover : ∀ᶠ N : ℕ in Filter.atTop, GDLine '' GDInterval ⊆ ⋃ i, t N i := by
    apply Filter.Eventually.of_forall
    intro N z hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp ((@yui_aux_0001 n E h_T002 h_T018 N) hx) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi, rfl⟩⟩
  have hcost : ∀ N, (∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) = ENNReal.ofReal ((N + 1 : ℝ) ^ (1 - a)) := by
    intro N
    dsimp only [t]
    simp_rw [h_T018.1.ediam_image]
    exact @yui_aux_0002 n E h_T002 h_T018 a N
  have hlim : Filter.Tendsto (fun N => ∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) Filter.atTop (nhds 0) := by
    simp_rw [hcost]
    exact @yui_aux_0004 n E h_T002 h_T018 a ha
  apply le_antisymm _ bot_le
  calc
    MeasureTheory.Measure.hausdorffMeasure a (GDLine '' GDInterval) ≤ Filter.liminf (fun N => ∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) Filter.atTop := @yui_aux_0005 n E h_T002 h_T018 a _ t hr ht hcover
    _ = 0 := hlim.liminf_eq
#check @checked
#print axioms checked
end YuiAuxiliary
