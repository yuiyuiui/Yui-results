import Mathlib
open scoped ENNReal NNReal
noncomputable section
abbrev YEucl (m : ℕ) := EuclideanSpace ℝ (Fin m)
def YI : Set ℝ := Set.Icc 0 1
def YJoin {m : ℕ} (x : YEucl m) (t : ℝ) : YEucl (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YBase {m : ℕ} (z : YEucl (m + 1)) : YEucl m :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def YLast {m : ℕ} (z : YEucl (m + 1)) : ℝ := z (Fin.last m)
def YF {m : ℕ} (A : Set (YEucl m)) : Set (YEucl (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ YI, z = YJoin x t}
def YLine (t : ℝ) : YEucl 1 := WithLp.toLp 2 (fun _ => t)
def YCover {X : Type*} [PseudoEMetricSpace X]
    (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def YCost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s
def YContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YCover δ A U), YCost s U
def YHaus {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A
def YCritical {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) : Prop :=
  0 ≤ dimH A ∧ ∀ s : ℝ, 0 < s →
    YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → YHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → YHaus s A = ⊤) ∧
    (YHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (YHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)

namespace Translation
set_option autoImplicit false

theorem T009 (n : ℕ) (E : Set (YEucl n)) (h_T008 : ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)) :
    (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤) := by
  have hpoint : ∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ →
      ∀ r : ℝ≥0∞, r ≤ ENNReal.ofReal δ →
        (ENNReal.ofReal δ) ^ (s - 1) * r ≤ r ^ s := by
    intro s δ hs hs1 hδ r hr
    by_cases h0 : r = 0
    · simp [h0, ENNReal.zero_rpow_of_pos hs]
    have ht : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr
    have hp : (ENNReal.ofReal δ) ^ (s - 1) ≤ r ^ (s - 1) := by
      have he : s - 1 = -(1 - s) := by ring
      rw [he, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hr (by linarith))
    calc
      (ENNReal.ofReal δ) ^ (s - 1) * r ≤ r ^ (s - 1) * r := by gcongr
      _ = r ^ s := by
        simpa only [sub_add_cancel, ENNReal.rpow_one] using
          (ENNReal.rpow_add (s - 1) 1 h0 ht).symm
  have hcover : ∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ →
      ∀ U : ℕ → Set ℝ, YCover δ YI U →
        (ENNReal.ofReal δ) ^ (s - 1) ≤ YCost s U := by
    intro s δ hs hs1 hδ U hU
    calc
      (ENNReal.ofReal δ) ^ (s - 1) =
          (ENNReal.ofReal δ) ^ (s - 1) * 1 := (mul_one _).symm
      _ ≤ (ENNReal.ofReal δ) ^ (s - 1) * ∑' i, Metric.ediam (U i) := by
        gcongr
        exact h_T008 δ hδ U hU
      _ = ∑' i, (ENNReal.ofReal δ) ^ (s - 1) * Metric.ediam (U i) :=
        ENNReal.tsum_mul_left.symm
      _ ≤ YCost s U := ENNReal.tsum_le_tsum fun i =>
        hpoint s δ hs hs1 hδ (Metric.ediam (U i)) (hU.2 i)
  refine ⟨hcover, ?_⟩
  intro s hs hs1
  have hcontent : ∀ δ : ℝ, 0 < δ →
      (ENNReal.ofReal δ) ^ (s - 1) ≤ YContent s δ YI := by
    intro δ hδ
    unfold YContent
    exact le_iInf fun U => le_iInf fun hU => hcover s δ hs hs1 hδ U hU
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro M
  have hlim := tendsto_rpow_neg_nhdsGT_zero (show s - 1 < 0 by linarith)
  have he : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), (M : ℝ) ≤ δ ^ (s - 1) :=
    hlim.eventually (Filter.eventually_ge_atTop (M : ℝ))
  have hp : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hM, hδ⟩ := (he.and hp).exists
  have hbound : (M : ℝ≥0∞) ≤ (ENNReal.ofReal δ) ^ (s - 1) := by
    rw [ENNReal.ofReal_rpow_of_pos hδ]
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hM
  exact hbound.trans ((hcontent δ hδ).trans
    (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)))

#check @T009
#print axioms T009

end Translation
