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

theorem T010 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T004 : (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ YI = YContent s δ (YLine '' YI)) ∧ (∀ s : ℝ, 0 < s → YHaus s YI = YHaus s (YLine '' YI)) ∧ dimH YI = dimH (YLine '' YI)) (h_T007 : ∀ a : ℝ, 1 < a → YHaus a YI = 0) (h_T008 : ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)) (h_T009 : (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)) :
    dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤) := by
  have hupper : ∀ a : ℝ, 1 < a → dimH YI ≤ ENNReal.ofReal a := by
    intro a ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have hz : YHaus a (YLine '' YI) = 0 :=
      (h_T004.2.1 a ha0).symm.trans (h_T007 a ha)
    rw [h_T004.2.2]
    exact ((h_T002 1 (YLine '' YI)).2 a ha0).2.2.2.1 hz
  have hlower : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH YI := by
    intro s hs hs1
    have ht : YHaus s (YLine '' YI) = ⊤ :=
      (h_T004.2.1 s hs).symm.trans (h_T009.2 s hs hs1)
    rw [h_T004.2.2]
    exact ((h_T002 1 (YLine '' YI)).2 s hs).2.2.2.2 ht
  have hd : dimH YI ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper 2 (by norm_num))
  have hrealupper : (dimH YI).toReal ≤ 1 := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    have ha0 : 0 ≤ a := le_of_lt (lt_trans zero_lt_one ha)
    have hc : (dimH YI).toReal ≤ (ENNReal.ofReal a).toReal :=
      (ENNReal.toReal_le_toReal (a := dimH YI) (b := ENNReal.ofReal a)
        hd ENNReal.ofReal_ne_top).2 (hupper a ha)
    simpa only [ENNReal.toReal_ofReal ha0] using hc
  have hreallower : (1 : ℝ) ≤ (dimH YI).toReal := by
    apply le_of_forall_lt_imp_le_of_dense
    intro s hs1
    by_cases hs : 0 < s
    · have hc : (ENNReal.ofReal s).toReal ≤ (dimH YI).toReal :=
        (ENNReal.toReal_le_toReal (a := ENNReal.ofReal s) (b := dimH YI)
          ENNReal.ofReal_ne_top hd).2 (hlower s hs hs1)
      simpa only [ENNReal.toReal_ofReal hs.le] using hc
    · exact le_trans (le_of_not_gt hs) ENNReal.toReal_nonneg
  have hdim : dimH YI = 1 := by
    calc
      dimH YI = ENNReal.ofReal (dimH YI).toReal := (ENNReal.ofReal_toReal hd).symm
      _ = 1 := by rw [le_antisymm hrealupper hreallower]; norm_num
  refine ⟨hdim, h_T007, ?_, h_T009.2⟩
  intro s δ hs hs1 hδ U hU
  exact ⟨h_T008 δ hδ U hU, h_T009.1 s δ hs hs1 hδ U hU⟩

#check @T010
#print axioms T010

end Translation
