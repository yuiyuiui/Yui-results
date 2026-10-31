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

theorem T006 (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T005 : (∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, |x i| ≤ L) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤) := by
  classical
  have hc : YCritical E := h_T002 n E
  have hzero : n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0 := by
    intro hn
    subst n
    have hsub : E.Subsingleton := fun x hx y hy => Subsingleton.elim x y
    have huniv : E = Set.univ := by
      rcases h_H001 with ⟨x, hx⟩
      apply Set.eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y x] using hx
    have hhaus : ∀ s : ℝ, 0 < s → YHaus s E = 0 := by
      intro s hs
      apply le_antisymm _ bot_le
      refine iSup_le fun δ => iSup_le fun hδ => ?_
      let U : ℕ → Set (YEucl 0) := fun i => if i = 0 then E else ∅
      have hdiam : ∀ i, Metric.ediam (U i) = 0 := by
        intro i
        by_cases hi : i = 0
        · simp only [U, if_pos hi, Metric.ediam_subsingleton hsub]
        · simp only [U, if_neg hi, Metric.ediam_empty]
      have hcov : YCover δ E U := by
        constructor
        · intro x hx
          apply Set.mem_iUnion.mpr
          exact ⟨0, by simpa only [U, if_pos rfl] using hx⟩
        · intro i
          rw [hdiam i]
          exact bot_le
      change YContent s δ E ≤ 0
      calc
        YContent s δ E ≤ YCost s U := iInf_le_of_le U (iInf_le _ hcov)
        _ = 0 := by simp [YCost, hdiam, ENNReal.zero_rpow_of_pos hs]
    have hdim : dimH E = 0 := by
      apply le_antisymm _ hc.1
      by_contra h
      have hpos : 0 < dimH E := lt_of_not_ge h
      obtain ⟨a, ha0, ha, haD⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
      have hap : 0 < a := ENNReal.ofReal_pos.mp ha
      have hle : dimH E ≤ ENNReal.ofReal a :=
        (hc.2 a hap).2.2.2.1 (hhaus a hap)
      exact (not_lt_of_ge hle) haD
    exact ⟨huniv, hsub, hdim⟩
  have hbound : dimH E ≤ (n : ℝ≥0∞) := by
    by_cases hn : n = 0
    · simpa only [hn, Nat.cast_zero, (hzero hn).2.2] using
        (le_refl (0 : ℝ≥0∞))
    · have hpositive : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hvanish : ∀ a : ℝ, (n : ℝ) < a →
          MeasureTheory.Measure.hausdorffMeasure a E = 0 := by
        intro a ha
        have hf : (Module.finrank ℝ (YEucl n) : ℝ) < a := by
          simpa only [YEucl, finrank_euclideanSpace_fin] using ha
        have hm : (MeasureTheory.Measure.hausdorffMeasure a :
            MeasureTheory.Measure (YEucl n)) = 0 :=
          Real.hausdorffMeasure_of_finrank_lt (E := YEucl n) hf
        rw [hm]
        rfl
      have hexponent : ∀ a : ℝ, (n : ℝ) < a → dimH E ≤ ENNReal.ofReal a := by
        intro a ha
        have hap : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
        have hhaus : YHaus a E = 0 :=
          (hc.2 a hap).1.trans (hvanish a ha)
        exact (hc.2 a hap).2.2.2.1 hhaus
      by_contra h
      obtain ⟨a, ha0, hna, haD⟩ :=
        ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
      have hncast : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := by simp
      have hna' : (n : ℝ) < a := by
        rw [← hncast] at hna
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg n)).mp hna
      exact (not_lt_of_ge (hexponent a hna')) haD
  exact ⟨⟨hc.1, hbound, lt_of_le_of_lt hbound (by simp)⟩, hzero, h_T005.2⟩

#check @T006
#print axioms T006

end Translation
