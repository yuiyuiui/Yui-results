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

theorem T020 (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T010 : dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)) :
    dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YF E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hD
  obtain ⟨x₀, hx₀⟩ := h_H001
  let j : ℝ → YEucl (n + 1) := fun t => YJoin x₀ t
  have hj : Isometry j := by
    apply Isometry.of_dist_eq
    intro t u
    rw [h_T003.1 n x₀ x₀ t u]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hcontent : ∀ (s δ : ℝ), 0 < s → 0 < δ →
      YContent s δ YI ≤ YContent s δ (YF E) := by
    intro s δ hs hδ
    unfold YContent
    refine le_iInf fun V => le_iInf fun hV => ?_
    let W : ℕ → Set ℝ := fun i => {t | t ∈ YI ∧ j t ∈ V i}
    have hd : ∀ i, Metric.ediam (W i) ≤ Metric.ediam (V i) := by
      intro i
      apply Metric.ediam_le_iff.mpr
      intro t ht u hu
      rw [← hj.edist_eq t u]
      exact Metric.edist_le_ediam_of_mem ht.2 hu.2
    have hW : YCover δ YI W := by
      constructor
      · intro t ht
        have hmem : j t ∈ YF E := ⟨x₀, hx₀, t, ht, rfl⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hmem)
        exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩
      · intro i
        exact (hd i).trans (hV.2 i)
    have hbound : YContent s δ YI ≤ YCost s W := by
      unfold YContent
      exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
    have hcost : YCost s W ≤ YCost s V :=
      ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hd i) hs.le
    exact hbound.trans hcost
  have hhaus : ∀ s : ℝ, 0 < s → YHaus s YI ≤ YHaus s (YF E) := by
    intro s hs
    unfold YHaus
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hcontent s δ hs hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hdim : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH (YF E) := by
    intro s hs hs1
    have htop : YHaus s (YF E) = ⊤ := by
      apply top_unique
      rw [← h_T010.2.2.2 s hs hs1]
      exact hhaus s hs
    exact (h_T002 (n + 1) (YF E)).2 s hs |>.2.2.2.2 htop
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hr1
    have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
    have hr1' : r < 1 := by exact_mod_cast hr1
    have hr1'' : (r : ℝ) < 1 := by exact_mod_cast hr1'
    have heq : ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞) :=
      ENNReal.ofReal_coe_nnreal
    rw [← heq]
    exact hdim (r : ℝ) hr0 hr1''
  · simp [hD]

#check @T020
#print axioms T020

end Translation
