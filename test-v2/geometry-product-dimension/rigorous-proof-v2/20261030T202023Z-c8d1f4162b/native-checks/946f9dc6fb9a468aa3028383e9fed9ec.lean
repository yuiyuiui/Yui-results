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

theorem T016 (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ, (∀ i, IsOpen (J i)) ∧ (∀ i, YLast '' (V i) ⊆ J i) ∧ (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s))) ∧ (∀ t ∈ YI, YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t) := by
  classical
  have interval : ∀ (B : Set ℝ), Bornology.IsBounded B → ∀ η : ℝ, 0 < η →
      ∃ J : Set ℝ, IsOpen J ∧ B ⊆ J ∧
        MeasureTheory.volume J ≤ Metric.ediam B + ENNReal.ofReal η := by
    intro B hB η hη
    by_cases hne : B.Nonempty
    · refine ⟨Set.Ioo (sInf B - η / 2) (sSup B + η / 2), isOpen_Ioo, ?_, ?_⟩
      · intro t ht
        have hlo : sInf B ≤ t := csInf_le hB.bddBelow ht
        have hhi : t ≤ sSup B := le_csSup hB.bddAbove ht
        constructor <;> linarith
      · rw [Real.volume_Ioo]
        have heq : sSup B + η / 2 - (sInf B - η / 2) = (sSup B - sInf B) + η := by ring
        rw [heq, Real.ediam_eq hB]
        exact ENNReal.ofReal_add_le
    · refine ⟨∅, isOpen_empty, ?_, ?_⟩
      · simpa only [Set.not_nonempty_iff_eq_empty.mp hne] using (Set.Subset.refl (∅ : Set ℝ))
      · simp
  intro s δ hs hδ V hV ε hε
  have hbase : LipschitzWith 1 (@YBase n) := (h_T003.2.2.2.1 n).1
  have hlast : LipschitzWith 1 (@YLast n) := (h_T003.2.2.2.1 n).2
  have hprojBase (i : ℕ) : Metric.ediam (YBase '' V i) ≤ Metric.ediam (V i) := by
    simpa using hbase.ediam_image_le (V i)
  have hprojLast (i : ℕ) : Metric.ediam (YLast '' V i) ≤ Metric.ediam (V i) := by
    simpa using hlast.ediam_image_le (V i)
  have hfinite (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  let η : ℕ → ℝ := fun i =>
    ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s)
  have hη (i : ℕ) : 0 < η i := by
    dsimp [η]
    apply div_pos
    · exact mul_pos hε (zpow_pos (by norm_num) _)
    · have hr : 0 ≤ (Metric.ediam (V i)).toReal ^ s :=
        Real.rpow_nonneg ENNReal.toReal_nonneg s
      linarith
  have hex (i : ℕ) : ∃ J : Set ℝ, IsOpen J ∧ YLast '' V i ⊆ J ∧
      MeasureTheory.volume J ≤ Metric.ediam (V i) + ENNReal.ofReal (η i) := by
    have hb : Bornology.IsBounded (YLast '' V i) :=
      Metric.isBounded_iff_ediam_ne_top.mpr
        (ne_top_of_le_ne_top (hfinite i) (hprojLast i))
    obtain ⟨J, ho, hsub, hv⟩ := interval (YLast '' V i) hb (η i) (hη i)
    exact ⟨J, ho, hsub, hv.trans (add_le_add (hprojLast i) (le_refl (ENNReal.ofReal (η i))))⟩
  choose J hJo hJsub hJvol using hex
  refine ⟨J, hJo, hJsub, hJvol, ?_⟩
  intro t ht
  let U : ℕ → Set (YEucl n) := fun i => if t ∈ J i then YBase '' V i else ∅
  have hcover : YCover δ E U := by
    constructor
    · intro x hx
      have hjoin : YJoin x t ∈ YF E := ⟨x, hx, t, ht, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hjoin)
      have hlastmem : t ∈ YLast '' V i :=
        ⟨YJoin x t, hi, (h_T003.2.2.1 n x t).2⟩
      have hti : t ∈ J i := hJsub i hlastmem
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change x ∈ if t ∈ J i then YBase '' V i else ∅
      rw [if_pos hti]
      exact ⟨YJoin x t, hi, (h_T003.2.2.1 n x t).1⟩
    · intro i
      dsimp [U]
      split_ifs with hti
      · exact (hprojBase i).trans (hV.2 i)
      · simp
  have hcontent : YContent s δ E ≤ YCost s U :=
    iInf_le_of_le U (iInf_le_of_le hcover le_rfl)
  refine hcontent.trans ?_
  unfold YCost
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hti : t ∈ J i
  · simpa [U, hti] using ENNReal.rpow_le_rpow (hprojBase i) hs.le
  · simp [U, hti, ENNReal.zero_rpow_of_pos hs]

#check @T016
#print axioms T016

end Translation
