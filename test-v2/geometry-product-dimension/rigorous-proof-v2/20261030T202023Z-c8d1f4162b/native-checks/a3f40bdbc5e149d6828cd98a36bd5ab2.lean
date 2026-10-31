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

theorem T004 (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) :
    (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ YI = YContent s δ (YLine '' YI)) ∧ (∀ s : ℝ, 0 < s → YHaus s YI = YHaus s (YLine '' YI)) ∧ dimH YI = dimH (YLine '' YI) := by
  have hi : Isometry YLine := h_T003.2.2.2.2.1
  have hs : Function.Surjective YLine := h_T003.2.2.2.2.2
  have hdpre : ∀ S : Set (YEucl 1), Metric.ediam (YLine ⁻¹' S) = Metric.ediam S := by
    intro S
    calc
      Metric.ediam (YLine ⁻¹' S) = Metric.ediam (YLine '' (YLine ⁻¹' S)) :=
        (hi.ediam_image _).symm
      _ = Metric.ediam S := congrArg Metric.ediam (Set.image_preimage_eq S hs)
  have hc : ∀ s δ : ℝ, YContent s δ YI = YContent s δ (YLine '' YI) := by
    intro s δ
    apply le_antisymm
    · unfold YContent
      refine le_iInf fun U => le_iInf fun hU => ?_
      have hV : YCover δ YI (fun i => YLine ⁻¹' U i) := by
        constructor
        · intro x hx
          have hmem := hU.1 (Set.mem_image_of_mem YLine hx)
          obtain ⟨i, hiU⟩ := Set.mem_iUnion.mp hmem
          exact Set.mem_iUnion.mpr ⟨i, hiU⟩
        · intro i
          rw [hdpre]
          exact hU.2 i
      refine iInf_le_of_le (fun i => YLine ⁻¹' U i) (iInf_le_of_le hV ?_)
      exact le_of_eq (by simp only [YCost, hdpre])
    · unfold YContent
      refine le_iInf fun U => le_iInf fun hU => ?_
      have hV : YCover δ (YLine '' YI) (fun i => YLine '' U i) := by
        constructor
        · rintro z ⟨x, hx, rfl⟩
          obtain ⟨i, hiU⟩ := Set.mem_iUnion.mp (hU.1 hx)
          exact Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem YLine hiU⟩
        · intro i
          rw [hi.ediam_image]
          exact hU.2 i
      refine iInf_le_of_le (fun i => YLine '' U i) (iInf_le_of_le hV ?_)
      exact le_of_eq (by simp only [YCost, hi.ediam_image])
  refine ⟨fun s δ _ _ => hc s δ, ?_, (hi.dimH_image YI).symm⟩
  intro s hs
  unfold YHaus
  simp only [hc]

#check @T004
#print axioms T004

end Translation
