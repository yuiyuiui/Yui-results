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

theorem T001 (n : ℕ) (E : Set (YEucl n))  :
    ∀ (m : ℕ) (A : Set (YEucl m)) (s : ℝ), 0 < s → YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A := by
  intro m A s hs
  classical
  have hterm (B : Set (YEucl m)) :
      (⨆ _ : B.Nonempty, Metric.ediam B ^ s) = Metric.ediam B ^ s := by
    by_cases hB : B.Nonempty
    · simp [hB]
    · have hB0 : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      simp [hB0, ENNReal.zero_rpow_of_pos hs]
  let C : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (U : ℕ → Set (YEucl m)) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, Metric.ediam (U i) ^ s
  have hcontent (δ : ℝ) : YContent s δ A = C (ENNReal.ofReal δ) := by
    simp only [YContent, YCover, YCost, iInf_and, C]
  have hmono : Antitone C := by
    intro r t hrt
    dsimp [C]
    refine le_iInf fun U => le_iInf fun hA => le_iInf fun hU => ?_
    exact iInf_le_of_le U (iInf_le_of_le hA
      (iInf_le_of_le (fun i => (hU i).trans hrt) le_rfl))
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  simp_rw [hterm]
  change (⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A) =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r), C r
  simp_rw [hcontent]
  apply le_antisymm
  · refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact le_iSup_of_le (ENNReal.ofReal δ)
      (le_iSup_of_le (ENNReal.ofReal_pos.mpr hδ) le_rfl)
  · refine iSup_le fun r => iSup_le fun hr => ?_
    by_cases hrTop : r = ⊤
    · subst r
      exact (hmono (show ENNReal.ofReal (1 : ℝ) ≤ ⊤ from le_top)).trans
        (le_iSup_of_le (1 : ℝ) (le_iSup_of_le (show (0 : ℝ) < 1 from zero_lt_one) le_rfl))
    · have hpos : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrTop
      have hconvert : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrTop
      exact le_iSup_of_le r.toReal (le_iSup_of_le hpos (by rw [hconvert]))

#check @T001
#print axioms T001

end Translation
