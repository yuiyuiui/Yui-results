import Mathlib
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
namespace YuiBasis
noncomputable def Content {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ δ),
    ∑' i, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ s
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
noncomputable def appendCoord (n : ℕ) (p : Ambient n × ℝ) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
end YuiBasis

open YuiBasis
namespace YuiPlan
noncomputable def H {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  hausdorffMeasure s A
noncomputable def C {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  YuiBasis.Content s (ENNReal.ofReal δ) A
end YuiPlan
open YuiPlan

namespace Translation
set_option autoImplicit false

section
universe u
theorem T005 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i)) := by
  classical
  intro X inst V δ hδ hV
  have hproj (i : ℕ) :
      Metric.ediam (Prod.snd '' V i) ≤ Metric.ediam (V i) := by
    simpa using
      (LipschitzWith.prod_snd : LipschitzWith 1 (@Prod.snd X ℝ)).ediam_image_le (V i)
  have hbounded (i : ℕ) : Bornology.IsBounded (Prod.snd '' V i) :=
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hproj i).trans (hV i)))
  have hex (i : ℕ) : ∃ J : Set ℝ,
      Prod.snd '' V i ⊆ J ∧ IsClosed J ∧ volume J ≤ Metric.ediam (V i) := by
    by_cases hi : (Prod.snd '' V i).Nonempty
    · refine ⟨Set.Icc (sInf (Prod.snd '' V i)) (sSup (Prod.snd '' V i)),
        (hbounded i).subset_Icc_sInf_sSup, isClosed_Icc, ?_⟩
      rw [Real.volume_Icc, ← Real.ediam_eq (hbounded i)]
      exact hproj i
    · refine ⟨∅, ?_, isClosed_empty, ?_⟩
      · simp only [Set.not_nonempty_iff_eq_empty] at hi
        simp [hi]
      · simp
  choose J hJ using hex
  exact ⟨J, fun i => (hJ i).1, fun i => (hJ i).2.1, fun i => (hJ i).2.2⟩

end
#check @T005
#print axioms T005

end Translation
