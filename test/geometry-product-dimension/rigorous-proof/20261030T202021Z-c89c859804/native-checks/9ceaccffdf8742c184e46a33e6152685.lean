import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

namespace Translation
set_option autoImplicit false

theorem T002 (n : ℕ) (E : Set (GPEucl n))  :
    (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) := by
  classical
  have comparison : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
      (A : Set X) (s : ℝ), 0 < s →
      GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A := by
    intro X _ _ _ A s hs
    have cost_eq (U : ℕ → Set X) :
        (∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ s) = GPcost s U := by
      unfold GPcost
      apply tsum_congr
      intro i
      by_cases hi : (U i).Nonempty
      · simp only [hi, iSup_pos]
      · have hempty : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
        simp [hempty, ENNReal.zero_rpow_of_pos hs]
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    simp_rw [cost_eq]
    apply le_antisymm
    · unfold GPmass
      refine iSup₂_le fun δ hδ => ?_
      have hpos : (0 : ENNReal) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
      calc
        GPcontent s δ A =
            ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
              (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), GPcost s U := by
          simp only [GPcontent, GPcover, iInf_and]
        _ ≤ _ := le_iSup₂ (ENNReal.ofReal δ) hpos
    · refine iSup₂_le fun r hr => ?_
      have radius : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r := by
        by_cases hfin : r = ⊤
        · exact ⟨1, zero_lt_one, by simp [hfin]⟩
        · have hconvert : 0 < r.toReal ∧ ENNReal.ofReal r.toReal = r :=
            ⟨ENNReal.toReal_pos hr.ne' hfin, ENNReal.ofReal_toReal hfin⟩
          exact ⟨r.toReal, hconvert.1, hconvert.2.le⟩
      obtain ⟨δ, hδ, hδr⟩ := radius
      refine le_trans ?_ (le_iSup₂ (f := fun δ : ℝ => ⨆ _ : 0 < δ, GPcontent s δ A) δ hδ)
      unfold GPcontent
      refine le_iInf fun U => le_iInf fun hU => ?_
      exact iInf₂_le_of_le U hU.1
        (iInf_le_of_le (fun i => (hU.2 i).trans hδr) le_rfl)
  constructor
  · intro k A s hs
    exact comparison (GPEucl k) A s hs
  · intro A s hs
    exact comparison ℝ A s hs

#check @T002
#print axioms T002

end Translation
