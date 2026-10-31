import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (E : Set (YEuclid n))  :
    (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ := by
  classical
  have hEq : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (s : ℝ), 0 < s → yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A := by
    intro X _ _ _ A s hs
    classical
    have hcost (V : Set X) : (⨆ _ : V.Nonempty, Metric.ediam V ^ s) = Metric.ediam V ^ s := by
      by_cases hV : V.Nonempty
      · simp only [hV, iSup_pos]
      · have hVe : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hV
        simp [hVe, ENNReal.zero_rpow_of_pos hs]
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    simp_rw [hcost]
    let C : ℝ≥0∞ → ℝ≥0∞ := fun r =>
      ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
        ∑' i, (Metric.ediam (U i)) ^ s
    have hanti : Antitone C := by
      intro a b hab
      refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
      exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le (fun i => (hd i).trans hab) le_rfl))
    change (⨆ (δ : ℝ) (_ : 0 < δ), C (ENNReal.ofReal δ)) = ⨆ (r : ℝ≥0∞) (_ : 0 < r), C r
    apply le_antisymm
    · refine iSup_le fun δ => iSup_le fun hδ => ?_
      exact le_iSup_of_le (ENNReal.ofReal δ) (le_iSup_of_le (ENNReal.ofReal_pos.mpr hδ) le_rfl)
    · refine iSup_le fun r => iSup_le fun hr => ?_
      by_cases hrtop : r = ⊤
      · subst r
        exact (hanti (show ENNReal.ofReal (1 : ℝ) ≤ ⊤ from le_top)).trans
          (le_iSup_of_le (1 : ℝ) (le_iSup_of_le (by norm_num : (0 : ℝ) < 1) le_rfl))
      · have hrreal : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr) hrtop
        have hconv : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrtop
        calc
          C r = C (ENNReal.ofReal r.toReal) := congrArg C hconv.symm
          _ ≤ ⨆ (δ : ℝ) (_ : 0 < δ), C (ENNReal.ofReal δ) :=
            le_iSup_of_le r.toReal (le_iSup_of_le hrreal le_rfl)
  have hall : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X], yCritical X := by
    intro X _ _ _
    constructor
    · intro A
      exact zero_le _
    · intro A s hs
      have heq : yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A := hEq X A s hs
      let a : NNReal := ⟨s, le_of_lt hs⟩
      have hcoe : ENNReal.ofReal s = (a : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal (le_of_lt hs)
      refine ⟨heq, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [heq]
        exact hausdorffMeasure_of_dimH_lt (s := A) (d := a) (by rwa [← hcoe])
      · intro h
        rw [heq]
        exact hausdorffMeasure_of_lt_dimH (s := A) (d := a) (by rwa [← hcoe])
      · intro h
        have hz : MeasureTheory.Measure.hausdorffMeasure s A = 0 := heq.symm.trans h
        have hnt : MeasureTheory.Measure.hausdorffMeasure s A ≠ ⊤ := by
          rw [hz]
          exact zero_ne_top
        have hd : dimH A ≤ (a : ℝ≥0∞) := dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := a) hnt
        rwa [← hcoe] at hd
      · intro h
        have ht : MeasureTheory.Measure.hausdorffMeasure s A = ⊤ := heq.symm.trans h
        have hd : (a : ℝ≥0∞) ≤ dimH A := le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := a) ht
        rwa [← hcoe] at hd
  exact ⟨fun m => hall (YEuclid m), hall ℝ⟩

#check @T001
#print axioms T001

end Translation
