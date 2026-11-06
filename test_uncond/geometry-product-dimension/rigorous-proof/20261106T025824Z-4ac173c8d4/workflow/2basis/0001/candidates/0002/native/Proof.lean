import Mathlib
noncomputable section
open scoped ENNReal NNReal
open Set MeasureTheory MeasureTheory.Measure
namespace YuiGeometry
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def content {X : Type*} [MetricSpace X] (s : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
    ∑' i, Metric.ediam (U i) ^ s
def join (n : ℕ) (p : Space n × ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => p.1 i) p.2)
def cylinder (n : ℕ) (A : Set (Space n)) : Set (Space (n + 1)) :=
  join n '' (A ×ˢ Set.Icc (0 : ℝ) 1)
end YuiGeometry

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (s : ℝ) (A : Set X),
  hausdorffMeasure s A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
      ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
        ∑' i, ⨆ _ : (U i).Nonempty, Metric.ediam (U i) ^ s := by
  intro X _ _ _ s A
  exact hausdorffMeasure_apply s A
set_option Elab.async false in
theorem B002 : ∀ (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
  (dimH A < (d : ℝ≥0∞) → hausdorffMeasure (d : ℝ) A = 0) ∧
  ((d : ℝ≥0∞) < dimH A → hausdorffMeasure (d : ℝ) A = ⊤) ∧
  (hausdorffMeasure (d : ℝ) A = 0 → dimH A ≤ (d : ℝ≥0∞)) ∧
  (hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A d
  refine ⟨fun h => hausdorffMeasure_of_dimH_lt h, fun h => hausdorffMeasure_of_lt_dimH h, ?_, fun h => le_dimH_of_hausdorffMeasure_eq_top h⟩
  intro h
  exact dimH_le_of_hausdorffMeasure_ne_top (by rw [h]; exact ENNReal.zero_ne_top)
set_option Elab.async false in
theorem B003 : ∀ (X Y : Type*) [MetricSpace X] [MetricSpace Y],
  (∀ (A B : Set X), A ⊆ B → dimH A ≤ dimH B) ∧
  (∀ (f : X → Y), Isometry f → ∀ (A : Set X), dimH (f '' A) = dimH A) := by
  intro X Y _ _
  exact ⟨fun A B h => dimH_mono h, fun f h A => h.dimH_image A⟩
set_option Elab.async false in
theorem B004 : ∀ (n : ℕ) (A : Set (YuiGeometry.Space n)), dimH A ≤ (n : ℝ≥0∞) := by
  intro n A
  calc
    dimH A ≤ dimH (Set.univ : Set (YuiGeometry.Space n)) := dimH_mono (Set.subset_univ A)
    _ = (n : ℝ≥0∞) := by rw [Real.dimH_univ_eq_finrank]; simp [YuiGeometry.Space]
set_option Elab.async false in
theorem B005 : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  simpa only [segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)] using
    (Real.dimH_segment (E := ℝ) (x := 0) (y := 1) (by norm_num : (0 : ℝ) ≠ 1))
set_option Elab.async false in
theorem B006 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (I : Set X) (J : ℕ → Set X)
  (w : ℕ → ℝ≥0∞) (c : ℝ≥0∞),
  MeasurableSet I → (∀ i, MeasurableSet (J i)) →
  (∀ t ∈ I, c ≤ ∑' i, (J i).indicator (fun _ => w i) t) →
  c * μ I ≤ ∑' i, w i * μ (J i ∩ I) := by
  intro X _ μ I J w c hI hJ h
  classical
  calc
    c * μ I = ∫⁻ t, I.indicator (fun _ => c) t ∂μ :=
      (lintegral_indicator_const hI c).symm
    _ ≤ ∫⁻ t, ∑' i, (J i ∩ I).indicator (fun _ => w i) t ∂μ := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ I
      · simpa only [Set.indicator_apply, Set.mem_inter_iff, ht, and_true, if_true] using h t ht
      · simp [Set.indicator_apply, ht]
    _ = ∑' i, ∫⁻ t, (J i ∩ I).indicator (fun _ => w i) t ∂μ :=
      lintegral_tsum (fun i => (measurable_const.indicator ((hJ i).inter hI)).aemeasurable)
    _ = ∑' i, w i * μ (J i ∩ I) := by
      congr 1
      funext i
      exact lintegral_indicator_const ((hJ i).inter hI) (w i)
set_option Elab.async false in
theorem B007 : ∀ (a b : ℝ),
  volume (Set.Icc a b) = ENNReal.ofReal (b - a) ∧
  volume (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
  intro a b
  exact ⟨Real.volume_Icc, Real.volume_Ioo⟩
set_option Elab.async false in
theorem B008 : (∀ (X : Type*) [MetricSpace X] (A : Set X),
  Bornology.IsBounded A ↔ Metric.ediam A ≠ ⊤) ∧
 (∀ (B : Set ℝ), Bornology.IsBounded B →
  Metric.ediam B = ENNReal.ofReal (sSup B - sInf B) ∧
  ∀ x ∈ B, sInf B ≤ x ∧ x ≤ sSup B) := by
  constructor
  · intro X _ A
    exact Metric.isBounded_iff_ediam_ne_top
  · intro B hB
    exact ⟨Real.ediam_eq hB, fun x hx => hB.subset_Icc_sInf_sSup hx⟩
set_option Elab.async false in
theorem B009 : ∀ (X Y : Type*) [MetricSpace X] [MetricSpace Y],
  (∀ p q : X × Y, edist p q = max (edist p.1 q.1) (edist p.2 q.2)) ∧
  (∀ (A : Set X) (r : ℝ≥0∞),
    Metric.ediam A ≤ r ↔ ∀ x ∈ A, ∀ y ∈ A, edist x y ≤ r) := by
  intro X Y _ _
  exact ⟨fun p q => Prod.edist_eq p q, fun A r => Metric.ediam_le_iff⟩
set_option Elab.async false in
theorem B010 : ∀ (n : ℕ) (A : Set (YuiGeometry.Space n)),
  dimH (YuiGeometry.cylinder n A) = dimH (A ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro n A
  let e : (YuiGeometry.Space n × ℝ) ≃ₗ[ℝ] YuiGeometry.Space (n + 1) :=
    { toFun := YuiGeometry.join n
      invFun := fun z => (WithLp.toLp 2 (fun i : Fin n => z i.castSucc), z (Fin.last n))
      left_inv := by
        intro p
        apply Prod.ext
        · ext i
          simp [YuiGeometry.join]
        · simp [YuiGeometry.join]
      right_inv := by
        intro z
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [YuiGeometry.join]
        · simp [YuiGeometry.join]
      map_add' := by
        intro p q
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [YuiGeometry.join]
      map_smul' := by
        intro c p
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [YuiGeometry.join] }
  exact e.toContinuousLinearEquiv.dimH_image (A ×ˢ Set.Icc (0 : ℝ) 1)

end YuiBasis
