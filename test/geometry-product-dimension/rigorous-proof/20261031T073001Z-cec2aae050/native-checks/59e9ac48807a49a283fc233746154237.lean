import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

namespace Translation
set_option autoImplicit false

theorem T004 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T003 : dimH GP.unitInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤)) :
    n = 0 → dimH (GP.cylinder E) ≤ dimH E + 1 := by
  intro hn
  subst n
  rcases h_T002.2.2.2.1 rfl with ⟨hE, _, hD⟩
  let f : ℝ → GP.Space (0 + 1) := fun t => GP.join (0 : GP.Space 0) t
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    have hs : dist (f t) (f u) ^ 2 = dist t u ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq]
      simp [f, GP.join, Fin.snoc_zero]
    nlinarith [dist_nonneg (x := f t) (y := f u), dist_nonneg (x := t) (y := u)]
  have himage : f '' GP.unitInterval = GP.cylinder E := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor
      · rw [hE]
        trivial
      · simpa [f, GP.vertical, GP.join, Fin.snoc_zero] using ht
    · intro hz
      refine ⟨GP.vertical z, hz.2, ?_⟩
      apply PiLp.ext
      intro i
      fin_cases i
      rfl
  have hbound : ∀ a : ℝ, 1 < a → dimH (GP.cylinder E) ≤ ENNReal.ofReal a := by
    intro a ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have hmeasure :
        MeasureTheory.Measure.hausdorffMeasure a (GP.cylinder E) =
          MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval := by
      rw [← himage]
      exact hf.hausdorffMeasure_image (Or.inl ha0.le) GP.unitInterval
    have hz : GP.hausdorff a (GP.cylinder E) = 0 := calc
      GP.hausdorff a (GP.cylinder E) =
          MeasureTheory.Measure.hausdorffMeasure a (GP.cylinder E) :=
        ((h_T001.1 1 (GP.cylinder E)).2 a ha0).1
      _ = MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval := hmeasure
      _ = GP.hausdorff a GP.unitInterval := (h_T001.2 GP.unitInterval a ha0).symm
      _ = 0 := h_T003.2.1 a ha
    exact ((h_T001.1 1 (GP.cylinder E)).2 a ha0).2.2.2.1 hz
  rw [hD, zero_add (1 : ℝ≥0∞)]
  have hd : dimH (GP.cylinder E) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound 2 (by norm_num))
  apply (ENNReal.toReal_le_toReal hd (by simp)).mp
  simp only [ENNReal.toReal_one]
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  exact ENNReal.toReal_le_of_le_ofReal (le_trans zero_le_one ha.le) (hbound a ha)

#check @T004
#print axioms T004

end Translation
