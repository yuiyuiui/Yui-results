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

theorem T013 (n : ℕ) (E : Set (YEuclid n)) (h_H002 : E.Nonempty) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T005 : dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤)) :
    dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (yProd E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hD
  obtain ⟨x, hx⟩ := h_H002
  have hcoords (t : ℝ) : yHoriz (yJoin x t) = x ∧ yVert (yJoin x t) = t := by
    constructor
    · ext i
      simp [yHoriz, yJoin]
    · simp [yVert, yJoin]
  have hf : Isometry (fun t : ℝ => yJoin x t) := by
    apply Isometry.of_dist_eq
    intro t u
    have hsq : dist (yJoin x t) (yJoin x u) ^ 2 = dist t u ^ 2 := by
      rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_castSucc]
      simp [yJoin]
    nlinarith [dist_nonneg (x := yJoin x t) (y := yJoin x u), dist_nonneg (x := t) (y := u)]
  have hmem : ∀ t ∈ yI, yJoin x t ∈ yProd E := by
    intro t ht
    change yHoriz (yJoin x t) ∈ E ∧ yVert (yJoin x t) ∈ yI
    rw [(hcoords t).1, (hcoords t).2]
    exact ⟨hx, ht⟩
  have hcover : ∀ (f : ℝ → YEuclid (n+1)), Isometry f → (∀ t ∈ yI, f t ∈ yProd E) → ∀ s : ℝ, 0 < s → yHaus s yI ≤ yHaus s (yProd E) := by
    intro f hf hmem s hs
    have hdiam (V : Set (YEuclid (n+1))) : Metric.ediam (f ⁻¹' V) ≤ Metric.ediam V := by
      apply Metric.ediam_le_iff.mpr
      intro t ht u hu
      rw [← hf.edist_eq t u]
      exact Metric.edist_le_ediam_of_mem ht hu
    have hcontent (δ : ℝ) : yContent s δ yI ≤ yContent s δ (yProd E) := by
      unfold yContent
      refine le_iInf fun V => le_iInf fun hcov => le_iInf fun hδ => ?_
      let W : ℕ → Set ℝ := fun i => f ⁻¹' V i
      have hWcov : yI ⊆ ⋃ i, W i := by
        intro t ht
        rcases Set.mem_iUnion.mp (hcov (hmem t ht)) with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      have hWδ : ∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal δ := fun i => (hdiam (V i)).trans (hδ i)
      have hbound : yContent s δ yI ≤ ∑' i, (Metric.ediam (W i)) ^ s := by
        unfold yContent
        exact iInf_le_of_le W (iInf_le_of_le hWcov (iInf_le_of_le hWδ le_rfl))
      exact hbound.trans (ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hdiam (V i)) hs.le)
    unfold yHaus
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hcontent δ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hbound : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH (yProd E) := by
    intro s hs hs1
    have hle := hcover (fun t => yJoin x t) hf hmem s hs
    rw [h_T005.2.2 s hs hs1] at hle
    have htop : yHaus s (yProd E) = ⊤ := top_unique hle
    exact ((h_T001.1 (n+1)).2 (yProd E) s hs).2.2.2.2 htop
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hr1
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hrlt : (r : ℝ) < 1 := by exact_mod_cast hr1
    simpa only [ENNReal.ofReal_coe_nnreal] using hbound (r : ℝ) hrpos hrlt
  · simp [hD]

#check @T013
#print axioms T013

end Translation
