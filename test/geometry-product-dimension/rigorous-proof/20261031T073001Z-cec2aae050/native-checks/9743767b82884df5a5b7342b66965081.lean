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

theorem T011 (n : ℕ) (E : Set (GP.Space n)) (h_H002 : E.Nonempty) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T003 : dimH GP.unitInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤)) :
    dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (GP.cylinder E) ∧
  (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hzero
  obtain ⟨x, hx⟩ := h_H002
  have hf : Isometry (GP.join x) := by
    apply Isometry.of_dist_eq
    intro t u
    rw [EuclideanSpace.dist_eq]
    simp [GP.join, Fin.sum_univ_castSucc, Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hmem : ∀ t ∈ GP.unitInterval, GP.join x t ∈ GP.cylinder E := by
    intro t ht
    constructor
    · simpa [GP.horizontal, GP.join] using hx
    · simpa [GP.vertical, GP.join] using ht
  have hmono : ∀ (s : ℝ), 0 < s →
      GP.hausdorff s GP.unitInterval ≤ GP.hausdorff s (GP.cylinder E) := by
    intro s hs
    have hc : ∀ δ : ℝ, GP.content s δ GP.unitInterval ≤ GP.content s δ (GP.cylinder E) := by
      intro δ
      unfold GP.content
      refine le_iInf fun V => le_iInf fun hV => ?_
      let W : ℕ → Set ℝ := fun i => GP.join x ⁻¹' V i
      have hd : ∀ i, Metric.ediam (W i) ≤ Metric.ediam (V i) := by
        intro i
        apply Metric.ediam_le
        intro t ht u hu
        rw [← hf.edist_eq t u]
        exact Metric.edist_le_ediam_of_mem ht hu
      have hW : GP.Cover GP.unitInterval δ W := by
        constructor
        · intro t ht
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 (hmem t ht))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        · intro i
          exact (hd i).trans (hV.2 i)
      have hcost : GP.cost s W ≤ GP.cost s V := by
        unfold GP.cost
        apply ENNReal.tsum_le_tsum
        intro i
        refine iSup_le fun hne => ?_
        have hneV : (V i).Nonempty := by
          obtain ⟨t, ht⟩ := hne
          exact ⟨GP.join x t, ht⟩
        exact (ENNReal.rpow_le_rpow (hd i) hs.le).trans (le_iSup_of_le hneV le_rfl)
      have hleft : GP.content s δ GP.unitInterval ≤ GP.cost s W := by
        unfold GP.content
        exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
      exact hleft.trans hcost
    unfold GP.hausdorff
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hc δ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hdim : ∀ s : ℝ, 0 < s → s < 1 →
      ENNReal.ofReal s ≤ dimH (GP.cylinder E) := by
    intro s hs hs1
    have hinf : GP.hausdorff s (GP.cylinder E) = ⊤ := by
      apply top_unique
      rw [← h_T003.2.2 s hs hs1]
      exact hmono s hs
    exact (h_T001.1 (n + 1) (GP.cylinder E)).2 s hs |>.2.2.2.2 hinf
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hr1
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hrlt : (r : ℝ) < 1 := by exact_mod_cast hr1
    have hconv : ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞) :=
      ENNReal.ofReal_coe_nnreal
    rw [← hconv]
    exact hdim (r : ℝ) hrpos hrlt
  · simp [hzero]

#check @T011
#print axioms T011

end Translation
