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

theorem T006 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T004 : n = 0 → dimH (GP.cylinder E) ≤ dimH E + 1) (h_T005 : 1 ≤ n → ∀ (q : ℝ), dimH E < ENNReal.ofReal q →
  ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    GP.content (q + 1) δ (GP.cylinder E) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) :
    dimH (GP.cylinder E) ≤ dimH E + 1 ∧ dimH (GP.cylinder E) < ⊤ := by
  have hbound : dimH (GP.cylinder E) ≤ dimH E + 1 := by
    by_cases hn : n = 0
    · exact h_T004 hn
    · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hqbound : ∀ q : ℝ, dimH E < ENNReal.ofReal q →
          dimH (GP.cylinder E) ≤ ENNReal.ofReal (q + 1) := by
        intro q hq
        have hqreal : (dimH E).toReal < q :=
          (ENNReal.lt_ofReal_iff_toReal_lt h_T002.1.ne).1 hq
        have hqpos : 0 < q := lt_of_le_of_lt ENNReal.toReal_nonneg hqreal
        have hC : 0 < 2 * (Real.sqrt 2) ^ (q + 1) := by positivity
        have hcontent : ∀ δ : ℝ, 0 < δ →
            GP.content (q + 1) δ (GP.cylinder E) = 0 := by
          intro δ hδ
          apply le_antisymm _ (zero_le _)
          apply ENNReal.le_of_forall_pos_le_add
          intro ε hε _
          have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
          have hεdiv : 0 < (ε : ℝ) / (2 * (Real.sqrt 2) ^ (q + 1)) :=
            div_pos hεr hC
          have hconv : ENNReal.ofReal
              (2 * (Real.sqrt 2) ^ (q + 1) *
                ((ε : ℝ) / (2 * (Real.sqrt 2) ^ (q + 1)))) = (ε : ℝ≥0∞) := by
            rw [mul_div_cancel₀ (ε : ℝ) (ne_of_gt hC), ENNReal.ofReal_coe_nnreal]
          simpa only [zero_add, hconv] using
            h_T005 hn' q hq δ ((ε : ℝ) / (2 * (Real.sqrt 2) ^ (q + 1))) hδ hεdiv
        have hhaus : GP.hausdorff (q + 1) (GP.cylinder E) = 0 := by
          apply le_antisymm _ (zero_le _)
          change (⨆ (δ : ℝ) (_ : 0 < δ), GP.content (q + 1) δ (GP.cylinder E)) ≤ 0
          exact iSup_le fun δ => iSup_le fun hδ => (hcontent δ hδ).le
        exact (h_T001.1 (n + 1) (GP.cylinder E)).2 (q + 1) (by linarith) |>.2.2.2.1 hhaus
      have hfixed : dimH E < ENNReal.ofReal ((dimH E).toReal + 1) := by
        apply (ENNReal.lt_ofReal_iff_toReal_lt h_T002.1.ne).2
        linarith
      have hfinite : dimH (GP.cylinder E) < ⊤ :=
        lt_of_le_of_lt (hqbound _ hfixed) ENNReal.ofReal_lt_top
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
      have hq : dimH E < ENNReal.ofReal ((dimH E).toReal + (ε : ℝ)) := by
        apply (ENNReal.lt_ofReal_iff_toReal_lt h_T002.1.ne).2
        linarith
      have hconv : ENNReal.ofReal ((dimH E).toReal + (ε : ℝ) + 1) =
          dimH E + 1 + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg ε.coe_nonneg) (by norm_num),
          ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg,
          ENNReal.ofReal_toReal h_T002.1.ne, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one]
        ac_rfl
      simpa only [hconv] using hqbound _ hq
  exact ⟨hbound, lt_of_le_of_lt hbound (ENNReal.add_lt_top.mpr ⟨h_T002.1, by simp⟩)⟩

#check @T006
#print axioms T006

end Translation
