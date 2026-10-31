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

theorem T008 (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T007 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ,
    (∀ i, IsOpen (J i)) ∧
    (∀ i, GP.vertical '' (V i) ⊆ J i) ∧
    (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) +
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + (Metric.diam (V i)) ^ s))) ∧
    (∀ t ∈ GP.unitInterval,
      GP.content s δ E ≤
        ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t)) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε →
    GP.content s δ E ≤ GP.cost (s + 1) V + ENNReal.ofReal ε := by
  classical
  intro s δ hs hδ V hV ε hε
  have hcfinite : GP.content s δ E < ⊤ := h_T002.2.2.2.2 s δ hs hδ
  obtain ⟨J, hJopen, hJimage, hJlength, hslice⟩ := h_T007 s δ hs hδ V hV ε hε
  have hfinite (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    (lt_of_le_of_lt (hV.2 i) ENNReal.ofReal_lt_top).ne
  have error_bound (r : ℝ≥0∞) (b : ℝ) (hr : r ≠ ⊤) (hb : 0 ≤ b) :
      ENNReal.ofReal (b / (1 + r.toReal ^ s)) * r ^ s ≤ ENNReal.ofReal b := by
    have hd : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    have hp : 0 ≤ r.toReal ^ s := Real.rpow_nonneg hd s
    have hconv : ENNReal.ofReal (r.toReal ^ s) = r ^ s := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hd hs.le, ENNReal.ofReal_toReal hr]
    rw [← hconv, ← ENNReal.ofReal_mul (div_nonneg hb (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 1 + r.toReal ^ s)).2
    nlinarith [mul_nonneg hb hp]
  have herr (i : ℕ) :
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + Metric.diam (V i) ^ s)) * Metric.ediam (V i) ^ s ≤
        ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1)) := by
    exact error_bound (Metric.ediam (V i)) (ε * (1 / 2 : ℝ) ^ (i + 1))
      (hfinite i) (by positivity)
  have hsumerror :
      (∑' i : ℕ, ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1))) =
        ENNReal.ofReal ε := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    simp_rw [ENNReal.ofReal_mul hε.le,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, hhalf,
      ENNReal.one_sub_inv_two, inv_inv,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
  have hcost : (∑' i, Metric.ediam (V i) ^ (s + 1)) = GP.cost (s + 1) V := by
    unfold GP.cost
    apply tsum_congr
    intro i
    by_cases hi : (V i).Nonempty
    · simp [hi]
    · have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp [he, ENNReal.zero_rpow_of_pos (by linarith : 0 < s + 1)]
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict GP.unitInterval
  have hI : MeasurableSet GP.unitInterval := measurableSet_Icc
  have hmass : μ Set.univ = 1 := by
    simp [μ, GP.unitInterval, Real.volume_Icc]
  have hm (i : ℕ) :
      AEMeasurable ((J i).indicator (fun _ : ℝ => Metric.ediam (V i) ^ s)) μ :=
    (measurable_const.indicator (hJopen i).measurableSet).aemeasurable
  calc
    GP.content s δ E = ∫⁻ _ : ℝ, GP.content s δ E ∂μ := by
      rw [MeasureTheory.lintegral_const, hmass, mul_one]
    _ ≤ ∫⁻ t : ℝ, ∑' i, (J i).indicator (fun _ => Metric.ediam (V i) ^ s) t ∂μ := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hI] with t ht
      exact hslice t ht
    _ = ∑' i, ∫⁻ t : ℝ, (J i).indicator (fun _ => Metric.ediam (V i) ^ s) t ∂μ :=
      MeasureTheory.lintegral_tsum hm
    _ ≤ ∑' i, Metric.ediam (V i) ^ s * MeasureTheory.volume (J i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [MeasureTheory.lintegral_indicator_const (hJopen i).measurableSet]
      exact mul_le_mul_left'
        (MeasureTheory.Measure.restrict_le_self
          (s := GP.unitInterval) (μ := MeasureTheory.volume) (J i)) _
    _ ≤ ∑' i, (Metric.ediam (V i) ^ (s + 1) +
        ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1))) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hpow : Metric.ediam (V i) ^ s * Metric.ediam (V i) =
          Metric.ediam (V i) ^ (s + 1) := by
        rw [ENNReal.rpow_add_of_nonneg s 1 hs.le zero_le_one, ENNReal.rpow_one]
      calc
        Metric.ediam (V i) ^ s * MeasureTheory.volume (J i) ≤
            Metric.ediam (V i) ^ s * (Metric.ediam (V i) +
              ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
                (1 + Metric.diam (V i) ^ s))) :=
          mul_le_mul_left' (hJlength i) _
        _ = Metric.ediam (V i) ^ (s + 1) +
            Metric.ediam (V i) ^ s *
              ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
                (1 + Metric.diam (V i) ^ s)) := by rw [mul_add, hpow]
        _ ≤ Metric.ediam (V i) ^ (s + 1) +
            ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1)) := by
          apply add_le_add_left
          rw [mul_comm]
          exact herr i
    _ = GP.cost (s + 1) V + ENNReal.ofReal ε := by
      rw [ENNReal.tsum_add, hcost, hsumerror]

#check @T008
#print axioms T008

end Translation
