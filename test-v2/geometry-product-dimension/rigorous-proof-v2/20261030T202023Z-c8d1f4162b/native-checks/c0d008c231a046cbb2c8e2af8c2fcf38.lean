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

theorem T017 (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T016 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ, (∀ i, IsOpen (J i)) ∧ (∀ i, YLast '' (V i) ⊆ J i) ∧ (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s))) ∧ (∀ t ∈ YI, YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t)) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → YContent s δ E ≤ YCost (s+1) V := by
  classical
  intro s δ hs hδ V hV
  have hcfin : YContent s δ E < ⊤ := h_T006.2.2 s δ hs hδ
  have hrfin (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  have herr (r : ℝ≥0∞) (a : ℝ) (hr : r ≠ ⊤) (ha : 0 ≤ a) :
      r ^ s * ENNReal.ofReal (a / (1 + r.toReal ^ s)) ≤ ENNReal.ofReal a := by
    have hc : ENNReal.ofReal (r.toReal ^ s) = r ^ s := by
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le,
        ENNReal.ofReal_toReal hr]
    rw [← hc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg s)]
    apply ENNReal.ofReal_le_ofReal
    have hp : 0 ≤ r.toReal ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg s
    have hd : 0 < 1 + r.toReal ^ s := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hgeom (a : ℝ) (ha : 0 ≤ a) :
      (∑' i : ℕ, ENNReal.ofReal (a * (2 : ℝ) ^ (-(i : ℤ)-1))) = ENNReal.ofReal a := by
    have he (i : ℕ) : a * (2 : ℝ) ^ (-(i : ℤ)-1) = a / 2 / 2 ^ i := by
      rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg, zpow_natCast]
      norm_num
      ring
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' a),
      tsum_geometric_two']
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hcost
  have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨J, hJ, hproj, hvol, hpt⟩ := h_T016 s δ hs hδ V hV (ε : ℝ) hεr
  have hm (i : ℕ) : Measurable (fun t : ℝ =>
      (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t) :=
    measurable_const.mul (measurable_const.indicator (hJ i).measurableSet)
  have hmono : (∫⁻ _ : ℝ in YI, YContent s δ E) ≤
      ∫⁻ t : ℝ in YI, ∑' i, (Metric.ediam (V i)) ^ s *
        (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t := by
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet YI from measurableSet_Icc)] with t ht
    exact hpt t ht
  have hc : (∫⁻ _ : ℝ in YI, YContent s δ E) = YContent s δ E := by
    simp [MeasureTheory.lintegral_const, YI, Real.volume_Icc]
  rw [hc, MeasureTheory.lintegral_tsum (fun i => (hm i).aemeasurable)] at hmono
  have hint : YContent s δ E ≤
      ∑' i, (Metric.ediam (V i)) ^ s * MeasureTheory.volume (J i) := by
    refine hmono.trans (ENNReal.tsum_le_tsum fun i => ?_)
    rw [MeasureTheory.lintegral_const_mul _ (measurable_const.indicator (hJ i).measurableSet),
      MeasureTheory.lintegral_indicator_const (hJ i).measurableSet, one_mul]
    have hrestrict : (MeasureTheory.volume.restrict YI) (J i) ≤ MeasureTheory.volume (J i) :=
      MeasureTheory.Measure.restrict_apply_le YI (J i)
    exact mul_le_mul_left' hrestrict _
  have hterm (i : ℕ) :
      (Metric.ediam (V i)) ^ s * MeasureTheory.volume (J i) ≤
      (Metric.ediam (V i)) ^ (s+1) +
        ENNReal.ofReal ((ε : ℝ) * (2 : ℝ) ^ (-(i : ℤ)-1)) := by
    calc
      _ ≤ (Metric.ediam (V i)) ^ s * ((Metric.ediam (V i)) +
          ENNReal.ofReal ((ε : ℝ) * (2 : ℝ) ^ (-(i : ℤ)-1) /
            (1 + (Metric.ediam (V i)).toReal ^ s))) :=
        mul_le_mul_left' (hvol i) _
      _ = (Metric.ediam (V i)) ^ (s+1) +
          (Metric.ediam (V i)) ^ s *
            ENNReal.ofReal ((ε : ℝ) * (2 : ℝ) ^ (-(i : ℤ)-1) /
            (1 + (Metric.ediam (V i)).toReal ^ s)) := by
        rw [mul_add, ENNReal.rpow_add_of_nonneg s 1 hs.le (by norm_num),
          ENNReal.rpow_one]
      _ ≤ _ := add_le_add (le_refl _) (herr (Metric.ediam (V i)) ((ε : ℝ) * (2 : ℝ) ^ (-(i : ℤ)-1)) (hrfin i) (by positivity))
  calc
    YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * MeasureTheory.volume (J i) := hint
    _ ≤ ∑' i, ((Metric.ediam (V i)) ^ (s+1) +
        ENNReal.ofReal ((ε : ℝ) * (2 : ℝ) ^ (-(i : ℤ)-1))) :=
      ENNReal.tsum_le_tsum hterm
    _ = YCost (s+1) V + ε := by
      rw [ENNReal.tsum_add, hgeom (ε : ℝ) hεr.le]
      simp [YCost]

#check @T017
#print axioms T017

end Translation
