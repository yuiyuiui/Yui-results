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

theorem T012 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) :
    1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set (YEucl n), YCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ YCost q U < ENNReal.ofReal ε := by
  classical
  intro hn q hq hdim r hr hr1 ε hε
  have hzero : YHaus q E = 0 := ((h_T002 n E).2 q hq).2.1 hdim
  have hc : YContent q r E = 0 := by
    apply le_antisymm _ zero_le
    calc YContent q r E ≤ YHaus q E :=
          le_iSup_of_le r (le_iSup_of_le hr le_rfl)
         _ = 0 := hzero
  have hsmall : YContent q r E < ENNReal.ofReal (ε / 2) := by
    rw [hc]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨V, hV, hcost⟩ : ∃ V : ℕ → Set (YEucl n),
      YCover r E V ∧ YCost q V < ENNReal.ofReal (ε / 2) := by
    simpa only [YContent, iInf_lt_iff, exists_prop] using hsmall
  have hball : ∀ η : ℝ, 0 < η → ∀ x : YEucl n, ∃ a : ℝ,
      0 < a ∧ Metric.ediam (Metric.ball x a) ≤ ENNReal.ofReal r ∧
      0 < Metric.ediam (Metric.ball x a) ∧
      (Metric.ediam (Metric.ball x a)) ^ q < ENNReal.ofReal η := by
    intro η hη x
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    let b : ℝ := min r (η ^ q⁻¹) / 2
    have hb : 0 < b := by dsimp [b]; positivity
    have hbr : b ≤ r := by
      have := min_le_left r (η ^ q⁻¹)
      dsimp [b]
      linarith [lt_min hr (Real.rpow_pos_of_pos hη q⁻¹)]
    have hbη : b < η ^ q⁻¹ := by
      have := min_le_right r (η ^ q⁻¹)
      dsimp [b]
      linarith [lt_min hr (Real.rpow_pos_of_pos hη q⁻¹)]
    have hd : Metric.ediam (Metric.ball x (b / 2)) = ENNReal.ofReal b := by
      have hh := Metric.diam_ball_eq x (show 0 ≤ b / 2 by positivity)
      have he : Metric.ediam (Metric.ball x (b / 2)) ≠ ⊤ :=
        Metric.isBounded_ball.ediam_ne_top
      calc
        Metric.ediam (Metric.ball x (b / 2)) =
          ENNReal.ofReal (Metric.diam (Metric.ball x (b / 2))) :=
            (ENNReal.ofReal_toReal he).symm
        _ = ENNReal.ofReal b := by rw [hh]; congr 1; ring
    refine ⟨b / 2, by positivity, ?_, ?_, ?_⟩
    · rw [hd]; exact ENNReal.ofReal_le_ofReal hbr
    · rw [hd]; exact ENNReal.ofReal_pos.mpr hb
    · rw [hd, ENNReal.ofReal_rpow_of_pos hb]
      apply (ENNReal.ofReal_lt_ofReal_iff hη).mpr
      calc b ^ q < (η ^ q⁻¹) ^ q := Real.rpow_lt_rpow hb.le hbη hq
           _ = η := Real.rpow_inv_rpow hη.le hq.ne'
  let w : ℕ → ℝ := fun i => (ε / 2) / 2 / 2 ^ i
  have hw : ∀ i, 0 < w i := by intro i; dsimp [w]; positivity
  have hwsum : (∑' i, ENNReal.ofReal (w i)) = ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hw i).le)
      (summable_geometric_two' (ε / 2))]
    rw [tsum_geometric_two']
  have hreplace : ∀ i : ℕ, ∃ S : Set (YEucl n),
      V i ⊆ S ∧ Metric.ediam S ≤ ENNReal.ofReal r ∧
      (S.Nonempty → 0 < Metric.ediam S) ∧
      (Metric.ediam S) ^ q ≤ (Metric.ediam (V i)) ^ q + ENNReal.ofReal (w i) := by
    intro i
    by_cases hne : (V i).Nonempty
    · by_cases hz : Metric.ediam (V i) = 0
      · obtain ⟨x, hx⟩ := hne
        obtain ⟨a, ha, har, hap, hac⟩ := hball (w i) (hw i) x
        refine ⟨Metric.ball x a, ?_, har, fun _ => hap, ?_⟩
        · intro y hy
          have hyx : y = x := (Metric.ediam_eq_zero_iff.mp hz) hy hx
          simpa [hyx] using Metric.mem_ball_self (x := x) ha
        · exact hac.le.trans le_add_self
      · exact ⟨V i, Set.Subset.rfl, hV.2 i,
          fun _ => lt_of_le_of_ne zero_le (Ne.symm hz), le_self_add⟩
    · refine ⟨∅, ?_, ?_, ?_, ?_⟩
      · simpa [Set.not_nonempty_iff_eq_empty.mp hne]
      · simp
      · simp
      · simp [ENNReal.zero_rpow_of_pos hq]
  choose U hsub hdiam hpos hbound using hreplace
  refine ⟨U, ⟨?_, hdiam⟩, hpos, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, hsub i hi⟩
  · calc
      YCost q U ≤ ∑' i, ((Metric.ediam (V i)) ^ q + ENNReal.ofReal (w i)) :=
        ENNReal.tsum_le_tsum hbound
      _ = YCost q V + ENNReal.ofReal (ε / 2) := by
        rw [ENNReal.tsum_add, hwsum]; rfl
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hcost
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 2) (by positivity : 0 ≤ ε / 2)]
        congr 1
        ring

#check @T012
#print axioms T012

end Translation
