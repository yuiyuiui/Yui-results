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

theorem T007 (n : ℕ) (E : Set (YEucl n))  :
    ∀ a : ℝ, 1 < a → YHaus a YI = 0 := by
  classical
  have hcov : ∀ k : ℕ, 0 < k → YI ⊆ ⋃ j : ℕ,
      (if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) := by
    intro k hk x hx
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    simp only [Set.mem_iUnion]
    by_cases h : x < 1
    · let j := ⌊x * k⌋₊
      have hj : j < k := by
        dsimp [j]
        apply (Nat.floor_lt (mul_nonneg hx0 hkR.le)).mpr
        nlinarith
      refine ⟨j, ?_⟩
      simp only [if_pos hj, Set.mem_Icc]
      constructor
      · apply (div_le_iff₀ hkR).mpr
        exact Nat.floor_le (mul_nonneg hx0 hkR.le)
      · apply (le_div_iff₀ hkR).mpr
        exact (Nat.lt_floor_add_one (x * k)).le
    · have hxE : x = 1 := le_antisymm hx1 (le_of_not_gt h)
      refine ⟨k - 1, ?_⟩
      rw [if_pos (Nat.sub_lt hk (by omega))]
      have hc : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        exact_mod_cast Nat.sub_add_cancel hk
      simp only [Set.mem_Icc]
      rw [hxE]
      constructor
      · apply (div_le_iff₀ hkR).mpr
        nlinarith
      · rw [hc, div_self hkR.ne']
  have hcost : ∀ a : ℝ, 0 < a → ∀ k : ℕ, 0 < k →
      YCost a (fun j : ℕ => if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) =
        ENNReal.ofReal ((k : ℝ) ^ (1 - a)) := by
    intro a ha k hk
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hd : ∀ j : ℕ, Metric.ediam (Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k)) = ENNReal.ofReal (1 / (k : ℝ)) := by
      intro j
      rw [Real.ediam_Icc]
      congr 1
      ring
    unfold YCost
    rw [tsum_eq_sum (s := Finset.range k)]
    · calc
        (∑ j ∈ Finset.range k, Metric.ediam (if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) ^ a)
            = (k : ℝ≥0∞) * (ENNReal.ofReal (1 / (k : ℝ))) ^ a := by
              calc
                _ = ∑ j ∈ Finset.range k, (ENNReal.ofReal (1 / (k : ℝ))) ^ a := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [if_pos (Finset.mem_range.mp hj), hd]
                _ = _ := by simp [nsmul_eq_mul]
        _ = ENNReal.ofReal ((k : ℝ) * (1 / (k : ℝ)) ^ a) := by
              rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_natCast,
                ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal ((k : ℝ) ^ (1 - a)) := by
              congr 1
              rw [sub_eq_add_neg, Real.rpow_add hkR, Real.rpow_one,
                Real.rpow_neg_eq_inv_rpow, one_div]
    · intro j hj
      have hj' : ¬ j < k := by simpa using hj
      simp [hj', ENNReal.zero_rpow_of_pos ha]

  have hadm : ∀ (δ : ℝ) (k : ℕ), 0 < k → 1 / (k : ℝ) ≤ δ →
      (YI ⊆ ⋃ j : ℕ, (if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅)) →
        YCover δ YI (fun j : ℕ => if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) := by
    intro δ k hk hδ hcov
    refine ⟨hcov, ?_⟩
    intro j
    change Metric.ediam (if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) ≤ ENNReal.ofReal δ
    by_cases hj : j < k
    · rw [if_pos hj, Real.ediam_Icc]
      have he : ((j : ℝ) + 1) / k - (j : ℝ) / k = 1 / k := by ring
      rw [he]
      exact ENNReal.ofReal_le_ofReal hδ
    · simp [hj]
  have hscale : ∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in Filter.atTop, 1 / (k : ℝ) ≤ δ := by
    intro δ hδ
    have h : Filter.Tendsto (fun k : ℕ => 1 / (k : ℝ)) Filter.atTop (nhds 0) := by
      simpa only [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    exact Filter.Eventually.mono (h.eventually (gt_mem_nhds hδ)) (fun k hk => hk.le)
  intro a ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hlimR : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (1 - a)) Filter.atTop (nhds 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < a - 1)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal ((k : ℝ) ^ (1 - a)))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlimR
  apply le_antisymm _ bot_le
  unfold YHaus
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  apply ge_of_tendsto hlim
  filter_upwards [hscale δ hδ, Filter.eventually_ge_atTop 1] with k hkδ hk
  have hk0 : 0 < k := by omega
  have hC := hadm δ k hk0 hkδ (hcov k hk0)
  calc
    YContent a δ YI ≤ YCost a (fun j : ℕ =>
        if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅) := by
      unfold YContent
      exact iInf_le_of_le _ (iInf_le_of_le hC le_rfl)
    _ = ENNReal.ofReal ((k : ℝ) ^ (1 - a)) := hcost a ha0 k hk0

#check @T007
#print axioms T007

end Translation
