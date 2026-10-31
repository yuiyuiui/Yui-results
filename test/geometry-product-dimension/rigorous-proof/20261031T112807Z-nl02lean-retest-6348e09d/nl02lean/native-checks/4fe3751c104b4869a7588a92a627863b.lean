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

theorem T003 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) :
    dimH yI ≤ 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) := by
  classical
  have hcover : ∀ N : ℕ, 0 < N → ∃ U : ℕ → Set ℝ,
      yCover (1 / (N : ℝ)) yI U ∧
      (∀ k, Metric.ediam (U k) = if k < N then ENNReal.ofReal (1 / (N : ℝ)) else 0) := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let U : ℕ → Set ℝ := fun k =>
      if k < N then Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N) else ∅
    have hd : ∀ k, Metric.ediam (U k) =
        if k < N then ENNReal.ofReal (1 / (N : ℝ)) else 0 := by
      intro k
      by_cases hk : k < N
      · simp only [U, if_pos hk, Real.ediam_Icc]
        congr 1
        ring
      · simp [U, hk]
    refine ⟨U, ⟨?_, ?_⟩, hd⟩
    · intro x hx
      change 0 ≤ x ∧ x ≤ 1 at hx
      apply Set.mem_iUnion.mpr
      by_cases hx1 : x = 1
      · refine ⟨N - 1, ?_⟩
        have hk : N - 1 < N := Nat.sub_lt hN (by omega)
        simp only [U, if_pos hk, mem_Icc, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
        subst x
        constructor
        · apply (div_le_iff₀ hNr).mpr
          linarith
        · apply (le_div_iff₀ hNr).mpr
          linarith
      · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
        let k := ⌊x * (N : ℝ)⌋₊
        have hmul : 0 ≤ x * (N : ℝ) := mul_nonneg hx.1 hNr.le
        have hk : k < N := (Nat.floor_lt hmul).mpr (by nlinarith)
        refine ⟨k, ?_⟩
        simp only [U, if_pos hk, mem_Icc]
        constructor
        · exact (div_le_iff₀ hNr).mpr (Nat.floor_le hmul)
        · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one (x * (N : ℝ))).le
    · intro k
      rw [hd k]
      split_ifs <;> simp
  have hcost : ∀ (a : ℝ) (N : ℕ) (U : ℕ → Set ℝ), 1 < a → 0 < N →
      (∀ k, Metric.ediam (U k) = if k < N then ENNReal.ofReal (1 / (N : ℝ)) else 0) →
      yCost a U = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
    intro a N U ha hN hd
    have ha0 : 0 < a := by linarith
    have hsum : yCost a U =
        (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by
      unfold yCost
      rw [tsum_eq_sum (s := Finset.range N) (fun k hk => ?_)]
      · simp only [hd]
        simp [Finset.sum_ite_of_true, Finset.mem_range]
      · have hk' : ¬ k < N := by simpa using hk
        simp [hd, hk', ha0]
    rw [hsum]
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNr)]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNr.le]
    congr 1
    rw [Real.rpow_sub hNr, Real.rpow_one, one_div, Real.inv_rpow hNr.le]
    rfl
  have hsmall : ∀ a δ η : ℝ, 1 < a → 0 < δ → 0 < η →
      ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ δ ∧ (N : ℝ) ^ (1 - a) < η := by
    intro a δ η ha hδ hη
    have hlim : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) Filter.atTop (nhds 0) := by
      simpa only [neg_sub, Function.comp_def] using
        (tendsto_rpow_neg_atTop (by linarith : 0 < a - 1)).comp
          (tendsto_natCast_atTop_atTop :
            Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)
    have hinv : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds 0) := by
      simpa only [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop :
            Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop))
    obtain ⟨N, hN, hδN, hηN⟩ := (Filter.eventually_gt_atTop 0 |>.and
      ((hinv.eventually (gt_mem_nhds hδ)).and
        (hlim.eventually (gt_mem_nhds hη)))).exists
    exact ⟨N, hN, hδN.le, hηN⟩
  have hz : ∀ a : ℝ, 1 < a → yHaus a yI = 0 := by
    intro a ha
    apply le_antisymm ?_ bot_le
    unfold yHaus
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    simp only [bot_eq_zero, zero_add]
    obtain ⟨N, hN, hδN, hηN⟩ := hsmall a δ (ε : ℝ) ha hδ (NNReal.coe_pos.mpr hε)
    obtain ⟨U, hU, hd⟩ := hcover N hN
    have hdδ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ :=
      fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hδN)
    have hc : yContent a δ yI ≤ yCost a U := by
      unfold yContent yCost
      exact iInf_le_of_le U (iInf_le_of_le hU.1 (iInf_le_of_le hdδ le_rfl))
    rw [hcost a N U ha hN hd] at hc
    exact hc.trans (by simpa using ENNReal.ofReal_le_ofReal hηN.le)
  refine ⟨?_, hz⟩
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  have ha : 0 < 1 + (ε : ℝ) := by positivity
  have hb : dimH yI ≤ ENNReal.ofReal (1 + (ε : ℝ)) :=
    ((h_T001.2.2 yI (1 + (ε : ℝ)) ha).2.2.2.1) (hz _ (by linarith))
  simpa only [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) ε.coe_nonneg,
    ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal] using hb

#check @T003
#print axioms T003

end Translation
