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

theorem T013 (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T012 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set (YEucl n), YCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ YCost q U < ENNReal.ofReal ε) :
    1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ V : ℕ → Set (YEucl (n+1)), YCover (Real.sqrt 2 * r) (YF E) V ∧ YCost (q+1) V < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) := by
  classical
  have partition : ∀ (d : ℝ), 0 < d → d ≤ 1 → let N := ⌈1 / d⌉₊; 0 < N ∧ 1 / (N : ℝ) ≤ d ∧ (N : ℝ) ≤ 2 / d ∧ ∀ t ∈ YI, ∃ j : ℕ, j < N ∧ t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
    intro d hd hd1 N
    have hc : 1 / d ≤ (N : ℝ) := Nat.le_ceil _
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨hN, (div_le_iff₀ hNr).2 ?_, ?_, ?_⟩
    · have := (div_le_iff₀ hd).1 hc
      nlinarith
    · have h := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / d)).le
      change (N : ℝ) ≤ 2 / d
      apply (le_div_iff₀ hd).2
      have hh : (N : ℝ) * d ≤ (1 / d + 1) * d := mul_le_mul_of_nonneg_right h hd.le
      field_simp at hh
      nlinarith
    · intro t ht
      change 0 ≤ t ∧ t ≤ 1 at ht
      by_cases ht1 : t = 1
      · refine ⟨N-1, by omega, ?_⟩
        have he : ((N-1 : ℕ) : ℝ) + 1 = N := by
          exact_mod_cast (Nat.sub_add_cancel hN)
        subst t
        constructor
        · apply (div_le_iff₀ hNr).2
          linarith
        · apply (le_div_iff₀ hNr).2
          linarith
      · refine ⟨⌊t * N⌋₊, ?_, ?_⟩
        · apply (Nat.floor_lt (mul_nonneg ht.1 hNr.le)).2
          have htt : t < 1 := lt_of_le_of_ne ht.2 ht1
          nlinarith
        · constructor
          · apply (div_le_iff₀ hNr).2
            exact Nat.floor_le (mul_nonneg ht.1 hNr.le)
          · apply (le_div_iff₀ hNr).2
            exact (Nat.lt_floor_add_one _).le
  have product_diam : ∀ (A : Set (YEucl n)) (d : ℝ) (N j : ℕ), Metric.ediam A ≠ ⊤ → (Metric.ediam A).toReal ≤ d → 0 < N → 1 / (N : ℝ) ≤ d → Metric.ediam {z : YEucl (n+1) | ∃ x ∈ A, ∃ t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ)+1)/N), z = YJoin x t} ≤ ENNReal.ofReal (Real.sqrt 2 * d) := by
    intro A d N j hfin hAd hN hNd
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hd : 0 ≤ d := (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)).trans hNd
    apply Metric.ediam_le_of_forall_dist_le
    rintro _ ⟨x, hx, t, ht, rfl⟩ _ ⟨y, hy, u, hu, rfl⟩
    rw [h_T003.1]
    have hxy : dist x y ≤ d := (Metric.dist_le_diam_of_mem' hfin hx hy).trans hAd
    have htu : |t-u| ≤ d := by
      simp only [add_div] at ht hu
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hh : dist x y ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ dist_nonneg hxy 2
    have hv : |t-u| ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (abs_nonneg _) htu 2
    nlinarith [sq_nonneg d]
  have cost_bound : ∀ (q d : ℝ) (N : ℕ), 0 < q → 0 < d → (N : ℝ) ≤ 2 / d → (N : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 2 * d) ^ (q+1) ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal d ^ q := by
    intro q d N hq hd hN
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [ENNReal.ofReal_rpow_of_pos (mul_pos hs hd), ENNReal.ofReal_rpow_of_pos hd,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.sqrt 2 ^ (q+1))]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.mul_rpow hs.le hd.le, Real.rpow_add hd, Real.rpow_one]
    have hn : (N : ℝ) * d ≤ 2 := (le_div_iff₀ hd).1 hN
    nlinarith [mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ Real.sqrt 2 ^ (q+1) * d ^ q)]
  intro hn q hq hdim r hr hr1 ε hε
  obtain ⟨U, hU, hpos, hcost⟩ := h_T012 hn q hq hdim r hr hr1 ε hε
  have hfin : ∀ i, Metric.ediam (U i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i)
  let d : ℕ → ℝ := fun i => (Metric.ediam (U i)).toReal
  have hd0 : ∀ i, 0 ≤ d i := fun i => ENNReal.toReal_nonneg
  have hde : ∀ i, ENNReal.ofReal (d i) = Metric.ediam (U i) :=
    fun i => ENNReal.ofReal_toReal (hfin i)
  have hdr : ∀ i, d i ≤ r :=
    fun i => ENNReal.toReal_le_of_le_ofReal hr.le (hU.2 i)
  have hdpos : ∀ i, (U i).Nonempty → 0 < d i :=
    fun i hi => ENNReal.toReal_pos (ne_of_gt (hpos i hi)) (hfin i)
  let N : ℕ → ℕ := fun i => ⌈1 / d i⌉₊
  have hparts : ∀ i, (U i).Nonempty →
      0 < N i ∧ 1 / (N i : ℝ) ≤ d i ∧ (N i : ℝ) ≤ 2 / d i ∧
        ∀ t ∈ YI, ∃ j : ℕ, j < N i ∧ t ∈ Set.Icc ((j : ℝ) / N i) (((j : ℝ)+1)/N i) :=
    fun i hi => partition (d i) (hdpos i hi) ((hdr i).trans hr1)
  let W : ℕ → ℕ → Set (YEucl (n+1)) := fun i j =>
    if j < N i then
      {z | ∃ x ∈ U i, ∃ t ∈ Set.Icc ((j : ℝ)/N i) (((j : ℝ)+1)/N i), z = YJoin x t}
    else ∅
  have hWempty : ∀ i, ¬(U i).Nonempty → ∀ j, W i j = ∅ := by
    intro i hi j
    have he : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp [W, he]
  have hWd : ∀ i j, Metric.ediam (W i j) ≤ ENNReal.ofReal (Real.sqrt 2 * d i) := by
    intro i j
    by_cases hi : (U i).Nonempty
    · by_cases hj : j < N i
      · simpa only [W, if_pos hj] using
          product_diam (U i) (d i) (N i) j (hfin i) le_rfl (hparts i hi).1 (hparts i hi).2.1
      · simp [W, hj]
    · simp [hWempty i hi j]
  have hrow : ∀ i, (∑' j, Metric.ediam (W i j) ^ (q+1)) ≤
      ENNReal.ofReal (2 * Real.sqrt 2 ^ (q+1)) * Metric.ediam (U i) ^ q := by
    intro i
    by_cases hi : (U i).Nonempty
    · calc
        (∑' j, Metric.ediam (W i j) ^ (q+1)) ≤
            ∑' j : ℕ, if j < N i then ENNReal.ofReal (Real.sqrt 2 * d i) ^ (q+1) else 0 := by
          apply ENNReal.tsum_le_tsum
          intro j
          by_cases hj : j < N i
          · simp only [if_pos hj]
            exact ENNReal.rpow_le_rpow (hWd i j) (by linarith)
          · simp [W, hj, ENNReal.zero_rpow_of_pos (by linarith : 0 < q+1)]
        _ = (N i : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 2 * d i) ^ (q+1) := by
          calc
            _ = ∑ j ∈ Finset.range (N i),
                (if j < N i then ENNReal.ofReal (Real.sqrt 2 * d i) ^ (q+1) else 0) :=
              tsum_eq_sum (fun j hj => if_neg (by simpa using hj))
            _ = ∑ j ∈ Finset.range (N i), ENNReal.ofReal (Real.sqrt 2 * d i) ^ (q+1) :=
              Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))
            _ = _ := by simp
        _ ≤ _ := by
          rw [← hde i]
          exact cost_bound q (d i) (N i) hq (hdpos i hi) (hparts i hi).2.2.1
    · simp [hWempty i hi, ENNReal.zero_rpow_of_pos (by linarith : 0 < q+1)]
  let V : ℕ → Set (YEucl (n+1)) := fun k =>
    W (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2
  refine ⟨V, ⟨?_, ?_⟩, ?_⟩
  · rintro z ⟨x, hx, t, ht, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hx)
    obtain ⟨j, hj, htj⟩ := (hparts i ⟨x, hi⟩).2.2.2 t ht
    apply Set.mem_iUnion.mpr
    refine ⟨Nat.pairEquiv (i,j), ?_⟩
    change YJoin x t ∈ W (Nat.pairEquiv.symm (Nat.pairEquiv (i,j))).1
      (Nat.pairEquiv.symm (Nat.pairEquiv (i,j))).2
    simp only [Equiv.symm_apply_apply]
    simp only [W, if_pos hj, Set.mem_setOf_eq]
    exact ⟨x, hi, t, htj, rfl⟩
  · intro k
    exact (hWd _ _).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hdr _) (Real.sqrt_nonneg _)))
  · have heq : YCost (q+1) V = ∑' i, ∑' j, Metric.ediam (W i j) ^ (q+1) := by
      change (∑' k : ℕ, (fun p : ℕ × ℕ => Metric.ediam (W p.1 p.2) ^ (q+1))
        (Nat.pairEquiv.symm k)) = _
      rw [Nat.pairEquiv.symm.tsum_eq, ENNReal.tsum_prod']
    rw [heq]
    calc
      (∑' i, ∑' j, Metric.ediam (W i j) ^ (q+1)) ≤
          ∑' i, ENNReal.ofReal (2 * Real.sqrt 2 ^ (q+1)) * Metric.ediam (U i) ^ q :=
        ENNReal.tsum_le_tsum hrow
      _ = ENNReal.ofReal (2 * Real.sqrt 2 ^ (q+1)) * YCost q U :=
        ENNReal.tsum_mul_left
      _ < ENNReal.ofReal (2 * Real.sqrt 2 ^ (q+1)) * ENNReal.ofReal ε :=
        ENNReal.mul_lt_mul_right (by positivity) ENNReal.ofReal_ne_top hcost
      _ = ENNReal.ofReal (2 * Real.sqrt 2 ^ (q+1) * ε) :=
        (ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.sqrt 2 ^ (q+1))).symm

#check @T013
#print axioms T013

end Translation
