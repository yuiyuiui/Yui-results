import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

namespace Translation
set_option autoImplicit false

theorem T009 (n : ℕ) (E : Set (GPEucl n)) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T008 : 1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ U : ℕ → Set (GPEucl n),
    GPcover E r U ∧
    (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧
    GPcost q U < ENNReal.ofReal ε) :
    1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ W : ℕ → Set (GPEucl (n + 1)),
    GPcover (GPproduct E) (Real.sqrt 2 * r) W ∧
    GPcost (q + 1) W <
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := by
  classical
  have hpartition : ∀ (d : ℝ), 0 < d → d ≤ 1 →
    let N := ⌈1 / d⌉₊
    0 < N ∧ 1 / (N : ℝ) ≤ d ∧ (N : ℝ) * d ≤ 2 ∧
    ∀ t ∈ GPI, ∃ j : ℕ, j < N ∧ (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N := by
      intro d hd hd1 N
      have hceil : 1 / d ≤ (N : ℝ) := Nat.le_ceil _
      have hNreal : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity) hceil
      have hN : 0 < N := by exact_mod_cast hNreal
      refine ⟨hN, ?_, ?_, ?_⟩
      · apply (div_le_iff₀ hNreal).2
        have := (div_le_iff₀ hd).1 hceil
        nlinarith
      · have hlt : (N : ℝ) < 1 / d + 1 := Nat.ceil_lt_add_one (by positivity)
        have hmul := (mul_lt_mul_of_pos_right hlt hd)
        have heq : (1 / d + 1) * d = 1 + d := by field_simp
        rw [heq] at hmul
        linarith
      · intro t ht
        change 0 ≤ t ∧ t ≤ 1 at ht
        by_cases ht0 : t = 0
        · refine ⟨0, hN, ?_, ?_⟩ <;> simp [ht0, hNreal.le]
        · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          let m := ⌈t * (N : ℝ)⌉₊
          have hmlo : t * (N : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
          have hmhi : (m : ℝ) < t * (N : ℝ) + 1 :=
            Nat.ceil_lt_add_one (by positivity)
          have hmpos : 0 < m := by
            have : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hmlo
            exact_mod_cast this
          have hmN : m ≤ N := by
            dsimp [m]
            exact Nat.ceil_le.2 (by nlinarith [ht.2])
          refine ⟨m - 1, by omega, ?_, ?_⟩
          · apply (div_le_iff₀ hNreal).2
            rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
            linarith
          · apply (le_div_iff₀ hNreal).2
            rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
            linarith
  have hcylinder : ∀ (A : Set (GPEucl n)) (d : ℝ), 0 ≤ d →
    Metric.ediam A ≤ ENNReal.ofReal d →
    ∀ (N : ℕ), 0 < N → 1 / (N : ℝ) ≤ d → ∀ j : ℕ,
    Metric.ediam {z : GPEucl (n + 1) | GPhead z ∈ A ∧
      (j : ℝ) / N ≤ z (Fin.last n) ∧ z (Fin.last n) ≤ ((j : ℝ) + 1) / N}
      ≤ ENNReal.ofReal (Real.sqrt 2 * d) := by
      intro A d hd hA N hN hNd j
      have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
      apply Metric.ediam_le_of_forall_dist_le
      intro z hz w hw
      have hhor : dist (GPhead z) (GPhead w) ≤ d :=
        (edist_le_ofReal hd).1 (Metric.edist_le_of_ediam_le hz.1 hw.1 hA)
      have hvert : |z (Fin.last n) - w (Fin.last n)| ≤ d := by
        apply le_trans _ hNd
        rw [abs_le]
        change _ ∧ _ ∧ _ at hz hw
        rw [add_div] at hz hw
        constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
      have hdist : dist z w = Real.sqrt
        (dist (GPhead z) (GPhead w) ^ 2 + |z (Fin.last n) - w (Fin.last n)| ^ 2) := by
        calc
          dist z w = dist (GPappend (GPhead z) (z (Fin.last n)))
            (GPappend (GPhead w) (w (Fin.last n))) := by
              rw [h_T001.2.1 n z, h_T001.2.1 n w]
          _ = _ := h_T001.2.2.1 _ _ _ _ _
      rw [hdist]
      have hh2 : dist (GPhead z) (GPhead w) ^ 2 ≤ d ^ 2 :=
        pow_le_pow_left₀ (dist_nonneg) hhor 2
      have hv2 : |z (Fin.last n) - w (Fin.last n)| ^ 2 ≤ d ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hvert 2
      have hs : 0 ≤ Real.sqrt 2 * d := mul_nonneg (Real.sqrt_nonneg _) hd
      apply (Real.sqrt_le_iff).2
      refine ⟨hs, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      linarith
  have hcost : ∀ (q d : ℝ) (N : ℕ), 0 < d → (N : ℝ) * d ≤ 2 →
    (N : ENNReal) * (ENNReal.ofReal (Real.sqrt 2 * d)) ^ (q + 1) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * (ENNReal.ofReal d) ^ q := by
      intro q d N hd hNd
      have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
      have hreal : (N : ℝ) * (Real.sqrt 2 * d) ^ (q + 1) ≤
          (2 * (Real.sqrt 2) ^ (q + 1)) * d ^ q := by
        rw [Real.mul_rpow hs.le hd.le, Real.rpow_add hd, Real.rpow_one]
        calc
          (N : ℝ) * (Real.sqrt 2 ^ (q + 1) * (d ^ q * d)) =
            ((N : ℝ) * d) * (Real.sqrt 2 ^ (q + 1) * d ^ q) := by ring
          _ ≤ 2 * (Real.sqrt 2 ^ (q + 1) * d ^ q) :=
            mul_le_mul_of_nonneg_right hNd (by positivity)
          _ = _ := by ring
      calc
        (N : ENNReal) * (ENNReal.ofReal (Real.sqrt 2 * d)) ^ (q + 1) =
          ENNReal.ofReal ((N : ℝ) * (Real.sqrt 2 * d) ^ (q + 1)) := by
            rw [ENNReal.ofReal_rpow_of_pos (mul_pos hs hd),
              ENNReal.ofReal_mul (Nat.cast_nonneg N)]
            simp
        _ ≤ ENNReal.ofReal ((2 * (Real.sqrt 2) ^ (q + 1)) * d ^ q) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_pos hd]
  intro hn q r ε hq hr hr1 hε
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (zero_le _) hq)
  have hq1 : 0 < q + 1 := by linarith
  obtain ⟨U, hU, hUpos, hUsum⟩ := h_T008 hn q r ε hq hr hr1 hε
  let d : ℕ → ℝ := fun i => (Metric.ediam (U i)).toReal
  let N : ℕ → ℕ := fun i => ⌈1 / d i⌉₊
  have hd0 (i : ℕ) : 0 ≤ d i := ENNReal.toReal_nonneg
  have hdeq (i : ℕ) : ENNReal.ofReal (d i) = Metric.ediam (U i) :=
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i))
  have hdr (i : ℕ) : d i ≤ r := ENNReal.toReal_le_of_le_ofReal hr.le (hU.2 i)
  have hdpos (i : ℕ) (hi : (U i).Nonempty) : 0 < d i :=
    ENNReal.toReal_pos (hUpos i hi).ne'
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i))
  have hN (i : ℕ) (hi : (U i).Nonempty) :
      0 < N i ∧ 1 / (N i : ℝ) ≤ d i ∧ (N i : ℝ) * d i ≤ 2 ∧
      ∀ t ∈ GPI, ∃ j : ℕ, j < N i ∧ (j : ℝ) / N i ≤ t ∧
        t ≤ ((j : ℝ) + 1) / N i :=
    hpartition (d i) (hdpos i hi) ((hdr i).trans hr1)
  let V : ℕ → ℕ → Set (GPEucl (n + 1)) := fun i j =>
    if j < N i ∧ (U i).Nonempty then
      {z | GPhead z ∈ U i ∧ (j : ℝ) / N i ≤ z (Fin.last n) ∧
        z (Fin.last n) ≤ ((j : ℝ) + 1) / N i}
    else ∅
  have hVdiam (i j : ℕ) :
      Metric.ediam (V i j) ≤ ENNReal.ofReal (Real.sqrt 2 * d i) := by
    by_cases hij : j < N i ∧ (U i).Nonempty
    · dsimp [V]
      rw [if_pos hij]
      exact hcylinder (U i) (d i) (hd0 i) (hdeq i).ge
        (N i) (hN i hij.2).1 (hN i hij.2).2.1 j
    · simp [V, hij]
  have hVzero (i j : ℕ) (hj : ¬ j < N i) : V i j = ∅ := by simp [V, hj]
  let W : ℕ → Set (GPEucl (n + 1)) := fun k =>
    V (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hz.1)
    have hine : (U i).Nonempty := ⟨GPhead z, hi⟩
    obtain ⟨j, hj, hleft, hright⟩ := (hN i hine).2.2.2 (z (Fin.last n)) hz.2
    apply Set.mem_iUnion.mpr
    refine ⟨Nat.pairEquiv (i,j), ?_⟩
    change z ∈ V (Nat.pairEquiv.symm (Nat.pairEquiv (i,j))).1
      (Nat.pairEquiv.symm (Nat.pairEquiv (i,j))).2
    simp only [Equiv.symm_apply_apply]
    simp only [V, if_pos ⟨hj, hine⟩, Set.mem_setOf_eq]
    exact ⟨hi, hleft, hright⟩
  · intro k
    exact (hVdiam _ _).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hdr _) (Real.sqrt_nonneg _)))
  · let C : ℝ := 2 * (Real.sqrt 2) ^ (q + 1)
    have hCpos : 0 < C := by dsimp [C]; positivity
    have hsum (i : ℕ) :
        (∑' j, (Metric.ediam (V i j)) ^ (q + 1)) ≤
        ENNReal.ofReal C * (Metric.ediam (U i)) ^ q := by
      by_cases hi : (U i).Nonempty
      · calc
          (∑' j, (Metric.ediam (V i j)) ^ (q + 1)) =
              ∑ j ∈ Finset.range (N i), (Metric.ediam (V i j)) ^ (q + 1) := by
            apply tsum_eq_sum
            intro j hj
            rw [hVzero i j (by simpa using hj), Metric.ediam_empty,
              ENNReal.zero_rpow_of_pos hq1]
          _ ≤ ∑ j ∈ Finset.range (N i),
              (ENNReal.ofReal (Real.sqrt 2 * d i)) ^ (q + 1) := by
            exact Finset.sum_le_sum fun j _ => ENNReal.rpow_le_rpow (hVdiam i j) hq1.le
          _ = (N i : ENNReal) * (ENNReal.ofReal (Real.sqrt 2 * d i)) ^ (q + 1) := by
            simp [nsmul_eq_mul]
          _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (d i)) ^ q :=
            hcost q (d i) (N i) (hdpos i hi) (hN i hi).2.2.1
          _ = _ := by rw [hdeq i]
      · have hv (j : ℕ) : V i j = ∅ := by simp [V, hi]
        simp only [hv, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hq1, tsum_zero]
        exact zero_le _
    have htotal : GPcost (q + 1) W ≤ ENNReal.ofReal C * GPcost q U := by
      calc
        GPcost (q + 1) W =
            ∑' i : ℕ, ∑' j : ℕ, (Metric.ediam (V i j)) ^ (q + 1) := by
          unfold GPcost
          change (∑' k : ℕ, (fun p : ℕ × ℕ => (Metric.ediam (V p.1 p.2)) ^ (q + 1))
            (Nat.pairEquiv.symm k)) = _
          rw [Nat.pairEquiv.symm.tsum_eq, ENNReal.tsum_prod']
        _ ≤ ∑' i : ℕ, ENNReal.ofReal C * (Metric.ediam (U i)) ^ q :=
          ENNReal.tsum_le_tsum hsum
        _ = _ := ENNReal.tsum_mul_left
    apply lt_of_le_of_lt htotal
    calc
      ENNReal.ofReal C * GPcost q U <
          ENNReal.ofReal C * ENNReal.ofReal ε :=
        ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hCpos))
          ENNReal.ofReal_ne_top hUsum
      _ = ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := by
        rw [← ENNReal.ofReal_mul hCpos.le]

#check @T009
#print axioms T009

end Translation
