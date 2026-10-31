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

theorem T012 (n : ℕ) (E : Set (GPEucl n)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T011 : ∀ (s δ ε : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → 0 < ε → GPcover (GPproduct E) δ V →
  (∀ i, Metric.ediam (GPhead '' V i) ≤ Metric.ediam (V i)) ∧
  ∃ a b : ℕ → ℝ, ∀ i, (V i).Nonempty →
    a i < b i ∧
    (∀ z ∈ V i, z (Fin.last n) ∈ Set.Ioo (a i) (b i)) ∧
    b i - a i ≤ (Metric.ediam (V i)).toReal +
      ε * (2 : ℝ) ^ (-(i : ℝ) - 1) /
        (1 + (Metric.ediam (V i)).toReal ^ s)) :
    ∀ (s δ : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → GPcover (GPproduct E) δ V →
  ∀ ε : ℝ, 0 < ε →
    GPcontent s δ E ≤ GPcost (s + 1) V + ENNReal.ofReal ε := by
  classical
  intro s δ V hs hδ hV ε hε
  obtain ⟨hproj, a, b, hab⟩ := h_T011 s δ ε V hs hδ hε hV
  let ρ : ℕ → ENNReal := fun i => Metric.ediam (V i)
  let J : ℕ → Set ℝ := fun i => Set.Ioo (a i) (b i)
  let c : ENNReal := GPcontent s δ E
  let g : ℕ → ℝ → ENNReal := fun i => (J i ∩ GPI).indicator (fun _ => ρ i ^ s)
  have hc : c < ⊤ := h_T005.2.2.2.1 s δ hs hδ
  have hρ : ∀ i, ρ i ≠ ⊤ := fun i =>
    (lt_of_le_of_lt (hV.2 i) ENNReal.ofReal_lt_top).ne
  have hconvert (i : ℕ) (p : ℝ) (hp : 0 ≤ p) :
      ENNReal.ofReal ((ρ i).toReal ^ p) = ρ i ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp,
      ENNReal.ofReal_toReal (hρ i)]
  have happ (x : GPEucl n) (t : ℝ) :
      GPhead (GPappend x t) = x ∧ GPappend x t (Fin.last n) = t := by
    constructor
    · ext i
      simp [GPhead, GPappend]
    · simp [GPappend]
  have hpoint : ∀ t : ℝ,
      GPI.indicator (fun _ => c) t ≤ ∑' i, g i t := by
    intro t
    by_cases ht : t ∈ GPI
    · rw [Set.indicator_of_mem ht]
      let U : ℕ → Set (GPEucl n) := fun i =>
        if t ∈ J i then GPhead '' V i else ∅
      have hU : GPcover E δ U := by
        constructor
        · intro x hx
          have hz : GPappend x t ∈ GPproduct E := by
            exact ⟨(happ x t).1.symm ▸ hx, (happ x t).2.symm ▸ ht⟩
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hz)
          have htJ : t ∈ J i := by
            simpa only [(happ x t).2] using (hab i ⟨_, hi⟩).2.1 _ hi
          apply Set.mem_iUnion.mpr
          refine ⟨i, ?_⟩
          dsimp [U]
          rw [if_pos htJ]
          exact ⟨GPappend x t, hi, (happ x t).1⟩
        · intro i
          dsimp [U]
          split_ifs with hi
          · exact (hproj i).trans (hV.2 i)
          · simp
      have hcost : c ≤ GPcost s U := by
        exact iInf_le_of_le U (iInf_le_of_le hU le_rfl)
      apply hcost.trans
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : t ∈ J i
      · simp only [U, if_pos hi]
        rw [show g i t = ρ i ^ s by
          exact Set.indicator_of_mem ⟨hi, ht⟩ _]
        exact ENNReal.rpow_le_rpow (hproj i) hs.le
      · simp [U, hi, g, Set.indicator_of_notMem, hs.ne', show t ∉ J i ∩ GPI from fun h => hi h.1]
    · rw [Set.indicator_of_notMem ht]
      exact zero_le _
  have hg (i : ℕ) : Measurable (g i) :=
    measurable_const.indicator (measurableSet_Ioo.inter measurableSet_Icc)
  have hint :
      c ≤ ∑' i, ρ i ^ s * MeasureTheory.volume (J i ∩ GPI) := by
    calc
      c = MeasureTheory.lintegral MeasureTheory.volume (GPI.indicator (fun _ => c)) := by
        rw [MeasureTheory.lintegral_indicator_const measurableSet_Icc]
        simp [GPI, Real.volume_Icc]
      _ ≤ MeasureTheory.lintegral MeasureTheory.volume (fun t => ∑' i, g i t) :=
        MeasureTheory.lintegral_mono hpoint
      _ = ∑' i, MeasureTheory.lintegral MeasureTheory.volume (g i) :=
        MeasureTheory.lintegral_tsum (fun i => (hg i).aemeasurable)
      _ = _ := by
        congr 1
        funext i
        exact MeasureTheory.lintegral_indicator_const
          (measurableSet_Ioo.inter measurableSet_Icc) _
  have hterm (i : ℕ) :
      ρ i ^ s * MeasureTheory.volume (J i ∩ GPI) ≤
        ρ i ^ (s+1) + ENNReal.ofReal ε *
          ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ) - 1)) := by
    by_cases hi : (V i).Nonempty
    · have hp : 0 ≤ (ρ i).toReal ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg _
      have hw : 0 ≤ (2 : ℝ) ^ (-(i : ℝ) - 1) := (Real.rpow_pos_of_pos (by norm_num) _).le
      have hf : (ρ i).toReal ^ s / (1 + (ρ i).toReal ^ s) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith)
      have herr : (ρ i).toReal ^ s *
          (ε * (2 : ℝ) ^ (-(i : ℝ) - 1) / (1 + (ρ i).toReal ^ s)) ≤
          ε * (2 : ℝ) ^ (-(i : ℝ) - 1) := by
        calc
          _ = (ε * (2 : ℝ) ^ (-(i : ℝ) - 1)) *
            ((ρ i).toReal ^ s / (1 + (ρ i).toReal ^ s)) := by ring
          _ ≤ (ε * (2 : ℝ) ^ (-(i : ℝ) - 1)) * 1 :=
            mul_le_mul_of_nonneg_left hf (mul_nonneg hε.le hw)
          _ = _ := mul_one _
      have hm := mul_le_mul_of_nonneg_left (hab i hi).2.2 hp
      have hreal : (ρ i).toReal ^ s * (b i - a i) ≤
          (ρ i).toReal ^ (s+1) + ε * (2 : ℝ) ^ (-(i : ℝ) - 1) := by
        rw [Real.rpow_add_of_nonneg ENNReal.toReal_nonneg hs.le (by norm_num),
          Real.rpow_one]
        dsimp [ρ] at *
        nlinarith
      calc
        _ ≤ ρ i ^ s * MeasureTheory.volume (J i) :=
          mul_le_mul_left' (MeasureTheory.measure_mono Set.inter_subset_left) _
        _ = ENNReal.ofReal ((ρ i).toReal ^ s * (b i - a i)) := by
          rw [show MeasureTheory.volume (J i) = ENNReal.ofReal (b i - a i) from Real.volume_Ioo,
            ENNReal.ofReal_mul hp, hconvert i s hs.le]
        _ ≤ ENNReal.ofReal ((ρ i).toReal ^ (s+1) +
            ε * (2 : ℝ) ^ (-(i : ℝ) - 1)) := ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
          rw [ENNReal.ofReal_add (Real.rpow_nonneg ENNReal.toReal_nonneg _)
            (mul_nonneg hε.le hw), hconvert i (s+1) (by linarith),
            ENNReal.ofReal_mul hε.le]
    · have hempty : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp [ρ, hempty, ENNReal.zero_rpow_of_pos hs]
  have hwtsum : (∑' i : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ) - 1))) = 1 := by
    have hw (i : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ) - 1)) =
        (2 : ENNReal) ^ (-1 - (i : ℤ)) := by
      rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← ENNReal.rpow_intCast]
      congr 1
      push_cast
      ring
    simpa only [hw] using ENNReal.tsum_two_zpow_neg_add_one
  calc
    GPcontent s δ E ≤ ∑' i, ρ i ^ s * MeasureTheory.volume (J i ∩ GPI) := hint
    _ ≤ ∑' i, (ρ i ^ (s+1) + ENNReal.ofReal ε *
        ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ) - 1))) := ENNReal.tsum_le_tsum hterm
    _ = GPcost (s+1) V + ENNReal.ofReal ε := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hwtsum, mul_one]
      rfl

#check @T012
#print axioms T012

end Translation
