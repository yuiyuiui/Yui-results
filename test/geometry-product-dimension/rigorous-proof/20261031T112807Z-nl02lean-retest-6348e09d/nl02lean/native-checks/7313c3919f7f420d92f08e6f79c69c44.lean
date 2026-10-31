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

theorem T002 (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) :
    dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤) := by
  classical
  -- The zero-dimensional case uses the empty-coordinate singleton cover.
  have hzero : n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0 := by
    classical
    intro hn
    subst n
    obtain ⟨x, hx⟩ := h_H002
    have he : E = {x} := by
      ext y
      constructor
      · intro _; exact Set.mem_singleton_iff.mpr (Subsingleton.elim y x)
      · intro hy; simpa only [Set.mem_singleton_iff.mp hy] using hx
    have hu : E = Set.univ := by
      ext y
      simp only [he, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim y x
    have hy : ∀ s : ℝ, 0 < s → yHaus s E = 0 := by
      intro s hs
      unfold yHaus
      refine le_antisymm (iSup₂_le fun δ hδ => ?_) bot_le
      let U : ℕ → Set (YEuclid 0) := fun _ => {x}
      have hc : E ⊆ ⋃ i, U i := by
        rw [he]
        exact Set.subset_iUnion U 0
      have hd : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ := by
        intro i; simp only [U, Metric.ediam_singleton, zero_le]
      have hcost : (∑' i, Metric.ediam (U i) ^ s) = 0 := by
        simp only [U, Metric.ediam_singleton, ENNReal.zero_rpow_of_pos hs, tsum_zero]
      have hle : yContent s δ E ≤ ∑' i, Metric.ediam (U i) ^ s := by
        unfold yContent
        exact iInf_le_of_le U (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))
      exact hle.trans_eq hcost
    have hdz : dimH E = 0 := by
      apply le_antisymm _ ((h_T001.1 0).1 E)
      by_contra! hpos
      obtain ⟨a, ha, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
      have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
      have hd := ((h_T001.1 0).2 E a har).2.2.2.1 (hy a har)
      rw [ENNReal.ofReal_coe_nnreal] at hd
      exact (not_lt_of_ge hd) had
    exact ⟨hu, ⟨x, he⟩, hdz⟩
  have hdim : dimH E ≤ (n : ℝ≥0∞) := by
    by_cases hn : n = 0
    · rw [(hzero hn).2.2, hn, Nat.cast_zero]
    · -- Coordinate boxes, a shrinking mesh of closed cubes, and the critical exponent.
      classical
      have hmesh : ∀ B : ℕ, 0 < B → MeasureTheory.Measure.hausdorffMeasure (n : ℝ)
          (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(B : ℝ)) B)) < ⊤ := by
        classical
        intro B hB
        open Filter in
          let γ := fun m : ℕ => Fin n → Fin (2 * B * m)
          let t : ∀ m : ℕ, γ m → Set (Fin n → ℝ) := fun m f =>
            Set.pi Set.univ (fun i => Set.Icc (-(B : ℝ) + f i / m) (-(B : ℝ) + (f i + 1) / m))
          have hd : ∀ᶠ m : ℕ in Filter.atTop, ∀ f : γ m, Metric.ediam (t m f) ≤ 1 / (m : ℝ≥0∞) := by
            refine Filter.eventually_atTop.mpr ⟨1, fun m hm f => ?_⟩
            refine Metric.ediam_pi_le_of_le fun i => ?_
            simp only [t, Real.ediam_Icc, add_div, add_sub_add_left_eq_sub, add_sub_cancel_left,
              ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hm), ENNReal.ofReal_one,
              ENNReal.ofReal_natCast, le_refl]
          have hc : ∀ᶠ m : ℕ in Filter.atTop,
              (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(B : ℝ)) B)) ⊆ ⋃ f : γ m, t m f := by
            refine Filter.eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
            have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
            intro x hx
            simp only [Set.mem_univ_pi, Set.mem_Ioo] at hx
            let f : γ m := fun i => ⟨⌊(x i + B) * m⌋₊, by
              apply (Nat.floor_lt (mul_nonneg (by linarith [(hx i).1]) hmpos.le)).mpr
              push_cast
              nlinarith [(hx i).2]⟩
            refine Set.mem_iUnion.mpr ⟨f, ?_⟩
            change ∀ i ∈ Set.univ, x i ∈ Set.Icc _ _
            intro i _
            constructor
            · have hfloor := Nat.floor_le (mul_nonneg (by linarith [(hx i).1] : 0 ≤ x i + B) hmpos.le)
              dsimp [f]
              have := (div_le_iff₀ hmpos).mpr hfloor
              nlinarith
            · have hfloor := (Nat.lt_floor_add_one ((x i + B) * m)).le
              dsimp [f]
              have := (le_div_iff₀ hmpos).mpr hfloor
              nlinarith
          have hcost : ∀ᶠ m : ℕ in Filter.atTop,
              (∑ f : γ m, Metric.ediam (t m f) ^ (n : ℝ)) ≤ ((2 * B : ℕ) : ℝ≥0∞) ^ n := by
            filter_upwards [hd, Filter.eventually_ge_atTop 1] with m hdm hm
            calc
              (∑ f : γ m, Metric.ediam (t m f) ^ (n : ℝ))
                  ≤ ∑ _f : γ m, (1 / (m : ℝ≥0∞)) ^ n := by
                apply Finset.sum_le_sum
                intro f _
                rw [ENNReal.rpow_natCast]
                exact pow_le_pow_left' (hdm f) n
              _ = ((2 * B : ℕ) : ℝ≥0∞) ^ n := by
                simp only [Finset.sum_const, Finset.card_univ, γ, Fintype.card_fun, Fintype.card_fin,
                  nsmul_eq_mul, Nat.cast_pow, Nat.cast_mul]
                rw [← mul_pow]
                have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
                rw [mul_one_div, ENNReal.mul_div_cancel_right hm0 (ENNReal.natCast_ne_top m)]
          have hlim : Filter.Tendsto (fun m : ℕ => 1 / (m : ℝ≥0∞)) Filter.atTop (nhds 0) := by
            simpa only [one_div] using ENNReal.tendsto_inv_nat_nhds_zero
          have hmes := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (n : ℝ)
            (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(B : ℝ)) B))
            (fun m : ℕ => 1 / (m : ℝ≥0∞)) hlim t hd hc
          apply lt_of_le_of_lt hmes
          have hl : Filter.liminf (fun m : ℕ => ∑ f : γ m, Metric.ediam (t m f) ^ (n : ℝ)) Filter.atTop ≤
              ((2 * B : ℕ) : ℝ≥0∞) ^ n := by
            calc
              _ ≤ Filter.liminf (fun _ : ℕ => ((2 * B : ℕ) : ℝ≥0∞) ^ n) Filter.atTop :=
                Filter.liminf_le_liminf hcost
              _ = _ := Filter.liminf_const _
          exact hl.trans_lt (by finiteness)

      obtain ⟨b, hb, hbound⟩ := h_H003.isBounded.exists_pos_norm_le
      obtain ⟨B, hbB⟩ := exists_nat_gt b
      have hB : 0 < B := Nat.cast_pos.mp (hb.trans hbB)
      let e : YEuclid n ≃L[ℝ] (Fin n → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
      let Q : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (-(B : ℝ)) B)
      have hsub : E ⊆ e.symm '' Q := by
        intro x hx
        refine ⟨e x, ?_, e.symm_apply_apply x⟩
        change ∀ i ∈ Set.univ, e x i ∈ Set.Ioo (-(B : ℝ)) B
        intro i _
        have hi : |x i| ≤ b := by
          simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans (hbound x hx)
        have his := abs_le.mp hi
        exact ⟨by change -(B : ℝ) < x i; linarith, by change x i < (B : ℝ); linarith⟩
      have hm : MeasureTheory.Measure.hausdorffMeasure (n : ℝ) Q < ⊤ := hmesh B hB
      have hL := PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)
      have himg : MeasureTheory.Measure.hausdorffMeasure (n : ℝ) (e.symm '' Q) < ⊤ := by
        apply lt_of_le_of_lt (hL.hausdorffMeasure_image_le (Nat.cast_nonneg n) Q)
        exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top) hm
      have hfinite : MeasureTheory.Measure.hausdorffMeasure (n : ℝ) E < ⊤ :=
        (measure_mono hsub).trans_lt himg
      have habove : ∀ a : ℝ≥0, (n : ℝ) < a → dimH E ≤ (a : ℝ≥0∞) := by
        intro a hna
        have ha : (0 : ℝ) < a := lt_of_le_of_lt (Nat.cast_nonneg n) hna
        have hz : MeasureTheory.Measure.hausdorffMeasure (a : ℝ) E = 0 :=
          (MeasureTheory.Measure.hausdorffMeasure_zero_or_top hna E).resolve_right hfinite.ne
        have hy : yHaus (a : ℝ) E = 0 := (((h_T001.1 n).2 E a ha).1).trans hz
        have hd := ((h_T001.1 n).2 E a ha).2.2.2.1 hy
        simpa only [ENNReal.ofReal_coe_nnreal] using hd
      by_contra! hdim
      obtain ⟨a, hna, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hdim
      have hnar : (n : ℝ) < a := by exact_mod_cast hna
      exact (not_lt_of_ge (habove a hnar)) had
  have hcontent : ∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤ := by
    classical
    intro s δ hs hδ
    obtain ⟨t, htE, htfin, htcover⟩ := h_H003.finite_cover_balls (half_pos hδ)
    letI : Fintype t := htfin.fintype
    let e := Fintype.equivFin t
    let U : ℕ → Set (YEuclid n) := fun i => if hi : i < Fintype.card t then Metric.ball (e.symm ⟨i, hi⟩).val (δ/2) else ∅
    have hc : E ⊆ ⋃ i, U i := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (htcover hx)
      let j := e ⟨y, hy⟩
      apply Set.mem_iUnion.mpr
      refine ⟨j.val, ?_⟩
      dsimp only [U]
      rw [dif_pos j.isLt]
      change x ∈ Metric.ball ((e.symm (e ⟨y, hy⟩)).val) (δ/2)
      simpa only [Equiv.symm_apply_apply] using hxy
    have hd : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ := by
      intro i
      dsimp only [U]
      split_ifs with hi
      · rw [← Metric.eball_ofReal]
        calc
          Metric.ediam _ ≤ 2 * ENNReal.ofReal (δ/2) := Metric.ediam_eball_le
          _ = ENNReal.ofReal δ := by
            calc
              (2 : ℝ≥0∞) * ENNReal.ofReal (δ/2) = ENNReal.ofReal (2 * (δ/2)) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
              _ = ENNReal.ofReal δ := by congr 1; ring
      · simp only [Metric.ediam_empty, zero_le]
    have hfin : (∑' i, Metric.ediam (U i) ^ s) < ⊤ := by
      rw [tsum_eq_sum (s := Finset.range (Fintype.card t)) (fun i hi => ?_)]
      · exact ENNReal.sum_lt_top.mpr (fun i hi => ENNReal.rpow_lt_top_of_nonneg hs.le (lt_of_le_of_lt (hd i) ENNReal.ofReal_lt_top).ne)
      · have hi' : ¬ i < Fintype.card t := by simpa only [Finset.mem_range] using hi
        simp only [U, dif_neg hi', Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]
    exact lt_of_le_of_lt (iInf_le_of_le U (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))) hfin
  exact ⟨hdim.trans_lt (ENNReal.natCast_lt_top n), (h_T001.1 n).1 E, hdim, hzero, hcontent⟩

#check @T002
#print axioms T002

end Translation
