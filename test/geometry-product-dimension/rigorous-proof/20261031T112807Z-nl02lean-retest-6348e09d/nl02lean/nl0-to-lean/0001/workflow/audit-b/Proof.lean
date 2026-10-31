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

theorem T001 (n : ℕ) (E : Set (YEuclid n))  :
    (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ := by
  classical
  have hEq : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (s : ℝ), 0 < s → yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A := by
    intro X _ _ _ A s hs
    classical
    have hcost (V : Set X) : (⨆ _ : V.Nonempty, Metric.ediam V ^ s) = Metric.ediam V ^ s := by
      by_cases hV : V.Nonempty
      · simp only [hV, iSup_pos]
      · have hVe : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hV
        simp [hVe, ENNReal.zero_rpow_of_pos hs]
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    simp_rw [hcost]
    let C : ℝ≥0∞ → ℝ≥0∞ := fun r =>
      ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
        ∑' i, (Metric.ediam (U i)) ^ s
    have hanti : Antitone C := by
      intro a b hab
      refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
      exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le (fun i => (hd i).trans hab) le_rfl))
    change (⨆ (δ : ℝ) (_ : 0 < δ), C (ENNReal.ofReal δ)) = ⨆ (r : ℝ≥0∞) (_ : 0 < r), C r
    apply le_antisymm
    · refine iSup_le fun δ => iSup_le fun hδ => ?_
      exact le_iSup_of_le (ENNReal.ofReal δ) (le_iSup_of_le (ENNReal.ofReal_pos.mpr hδ) le_rfl)
    · refine iSup_le fun r => iSup_le fun hr => ?_
      by_cases hrtop : r = ⊤
      · subst r
        exact (hanti (show ENNReal.ofReal (1 : ℝ) ≤ ⊤ from le_top)).trans
          (le_iSup_of_le (1 : ℝ) (le_iSup_of_le (by norm_num : (0 : ℝ) < 1) le_rfl))
      · have hrreal : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr) hrtop
        have hconv : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrtop
        calc
          C r = C (ENNReal.ofReal r.toReal) := congrArg C hconv.symm
          _ ≤ ⨆ (δ : ℝ) (_ : 0 < δ), C (ENNReal.ofReal δ) :=
            le_iSup_of_le r.toReal (le_iSup_of_le hrreal le_rfl)
  have hall : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X], yCritical X := by
    intro X _ _ _
    constructor
    · intro A
      exact zero_le
    · intro A s hs
      have heq : yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A := hEq X A s hs
      let a : NNReal := ⟨s, le_of_lt hs⟩
      have hcoe : ENNReal.ofReal s = (a : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal (le_of_lt hs)
      refine ⟨heq, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [heq]
        exact hausdorffMeasure_of_dimH_lt (s := A) (d := a) (by rwa [← hcoe])
      · intro h
        rw [heq]
        exact hausdorffMeasure_of_lt_dimH (s := A) (d := a) (by rwa [← hcoe])
      · intro h
        have hz : MeasureTheory.Measure.hausdorffMeasure s A = 0 := heq.symm.trans h
        have hnt : MeasureTheory.Measure.hausdorffMeasure s A ≠ ⊤ := by
          rw [hz]
          exact ENNReal.zero_ne_top
        have hd : dimH A ≤ (a : ℝ≥0∞) := dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := a) hnt
        rwa [← hcoe] at hd
      · intro h
        have ht : MeasureTheory.Measure.hausdorffMeasure s A = ⊤ := heq.symm.trans h
        have hd : (a : ℝ≥0∞) ≤ dimH A := le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := a) ht
        rwa [← hcoe] at hd
  exact ⟨fun m => hall (YEuclid m), hall ℝ⟩

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

theorem T004 (n : ℕ) (E : Set (YEuclid n))  :
    ∀ (δ : ℝ), 0 < δ → ∀ V : ℕ → Set ℝ, yCover δ yI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) := by
  classical
  intro δ hδ V hV
  have hbounded : ∀ i, Bornology.IsBounded (V i) := by
    intro i
    apply Metric.isBounded_iff_ediam_ne_top.mpr
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  have henlarge : ∀ (B : Set ℝ), Bornology.IsBounded B →
      ∀ (w : ℝ), 0 < w → ∃ J : Set ℝ,
        IsOpen J ∧ B ⊆ J ∧ volume J ≤ Metric.ediam B + ENNReal.ofReal w := by
    intro B hB w hw
    by_cases he : B = ∅
    · subst B
      exact ⟨∅, isOpen_empty, Subset.rfl, by simp⟩
    · let J := Set.Ioo (sInf B - w / 2) (sSup B + w / 2)
      refine ⟨J, isOpen_Ioo, ?_, ?_⟩
      · intro x hx
        have hx' := hB.subset_Icc_sInf_sSup hx
        change sInf B - w / 2 < x ∧ x < sSup B + w / 2
        constructor <;> linarith [hx'.1, hx'.2]
      · have hlen : 0 ≤ sSup B - sInf B :=
          sub_nonneg.mpr (Real.sInf_le_sSup B hB.bddBelow hB.bddAbove)
        change volume (Set.Ioo _ _) ≤ _
        rw [Real.volume_Ioo, Real.ediam_eq hB]
        have heq : sSup B + w / 2 - (sInf B - w / 2) =
            (sSup B - sInf B) + w := by ring
        rw [heq, ENNReal.ofReal_add hlen hw.le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hsum
  have hεreal : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  let w : ℕ → ℝ := fun i => (ε : ℝ) / 2 / 2 ^ i
  have hw : ∀ i, 0 < w i := by
    intro i
    dsimp [w]
    positivity
  have hJ : ∀ i : ℕ, ∃ J : Set ℝ, IsOpen J ∧ V i ⊆ J ∧
      volume J ≤ Metric.ediam (V i) + ENNReal.ofReal (w i) :=
    fun i => henlarge (V i) (hbounded i) (w i) (hw i)
  choose J hJopen hJsub hJvol using hJ
  have hcover : yI ⊆ ⋃ i, J i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, hJsub i hi⟩
  have hsumw : (∑' i : ℕ, ENNReal.ofReal (w i)) = (ε : ℝ≥0∞) := by
    dsimp [w]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_two' (ε : ℝ)), tsum_geometric_two',
      ENNReal.ofReal_coe_nnreal]
  calc
    (1 : ℝ≥0∞) = volume yI := by simp [yI, Real.volume_Icc]
    _ ≤ volume (⋃ i, J i) := measure_mono hcover
    _ ≤ ∑' i, volume (J i) := measure_iUnion_le J
    _ ≤ ∑' i, (Metric.ediam (V i) + ENNReal.ofReal (w i)) :=
      ENNReal.tsum_le_tsum hJvol
    _ = (∑' i, Metric.ediam (V i)) + (ε : ℝ≥0∞) := by
      rw [ENNReal.tsum_add, hsumw]

theorem T005 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T003 : dimH yI ≤ 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0)) (h_T004 : ∀ (δ : ℝ), 0 < δ → ∀ V : ℕ → Set ℝ, yCover δ yI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)) :
    dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤) := by
  have hcontent : ∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ →
      (ENNReal.ofReal δ) ^ (s - 1) ≤ yContent s δ yI := by
    intro s δ hs hs1 hδ
    unfold yContent
    refine le_iInf fun V => le_iInf fun hV => le_iInf fun hd => ?_
    have hsum : (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) :=
      h_T004 δ hδ V ⟨hV, hd⟩
    calc
      (ENNReal.ofReal δ) ^ (s - 1) =
          (ENNReal.ofReal δ) ^ (s - 1) * 1 := (mul_one _).symm
      _ ≤ (ENNReal.ofReal δ) ^ (s - 1) * ∑' i, Metric.ediam (V i) :=
        mul_le_mul_left' hsum _
      _ = ∑' i, (ENNReal.ofReal δ) ^ (s - 1) * Metric.ediam (V i) :=
        ENNReal.tsum_mul_left.symm
      _ ≤ ∑' i, (Metric.ediam (V i)) ^ s := by
        apply ENNReal.tsum_le_tsum
        intro i
        by_cases hz : Metric.ediam (V i) = 0
        · simp [hz, ENNReal.zero_rpow_of_pos hs]
        have ht : Metric.ediam (V i) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hd i)
        have hp : (ENNReal.ofReal δ) ^ (s - 1) ≤ (Metric.ediam (V i)) ^ (s - 1) := by
          have he : s - 1 = -(1 - s) := by ring
          rw [he, ENNReal.rpow_neg, ENNReal.rpow_neg]
          exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow (hd i) (by linarith))
        calc
          _ ≤ (Metric.ediam (V i)) ^ (s - 1) * Metric.ediam (V i) :=
            mul_le_mul_right' hp _
          _ = (Metric.ediam (V i)) ^ s := by
            calc
              _ = (Metric.ediam (V i)) ^ (s - 1) *
                  (Metric.ediam (V i)) ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
              _ = (Metric.ediam (V i)) ^ ((s - 1) + 1) :=
                (ENNReal.rpow_add _ _ hz ht).symm
              _ = (Metric.ediam (V i)) ^ s := by congr 1; ring
  have hinf : ∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤ := by
    intro s hs hs1
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    have he : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), (r : ℝ) ≤ δ ^ (s - 1) :=
      (tendsto_rpow_neg_nhdsGT_zero (by linarith : s - 1 < 0)).eventually
        (Filter.eventually_ge_atTop (r : ℝ))
    obtain ⟨δ, hb, hδ⟩ := (he.and self_mem_nhdsWithin).exists
    have hr : (r : ℝ≥0∞) ≤ (ENNReal.ofReal δ) ^ (s - 1) := by
      rw [ENNReal.ofReal_rpow_of_pos hδ]
      have hconv : ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞) := by simp
      rw [← hconv]
      exact ENNReal.ofReal_le_ofReal hb
    exact hr.trans ((hcontent s δ hs hs1 hδ).trans
      (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)))
  have hdim : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH yI := by
    intro s hs hs1
    exact (h_T001.2.2 yI s hs).2.2.2.2 (hinf s hs hs1)
  have hlower : (1 : ℝ≥0∞) ≤ dimH yI := by
    apply ENNReal.le_of_forall_lt_one_mul_le
    intro a ha
    rw [mul_one]
    by_cases hz : a = 0
    · simp [hz]
    have ht : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha.le
    have hp : 0 < a.toReal := ENNReal.toReal_pos hz ht
    have h1 : a.toReal < 1 := by
      have hh := (ENNReal.toReal_lt_toReal ht ENNReal.one_ne_top).2 ha
      simpa using hh
    have hh := hdim a.toReal hp h1
    rwa [ENNReal.ofReal_toReal ht] at hh
  exact ⟨le_antisymm h_T003.1 hlower, h_T003.2, hinf⟩

theorem T006 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T005 : dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤)) :
    n = 0 → dimH (yProd E) ≤ dimH E + 1 := by
  intro hn
  subst n
  rcases h_T002.2.2.2.1 rfl with ⟨hE, ⟨x, hx⟩, hD⟩
  rw [hD]
  rw [zero_add (1 : ℝ≥0∞)]
  have hlast (t : ℝ) : yJoin x t (Fin.last 0) = t := by
    exact Fin.snoc_last (α := fun _ : Fin 1 => ℝ) (x := t) (p := fun i => x i)
  have hf : Isometry (yJoin x) := by
    apply Isometry.of_dist_eq
    intro t u
    have hsq : dist (yJoin x t) (yJoin x u) ^ 2 = dist t u ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_one]
      change dist (yJoin x t (Fin.last 0)) (yJoin x u (Fin.last 0)) ^ 2 = _
      rw [hlast, hlast]
    have h₁ : 0 ≤ dist (yJoin x t) (yJoin x u) := dist_nonneg
    have h₂ : 0 ≤ dist t u := dist_nonneg
    nlinarith
  have himg : yJoin x '' yI = yProd E := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      constructor
      · rw [hE]
        trivial
      · change yJoin x t (Fin.last 0) ∈ yI
        rwa [hlast]
    · intro z hz
      refine ⟨yVert z, hz.2, ?_⟩
      ext i
      have hi : i = Fin.last 0 := by
        apply Fin.ext
        have hi' := i.isLt
        simp only [Fin.val_last]
        omega
      rw [hi, hlast]
      rfl
  have hcontent (s δ : ℝ) : yContent s δ (yProd E) ≤ yContent s δ yI := by
    rw [← himg]
    unfold yContent
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    refine iInf_le_of_le (fun i => yJoin x '' U i) ?_
    have hcover : yJoin x '' yI ⊆ ⋃ i, yJoin x '' U i := by
      rintro z ⟨t, ht, rfl⟩
      rcases Set.mem_iUnion.mp (hU ht) with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨t, hi, rfl⟩⟩
    refine iInf_le_of_le hcover ?_
    have hdiam : ∀ i, Metric.ediam (yJoin x '' U i) ≤ ENNReal.ofReal δ := by
      intro i
      rw [hf.ediam_image]
      exact hd i
    refine iInf_le_of_le hdiam ?_
    simp only [hf.ediam_image, le_refl]
  have hbound (a : ℝ) (ha : 1 < a) : dimH (yProd E) ≤ ENNReal.ofReal a := by
    have hapos : 0 < a := lt_trans zero_lt_one ha
    have hzero : yHaus a (yProd E) = 0 := by
      apply le_antisymm ?_ bot_le
      calc
        yHaus a (yProd E) ≤ yHaus a yI := by
          unfold yHaus
          refine iSup_le fun δ => iSup_le fun hδ => ?_
          exact (hcontent a δ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
        _ = 0 := h_T005.2.1 a ha
    exact ((h_T001.1 (0+1)).2 (yProd E) a hapos).2.2.2.1 hzero
  by_contra hn
  have hd : (1 : ℝ≥0∞) < dimH (yProd E) := lt_of_not_ge hn
  rcases ENNReal.lt_iff_exists_real_btwn.mp hd with ⟨a, ha0, ha, had⟩
  have hreal : 1 < a := ENNReal.one_lt_ofReal.mp ha
  exact (not_lt_of_ge (hbound a hreal)) had

theorem T007 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) :
    1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε := by
  classical
  intro hn q r ε hq hdim hr hr1 hε
  have hz : yHaus q E = 0 := ((h_T001.1 n).2 E q hq).2.1 hdim
  have hle : yContent q r E ≤ yHaus q E := by
    unfold yHaus
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hc : yContent q r E = 0 := le_antisymm (hle.trans_eq hz) zero_le
  have hl : yContent q r E < ENNReal.ofReal (ε / 2) := by
    rw [hc]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hex : ∃ W : ℕ → Set (YEuclid n),
      yCover r E W ∧ yCost q W < ENNReal.ofReal (ε / 2) := by
    simpa only [yContent, iInf_lt_iff, yCover, yCost,
      exists_prop, exists_and_left, and_assoc] using hl
  obtain ⟨W, hW, hcost⟩ := hex
  let a : ℕ → ℝ := fun i => ε / 8 * (1 / 2 : ℝ) ^ i
  have ha : ∀ i, 0 < a i := fun i => by dsimp [a]; positivity
  have hsmall : ∀ i : ℕ, ∃ b : ℝ, 0 < b ∧ b ≤ r ∧
      (ENNReal.ofReal b) ^ q ≤ ENNReal.ofReal (a i) := by
    intro i
    let b := min (r / 2) ((a i) ^ q⁻¹)
    have hb : 0 < b := lt_min (by positivity) (Real.rpow_pos_of_pos (ha i) _)
    refine ⟨b, hb, (min_le_left _ _).trans (by linarith), ?_⟩
    rw [ENNReal.ofReal_rpow_of_nonneg hb.le hq.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      b ^ q ≤ ((a i) ^ q⁻¹) ^ q :=
        Real.rpow_le_rpow hb.le (min_le_right _ _) hq.le
      _ = a i := Real.rpow_inv_rpow (ha i).le hq.ne'
  choose b hb using hsmall
  have hball : ∀ (x : YEuclid n) (d : ℝ), 0 < d →
      Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal d := by
    intro x d hd
    letI : NeZero n := ⟨by omega⟩
    have hfin : Metric.ediam (Metric.ball x (d / 2)) ≠ ⊤ :=
      Metric.isBounded_ball.ediam_ne_top
    calc
      Metric.ediam (Metric.ball x (d / 2)) =
          ENNReal.ofReal (Metric.diam (Metric.ball x (d / 2))) :=
        (ENNReal.ofReal_toReal hfin).symm
      _ = ENNReal.ofReal d := by
        rw [Metric.diam_ball_eq x (by positivity)]
        congr 1
        ring
  let U : ℕ → Set (YEuclid n) := fun i =>
    if h : (W i).Nonempty ∧ Metric.ediam (W i) = 0 then
      Metric.ball h.1.choose (b i / 2)
    else W i
  have hU : ∀ i, W i ⊆ U i ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r ∧
      ((U i).Nonempty → 0 < Metric.ediam (U i)) ∧
      (Metric.ediam (U i)) ^ q ≤
        (Metric.ediam (W i)) ^ q + ENNReal.ofReal (a i) := by
    intro i
    dsimp only [U]
    split_ifs with hi
    · have hd := hball hi.1.choose (b i) (hb i).1
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        have heq : x = hi.1.choose :=
          (Metric.ediam_eq_zero_iff.mp hi.2) hx hi.1.choose_spec
        rw [heq]
        exact Metric.mem_ball_self (half_pos (hb i).1)
      · rw [hd]
        exact ENNReal.ofReal_le_ofReal (hb i).2.1
      · intro _
        rw [hd]
        exact ENNReal.ofReal_pos.mpr (hb i).1
      · rw [hd]
        exact (hb i).2.2.trans (le_add_left le_rfl)
    · refine ⟨Subset.rfl, hW.2 i, ?_, le_add_right le_rfl⟩
      intro hne
      exact pos_iff_ne_zero.mpr (fun heq => hi ⟨hne, heq⟩)
  have hsum : (∑' i : ℕ, ENNReal.ofReal (a i)) = ENNReal.ofReal (ε / 4) := by
    have hs : Summable (fun i : ℕ => ε / 8 * (1 / 2 : ℝ) ^ i) :=
      summable_geometric_two.mul_left (ε / 8)
    dsimp only [a]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs,
      tsum_mul_left, tsum_geometric_two]
    congr 1
    ring
  refine ⟨U, ⟨?_, fun i => (hU i).2.1⟩, fun i => (hU i).2.2.1, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, (hU i).1 hi⟩
  · calc
      yCost q U ≤ ∑' i, ((Metric.ediam (W i)) ^ q + ENNReal.ofReal (a i)) :=
        ENNReal.tsum_le_tsum fun i => (hU i).2.2.2
      _ = yCost q W + ENNReal.ofReal (ε / 4) := by
        rw [ENNReal.tsum_add, hsum]
        rfl
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) :=
        add_le_add hcost.le le_rfl
      _ = ENNReal.ofReal (ε / 2 + ε / 4) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

theorem T008 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T007 : 1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε) :
    1 ≤ n → dimH (yProd E) ≤ dimH E + 1 := by
  classical
  have hinterval : ∀ a : ℝ, 0 < a → a ≤ 1 → ∃ (N : ℕ) (J : Fin N → Set ℝ), 0 < N ∧ (N : ℝ) ≤ 2 / a ∧ (∀ t ∈ yI, ∃ j, t ∈ J j) ∧ ∀ j s, s ∈ J j → ∀ t, t ∈ J j → dist s t ≤ a := by
    intro a ha ha1
    let N : ℕ := ⌈1 / a⌉₊
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hNa : (N : ℝ) ≤ 2 / a := by
      have hc : (N : ℝ) < 1 / a + 1 := Nat.ceil_lt_add_one (by positivity)
      have h1 : (1 : ℝ) ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha1)
      rw [show 2 / a = 1 / a + 1 / a by ring]
      linarith
    have hlen : 1 / (N : ℝ) ≤ a := by
      have hc : 1 / a ≤ (N : ℝ) := Nat.le_ceil _
      apply (div_le_iff₀ hNr).mpr
      have := (div_le_iff₀ ha).mp hc
      nlinarith
    let J : Fin N → Set ℝ := fun j => Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    refine ⟨N, J, hN, hNa, ?_, ?_⟩
    · intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      by_cases ht : t = 1
      · let j : Fin N := ⟨N-1, by omega⟩
        refine ⟨j, ?_⟩
        change (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N
        have hj : (j : ℝ) + 1 = (N : ℝ) := by
          dsimp [j]
          norm_cast
          omega
        rw [ht]
        constructor
        · apply (div_le_iff₀ hNr).mpr
          linarith
        · rw [hj, div_self (ne_of_gt hNr)]
      · have htlt : t < 1 := lt_of_le_of_ne ht1 ht
        let j : Fin N := ⟨⌊t * N⌋₊, (Nat.floor_lt (mul_nonneg ht0 hNr.le)).mpr (by nlinarith)⟩
        refine ⟨j, ?_⟩
        change (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N
        constructor
        · apply (div_le_iff₀ hNr).mpr
          exact Nat.floor_le (mul_nonneg ht0 hNr.le)
        · apply (le_div_iff₀ hNr).mpr
          exact (Nat.lt_floor_add_one (t * N)).le
    · intro j s hs t ht
      have hst : |s-t| ≤ 1 / (N : ℝ) := by
        change _ ≤ s ∧ s ≤ _ at hs
        change _ ≤ t ∧ t ≤ _ at ht
        simp only [add_div] at hs ht
        rw [abs_le]
        constructor <;> linarith
      exact (by simpa [Real.dist_eq] using hst : dist s t ≤ 1 / (N : ℝ)).trans hlen
  have hcountable : ∀ (ι : Type) [Countable ι] (s δ : ℝ) (A : Set (YEuclid (n+1))) (V : ι → Set (YEuclid (n+1))), 0 < s → A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → yContent s δ A ≤ ∑' i, Metric.ediam (V i) ^ s := by
    intro ι hι s δ A V hs hcov hdiam
    letI : Encodable ι := Encodable.ofCountable ι
    let U : ℕ → Set (YEuclid (n+1)) := fun k => ⋃ b ∈ Encodable.decode₂ ι k, V b
    have hUcov : A ⊆ ⋃ k, U k := by
      simpa only [U, Encodable.iUnion_decode₂] using hcov
    have hUdiam : ∀ k, Metric.ediam (U k) ≤ ENNReal.ofReal δ := by
      intro k
      change Metric.ediam (⋃ b ∈ Encodable.decode₂ ι k, V b) ≤ ENNReal.ofReal δ
      apply Encodable.iUnion_decode₂_cases (C := fun B => Metric.ediam B ≤ ENNReal.ofReal δ)
      · simp
      · exact hdiam
    have hle : yContent s δ A ≤ ∑' k, Metric.ediam (U k) ^ s := by
      unfold yContent
      exact iInf_le_of_le U (iInf_le_of_le hUcov (iInf_le_of_le hUdiam le_rfl))
    refine hle.trans_eq ?_
    exact tsum_iUnion_decode₂ (fun B : Set (YEuclid (n+1)) => Metric.ediam B ^ s) (by simp [ENNReal.zero_rpow_of_pos hs]) V
  have hcostlemma : ∀ (q a : ℝ) (N : ℕ), 0 < q → 0 < a → (N : ℝ) ≤ 2 / a → (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * a)) ^ (q+1) ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * (ENNReal.ofReal a) ^ q := by
    intro q a N hq ha hN
    have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hreal : (N : ℝ) * (Real.sqrt 2 * a) ^ (q+1) ≤ (2 * (Real.sqrt 2) ^ (q+1)) * a ^ q := by
      rw [Real.mul_rpow hsq.le ha.le, Real.rpow_add ha, Real.rpow_one]
      have hNa : (N : ℝ) * a ≤ 2 := (le_div_iff₀ ha).mp hN
      calc
        (N : ℝ) * ((Real.sqrt 2) ^ (q+1) * (a ^ q * a)) =
            ((Real.sqrt 2) ^ (q+1) * a ^ q) * ((N : ℝ) * a) := by ring
        _ ≤ ((Real.sqrt 2) ^ (q+1) * a ^ q) * 2 := mul_le_mul_of_nonneg_left hNa (by positivity)
        _ = _ := by ring
    have hc : 0 ≤ 2 * (Real.sqrt 2) ^ (q+1) := by positivity
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos (mul_pos hsq ha),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_rpow_of_pos ha,
      ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal hreal
  have hgeo : ∀ (U : Set (YEuclid n)) (J : Set ℝ) (a : ℝ), 0 ≤ a → Metric.ediam U ≤ ENNReal.ofReal a → (∀ s ∈ J, ∀ t ∈ J, dist s t ≤ a) → Metric.ediam {z : YEuclid (n+1) | yHoriz z ∈ U ∧ yVert z ∈ J} ≤ ENNReal.ofReal (Real.sqrt 2 * a) := by
    intro U J a ha hd hJ
    apply Metric.ediam_le_of_forall_dist_le
    intro z hz w hw
    have hh : dist (yHoriz z) (yHoriz w) ≤ a := by
      exact (edist_le_ofReal ha).mp ((Metric.edist_le_ediam_of_mem hz.1 hw.1).trans hd)
    have hv : dist (yVert z) (yVert w) ≤ a := hJ _ hz.2 _ hw.2
    have heq : dist z w ^ 2 = dist (yHoriz z) (yHoriz w) ^ 2 + dist (yVert z) (yVert w) ^ 2 := by
      rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_castSucc, PiLp.dist_sq_eq_of_L2]
      rfl
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsq0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hh0 : 0 ≤ dist (yHoriz z) (yHoriz w) := dist_nonneg
    have hv0 : 0 ≤ dist (yVert z) (yVert w) := dist_nonneg
    have hd0 : 0 ≤ dist z w := dist_nonneg
    apply (sq_le_sq₀ hd0 (mul_nonneg hsq0 ha)).mp
    rw [mul_pow, hsq, heq]
    nlinarith [mul_self_le_mul_self hh0 hh, mul_self_le_mul_self hv0 hv]
  have hjoin : (∀ (x : YEuclid n) (t : ℝ), yHoriz (yJoin x t) = x ∧ yVert (yJoin x t) = t) ∧ (∀ z : YEuclid (n+1), yJoin (yHoriz z) (yVert z) = z) := by
    constructor
    · intro x t
      constructor
      · ext i
        simp [yHoriz, yJoin]
      · simp [yVert, yJoin]
    · intro z
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [yJoin, yVert]
      · simp [yJoin, yHoriz]
  have himage : ∀ (U : Set (YEuclid n)) (J : Set ℝ), Set.image2 (@yJoin n) U J = {z : YEuclid (n+1) | yHoriz z ∈ U ∧ yVert z ∈ J} := by
    intro U J
    ext z
    constructor
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨by simpa only [(hjoin.1 x t).1] using hx, by simpa only [(hjoin.1 x t).2] using ht⟩
    · intro hz
      exact ⟨yHoriz z, hz.1, yVert z, hz.2, hjoin.2 z⟩
  have hzero : ∀ (X : ℝ≥0∞) (C : ℝ), 0 < C → (∀ ε : ℝ, 0 < ε → X ≤ ENNReal.ofReal C * ENNReal.ofReal ε) → X = 0 := by
    intro X C hC h
    apply le_antisymm _ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hηr : (0 : ℝ) < η := hη
    have he : 0 < (η : ℝ) / C := div_pos hηr hC
    have hb := h ((η : ℝ) / C) he
    rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne'] at hb
    simpa using hb
  have hlimit : ∀ (Y D : ℝ≥0∞), D ≠ ⊤ → (∀ q : ℝ, 0 < q → D < ENNReal.ofReal q → Y ≤ ENNReal.ofReal (q+1)) → Y ≤ D+1 := by
    intro Y D hD h
    have heq : ENNReal.ofReal D.toReal = D := ENNReal.ofReal_toReal hD
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hηr : (0 : ℝ) < η := hη
    have hq : 0 < D.toReal + (η : ℝ) := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hηr
    have hlt : D < ENNReal.ofReal (D.toReal + (η : ℝ)) := by
      nth_rw 1 [← heq]
      apply (ENNReal.ofReal_lt_ofReal_iff hq).mpr
      linarith
    have hb := h (D.toReal + (η : ℝ)) hq hlt
    rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg η.coe_nonneg) (by norm_num),
      ENNReal.ofReal_add ENNReal.toReal_nonneg η.coe_nonneg, heq,
      ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal] at hb
    simpa only [add_assoc, add_comm, add_left_comm] using hb
  have hbound : 1 ≤ n → ∀ q δ ε : ℝ, 0 < q → dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε → yContent (q+1) δ (yProd E) ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal ε := by
    intro hn q δ ε hq hD hδ hε
    have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hsq)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrδ : Real.sqrt 2 * r ≤ δ := by
      have h := min_le_right (1 : ℝ) (δ / Real.sqrt 2)
      have hh := (le_div_iff₀ hsq).mp h
      simpa only [mul_comm] using hh
    obtain ⟨U, hU, hpos, hcost⟩ := h_T007 hn q r ε hq hD hr hr1 hε
    have hfin : ∀ i, Metric.ediam (U i) ≠ ⊤ := fun i =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i)
    let K := {i : ℕ // (U i).Nonempty}
    let a : K → ℝ := fun i => (Metric.ediam (U i)).toReal
    have ha : ∀ i, 0 < a i := fun i => ENNReal.toReal_pos (ne_of_gt (hpos i i.property)) (hfin i)
    have har : ∀ i, a i ≤ r := fun i => ENNReal.toReal_le_of_le_ofReal hr.le (hU.2 i)
    have ha1 : ∀ i, a i ≤ 1 := fun i => (har i).trans hr1
    have heq : ∀ i : K, ENNReal.ofReal (a i) = Metric.ediam (U i) := fun i =>
      ENNReal.ofReal_toReal (hfin i)
    choose N J hN hNa hJcov hJdiam using fun i : K => hinterval (a i) (ha i) (ha1 i)
    let V : (Σ i : K, Fin (N i)) → Set (YEuclid (n+1)) :=
      fun p => Set.image2 yJoin (U p.1) (J p.1 p.2)
    have hV : ∀ p, Metric.ediam (V p) ≤ ENNReal.ofReal (Real.sqrt 2 * a p.1) := by
      intro p
      simpa only [V, himage] using hgeo (U p.1) (J p.1 p.2) (a p.1) (ha p.1).le (heq p.1).ge (hJdiam p.1 p.2)
    have hVδ : ∀ p, Metric.ediam (V p) ≤ ENNReal.ofReal δ := by
      intro p
      exact (hV p).trans (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (har p.1) hsq.le).trans hrδ))
    have hcov : yProd E ⊆ ⋃ p, V p := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hz.1)
      let k : K := ⟨i, ⟨yHoriz z, hi⟩⟩
      obtain ⟨j, hj⟩ := hJcov k (yVert z) hz.2
      apply Set.mem_iUnion.mpr
      refine ⟨⟨k,j⟩, ?_⟩
      change z ∈ Set.image2 yJoin (U k) (J k j)
      rw [himage]
      exact ⟨hi, hj⟩
    have hs : 0 < q+1 := by linarith
    calc
      yContent (q+1) δ (yProd E) ≤ ∑' p, Metric.ediam (V p) ^ (q+1) :=
        hcountable _ _ _ _ V hs hcov hVδ
      _ ≤ ∑' p : (Σ i : K, Fin (N i)), (ENNReal.ofReal (Real.sqrt 2 * a p.1)) ^ (q+1) :=
        ENNReal.tsum_le_tsum fun p => ENNReal.rpow_le_rpow (hV p) hs.le
      _ = ∑' i : K, (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * a i)) ^ (q+1) := by
        rw [ENNReal.tsum_sigma' (fun p : (Σ i : K, Fin (N i)) => (ENNReal.ofReal (Real.sqrt 2 * a p.1)) ^ (q+1))]
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑' i : K, ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * (Metric.ediam (U i)) ^ q := by
        apply ENNReal.tsum_le_tsum
        intro i
        simpa only [heq i] using hcostlemma q (a i) (N i) hq (ha i) (hNa i)
      _ = ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ∑' i : K, (Metric.ediam (U i)) ^ q :=
        ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * yCost q U := by
        apply mul_le_mul_left'
        exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun i => Metric.ediam (U i) ^ q)
      _ ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal ε :=
        mul_le_mul_left' hcost.le _
  intro hn
  apply hlimit (dimH (yProd E)) (dimH E) h_T002.1.ne
  intro q hq hD
  have hs : 0 < q+1 := by linarith
  have hhaus : yHaus (q+1) (yProd E) = 0 := by
    apply le_antisymm _ bot_le
    unfold yHaus
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    have hC : 0 < 2 * (Real.sqrt 2) ^ (q+1) := by
      apply mul_pos (by norm_num)
      exact Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (by norm_num)) _
    have hz : yContent (q+1) δ (yProd E) = 0 :=
      hzero _ _ hC (fun ε hε => hbound hn q δ ε hq hD hδ hε)
    exact hz.le
  exact ((h_T001.1 (n+1)).2 (yProd E) (q+1) hs).2.2.2.1 hhaus

theorem T009 (n : ℕ) (E : Set (YEuclid n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (yProd E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → dimH (yProd E) ≤ dimH E + 1) :
    dimH (yProd E) ≤ dimH E + 1 ∧ dimH (yProd E) < ⊤ := by
  have hbound : dimH (yProd E) ≤ dimH E + 1 := by
    by_cases hn : n = 0
    · exact h_T006 hn
    · exact h_T008 (by omega)
  refine ⟨hbound, lt_of_le_of_lt hbound ?_⟩
  exact ENNReal.add_lt_top.mpr ⟨h_T002.1, by simp⟩

theorem T010 (n : ℕ) (E : Set (YEuclid n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEuclid (n+1)), yCover δ (yProd E) V → ∀ ε : ℝ, 0 < ε → yContent s δ E ≤ yCost (s+1) V + ENNReal.ofReal ε := by
  classical
  have hproj : ∀ z w : YEuclid (n+1),
      edist (yHoriz z) (yHoriz w) ≤ edist z w ∧
      edist (yVert z) (yVert w) ≤ edist z w := by
      intro z w
      have hd : dist z w ^ 2 =
          dist (yHoriz z) (yHoriz w) ^ 2 + dist (yVert z) (yVert w) ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
        rfl
      constructor <;>
        simp only [edist_dist, ENNReal.ofReal_le_ofReal_iff (dist_nonneg)] <;>
        nlinarith [sq_nonneg (dist (yHoriz z) (yHoriz w)), sq_nonneg (dist (yVert z) (yVert w)),
          dist_nonneg (x := z) (y := w), dist_nonneg (x := yHoriz z) (y := yHoriz w),
          dist_nonneg (x := yVert z) (y := yVert w)]

  have hinter : ∀ (B : Set ℝ) (d : ℝ≥0∞), d ≠ ⊤ → Metric.ediam B ≤ d →
      ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ B ⊆ J ∧ volume J ≤ d + ENNReal.ofReal η := by
      intro B d hd hB η hη
      classical
      by_cases hne : B.Nonempty
      · have hb : Bornology.IsBounded B :=
          Metric.isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top hd hB)
        refine ⟨Ioo (sInf B - η/2) (sSup B + η/2), isOpen_Ioo, ?_, ?_⟩
        · intro t ht
          have ht' := hb.subset_Icc_sInf_sSup ht
          constructor <;> dsimp at * <;> linarith [ht'.1, ht'.2]
        · rw [Real.volume_Ioo]
          have he : sSup B + η/2 - (sInf B - η/2) = (sSup B - sInf B) + η := by ring
          rw [he]
          exact (ENNReal.ofReal_add_le).trans (add_le_add (by simpa [Real.ediam_eq hb] using hB) le_rfl)
      · refine ⟨∅, isOpen_empty, ?_, ?_⟩
        · simpa [Set.not_nonempty_iff_eq_empty.mp hne]
        · simp
  have hnum : ∀ (a : ℝ≥0∞), a ≠ ⊤ → ∀ e : ℝ, 0 ≤ e →
      a * ENNReal.ofReal (e / (1 + a.toReal)) ≤ ENNReal.ofReal e := by
      intro a ha e he
      have hn : 0 ≤ a.toReal := ENNReal.toReal_nonneg
      have hd : 0 < 1 + a.toReal := by positivity
      calc
        a * ENNReal.ofReal (e / (1 + a.toReal)) =
            ENNReal.ofReal (a.toReal * (e / (1 + a.toReal))) := by
          rw [ENNReal.ofReal_mul hn, ENNReal.ofReal_toReal ha]
        _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ hd).mpr
          nlinarith)

  have hjoin : ∀ (x : YEuclid n) (t : ℝ),
      yHoriz (yJoin x t) = x ∧ yVert (yJoin x t) = t := by
    intro x t
    constructor
    · ext i
      simp [yHoriz, yJoin]
    · simp [yVert, yJoin]
  have hrejoin : ∀ z : YEuclid (n+1), yJoin (yHoriz z) (yVert z) = z := by
    intro z
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [yJoin, yVert]
    · simp [yJoin, yHoriz]
  intro s δ hs hδ V hV ε hε
  let ρ : ℕ → ℝ≥0∞ := fun i => Metric.ediam (V i)
  let A : ℕ → Set (YEuclid n) := fun i => yHoriz '' V i
  let B : ℕ → Set ℝ := fun i => yVert '' V i
  let c := yContent s δ E
  have hc : c < ⊤ := h_T002.2.2.2.2 s δ hs hδ
  have hρ : ∀ i, ρ i ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  have hA : ∀ i, Metric.ediam (A i) ≤ ρ i := by
    intro i
    exact Metric.ediam_image_le_iff.mpr (fun z hz w hw =>
      (hproj z w).1.trans (Metric.edist_le_ediam_of_mem hz hw))
  have hB : ∀ i, Metric.ediam (B i) ≤ ρ i := by
    intro i
    exact Metric.ediam_image_le_iff.mpr (fun z hz w hw =>
      (hproj z w).2.trans (Metric.edist_le_ediam_of_mem hz hw))
  let a : ℕ → ℝ≥0∞ := fun i => ρ i ^ s
  have ha : ∀ i, a i ≠ ⊤ := fun i => ENNReal.rpow_ne_top_of_nonneg hs.le (hρ i)
  let e : ℕ → ℝ := fun i => ε / 2 / 2 ^ i
  let η : ℕ → ℝ := fun i => e i / (1 + (a i).toReal)
  have he : ∀ i, 0 < e i := by intro i; dsimp [e]; positivity
  have hη : ∀ i, 0 < η i := by intro i; dsimp [η]; exact div_pos (he i) (by positivity)
  choose J hJopen hJsub hJvol using fun i => hinter (B i) (ρ i) (hρ i) (hB i) (η i) (hη i)
  let f : ℕ → ℝ → ℝ≥0∞ := fun i => (J i).indicator (fun _ => a i)
  have hf : ∀ i, Measurable (f i) := fun i => measurable_const.indicator (hJopen i).measurableSet
  have hslice : ∀ t ∈ yI, c ≤ ∑' i, f i t := by
    intro t ht
    let W : ℕ → Set (YEuclid n) := fun i => if t ∈ J i then A i else ∅
    have hcov : E ⊆ ⋃ i, W i := by
      intro x hx
      have hxt : yJoin x t ∈ yProd E := by
        change yHoriz (yJoin x t) ∈ E ∧ yVert (yJoin x t) ∈ yI
        simpa only [(hjoin x t).1, (hjoin x t).2] using And.intro hx ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hxt)
      have htJ : t ∈ J i := hJsub i ⟨yJoin x t, hi, (hjoin x t).2⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simpa only [W, if_pos htJ] using
        (show x ∈ A i from ⟨yJoin x t, hi, (hjoin x t).1⟩)
    have hdiam : ∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal δ := by
      intro i
      dsimp [W]
      split_ifs
      · exact (hA i).trans (hV.2 i)
      · simp
    calc
      c ≤ ∑' i, Metric.ediam (W i) ^ s := by
        exact iInf_le_of_le W (iInf_le_of_le hcov (iInf_le _ hdiam))
      _ ≤ ∑' i, f i t := by
        apply ENNReal.tsum_le_tsum
        intro i
        by_cases htJ : t ∈ J i
        · simpa only [W, if_pos htJ, f, Set.indicator_of_mem htJ, a] using
            ENNReal.rpow_le_rpow (hA i) hs.le
        · simp [W, htJ, f, ENNReal.zero_rpow_of_pos hs]
  let μ : Measure ℝ := volume.restrict yI
  have hμ : μ Set.univ = 1 := by simp [μ, yI]
  have hlower : c ≤ ∫⁻ t, ∑' i, f i t ∂μ := by
    calc
      c = ∫⁻ _ : ℝ, c ∂μ := by rw [lintegral_const, hμ, mul_one]
      _ ≤ ∫⁻ t, ∑' i, f i t ∂μ := by
        apply lintegral_mono_ae
        exact (ae_restrict_mem (show MeasurableSet yI from measurableSet_Icc)).mono hslice
  have hint : ∀ i, (∫⁻ t, f i t ∂μ) ≤ ρ i ^ (s+1) + ENNReal.ofReal (e i) := by
    intro i
    calc
      (∫⁻ t, f i t ∂μ) = a i * μ (J i) :=
        lintegral_indicator_const (hJopen i).measurableSet (a i)
      _ ≤ a i * (ρ i + ENNReal.ofReal (η i)) := by
        apply mul_le_mul_left'
        exact (Measure.restrict_apply_le yI (J i)).trans (hJvol i)
      _ = ρ i ^ (s+1) + a i * ENNReal.ofReal (η i) := by
        dsimp [a]
        rw [ENNReal.rpow_add_of_nonneg s 1 hs.le zero_le_one, ENNReal.rpow_one, mul_add]
      _ ≤ ρ i ^ (s+1) + ENNReal.ofReal (e i) :=
        add_le_add le_rfl (hnum (a i) (ha i) (e i) (he i).le)
  have hsum : (∑' i, ENNReal.ofReal (e i)) = ENNReal.ofReal ε := by
    dsimp [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (he i).le) (summable_geometric_two' ε),
      tsum_geometric_two']
  calc
    yContent s δ E ≤ ∫⁻ t, ∑' i, f i t ∂μ := hlower
    _ = ∑' i, ∫⁻ t, f i t ∂μ :=
      MeasureTheory.lintegral_tsum (α := ℝ) (β := ℕ) (μ := μ) (f := f) (fun i => (hf i).aemeasurable)
    _ ≤ ∑' i, (ρ i ^ (s+1) + ENNReal.ofReal (e i)) := ENNReal.tsum_le_tsum hint
    _ = yCost (s+1) V + ENNReal.ofReal ε := by rw [ENNReal.tsum_add, hsum]; rfl

theorem T011 (n : ℕ) (E : Set (YEuclid n)) (h_T010 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEuclid (n+1)), yCover δ (yProd E) V → ∀ ε : ℝ, 0 < ε → yContent s δ E ≤ yCost (s+1) V + ENNReal.ofReal ε) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E ≤ yContent (s+1) δ (yProd E) := by
  intro s δ hs hδ
  refine le_iInf fun V => le_iInf fun hcov => le_iInf fun hdiam => ?_
  change yContent s δ E ≤ yCost (s + 1) V
  by_cases htop : yCost (s + 1) V = ⊤
  · rw [htop]
    exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    have hεreal : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.mpr hε
    have hεcoe : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) :=
      ENNReal.ofReal_coe_nnreal
    simpa only [hεcoe] using
      h_T010 s δ hs hδ V ⟨hcov, hdiam⟩ (ε : ℝ) hεreal

theorem T012 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T011 : ∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E ≤ yContent (s+1) δ (yProd E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (yProd E) := by
  intro hDpos
  have hDfin : dimH E ≠ ⊤ := h_T002.1.ne
  have hDrealpos : 0 < (dimH E).toReal :=
    ENNReal.toReal_pos hDpos.ne' hDfin
  have hDrepr : ENNReal.ofReal (dimH E).toReal = dimH E :=
    ENNReal.ofReal_toReal hDfin
  have hmono : ∀ (s δ δ' : ℝ), δ' ≤ δ →
      yContent s δ E ≤ yContent s δ' E := by
    intro s δ δ' hδ
    unfold yContent
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    exact iInf_le_of_le U (iInf_le_of_le hU
      (iInf_le_of_le (fun i => (hd i).trans (ENNReal.ofReal_le_ofReal hδ)) le_rfl))
  have F003 : ∀ s : ℝ, 0 < s → s < (dimH E).toReal →
      ENNReal.ofReal (s + 1) ≤ dimH (yProd E) := by
    intro s hs hsD
    have hsD' : ENNReal.ofReal s < dimH E :=
      (ENNReal.ofReal_lt_iff_lt_toReal hs.le hDfin).2 hsD
    have htopE : yHaus s E = ⊤ :=
      ((h_T001.1 n).2 E s hs).2.2.1 hsD'
    have F001 : ∀ (T ε : ℝ), 0 < T → 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ENNReal.ofReal T < yContent s δ E := by
      intro T ε hT hε
      have hlarge : ENNReal.ofReal T < yHaus s E := by
        rw [htopE]
        exact ENNReal.ofReal_lt_top
      change ENNReal.ofReal T < ⨆ δ : ℝ, ⨆ (_ : 0 < δ), yContent s δ E at hlarge
      obtain ⟨δ, hδ⟩ := lt_iSup_iff.mp hlarge
      obtain ⟨hδpos, hδlarge⟩ := lt_iSup_iff.mp hδ
      refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, ?_⟩
      exact hδlarge.trans_le (hmono s δ (min δ ε) (min_le_left _ _))
    have F002 : ∀ T : ℝ, 0 < T →
        ENNReal.ofReal T < yHaus (s + 1) (yProd E) := by
      intro T hT
      obtain ⟨δ, hδpos, _, hδlarge⟩ := F001 T 1 hT zero_lt_one
      have hbound : yContent (s + 1) δ (yProd E) ≤ yHaus (s + 1) (yProd E) := by
        unfold yHaus
        exact le_iSup_of_le δ (le_iSup_of_le hδpos le_rfl)
      exact hδlarge.trans_le ((h_T011 s δ hs hδpos).trans hbound)
    have htopF : yHaus (s + 1) (yProd E) = ⊤ := by
      by_contra hfinite
      have hTpos : 0 < (yHaus (s + 1) (yProd E)).toReal + 1 :=
        by positivity
      have hlt := F002 ((yHaus (s + 1) (yProd E)).toReal + 1) hTpos
      have hlt' := (ENNReal.ofReal_lt_iff_lt_toReal hTpos.le hfinite).1 hlt
      linarith
    have hsp : 0 < s + 1 := by linarith
    exact ((h_T001.1 (n + 1)).2 (yProd E) (s + 1) hsp).2.2.2.2 htopF
  have hrepr : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add (le_of_lt hDrealpos) (by norm_num), hDrepr]
    norm_num
  rw [← hrepr]
  by_cases hQtop : dimH (yProd E) = ⊤
  · rw [hQtop]
    exact le_top
  · apply (ENNReal.ofReal_le_iff_le_toReal hQtop).2
    by_contra hnot
    have hQlt : (dimH (yProd E)).toReal < (dimH E).toReal + 1 :=
      lt_of_not_ge hnot
    have hmax : max 0 ((dimH (yProd E)).toReal - 1) < (dimH E).toReal := by
      apply max_lt hDrealpos
      linarith
    obtain ⟨s, hslo, hsD⟩ := exists_between hmax
    have hs : 0 < s := (le_max_left _ _).trans_lt hslo
    have hsQ : (dimH (yProd E)).toReal - 1 < s :=
      (le_max_right _ _).trans_lt hslo
    have hbound := (ENNReal.ofReal_le_iff_le_toReal hQtop).1 (F003 s hs hsD)
    linarith

theorem T013 (n : ℕ) (E : Set (YEuclid n)) (h_H002 : E.Nonempty) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T005 : dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤)) :
    dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (yProd E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hD
  obtain ⟨x, hx⟩ := h_H002
  have hcoords (t : ℝ) : yHoriz (yJoin x t) = x ∧ yVert (yJoin x t) = t := by
    constructor
    · ext i
      simp [yHoriz, yJoin]
    · simp [yVert, yJoin]
  have hf : Isometry (fun t : ℝ => yJoin x t) := by
    apply Isometry.of_dist_eq
    intro t u
    have hsq : dist (yJoin x t) (yJoin x u) ^ 2 = dist t u ^ 2 := by
      rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_castSucc]
      simp [yJoin]
    nlinarith [dist_nonneg (x := yJoin x t) (y := yJoin x u), dist_nonneg (x := t) (y := u)]
  have hmem : ∀ t ∈ yI, yJoin x t ∈ yProd E := by
    intro t ht
    change yHoriz (yJoin x t) ∈ E ∧ yVert (yJoin x t) ∈ yI
    rw [(hcoords t).1, (hcoords t).2]
    exact ⟨hx, ht⟩
  have hcover : ∀ (f : ℝ → YEuclid (n+1)), Isometry f → (∀ t ∈ yI, f t ∈ yProd E) → ∀ s : ℝ, 0 < s → yHaus s yI ≤ yHaus s (yProd E) := by
    intro f hf hmem s hs
    have hdiam (V : Set (YEuclid (n+1))) : Metric.ediam (f ⁻¹' V) ≤ Metric.ediam V := by
      apply Metric.ediam_le_iff.mpr
      intro t ht u hu
      rw [← hf.edist_eq t u]
      exact Metric.edist_le_ediam_of_mem ht hu
    have hcontent (δ : ℝ) : yContent s δ yI ≤ yContent s δ (yProd E) := by
      unfold yContent
      refine le_iInf fun V => le_iInf fun hcov => le_iInf fun hδ => ?_
      let W : ℕ → Set ℝ := fun i => f ⁻¹' V i
      have hWcov : yI ⊆ ⋃ i, W i := by
        intro t ht
        rcases Set.mem_iUnion.mp (hcov (hmem t ht)) with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      have hWδ : ∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal δ := fun i => (hdiam (V i)).trans (hδ i)
      have hbound : yContent s δ yI ≤ ∑' i, (Metric.ediam (W i)) ^ s := by
        unfold yContent
        exact iInf_le_of_le W (iInf_le_of_le hWcov (iInf_le_of_le hWδ le_rfl))
      exact hbound.trans (ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hdiam (V i)) hs.le)
    unfold yHaus
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hcontent δ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hbound : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH (yProd E) := by
    intro s hs hs1
    have hle := hcover (fun t => yJoin x t) hf hmem s hs
    rw [h_T005.2.2 s hs hs1] at hle
    have htop : yHaus s (yProd E) = ⊤ := top_unique hle
    exact ((h_T001.1 (n+1)).2 (yProd E) s hs).2.2.2.2 htop
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hr1
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hrlt : (r : ℝ) < 1 := by exact_mod_cast hr1
    simpa only [ENNReal.ofReal_coe_nnreal] using hbound (r : ℝ) hrpos hrlt
  · simp [hD]

theorem T014 (n : ℕ) (E : Set (YEuclid n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T009 : dimH (yProd E) ≤ dimH E + 1 ∧ dimH (yProd E) < ⊤) (h_T012 : 0 < dimH E → dimH E + 1 ≤ dimH (yProd E)) (h_T013 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (yProd E) ∧ (1 : ℝ≥0∞) = dimH E + 1) :
    dimH (yProd E) = dimH E + 1 := by
  apply le_antisymm h_T009.1
  rcases lt_or_eq_of_le h_T002.2.1 with hpos | hzero
  · exact h_T012 hpos
  · obtain ⟨hlower, hone⟩ := h_T013 hzero.symm
    exact hone ▸ hlower

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) :
    dimH (yProd E) = dimH E + 1 := by
  have h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ := @T001 n E 
  have h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤) := @T002 n E h_H001 h_H002 h_H003 h_T001
  have h_T003 : dimH yI ≤ 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) := @T003 n E h_T001
  have h_T004 : ∀ (δ : ℝ), 0 < δ → ∀ V : ℕ → Set ℝ, yCover δ yI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) := @T004 n E 
  have h_T005 : dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤) := @T005 n E h_T001 h_T003 h_T004
  have h_T006 : n = 0 → dimH (yProd E) ≤ dimH E + 1 := @T006 n E h_T001 h_T002 h_T005
  have h_T007 : 1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε := @T007 n E h_T001 h_T002
  have h_T008 : 1 ≤ n → dimH (yProd E) ≤ dimH E + 1 := @T008 n E h_T001 h_T002 h_T007
  have h_T009 : dimH (yProd E) ≤ dimH E + 1 ∧ dimH (yProd E) < ⊤ := @T009 n E h_T002 h_T006 h_T008
  have h_T010 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEuclid (n+1)), yCover δ (yProd E) V → ∀ ε : ℝ, 0 < ε → yContent s δ E ≤ yCost (s+1) V + ENNReal.ofReal ε := @T010 n E h_T002
  have h_T011 : ∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E ≤ yContent (s+1) δ (yProd E) := @T011 n E h_T010
  have h_T012 : 0 < dimH E → dimH E + 1 ≤ dimH (yProd E) := @T012 n E h_T001 h_T002 h_T011
  have h_T013 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (yProd E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := @T013 n E h_H002 h_T001 h_T005
  have h_T014 : dimH (yProd E) = dimH E + 1 := @T014 n E h_T002 h_T009 h_T012 h_T013
  exact h_T014

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) : dimH (yProd E) = dimH E + 1 := by
  exact @Translation.P n E h_H001 h_H002 h_H003

#check @P
#print axioms P
end AuditBExport
