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

theorem T002 (n : ℕ) (E : Set (GPEucl n))  :
    (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) := by
  classical
  have comparison : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
      (A : Set X) (s : ℝ), 0 < s →
      GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A := by
    intro X _ _ _ A s hs
    have cost_eq (U : ℕ → Set X) :
        (∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ s) = GPcost s U := by
      unfold GPcost
      apply tsum_congr
      intro i
      by_cases hi : (U i).Nonempty
      · simp only [hi, iSup_pos]
      · have hempty : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
        simp [hempty, ENNReal.zero_rpow_of_pos hs]
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    simp_rw [cost_eq]
    apply le_antisymm
    · unfold GPmass
      refine iSup₂_le fun δ hδ => ?_
      have hpos : (0 : ENNReal) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
      calc
        GPcontent s δ A =
            ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
              (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), GPcost s U := by
          simp only [GPcontent, GPcover, iInf_and]
        _ ≤ _ := le_iSup₂ (f := fun (r : ENNReal) (_ : 0 < r) =>
            ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
              (_ : ∀ i, Metric.ediam (U i) ≤ r), GPcost s U)
            (ENNReal.ofReal δ) hpos
    · refine iSup₂_le fun r hr => ?_
      have radius : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r := by
        by_cases hfin : r = ⊤
        · exact ⟨1, zero_lt_one, by simp [hfin]⟩
        · have hconvert : 0 < r.toReal ∧ ENNReal.ofReal r.toReal = r :=
            ⟨ENNReal.toReal_pos hr.ne' hfin, ENNReal.ofReal_toReal hfin⟩
          exact ⟨r.toReal, hconvert.1, hconvert.2.le⟩
      obtain ⟨δ, hδ, hδr⟩ := radius
      refine le_trans ?_ (le_iSup₂
        (f := fun (δ : ℝ) (_ : 0 < δ) => GPcontent s δ A) δ hδ)
      unfold GPcontent
      refine le_iInf fun U => le_iInf fun hU => ?_
      exact iInf₂_le_of_le U hU.1
        (iInf_le_of_le (fun i => (hU.2 i).trans hδr) le_rfl)
  constructor
  · intro k A s hs
    exact comparison (GPEucl k) A s hs
  · intro A s hs
    exact comparison ℝ A s hs

theorem T003 (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) :
    ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A) := by
  intro k A s hs
  have hr : (s.toNNReal : ℝ) = s := by
    rw [Real.toNNReal_of_nonneg hs.le]
    rfl
  have he : (s.toNNReal : ENNReal) = ENNReal.ofReal s := rfl
  have hEq := h_T002.1 k A s hs
  have hn : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) A = GPmass s A := by
    rw [hr, hEq]
  have hmono : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
      GPcontent s δ₂ A ≤ GPcontent s δ₁ A := by
    intro δ₁ δ₂ hδ₁ hδ₂ hδ
    unfold GPcontent
    refine le_iInf fun U => le_iInf fun hU => ?_
    have hU₂ : GPcover A δ₂ U :=
      ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hδ)⟩
    exact iInf_le_of_le U (iInf_le_of_le hU₂ le_rfl)
  refine ⟨hEq, bot_le, ?_, ?_, ?_, ?_, hmono, ?_, ?_⟩
  · intro h
    have hd : dimH A < (s.toNNReal : ENNReal) := by simpa only [he] using h
    simpa only [hn] using (hausdorffMeasure_of_dimH_lt (s := A) (d := s.toNNReal) hd)
  · intro h
    have hd : (s.toNNReal : ENNReal) < dimH A := by simpa only [he] using h
    simpa only [hn] using (hausdorffMeasure_of_lt_dimH (s := A) (d := s.toNNReal) hd)
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) A ≠ ⊤ := by
      rw [hn, h]
      exact ENNReal.zero_ne_top
    simpa only [he] using
      (dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := s.toNNReal) hm)
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) A = ⊤ := by
      rw [hn, h]
    simpa only [he] using
      (le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := s.toNNReal) hm)
  · intro hm δ ε hδ hε
    have hc : GPcontent s δ A = 0 := by
      apply le_antisymm _ bot_le
      calc
        GPcontent s δ A ≤ GPmass s A := by
          unfold GPmass
          exact le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)
        _ = 0 := hm
    have hcε : GPcontent s δ A < ENNReal.ofReal ε := by
      rw [hc]
      exact ENNReal.ofReal_pos.mpr hε
    simpa only [GPcontent, iInf_lt_iff, exists_prop] using hcε
  · intro hm L δ₀ hL hδ₀
    have hlarge : ENNReal.ofReal L < GPmass s A := by
      rw [hm]
      exact ENNReal.ofReal_lt_top
    obtain ⟨δ, hδ, hbig⟩ : ∃ δ : ℝ, ∃ hδ : 0 < δ,
        ENNReal.ofReal L < GPcontent s δ A := by
      simpa only [GPmass, lt_iSup_iff] using hlarge
    refine ⟨min δ δ₀, lt_min hδ hδ₀, min_le_right _ _, ?_⟩
    exact hbig.trans_le (hmono (min δ δ₀) δ (lt_min hδ hδ₀) hδ (min_le_left _ _))

theorem T004 (n : ℕ) (E : Set (GPEucl n)) (h_H002 : IsCompact E) :
    Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) := by
  classical
  have hb : Bornology.IsBounded E := h_H002.isBounded
  have hcoords : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R := by
    obtain ⟨R, hR, hER⟩ := hb.subset_ball_lt 0 (0 : GPEucl n)
    refine ⟨R, hR, ?_⟩
    intro x hx j
    have hnorm : ‖x‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hER hx
    have hcoord : |x j| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
    exact abs_le.mp (hcoord.trans hnorm.le)
  have hfinite : ∀ (s δ : ℝ), 0 < s → 0 < δ →
      ∃ T : Finset (GPEucl n),
        (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
        (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
        (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal) := by
    intro s δ hs hδ
    have hrad : 0 < δ / 2 := by positivity
    obtain ⟨T, hT⟩ := h_H002.elim_finite_subcover
      (fun x : GPEucl n => Metric.ball x (δ / 2))
      (fun _ => Metric.isOpen_ball)
      (fun x hx => Set.mem_iUnion.mpr ⟨x, by simpa using hrad⟩)
    have hd : ∀ x : GPEucl n,
        Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ := by
      intro x
      apply Metric.ediam_le_of_forall_dist_le
      intro y hy z hz
      have hy' : dist y x < δ / 2 := hy
      have hz' : dist x z < δ / 2 := by
        simpa only [Metric.mem_ball, dist_comm] using hz
      have ht := dist_triangle y x z
      linarith
    refine ⟨T, hT, fun x _ => hd x, ?_⟩
    exact ENNReal.sum_lt_top.mpr fun x hx =>
      ENNReal.rpow_lt_top_of_nonneg hs.le
        (ne_of_lt (lt_of_le_of_lt (hd x) ENNReal.ofReal_lt_top))
  refine ⟨hb, hcoords, hfinite, ?_⟩
  intro s δ hs hδ
  obtain ⟨T, hT, hd, hsum⟩ := hfinite s δ hs hδ
  let N := Fintype.card T
  let e : T ≃ Fin N := Fintype.equivFin T
  let U : ℕ → Set (GPEucl n) := fun i =>
    if hi : i < N then Metric.ball (e.symm ⟨i, hi⟩).val (δ / 2) else ∅
  have hcover : GPcover E δ U := by
    constructor
    · intro y hy
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hT hy)
      let t : T := ⟨x, hx⟩
      refine Set.mem_iUnion.mpr ⟨(e t).val, ?_⟩
      simpa only [U, dif_pos (e t).isLt, Fin.eta, Equiv.symm_apply_apply] using hyx
    · intro i
      dsimp [U]
      split_ifs with hi
      · exact hd _ (e.symm ⟨i, hi⟩).property
      · simp
  have hcost : GPcost s U < ⊤ := by
    unfold GPcost
    rw [tsum_eq_sum (s := Finset.range N) (fun i hi => ?_)]
    · refine ENNReal.sum_lt_top.mpr fun i hi => ?_
      exact ENNReal.rpow_lt_top_of_nonneg hs.le
        (ne_of_lt (lt_of_le_of_lt (hcover.2 i) ENNReal.ofReal_lt_top))
    · have hi' : ¬ i < N := by simpa only [Finset.mem_range] using hi
      simp only [U, dif_neg hi', Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]
  exact lt_of_le_of_lt (iInf_le_of_le U (iInf_le_of_le hcover le_rfl)) hcost

theorem T005 (n : ℕ) (E : Set (GPEucl n)) (h_H001 : E.Nonempty) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T004 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤)) :
    Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) := by
  classical
  have hbound : ∀ a : ℝ, 0 ≤ a → (∀ s : ℝ, a < s → GPmass s E = 0) → dimH E ≤ ENNReal.ofReal a := by
    intro a ha hz
    by_contra! hlt
    rcases ENNReal.lt_iff_exists_real_btwn.mp hlt with ⟨s, hs0, has, hsD⟩
    have has' : a < s := (ENNReal.ofReal_lt_ofReal_iff'.mp has).1
    have hs : 0 < s := lt_of_le_of_lt ha has'
    have hle : dimH E ≤ ENNReal.ofReal s :=
      (h_T003 n E s hs).2.2.2.2.1 (hz s has')
    exact (not_lt_of_ge hle) hsD
  have hsing : E.Subsingleton → ∀ s : ℝ, 0 < s → GPmass s E = 0 := by
    intro hE s hs
    have hdiam : Metric.ediam E = 0 := hE.ediam_eq
    have hcost : GPcost s (fun _ : ℕ => E) = 0 := by
      simp [GPcost, hdiam, ENNReal.zero_rpow_of_pos hs]
    apply le_antisymm _ bot_le
    unfold GPmass
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    have hcover : GPcover E δ (fun _ : ℕ => E) := by
      constructor
      · intro x hx
        exact Set.mem_iUnion.mpr ⟨0, hx⟩
      · intro i
        simp [hdiam]
    unfold GPcontent
    exact iInf_le_of_le (fun _ : ℕ => E) (iInf_le_of_le hcover (le_of_eq hcost))
  have hzero_case : n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0 := by
    intro hn
    have hamb : ∀ x y : GPEucl n, x = y := by
      intro x y
      ext j
      have hj := j.isLt
      omega
    have hsub : E.Subsingleton := fun x _ y _ => hamb x y
    have hall : E = Set.univ := by
      rcases h_H001 with ⟨y, hy⟩
      apply Set.eq_univ_of_forall
      intro x
      rw [hamb x y]
      exact hy
    refine ⟨hall, hsub, le_antisymm ?_ bot_le⟩
    simpa only [ENNReal.ofReal_zero] using hbound 0 le_rfl (hsing hsub)
  have hdim : dimH E ≤ (n : ENNReal) := by
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, (hzero_case hn).2.2, le_refl]
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hmesh : ∀ s : ℝ, (n : ℝ) < s → GPmass s E = 0 := by
        classical
        intro s hs
        have hspos : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg n) hs
        have grid : ∀ (R m : ℝ), 0 < R → 1 ≤ m →
        let K := ⌈2 * R * m⌉₊
        let t : (Fin n → Fin K) → Set (GPEucl n) := fun f => {x | ∀ j, -R + (f j : ℝ) / m ≤ x j ∧ x j ≤ -R + ((f j : ℝ) + 1) / m}
        ((∀ x ∈ E, ∀ j, -R < x j ∧ x j < R) → E ⊆ ⋃ f, t f) ∧
        (∀ f, Metric.ediam (t f) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ) / m)) ∧
        ((Fintype.card (Fin n → Fin K) : ℝ) ≤ (2 * R + 1)^n * m^n) := by
          classical
          intro R m hR hm
          dsimp only
          let K := ⌈2 * R * m⌉₊
          let t : (Fin n → Fin K) → Set (GPEucl n) := fun f => {x | ∀ j, -R + (f j : ℝ) / m ≤ x j ∧ x j ≤ -R + ((f j : ℝ) + 1) / m}
          change ((∀ x ∈ E, ∀ j, -R < x j ∧ x j < R) → E ⊆ ⋃ f, t f) ∧ _ ∧ _
          have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
          have hdiam : ∀ (h : ℝ), 0 ≤ h → ∀ (x y : GPEucl n), (∀ j, |x j - y j| ≤ h) → dist x y ≤ Real.sqrt (n : ℝ) * h := by
            intro h hh x y hxy
            rw [EuclideanSpace.dist_eq]
            calc
              Real.sqrt (∑ j : Fin n, dist (x j) (y j) ^ 2) ≤
                  Real.sqrt (∑ j : Fin n, h ^ 2) := by
                apply Real.sqrt_le_sqrt
                exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (dist_nonneg) (by simpa [Real.dist_eq] using hxy j) 2
              _ = Real.sqrt (n : ℝ) * h := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hh]
          refine ⟨?_, ?_, ?_⟩
          · intro hbox x hx
            let f : Fin n → Fin K := fun j => ⟨⌊(x j + R) * m⌋₊, by
              apply Nat.floor_lt_ceil_of_lt_of_pos
              · nlinarith [(hbox x hx j).2]
              · positivity⟩
            refine Set.mem_iUnion.mpr ⟨f, ?_⟩
            intro j
            have hfloor := Nat.floor_le (show 0 ≤ (x j + R) * m by nlinarith [(hbox x hx j).1])
            have hnext := (Nat.lt_floor_add_one ((x j + R) * m)).le
            constructor
            · change -R + (⌊(x j + R) * m⌋₊ : ℝ) / m ≤ x j
              have hd := (div_le_iff₀ hm0).mpr hfloor
              have heq : ((x j + R) * m) / m = x j + R := by field_simp
              linarith
            · change x j ≤ -R + ((⌊(x j + R) * m⌋₊ : ℝ) + 1) / m
              have hd := (le_div_iff₀ hm0).mpr hnext
              linarith
          · intro f
            apply Metric.ediam_le_of_forall_dist_le
            intro x hx y hy
            rw [div_eq_mul_inv]
            apply hdiam m⁻¹ (inv_nonneg.mpr hm0.le) x y
            intro j
            apply abs_le.mpr
            have hxj := hx j
            have hyj := hy j
            have heq : (-R + ((f j : ℝ) + 1) / m) - (-R + (f j : ℝ) / m) = m⁻¹ := by field_simp; ring
            constructor <;> linarith
          · have hk : (K : ℝ) ≤ (2 * R + 1) * m := by
              have hc := (Nat.ceil_lt_add_one (show 0 ≤ 2 * R * m by positivity)).le
              dsimp [K]
              nlinarith
            simpa [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_pow] using
              (pow_le_pow_left₀ (Nat.cast_nonneg K) hk n)
        have sum_bound : ∀ (α : Type) [Fintype α] (U : α → Set (GPEucl n)) (d s : ℝ), 0 ≤ d → 0 ≤ s →
        (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal d) →
        (∑ i, Metric.ediam (U i)^s) ≤ ENNReal.ofReal ((Fintype.card α : ℝ) * d^s) := by
          intro α _ U d s hd hs hU
          calc
            (∑ i, Metric.ediam (U i)^s) ≤ ∑ _ : α, (ENNReal.ofReal d)^s :=
              Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hU i) hs
            _ = ENNReal.ofReal ((Fintype.card α : ℝ) * d^s) := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              rw [ENNReal.ofReal_rpow_of_nonneg hd hs, ← ENNReal.ofReal_natCast,
                ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        have algebra : ∀ (R m s : ℝ), 0 < m →
        (2 * R + 1)^n * m^n * (Real.sqrt (n : ℝ) / m)^s =
        ((2 * R + 1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ))) := by
          intro R m s hm
          rw [Real.div_rpow (Real.sqrt_nonneg _) hm.le, ← Real.rpow_natCast m n,
            show -(s - (n : ℝ)) = (n : ℝ) - s by ring, Real.rpow_sub hm]
          ring
        have limits : ∀ R s : ℝ, (n : ℝ) < s →
        Filter.Tendsto (fun m : ℝ => ENNReal.ofReal (((2*R+1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ))))) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun m : ℝ => ENNReal.ofReal (Real.sqrt (n : ℝ) / m)) Filter.atTop (nhds 0) := by
          intro R s hs
          constructor
          · have hr : Filter.Tendsto (fun m : ℝ => ((2*R+1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ)))) Filter.atTop (nhds 0) := by
              simpa only [mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).const_mul ((2*R+1)^n * (Real.sqrt (n : ℝ))^s)
            simpa only [ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr
          · have hr : Filter.Tendsto (fun m : ℝ => Real.sqrt (n : ℝ) / m) Filter.atTop (nhds 0) :=
              Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
            simpa only [ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr
        rcases h_T004.2.1 with ⟨R₀, hR₀, hbox₀⟩
        let R : ℝ := R₀ + 1
        have hR : 0 < R := by dsimp [R]; linarith
        have hbox : ∀ x ∈ E, ∀ j : Fin n, -R < x j ∧ x j < R := by
          intro x hx j
          rcases hbox₀ x hx j with ⟨ha, hb⟩
          dsimp [R]
          constructor <;> linarith
        let K : ℝ → ℕ := fun m => ⌈2 * R * m⌉₊
        let t : ∀ m : ℝ, (Fin n → Fin (K m)) → Set (GPEucl n) := fun m f =>
          {x | ∀ j, -R + (f j : ℝ) / m ≤ x j ∧ x j ≤ -R + ((f j : ℝ) + 1) / m}
        let B : ℝ → ENNReal := fun m =>
          ENNReal.ofReal (((2*R+1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ))))
        have hlim : Filter.Tendsto B Filter.atTop (nhds 0) := (limits R s hs).1
        have hr : Filter.Tendsto (fun m : ℝ => ENNReal.ofReal (Real.sqrt (n : ℝ) / m)) Filter.atTop (nhds 0) := (limits R s hs).2
        have hd : ∀ᶠ m : ℝ in Filter.atTop, ∀ f, Metric.ediam (t m f) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ) / m) := by
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
          exact (grid R m hR hm).2.1
        have hc : ∀ᶠ m : ℝ in Filter.atTop, E ⊆ ⋃ f, t m f := by
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
          exact (grid R m hR hm).1 hbox
        have hcost : ∀ᶠ m : ℝ in Filter.atTop, (∑ f, Metric.ediam (t m f)^s) ≤ B m := by
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
          have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
          have hd0 : 0 ≤ Real.sqrt (n : ℝ) / m := div_nonneg (Real.sqrt_nonneg _) hm0.le
          calc
            (∑ f, Metric.ediam (t m f)^s) ≤
                ENNReal.ofReal ((Fintype.card (Fin n → Fin (K m)) : ℝ) * (Real.sqrt (n : ℝ) / m)^s) :=
              sum_bound _ (t m) _ _ hd0 hspos.le (grid R m hR hm).2.1
            _ ≤ ENNReal.ofReal ((2*R+1)^n * m^n * (Real.sqrt (n : ℝ) / m)^s) := by
              apply ENNReal.ofReal_le_ofReal
              exact mul_le_mul_of_nonneg_right (grid R m hR hm).2.2 (Real.rpow_nonneg hd0 s)
            _ = B m := by rw [algebra R m s hm0]
        have hnative : MeasureTheory.Measure.hausdorffMeasure s E ≤
            Filter.liminf (fun m : ℝ => ∑ f, Metric.ediam (t m f)^s) Filter.atTop :=
          MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s E _ hr t hd hc
        have hlimle : Filter.liminf (fun m : ℝ => ∑ f, Metric.ediam (t m f)^s) Filter.atTop ≤
            Filter.liminf B Filter.atTop := Filter.liminf_le_liminf hcost
        have hzero : MeasureTheory.Measure.hausdorffMeasure s E = 0 :=
          le_antisymm (hnative.trans (hlimle.trans_eq hlim.liminf_eq)) bot_le
        exact (h_T003 n E s hspos).1.trans hzero
      simpa only [ENNReal.ofReal_natCast] using hbound (n : ℝ) (Nat.cast_nonneg n) hmesh
  exact ⟨h_T004.1, h_T004.2.1, h_T004.2.2.1, h_T004.2.2.2,
    ⟨(h_T003 n E 1 (by norm_num)).2.1, hdim, hdim.trans_lt (by simp)⟩, hzero_case⟩

theorem T001 (n : ℕ) (E : Set (GPEucl n))  :
    (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w) := by
  have hinv : ∀ (k : ℕ) (z : GPEucl (k + 1)),
      GPappend (GPhead z) (z (Fin.last k)) = z := by
    intro k z
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [GPappend]
    · simp [GPappend, GPhead]
  have hsq : ∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
      dist (GPappend x t) (GPappend y u) ^ 2 = dist x y ^ 2 + |t - u| ^ 2 := by
    intro k x y t u
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
    simp only [GPappend, PiLp.toLp_apply, Fin.snoc_castSucc, Fin.snoc_last]
    rw [← EuclideanSpace.dist_sq_eq, Real.dist_eq]
  refine ⟨?_, hinv, ?_, ?_⟩
  · intro k x t
    constructor
    · ext i
      simp [GPhead, GPappend]
    · simp [GPappend]
  · intro k x y t u
    calc
      dist (GPappend x t) (GPappend y u) =
          Real.sqrt (dist (GPappend x t) (GPappend y u) ^ 2) :=
        (Real.sqrt_sq dist_nonneg).symm
      _ = Real.sqrt (dist x y ^ 2 + |t - u| ^ 2) := by rw [hsq]
  · intro k z w
    have h : dist z w ^ 2 =
        dist (GPhead z) (GPhead w) ^ 2 + |z (Fin.last k) - w (Fin.last k)| ^ 2 := by
      simpa only [hinv] using hsq k (GPhead z) (GPhead w) (z (Fin.last k)) (w (Fin.last k))
    constructor
    · nlinarith [dist_nonneg (x := z) (y := w), dist_nonneg (x := GPhead z) (y := GPhead w),
        sq_nonneg (z (Fin.last k) - w (Fin.last k))]
    · nlinarith [dist_nonneg (x := z) (y := w),
        abs_nonneg (z (Fin.last k) - w (Fin.last k)),
        sq_nonneg (dist (GPhead z) (GPhead w))]

theorem T007 (n : ℕ) (E : Set (GPEucl n)) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) :
    n = 0 →
  dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧ GPmass (q + 1) (GPproduct E) = 0 := by
  classical
  have hcover : n = 0 → ∀ (N : ℕ) (a : ℝ), 0 < N → 0 < a →
      ∃ U : ℕ → Set (GPEucl (n + 1)),
        GPcover (GPproduct E) (1 / (N : ℝ)) U ∧
        GPcost a U ≤ ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
    classical
    intro hn
    subst n
    have hpart : ∀ (N : ℕ), 0 < N → ∀ t ∈ GPI,
        ∃ i : ℕ, i < N ∧ t ∈ Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
      intro N hN t ht
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      rcases ht with ⟨ht0, ht1⟩
      by_cases he : t = 1
      · subst t
        refine ⟨N - 1, by omega, ?_, ?_⟩
        · apply (div_le_iff₀ hNr).2
          have : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
          simpa using this
        · apply (le_div_iff₀ hNr).2
          have : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
            norm_cast
            omega
          linarith
      · have htlt : t < 1 := lt_of_le_of_ne ht1 he
        refine ⟨⌊t * N⌋₊, (Nat.floor_lt (mul_nonneg ht0 hNr.le)).2 ?_, ?_, ?_⟩
        · nlinarith
        · exact (div_le_iff₀ hNr).2 (Nat.floor_le (mul_nonneg ht0 hNr.le))
        · exact (le_div_iff₀ hNr).2 (Nat.lt_floor_add_one (t * N)).le
    have hcost : ∀ (N : ℕ) (a : ℝ), 0 < N → 0 < a →
        (N : ENNReal) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a =
          ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
      intro N a hN ha
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNr)]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNr.le]
      congr 1
      rw [sub_eq_add_neg, Real.rpow_add hNr, Real.rpow_one,
        Real.rpow_neg_eq_inv_rpow, one_div]
    intro N a hN ha
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let f : ℝ → GPEucl 1 := fun t => GPappend (0 : GPEucl 0) t
    have hf : ∀ t u : ℝ, dist (f t) (f u) = |t - u| := by
      intro t u
      dsimp [f]
      rw [h_T001.2.2.1, dist_self, zero_pow (by decide : 2 ≠ 0), zero_add,
        Real.sqrt_sq (abs_nonneg _)]
    let U : ℕ → Set (GPEucl 1) := fun i =>
      if i < N then f '' Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) else ∅
    have hd : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (1 / (N : ℝ)) := by
      intro i
      by_cases hi : i < N
      · dsimp [U]
        rw [if_pos hi]
        apply Metric.ediam_image_le_iff.mpr
        intro t ht u hu
        rw [edist_dist, hf]
        apply ENNReal.ofReal_le_ofReal
        apply abs_le.mpr
        simp only [Set.mem_Icc, add_div] at ht hu
        constructor
        · linarith [ht.1, hu.2]
        · linarith [hu.1, ht.2]
      · simp [U, hi]
    refine ⟨U, ⟨?_, hd⟩, ?_⟩
    · intro z hz
      obtain ⟨i, hi, hit⟩ := hpart N hN (z (Fin.last 0)) hz.2
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      dsimp [U]
      rw [if_pos hi]
      refine ⟨z (Fin.last 0), hit, ?_⟩
      have hhead : GPhead z = (0 : GPEucl 0) := Subsingleton.elim _ _
      simpa only [f, ← hhead] using h_T001.2.1 0 z
    · calc
        GPcost a U = ∑ i ∈ Finset.range N, (Metric.ediam (U i)) ^ a := by
          apply tsum_eq_sum
          intro i hi
          have : ¬ i < N := by simpa using hi
          simp [U, this, ENNReal.zero_rpow_of_pos ha]
        _ ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by
          exact Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hd i) ha.le
        _ = (N : ENNReal) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by simp
        _ = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := hcost N a hN ha
  have hlimit : ∀ a : ℝ, 1 < a → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ δ ∧ (N : ℝ) ^ (1 - a) < ε := by
    intro a ha δ ε hδ hε
    have ht : Filter.Tendsto (fun x : ℝ => x ^ (1 - a)) Filter.atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop (show 0 < a - 1 by linarith)
      simpa only [neg_sub] using h
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
    obtain ⟨N, hN⟩ := exists_nat_gt (max T (max 0 (1 / δ)))
    have hNT : T ≤ (N : ℝ) := (le_max_left _ _).trans hN.le
    have hNpos : (0 : ℝ) < N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hN
    have hNδ : 1 / δ < (N : ℝ) :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hN
    refine ⟨N, Nat.cast_pos.mp hNpos, ?_, hT N hNT⟩
    apply (div_le_iff₀ hNpos).2
    have := (div_lt_iff₀ hδ).mp hNδ
    nlinarith
  intro hn
  obtain ⟨hE, hEss, hD⟩ := h_T005.2.2.2.2.2 hn
  have hcontent : ∀ a : ℝ, 1 < a → ∀ δ : ℝ, 0 < δ →
      GPcontent a δ (GPproduct E) = 0 := by
    intro a ha δ hδ
    apply le_antisymm _ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    simp only [zero_add]
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨N, hN, hNδ, hNa⟩ := hlimit a ha δ (ε : ℝ) hδ hεr
    obtain ⟨U, hU, hc⟩ := hcover hn N a hN (by linarith)
    have hUδ : GPcover (GPproduct E) δ U :=
      ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hNδ)⟩
    have hi : GPcontent a δ (GPproduct E) ≤ GPcost a U :=
      iInf_le_of_le U (iInf_le_of_le hUδ le_rfl)
    apply (hi.trans hc).trans
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hNa.le
  have hmass : ∀ a : ℝ, 1 < a → GPmass a (GPproduct E) = 0 := by
    intro a ha
    apply le_antisymm _ zero_le
    change (⨆ (δ : ℝ) (_ : 0 < δ), GPcontent a δ (GPproduct E)) ≤ 0
    exact iSup_le fun δ => iSup_le fun hδ => (hcontent a ha δ hδ).le
  constructor
  · rw [hD, zero_add]
    by_contra hnot
    have hlt : (1 : ENNReal) < dimH (GPproduct E) := lt_of_not_ge hnot
    obtain ⟨a, ha0, h1a, haD⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
    have ha : 1 < a := by
      have : ENNReal.ofReal (1 : ℝ) < ENNReal.ofReal a := by simpa using h1a
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp this
    have hb : dimH (GPproduct E) ≤ ENNReal.ofReal a :=
      (h_T003 (n + 1) (GPproduct E) a (by linarith)).2.2.2.2.1 (hmass a ha)
    exact (not_lt_of_ge hb) haD
  · intro q δ hq hδ
    have hqpos : 0 < q := by
      apply ENNReal.ofReal_pos.mp
      simpa only [hD] using hq
    exact ⟨hcontent (q + 1) (by linarith) δ hδ, hmass (q + 1) (by linarith)⟩

theorem T008 (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) :
    1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ U : ℕ → Set (GPEucl n),
    GPcover E r U ∧
    (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧
    GPcost q U < ENNReal.ofReal ε := by
  classical
  intro hn q r ε hdim hr hr1 hε
  have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (show (0 : ENNReal) ≤ dimH E from bot_le) hdim)
  rcases h_T003 n E q hq with ⟨hNative, hD, hzero, hinf, hzeroDim, hinfDim, hmono, hsmall, hlarge⟩
  obtain ⟨U₀, hcover, hcost⟩ := hsmall (hzero hdim) r (ε / 2) hr (half_pos hε)
  have hball : ∀ (hn : 1 ≤ n) (q r b : ℝ), 0 < q → 0 < r → 0 < b →
      ∀ x : GPEucl n, ∃ V : Set (GPEucl n), x ∈ V ∧ 0 < Metric.ediam V ∧
        Metric.ediam V ≤ ENNReal.ofReal r ∧ (Metric.ediam V) ^ q < ENNReal.ofReal b := by
    intro hn q r b hq hr hb x
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    letI : Nontrivial (GPEucl n) := inferInstance
    let ρ : ℝ := min r (b ^ q⁻¹) / 4
    have hp : 0 < ρ := div_pos (lt_min hr (Real.rpow_pos_of_pos hb _)) (by norm_num)
    have hd : Metric.ediam (Metric.ball x ρ) = ENNReal.ofReal (2 * ρ) := by
      rw [← Metric.diam_ball_eq x hp.le]
      exact (ENNReal.ofReal_toReal Metric.isBounded_ball.ediam_ne_top).symm
    refine ⟨Metric.ball x ρ, Metric.mem_ball_self hp, ?_, ?_, ?_⟩
    · rw [hd]; exact ENNReal.ofReal_pos.mpr (by positivity)
    · rw [hd]
      apply ENNReal.ofReal_le_ofReal
      have := min_le_left r (b ^ q⁻¹)
      dsimp [ρ]; linarith
    · rw [hd, ENNReal.ofReal_rpow_of_pos (by positivity)]
      apply (ENNReal.ofReal_lt_ofReal_iff hb).mpr
      have hlt : 2 * ρ < b ^ q⁻¹ := by
        have := min_le_right r (b ^ q⁻¹)
        have := Real.rpow_pos_of_pos hb q⁻¹
        dsimp [ρ]; linarith
      simpa only [Real.rpow_inv_rpow hb.le hq.ne'] using Real.rpow_lt_rpow (by positivity : 0 ≤ 2 * ρ) hlt hq
  let b : ℕ → ℝ := fun i => ε / 4 * (1 / 2 : ℝ) ^ i
  have hb : ∀ i, 0 < b i := by intro i; dsimp [b]; positivity
  have hsum : (∑' i, ENNReal.ofReal (b i)) = ENNReal.ofReal (ε / 2) := by
    dsimp [b]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_two.mul_left (ε / 4))]
    rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
    congr 1
    ring
  have hreplace : ∀ i : ℕ, ∃ V : Set (GPEucl n),
      U₀ i ⊆ V ∧ Metric.ediam V ≤ ENNReal.ofReal r ∧
      (V.Nonempty → 0 < Metric.ediam V) ∧
      (Metric.ediam V) ^ q ≤ (Metric.ediam (U₀ i)) ^ q + ENNReal.ofReal (b i) := by
    intro i
    by_cases hd : Metric.ediam (U₀ i) = 0
    · by_cases he : (U₀ i).Nonempty
      · obtain ⟨x, hx⟩ := he
        obtain ⟨V, hxV, hpos, hbound, hcheap⟩ := hball hn q r (b i) hq hr (hb i) x
        refine ⟨V, ?_, hbound, fun _ => hpos, ?_⟩
        · intro y hy
          have hyx : y = x := (Metric.ediam_eq_zero_iff.mp hd) hy hx
          simpa only [hyx] using hxV
        · exact hcheap.le.trans (le_add_left le_rfl)
      · refine ⟨U₀ i, (fun _ hx => hx), hcover.2 i, ?_, le_add_right le_rfl⟩
        intro hne
        exact (he hne).elim
    · exact ⟨U₀ i, (fun _ hx => hx), hcover.2 i, fun _ => pos_iff_ne_zero.mpr hd,
        le_add_right le_rfl⟩
  choose U hsub hbound hpos hterm using hreplace
  refine ⟨U, ⟨?_, hbound⟩, hpos, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, hsub i hi⟩
  · calc
      GPcost q U ≤ GPcost q U₀ + ∑' i, ENNReal.ofReal (b i) := by
        unfold GPcost
        rw [← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum hterm
      _ = GPcost q U₀ + ENNReal.ofReal (ε / 2) := by rw [hsum]
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hcost
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

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
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hq)
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
    have hij : j < N i ∧ (U i).Nonempty := ⟨hj, hine⟩
    simp only [V, if_pos hij, Set.mem_setOf_eq]
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
        exact bot_le
    have htotal : GPcost (q + 1) W ≤ ENNReal.ofReal C * GPcost q U := by
      calc
        GPcost (q + 1) W =
            ∑' i : ℕ, ∑' j : ℕ, (Metric.ediam (V i j)) ^ (q + 1) := by
          unfold GPcost
          change (∑' k : ℕ, (fun p : ℕ × ℕ => (Metric.ediam (V p.1 p.2)) ^ (q + 1))
            (Nat.pairEquiv.symm k)) = _
          rw [Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ =>
            (Metric.ediam (V p.1 p.2)) ^ (q + 1)), ENNReal.tsum_prod']
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

theorem T010 (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T007 : n = 0 →
  dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧ GPmass (q + 1) (GPproduct E) = 0) (h_T009 : 1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ W : ℕ → Set (GPEucl (n + 1)),
    GPcover (GPproduct E) (Real.sqrt 2 * r) W ∧
    GPcost (q + 1) W <
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) :
    dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧
    GPmass (q + 1) (GPproduct E) = 0 := by
  classical
  by_cases hn0 : n = 0
  · exact h_T007 hn0
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hcontent : ∀ (q δ : ℝ), 1 ≤ n → dimH E < ENNReal.ofReal q →
      0 < δ → GPcontent (q + 1) δ (GPproduct E) = 0 := by
    intro q δ hn hq hδ
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hsqrt)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrδ : Real.sqrt 2 * r ≤ δ := by
      have hh : r ≤ δ / Real.sqrt 2 := min_le_right _ _
      simpa only [mul_comm] using (le_div_iff₀ hsqrt).1 hh
    let C : ℝ := 2 * (Real.sqrt 2) ^ (q + 1)
    have hC : 0 < C := mul_pos (by norm_num) (Real.rpow_pos_of_pos hsqrt _)
    apply le_antisymm ?_ (by positivity)
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hηreal : 0 < (η : ℝ) := hη
    obtain ⟨W, hW, hcost⟩ := h_T009 hn q r ((η : ℝ) / C) hq hr hr1 (div_pos hηreal hC)
    have hcover : GPcover (GPproduct E) δ W := by
      exact ⟨hW.1, fun i => (hW.2 i).trans (ENNReal.ofReal_le_ofReal hrδ)⟩
    have hinf : GPcontent (q + 1) δ (GPproduct E) ≤ GPcost (q + 1) W :=
      iInf_le_of_le W (iInf_le _ hcover)
    have hsmall : GPcost (q + 1) W < ENNReal.ofReal (η : ℝ) := by
      convert hcost using 1
      dsimp [C] at *
      congr 1
      field_simp
    simpa using (hinf.trans hsmall.le)
  have hmass : ∀ q : ℝ, dimH E < ENNReal.ofReal q →
      GPmass (q + 1) (GPproduct E) = 0 := by
    intro q hq
    apply le_antisymm ?_ (by positivity)
    unfold GPmass
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    rw [hcontent q δ hn hq hδ]
  have hbound : ∀ q : ℝ, dimH E < ENNReal.ofReal q →
      dimH (GPproduct E) ≤ ENNReal.ofReal (q + 1) := by
    intro q hq
    have hqpos : 0 < q := ENNReal.ofReal_pos.1 (lt_of_le_of_lt (by positivity) hq)
    have hs : 0 < q + 1 := by linarith
    exact (h_T003 (n + 1) (GPproduct E) (q + 1) hs).2.2.2.2.1 (hmass q hq)
  have hendpoint : ∀ (D F : ENNReal), D < ⊤ →
      (∀ q : ℝ, D < ENNReal.ofReal q → F ≤ ENNReal.ofReal (q + 1)) →
      F ≤ D + 1 := by
    intro D F hD hb
    have hq₀ : D < ENNReal.ofReal (D.toReal + 1) :=
      (ENNReal.lt_ofReal_iff_toReal_lt hD.ne).2 (by linarith)
    have hF : F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb _ hq₀)
    have hsum : ENNReal.ofReal (D.toReal + 1) = D + 1 := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
        ENNReal.ofReal_toReal hD.ne, ENNReal.ofReal_one]
    by_contra hh
    have hgap : D.toReal + 1 < F.toReal := by
      apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hF).1
      rw [hsum]
      exact lt_of_not_ge hh
    obtain ⟨q, hqD, hqF⟩ := exists_between (show D.toReal < F.toReal - 1 by linarith)
    have hq : D < ENNReal.ofReal q := (ENNReal.lt_ofReal_iff_toReal_lt hD.ne).2 hqD
    have hqpos : 0 < q := lt_of_le_of_lt ENNReal.toReal_nonneg hqD
    have hbq : F.toReal ≤ q + 1 :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) (hb q hq)
    linarith
  refine ⟨hendpoint (dimH E) (dimH (GPproduct E)) h_T005.2.2.2.2.1.2.2 hbound, ?_⟩
  intro q δ hq hδ
  exact ⟨hcontent q δ hn hq hδ, hmass q hq⟩

theorem T006 (n : ℕ) (E : Set (GPEucl n))  :
    ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η) := by
  intro B ρ η hB hρ hpair hη
  obtain ⟨b₀, hb₀⟩ := hB
  have habove : BddAbove B := by
    refine ⟨b₀ + ρ, ?_⟩
    intro b hb
    have h := (abs_le.mp (hpair b hb b₀ hb₀)).2
    linarith
  have hbelow : BddBelow B := by
    refine ⟨b₀ - ρ, ?_⟩
    intro b hb
    have h := (abs_le.mp (hpair b hb b₀ hb₀)).1
    linarith
  have hlub : IsLUB B (sSup B) := isLUB_csSup ⟨b₀, hb₀⟩ habove
  have hglb : IsGLB B (sInf B) := isGLB_csInf ⟨b₀, hb₀⟩ hbelow
  have hsup : ∀ b' ∈ B, sSup B ≤ b' + ρ := by
    intro b' hb'
    apply hlub.2
    intro b hb
    have h := (abs_le.mp (hpair b hb b' hb')).2
    linarith
  have hlower : sSup B - ρ ≤ sInf B := by
    apply hglb.2
    intro b hb
    have h := hsup b hb
    linarith
  have hdiam : sSup B - sInf B ≤ ρ := by linarith
  have hcontain : B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) := by
    intro b hb
    have hlo : sInf B ≤ b := hglb.1 hb
    have hhi : b ≤ sSup B := hlub.1 hb
    constructor <;> linarith
  have horder : sInf B ≤ sSup B := le_trans (hglb.1 hb₀) (hlub.1 hb₀)
  refine ⟨habove, hbelow, hlub, hglb, hdiam, hcontain, ?_, ?_⟩
  · linarith
  · linarith

theorem T011 (n : ℕ) (E : Set (GPEucl n)) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T006 : ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η)) :
    ∀ (s δ ε : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → 0 < ε → GPcover (GPproduct E) δ V →
  (∀ i, Metric.ediam (GPhead '' V i) ≤ Metric.ediam (V i)) ∧
  ∃ a b : ℕ → ℝ, ∀ i, (V i).Nonempty →
    a i < b i ∧
    (∀ z ∈ V i, z (Fin.last n) ∈ Set.Ioo (a i) (b i)) ∧
    b i - a i ≤ (Metric.ediam (V i)).toReal +
      ε * (2 : ℝ) ^ (-(i : ℝ) - 1) /
        (1 + (Metric.ediam (V i)).toReal ^ s) := by
  classical
  intro s δ ε V hs hδ hε hV
  have hfin (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  have hdist (i : ℕ) (z w : GPEucl (n + 1)) (hz : z ∈ V i) (hw : w ∈ V i) :
      dist z w ≤ (Metric.ediam (V i)).toReal := by
    rw [dist_edist]
    exact ENNReal.toReal_mono (hfin i) (Metric.edist_le_ediam_of_mem hz hw)
  constructor
  · intro i
    apply Metric.ediam_image_le_iff.mpr
    intro z hz w hw
    have hc : edist (GPhead z) (GPhead w) ≤ edist z w := by
      rw [edist_dist, edist_dist]
      exact ENNReal.ofReal_le_ofReal ((h_T001.2.2.2 n z w).1)
    exact hc.trans (Metric.edist_le_ediam_of_mem hz hw)
  · let ρ : ℕ → ℝ := fun i => (Metric.ediam (V i)).toReal
    let η : ℕ → ℝ := fun i => ε * (2 : ℝ) ^ (-(i : ℝ) - 1) / (1 + ρ i ^ s)
    have hη (i : ℕ) : 0 < η i := by
      have hp : 0 ≤ ρ i ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg s
      exact div_pos (mul_pos hε (Real.rpow_pos_of_pos (by norm_num) _)) (by linarith)
    have intervals : ∀ i, ∃ a b : ℝ, (V i).Nonempty →
        a < b ∧ (∀ z ∈ V i, z (Fin.last n) ∈ Set.Ioo a b) ∧ b - a ≤ ρ i + η i := by
      intro i
      by_cases hi : (V i).Nonempty
      · let B : Set ℝ := (fun z : GPEucl (n + 1) => z (Fin.last n)) '' V i
        have hB : B.Nonempty := hi.image _
        have hpair : ∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ i := by
          rintro b ⟨z, hz, rfl⟩ b' ⟨w, hw, rfl⟩
          exact ((h_T001.2.2.2 n z w).2).trans (hdist i z w hz hw)
        rcases h_T006 B (ρ i) (η i) hB ENNReal.toReal_nonneg hpair (hη i) with
          ⟨_, _, _, _, _, hsub, hlt, hlen⟩
        refine ⟨sInf B - η i / 2, sSup B + η i / 2, fun _ => ⟨hlt, ?_, hlen⟩⟩
        intro z hz
        exact hsub ⟨z, hz, rfl⟩
      · exact ⟨0, 0, fun h => (hi h).elim⟩
    choose a b hab using intervals
    exact ⟨a, b, hab⟩

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
          exact Set.indicator_of_mem (show t ∈ J i ∩ GPI from ⟨hi, ht⟩) _]
        exact ENNReal.rpow_le_rpow (hproj i) hs.le
      · simp [U, hi, g, Set.indicator_of_notMem, ENNReal.zero_rpow_of_pos hs, show t ∉ J i ∩ GPI from fun h => hi h.1]
    · rw [Set.indicator_of_notMem ht]
      exact bot_le
  have hg (i : ℕ) : Measurable (g i) :=
    measurable_const.indicator (measurableSet_Ioo.inter measurableSet_Icc)
  have hint :
      c ≤ ∑' i, ρ i ^ s * MeasureTheory.volume (J i ∩ GPI) := by
    calc
      c = MeasureTheory.lintegral MeasureTheory.volume (GPI.indicator (fun _ => c)) := by
        change c = MeasureTheory.lintegral MeasureTheory.volume
          (fun t : ℝ => (Set.Icc (0 : ℝ) 1).indicator (fun _ => c) t)
        rw [MeasureTheory.lintegral_indicator_const measurableSet_Icc]
        simp [Real.volume_Icc]
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

theorem T013 (n : ℕ) (E : Set (GPEucl n)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T012 : ∀ (s δ : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → GPcover (GPproduct E) δ V →
  ∀ ε : ℝ, 0 < ε →
    GPcontent s δ E ≤ GPcost (s + 1) V + ENNReal.ofReal ε) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GPcontent s δ E ≤ GPcontent (s + 1) δ (GPproduct E) := by
  intro s δ hs hδ
  change GPcontent s δ E ≤ ⨅ (V : ℕ → Set (GPEucl (n + 1))) (_ : GPcover (GPproduct E) δ V), GPcost (s + 1) V
  refine le_iInf fun V => le_iInf fun hV => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεreal : 0 < (ε : ℝ) := NNReal.coe_pos.mpr hε
  have hεcoe : ENNReal.ofReal (ε : ℝ) = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal
  simpa only [hεcoe] using h_T012 s δ V hs hδ hV (ε : ℝ) hεreal

theorem T018 (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T013 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GPcontent s δ E ≤ GPcontent (s + 1) δ (GPproduct E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (GPproduct E) := by
  intro hDpos
  have hDfin : dimH E ≠ ⊤ := h_T005.2.2.2.2.1.2.2.ne
  have hbound : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
      ENNReal.ofReal (s + 1) ≤ dimH (GPproduct E) := by
    intro s hs hsD
    have hEinfty : GPmass s E = ⊤ := (h_T003 n E s hs).2.2.2.1 hsD
    have hmassle : GPmass s E ≤ GPmass (s + 1) (GPproduct E) := by
      unfold GPmass
      exact iSup_mono fun δ => iSup_mono fun hδ => h_T013 s δ hs hδ
    have hFinfty : GPmass (s + 1) (GPproduct E) = ⊤ := by
      rw [hEinfty] at hmassle
      exact top_unique hmassle
    exact (h_T003 (n + 1) (GPproduct E) (s + 1) (by linarith)).2.2.2.2.2.1 hFinfty
  by_contra hnot
  have hlt : dimH (GPproduct E) < dimH E + 1 := lt_of_not_ge hnot
  have hdfin : dimH (GPproduct E) ≠ ⊤ := (lt_of_lt_of_le hlt le_top).ne
  have hD1fin : dimH E + 1 ≠ ⊤ := by simp [hDfin]
  have hDreal : 0 < (dimH E).toReal := ENNReal.toReal_pos hDpos.ne' hDfin
  have hdreal : (dimH (GPproduct E)).toReal < (dimH E).toReal + 1 := by
    have h := (ENNReal.toReal_lt_toReal hdfin hD1fin).2 hlt
    simpa only [ENNReal.toReal_add hDfin (by simp : (1 : ENNReal) ≠ ⊤), ENNReal.toReal_one] using h
  have hmax : max 0 ((dimH (GPproduct E)).toReal - 1) < (dimH E).toReal :=
    max_lt hDreal (by linarith)
  obtain ⟨s, hsmax, hsD⟩ := exists_between hmax
  have hs : 0 < s := lt_of_le_of_lt (le_max_left _ _) hsmax
  have hds : (dimH (GPproduct E)).toReal < s + 1 := by
    have := lt_of_le_of_lt (le_max_right 0 ((dimH (GPproduct E)).toReal - 1)) hsmax
    linarith
  have hsDE : ENNReal.ofReal s < dimH E := by
    rw [← ENNReal.ofReal_toReal hDfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hDreal).2 hsD
  have hdF : dimH (GPproduct E) < ENNReal.ofReal (s + 1) := by
    rw [← ENNReal.ofReal_toReal hdfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < s + 1)).2 hds
  exact (not_lt_of_ge (hbound s hs hsDE)) hdF

theorem T014 (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) :
    dimH GPI ≤ 1 ∧ ∀ a : ℝ, 1 < a → GPmass a GPI = 0 := by
  classical
  have hz : ∀ a : ℝ, 1 < a → GPmass a GPI = 0 := by
    have hcov : ∀ a : ℝ, 1 < a → ∀ N : ℕ, 0 < N →
        ∃ U : ℕ → Set ℝ, GPcover GPI (1 / (N : ℝ)) U ∧
          GPcost a U = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
      classical
      have hpart : ∀ N : ℕ, 0 < N → ∀ x : ℝ, 0 ≤ x → x ≤ N →
          ∃ i : ℕ, i < N ∧ (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          intro hn x hx hxN
          by_cases hN : N = 0
          · subst N
            exact ⟨0, by omega, by simpa using hx, by simpa using hxN⟩
          · by_cases h : x ≤ N
            · obtain ⟨i, hi, hix, hxi⟩ := ih (Nat.pos_of_ne_zero hN) x hx h
              exact ⟨i, by omega, hix, hxi⟩
            · exact ⟨N, Nat.lt_succ_self N, le_of_not_ge h, by exact_mod_cast hxN⟩
      intro a ha N hN
      have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      let U : ℕ → Set ℝ := fun i =>
        if i < N then Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) else ∅
      have hd : ∀ i, Metric.ediam (U i) =
          if i < N then ENNReal.ofReal (1 / (N : ℝ)) else 0 := by
        intro i
        by_cases hi : i < N
        · simp only [U, if_pos hi, Real.ediam_Icc]
          congr 1
          ring
        · simp [U, hi]
      have hc : GPcover GPI (1 / (N : ℝ)) U := by
        constructor
        · intro x hx
          obtain ⟨i, hi, hil, hiu⟩ := hpart N hN (x * N)
            (mul_nonneg hx.1 hNp.le) (by nlinarith [hx.2])
          apply Set.mem_iUnion.mpr
          refine ⟨i, ?_⟩
          simp only [U, if_pos hi, Set.mem_Icc]
          exact ⟨(div_le_iff₀ hNp).mpr hil, (le_div_iff₀ hNp).mpr hiu⟩
        · intro i
          rw [hd]
          split_ifs <;> simp
      have hcost : GPcost a U = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
        unfold GPcost
        rw [tsum_eq_sum (s := Finset.range N) (fun i hi => ?_)]
        · calc
            ∑ i ∈ Finset.range N, Metric.ediam (U i) ^ a =
                ∑ i ∈ Finset.range N, (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hd, if_pos (Finset.mem_range.mp hi)]
            _ = (N : ENNReal) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by simp
            _ = ENNReal.ofReal ((N : ℝ) * (1 / (N : ℝ)) ^ a) := by
              rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNp),
                ENNReal.ofReal_mul hNp.le, ENNReal.ofReal_natCast]
            _ = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
              congr 1
              rw [sub_eq_add_neg, Real.rpow_add hNp, Real.rpow_one,
                Real.rpow_neg_eq_inv_rpow, one_div]
        · rw [hd, if_neg (by simpa using hi)]
          exact ENNReal.zero_rpow_of_pos (by linarith)
      exact ⟨U, hc, hcost⟩
    intro a ha
    have hlimR : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a))
        Filter.atTop (nhds 0) := by
      simpa only [neg_sub, Function.comp_def] using
        (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    have hlim : Filter.Tendsto
        (fun N : ℕ => ENNReal.ofReal ((N : ℝ) ^ (1 - a)))
        Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hlimR
    have hscale : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ))
        Filter.atTop (nhds 0) := by
      simpa only [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    apply le_antisymm _ zero_le
    unfold GPmass
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    apply ge_of_tendsto hlim
    have hs : ∀ᶠ N : ℕ in Filter.atTop, 1 / (N : ℝ) ≤ δ :=
      hscale.eventually (eventually_le_nhds hδ)
    filter_upwards [hs, Filter.eventually_gt_atTop (0 : ℕ)] with N hNδ hN
    obtain ⟨U, hU, hcost⟩ := hcov a ha N hN
    have hUd : GPcover GPI δ U :=
      ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hNδ)⟩
    calc
      GPcontent a δ GPI ≤ GPcost a U := iInf_le_of_le U (iInf_le _ hUd)
      _ = _ := hcost
  have hdim : ∀ a : ℝ, 1 < a → dimH GPI ≤ ENNReal.ofReal a := by
    intro a ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    let d : NNReal := ⟨a, ha0.le⟩
    have hd : (d : ENNReal) = ENNReal.ofReal a := ENNReal.coe_nnreal_eq d
    have hm : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) GPI = 0 := by
      change MeasureTheory.Measure.hausdorffMeasure a GPI = 0
      rw [← h_T002.2 GPI a ha0, hz a ha]
    rw [← hd]
    exact dimH_le_of_hausdorffMeasure_ne_top (d := d) (by simp [hm])
  refine ⟨?_, hz⟩
  by_contra h
  have hh : (1 : ENNReal) < dimH GPI := lt_of_not_ge h
  obtain ⟨d, hd1, hdd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hh
  have hdr : (1 : ℝ) < (d : ℝ) := by
    exact_mod_cast hd1
  have hb : dimH GPI ≤ (d : ENNReal) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hdim (d : ℝ) hdr
  exact (not_le_of_gt hdd) hb

theorem T015 (n : ℕ) (E : Set (GPEucl n)) (h_T006 : ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η)) :
    ∀ (δ : ℝ) (U : ℕ → Set ℝ), 0 < δ →
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i) := by
  classical
  intro δ U hδ hU
  have hfin (i : ℕ) : Metric.ediam (U i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i)
  have hdiam (i : ℕ) : ENNReal.ofReal (Metric.diam (U i)) = Metric.ediam (U i) :=
    ENNReal.ofReal_toReal (hfin i)
  have hpair (i : ℕ) : ∀ b ∈ U i, ∀ b' ∈ U i, |b - b'| ≤ Metric.diam (U i) := by
    intro b hb b' hb'
    simpa only [Real.dist_eq] using Metric.dist_le_diam_of_mem' (hfin i) hb hb'
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεreal : 0 < (ε : ℝ) := hε
  let η : ℕ → ℝ := fun i => (ε : ℝ) / 2 / 2 ^ i
  have hη (i : ℕ) : 0 < η i := by dsimp [η]; positivity
  have hsumη : (∑' i, ENNReal.ofReal (η i)) = (ε : ENNReal) := by
    dsimp [η]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_two' (ε : ℝ)), tsum_geometric_two']
    simp
  let J : ℕ → Set ℝ := fun i =>
    if (U i).Nonempty then
      Set.Ioo (sInf (U i) - η i / 2) (sSup (U i) + η i / 2)
    else ∅
  have hJ (i : ℕ) : U i ⊆ J i ∧
      MeasureTheory.volume (J i) ≤ Metric.ediam (U i) + ENNReal.ofReal (η i) := by
    by_cases hi : (U i).Nonempty
    · obtain ⟨_, _, _, _, _, hsub, _, hlen⟩ :=
        h_T006 (U i) (Metric.diam (U i)) (η i) hi Metric.diam_nonneg (hpair i) (hη i)
      have hJi : J i = Set.Ioo (sInf (U i) - η i / 2) (sSup (U i) + η i / 2) := by
        simp only [J, if_pos hi]
      rw [hJi]
      refine ⟨hsub, ?_⟩
      rw [Real.volume_Ioo]
      calc
        ENNReal.ofReal (sSup (U i) + η i / 2 - (sInf (U i) - η i / 2))
            ≤ ENNReal.ofReal (Metric.diam (U i) + η i) := ENNReal.ofReal_le_ofReal hlen
        _ = Metric.ediam (U i) + ENNReal.ofReal (η i) := by
          rw [ENNReal.ofReal_add Metric.diam_nonneg (hη i).le, hdiam i]
    · have hempty : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp [J, hi, hempty]
  have hcov : GPI ⊆ ⋃ i, J i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, (hJ i).1 hi⟩
  calc
    (1 : ENNReal) = MeasureTheory.volume GPI := by
      simp [GPI, Real.volume_Icc]
    _ ≤ MeasureTheory.volume (⋃ i, J i) := MeasureTheory.measure_mono hcov
    _ ≤ ∑' i, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
    _ ≤ ∑' i, (Metric.ediam (U i) + ENNReal.ofReal (η i)) :=
      ENNReal.tsum_le_tsum (fun i => (hJ i).2)
    _ = (∑' i, Metric.ediam (U i)) + ε := by rw [ENNReal.tsum_add, hsumη]

theorem T016 (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T014 : dimH GPI ≤ 1 ∧ ∀ a : ℝ, 1 < a → GPmass a GPI = 0) (h_T015 : ∀ (δ : ℝ) (U : ℕ → Set ℝ), 0 < δ →
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i)) :
    dimH GPI = 1 ∧
  ∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤ := by
  have hreal : ∀ (s δ ρ : ℝ), 0 < s → s < 1 → 0 < δ →
      0 ≤ ρ → ρ ≤ δ → δ ^ (s - 1) * ρ ≤ ρ ^ s := by
    intro s δ ρ hs hs1 hδ hρ hρδ
    by_cases hzero : ρ = 0
    · subst ρ
      simp [Real.zero_rpow (ne_of_gt hs)]
    · have hpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hzero)
      calc
        δ ^ (s - 1) * ρ ≤ ρ ^ (s - 1) * ρ :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hpos hρδ (by linarith)) hρ
        _ = ρ ^ s := by simpa using (Real.rpow_add hpos (s - 1) 1).symm
  have hterm : ∀ (s δ : ℝ) (d : ENNReal), 0 < s → s < 1 →
      0 < δ → d ≤ ENNReal.ofReal δ →
      ENNReal.ofReal (δ ^ (s - 1)) * d ≤ d ^ s := by
    intro s δ d hs hs1 hδ hd
    have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd
    have hconv : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hdtop
    have hpow : d ^ s = ENNReal.ofReal (d.toReal ^ s) := by
      calc
        d ^ s = (ENNReal.ofReal d.toReal) ^ s :=
          congrArg (fun x : ENNReal => x ^ s) hconv.symm
        _ = _ := ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le
    calc
      ENNReal.ofReal (δ ^ (s - 1)) * d =
          ENNReal.ofReal (δ ^ (s - 1) * d.toReal) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hconv]
      _ ≤ ENNReal.ofReal (d.toReal ^ s) :=
        ENNReal.ofReal_le_ofReal (hreal s δ d.toReal hs hs1 hδ
          ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hδ.le hd))
      _ = d ^ s := hpow.symm
  have hinfinite : ∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤ := by
    intro s hs hs1
    have hcontent : ∀ δ : ℝ, 0 < δ →
        ENNReal.ofReal (δ ^ (s - 1)) ≤ GPcontent s δ GPI := by
      intro δ hδ
      unfold GPcontent
      refine le_iInf fun U => le_iInf fun hU => ?_
      calc
        ENNReal.ofReal (δ ^ (s - 1)) =
            ENNReal.ofReal (δ ^ (s - 1)) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (δ ^ (s - 1)) * ∑' i, Metric.ediam (U i) :=
          mul_le_mul_left' (h_T015 δ U hδ hU) _
        _ = ∑' i, ENNReal.ofReal (δ ^ (s - 1)) * Metric.ediam (U i) :=
          ENNReal.tsum_mul_left.symm
        _ ≤ GPcost s U :=
          ENNReal.tsum_le_tsum (fun i => hterm s δ (Metric.ediam (U i)) hs hs1 hδ (hU.2 i))
    have hbound : ∀ δ : ℝ, 0 < δ →
        ENNReal.ofReal (δ ^ (s - 1)) ≤ GPmass s GPI := by
      intro δ hδ
      exact (hcontent δ hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
    have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ (s - 1)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (⊤ : ENNReal)) :=
      ENNReal.tendsto_ofReal_atTop.comp
        (tendsto_rpow_neg_nhdsGT_zero (by linarith : s - 1 < 0))
    apply top_unique
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hbound δ hδ
  refine ⟨le_antisymm h_T014.1 ?_, hinfinite⟩
  apply le_of_not_gt
  intro hlt
  obtain ⟨s, hs0, hds, hs1⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hs : 0 < s := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hds)
  have hsone : s < 1 := by
    have : ENNReal.ofReal s < ENNReal.ofReal 1 := by simpa using hs1
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp this
  have hm : MeasureTheory.Measure.hausdorffMeasure s GPI = ⊤ :=
    (h_T002.2 GPI s hs).symm.trans (hinfinite s hs hsone)
  have hscoe : (s.toNNReal : ℝ) = s := by
    simp [Real.toNNReal_of_nonneg hs.le]
  have hn : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) GPI = ⊤ := by
    rwa [hscoe]
  have hle : ENNReal.ofReal s ≤ dimH GPI :=
    le_dimH_of_hausdorffMeasure_eq_top (d := s.toNNReal) hn
  exact (not_lt_of_ge hle) hds

theorem T017 (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T016 : dimH GPI = 1 ∧
  ∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤) :
    dimH GPI = 1 ∧
  (∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤) ∧
  (∀ (k : ℕ) (A : Set (GPEucl k)) (e : GPI → GPEucl k),
    (∀ t, e t ∈ A) →
    (∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)|) →
    (1 : ENNReal) ≤ dimH A ∧
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
      GPcontent s δ GPI ≤ GPcontent s δ A) := by
  classical
  refine ⟨h_T016.1, h_T016.2, ?_⟩
  intro k A e heA he
  have hed : ∀ t u : GPI, edist (t : ℝ) (u : ℝ) = edist (e t) (e u) := by
    intro t u
    rw [edist_dist, edist_dist, he, Real.dist_eq]
  have hc : ∀ (s δ : ℝ), 0 < s → 0 < δ →
      GPcontent s δ GPI ≤ GPcontent s δ A := by
    intro s δ hs hδ
    unfold GPcontent
    refine le_iInf fun V => le_iInf fun hV => ?_
    let P : ℕ → Set ℝ := fun i => {t | ∃ ht : t ∈ GPI, e ⟨t, ht⟩ ∈ V i}
    have hd : ∀ i, Metric.ediam (P i) ≤ Metric.ediam (V i) := by
      intro i
      apply Metric.ediam_le
      intro t ht u hu
      rcases ht with ⟨ht, hte⟩
      rcases hu with ⟨hu, hue⟩
      rw [hed ⟨t, ht⟩ ⟨u, hu⟩]
      exact Metric.edist_le_ediam_of_mem hte hue
    have hp : GPcover GPI δ P := by
      constructor
      · intro t ht
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 (heA ⟨t, ht⟩))
        exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩
      · intro i
        exact (hd i).trans (hV.2 i)
    calc
      (⨅ (U : ℕ → Set ℝ) (_ : GPcover GPI δ U), GPcost s U) ≤ GPcost s P :=
        iInf_le_of_le P (iInf_le_of_le hp le_rfl)
      _ ≤ GPcost s V := by
        unfold GPcost
        exact ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hd i) hs.le
  have hm : ∀ s : ℝ, 0 < s → GPmass s GPI ≤ GPmass s A := by
    intro s hs
    unfold GPmass
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hc s δ hs hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  refine ⟨?_, hc⟩
  by_contra hn
  have hlt : dimH A < (1 : ENNReal) := lt_of_not_ge hn
  obtain ⟨s, hs0, hds, hs1⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hs : 0 < s := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hds)
  have hsone : s < 1 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 1 by norm_num)).mp
    simpa using hs1
  have htop : GPmass s A = ⊤ := by
    apply top_unique
    calc
      ⊤ = GPmass s GPI := (h_T016.2 s hs hsone).symm
      _ ≤ GPmass s A := hm s hs
  have hdims : ENNReal.ofReal s ≤ dimH A := (h_T003 k A s hs).2.2.2.2.2.1 htop
  exact (not_lt_of_ge hdims) hds

theorem T019 (n : ℕ) (E : Set (GPEucl n)) (h_H001 : E.Nonempty) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T017 : dimH GPI = 1 ∧
  (∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤) ∧
  (∀ (k : ℕ) (A : Set (GPEucl k)) (e : GPI → GPEucl k),
    (∀ t, e t ∈ A) →
    (∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)|) →
    (1 : ENNReal) ≤ dimH A ∧
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
      GPcontent s δ GPI ≤ GPcontent s δ A)) :
    dimH E = 0 → dimH E + 1 ≤ dimH (GPproduct E) := by
  intro hdim
  obtain ⟨x₀, hx₀⟩ := h_H001
  let e : GPI → GPEucl (n + 1) := fun t => GPappend x₀ (t : ℝ)
  have he_mem : ∀ t, e t ∈ GPproduct E := by
    intro t
    change GPhead (GPappend x₀ (t : ℝ)) ∈ E ∧
      (GPappend x₀ (t : ℝ)) (Fin.last n) ∈ GPI
    rw [(h_T001.1 n x₀ (t : ℝ)).1, (h_T001.1 n x₀ (t : ℝ)).2]
    exact ⟨hx₀, t.property⟩
  have he_dist : ∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)| := by
    intro t u
    change dist (GPappend x₀ (t : ℝ)) (GPappend x₀ (u : ℝ)) = _
    rw [h_T001.2.2.1 n x₀ x₀ (t : ℝ) (u : ℝ), dist_self]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
      Real.sqrt_sq_eq_abs, abs_abs]
  have hbound : (1 : ENNReal) ≤ dimH (GPproduct E) :=
    (h_T017.2.2 (n + 1) (GPproduct E) e he_mem he_dist).1
  simpa only [hdim, zero_add] using hbound

theorem T020 (n : ℕ) (E : Set (GPEucl n)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T010 : dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧
    GPmass (q + 1) (GPproduct E) = 0) (h_T018 : 0 < dimH E → dimH E + 1 ≤ dimH (GPproduct E)) (h_T019 : dimH E = 0 → dimH E + 1 ≤ dimH (GPproduct E)) :
    dimH (GPproduct E) = dimH E + 1 := by
  apply le_antisymm h_T010.1
  have hnonneg : 0 ≤ dimH E := h_T005.2.2.2.2.1.1
  rcases lt_or_eq_of_le hnonneg with hpos | hzero
  · exact h_T018 hpos
  · exact h_T019 hzero.symm

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (GPEucl n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_H003 : 0 ≤ n) :
    dimH (GPproduct E) = dimH E + 1 := by
  have h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) := @T002 n E 
  have h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A) := @T003 n E h_T002
  have h_T004 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) := @T004 n E h_H002
  have h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) := @T005 n E h_H001 h_T003 h_T004
  have h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w) := @T001 n E 
  have h_T007 : n = 0 →
  dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧ GPmass (q + 1) (GPproduct E) = 0 := @T007 n E h_T001 h_T003 h_T005
  have h_T008 : 1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ U : ℕ → Set (GPEucl n),
    GPcover E r U ∧
    (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧
    GPcost q U < ENNReal.ofReal ε := @T008 n E h_T003 h_T005
  have h_T009 : 1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ W : ℕ → Set (GPEucl (n + 1)),
    GPcover (GPproduct E) (Real.sqrt 2 * r) W ∧
    GPcost (q + 1) W <
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := @T009 n E h_T001 h_T008
  have h_T010 : dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧
    GPmass (q + 1) (GPproduct E) = 0 := @T010 n E h_T003 h_T005 h_T007 h_T009
  have h_T006 : ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η) := @T006 n E 
  have h_T011 : ∀ (s δ ε : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → 0 < ε → GPcover (GPproduct E) δ V →
  (∀ i, Metric.ediam (GPhead '' V i) ≤ Metric.ediam (V i)) ∧
  ∃ a b : ℕ → ℝ, ∀ i, (V i).Nonempty →
    a i < b i ∧
    (∀ z ∈ V i, z (Fin.last n) ∈ Set.Ioo (a i) (b i)) ∧
    b i - a i ≤ (Metric.ediam (V i)).toReal +
      ε * (2 : ℝ) ^ (-(i : ℝ) - 1) /
        (1 + (Metric.ediam (V i)).toReal ^ s) := @T011 n E h_T001 h_T006
  have h_T012 : ∀ (s δ : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → GPcover (GPproduct E) δ V →
  ∀ ε : ℝ, 0 < ε →
    GPcontent s δ E ≤ GPcost (s + 1) V + ENNReal.ofReal ε := @T012 n E h_T005 h_T011
  have h_T013 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GPcontent s δ E ≤ GPcontent (s + 1) δ (GPproduct E) := @T013 n E h_T005 h_T012
  have h_T018 : 0 < dimH E → dimH E + 1 ≤ dimH (GPproduct E) := @T018 n E h_T003 h_T005 h_T013
  have h_T014 : dimH GPI ≤ 1 ∧ ∀ a : ℝ, 1 < a → GPmass a GPI = 0 := @T014 n E h_T002
  have h_T015 : ∀ (δ : ℝ) (U : ℕ → Set ℝ), 0 < δ →
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i) := @T015 n E h_T006
  have h_T016 : dimH GPI = 1 ∧
  ∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤ := @T016 n E h_T002 h_T014 h_T015
  have h_T017 : dimH GPI = 1 ∧
  (∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤) ∧
  (∀ (k : ℕ) (A : Set (GPEucl k)) (e : GPI → GPEucl k),
    (∀ t, e t ∈ A) →
    (∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)|) →
    (1 : ENNReal) ≤ dimH A ∧
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
      GPcontent s δ GPI ≤ GPcontent s δ A) := @T017 n E h_T003 h_T016
  have h_T019 : dimH E = 0 → dimH E + 1 ≤ dimH (GPproduct E) := @T019 n E h_H001 h_T001 h_T017
  have h_T020 : dimH (GPproduct E) = dimH E + 1 := @T020 n E h_T005 h_T010 h_T018 h_T019
  exact h_T020

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (E : Set (GPEucl n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_H003 : 0 ≤ n) : dimH (GPproduct E) = dimH E + 1 := by
  exact @Translation.P n E h_H001 h_H002 h_H003

#check @P
#print axioms P
end AuditBExport
