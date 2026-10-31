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

theorem T001 (n : ℕ) (E : Set (YEucl n))  :
    ∀ (m : ℕ) (A : Set (YEucl m)) (s : ℝ), 0 < s → YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A := by
  intro m A s hs
  classical
  have hterm (B : Set (YEucl m)) :
      (⨆ _ : B.Nonempty, Metric.ediam B ^ s) = Metric.ediam B ^ s := by
    by_cases hB : B.Nonempty
    · simp [hB]
    · have hB0 : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      simp [hB0, ENNReal.zero_rpow_of_pos hs]
  let C : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (U : ℕ → Set (YEucl m)) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, Metric.ediam (U i) ^ s
  have hcontent (δ : ℝ) : YContent s δ A = C (ENNReal.ofReal δ) := by
    simp only [YContent, YCover, YCost, iInf_and, C]
  have hmono : Antitone C := by
    intro r t hrt
    dsimp [C]
    refine le_iInf fun U => le_iInf fun hA => le_iInf fun hU => ?_
    exact iInf_le_of_le U (iInf_le_of_le hA
      (iInf_le_of_le (fun i => (hU i).trans hrt) le_rfl))
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  simp_rw [hterm]
  change (⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A) =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r), C r
  simp_rw [hcontent]
  apply le_antisymm
  · refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact le_iSup_of_le (ENNReal.ofReal δ)
      (le_iSup_of_le (ENNReal.ofReal_pos.mpr hδ) le_rfl)
  · refine iSup_le fun r => iSup_le fun hr => ?_
    by_cases hrTop : r = ⊤
    · subst r
      exact (hmono (show ENNReal.ofReal (1 : ℝ) ≤ ⊤ from le_top)).trans
        (le_iSup_of_le (1 : ℝ) (le_iSup_of_le (show (0 : ℝ) < 1 from zero_lt_one) le_rfl))
    · have hpos : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrTop
      have hconvert : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrTop
      exact le_iSup_of_le r.toReal (le_iSup_of_le hpos (by rw [hconvert]))

theorem T002 (n : ℕ) (E : Set (YEucl n)) (h_T001 : ∀ (m : ℕ) (A : Set (YEucl m)) (s : ℝ), 0 < s → YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A) :
    ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A := by
  intro m A
  refine ⟨bot_le, ?_⟩
  intro s hs
  have hr : (Real.toNNReal s : ℝ) = s := Real.coe_toNNReal s hs.le
  have he : (Real.toNNReal s : ℝ≥0∞) = ENNReal.ofReal s :=
    ENNReal.ofNNReal_toNNReal s
  refine ⟨h_T001 m A s hs, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h_T001 m A s hs]
    have h' : dimH A < (Real.toNNReal s : ℝ≥0∞) := by
      simpa only [he] using h
    simpa only [hr] using
      (hausdorffMeasure_of_dimH_lt (s := A) (d := Real.toNNReal s) h')
  · intro h
    rw [h_T001 m A s hs]
    have h' : (Real.toNNReal s : ℝ≥0∞) < dimH A := by
      simpa only [he] using h
    simpa only [hr] using
      (hausdorffMeasure_of_lt_dimH (s := A) (d := Real.toNNReal s) h')
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (Real.toNNReal s : ℝ) A ≠ ⊤ := by
      rw [hr, ← h_T001 m A s hs, h]
      exact ENNReal.zero_ne_top
    simpa only [he] using
      (dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := Real.toNNReal s) hm)
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (Real.toNNReal s : ℝ) A = ⊤ := by
      rw [hr, ← h_T001 m A s hs]
      exact h
    simpa only [he] using
      (le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := Real.toNNReal s) hm)

theorem T005 (n : ℕ) (E : Set (YEucl n)) (h_H002 : IsCompact E) :
    (∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, |x i| ≤ L) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤) := by
  constructor
  · classical
    let B : ℕ → Set (YEucl n) := fun k => {x | ∀ i : Fin n, |x i| < (k : ℝ) + 1}
    have hBo : ∀ k, IsOpen (B k) := by
      intro k
      dsimp only [B]
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).abs continuous_const)
    have hBc : E ⊆ ⋃ k, B k := by
      intro x hx
      obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      intro i
      have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
      dsimp [B]
      linarith
    obtain ⟨t, ht⟩ := h_H002.elim_finite_subcover B hBo hBc
    let L : ℝ := (∑ k ∈ t, ((k : ℝ) + 1)) + 1
    have hsum : 0 ≤ ∑ k ∈ t, ((k : ℝ) + 1) :=
      Finset.sum_nonneg (fun k hk => by positivity)
    refine ⟨L, by dsimp [L]; linarith, ?_⟩
    intro x hx i
    obtain ⟨k, hkt, hxk⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hk : (k : ℝ) + 1 ≤ ∑ j ∈ t, ((j : ℝ) + 1) :=
      Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) + 1) (fun j hj => by positivity) hkt
    have hi : |x i| < (k : ℝ) + 1 := hxk i
    dsimp [L]
    linarith
  · classical
    intro s δ hs hδ
    have hδ2 : 0 < δ / 2 := half_pos hδ
    have hc : E ⊆ ⋃ a : E, Metric.ball a.val (δ / 2) := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hδ2⟩
    obtain ⟨t, ht⟩ := h_H002.elim_finite_subcover
      (fun a : E => Metric.ball a.val (δ / 2)) (fun a => Metric.isOpen_ball) hc
    let e : t ≃ Fin t.card := t.equivFin
    let U : ℕ → Set (YEucl n) := fun j =>
      if hj : j < t.card then Metric.ball (e.symm ⟨j, hj⟩).val.val (δ / 2) else ∅
    have hcov : E ⊆ ⋃ j, U j := by
      intro x hx
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
      let a' : t := ⟨a, ha⟩
      let j : Fin t.card := e a'
      have hU : U j.val = Metric.ball a.val (δ / 2) := by
        dsimp only [U]
        rw [dif_pos j.isLt]
        change Metric.ball (e.symm (e a')).val.val (δ / 2) = _
        rw [e.symm_apply_apply]
      exact Set.mem_iUnion.mpr ⟨j.val, by rw [hU]; exact hxa⟩
    have hb : ∀ c : YEucl n, Metric.ediam (Metric.ball c (δ / 2)) ≤ ENNReal.ofReal δ := by
      intro c
      apply Metric.ediam_le_of_forall_dist_le
      intro x hx y hy
      have hx' : dist x c < δ / 2 := Metric.mem_ball.mp hx
      have hy' : dist c y < δ / 2 := by simpa only [dist_comm] using Metric.mem_ball.mp hy
      have htri : dist x y ≤ dist x c + dist c y := dist_triangle x c y
      linarith
    have hd : ∀ j, Metric.ediam (U j) ≤ ENNReal.ofReal δ := by
      intro j
      dsimp only [U]
      split_ifs with hj
      · exact hb _
      · simp only [Metric.ediam_empty]; exact zero_le
    have hcover : YCover δ E U := ⟨hcov, hd⟩
    have hzero : ∀ j, j ∉ Finset.range t.card → (Metric.ediam (U j)) ^ s = 0 := by
      intro j hj
      have hj' : ¬ j < t.card := by simpa only [Finset.mem_range] using hj
      simp only [U, dif_neg hj', Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]
    have hcost : YCost s U < ⊤ := by
      unfold YCost
      rw [tsum_eq_sum hzero]
      apply ENNReal.sum_lt_top.mpr
      intro j hj
      apply (ENNReal.rpow_lt_top_iff_of_pos hs).mpr
      exact (hd j).trans_lt ENNReal.ofReal_lt_top
    have hle : YContent s δ E ≤ YCost s U := by
      unfold YContent
      exact iInf_le_of_le U (iInf_le_of_le hcover le_rfl)
    exact hle.trans_lt hcost

theorem T006 (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T005 : (∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, |x i| ≤ L) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤) := by
  classical
  have hc : YCritical E := h_T002 n E
  have hzero : n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0 := by
    intro hn
    subst n
    have hsub : E.Subsingleton := fun x hx y hy => Subsingleton.elim x y
    have huniv : E = Set.univ := by
      rcases h_H001 with ⟨x, hx⟩
      apply Set.eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y x] using hx
    have hhaus : ∀ s : ℝ, 0 < s → YHaus s E = 0 := by
      intro s hs
      apply le_antisymm _ bot_le
      refine iSup_le fun δ => iSup_le fun hδ => ?_
      let U : ℕ → Set (YEucl 0) := fun i => if i = 0 then E else ∅
      have hdiam : ∀ i, Metric.ediam (U i) = 0 := by
        intro i
        by_cases hi : i = 0
        · simp only [U, if_pos hi, Metric.ediam_subsingleton hsub]
        · simp only [U, if_neg hi, Metric.ediam_empty]
      have hcov : YCover δ E U := by
        constructor
        · intro x hx
          apply Set.mem_iUnion.mpr
          exact ⟨0, by simpa only [U, if_pos rfl] using hx⟩
        · intro i
          rw [hdiam i]
          exact bot_le
      change YContent s δ E ≤ 0
      calc
        YContent s δ E ≤ YCost s U := iInf_le_of_le U (iInf_le _ hcov)
        _ = 0 := by simp [YCost, hdiam, ENNReal.zero_rpow_of_pos hs]
    have hdim : dimH E = 0 := by
      apply le_antisymm _ hc.1
      by_contra h
      have hpos : 0 < dimH E := lt_of_not_ge h
      obtain ⟨a, ha0, ha, haD⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
      have hap : 0 < a := ENNReal.ofReal_pos.mp ha
      have hle : dimH E ≤ ENNReal.ofReal a :=
        (hc.2 a hap).2.2.2.1 (hhaus a hap)
      exact (not_lt_of_ge hle) haD
    exact ⟨huniv, hsub, hdim⟩
  have hbound : dimH E ≤ (n : ℝ≥0∞) := by
    by_cases hn : n = 0
    · simpa only [hn, Nat.cast_zero, (hzero hn).2.2] using
        (le_refl (0 : ℝ≥0∞))
    · have hpositive : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hvanish : ∀ a : ℝ, (n : ℝ) < a →
          MeasureTheory.Measure.hausdorffMeasure a E = 0 := by
        intro a ha
        have hf : (Module.finrank ℝ (YEucl n) : ℝ) < a := by
          simpa only [YEucl, finrank_euclideanSpace_fin] using ha
        have hm : (MeasureTheory.Measure.hausdorffMeasure a :
            MeasureTheory.Measure (YEucl n)) = 0 :=
          Real.hausdorffMeasure_of_finrank_lt (E := YEucl n) hf
        rw [hm]
        rfl
      have hexponent : ∀ a : ℝ, (n : ℝ) < a → dimH E ≤ ENNReal.ofReal a := by
        intro a ha
        have hap : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
        have hhaus : YHaus a E = 0 :=
          (hc.2 a hap).1.trans (hvanish a ha)
        exact (hc.2 a hap).2.2.2.1 hhaus
      by_contra h
      obtain ⟨a, ha0, hna, haD⟩ :=
        ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
      have hncast : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := by simp
      have hna' : (n : ℝ) < a := by
        rw [← hncast] at hna
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg n)).mp hna
      exact (not_lt_of_ge (hexponent a hna')) haD
  exact ⟨⟨hc.1, hbound, lt_of_le_of_lt hbound (by simp)⟩, hzero, h_T005.2⟩

theorem T003 (n : ℕ) (E : Set (YEucl n))  :
    (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine := by
  have hsq : ∀ (m : ℕ) (z w : YEucl (m+1)),
      dist z w ^ 2 = dist (YBase z) (YBase w) ^ 2 + |YLast z-YLast w| ^ 2 := by
    intro m z w
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc, EuclideanSpace.dist_sq_eq]
    simp [YBase, YLast, Real.dist_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m x y t u
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_castSucc, EuclideanSpace.dist_sq_eq]
    simp [YJoin, Real.dist_eq]
  · intro m z
    ext i
    cases i using Fin.lastCases <;> simp [YJoin, YBase, YLast]
  · intro m x t
    constructor
    · ext i
      simp [YBase, YJoin]
    · simp [YLast, YJoin]
  · intro m
    constructor
    · apply LipschitzWith.mk_one
      intro z w
      have h := hsq m z w
      have hz : 0 ≤ dist z w := dist_nonneg
      have hb : 0 ≤ dist (YBase z) (YBase w) := dist_nonneg
      nlinarith [sq_nonneg (YLast z-YLast w)]
    · apply LipschitzWith.mk_one
      intro z w
      rw [Real.dist_eq]
      have h := hsq m z w
      have hz : 0 ≤ dist z w := dist_nonneg
      have hl : 0 ≤ |YLast z-YLast w| := abs_nonneg _
      nlinarith [sq_nonneg (dist (YBase z) (YBase w))]
  · apply Isometry.of_dist_eq
    intro t u
    simpa [EuclideanSpace.dist_eq, YLine, Real.dist_eq] using
      (Real.sqrt_sq_eq_abs (t-u))
  · intro z
    refine ⟨z 0, ?_⟩
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [YLine, hi]

theorem T004 (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) :
    (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ YI = YContent s δ (YLine '' YI)) ∧ (∀ s : ℝ, 0 < s → YHaus s YI = YHaus s (YLine '' YI)) ∧ dimH YI = dimH (YLine '' YI) := by
  have hi : Isometry YLine := h_T003.2.2.2.2.1
  have hs : Function.Surjective YLine := h_T003.2.2.2.2.2
  have hdpre : ∀ S : Set (YEucl 1), Metric.ediam (YLine ⁻¹' S) = Metric.ediam S := by
    intro S
    calc
      Metric.ediam (YLine ⁻¹' S) = Metric.ediam (YLine '' (YLine ⁻¹' S)) :=
        (hi.ediam_image _).symm
      _ = Metric.ediam S := congrArg Metric.ediam (Set.image_preimage_eq S hs)
  have hc : ∀ s δ : ℝ, YContent s δ YI = YContent s δ (YLine '' YI) := by
    intro s δ
    apply le_antisymm
    · unfold YContent
      refine le_iInf fun U => le_iInf fun hU => ?_
      have hV : YCover δ YI (fun i => YLine ⁻¹' U i) := by
        constructor
        · intro x hx
          have hmem := hU.1 (Set.mem_image_of_mem YLine hx)
          obtain ⟨i, hiU⟩ := Set.mem_iUnion.mp hmem
          exact Set.mem_iUnion.mpr ⟨i, hiU⟩
        · intro i
          rw [hdpre]
          exact hU.2 i
      refine iInf_le_of_le (fun i => YLine ⁻¹' U i) (iInf_le_of_le hV ?_)
      exact le_of_eq (by simp only [YCost, hdpre])
    · unfold YContent
      refine le_iInf fun U => le_iInf fun hU => ?_
      have hV : YCover δ (YLine '' YI) (fun i => YLine '' U i) := by
        constructor
        · rintro z ⟨x, hx, rfl⟩
          obtain ⟨i, hiU⟩ := Set.mem_iUnion.mp (hU.1 hx)
          exact Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem YLine hiU⟩
        · intro i
          rw [hi.ediam_image]
          exact hU.2 i
      refine iInf_le_of_le (fun i => YLine '' U i) (iInf_le_of_le hV ?_)
      exact le_of_eq (by simp only [YCost, hi.ediam_image])
  refine ⟨fun s δ _ _ => hc s δ, ?_, (hi.dimH_image YI).symm⟩
  intro s hs
  unfold YHaus
  simp only [hc]

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

theorem T008 (n : ℕ) (E : Set (YEucl n))  :
    ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) := by
  classical
  intro δ hδ U hU
  have hbdd (i : ℕ) : Bornology.IsBounded (U i) :=
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i))
  let K : Set ℕ := {i | (U i).Nonempty}
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  have hεR : 0 < (ε : ℝ) := hε
  let b : ℕ → ℝ := fun i => (ε : ℝ) / 2 / 2 ^ i
  have hbpos (i : ℕ) : 0 < b i := by dsimp [b]; positivity
  have hbsum : (∑' i : ℕ, ENNReal.ofReal (b i)) = (ε : ℝ≥0∞) := by
    dsimp [b]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_two' (ε : ℝ)), tsum_geometric_two']
    simp
  let J : K → Set ℝ := fun i =>
    Set.Ioo (sInf (U i) - b i / 2) (sSup (U i) + b i / 2)
  have hsub (i : K) : U i ⊆ J i := by
    intro x hx
    have hb := (hbdd i).subset_Icc_sInf_sSup hx
    change sInf (U i) - b i / 2 < x ∧ x < sSup (U i) + b i / 2
    constructor <;> linarith [hbpos i, hb.1, hb.2]
  have hvol (i : K) : MeasureTheory.volume (J i) =
      Metric.ediam (U i) + ENNReal.ofReal (b i) := by
    dsimp [J]
    rw [Real.volume_Ioo, Real.ediam_eq (hbdd i)]
    have hd : 0 ≤ sSup (U i) - sInf (U i) := by
      rw [← Real.diam_eq (hbdd i)]
      exact Metric.diam_nonneg
    have he : sSup (U i) + b i / 2 - (sInf (U i) - b i / 2) =
        (sSup (U i) - sInf (U i)) + b i := by ring
    rw [he, ENNReal.ofReal_add hd (hbpos i).le]
  have hcover : YI ⊆ ⋃ i : K, J i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hsub ⟨i, ⟨x, hi⟩⟩ hi⟩
  calc
    (1 : ℝ≥0∞) = MeasureTheory.volume YI := by simp [YI, Real.volume_Icc]
    _ ≤ MeasureTheory.volume (⋃ i : K, J i) := MeasureTheory.measure_mono hcover
    _ ≤ ∑' i : K, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
    _ = ∑' i : K, (Metric.ediam (U i) + ENNReal.ofReal (b i)) := tsum_congr hvol
    _ = (∑' i : K, Metric.ediam (U i)) + ∑' i : K, ENNReal.ofReal (b i) := ENNReal.tsum_add
    _ ≤ (∑' i : ℕ, Metric.ediam (U i)) + ∑' i : ℕ, ENNReal.ofReal (b i) :=
      add_le_add
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun i : K => (i : ℕ)) Subtype.coe_injective (fun i => Metric.ediam (U i)))
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun i : K => (i : ℕ)) Subtype.coe_injective (fun i => ENNReal.ofReal (b i)))
    _ = (∑' i : ℕ, Metric.ediam (U i)) + ε := by rw [hbsum]

theorem T009 (n : ℕ) (E : Set (YEucl n)) (h_T008 : ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)) :
    (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤) := by
  have hpoint : ∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ →
      ∀ r : ℝ≥0∞, r ≤ ENNReal.ofReal δ →
        (ENNReal.ofReal δ) ^ (s - 1) * r ≤ r ^ s := by
    intro s δ hs hs1 hδ r hr
    by_cases h0 : r = 0
    · simp [h0, ENNReal.zero_rpow_of_pos hs]
    have ht : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr
    have hp : (ENNReal.ofReal δ) ^ (s - 1) ≤ r ^ (s - 1) := by
      have he : s - 1 = -(1 - s) := by ring
      rw [he, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hr (by linarith))
    calc
      (ENNReal.ofReal δ) ^ (s - 1) * r ≤ r ^ (s - 1) * r := by gcongr
      _ = r ^ s := by
        simpa only [sub_add_cancel, ENNReal.rpow_one] using
          (ENNReal.rpow_add (s - 1) 1 h0 ht).symm
  have hcover : ∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ →
      ∀ U : ℕ → Set ℝ, YCover δ YI U →
        (ENNReal.ofReal δ) ^ (s - 1) ≤ YCost s U := by
    intro s δ hs hs1 hδ U hU
    calc
      (ENNReal.ofReal δ) ^ (s - 1) =
          (ENNReal.ofReal δ) ^ (s - 1) * 1 := (mul_one _).symm
      _ ≤ (ENNReal.ofReal δ) ^ (s - 1) * ∑' i, Metric.ediam (U i) := by
        gcongr
        exact h_T008 δ hδ U hU
      _ = ∑' i, (ENNReal.ofReal δ) ^ (s - 1) * Metric.ediam (U i) :=
        ENNReal.tsum_mul_left.symm
      _ ≤ YCost s U := ENNReal.tsum_le_tsum fun i =>
        hpoint s δ hs hs1 hδ (Metric.ediam (U i)) (hU.2 i)
  refine ⟨hcover, ?_⟩
  intro s hs hs1
  have hcontent : ∀ δ : ℝ, 0 < δ →
      (ENNReal.ofReal δ) ^ (s - 1) ≤ YContent s δ YI := by
    intro δ hδ
    unfold YContent
    exact le_iInf fun U => le_iInf fun hU => hcover s δ hs hs1 hδ U hU
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro M
  have hlim := tendsto_rpow_neg_nhdsGT_zero (show s - 1 < 0 by linarith)
  have he : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), (M : ℝ) ≤ δ ^ (s - 1) :=
    hlim.eventually (Filter.eventually_ge_atTop (M : ℝ))
  have hp : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hM, hδ⟩ := (he.and hp).exists
  have hbound : (M : ℝ≥0∞) ≤ (ENNReal.ofReal δ) ^ (s - 1) := by
    rw [ENNReal.ofReal_rpow_of_pos hδ]
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hM
  exact hbound.trans ((hcontent δ hδ).trans
    (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)))

theorem T010 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T004 : (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ YI = YContent s δ (YLine '' YI)) ∧ (∀ s : ℝ, 0 < s → YHaus s YI = YHaus s (YLine '' YI)) ∧ dimH YI = dimH (YLine '' YI)) (h_T007 : ∀ a : ℝ, 1 < a → YHaus a YI = 0) (h_T008 : ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)) (h_T009 : (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)) :
    dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤) := by
  have hupper : ∀ a : ℝ, 1 < a → dimH YI ≤ ENNReal.ofReal a := by
    intro a ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have hz : YHaus a (YLine '' YI) = 0 :=
      (h_T004.2.1 a ha0).symm.trans (h_T007 a ha)
    rw [h_T004.2.2]
    exact ((h_T002 1 (YLine '' YI)).2 a ha0).2.2.2.1 hz
  have hlower : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH YI := by
    intro s hs hs1
    have ht : YHaus s (YLine '' YI) = ⊤ :=
      (h_T004.2.1 s hs).symm.trans (h_T009.2 s hs hs1)
    rw [h_T004.2.2]
    exact ((h_T002 1 (YLine '' YI)).2 s hs).2.2.2.2 ht
  have hd : dimH YI ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper 2 (by norm_num))
  have hrealupper : (dimH YI).toReal ≤ 1 := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    have ha0 : 0 ≤ a := le_of_lt (lt_trans zero_lt_one ha)
    have hc : (dimH YI).toReal ≤ (ENNReal.ofReal a).toReal :=
      (ENNReal.toReal_le_toReal (a := dimH YI) (b := ENNReal.ofReal a)
        hd ENNReal.ofReal_ne_top).2 (hupper a ha)
    simpa only [ENNReal.toReal_ofReal ha0] using hc
  have hreallower : (1 : ℝ) ≤ (dimH YI).toReal := by
    apply le_of_forall_lt_imp_le_of_dense
    intro s hs1
    by_cases hs : 0 < s
    · have hc : (ENNReal.ofReal s).toReal ≤ (dimH YI).toReal :=
        (ENNReal.toReal_le_toReal (a := ENNReal.ofReal s) (b := dimH YI)
          ENNReal.ofReal_ne_top hd).2 (hlower s hs hs1)
      simpa only [ENNReal.toReal_ofReal hs.le] using hc
    · exact le_trans (le_of_not_gt hs) ENNReal.toReal_nonneg
  have hdim : dimH YI = 1 := by
    calc
      dimH YI = ENNReal.ofReal (dimH YI).toReal := (ENNReal.ofReal_toReal hd).symm
      _ = 1 := by rw [le_antisymm hrealupper hreallower]; norm_num
  refine ⟨hdim, h_T007, ?_, h_T009.2⟩
  intro s δ hs hs1 hδ U hU
  exact ⟨h_T008 δ hδ U hU, h_T009.1 s δ hs hs1 hδ U hU⟩

theorem T011 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T010 : dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)) :
    n = 0 → dimH (YF E) ≤ dimH E + 1 := by
  intro hn
  rcases h_T006.2.1 hn with ⟨hE, hsub, hD⟩
  let f : ℝ → YEucl (n + 1) := fun t => YJoin (0 : YEucl n) t
  have h0 : (0 : YEucl n) ∈ E := by rw [hE]; trivial
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    dsimp [f]
    rw [h_T003.1 n 0 0 t u]
    simp [Real.sqrt_sq_eq_abs, Real.dist_eq]
  have hF : YF E = f '' YI := by
    ext z
    constructor
    · rintro ⟨x, hx, t, ht, hz⟩
      have hx0 : x = 0 := hsub hx h0
      exact ⟨t, ht, by simpa [f, hx0] using hz.symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, h0, t, ht, rfl⟩
  have hcontent : ∀ (a δ : ℝ), 0 < a →
      YContent a δ (YF E) ≤ YContent a δ YI := by
    intro a δ ha
    unfold YContent
    refine le_iInf fun U => le_iInf fun hU => ?_
    let V : ℕ → Set (YEucl (n + 1)) := fun i => f '' (U i ∩ YI)
    have hd : ∀ i, Metric.ediam (V i) ≤ Metric.ediam (U i) := by
      intro i
      dsimp [V]
      rw [hf.ediam_image]
      exact Metric.ediam_mono Set.inter_subset_left
    have hV : YCover δ (YF E) V := by
      constructor
      · intro z hz
        rw [hF] at hz
        rcases hz with ⟨t, ht, rfl⟩
        rcases Set.mem_iUnion.mp (hU.1 ht) with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, t, ⟨hi, ht⟩, rfl⟩
      · intro i
        exact (hd i).trans (hU.2 i)
    have hbound : YContent a δ (YF E) ≤ YCost a V :=
      iInf_le_of_le V (iInf_le_of_le hV le_rfl)
    refine hbound.trans ?_
    exact ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hd i) ha.le
  have hhaus : ∀ a : ℝ, 1 < a → YHaus a (YF E) = 0 := by
    intro a ha
    apply le_antisymm _ zero_le
    rw [← h_T010.2.1 a ha]
    unfold YHaus
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hcontent a δ (lt_trans zero_lt_one ha)).trans
      (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hdim : ∀ a : ℝ, 1 < a → dimH (YF E) ≤ ENNReal.ofReal a := by
    intro a ha
    exact ((h_T002 (n + 1) (YF E)).2 a (lt_trans zero_lt_one ha)).2.2.2.1 (hhaus a ha)
  rw [hD, zero_add]
  by_contra h
  have hlt : (1 : ℝ≥0∞) < dimH (YF E) := lt_of_not_ge h
  rcases ENNReal.lt_iff_exists_real_btwn.mp hlt with ⟨a, ha0, ha1, haD⟩
  exact (not_lt_of_ge (hdim a (ENNReal.one_lt_ofReal.mp ha1))) haD

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
      exact (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => Metric.ediam (W p.1 p.2) ^ (q+1))).trans ENNReal.tsum_prod'
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

theorem T014 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T013 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ V : ℕ → Set (YEucl (n+1)), YCover (Real.sqrt 2 * r) (YF E) V ∧ YCost (q+1) V < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε)) :
    1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → YHaus (q+1) (YF E) = 0 ∧ dimH (YF E) ≤ ENNReal.ofReal (q+1) := by
  intro hn q hq
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt h_T006.1.1 hq)
  have hqone : 0 < q + 1 := by linarith
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hC : 0 < 2 * (Real.sqrt 2) ^ (q+1) := by positivity
  have hcontent : ∀ δ : ℝ, 0 < δ → YContent (q+1) δ (YF E) = 0 := by
    intro δ hδ
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hrpos : 0 < r := lt_min (by norm_num) (div_pos hδ hsqrt)
    have hrone : r ≤ 1 := min_le_left _ _
    have hrscale : Real.sqrt 2 * r ≤ δ := by
      have h : r * Real.sqrt 2 ≤ δ := (le_div_iff₀ hsqrt).mp (min_le_right _ _)
      simpa only [mul_comm] using h
    have hsmall : ∀ e : ℝ, 0 < e → YContent (q+1) δ (YF E) < ENNReal.ofReal e := by
      intro e he
      let ε : ℝ := e / (2 * (Real.sqrt 2) ^ (q+1))
      have hε : 0 < ε := div_pos he hC
      have hconvert : ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) = ENNReal.ofReal e := by
        congr 1
        exact mul_div_cancel₀ e (ne_of_gt hC)
      obtain ⟨V, hV, hcost⟩ := h_T013 hn q hqpos hq r hrpos hrone ε hε
      have hVδ : YCover δ (YF E) V := by
        refine ⟨hV.1, fun i => (hV.2 i).trans (ENNReal.ofReal_le_ofReal hrscale)⟩
      have hle : YContent (q+1) δ (YF E) ≤ YCost (q+1) V := by
        exact iInf_le_of_le V (iInf_le_of_le hVδ le_rfl)
      exact hle.trans_lt (hconvert ▸ hcost)
    by_contra hne
    have hpos : 0 < YContent (q+1) δ (YF E) := bot_lt_iff_ne_bot.mpr hne
    obtain ⟨e, he0, hepos, helt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
    exact (lt_irrefl (YContent (q+1) δ (YF E))) ((hsmall e (ENNReal.ofReal_pos.mp hepos)).trans helt)
  have hhaus : YHaus (q+1) (YF E) = 0 := by
    apply le_antisymm _ zero_le
    exact iSup_le fun δ => iSup_le fun hδ => le_of_eq (hcontent δ hδ)
  refine ⟨hhaus, ?_⟩
  exact ((h_T002 (n+1) (YF E)).2 (q+1) hqone).2.2.2.1 hhaus

theorem T015 (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T011 : n = 0 → dimH (YF E) ≤ dimH E + 1) (h_T014 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → YHaus (q+1) (YF E) = 0 ∧ dimH (YF E) ≤ ENNReal.ofReal (q+1)) :
    dimH (YF E) ≤ dimH E + 1 := by
  by_cases hn : n = 0
  · exact h_T011 hn
  · have hn1 : 1 ≤ n := by omega
    have hD : dimH E ≠ ⊤ := ne_of_lt h_T006.1.2.2
    have hconv : ENNReal.ofReal (dimH E).toReal = dimH E := ENNReal.ofReal_toReal hD
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hlt : ENNReal.ofReal (dimH E).toReal < ENNReal.ofReal ((dimH E).toReal + (ε : ℝ)) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    have hq : dimH E < ENNReal.ofReal ((dimH E).toReal + (ε : ℝ)) :=
      hconv.symm.trans_lt hlt
    have hbound := (h_T014 hn1 ((dimH E).toReal + (ε : ℝ)) hq).2
    have heq : ENNReal.ofReal (((dimH E).toReal + (ε : ℝ)) + 1) = (dimH E + 1) + (ε : ℝ≥0∞) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg, hconv]
      simp only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one]
      ac_rfl
    exact hbound.trans_eq heq

theorem T016 (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ, (∀ i, IsOpen (J i)) ∧ (∀ i, YLast '' (V i) ⊆ J i) ∧ (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s))) ∧ (∀ t ∈ YI, YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t) := by
  classical
  have interval : ∀ (B : Set ℝ), Bornology.IsBounded B → ∀ η : ℝ, 0 < η →
      ∃ J : Set ℝ, IsOpen J ∧ B ⊆ J ∧
        MeasureTheory.volume J ≤ Metric.ediam B + ENNReal.ofReal η := by
    intro B hB η hη
    by_cases hne : B.Nonempty
    · refine ⟨Set.Ioo (sInf B - η / 2) (sSup B + η / 2), isOpen_Ioo, ?_, ?_⟩
      · intro t ht
        have hlo : sInf B ≤ t := csInf_le hB.bddBelow ht
        have hhi : t ≤ sSup B := le_csSup hB.bddAbove ht
        constructor <;> linarith
      · rw [Real.volume_Ioo]
        have heq : sSup B + η / 2 - (sInf B - η / 2) = (sSup B - sInf B) + η := by ring
        rw [heq, Real.ediam_eq hB]
        exact ENNReal.ofReal_add_le
    · refine ⟨∅, isOpen_empty, ?_, ?_⟩
      · simpa only [Set.not_nonempty_iff_eq_empty.mp hne] using (Set.Subset.refl (∅ : Set ℝ))
      · simp
  intro s δ hs hδ V hV ε hε
  have hbase : LipschitzWith 1 (@YBase n) := (h_T003.2.2.2.1 n).1
  have hlast : LipschitzWith 1 (@YLast n) := (h_T003.2.2.2.1 n).2
  have hprojBase (i : ℕ) : Metric.ediam (YBase '' V i) ≤ Metric.ediam (V i) := by
    simpa using hbase.ediam_image_le (V i)
  have hprojLast (i : ℕ) : Metric.ediam (YLast '' V i) ≤ Metric.ediam (V i) := by
    simpa using hlast.ediam_image_le (V i)
  have hfinite (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  let η : ℕ → ℝ := fun i =>
    ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s)
  have hη (i : ℕ) : 0 < η i := by
    dsimp [η]
    apply div_pos
    · exact mul_pos hε (zpow_pos (by norm_num) _)
    · have hr : 0 ≤ (Metric.ediam (V i)).toReal ^ s :=
        Real.rpow_nonneg ENNReal.toReal_nonneg s
      linarith
  have hex (i : ℕ) : ∃ J : Set ℝ, IsOpen J ∧ YLast '' V i ⊆ J ∧
      MeasureTheory.volume J ≤ Metric.ediam (V i) + ENNReal.ofReal (η i) := by
    have hb : Bornology.IsBounded (YLast '' V i) :=
      Metric.isBounded_iff_ediam_ne_top.mpr
        (ne_top_of_le_ne_top (hfinite i) (hprojLast i))
    obtain ⟨J, ho, hsub, hv⟩ := interval (YLast '' V i) hb (η i) (hη i)
    exact ⟨J, ho, hsub, hv.trans (add_le_add (hprojLast i) (le_refl (ENNReal.ofReal (η i))))⟩
  choose J hJo hJsub hJvol using hex
  refine ⟨J, hJo, hJsub, hJvol, ?_⟩
  intro t ht
  let U : ℕ → Set (YEucl n) := fun i => if t ∈ J i then YBase '' V i else ∅
  have hcover : YCover δ E U := by
    constructor
    · intro x hx
      have hjoin : YJoin x t ∈ YF E := ⟨x, hx, t, ht, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hjoin)
      have hlastmem : t ∈ YLast '' V i :=
        ⟨YJoin x t, hi, (h_T003.2.2.1 n x t).2⟩
      have hti : t ∈ J i := hJsub i hlastmem
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change x ∈ if t ∈ J i then YBase '' V i else ∅
      rw [if_pos hti]
      exact ⟨YJoin x t, hi, (h_T003.2.2.1 n x t).1⟩
    · intro i
      dsimp [U]
      split_ifs with hti
      · exact (hprojBase i).trans (hV.2 i)
      · simp
  have hcontent : YContent s δ E ≤ YCost s U :=
    iInf_le_of_le U (iInf_le_of_le hcover le_rfl)
  refine hcontent.trans ?_
  unfold YCost
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hti : t ∈ J i
  · simpa [U, hti] using ENNReal.rpow_le_rpow (hprojBase i) hs.le
  · simp [U, hti, ENNReal.zero_rpow_of_pos hs]

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

theorem T018 (n : ℕ) (E : Set (YEucl n)) (h_T017 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → YContent s δ E ≤ YCost (s+1) V) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E ≤ YContent (s+1) δ (YF E) := by
  intro s δ hs hδ
  unfold YContent
  refine le_iInf fun V => le_iInf fun hV => ?_
  exact h_T017 s δ hs hδ V hV

theorem T019 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T018 : ∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E ≤ YContent (s+1) δ (YF E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (YF E) := by
  intro hD
  have hDfin : dimH E < ⊤ := h_T006.1.2.2
  have hDpos : 0 < (dimH E).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hD, hDfin⟩
  have hDeq : ENNReal.ofReal (dimH E).toReal = dimH E :=
    ENNReal.ofReal_toReal hDfin.ne
  have hbelow : ∀ s : ℝ, s < (dimH E).toReal → ENNReal.ofReal s < dimH E := by
    intro s hs
    rw [← hDeq]
    exact (ENNReal.ofReal_lt_ofReal_iff hDpos).2 hs
  have hbound : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
      ENNReal.ofReal (s + 1) ≤ dimH (YF E) := by
    intro s hs hsD
    have hEinf : YHaus s E = ⊤ := ((h_T002 n E).2 s hs).2.2.1 hsD
    have hcomp : YHaus s E ≤ YHaus (s + 1) (YF E) := by
      unfold YHaus
      exact iSup_mono fun δ => iSup_mono fun hδ => h_T018 s δ hs hδ
    have hFinf : YHaus (s + 1) (YF E) = ⊤ := by
      apply top_unique
      rw [← hEinf]
      exact hcomp
    exact ((h_T002 (n + 1) (YF E)).2 (s + 1) (by linarith)).2.2.2.2 hFinf
  by_cases hFtop : dimH (YF E) = ⊤
  · rw [hFtop]
    exact le_top
  · have hreal : (dimH E).toReal + 1 ≤ (dimH (YF E)).toReal := by
      apply le_of_forall_lt_imp_le_of_dense
      intro r hr
      have hm : max 0 (r - 1) < (dimH E).toReal :=
        max_lt hDpos (by linarith)
      obtain ⟨s, hslo, hshi⟩ := exists_between hm
      have hspos : 0 < s := lt_of_le_of_lt (le_max_left _ _) hslo
      have hb : s + 1 ≤ (dimH (YF E)).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hFtop).mp (hbound s hspos (hbelow s hshi))
      have hrs : r - 1 < s := lt_of_le_of_lt (le_max_right _ _) hslo
      linarith
    have heq : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
      rw [ENNReal.ofReal_add hDpos.le (by norm_num), hDeq, ENNReal.ofReal_one]
    rw [← heq]
    exact ENNReal.ofReal_le_of_le_toReal hreal

theorem T020 (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T010 : dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)) :
    dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YF E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hD
  obtain ⟨x₀, hx₀⟩ := h_H001
  let j : ℝ → YEucl (n + 1) := fun t => YJoin x₀ t
  have hj : Isometry j := by
    apply Isometry.of_dist_eq
    intro t u
    rw [h_T003.1 n x₀ x₀ t u]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hcontent : ∀ (s δ : ℝ), 0 < s → 0 < δ →
      YContent s δ YI ≤ YContent s δ (YF E) := by
    intro s δ hs hδ
    unfold YContent
    refine le_iInf fun V => le_iInf fun hV => ?_
    let W : ℕ → Set ℝ := fun i => {t | t ∈ YI ∧ j t ∈ V i}
    have hd : ∀ i, Metric.ediam (W i) ≤ Metric.ediam (V i) := by
      intro i
      apply Metric.ediam_le_iff.mpr
      intro t ht u hu
      rw [← hj.edist_eq t u]
      exact Metric.edist_le_ediam_of_mem ht.2 hu.2
    have hW : YCover δ YI W := by
      constructor
      · intro t ht
        have hmem : j t ∈ YF E := ⟨x₀, hx₀, t, ht, rfl⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hmem)
        exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩
      · intro i
        exact (hd i).trans (hV.2 i)
    have hbound : YContent s δ YI ≤ YCost s W := by
      unfold YContent
      exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
    have hcost : YCost s W ≤ YCost s V :=
      ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hd i) hs.le
    exact hbound.trans hcost
  have hhaus : ∀ s : ℝ, 0 < s → YHaus s YI ≤ YHaus s (YF E) := by
    intro s hs
    unfold YHaus
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hcontent s δ hs hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hdim : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH (YF E) := by
    intro s hs hs1
    have htop : YHaus s (YF E) = ⊤ := by
      apply top_unique
      rw [← h_T010.2.2.2 s hs hs1]
      exact hhaus s hs
    exact (h_T002 (n + 1) (YF E)).2 s hs |>.2.2.2.2 htop
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hr1
    have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
    have hr1' : r < 1 := by exact_mod_cast hr1
    have hr1'' : (r : ℝ) < 1 := by exact_mod_cast hr1'
    have heq : ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞) :=
      ENNReal.ofReal_coe_nnreal
    rw [← heq]
    exact hdim (r : ℝ) hr0 hr1''
  · simp [hD]

theorem T021 (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T015 : dimH (YF E) ≤ dimH E + 1) (h_T019 : 0 < dimH E → dimH E + 1 ≤ dimH (YF E)) (h_T020 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YF E) ∧ (1 : ℝ≥0∞) = dimH E + 1) :
    dimH (YF E) = dimH E + 1 := by
  apply le_antisymm h_T015
  by_cases hD : dimH E = 0
  · rcases h_T020 hD with ⟨h_lower, h_eq⟩
    exact h_eq ▸ h_lower
  · exact h_T019 (lt_of_le_of_ne bot_le (Ne.symm hD))

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) :
    dimH (YF E) = dimH E + 1 := by
  have h_T001 : ∀ (m : ℕ) (A : Set (YEucl m)) (s : ℝ), 0 < s → YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A := @T001 n E 
  have h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A := @T002 n E h_T001
  have h_T005 : (∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, |x i| ≤ L) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤) := @T005 n E h_H002
  have h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤) := @T006 n E h_H001 h_T002 h_T005
  have h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine := @T003 n E 
  have h_T004 : (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ YI = YContent s δ (YLine '' YI)) ∧ (∀ s : ℝ, 0 < s → YHaus s YI = YHaus s (YLine '' YI)) ∧ dimH YI = dimH (YLine '' YI) := @T004 n E h_T003
  have h_T007 : ∀ a : ℝ, 1 < a → YHaus a YI = 0 := @T007 n E 
  have h_T008 : ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) := @T008 n E 
  have h_T009 : (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤) := @T009 n E h_T008
  have h_T010 : dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤) := @T010 n E h_T002 h_T004 h_T007 h_T008 h_T009
  have h_T011 : n = 0 → dimH (YF E) ≤ dimH E + 1 := @T011 n E h_T002 h_T003 h_T006 h_T010
  have h_T012 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set (YEucl n), YCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ YCost q U < ENNReal.ofReal ε := @T012 n E h_T002
  have h_T013 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ V : ℕ → Set (YEucl (n+1)), YCover (Real.sqrt 2 * r) (YF E) V ∧ YCost (q+1) V < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) := @T013 n E h_T003 h_T012
  have h_T014 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → YHaus (q+1) (YF E) = 0 ∧ dimH (YF E) ≤ ENNReal.ofReal (q+1) := @T014 n E h_T002 h_T006 h_T013
  have h_T015 : dimH (YF E) ≤ dimH E + 1 := @T015 n E h_T006 h_T011 h_T014
  have h_T016 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ, (∀ i, IsOpen (J i)) ∧ (∀ i, YLast '' (V i) ⊆ J i) ∧ (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s))) ∧ (∀ t ∈ YI, YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t) := @T016 n E h_T003
  have h_T017 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → YContent s δ E ≤ YCost (s+1) V := @T017 n E h_T006 h_T016
  have h_T018 : ∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E ≤ YContent (s+1) δ (YF E) := @T018 n E h_T017
  have h_T019 : 0 < dimH E → dimH E + 1 ≤ dimH (YF E) := @T019 n E h_T002 h_T006 h_T018
  have h_T020 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YF E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := @T020 n E h_H001 h_T002 h_T003 h_T010
  have h_T021 : dimH (YF E) = dimH E + 1 := @T021 n E h_T006 h_T015 h_T019 h_T020
  exact h_T021

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) : dimH (YF E) = dimH E + 1 := by
  exact @Translation.P n E h_H001 h_H002

#check @P
#print axioms P
end AuditBExport
