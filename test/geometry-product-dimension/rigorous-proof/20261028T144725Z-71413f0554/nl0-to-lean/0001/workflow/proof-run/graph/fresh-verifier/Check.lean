import Mathlib
open scoped ENNReal NNReal
open Set MeasureTheory
abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def base {n : ℕ} (z : V (n+1)) : V n := WithLp.toLp 2 (fun i => z i.castSucc)
def height {n : ℕ} (z : V (n+1)) : ℝ := z (Fin.last n)
noncomputable def join {n : ℕ} (x : V n) (t : ℝ) : V (n+1) := WithLp.toLp 2 (Fin.lastCases t (fun i => x i))
def unitI : Set ℝ := Set.Icc 0 1
def cylinder {n : ℕ} (E : Set (V n)) : Set (V (n+1)) := {z | base z ∈ E ∧ height z ∈ unitI}
def scaleCover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop := A ⊆ (⋃ i, U i) ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [MetricSpace X] {K : Type*} (s : ℝ) (U : K → Set X) : ℝ≥0∞ := ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ := ⨅ (U : ℕ → Set X) (_ : scaleCover δ A U), cost s U
noncomputable def haus {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ := ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
noncomputable def padding {X : Type*} [MetricSpace X] (ε s : ℝ) (W : ℕ → Set X) (i : ℕ) : ℝ := ε * (2 : ℝ) ^ (-(i : ℝ)-1) / (1 + (Metric.diam (W i)) ^ s)
structure ScaleLaws : Prop where
  native_eq : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (s : ℝ), 0 < s → haus s A = MeasureTheory.Measure.hausdorffMeasure s A
  antitone : ∀ {X : Type} [MetricSpace X] (A : Set X) (s δ r : ℝ), 0 < s → 0 < δ → δ ≤ r → content s r A ≤ content s δ A
  supremum : ∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ), haus s A = ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
  unbounded : ∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ), 0 < s → haus s A = ⊤ → ∀ B : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ ≤ r → ENNReal.ofReal B < content s δ A
structure CriticalLaws : Prop where
  nonneg : ∀ {X : Type} [MetricSpace X] (A : Set X), 0 ≤ dimH A
  critical : ∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ), 0 < s → ((ENNReal.ofReal s < dimH A → haus s A = ⊤) ∧ (dimH A < ENNReal.ofReal s → haus s A = 0) ∧ (haus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧ (haus s A = ⊤ → ENNReal.ofReal s ≤ dimH A))
structure InvarianceLaws : Prop where
  mono : ∀ {X : Type} [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B
  isometry : ∀ {X Y : Type} [MetricSpace X] [MetricSpace Y] (A : Set X) (f : A → Y), Isometry f → (dimH (Set.range f) = dimH A ∧ ∀ s : ℝ, 0 < s → haus s (Set.range f) = haus s A)
structure PowerLaws : Prop where
  positive_limit : ∀ a : ℝ, 0 < a → Filter.Tendsto (fun h : ℝ => h ^ a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  negative_limit : ∀ b : ℝ, b < 0 → Filter.Tendsto (fun h : ℝ => h ^ b) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop
  series_one : (∑' i : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ)-1))) = 1
  series_half : (∑' i : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ)-2))) = (1/2 : ℝ≥0∞)

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (E : Set (V n))  :
    ScaleLaws := by
  classical
  have hmono : ∀ {X : Type} [MetricSpace X] (A : Set X) (s δ r : ℝ), δ ≤ r → content s r A ≤ content s δ A := by
    intro X _ A s δ r hdr
    unfold content
    refine le_iInf fun U => le_iInf fun hU => ?_
    exact iInf₂_le_of_le U ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hdr)⟩ le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X _ _ _ A s hs
    have hcost (U : ℕ → Set X) : (∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ s) = cost s U := by
      unfold cost
      apply tsum_congr
      intro i
      by_cases hi : (U i).Nonempty
      · simp [hi]
      · have he : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
        simp [he, ENNReal.zero_rpow_of_pos hs]
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    apply le_antisymm
    · refine iSup₂_le fun δ hδ => ?_
      refine le_iSup_of_le (ENNReal.ofReal δ) (le_iSup_of_le (ENNReal.ofReal_pos.mpr hδ) ?_)
      refine le_iInf fun U => le_iInf fun hcov => le_iInf fun hdiam => ?_
      rw [hcost]
      exact iInf₂_le_of_le U ⟨hcov, hdiam⟩ le_rfl
    · refine iSup₂_le fun r hr => ?_
      have hex : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r := by
        by_cases ht : r = ⊤
        · exact ⟨1, by norm_num, by simp [ht]⟩
        · exact ⟨r.toReal, ENNReal.toReal_pos hr.ne' ht, (ENNReal.ofReal_toReal ht).le⟩
      obtain ⟨δ, hδ, hdr⟩ := hex
      refine le_iSup_of_le δ (le_iSup_of_le hδ ?_)
      refine le_iInf fun U => le_iInf fun hU => ?_
      refine iInf_le_of_le U (iInf_le_of_le hU.1 (iInf_le_of_le (fun i => (hU.2 i).trans hdr) ?_))
      exact (hcost U).le
  · intro X _ A s δ r hs hδ hdr
    exact hmono A s δ r hdr
  · intro X _ A s
    rfl
  · intro X _ A s hs hinf B
    have hb : ENNReal.ofReal B < haus s A := by
      rw [hinf]
      exact ENNReal.ofReal_lt_top
    obtain ⟨r, hr, hBr⟩ : ∃ r : ℝ, ∃ _ : 0 < r, ENNReal.ofReal B < content s r A := by
      simpa only [haus, lt_iSup_iff] using hb
    exact ⟨r, hr, fun δ hδ hdr => hBr.trans_le (hmono A s δ r hdr)⟩

theorem T002 (n : ℕ) (E : Set (V n)) (h_T001 : ScaleLaws) :
    CriticalLaws := by
  constructor
  · intro X _ A
    exact bot_le
  · intro X _ A s hs
    borelize X
    let u : NNReal := ⟨s, hs.le⟩
    have hu : ENNReal.ofReal s = (u : ENNReal) :=
      (ENNReal.coe_nnreal_eq u).symm
    have hnative : haus s A = MeasureTheory.Measure.hausdorffMeasure (u : ℝ) A :=
      h_T001.native_eq A s hs
    constructor
    · intro h
      rw [hnative]
      exact hausdorffMeasure_of_lt_dimH (d := u) (hu ▸ h)
    constructor
    · intro h
      rw [hnative]
      exact hausdorffMeasure_of_dimH_lt (d := u) (hu ▸ h)
    constructor
    · intro h
      have hz : MeasureTheory.Measure.hausdorffMeasure (u : ℝ) A = 0 :=
        hnative.symm.trans h
      rw [hu]
      exact dimH_le_of_hausdorffMeasure_ne_top (d := u) (by rw [hz]; simp)
    · intro h
      have ht : MeasureTheory.Measure.hausdorffMeasure (u : ℝ) A = ⊤ :=
        hnative.symm.trans h
      rw [hu]
      exact le_dimH_of_hausdorffMeasure_eq_top (d := u) ht

theorem T003 (n : ℕ) (E : Set (V n)) (h_T001 : ScaleLaws) (h_T002 : CriticalLaws) :
    InvarianceLaws := by
  constructor
  · intro X _ A B hAB
    exact dimH_mono hAB
  · intro X Y _ _ A f hf
    constructor
    · have hval : dimH ((Subtype.val : A → X) '' (Set.univ : Set A)) = dimH (Set.univ : Set A) :=
        isometry_subtype_coe.dimH_image _
      have himage : dimH (f '' (Set.univ : Set A)) = dimH (Set.univ : Set A) :=
        hf.dimH_image _
      simpa only [Set.image_univ, Subtype.range_coe] using himage.trans hval.symm
    · intro s hs
      borelize X Y
      rw [h_T001.native_eq _ s hs, h_T001.native_eq _ s hs]
      have hfmeasure := hf.hausdorffMeasure_image (Or.inl hs.le) (Set.univ : Set A)
      have hvalmeasure := (isometry_subtype_coe (s := A)).hausdorffMeasure_image
        (Or.inl hs.le) (Set.univ : Set A)
      simpa only [Set.image_univ, Subtype.range_coe] using hfmeasure.trans hvalmeasure.symm

theorem T004 (n : ℕ) (E : Set (V n)) (h_T001 : ScaleLaws) (h_T002 : CriticalLaws) (h_T003 : InvarianceLaws) :
    ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws := by
  refine ⟨h_T001, h_T002, h_T003, ?_⟩
  have hpow : ∀ i k : ℕ, (2 : ℝ) ^ (-(i : ℝ) - (k : ℝ)) = ((1 : ℝ) / 2) ^ i / 2 ^ k := by
    intro i k
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, Real.rpow_natCast]
    simp [one_div]
  have hseries : ∀ k : ℕ, (∑' i : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ) - (k : ℝ)))) = ENNReal.ofReal (2 / (2 : ℝ) ^ k) := by
    intro k
    have hs : HasSum (fun i : ℕ => (2 : ℝ) ^ (-(i : ℝ) - (k : ℝ))) (2 / (2 : ℝ) ^ k) := by
      simpa only [hpow] using (hasSum_geometric_two.div_const ((2 : ℝ) ^ k))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => Real.rpow_nonneg (by norm_num) _) hs.summable, hs.tsum_eq]
  have hhalf : ENNReal.ofReal (2 / (2 : ℝ) ^ (2 : ℕ)) = (1 / 2 : ℝ≥0∞) := by
    norm_num
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  constructor
  · intro a ha
    simpa only [Real.zero_rpow (ne_of_gt ha)] using (Real.continuousAt_rpow_const 0 a (Or.inr (le_of_lt ha))).continuousWithinAt.tendsto
  · intro b hb
    exact tendsto_rpow_neg_nhdsGT_zero hb
  · simpa using hseries 1
  · simpa only [Nat.cast_ofNat] using (hseries 2).trans hhalf

theorem T005 (n : ℕ) (E : Set (V n)) (h_H003 : IsCompact E) :
    (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ Bornology.IsBounded E ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) := by
  classical
  have hR : ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ‖x‖ ≤ R := by
    obtain ⟨t, ht⟩ := h_H003.elim_finite_subcover (fun m : ℕ => Metric.ball (0 : V n) ((m : ℝ) + 1)) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
      refine Set.mem_iUnion.mpr ⟨m, ?_⟩
      simp only [Metric.mem_ball, dist_zero_right]
      linarith)
    refine ⟨((t.sup id : ℕ) : ℝ) + 1, ?_, ?_⟩
    · have h : (0 : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · intro x hx
      obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.mp (ht hx)
      have hm' : m ≤ t.sup id := Finset.le_sup (f := id) hm
      have hm'' : (m : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := by exact_mod_cast hm'
      have hx' : ‖x‖ < (m : ℝ) + 1 := by simpa using hxm
      linarith
  obtain ⟨R, hRone, hRbound⟩ := hR
  refine ⟨⟨R, hRone, ?_⟩, isBounded_iff_forall_norm_le.mpr ⟨R, hRbound⟩, ?_⟩
  · intro x hx j
    have hj : ‖x j‖ ≤ ‖x‖ := PiLp.norm_apply_le x j
    have hj' : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using hj
    exact hj'.trans (hRbound x hx)
  · intro s δ hs hδ
    obtain ⟨t, ht⟩ := h_H003.elim_finite_subcover (fun x : E => Metric.ball (x : V n) (δ / 2)) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith)⟩)
    let m := Fintype.card t
    let e : t ≃ Fin m := Fintype.equivFin t
    let U : ℕ → Set (V n) := fun i => if h : i < m then Metric.ball (((e.symm ⟨i, h⟩ : t) : E) : V n) (δ / 2) else ∅
    have hU : scaleCover δ E U := by
      constructor
      · intro x hx
        obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (ht hx)
        let k : t := ⟨c, hc⟩
        refine Set.mem_iUnion.mpr ⟨(e k).val, ?_⟩
        simpa [U, (e k).isLt] using hxc
      · intro i
        dsimp [U]
        split_ifs with hi
        · apply Metric.ediam_le_of_forall_dist_le
          intro x hx y hy
          have hx' := Metric.mem_ball.mp hx
          have hy' := Metric.mem_ball.mp hy
          have htri := dist_triangle x (((e.symm ⟨i, hi⟩ : t) : E) : V n) y
          rw [dist_comm (((e.symm ⟨i, hi⟩ : t) : E) : V n) y] at htri
          linarith
        · simp
    have hfin : cost s U < ⊤ := by
      unfold cost
      rw [tsum_eq_sum (s := Finset.range m) (fun i hi => by
        have hi' : ¬ i < m := by simpa using hi
        simp [U, hi', ENNReal.zero_rpow_of_pos hs])]
      apply ENNReal.sum_lt_top.mpr
      intro i hi
      apply ENNReal.rpow_lt_top_of_nonneg hs.le
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i)
    exact lt_of_le_of_lt (iInf_le_of_le U (iInf_le_of_le hU le_rfl)) hfin

theorem T006 (n : ℕ) (E : Set (V n)) (h_H002 : E.Nonempty) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) (h_T005 : (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ Bornology.IsBounded E ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤)) :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) := by
  classical
  have hnzero : n = 0 → E = Set.univ ∧ dimH E = 0 := by
    intro hn
    subst n
    have hE : E = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy⟩ := h_H002
      simpa only [Subsingleton.elim x y] using hy
    refine ⟨hE, ?_⟩
    have hzero : ∀ s : ℝ, 0 < s → haus s E = 0 := by
      intro s hs
      apply le_antisymm _ bot_le
      unfold haus
      refine iSup_le fun δ => iSup_le fun hδ => ?_
      have hc : scaleCover δ E (fun _ : ℕ => ({h_H002.some} : Set (V 0))) := by
        constructor
        · intro x hx
          exact Set.mem_iUnion.2 ⟨0, Set.mem_singleton_iff.2 (Subsingleton.elim _ _)⟩
        · intro i
          simp
      calc
        content s δ E ≤ cost s (fun _ : ℕ => ({h_H002.some} : Set (V 0))) := iInf_le_of_le _ (iInf_le _ hc)
        _ = 0 := by simp [cost, ENNReal.zero_rpow_of_pos hs]
    apply le_antisymm _ bot_le
    by_contra h
    obtain ⟨s, hs0, hs, hsd⟩ := ENNReal.lt_iff_exists_real_btwn.1 (lt_of_not_ge h)
    have hsp : 0 < s := ENNReal.ofReal_pos.1 hs
    have hd := (h_T004.2.1.critical E s hsp).2.2.1 (hzero s hsp)
    exact (not_lt_of_ge hd) hsd
  refine ⟨⟨h_T004.2.1.nonneg E, ?_⟩, hnzero⟩
  by_cases hn : n = 0
  · simp [hn, (hnzero hn).2]
  obtain ⟨R₀, hR₀, hbox⟩ := h_T005.1
  let R : ℝ := R₀ + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hbox' : ∀ x ∈ E, ∀ j : Fin n, |x j| < R := by
    intro x hx j
    have := hbox x hx j
    dsimp [R]
    linarith
  let m : ℝ → ℕ := fun h => ⌈2*R/h⌉₊
  let w : ℝ → ℝ := fun h => 2*R/(m h : ℝ)
  let t : ∀ h : ℝ, (Fin n → Fin (m h)) → Set (V n) := fun h f =>
    {x | ∀ j, x j ∈ Set.Icc (-R + (f j : ℕ)*w h) (-R + ((f j : ℕ)+1)*w h)}
  have grid : ∀ h : ℝ, 0 < h → E ⊆ ⋃ f, t h f ∧ ∀ f, Metric.ediam (t h f) ≤ ENNReal.ofReal (Real.sqrt n * h) := by
    intro h hh
    have hm : 0 < (m h : ℝ) := Nat.cast_pos.2 (Nat.ceil_pos.2 (by positivity))
    have hw : 0 < w h := div_pos (by positivity) hm
    have hwm : w h * (m h : ℝ) = 2*R := div_mul_cancel₀ _ hm.ne'
    have hwh : w h ≤ h := by
      apply (div_le_iff₀ hm).2
      have hc := (div_le_iff₀ hh).1 (Nat.le_ceil (2*R/h))
      nlinarith
    constructor
    · intro x hx
      let f : Fin n → Fin (m h) := fun j => ⟨⌊(x j + R)/w h⌋₊, by
        apply (Nat.floor_lt (div_nonneg (by linarith [(abs_lt.1 (hbox' x hx j)).1]) hw.le)).2
        apply (div_lt_iff₀ hw).2
        nlinarith [(abs_lt.1 (hbox' x hx j)).2]⟩
      refine Set.mem_iUnion.2 ⟨f, ?_⟩
      intro j
      have hnon : 0 ≤ (x j + R)/w h := div_nonneg (by linarith [(abs_lt.1 (hbox' x hx j)).1]) hw.le
      have hlo := Nat.floor_le hnon
      have hhi := Nat.lt_floor_add_one ((x j + R)/w h)
      dsimp [t, f]
      constructor
      · have := (le_div_iff₀ hw).1 hlo
        linarith
      · have := (div_lt_iff₀ hw).1 hhi
        linarith
    · intro f
      apply Metric.ediam_le_of_forall_dist_le
      intro x hx y hy
      rw [EuclideanSpace.dist_eq]
      calc
        Real.sqrt (∑ j, dist (x j) (y j) ^ 2) ≤ Real.sqrt (∑ _j : Fin n, h^2) := by
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro j _
          have hxy : dist (x j) (y j) ≤ h := by
            rw [Real.dist_eq, abs_le]
            have hxj := hx j
            have hyj := hy j
            constructor <;> nlinarith [hxj.1, hxj.2, hyj.1, hyj.2]
          exact pow_le_pow_left₀ dist_nonneg hxy 2
        _ = Real.sqrt n * h := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hh.le]
  have hzero : ∀ a : ℝ, (n:ℝ) < a → haus a E = 0 := by
    intro a hna
    have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) hna
    let C : ℝ := (2*R+1)^n * (Real.sqrt n)^a
    have hcost : ∀ h : ℝ, 0 < h → h ≤ 1 → (∑ f, Metric.ediam (t h f)^a) ≤ ENNReal.ofReal (C*h^(a-(n:ℝ))) := by
      intro h hh hh1
      have hm : (m h : ℝ) ≤ (2*R+1)/h := by
        have hc := Nat.ceil_lt_add_one (show 0 ≤ 2*R/h by positivity)
        have hle : 2*R/h + 1 ≤ (2*R+1)/h := by
          apply (le_div_iff₀ hh).2
          field_simp
          nlinarith
        exact hc.le.trans hle
      have hreal : (m h : ℝ)^n * (Real.sqrt n*h)^a ≤ C*h^(a-(n:ℝ)) := by
        calc
          (m h : ℝ)^n * (Real.sqrt n*h)^a ≤ ((2*R+1)/h)^n * (Real.sqrt n*h)^a :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hm n) (Real.rpow_nonneg (by positivity) _)
          _ = C*h^(a-(n:ℝ)) := by
            dsimp [C]
            rw [div_pow, Real.mul_rpow (Real.sqrt_nonneg _) hh.le, Real.rpow_sub hh, Real.rpow_natCast]
            ring
      calc
        (∑ f, Metric.ediam (t h f)^a) ≤ ∑ _f : Fin n → Fin (m h), (ENNReal.ofReal (Real.sqrt n*h))^a := by
          exact Finset.sum_le_sum fun f _ => ENNReal.rpow_le_rpow ((grid h hh).2 f) ha.le
        _ = ENNReal.ofReal ((m h : ℝ)^n * (Real.sqrt n*h)^a) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) ha.le]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (by positivity)]
          simp
        _ ≤ ENNReal.ofReal (C*h^(a-(n:ℝ))) := ENNReal.ofReal_le_ofReal hreal
    let l := nhdsWithin (0:ℝ) (Set.Ioi 0)
    have hid : Filter.Tendsto (fun h : ℝ => h) l (nhds 0) :=
      (Filter.tendsto_id : Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0)).mono_left nhdsWithin_le_nhds
    have hdiamlim : Filter.Tendsto (fun h : ℝ => ENNReal.ofReal (Real.sqrt n*h)) l (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal (hid.const_mul (Real.sqrt n))
    have hbound : ∀ᶠ h in l, ∀ f, Metric.ediam (t h f) ≤ ENNReal.ofReal (Real.sqrt n*h) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact (grid h hh).2
    have hcover : ∀ᶠ h in l, E ⊆ ⋃ f, t h f := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact (grid h hh).1
    have hp := h_T004.2.2.2.positive_limit (a-(n:ℝ)) (sub_pos.2 hna)
    have ht : Filter.Tendsto (fun h : ℝ => C*h^(a-(n:ℝ))) l (nhds 0) := by
      simpa using hp.const_mul C
    have ht' : Filter.Tendsto (fun h : ℝ => ENNReal.ofReal (C*h^(a-(n:ℝ)))) l (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal ht
    have h1 : ∀ᶠ h : ℝ in l, h < 1 := nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))
    have hlim : Filter.liminf (fun h => ∑ f, Metric.ediam (t h f)^a) l ≤ 0 := by
      rw [← ht'.liminf_eq]
      apply Filter.liminf_le_liminf
      · filter_upwards [self_mem_nhdsWithin, h1] with h hh hh1
        exact hcost h hh hh1.le
      · isBoundedDefault
      · isBoundedDefault
    rw [h_T004.1.native_eq E a ha]
    apply le_antisymm _ bot_le
    exact (MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum a E (fun h => ENNReal.ofReal (Real.sqrt n*h)) hdiamlim t hbound hcover).trans hlim
  by_contra h
  obtain ⟨a, ha0, hna, had⟩ := ENNReal.lt_iff_exists_real_btwn.1 (lt_of_not_ge h)
  have hna' : (n:ℝ) < a := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg n)).1 (by simpa using hna)
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) hna'
  have hd := (h_T004.2.1.critical E a ha).2.2.1 (hzero a hna')
  exact (not_lt_of_ge hd) had

theorem T007 (n : ℕ) (E : Set (V n))  :
    Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2) := by
  have h₁ : ∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t := by
    intro x t
    constructor
    · ext i
      simp [base, join]
    · simp [height, join]
  have h₂ : ∀ z : V (n+1), join (base z) (height z) = z := by
    intro z
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [join, height]
    · simp [join, base]
  refine ⟨⟨?_, ?_⟩, h₁, h₂, ?_⟩
  · intro p q h
    apply Prod.ext
    · have hb := congrArg base h
      simpa only [(h₁ p.1 p.2).1, (h₁ q.1 q.2).1] using hb
    · have ht := congrArg height h
      simpa only [(h₁ p.1 p.2).2, (h₁ q.1 q.2).2] using ht
  · intro z
    exact ⟨(base z, height z), h₂ z⟩
  · intro x y t u
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
    simp [join]

theorem T008 (n : ℕ) (E : Set (V n)) (h_T005 : (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ Bornology.IsBounded E ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2) := by
  have hfinite : dimH E ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h_T006.1.2 (ENNReal.natCast_lt_top n))
  exact ⟨h_T006.1, hfinite, h_T005.2.1, h_T005.1, h_T005.2.2, h_T006.2, h_T007⟩

theorem T011 (n : ℕ) (E : Set (V n)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    n = 0 → dimH (cylinder E) ≤ dimH E + 1 := by
  classical
  intro hn
  subst n
  rcases h_T008 with ⟨_, _, _, _, _, hzero, _, _, hinv, hd⟩
  rcases hzero rfl with ⟨hE, hD⟩
  rcases h_T004 with ⟨hs, hc, hi, hp⟩
  let f : ℝ → V 1 := fun t => join (0 : V 0) t
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simpa [f] using hd (0 : V 0) 0 t u
  have hfinv : ∀ z : V 1, f (height z) = z := by
    intro z
    have hb : base z = (0 : V 0) := Subsingleton.elim _ _
    simpa [f, hb] using hinv z
  have partition : ∀ (h : ℝ), 0 ≤ h → ∀ m : ℕ, ∀ t ∈ Set.Icc 0 (((m : ℝ)+1)*h), ∃ i : ℕ, i < m+1 ∧ t ∈ Set.Icc ((i : ℝ)*h) (((i : ℝ)+1)*h) := by
    intro h hh m
    induction m with
    | zero =>
      intro t ht
      exact ⟨0, by omega, by simpa using ht⟩
    | succ m ih =>
      intro t ht
      by_cases hm : t ≤ ((m : ℝ)+1)*h
      · obtain ⟨i, hi, hit⟩ := ih t ⟨ht.1, hm⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, hit⟩
      · exact ⟨m+1, Nat.lt_succ_self _, by simpa using (le_of_lt (lt_of_not_ge hm)), by simpa [Nat.cast_add, Nat.cast_one] using ht.2⟩
  have hcosteq : ∀ (m : ℕ) (a : ℝ), 1 < a → ((m+1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (1 / ((m : ℝ)+1))) ^ a = ENNReal.ofReal ((1 / ((m : ℝ)+1)) ^ (a-1)) := by
    intro m a ha
    have hm : 0 < (m : ℝ)+1 := by positivity
    have hh : 0 < 1 / ((m : ℝ)+1) := by positivity
    have heq : ((m : ℝ)+1) * (1 / ((m : ℝ)+1)) ^ a = (1 / ((m : ℝ)+1)) ^ (a-1) := by
      rw [Real.rpow_sub hh, Real.rpow_one]
      field_simp
    rw [ENNReal.ofReal_rpow_of_nonneg hh.le (by linarith : 0 ≤ a)]
    have hc' : ((m+1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ)+1) := by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg m) (by norm_num)]
      simp
    rw [hc', ← ENNReal.ofReal_mul hm.le, heq]
  have bound : ∀ (a δ : ℝ), 1 < a → ∀ m : ℕ, 1 / ((m : ℝ)+1) ≤ δ → content a δ (cylinder E) ≤ ENNReal.ofReal ((1 / ((m : ℝ)+1)) ^ (a-1)) := by
    intro a δ ha m hmδ
    have ha0 : 0 < a := by linarith
    let h : ℝ := 1 / ((m : ℝ)+1)
    have hm : 0 < (m : ℝ)+1 := by positivity
    have hh : 0 < h := by dsimp [h]; positivity
    let U : ℕ → Set (V 1) := fun i => if i < m+1 then f '' Set.Icc ((i : ℝ)*h) (((i : ℝ)+1)*h) else ∅
    have hdi : ∀ i, Metric.ediam (U i) = if i < m+1 then ENNReal.ofReal h else 0 := by
      intro i
      dsimp [U]
      split_ifs with hi'
      · rw [hf.ediam_image, Real.ediam_Icc]
        congr 1
        ring
      · simp
    have hcov : scaleCover δ (cylinder E) U := by
      constructor
      · intro z hz
        have ht : height z ∈ Set.Icc 0 (((m : ℝ)+1)*h) := by
          simpa [h, hm.ne', unitI] using hz.2
        obtain ⟨i, hi', hit⟩ := partition h hh.le m (height z) ht
        apply Set.mem_iUnion.mpr
        refine ⟨i, ?_⟩
        dsimp [U]
        rw [if_pos hi']
        exact ⟨height z, hit, hfinv z⟩
      · intro i
        rw [hdi]
        split_ifs
        · exact ENNReal.ofReal_le_ofReal hmδ
        · exact zero_le
    have hcost : cost a U = ((m+1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal h)^a := by
      rw [cost, tsum_eq_sum (s := Finset.range (m+1)) (fun i hi' => by
        rw [hdi, if_neg (by simpa using hi'), ENNReal.zero_rpow_of_pos ha0])]
      calc
        (∑ i ∈ Finset.range (m+1), (Metric.ediam (U i)) ^ a) = ∑ i ∈ Finset.range (m+1), (ENNReal.ofReal h)^a := by
          apply Finset.sum_congr rfl
          intro i hi'
          rw [hdi, if_pos (Finset.mem_range.mp hi')]
        _ = _ := by simp [nsmul_eq_mul]
    calc
      content a δ (cylinder E) ≤ cost a U := iInf₂_le U hcov
      _ = ((m+1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal h)^a := hcost
      _ = ENNReal.ofReal ((1 / ((m : ℝ)+1)) ^ (a-1)) := hcosteq m a ha
  have hz : ∀ a : ℝ, 1 < a → haus a (cylinder E) = 0 := by
    intro a ha
    have hcont : ∀ δ : ℝ, 0 < δ → content a δ (cylinder E) = 0 := by
      intro δ hδ
      have hl : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ)+1)) Filter.atTop (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hlw : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ)+1)) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hl, Filter.Eventually.of_forall (fun m => by simp only [Set.mem_Ioi]; positivity)⟩
      have hpow := (hp.positive_limit (a-1) (by linarith)).comp hlw
      have he : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / ((m : ℝ)+1)) ^ (a-1))) Filter.atTop (nhds (0 : ℝ≥0∞)) := by
        simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hpow
      apply le_antisymm _ zero_le
      apply ge_of_tendsto he
      filter_upwards [hl.eventually (gt_mem_nhds hδ)] with m hm'
      exact bound a δ ha m hm'.le
    rw [hs.supremum]
    exact le_antisymm (iSup₂_le (fun δ hδ => (hcont δ hδ).le)) zero_le
  simp only [hD, zero_add]
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨a, ha0, h1a, har⟩ := ENNReal.lt_iff_exists_real_btwn.mp hr
  have ha : 1 < a := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa using h1a
  exact ((hc.critical (cylinder E) a (by linarith)).2.2.1 (hz a ha)).trans har.le

theorem T009 (n : ℕ) (E : Set (V n)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (V n), scaleCover r E W ∧ cost q W < ENNReal.ofReal (ε/2) := by
  intro hn q r ε hD hr hr1 hε
  have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt h_T008.1.1 hD)
  have hhaus : haus q E = 0 := (h_T004.2.1.critical E q hq).2.1 hD
  have hcontent_le : content q r E ≤ haus q E := by
    unfold haus
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hcontent : content q r E = 0 := le_antisymm (hhaus ▸ hcontent_le) zero_le
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  by_contra hW
  have hlow : ENNReal.ofReal (ε / 2) ≤ content q r E := by
    unfold content
    refine le_iInf fun W => le_iInf fun hcov => ?_
    exact le_of_not_gt (fun hc => hW ⟨W, hcov, hc⟩)
  exact (not_le_of_gt hpos) (hcontent ▸ hlow)

theorem T010 (n : ℕ) (E : Set (V n)) (h_T009 : 1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (V n), scaleCover r E W ∧ cost q W < ENNReal.ofReal (ε/2)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) :
    1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ K : Set ℕ, ∃ U : K → Set (V n), E ⊆ (⋃ i, U i) ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ cost q U < ENNReal.ofReal ε := by
  classical
  intro hn q r ε hdim hr hr1 hε
  have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hdim)
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have ball_replace : ∀ (a : ℝ), 0 < a → ∀ c : V n, ∃ B : Set (V n), c ∈ B ∧ B.Nonempty ∧ 0 < Metric.ediam B ∧ Metric.ediam B ≤ ENNReal.ofReal r ∧ (Metric.ediam B)^q ≤ ENNReal.ofReal a := by
    intro a ha c
    let d : ℝ := min (r / 2) (a ^ q⁻¹)
    have hd : 0 < d := lt_min (by positivity) (Real.rpow_pos_of_pos ha _)
    have hdiam : Metric.diam (Metric.closedBall c (d / 2)) = d := by
      rw [Metric.diam_closedBall_eq c (by positivity)]
      ring
    have hediam : Metric.ediam (Metric.closedBall c (d / 2)) = ENNReal.ofReal d := by
      calc
        _ = ENNReal.ofReal (Metric.diam (Metric.closedBall c (d/2))) := (ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top).symm
        _ = ENNReal.ofReal d := congrArg ENNReal.ofReal hdiam
    have hpow : d ^ q ≤ a := by
      calc
        d ^ q ≤ (a ^ q⁻¹) ^ q := Real.rpow_le_rpow hd.le (min_le_right _ _) hq.le
        _ = a := Real.rpow_inv_rpow ha.le hq.ne'
    refine ⟨Metric.closedBall c (d/2), Metric.mem_closedBall_self (by positivity), ⟨c, Metric.mem_closedBall_self (by positivity)⟩, ?_, ?_, ?_⟩
    · rw [hediam]; exact ENNReal.ofReal_pos.mpr hd
    · rw [hediam]; exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (by linarith))
    · rw [hediam, ENNReal.ofReal_rpow_of_nonneg hd.le hq.le]
      exact ENNReal.ofReal_le_ofReal hpow
  obtain ⟨W, hW, hcost⟩ := h_T009 hn q r ε hdim hr hr1 hε
  let K : Set ℕ := {i | (W i).Nonempty}
  let b : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (ε * (2:ℝ)^(-(i:ℝ)-2))
  have replacement : ∀ i : K, ∃ B : Set (V n), W i ⊆ B ∧ B.Nonempty ∧ 0 < Metric.ediam B ∧ Metric.ediam B ≤ ENNReal.ofReal r ∧ (Metric.ediam B)^q ≤ (Metric.ediam (W i))^q + b i := by
    intro i
    by_cases hz : Metric.ediam (W i) = 0
    · obtain ⟨c, hc⟩ := i.property
      have ha : 0 < ε * (2:ℝ)^(-(i.val:ℝ)-3) := mul_pos hε (Real.rpow_pos_of_pos (by norm_num) _)
      obtain ⟨B, hcB, hB, hp, hBr, hBcost⟩ := ball_replace _ ha c
      refine ⟨B, ?_, hB, hp, hBr, ?_⟩
      · intro x hx
        have : x = c := (Metric.ediam_eq_zero_iff.mp hz) hx hc
        simpa [this] using hcB
      · calc
          _ ≤ ENNReal.ofReal (ε * (2:ℝ)^(-(i.val:ℝ)-3)) := hBcost
          _ ≤ b i := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) hε.le)
          _ ≤ _ := le_add_left le_rfl
    · exact ⟨W i, Subset.rfl, i.property, lt_of_le_of_ne bot_le (Ne.symm hz), hW.2 i, le_add_right le_rfl⟩
  choose U hU using replacement
  refine ⟨K, U, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, (hU ⟨i, ⟨x, hi⟩⟩).1 hi⟩
  · intro i
    exact ⟨(hU i).2.1, (hU i).2.2.1, (hU i).2.2.2.1⟩
  · have hsum : (∑' i : ℕ, b i) = ENNReal.ofReal (ε/2) := by
      simp only [b, ENNReal.ofReal_mul hε.le]
      rw [ENNReal.tsum_mul_left, h_T004.2.2.2.series_half]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      simp [div_eq_mul_inv]
    calc
      cost q U ≤ ∑' i : K, ((Metric.ediam (W i))^q + b i) := ENNReal.tsum_le_tsum (fun i => (hU i).2.2.2.2)
      _ ≤ ∑' i : ℕ, ((Metric.ediam (W i))^q + b i) := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = cost q W + ENNReal.ofReal (ε/2) := by rw [ENNReal.tsum_add, hsum]; rfl
      _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hcost
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem T012 (n : ℕ) (E : Set (V n)) (h_T010 : 1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ K : Set ℕ, ∃ U : K → Set (V n), E ⊆ (⋃ i, U i) ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ cost q U < ENNReal.ofReal ε) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    1 ≤ n → ∀ q δ ε : ℝ, dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε → ∃ W : ℕ → Set (V (n+1)), scaleCover δ (cylinder E) W ∧ cost (q+1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) := by
  classical
  intro hn q δ ε hq hδ hε
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hq0 : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hq)
  have hp : 0 < q+1 := by linarith
  let r : ℝ := min 1 (δ / Real.sqrt 2)
  have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hs)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : Real.sqrt 2 * r ≤ δ := by
    have h := min_le_right (1 : ℝ) (δ / Real.sqrt 2)
    have h' : min 1 (δ / Real.sqrt 2) * Real.sqrt 2 ≤ δ := (le_div_iff₀ hs).mp h
    simpa only [mul_comm] using h'
  obtain ⟨K, U, hcov, hU, hcost⟩ := h_T010 hn q r ε hq hr hr1 hε
  rcases h_T008 with ⟨_, _, _, _, _, _, _, _, hinv, hsq⟩
  let d : K → ℝ := fun i => Metric.diam (U i)
  have hfinite (i : K) : Metric.ediam (U i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU i).2.2
  have hd (i : K) : 0 < d i ∧ d i ≤ r ∧ ENNReal.ofReal (d i) = Metric.ediam (U i) := by
    exact ⟨ENNReal.toReal_pos_iff.mpr ⟨(hU i).2.1, lt_top_iff_ne_top.mpr (hfinite i)⟩,
      ENNReal.toReal_le_of_le_ofReal hr.le (hU i).2.2, ENNReal.ofReal_toReal (hfinite i)⟩
  let N : K → ℕ := fun i => ⌈1 / d i⌉₊
  have hnum (i : K) : 0 < N i ∧ 1 / (N i : ℝ) ≤ d i ∧ (N i : ℝ) * (Real.sqrt 2 * d i) ^ (q+1) ≤ (2 * (Real.sqrt 2) ^ (q+1)) * (d i) ^ q := by
    have hd0 := (hd i).1
    have hd1 := (hd i).2.1.trans hr1
    have hN : 0 < N i := Nat.one_le_ceil_iff.mpr (by positivity)
    have hNr : (0 : ℝ) < N i := by exact_mod_cast hN
    have hlo : 1 / d i ≤ (N i : ℝ) := Nat.le_ceil _
    have hNd : 1 ≤ (N i : ℝ) * d i := (div_le_iff₀ hd0).mp hlo
    have hhi := Nat.ceil_lt_add_one (show 0 ≤ 1/d i by positivity)
    have hNd2 : (N i : ℝ) * d i ≤ 2 := by
      have h := (mul_lt_mul_of_pos_right hhi hd0).le
      have he : (1/d i+1)*d i = 1+d i := by field_simp
      rw [he] at h
      linarith
    refine ⟨hN, (div_le_iff₀ hNr).mpr (by nlinarith), ?_⟩
    rw [Real.mul_rpow hs.le hd0.le, Real.rpow_add_one hd0.ne']
    have h := mul_le_mul_of_nonneg_right hNd2 (show 0 ≤ (Real.sqrt 2) ^ (q+1) * (d i) ^ q by positivity)
    nlinarith only [h]
  have hinterval : ∀ (M : ℕ), 0 < M → ∀ t ∈ unitI, ∃ j : Fin M, t ∈ Set.Icc ((j : ℕ) / (M : ℝ)) (((j : ℕ) + 1 : ℝ) / M) := by
    intro M hM t ht
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    rcases ht with ⟨ht0, ht1⟩
    by_cases he : t = 1
    · refine ⟨⟨M-1, by omega⟩, ?_, ?_⟩
      · rw [he, div_le_iff₀ hMr]
        norm_cast
        omega
      · rw [he, le_div_iff₀ hMr]
        have h : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast (Nat.sub_add_cancel hM)
        simpa only [Fin.val_mk, one_mul] using h.ge
    · have htlt : t < 1 := lt_of_le_of_ne ht1 he
      have hf : ⌊t * (M : ℝ)⌋₊ < M := (Nat.floor_lt (by positivity)).2 (by nlinarith)
      refine ⟨⟨⌊t * (M : ℝ)⌋₊, hf⟩, ?_, ?_⟩
      · rw [div_le_iff₀ hMr]
        exact Nat.floor_le (by positivity)
      · rw [le_div_iff₀ hMr]
        exact (Nat.lt_floor_add_one (t * (M : ℝ))).le
  let J := Σ i : K, Fin (N i)
  let P : J → Set (V (n+1)) := fun b => {z | base z ∈ U b.1 ∧ height z ∈ Set.Icc ((b.2 : ℕ) / (N b.1 : ℝ)) (((b.2 : ℕ)+1 : ℝ) / N b.1)}
  have hPcov : cylinder E ⊆ ⋃ b, P b := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hz.1)
    obtain ⟨j, hj⟩ := hinterval (N i) (hnum i).1 (height z) hz.2
    exact Set.mem_iUnion.mpr ⟨⟨i,j⟩, hi, hj⟩
  have hPdiam (b : J) : Metric.ediam (P b) ≤ ENNReal.ofReal (Real.sqrt 2 * d b.1) := by
    apply Metric.ediam_le_of_forall_dist_le
    intro z hz w hw
    have hbase : dist (base z) (base w) ≤ d b.1 := Metric.dist_le_diam_of_mem' (hfinite b.1) hz.1 hw.1
    have ht : dist (height z) (height w) ≤ 1/(N b.1 : ℝ) := by
      rw [Real.dist_eq, abs_le]
      have hzlo := hz.2.1
      have hzhi := hz.2.2
      have hwlo := hw.2.1
      have hwhi := hw.2.2
      rw [add_div] at hzhi hwhi
      constructor <;> linarith
    have ht' := ht.trans (hnum b.1).2.1
    have hsq' : dist z w ^ 2 = dist (base z) (base w) ^ 2 + dist (height z) (height w) ^ 2 := by
      simpa only [hinv] using hsq (base z) (base w) (height z) (height w)
    have hb2 := mul_self_le_mul_self dist_nonneg hbase
    have ht2 := mul_self_le_mul_self dist_nonneg ht'
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hnonneg : 0 ≤ Real.sqrt 2 * d b.1 := mul_nonneg hs.le (hd b.1).1.le
    nlinarith [dist_nonneg (x := z) (y := w)]
  have hPscale (b : J) : Metric.ediam (P b) ≤ ENNReal.ofReal δ := by
    refine (hPdiam b).trans (ENNReal.ofReal_le_ofReal ?_)
    exact (mul_le_mul_of_nonneg_left (hd b.1).2.1 hs.le).trans hrδ
  let C : ℝ := 2 * (Real.sqrt 2) ^ (q+1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hfiber (i : K) : (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * d i)) ^ (q+1) ≤ ENNReal.ofReal C * (Metric.ediam (U i)) ^ q := by
    have hconv1 : ENNReal.ofReal ((Real.sqrt 2*d i)^(q+1)) = (ENNReal.ofReal (Real.sqrt 2*d i))^(q+1) := (ENNReal.ofReal_rpow_of_pos (mul_pos hs (hd i).1)).symm
    have hconv2 : ENNReal.ofReal ((d i)^q) = (ENNReal.ofReal (d i))^q := (ENNReal.ofReal_rpow_of_pos (hd i).1).symm
    have hNi : ENNReal.ofReal (N i : ℝ) = (N i : ℝ≥0∞) := by simp
    have h' := ENNReal.ofReal_le_ofReal (hnum i).2.2
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC.le, hNi, hconv1, hconv2, (hd i).2.2] at h'
    exact h'
  have hPcost : cost (q+1) P ≤ ENNReal.ofReal C * cost q U := by
    calc
      cost (q+1) P ≤ ∑' b : J, (ENNReal.ofReal (Real.sqrt 2 * d b.1)) ^ (q+1) := ENNReal.tsum_le_tsum (fun b => ENNReal.rpow_le_rpow (hPdiam b) hp.le)
      _ = ∑' i : K, (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * d i)) ^ (q+1) := by
        rw [ENNReal.tsum_sigma']
        congr 1
        funext i
        simp
      _ ≤ ∑' i : K, ENNReal.ofReal C * (Metric.ediam (U i)) ^ q := ENNReal.tsum_le_tsum hfiber
      _ = ENNReal.ofReal C * cost q U := ENNReal.tsum_mul_left
  letI : Encodable J := Encodable.ofCountable J
  let W : ℕ → Set (V (n+1)) := fun k => ⋃ b ∈ Encodable.decode₂ J k, P b
  have hWcover : scaleCover δ (cylinder E) W := by
    constructor
    · simpa only [W, Encodable.iUnion_decode₂] using hPcov
    · intro k
      dsimp only [W]
      exact Encodable.iUnion_decode₂_cases (C := fun S : Set (V (n+1)) => Metric.ediam S ≤ ENNReal.ofReal δ) (by simp) hPscale
  have hWcost : cost (q+1) W = cost (q+1) P := tsum_iUnion_decode₂ (fun S : Set (V (n+1)) => Metric.ediam S ^ (q+1)) (by simp [ENNReal.zero_rpow_of_pos hp]) P
  refine ⟨W, hWcover, ?_⟩
  rw [hWcost]
  have hstrict : ENNReal.ofReal C * cost q U < ENNReal.ofReal C * ENNReal.ofReal ε := ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top hcost
  have heq : ENNReal.ofReal C * ENNReal.ofReal ε = ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) := (ENNReal.ofReal_mul hC.le).symm
  exact hPcost.trans_lt (hstrict.trans_eq heq)

theorem T013 (n : ℕ) (E : Set (V n)) (h_T011 : n = 0 → dimH (cylinder E) ≤ dimH E + 1) (h_T012 : 1 ≤ n → ∀ q δ ε : ℝ, dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε → ∃ W : ℕ → Set (V (n+1)), scaleCover δ (cylinder E) W ∧ cost (q+1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    dimH (cylinder E) ≤ dimH E + 1 := by
  by_cases hn : n = 0
  · exact h_T011 hn
  have hn' : 1 ≤ n := by omega
  have hD : dimH E ≠ ⊤ := h_T008.2.1
  have hzero : ∀ (a : ℝ≥0∞) (C : ℝ), 0 < C → (∀ ε : ℝ, 0 < ε → a ≤ ENNReal.ofReal (C * ε)) → a = 0 := by
    intro a C hC h
    apply le_antisymm _ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfin
    have he : 0 < (ε : ℝ) := by exact_mod_cast hε
    have hb := h ((ε : ℝ) / C) (div_pos he hC)
    have hc : C * ((ε : ℝ) / C) = (ε : ℝ) := by field_simp
    simpa [hc] using hb
  have h : ∀ q : ℝ, (dimH E).toReal < q → dimH (cylinder E) ≤ ENNReal.ofReal (q+1) := by
    intro q hq
    have hqpos : 0 < q := lt_of_le_of_lt ENNReal.toReal_nonneg hq
    have hexp : 0 < q+1 := by linarith
    have hdim : dimH E < ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_toReal hD]
      exact (ENNReal.ofReal_lt_ofReal_iff hqpos).2 hq
    have hc : ∀ δ : ℝ, 0 < δ → content (q+1) δ (cylinder E) = 0 := by
      intro δ hδ
      apply hzero _ (2 * (Real.sqrt 2) ^ (q+1)) (by positivity)
      intro ε hε
      obtain ⟨W, hW, hcost⟩ := h_T012 hn' q δ ε hdim hδ hε
      have hle : content (q+1) δ (cylinder E) ≤ cost (q+1) W := by
        unfold content
        exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
      exact hle.trans hcost.le
    have hh : haus (q+1) (cylinder E) = 0 := by
      rw [h_T004.1.supremum]
      apply le_antisymm _ bot_le
      exact iSup_le fun δ => iSup_le fun hδ => (hc δ hδ).le
    exact (h_T004.2.1.critical (cylinder E) (q+1) hexp).2.2.1 hh
  have hb := h ((dimH E).toReal + 1) (by linarith)
  have hA : dimH (cylinder E) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hreal : (dimH (cylinder E)).toReal ≤ (dimH E).toReal + 1 := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    have hq : (dimH E).toReal < r - 1 := by linarith
    have hpos : 0 ≤ r := by have := ENNReal.toReal_nonneg (a := dimH E); linarith
    have hh : dimH (cylinder E) ≤ ENNReal.ofReal r := by simpa using h (r - 1) hq
    simpa [ENNReal.toReal_ofReal hpos] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  have hconvert : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hD]
    norm_num
  rw [← hconvert, ← ENNReal.ofReal_toReal hA]
  exact ENNReal.ofReal_le_ofReal hreal

theorem T014 (n : ℕ) (E : Set (V n))  :
    MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1 := by
  constructor
  · exact measurableSet_Icc
  · simp [unitI, Real.volume_Icc]

theorem T015 (n : ℕ) (E : Set (V n)) (h_T014 : MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1) :
    (MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1) ∧ (∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → Metric.ediam B ≤ ENNReal.ofReal ρ → 0 < η → Bornology.IsBounded B ∧ BddBelow B ∧ BddAbove B ∧ (∀ b ∈ B, sInf B ≤ b ∧ b ≤ sSup B) ∧ sSup B - sInf B ≤ ρ ∧ B ⊆ Set.Ioo (sInf B - η/2) (sSup B + η/2) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2)) ∧ 0 < sSup B - sInf B + η ∧ sSup B - sInf B + η ≤ ρ + η ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2)) : ℝ≥0∞) = ENNReal.ofReal (sSup B - sInf B + η) ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (ρ + η) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI)) := by
  refine ⟨h_T014, ?_⟩
  intro B ρ η hB hρ hdiam hη
  have habs : ∀ x ∈ B, ∀ y ∈ B, |x-y| ≤ ρ := by
    intro x hx y hy
    have he : edist x y ≤ ENNReal.ofReal ρ := (Metric.edist_le_ediam_of_mem hx hy).trans hdiam
    have hd : dist x y ≤ ρ := (ENNReal.ofReal_le_ofReal_iff hρ).mp (by simpa only [edist_dist] using he)
    simpa only [Real.dist_eq] using hd
  obtain ⟨b₀, hb₀⟩ := hB
  have hlo : BddBelow B := by
    refine ⟨b₀ - ρ, ?_⟩
    intro b hb
    have h := (abs_le.mp (habs b hb b₀ hb₀)).1
    linarith
  have hup : BddAbove B := by
    refine ⟨b₀ + ρ, ?_⟩
    intro b hb
    have h := (abs_le.mp (habs b hb b₀ hb₀)).2
    linarith
  have hbnd : Bornology.IsBounded B := isBounded_iff_bddBelow_bddAbove.mpr ⟨hlo, hup⟩
  have hbounds : ∀ b ∈ B, sInf B ≤ b ∧ b ≤ sSup B := fun b hb => ⟨csInf_le hlo hb, le_csSup hup hb⟩
  have hsup : ∀ b ∈ B, sSup B ≤ b + ρ := by
    intro b hb
    apply csSup_le ⟨b₀, hb₀⟩
    intro c hc
    have h := (abs_le.mp (habs c hc b hb)).2
    linarith
  have hinf : sSup B - ρ ≤ sInf B := by
    apply le_csInf ⟨b₀, hb₀⟩
    intro b hb
    have h := hsup b hb
    linarith
  have hlen : sSup B - sInf B ≤ ρ := by linarith
  have horder : sInf B ≤ sSup B := (hbounds b₀ hb₀).1.trans (hbounds b₀ hb₀).2
  have hsub : B ⊆ Ioo (sInf B - η/2) (sSup B + η/2) := by
    intro b hb
    obtain ⟨h₁, h₂⟩ := hbounds b hb
    constructor <;> linarith
  have hpos : 0 < sSup B - sInf B + η := by linarith
  have hle : sSup B - sInf B + η ≤ ρ + η := by linarith
  have hvol : (volume (Ioo (sInf B - η/2) (sSup B + η/2)) : ℝ≥0∞) = ENNReal.ofReal (sSup B - sInf B + η) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  refine ⟨hbnd, hlo, hup, hbounds, hlen, hsub, measurableSet_Ioo, hpos, hle, hvol, ?_, measurableSet_Ioo.inter h_T014.1⟩
  calc
    volume (Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI) ≤ volume (Ioo (sInf B - η/2) (sSup B + η/2)) := measure_mono inter_subset_left
    _ = ENNReal.ofReal (sSup B - sInf B + η) := hvol
    _ ≤ ENNReal.ofReal (ρ + η) := ENNReal.ofReal_le_ofReal hle

theorem T016 (n : ℕ) (E : Set (V n)) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    LipschitzWith 1 (base : V (n+1) → V n) ∧ LipschitzWith 1 (height : V (n+1) → ℝ) ∧ (∀ (δ : ℝ) (W : ℕ → Set (V (n+1))), 0 < δ → scaleCover δ (cylinder E) W → ∀ i, Metric.ediam (W i) = ENNReal.ofReal (Metric.diam (W i)) ∧ 0 ≤ Metric.diam (W i) ∧ Metric.diam (W i) ≤ δ ∧ Metric.ediam (base '' W i) ≤ Metric.ediam (W i) ∧ Metric.ediam (height '' W i) ≤ Metric.ediam (W i)) := by
  rcases h_T008 with ⟨_, _, _, _, _, _, _, _, hjoin, hdist⟩
  have hsplit (z w : V (n+1)) :
      dist z w ^ 2 = dist (base z) (base w) ^ 2 + dist (height z) (height w) ^ 2 := by
    simpa only [hjoin] using hdist (base z) (base w) (height z) (height w)
  have hb : LipschitzWith 1 (base : V (n+1) → V n) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    have hs := hsplit z w
    nlinarith [(dist_nonneg : 0 ≤ dist (base z) (base w)),
      (dist_nonneg : 0 ≤ dist z w), sq_nonneg (dist (height z) (height w))]
  have hh : LipschitzWith 1 (height : V (n+1) → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    have hs := hsplit z w
    nlinarith [(dist_nonneg : 0 ≤ dist (height z) (height w)),
      (dist_nonneg : 0 ≤ dist z w), sq_nonneg (dist (base z) (base w))]
  refine ⟨hb, hh, ?_⟩
  intro δ W hδ hW i
  have hi : Metric.ediam (W i) ≤ ENNReal.ofReal δ := hW.2 i
  have hfin : Metric.ediam (W i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi
  have hconv : ENNReal.ofReal (Metric.diam (W i)) = Metric.ediam (W i) :=
    ENNReal.ofReal_toReal hfin
  refine ⟨hconv.symm, Metric.diam_nonneg, ENNReal.toReal_le_of_le_ofReal hδ.le hi, ?_, ?_⟩
  · simpa only [ENNReal.coe_one, one_mul] using hb.ediam_image_le (W i)
  · simpa only [ENNReal.coe_one, one_mul] using hh.ediam_image_le (W i)

theorem T017 (n : ℕ) (E : Set (V n)) (h_T015 : (MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1) ∧ (∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → Metric.ediam B ≤ ENNReal.ofReal ρ → 0 < η → Bornology.IsBounded B ∧ BddBelow B ∧ BddAbove B ∧ (∀ b ∈ B, sInf B ≤ b ∧ b ≤ sSup B) ∧ sSup B - sInf B ≤ ρ ∧ B ⊆ Set.Ioo (sInf B - η/2) (sSup B + η/2) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2)) ∧ 0 < sSup B - sInf B + η ∧ sSup B - sInf B + η ≤ ρ + η ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2)) : ℝ≥0∞) = ENNReal.ofReal (sSup B - sInf B + η) ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (ρ + η) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI))) (h_T016 : LipschitzWith 1 (base : V (n+1) → V n) ∧ LipschitzWith 1 (height : V (n+1) → ℝ) ∧ (∀ (δ : ℝ) (W : ℕ → Set (V (n+1))), 0 < δ → scaleCover δ (cylinder E) W → ∀ i, Metric.ediam (W i) = ENNReal.ofReal (Metric.diam (W i)) ∧ 0 ≤ Metric.diam (W i) ∧ Metric.diam (W i) ≤ δ ∧ Metric.ediam (base '' W i) ≤ Metric.ediam (W i) ∧ Metric.ediam (height '' W i) ≤ Metric.ediam (W i))) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    ∀ (s δ ε : ℝ) (W : ℕ → Set (V (n+1))), 0 < s → 0 < δ → 0 < ε → scaleCover δ (cylinder E) W → ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i) ∧ height '' W i ⊆ J i ∧ (volume (J i ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (Metric.diam (W i) + padding ε s W i)) ∧ (∀ t ∈ unitI, content s δ E ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => (Metric.ediam (W i)) ^ s) t) := by
  classical
  intro s δ ε W hs hδ hε hW
  have hdiam := h_T016.2.2 δ W hδ hW
  have hpad (i : ℕ) : 0 < padding ε s W i := by
    unfold padding
    exact div_pos (mul_pos hε (Real.rpow_pos_of_pos (by norm_num) _))
      (by positivity)
  let J : ℕ → Set ℝ := fun i => if (W i).Nonempty then
    Set.Ioo (sInf (height '' W i) - padding ε s W i / 2)
      (sSup (height '' W i) + padding ε s W i / 2) else ∅
  have hJ (i : ℕ) : MeasurableSet (J i) ∧ height '' W i ⊆ J i ∧
      volume (J i ∩ unitI) ≤ ENNReal.ofReal (Metric.diam (W i) + padding ε s W i) := by
    by_cases hi : (W i).Nonempty
    · have hB : (height '' W i).Nonempty := hi.image height
      have hbound : Metric.ediam (height '' W i) ≤ ENNReal.ofReal (Metric.diam (W i)) :=
        (hdiam i).2.2.2.2.trans (hdiam i).1.le
      rcases h_T015.2 (height '' W i) (Metric.diam (W i)) (padding ε s W i)
        hB (hdiam i).2.1 hbound (hpad i) with
        ⟨hb, hlo, hup, hmem, hlen, hsub, hmeas, hpos, hle, hvol, hinter, hmi⟩
      simpa only [J, if_pos hi] using And.intro hmeas (And.intro hsub hinter)
    · have he : W i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp only [J, if_neg hi, he, Set.image_empty, Set.empty_subset, Set.empty_inter,
        measure_empty, true_and]
      exact ⟨MeasurableSet.empty, bot_le⟩
  refine ⟨J, hJ, ?_⟩
  intro t ht
  let A : ℕ → Set (V n) := fun i => if t ∈ J i then base '' W i else ∅
  have hA : scaleCover δ E A := by
    constructor
    · intro x hx
      have hinv := h_T008.2.2.2.2.2.2.2.1 x t
      have hxt : join x t ∈ cylinder E := by
        change base (join x t) ∈ E ∧ height (join x t) ∈ unitI
        simpa only [hinv.1, hinv.2] using And.intro hx ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hxt)
      have htJ : t ∈ J i := by
        apply (hJ i).2.1
        exact ⟨join x t, hi, hinv.2⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simp only [A, if_pos htJ]
      exact ⟨join x t, hi, hinv.1⟩
    · intro i
      by_cases hi : t ∈ J i
      · simpa only [A, if_pos hi] using (hdiam i).2.2.2.1.trans (hW.2 i)
      · simp only [A, if_neg hi, Metric.ediam_empty]
        exact bot_le
  have hc : content s δ E ≤ cost s A := by
    unfold content
    exact iInf_le_of_le A (iInf_le_of_le hA le_rfl)
  refine hc.trans ?_
  unfold cost
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : t ∈ J i
  · simp only [A, if_pos hi, Set.indicator_of_mem hi]
    exact ENNReal.rpow_le_rpow (hdiam i).2.2.2.1 hs.le
  · simp only [A, if_neg hi, Metric.ediam_empty, Set.indicator_of_notMem hi]
    simp [ENNReal.zero_rpow_of_pos hs]

theorem T018 (n : ℕ) (E : Set (V n)) (h_T015 : (MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1) ∧ (∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → Metric.ediam B ≤ ENNReal.ofReal ρ → 0 < η → Bornology.IsBounded B ∧ BddBelow B ∧ BddAbove B ∧ (∀ b ∈ B, sInf B ≤ b ∧ b ≤ sSup B) ∧ sSup B - sInf B ≤ ρ ∧ B ⊆ Set.Ioo (sInf B - η/2) (sSup B + η/2) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2)) ∧ 0 < sSup B - sInf B + η ∧ sSup B - sInf B + η ≤ ρ + η ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2)) : ℝ≥0∞) = ENNReal.ofReal (sSup B - sInf B + η) ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (ρ + η) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI))) :
    ∀ (c : ℝ≥0∞) (w : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ t ∈ unitI, c ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => w i) t) → ((∀ i, Measurable (Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i))) ∧ (∀ t : ℝ, Set.indicator unitI (fun t0 : ℝ => c) t ≤ ∑' i, Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i) t) ∧ c ≤ ∑' i, w i * volume (J i ∩ unitI)) := by
  intro c w J hJ hbound
  have hI : MeasurableSet unitI := h_T015.1.1
  have hvol : volume unitI = 1 := h_T015.1.2
  have hm : ∀ i, Measurable (Set.indicator (J i ∩ unitI) (fun _ : ℝ => w i)) := by
    intro i
    exact measurable_const.indicator ((hJ i).inter hI)
  have hp : ∀ t : ℝ, Set.indicator unitI (fun _ : ℝ => c) t ≤ ∑' i, Set.indicator (J i ∩ unitI) (fun _ : ℝ => w i) t := by
    intro t
    by_cases ht : t ∈ unitI
    · have heq : ∀ i, Set.indicator (J i ∩ unitI) (fun _ : ℝ => w i) t = Set.indicator (J i) (fun _ : ℝ => w i) t := by
        intro i
        by_cases hj : t ∈ J i
        · simp [Set.indicator_of_mem, hj, ht]
        · simp [Set.indicator_of_notMem, hj, ht]
      simpa only [Set.indicator_of_mem ht, heq] using hbound t ht
    · simp [Set.indicator_of_notMem, ht]
  refine ⟨hm, hp, ?_⟩
  have hi := lintegral_mono (μ := volume) hp
  rw [lintegral_indicator_const hI c, hvol, mul_one,
    lintegral_tsum (fun i => (hm i).aemeasurable)] at hi
  simpa only [lintegral_indicator_const ((hJ _).inter hI)] using hi

theorem T019 (n : ℕ) (E : Set (V n)) (h_T017 : ∀ (s δ ε : ℝ) (W : ℕ → Set (V (n+1))), 0 < s → 0 < δ → 0 < ε → scaleCover δ (cylinder E) W → ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i) ∧ height '' W i ⊆ J i ∧ (volume (J i ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (Metric.diam (W i) + padding ε s W i)) ∧ (∀ t ∈ unitI, content s δ E ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => (Metric.ediam (W i)) ^ s) t)) (h_T018 : ∀ (c : ℝ≥0∞) (w : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ t ∈ unitI, c ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => w i) t) → ((∀ i, Measurable (Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i))) ∧ (∀ t : ℝ, Set.indicator unitI (fun t0 : ℝ => c) t ≤ ∑' i, Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i) t) ∧ c ≤ ∑' i, w i * volume (J i ∩ unitI))) (h_T016 : LipschitzWith 1 (base : V (n+1) → V n) ∧ LipschitzWith 1 (height : V (n+1) → ℝ) ∧ (∀ (δ : ℝ) (W : ℕ → Set (V (n+1))), 0 < δ → scaleCover δ (cylinder E) W → ∀ i, Metric.ediam (W i) = ENNReal.ofReal (Metric.diam (W i)) ∧ 0 ≤ Metric.diam (W i) ∧ Metric.diam (W i) ≤ δ ∧ Metric.ediam (base '' W i) ≤ Metric.ediam (W i) ∧ Metric.ediam (height '' W i) ≤ Metric.ediam (W i))) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) :
    ∀ (s δ ε : ℝ) (W : ℕ → Set (V (n+1))), 0 < s → 0 < δ → 0 < ε → scaleCover δ (cylinder E) W → content s δ E ≤ cost (s+1) W + ENNReal.ofReal ε := by
  intro s δ ε W hs hδ hε hW
  obtain ⟨J, hJ, hpoint⟩ := h_T017 s δ ε W hs hδ hε hW
  have hint := (h_T018 (content s δ E) (fun i => (Metric.ediam (W i)) ^ s) J (fun i => (hJ i).1) hpoint).2.2
  have hterm : ∀ i, (Metric.ediam (W i)) ^ s * volume (J i ∩ unitI) ≤ (Metric.ediam (W i)) ^ (s+1) + ENNReal.ofReal ε * ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ)-1)) := by
    intro i
    apply le_trans (mul_le_mul_left' (hJ i).2.2 _)
    obtain ⟨he, hd, _⟩ := h_T016.2.2 δ W hδ hW i
    have ha : 0 ≤ (Metric.diam (W i)) ^ s := Real.rpow_nonneg hd s
    have hg : 0 ≤ (2 : ℝ) ^ (-(i : ℝ)-1) := Real.rpow_nonneg (by norm_num) _
    have hb : 0 ≤ ε * (2 : ℝ) ^ (-(i : ℝ)-1) := mul_nonneg hε.le hg
    have hpad : padding ε s W i * (Metric.diam (W i)) ^ s ≤ ε * (2 : ℝ) ^ (-(i : ℝ)-1) := by
      unfold padding
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 1 + (Metric.diam (W i)) ^ s)).2
      nlinarith
    have halg : (Metric.diam (W i)) ^ s * (Metric.diam (W i) + padding ε s W i) ≤ (Metric.diam (W i)) ^ (s+1) + ε * (2 : ℝ) ^ (-(i : ℝ)-1) := by
      rw [Real.rpow_add_of_nonneg hd hs.le (by norm_num), Real.rpow_one]
      nlinarith
    rw [he, ENNReal.ofReal_rpow_of_nonneg hd hs.le, ENNReal.ofReal_rpow_of_nonneg hd (by linarith)]
    rw [← ENNReal.ofReal_mul ha]
    calc
      _ ≤ ENNReal.ofReal ((Metric.diam (W i)) ^ (s+1) + ε * (2 : ℝ) ^ (-(i : ℝ)-1)) := ENNReal.ofReal_le_ofReal halg
      _ ≤ _ := by
        simpa only [ENNReal.ofReal_mul hε.le] using (ENNReal.ofReal_add_le (p := (Metric.diam (W i)) ^ (s+1)) (q := ε * (2 : ℝ) ^ (-(i : ℝ)-1)))
  calc
    content s δ E ≤ ∑' i, (Metric.ediam (W i)) ^ s * volume (J i ∩ unitI) := hint
    _ ≤ ∑' i, ((Metric.ediam (W i)) ^ (s+1) + ENNReal.ofReal ε * ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ)-1))) := ENNReal.tsum_le_tsum hterm
    _ = cost (s+1) W + ENNReal.ofReal ε := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, h_T004.2.2.2.series_one, mul_one]
      rfl

theorem T020 (n : ℕ) (E : Set (V n)) (h_T019 : ∀ (s δ ε : ℝ) (W : ℕ → Set (V (n+1))), 0 < s → 0 < δ → 0 < ε → scaleCover δ (cylinder E) W → content s δ E ≤ cost (s+1) W + ENNReal.ofReal ε) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    ∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E ≤ content (s+1) δ (cylinder E) := by
  intro s δ hs hδ
  unfold content
  refine le_iInf fun W => le_iInf fun hW => ?_
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hcoe : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) := by simp
  have h := h_T019 s δ (ε : ℝ) W hs hδ hεreal hW
  rw [hcoe] at h
  exact h

theorem T021 (n : ℕ) (E : Set (V n)) (h_T020 : ∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E ≤ content (s+1) δ (cylinder E)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    0 < dimH E → ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E → haus (s+1) (cylinder E) = ⊤ ∧ ENNReal.ofReal (s+1) ≤ dimH (cylinder E) := by
  intro _ s hs hsD
  have hE : haus s E = ⊤ := (h_T004.2.1.critical E s hs).1 hsD
  have hle : haus s E ≤ haus (s + 1) (cylinder E) := by
    unfold haus
    exact iSup_mono fun δ => iSup_mono fun hδ => h_T020 s δ hs hδ
  have hF : haus (s + 1) (cylinder E) = ⊤ := by
    apply top_unique
    simpa only [hE] using hle
  have hs1 : 0 < s + 1 := by linarith
  exact ⟨hF, (h_T004.2.1.critical (cylinder E) (s + 1) hs1).2.2.2 hF⟩

theorem T022 (n : ℕ) (E : Set (V n)) (h_T021 : 0 < dimH E → ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E → haus (s+1) (cylinder E) = ⊤ ∧ ENNReal.ofReal (s+1) ≤ dimH (cylinder E)) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) :
    0 < dimH E → dimH E + 1 ≤ dimH (cylinder E) := by
  intro hD
  by_cases hQ : dimH (cylinder E) = ⊤
  · simp [hQ]
  have hDfin : dimH E ≠ ⊤ := h_T008.2.1
  have hDpos : 0 < (dimH E).toReal := ENNReal.toReal_pos (ne_of_gt hD) hDfin
  have hbound : (dimH E).toReal + 1 ≤ (dimH (cylinder E)).toReal := by
    by_contra h
    have hlt : (dimH (cylinder E)).toReal - 1 < (dimH E).toReal := by
      linarith
    obtain ⟨s, hs, hsD⟩ := exists_between (max_lt hDpos hlt)
    have hspos : 0 < s := lt_of_le_of_lt (le_max_left _ _) hs
    have hsQ : (dimH (cylinder E)).toReal - 1 < s :=
      lt_of_le_of_lt (le_max_right _ _) hs
    have hsDim : ENNReal.ofReal s < dimH E :=
      (ENNReal.ofReal_lt_iff_lt_toReal hspos.le hDfin).2 hsD
    have hle : ENNReal.ofReal (s + 1) ≤ dimH (cylinder E) :=
      (h_T021 hD s hspos hsDim).2
    have hreal : s + 1 ≤ (dimH (cylinder E)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hQ).1 hle
    linarith
  have hconvert : dimH E + 1 = ENNReal.ofReal ((dimH E).toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.ofReal_toReal hDfin, ENNReal.ofReal_one]
  rw [hconvert]
  exact (ENNReal.ofReal_le_iff_le_toReal hQ).2 hbound

theorem T023 (n : ℕ) (E : Set (V n)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) :
    (∀ a : ℝ, 1 < a → haus a unitI = 0) ∧ dimH unitI ≤ 1 := by
  have hbound : ∀ (a : ℝ), 1 < a → ∀ (m : ℕ), 0 < m → ∀ δ : ℝ, 1 / (m : ℝ) ≤ δ → content a δ unitI ≤ ENNReal.ofReal ((1 / (m : ℝ)) ^ (a - 1)) := by
    intro a ha m hm δ hδ
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hrec : 0 < 1 / (m : ℝ) := by positivity
    let U : ℕ → Set ℝ := fun j => if j < m then Icc ((j : ℝ) / m) (((j : ℝ) + 1) / m) else ∅
    have hcov : scaleCover δ unitI U := by
      constructor
      · intro x hx
        have hx0 : 0 ≤ x := hx.1
        have hx1 : x ≤ 1 := hx.2
        apply Set.mem_iUnion.mpr
        by_cases hx : x = 1
        · refine ⟨m - 1, ?_⟩
          have hj : m - 1 < m := by omega
          have hjR : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
          simp only [U, if_pos hj, mem_Icc, hx, hjR]
          constructor
          · apply (div_le_iff₀ hmR).2; linarith
          · apply (le_div_iff₀ hmR).2; linarith
        · have hxl : x < 1 := lt_of_le_of_ne hx1 hx
          have hxm : x * m < (m : ℝ) := by nlinarith
          have hj : ⌊x * m⌋₊ < m := (Nat.floor_lt (by positivity)).2 hxm
          refine ⟨⌊x * m⌋₊, ?_⟩
          simp only [U, if_pos hj, mem_Icc]
          constructor
          · exact (div_le_iff₀ hmR).2 (Nat.floor_le (by positivity))
          · exact (le_div_iff₀ hmR).2 (Nat.lt_floor_add_one (x * m)).le
      · intro j
        dsimp [U]
        split_ifs with hj
        · rw [Real.ediam_Icc]
          have heq : ((j : ℝ) + 1) / m - (j : ℝ) / m = 1 / (m : ℝ) := by ring
          rw [heq]
          exact ENNReal.ofReal_le_ofReal hδ
        · simp
    have hcost : cost a U = ENNReal.ofReal ((1 / (m : ℝ)) ^ (a - 1)) := by
      unfold cost
      rw [tsum_eq_sum (s := Finset.range m)]
      · have hd : ∀ j ∈ Finset.range m, Metric.ediam (U j) = ENNReal.ofReal (1 / (m : ℝ)) := by
          intro j hj
          simp only [U, if_pos (Finset.mem_range.mp hj), Real.ediam_Icc]
          congr 1
          ring
        rw [Finset.sum_congr rfl (fun j hj => congrArg (fun d : ℝ≥0∞ => d ^ a) (hd j hj))]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_rpow_of_pos hrec]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hmR.le]
        congr 1
        rw [Real.rpow_sub_one (ne_of_gt hrec)]
        field_simp
      · intro j hj
        have hj' : ¬ j < m := by simpa using hj
        simp [U, hj', ENNReal.zero_rpow_of_pos (show 0 < a by linarith)]
    have hb : content a δ unitI ≤ cost a U := by
      unfold content
      exact iInf_le_of_le U (iInf_le_of_le hcov le_rfl)
    exact hb.trans_eq hcost
  have hzero : ∀ a : ℝ, 1 < a → haus a unitI = 0 := by
    intro a ha
    have hr : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hrWithin : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhdsWithin 0 (Ioi 0)) := by
      exact tendsto_nhdsWithin_iff.mpr ⟨hr, Filter.Eventually.of_forall (fun k => by simp only [mem_Ioi]; positivity)⟩
    have hp : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ (a - 1)) Filter.atTop (nhds 0) :=
      (h_T004.2.2.2.positive_limit (a - 1) (by linarith)).comp hrWithin
    have hpE : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal ((1 / ((k : ℝ) + 1)) ^ (a - 1))) Filter.atTop (nhds 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
    have hc : ∀ δ : ℝ, 0 < δ → content a δ unitI = 0 := by
      intro δ hδ
      apply le_antisymm _ bot_le
      apply ge_of_tendsto hpE
      have hev : ∀ᶠ k : ℕ in Filter.atTop, 1 / ((k : ℝ) + 1) < δ := hr.eventually (gt_mem_nhds hδ)
      filter_upwards [hev] with k hk
      have hkm : 1 / ((k + 1 : ℕ) : ℝ) ≤ δ := by simpa only [Nat.cast_add, Nat.cast_one] using hk.le
      simpa only [Nat.cast_add, Nat.cast_one] using hbound a ha (k + 1) (by omega) δ hkm
    rw [h_T004.1.supremum]
    apply le_antisymm _ bot_le
    exact iSup_le fun δ => iSup_le fun hδ => (hc δ hδ).le
  refine ⟨hzero, ?_⟩
  by_contra hn
  have hlt : (1 : ℝ≥0∞) < dimH unitI := lt_of_not_ge hn
  obtain ⟨a, ha0, h1a, had⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have ha : 1 < a := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa using h1a)
  have hd : dimH unitI ≤ ENNReal.ofReal a := (h_T004.2.1.critical unitI a (by linarith)).2.2.1 (hzero a ha)
  exact (not_lt_of_ge hd) had

theorem T024 (n : ℕ) (E : Set (V n)) (h_T015 : (MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1) ∧ (∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → Metric.ediam B ≤ ENNReal.ofReal ρ → 0 < η → Bornology.IsBounded B ∧ BddBelow B ∧ BddAbove B ∧ (∀ b ∈ B, sInf B ≤ b ∧ b ≤ sSup B) ∧ sSup B - sInf B ≤ ρ ∧ B ⊆ Set.Ioo (sInf B - η/2) (sSup B + η/2) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2)) ∧ 0 < sSup B - sInf B + η ∧ sSup B - sInf B + η ≤ ρ + η ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2)) : ℝ≥0∞) = ENNReal.ofReal (sSup B - sInf B + η) ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (ρ + η) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI))) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) :
    ∀ (δ : ℝ) (W : ℕ → Set ℝ), 0 < δ → scaleCover δ unitI W → (1 : ℝ≥0∞) ≤ cost 1 W := by
  classical
  intro δ W hδ hW
  have hconv (i : ℕ) : ENNReal.ofReal (Metric.diam (W i)) = Metric.ediam (W i) := by
    apply ENNReal.ofReal_toReal
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW.2 i)
  have hcost : cost 1 W = ∑' i, Metric.ediam (W i) := by
    simp [cost]
  rw [hcost]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  let η : ℕ → ℝ := fun i => (ε : ℝ) * (2 : ℝ) ^ (-(i : ℝ)-1)
  have hη (i : ℕ) : 0 < η i := by
    dsimp [η]
    exact mul_pos (by exact_mod_cast hε) (Real.rpow_pos_of_pos (by norm_num) _)
  let J : ℕ → Set ℝ := fun i => if (W i).Nonempty then
    Set.Ioo (sInf (W i) - η i / 2) (sSup (W i) + η i / 2) else ∅
  have hJ (i : ℕ) : W i ⊆ J i ∧ volume (J i) ≤ Metric.ediam (W i) + ENNReal.ofReal (η i) := by
    by_cases hi : (W i).Nonempty
    · rcases h_T015.2 (W i) (Metric.diam (W i)) (η i) hi Metric.diam_nonneg (hconv i).symm.le (hη i) with
        ⟨hb, hlo, hup, hbds, hwidth, hsub, hm, hp, hlen, hvol, hrest⟩
      dsimp [J]
      rw [if_pos hi]
      refine ⟨hsub, ?_⟩
      calc
        volume (Set.Ioo (sInf (W i) - η i / 2) (sSup (W i) + η i / 2)) = ENNReal.ofReal (sSup (W i) - sInf (W i) + η i) := hvol
        _ ≤ ENNReal.ofReal (Metric.diam (W i) + η i) := ENNReal.ofReal_le_ofReal hlen
        _ = Metric.ediam (W i) + ENNReal.ofReal (η i) := by
          rw [ENNReal.ofReal_add Metric.diam_nonneg (le_of_lt (hη i)), hconv i]
    · have hw : W i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp [J, hi, hw]
  have hcover : unitI ⊆ ⋃ i, J i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, (hJ i).1 hi⟩
  have herr : (∑' i, ENNReal.ofReal (η i)) = (ε : ℝ≥0∞) := by
    simp only [η, ENNReal.ofReal_mul ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.tsum_mul_left, h_T004.2.2.2.series_one, mul_one]
  calc
    (1 : ℝ≥0∞) = volume unitI := h_T015.1.2.symm
    _ ≤ volume (⋃ i, J i) := measure_mono hcover
    _ ≤ ∑' i, volume (J i) := measure_iUnion_le J
    _ ≤ ∑' i, (Metric.ediam (W i) + ENNReal.ofReal (η i)) := ENNReal.tsum_le_tsum (fun i => (hJ i).2)
    _ = (∑' i, Metric.ediam (W i)) + ε := by rw [ENNReal.tsum_add, herr]

theorem T025 (n : ℕ) (E : Set (V n)) (h_T024 : ∀ (δ : ℝ) (W : ℕ → Set ℝ), 0 < δ → scaleCover δ unitI W → (1 : ℝ≥0∞) ≤ cost 1 W) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) :
    (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → ENNReal.ofReal (δ ^ (s-1)) ≤ content s δ unitI) ∧ (∀ s : ℝ, 0 < s → s < 1 → haus s unitI = ⊤) ∧ (1 : ℝ≥0∞) ≤ dimH unitI := by
  rcases h_T004 with ⟨hscale, hcrit, hinv, hpower⟩
  have hscalar : ∀ (s δ : ℝ) (r : ℝ≥0∞), 0 < s → s < 1 → 0 < δ → r ≤ ENNReal.ofReal δ → ENNReal.ofReal (δ ^ (s-1)) * r ≤ r ^ s := by
    intro s δ r hs hs1 hd hr
    have hrfin : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr
    have hrδ : r.toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hd.le hr
    have hre : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrfin
    have hreal : δ ^ (s-1) * r.toReal ≤ r.toReal ^ s := by
      by_cases hz : r.toReal = 0
      · simp [hz, Real.zero_rpow (ne_of_gt hs)]
      · have hp : 0 < r.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
        have hpow := Real.rpow_le_rpow_of_nonpos hp hrδ (by linarith : s-1 ≤ 0)
        calc
          δ ^ (s-1) * r.toReal ≤ r.toReal ^ (s-1) * r.toReal := mul_le_mul_of_nonneg_right hpow hp.le
          _ = r.toReal ^ s := by rw [Real.rpow_sub_one hz, div_mul_cancel₀ _ hz]
    calc
      ENNReal.ofReal (δ ^ (s-1)) * r = ENNReal.ofReal (δ ^ (s-1) * r.toReal) := by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), hre]
      _ ≤ ENNReal.ofReal (r.toReal ^ s) := ENNReal.ofReal_le_ofReal hreal
      _ = r ^ s := by rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le, hre]
  have hcontent : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → ENNReal.ofReal (δ ^ (s-1)) ≤ content s δ unitI := by
    intro s δ hs hs1 hd
    unfold content
    refine le_iInf fun W => le_iInf fun hW => ?_
    have hsum : ENNReal.ofReal (δ ^ (s-1)) * cost 1 W ≤ cost s W := by
      simp only [cost, ENNReal.rpow_one, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun i => hscalar s δ (Metric.ediam (W i)) hs hs1 hd (hW.2 i)
    calc
      ENNReal.ofReal (δ ^ (s-1)) = ENNReal.ofReal (δ ^ (s-1)) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (δ ^ (s-1)) * cost 1 W := mul_le_mul_left' (h_T024 δ W hd hW) _
      _ ≤ cost s W := hsum
  have hhaus : ∀ s : ℝ, 0 < s → s < 1 → haus s unitI = ⊤ := by
    intro s hs hs1
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro b
    have hev := (hpower.negative_limit (s-1) (by linarith)).eventually_ge_atTop (b : ℝ)
    obtain ⟨δ, hδ, hb⟩ := (Filter.Eventually.and (show ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), 0 < δ from self_mem_nhdsWithin) hev).exists
    calc
      (b : ℝ≥0∞) = ENNReal.ofReal (b : ℝ) := by simp
      _ ≤ ENNReal.ofReal (δ ^ (s-1)) := ENNReal.ofReal_le_ofReal hb
      _ ≤ content s δ unitI := hcontent s δ hs hs1 hδ
      _ ≤ haus s unitI := by
        rw [hscale.supremum]
        exact le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)
  refine ⟨hcontent, hhaus, ?_⟩
  by_contra hn
  have hlt : dimH unitI < (1 : ℝ≥0∞) := lt_of_not_ge hn
  obtain ⟨s, hs0, hds, hs1⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hs : 0 < s := by
    by_contra h
    have : ENNReal.ofReal s = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h)
    rw [this] at hds
    exact (not_lt_of_ge bot_le) hds
  have hsone : s < 1 := (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp (by simpa using hs1)
  have hsd : ENNReal.ofReal s ≤ dimH unitI := (hcrit.critical unitI s hs).2.2.2 (hhaus s hs hsone)
  exact (not_le_of_gt hds) hsd

theorem T026 (n : ℕ) (E : Set (V n)) (h_T023 : (∀ a : ℝ, 1 < a → haus a unitI = 0) ∧ dimH unitI ≤ 1) (h_T025 : (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → ENNReal.ofReal (δ ^ (s-1)) ≤ content s δ unitI) ∧ (∀ s : ℝ, 0 < s → s < 1 → haus s unitI = ⊤) ∧ (1 : ℝ≥0∞) ≤ dimH unitI) :
    (∀ a : ℝ, 1 < a → haus a unitI = 0) ∧ (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → ENNReal.ofReal (δ ^ (s-1)) ≤ content s δ unitI) ∧ (∀ s : ℝ, 0 < s → s < 1 → haus s unitI = ⊤) ∧ dimH unitI = 1 := by
  exact ⟨h_T023.1, h_T025.1, h_T025.2.1, le_antisymm h_T023.2 h_T025.2.2⟩

theorem T027 (n : ℕ) (E : Set (V n)) (h_H002 : E.Nonempty) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) (h_T013 : dimH (cylinder E) ≤ dimH E + 1) (h_T022 : 0 < dimH E → dimH E + 1 ≤ dimH (cylinder E)) (h_T026 : (∀ a : ℝ, 1 < a → haus a unitI = 0) ∧ (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → ENNReal.ofReal (δ ^ (s-1)) ≤ content s δ unitI) ∧ (∀ s : ℝ, 0 < s → s < 1 → haus s unitI = ⊤) ∧ dimH unitI = 1) :
    dimH (cylinder E) = dimH E + 1 := by
  apply le_antisymm h_T013
  by_cases hpos : 0 < dimH E
  · exact h_T022 hpos
  · have hzero : dimH E = 0 := le_antisymm (le_of_not_gt hpos) bot_le
    obtain ⟨x₀, hx₀⟩ := h_H002
    rcases h_T008 with ⟨hbound, hfin, hbdd, hR, hc, hn, hbij, hjoin, hinv, hdist⟩
    let f : unitI → V (n+1) := fun t => join x₀ (t : ℝ)
    have hf : Isometry f := by
      apply isometry_iff_dist_eq.mpr
      intro t u
      have hs : dist (f t) (f u) ^ 2 = dist (t : ℝ) (u : ℝ) ^ 2 := by
        simpa only [f, dist_self, zero_pow (by decide : 2 ≠ 0), zero_add] using
          hdist x₀ x₀ (t : ℝ) (u : ℝ)
      change dist (f t) (f u) = dist (t : ℝ) (u : ℝ)
      have ha : 0 ≤ dist (f t) (f u) := dist_nonneg
      have hb : 0 ≤ dist (t : ℝ) (u : ℝ) := dist_nonneg
      nlinarith
    have hsub : Set.range f ⊆ cylinder E := by
      rintro z ⟨t, rfl⟩
      change base (join x₀ (t : ℝ)) ∈ E ∧ height (join x₀ (t : ℝ)) ∈ unitI
      rw [(hjoin x₀ (t : ℝ)).1, (hjoin x₀ (t : ℝ)).2]
      exact ⟨hx₀, t.property⟩
    have heq : dimH (Set.range f) = dimH unitI :=
      (h_T004.2.2.1.isometry unitI f hf).1
    have hmono : dimH (Set.range f) ≤ dimH (cylinder E) :=
      h_T004.2.2.1.mono (Set.range f) (cylinder E) hsub
    rw [heq, h_T026.2.2.2] at hmono
    simpa only [hzero, zero_add] using hmono

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (V n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) :
    dimH (cylinder E) = dimH E + 1 := by
  have h_T001 : ScaleLaws := @T001 n E 
  have h_T002 : CriticalLaws := @T002 n E h_T001
  have h_T003 : InvarianceLaws := @T003 n E h_T001 h_T002
  have h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws := @T004 n E h_T001 h_T002 h_T003
  have h_T005 : (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ Bornology.IsBounded E ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) := @T005 n E h_H003
  have h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) := @T006 n E h_H002 h_T004 h_T005
  have h_T007 : Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2) := @T007 n E 
  have h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2) := @T008 n E h_T005 h_T006 h_T007
  have h_T011 : n = 0 → dimH (cylinder E) ≤ dimH E + 1 := @T011 n E h_T004 h_T008
  have h_T009 : 1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (V n), scaleCover r E W ∧ cost q W < ENNReal.ofReal (ε/2) := @T009 n E h_T004 h_T008
  have h_T010 : 1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ K : Set ℕ, ∃ U : K → Set (V n), E ⊆ (⋃ i, U i) ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ cost q U < ENNReal.ofReal ε := @T010 n E h_T009 h_T004
  have h_T012 : 1 ≤ n → ∀ q δ ε : ℝ, dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε → ∃ W : ℕ → Set (V (n+1)), scaleCover δ (cylinder E) W ∧ cost (q+1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) := @T012 n E h_T010 h_T008
  have h_T013 : dimH (cylinder E) ≤ dimH E + 1 := @T013 n E h_T011 h_T012 h_T004 h_T008
  have h_T014 : MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1 := @T014 n E 
  have h_T015 : (MeasurableSet unitI ∧ (volume unitI : ℝ≥0∞) = 1) ∧ (∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → Metric.ediam B ≤ ENNReal.ofReal ρ → 0 < η → Bornology.IsBounded B ∧ BddBelow B ∧ BddAbove B ∧ (∀ b ∈ B, sInf B ≤ b ∧ b ≤ sSup B) ∧ sSup B - sInf B ≤ ρ ∧ B ⊆ Set.Ioo (sInf B - η/2) (sSup B + η/2) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2)) ∧ 0 < sSup B - sInf B + η ∧ sSup B - sInf B + η ≤ ρ + η ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2)) : ℝ≥0∞) = ENNReal.ofReal (sSup B - sInf B + η) ∧ (volume (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (ρ + η) ∧ MeasurableSet (Set.Ioo (sInf B - η/2) (sSup B + η/2) ∩ unitI)) := @T015 n E h_T014
  have h_T016 : LipschitzWith 1 (base : V (n+1) → V n) ∧ LipschitzWith 1 (height : V (n+1) → ℝ) ∧ (∀ (δ : ℝ) (W : ℕ → Set (V (n+1))), 0 < δ → scaleCover δ (cylinder E) W → ∀ i, Metric.ediam (W i) = ENNReal.ofReal (Metric.diam (W i)) ∧ 0 ≤ Metric.diam (W i) ∧ Metric.diam (W i) ≤ δ ∧ Metric.ediam (base '' W i) ≤ Metric.ediam (W i) ∧ Metric.ediam (height '' W i) ≤ Metric.ediam (W i)) := @T016 n E h_T008
  have h_T017 : ∀ (s δ ε : ℝ) (W : ℕ → Set (V (n+1))), 0 < s → 0 < δ → 0 < ε → scaleCover δ (cylinder E) W → ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i) ∧ height '' W i ⊆ J i ∧ (volume (J i ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (Metric.diam (W i) + padding ε s W i)) ∧ (∀ t ∈ unitI, content s δ E ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => (Metric.ediam (W i)) ^ s) t) := @T017 n E h_T015 h_T016 h_T008
  have h_T018 : ∀ (c : ℝ≥0∞) (w : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ t ∈ unitI, c ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => w i) t) → ((∀ i, Measurable (Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i))) ∧ (∀ t : ℝ, Set.indicator unitI (fun t0 : ℝ => c) t ≤ ∑' i, Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i) t) ∧ c ≤ ∑' i, w i * volume (J i ∩ unitI)) := @T018 n E h_T015
  have h_T019 : ∀ (s δ ε : ℝ) (W : ℕ → Set (V (n+1))), 0 < s → 0 < δ → 0 < ε → scaleCover δ (cylinder E) W → content s δ E ≤ cost (s+1) W + ENNReal.ofReal ε := @T019 n E h_T017 h_T018 h_T016 h_T004
  have h_T020 : ∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E ≤ content (s+1) δ (cylinder E) := @T020 n E h_T019 h_T008
  have h_T021 : 0 < dimH E → ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E → haus (s+1) (cylinder E) = ⊤ ∧ ENNReal.ofReal (s+1) ≤ dimH (cylinder E) := @T021 n E h_T020 h_T004 h_T008
  have h_T022 : 0 < dimH E → dimH E + 1 ≤ dimH (cylinder E) := @T022 n E h_T021 h_T008
  have h_T023 : (∀ a : ℝ, 1 < a → haus a unitI = 0) ∧ dimH unitI ≤ 1 := @T023 n E h_T004
  have h_T024 : ∀ (δ : ℝ) (W : ℕ → Set ℝ), 0 < δ → scaleCover δ unitI W → (1 : ℝ≥0∞) ≤ cost 1 W := @T024 n E h_T015 h_T004
  have h_T025 : (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → ENNReal.ofReal (δ ^ (s-1)) ≤ content s δ unitI) ∧ (∀ s : ℝ, 0 < s → s < 1 → haus s unitI = ⊤) ∧ (1 : ℝ≥0∞) ≤ dimH unitI := @T025 n E h_T024 h_T004
  have h_T026 : (∀ a : ℝ, 1 < a → haus a unitI = 0) ∧ (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → ENNReal.ofReal (δ ^ (s-1)) ≤ content s δ unitI) ∧ (∀ s : ℝ, 0 < s → s < 1 → haus s unitI = ⊤) ∧ dimH unitI = 1 := @T026 n E h_T023 h_T025
  have h_T027 : dimH (cylinder E) = dimH E + 1 := @T027 n E h_H002 h_T004 h_T008 h_T013 h_T022 h_T026
  exact h_T027

#check @P
#print axioms P

end Translation
