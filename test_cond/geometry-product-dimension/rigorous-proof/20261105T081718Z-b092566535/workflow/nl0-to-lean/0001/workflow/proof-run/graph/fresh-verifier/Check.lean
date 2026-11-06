import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ r : ℝ≥0∞, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r" := by
  intro r hr
  by_cases htop : r = ⊤
  · exact ⟨1, zero_lt_one, by simp [htop]⟩
  · exact ⟨r.toReal, ENNReal.toReal_pos (ne_of_gt hr) htop, ENNReal.ofReal_toReal_le⟩

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A := by
  intro X instMetric instMeas instBorel A a ha
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  unfold YuiMeasure YuiContent YuiCost
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    refine le_trans ?_ (le_iSup₂ (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ))
    refine le_iInf fun U => le_iInf fun hA => le_iInf fun hdiam => ?_
    exact iInf₂_le_of_le U ⟨hA, hdiam⟩ le_rfl
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨δ, hδ, hδr⟩ := yui_aux_0001 n E r hr
    refine le_trans ?_ (le_iSup₂ δ hδ)
    refine le_iInf fun U => le_iInf fun hU => ?_
    refine iInf₂_le_of_le U hU.1 ?_
    exact iInf_le_of_le (fun i => (hU.2 i).trans hδr) le_rfl

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)" := by
  intro k A a ha
  let d : ℝ≥0 := ⟨a, ha.le⟩
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal a := by
    exact (ENNReal.ofReal_coe_nnreal (p := d)).symm
  have hn := h_T001 (YuiEucl k) A a ha
  have hz : dimH A < ENNReal.ofReal a → YuiMeasure a A = 0 := by
    intro h
    rw [hn]
    exact hausdorffMeasure_of_dimH_lt (d := d) (by simpa only [hd] using h)
  have ht : ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤ := by
    intro h
    rw [hn]
    exact hausdorffMeasure_of_lt_dimH (d := d) (by simpa only [hd] using h)
  refine ⟨hn, hz, ht, ?_, ?_⟩
  · intro h
    apply le_of_not_gt
    intro hlt
    have hc := ht hlt
    rw [h] at hc
    exact ENNReal.zero_ne_top hc
  · intro h
    apply le_of_not_gt
    intro hlt
    have hc := hz hlt
    rw [h] at hc
    exact ENNReal.top_ne_zero hc

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (X Y : Type) [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (a : ℝ) (U : ℕ → Set X) (V : ℕ → Set Y), 0 ≤ a → (∀ i, (V i).Nonempty → (U i).Nonempty) → (∀ i, Metric.ediam (V i) ≤ Metric.ediam (U i)) → YuiCost a V ≤ YuiCost a U" := by
  intro X Y _ _ a U V ha hne hd
  unfold YuiCost
  apply ENNReal.tsum_le_tsum
  intro i
  apply iSup_le
  intro hv
  exact le_iSup_of_le (hne i hv) (ENNReal.rpow_le_rpow (hd i) ha)

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (X : Type) [PseudoEMetricSpace X] (a δ : ℝ) (A : Set X) (V : ℕ → Set X), YuiCover δ A V → YuiContent a δ A ≤ YuiCost a V" := by
  intro X _ a δ A V hV
  exact iInf_le_of_le V (iInf_le_of_le hV (le_refl (YuiCost a V)))

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (X Y : Type) [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (a δ : ℝ) (A : Set X) (B : Set Y), (∀ U : ℕ → Set Y, YuiCover δ B U → ∃ V : ℕ → Set X, YuiCover δ A V ∧ YuiCost a V ≤ YuiCost a U) → YuiContent a δ A ≤ YuiContent a δ B" := by
  intro X Y _ _ a δ A B h
  unfold YuiContent
  apply le_iInf
  intro U
  apply le_iInf
  intro hU
  obtain ⟨V, hV, hc⟩ := h U hU
  exact (yui_aux_0003 n E h_T001 X a δ A V hV).trans hc

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (X : Type) [PseudoEMetricSpace X] (a : ℝ) (A B : Set X), A ⊆ B → YuiMeasure a A ≤ YuiMeasure a B" := by
  intro X _ a A B hAB
  have hc : ∀ δ : ℝ, YuiContent a δ A ≤ YuiContent a δ B := by
    intro δ
    unfold YuiContent
    apply le_iInf
    intro U
    apply le_iInf
    intro hU
    exact yui_aux_0003 n E h_T001 X a δ A U ⟨hAB.trans hU.1, hU.2⟩
  unfold YuiMeasure
  exact iSup_mono fun δ => iSup_mono fun _ => hc δ

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (k l : ℕ) (A : Set (YuiEucl k)) (B : Set (YuiEucl l)), (∀ a : ℝ, 0 < a → YuiMeasure a A ≤ YuiMeasure a B) → dimH A ≤ dimH B" := by
  intro k l A B hm
  apply le_of_not_gt
  intro h
  obtain ⟨a, _, hBa, haA⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  have ha : 0 < a := ENNReal.ofReal_pos.mp ((bot_le : 0 ≤ dimH B).trans_lt hBa)
  have htop := (yui_aux_0001 n E h_T001 k A a ha).2.2.1 haA
  have hzero := (yui_aux_0001 n E h_T001 l B a ha).2.1 hBa
  have hc := hm a ha
  rw [htop, hzero] at hc
  exact ENNReal.top_ne_zero (le_antisymm hc bot_le)

theorem yui_aux_0007 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → ∀ (a δ : ℝ), 0 < a → 0 < δ → YuiContent a δ (Set.range g) ≤ YuiContent a δ A" := by
  intro k l A g hg a δ ha hδ
  apply yui_aux_0004 n E h_T001 (YuiEucl l) (YuiEucl k) a δ (Set.range g) A
  intro U hU
  let V : ℕ → Set (YuiEucl l) := fun i => g '' ((Subtype.val : A → YuiEucl k) ⁻¹' U i)
  have hd : ∀ i, Metric.ediam (V i) ≤ Metric.ediam (U i) := by
    intro i
    apply Metric.ediam_image_le_iff.mpr
    intro x hx y hy
    rw [hg.edist_eq]
    exact Metric.edist_le_ediam_of_mem hx hy
  have hV : YuiCover δ (Set.range g) V := by
    constructor
    · rintro z ⟨x, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 x.property)
      exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
    · intro i
      exact (hd i).trans (hU.2 i)
  refine ⟨V, hV, ?_⟩
  apply yui_aux_0002 n E h_T001 (YuiEucl k) (YuiEucl l) a U V ha.le
  · intro i hi
    obtain ⟨z, x, hx, _⟩ := hi
    exact ⟨x.val, hx⟩
  · exact hd

theorem yui_aux_0008 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) : yui_aux_type% "∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → ∀ (a δ : ℝ), 0 < a → 0 < δ → YuiContent a δ A ≤ YuiContent a δ (Set.range g)" := by
  intro k l A g hg a δ ha hδ
  apply yui_aux_0004 n E h_T001 (YuiEucl k) (YuiEucl l) a δ A (Set.range g)
  intro U hU
  let V : ℕ → Set (YuiEucl k) := fun i => (Subtype.val : A → YuiEucl k) '' (g ⁻¹' U i)
  have hd : ∀ i, Metric.ediam (V i) ≤ Metric.ediam (U i) := by
    intro i
    apply Metric.ediam_image_le_iff.mpr
    intro x hx y hy
    change edist x y ≤ Metric.ediam (U i)
    rw [← hg.edist_eq]
    exact Metric.edist_le_ediam_of_mem hx hy
  have hV : YuiCover δ A V := by
    constructor
    · intro x hx
      let z : A := ⟨x, hx⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 (Set.mem_range_self z))
      exact Set.mem_iUnion.mpr ⟨i, z, hi, rfl⟩
    · intro i
      exact (hd i).trans (hU.2 i)
  refine ⟨V, hV, ?_⟩
  apply yui_aux_0002 n E h_T001 (YuiEucl l) (YuiEucl k) a U V ha.le
  · intro i hi
    obtain ⟨z, x, hx, _⟩ := hi
    exact ⟨g x, hx⟩
  · exact hd

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) :
    (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A) := by
  refine ⟨yui_aux_0001 n E h_T001, ?_, ?_, ?_⟩
  · intro k A
    exact bot_le
  · intro k A B hAB
    apply yui_aux_0006 n E h_T001 k k A B
    intro a ha
    exact yui_aux_0005 n E h_T001 (YuiEucl k) a A B hAB
  · intro k l A g hg
    have hm : ∀ a : ℝ, 0 < a → YuiMeasure a (Set.range g) = YuiMeasure a A := by
      intro a ha
      unfold YuiMeasure
      apply le_antisymm
      · exact iSup_mono fun δ => iSup_mono fun hδ =>
          yui_aux_0007 n E h_T001 k l A g hg a δ ha hδ
      · exact iSup_mono fun δ => iSup_mono fun hδ =>
          yui_aux_0008 n E h_T001 k l A g hg a δ ha hδ
    apply le_antisymm
    · apply yui_aux_0006 n E h_T001 l k (Set.range g) A
      intro a ha
      exact (hm a ha).le
    · apply yui_aux_0006 n E h_T001 k l A (Set.range g)
      intro a ha
      exact (hm a ha).ge

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, -(L) < x i ∧ x i < L" := by
  obtain ⟨L, hL, hE⟩ := h_H003.isBounded.subset_ball_lt 0 (0 : YuiEucl n)
  refine ⟨L, hL, ?_⟩
  intro x hx i
  have hxL : ‖x‖ < L := by simpa using hE hx
  have hi : |x i| < L := lt_of_le_of_lt (by simpa using PiLp.norm_apply_le x i) hxL
  exact abs_lt.mp hi

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∃ A : ℕ, 0 < A ∧ ∀ x ∈ E, ∀ i : Fin n, -(A : ℝ) < x i ∧ x i < A" := by
  obtain ⟨L, hL, hEL⟩ := @yui_aux_0001 n E h_H001 h_H002 h_H003 h_T002
  obtain ⟨A, hA⟩ := exists_nat_gt L
  refine ⟨A, Nat.cast_pos.mp (hL.trans hA), ?_⟩
  intro x hx i
  exact ⟨lt_trans (neg_lt_neg hA) (hEL x hx i).1, (hEL x hx i).2.trans hA⟩

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "(∀ (r : ℝ) (m : ℕ), 0 ≤ r → r < (m : ℝ) → ⌊r⌋₊ < m) ∧ (∀ x : YuiEucl n, WithLp.toLp 2 (WithLp.ofLp x) = x)" := by
  constructor
  · intro r m hr hm
    exact (Nat.floor_lt hr).mpr hm
  · intro x
    exact WithLp.toLp_ofLp 2 x

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ (A k : ℕ), 0 < k →\n (∀ x ∈ E, ∀ i : Fin n, -(A : ℝ) < x i ∧ x i < A) →\n let U : (Fin n → Fin (2 * A * k)) → Set (YuiEucl n) := fun f =>\n   WithLp.toLp 2 '' (Set.pi Set.univ fun i : Fin n =>\n     Set.Icc (-(A : ℝ) + (f i : ℝ) / k)\n       (-(A : ℝ) + ((f i : ℝ) + 1) / k))\n E ⊆ ⋃ f, U f ∧\n ∀ f, Metric.ediam (U f) ≤\n   (((n : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal : ℝ≥0) : ℝ≥0∞) * (1 / (k : ℝ≥0∞))" := by
  classical
  intro A k hk hE
  dsimp only
  constructor
  · intro x hx
    have kpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    let f : Fin n → Fin (2 * A * k) := fun i =>
      ⟨⌊(x i + (A : ℝ)) * k⌋₊, by
        apply (@yui_aux_0003 n E h_H001 h_H002 h_H003 h_T002).1 _ _
          (mul_nonneg (by linarith [(hE x hx i).1]) kpos.le)
        have hi := (hE x hx i).2
        have hlt : (x i + (A : ℝ)) * k < (2 * A : ℝ) * k :=
          mul_lt_mul_of_pos_right (by linarith) kpos
        exact_mod_cast hlt⟩
    refine Set.mem_iUnion.mpr ⟨f, ?_⟩
    refine ⟨WithLp.ofLp x, ?_, (@yui_aux_0003 n E h_H001 h_H002 h_H003 h_T002).2 x⟩
    simp only [Set.mem_univ_pi, Set.mem_Icc]
    intro i
    have hnonneg : 0 ≤ (x i + (A : ℝ)) * k :=
      mul_nonneg (by linarith [(hE x hx i).1]) kpos.le
    change -(A : ℝ) + (⌊(x i + (A : ℝ)) * k⌋₊ : ℝ) / k ≤ x i ∧
      x i ≤ -(A : ℝ) + ((⌊(x i + (A : ℝ)) * k⌋₊ : ℝ) + 1) / k
    constructor
    · have hfloor := Nat.floor_le hnonneg
      have hd := (div_le_iff₀ kpos).mpr hfloor
      nlinarith
    · have hfloor := (Nat.lt_floor_add_one ((x i + (A : ℝ)) * k)).le
      have hd := (le_div_iff₀ kpos).mpr hfloor
      nlinarith
  · intro f
    have hLip := PiLp.lipschitzWith_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n => ℝ)
    have hdiam := hLip.ediam_image_le
      (Set.pi Set.univ fun i : Fin n =>
        Set.Icc (-(A : ℝ) + (f i : ℝ) / k)
          (-(A : ℝ) + ((f i : ℝ) + 1) / k))
    simp only [Fintype.card_fin] at hdiam
    refine hdiam.trans (mul_le_mul_left' ?_ _)
    apply Metric.ediam_pi_le_of_le
    intro i
    rw [Real.ediam_Icc]
    have heq : -(A : ℝ) + ((f i : ℝ) + 1) / k -
        (-(A : ℝ) + (f i : ℝ) / k) = 1 / k := by ring
    rw [heq, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hk)]
    simp

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ (A k : ℕ) (K : ℝ≥0∞) (s : ℝ), 0 < k → 0 ≤ s →\n (((2 * A * k : ℕ) : ℝ≥0∞) ^ n) * (K * (1 / (k : ℝ≥0∞))) ^ s =\n ((2 * A : ℕ) : ℝ≥0∞) ^ n * K ^ s * (1 / (k : ℝ≥0∞)) ^ (s - n)" := by
  intro A k K s hk hs
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hki0 : (k : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hkit : (k : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [hk0]
  have hp : (k : ℝ≥0∞) ^ n = ((k : ℝ≥0∞)⁻¹) ^ (-(n : ℝ)) := by
    rw [ENNReal.rpow_neg, ENNReal.inv_rpow, ENNReal.rpow_natCast, inv_inv]
  rw [Nat.cast_mul, mul_pow, ENNReal.mul_rpow_of_nonneg _ _ hs, one_div, hp]
  rw [sub_eq_add_neg, ENNReal.rpow_add _ _ hki0 hkit]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "Filter.Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ≥0∞)) Filter.atTop (nhds 0) ∧\n ∀ (u v : ℕ → ℝ≥0∞), (∀ᶠ k in Filter.atTop, u k ≤ v k) →\n   Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop" := by
  constructor
  · simpa only [one_div, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
  · intro u v huv
    exact Filter.liminf_le_liminf huv (by isBoundedDefault) (by isBoundedDefault)

theorem yui_aux_0007 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ s : ℝ, (n : ℝ) < s →\n  MeasureTheory.Measure.hausdorffMeasure s E = 0" := by
  classical
  intro s hs
  have hs0 : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg n) hs
  obtain ⟨A, hA, hE⟩ := @yui_aux_0002 n E h_H001 h_H002 h_H003 h_T002
  let K : ℝ≥0 := (n : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal
  let G : ℕ → Type := fun k => Fin n → Fin (2 * A * (k + 1))
  let U : ∀ k : ℕ, G k → Set (YuiEucl n) := fun k f =>
    WithLp.toLp 2 '' (Set.pi Set.univ fun i : Fin n =>
      Set.Icc (-(A : ℝ) + (f i : ℝ) / (k + 1 : ℕ))
        (-(A : ℝ) + ((f i : ℝ) + 1) / (k + 1 : ℕ)))
  have hgrid (k : ℕ) : E ⊆ ⋃ f, U k f ∧
      ∀ f, Metric.ediam (U k f) ≤ (K : ℝ≥0∞) * (1 / (k + 1 : ℕ)) :=
    @yui_aux_0004 n E h_H001 h_H002 h_H003 h_T002 A (k + 1) (Nat.succ_pos k) hE
  have hinv : Filter.Tendsto (fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ≥0∞)))
      Filter.atTop (nhds 0) :=
    (@yui_aux_0006 n E h_H001 h_H002 h_H003 h_T002).1
  have hr : Filter.Tendsto (fun k : ℕ => (K : ℝ≥0∞) * (1 / ((k + 1 : ℕ) : ℝ≥0∞)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hinv (a := (K : ℝ≥0∞))
      (Or.inr ENNReal.coe_ne_top)
  let c : ℝ≥0∞ := ((2 * A : ℕ) : ℝ≥0∞) ^ n * (K : ℝ≥0∞) ^ s
  have hc : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by finiteness)
      (ENNReal.rpow_ne_top_of_nonneg hs0.le ENNReal.coe_ne_top)
  have hcost : Filter.Tendsto
      (fun k : ℕ => c * (1 / ((k + 1 : ℕ) : ℝ≥0∞)) ^ (s - n))
      Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc (sub_pos.mpr hs)).comp hinv
  apply le_antisymm _ zero_le
  calc
    MeasureTheory.Measure.hausdorffMeasure s E ≤
        Filter.liminf (fun k => ∑ f : G k, Metric.ediam (U k f) ^ s) Filter.atTop :=
      MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s E _ hr U
        (Filter.Eventually.of_forall fun k => (hgrid k).2)
        (Filter.Eventually.of_forall fun k => (hgrid k).1)
    _ ≤ Filter.liminf
        (fun k : ℕ => c * (1 / ((k + 1 : ℕ) : ℝ≥0∞)) ^ (s - n)) Filter.atTop := by
      apply (@yui_aux_0006 n E h_H001 h_H002 h_H003 h_T002).2
      apply Filter.Eventually.of_forall
      intro k
      calc
        (∑ f : G k, Metric.ediam (U k f) ^ s) ≤
            ∑ f : G k, ((K : ℝ≥0∞) * (1 / ((k + 1 : ℕ) : ℝ≥0∞))) ^ s := by
          apply Finset.sum_le_sum
          intro f hf
          exact ENNReal.monotone_rpow_of_nonneg hs0.le ((hgrid k).2 f)
        _ = (((2 * A * (k + 1) : ℕ) : ℝ≥0∞) ^ n) *
            ((K : ℝ≥0∞) * (1 / ((k + 1 : ℕ) : ℝ≥0∞))) ^ s := by
          simp [G, Fintype.card_fun, nsmul_eq_mul]
        _ = c * (1 / ((k + 1 : ℕ) : ℝ≥0∞)) ^ (s - n) :=
          @yui_aux_0005 n E h_H001 h_H002 h_H003 h_T002 A (k + 1)
            (K : ℝ≥0∞) s (Nat.succ_pos k) hs0.le
    _ = 0 := hcost.liminf_eq

theorem yui_aux_0008 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "n = 0 → ∀ s : ℝ, 0 < s → YuiMeasure s E = 0" := by
  intro hn s hs
  subst n
  obtain ⟨x, hx⟩ := h_H002
  have hsing : E = {x} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (Subsingleton.elim y x)
    · intro hy
      exact (Set.mem_singleton_iff.mp hy) ▸ hx
  rw [hsing]
  unfold YuiMeasure
  apply le_antisymm _ zero_le
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  unfold YuiContent
  refine iInf_le_of_le (fun _ : ℕ => ({x} : Set (YuiEucl 0))) (iInf_le_of_le ?_ ?_)
  · constructor
    · exact Set.subset_iUnion (fun _ : ℕ => ({x} : Set (YuiEucl 0))) 0
    · intro i
      simp [Metric.ediam_singleton]
  · simp [YuiCost, ENNReal.zero_rpow_of_pos hs]

theorem yui_aux_0009 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ s : ℝ, (n : ℝ≥0∞) < ENNReal.ofReal s → (n : ℝ) < s ∧ 0 < s" := by
  intro s hs
  have h : ENNReal.ofReal (n : ℝ) < ENNReal.ofReal s := by simpa only [ENNReal.ofReal_natCast] using hs
  exact ENNReal.ofReal_lt_ofReal_iff'.mp h

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) :
    0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ := by
  have hupper : dimH E ≤ (n : ℝ≥0∞) := by
    by_contra! h
    obtain ⟨s, hsnonneg, hns, hsD⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp h
    obtain ⟨hnsReal, hspos⟩ :=
      @yui_aux_0009 n E h_H001 h_H002 h_H003 h_T002 s hns
    have hzero : YuiMeasure s E = 0 := by
      by_cases hn : n = 0
      · exact @yui_aux_0008 n E h_H001 h_H002 h_H003 h_T002 hn s hspos
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        rw [(h_T002.1 n E s hspos).1]
        exact @yui_aux_0007 n E h_H001 h_H002 h_H003 h_T002 s hnsReal
    have hDs : dimH E ≤ ENNReal.ofReal s :=
      (h_T002.1 n E s hspos).2.2.2.1 hzero
    exact (not_lt_of_ge hDs) hsD
  exact ⟨h_T002.2.1 n E, hupper, lt_of_le_of_lt hupper (by simp)⟩

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_H003 : IsCompact E) (h_T004 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) : yui_aux_type% "∀ (δ : ℝ), 0 < δ → ∃ (U : ℕ → Set (YuiEucl n)) (N : ℕ), YuiCover δ E U ∧ (∀ i, N ≤ i → U i = ∅)" := by
  classical
  intro δ hδ
  have hr : 0 < δ / 4 := by positivity
  obtain ⟨t, ht⟩ := h_H003.elim_finite_subcover
    (fun x : E => Metric.ball (x : YuiEucl n) (δ / 4))
    (fun _ => Metric.isOpen_ball)
    (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hr⟩)
  let e : t ≃ Fin t.card := t.equivFin
  let U : ℕ → Set (YuiEucl n) := fun i =>
    if h : i < t.card then Metric.ball ((e.symm ⟨i, h⟩).val : YuiEucl n) (δ / 4)
    else ∅
  have hb (x : YuiEucl n) :
      Metric.ediam (Metric.ball x (δ / 4)) ≤ ENNReal.ofReal (δ / 2) := by
    apply Metric.ediam_le_of_forall_dist_le
    intro y hy z hz
    have hy' : dist y x < δ / 4 := Metric.mem_ball.mp hy
    have hz' : dist x z < δ / 4 := by
      simpa only [dist_comm] using (Metric.mem_ball.mp hz)
    have := dist_triangle y x z
    linarith
  refine ⟨U, t.card, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    let j : Fin t.card := e ⟨y, hy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j.val, ?_⟩
    simpa [U, j] using hxy
  · intro i
    dsimp [U]
    split_ifs with hi
    · exact (hb _).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · simp
  · intro i hi
    simp [U, not_lt.mpr hi]

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (E : Set (YuiEucl n)) (h_H003 : IsCompact E) (h_T004 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤) := by
  classical
  refine ⟨h_T004, ?_⟩
  intro s δ hs hδ
  obtain ⟨U, N, hU, hN⟩ := yui_aux_0001 n E h_H003 h_T004 δ hδ
  have hterm (i : ℕ) :
      (⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s) < ⊤ := by
    refine lt_of_le_of_lt (iSup_le fun _ => le_rfl) ?_
    apply ENNReal.rpow_lt_top_of_nonneg hs.le
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i)
  have hcost : YuiCost s U < ⊤ := by
    unfold YuiCost
    rw [tsum_eq_sum (s := Finset.range N) (fun i hi => ?_)]
    · exact ENNReal.sum_lt_top.mpr (fun i _ => hterm i)
    · have hi' : N ≤ i := Nat.le_of_not_gt (by simpa using hi)
      simp [hN i hi']
  have hcontent : YuiContent s δ E ≤ YuiCost s U := by
    unfold YuiContent
    exact iInf_le_of_le U (iInf_le_of_le hU le_rfl)
  exact lt_of_le_of_lt hcontent hcost

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (k : ℕ) (z w : YuiEucl (k + 1)), dist z w ^ 2 = dist (YuiHead z) (YuiHead w) ^ 2 + |YuiLast z - YuiLast w| ^ 2" := by
  intro k z w
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
  rfl

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k)) := by
  intro k
  have hinv : ∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t := by
    intro x t
    constructor
    · ext i
      simp [YuiHead, YuiSnoc]
    · simp [YuiLast, YuiSnoc]
  have hrec : ∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z := by
    intro z
    ext i
    cases i using Fin.lastCases <;> simp [YuiHead, YuiLast, YuiSnoc]
  refine ⟨hinv, hrec, ?_, ?_, ?_⟩
  · intro x y t u
    have hs := yui_aux_0001 n E k (YuiSnoc x t) (YuiSnoc y u)
    rw [(hinv x t).1, (hinv y u).1, (hinv x t).2, (hinv y u).2] at hs
    rw [← hs, Real.sqrt_sq (dist_nonneg)]
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    have hs := yui_aux_0001 n E k z w
    have ha := sq_nonneg (YuiLast z - YuiLast w)
    have hz : 0 ≤ dist z w := dist_nonneg
    have hh : 0 ≤ dist (YuiHead z) (YuiHead w) := dist_nonneg
    norm_num only [NNReal.coe_one, one_mul]
    nlinarith [sq_abs (YuiLast z - YuiLast w)]
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    have hs := yui_aux_0001 n E k z w
    have hh := sq_nonneg (dist (YuiHead z) (YuiHead w))
    have hz : 0 ≤ dist z w := dist_nonneg
    have ha := abs_nonneg (YuiLast z - YuiLast w)
    norm_num only [NNReal.coe_one, one_mul]
    rw [Real.dist_eq]
    nlinarith

namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "n = 0 → ∃ x : YuiEucl n, E = {x} ∧ Isometry (YuiSnoc x) ∧ YuiCylinder E = (YuiSnoc x) '' YuiI ∧ dimH E = 0" := by
  intro hn
  subst n
  obtain ⟨x, hx⟩ := h_H002
  have hE : E = {x} := by
    ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · intro _; exact Subsingleton.elim _ _
    · rintro rfl; exact hx
  refine ⟨x, hE, ?_, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro t u
    rw [(h_T003 0).2.2.1 x x t u]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  · ext z
    constructor
    · intro hz
      refine ⟨YuiLast z, hz.2, ?_⟩
      have hh : YuiHead z = x := Subsingleton.elim _ _
      simpa only [hh] using (h_T003 0).2.1 z
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(h_T003 0).1 x t |>.1 ▸ hx, (h_T003 0).1 x t |>.2 ▸ ht⟩
  · have h0 : dimH E ≤ 0 := by simpa only [Nat.cast_zero] using h_T005.1.2.1
    exact le_antisymm h0 zero_le

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (N : ℕ), 0 < N → (Set.Icc (0 : ℝ) 1) ⊆ ⋃ j : Fin N, Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro N hN t ht
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  by_cases ht1 : t = 1
  · subst t
    refine Set.mem_iUnion.mpr ⟨⟨N-1, by omega⟩, ?_⟩
    have hc : ((N-1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast (Nat.sub_add_cancel hN)
    constructor
    · apply (div_le_iff₀ hNr).mpr
      nlinarith
    · apply (le_div_iff₀ hNr).mpr
      nlinarith
  · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hfloor : ⌊t * N⌋₊ < N := by
      apply (Nat.floor_lt (mul_nonneg ht.1 hNr.le)).mpr
      nlinarith
    refine Set.mem_iUnion.mpr ⟨⟨⌊t * N⌋₊, hfloor⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ hNr).mpr
      exact Nat.floor_le (mul_nonneg ht.1 hNr.le)
    · apply (le_div_iff₀ hNr).mpr
      exact (Nat.lt_floor_add_one (t*N)).le

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (x : YuiEucl n), Isometry (YuiSnoc x) → ∀ (N : ℕ), 0 < N → ∀ j : Fin N, Metric.ediam ((YuiSnoc x) '' Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) = 1 / (N : ℝ≥0∞)" := by
  intro x hi N hN j
  rw [hi.ediam_image, Real.ediam_Icc]
  have hlen : (((j : ℝ) + 1) / N) - ((j : ℝ) / N) = 1 / (N : ℝ) := by ring
  rw [hlen, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hN)]
  simp

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (a : ℝ), 1 < a → Filter.Tendsto (fun N : ℕ => ((N : ℝ≥0∞)⁻¹) ^ (a-1)) Filter.atTop (nhds 0)" := by
  intro a ha
  have h : Filter.Tendsto (fun N : ℕ => ((N : ℝ≥0∞)⁻¹) ^ (a-1)) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ (a-1))) := (ENNReal.continuous_rpow_const (y := a-1)).tendsto 0 |>.comp ENNReal.tendsto_inv_nat_nhds_zero
  simpa only [ENNReal.zero_rpow_of_pos (sub_pos.mpr ha)] using h

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (a : ℝ), 1 < a → Filter.Tendsto (fun N : ℕ => (N : ℝ≥0∞) * (1 / (N : ℝ≥0∞)) ^ a) Filter.atTop (nhds 0)" := by
  intro a ha
  have hlim := @yui_aux_0004 n E h_H002 h_T002 h_T003 h_T005 a ha
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < N by omega))
  calc
    ((N : ℝ≥0∞)⁻¹) ^ (a-1) = (N : ℝ≥0∞) ^ (1-a) := by
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      congr 1
      ring
    _ = (N : ℝ≥0∞) ^ (1 : ℝ) / (N : ℝ≥0∞) ^ a := ENNReal.rpow_sub 1 a hN0 (ENNReal.natCast_ne_top N)
    _ = (N : ℝ≥0∞) * (1 / (N : ℝ≥0∞)) ^ a := by
      rw [ENNReal.rpow_one, one_div, ENNReal.inv_rpow, div_eq_mul_inv]

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (x : YuiEucl n) (N : ℕ), 0 < N → (YuiSnoc x) '' YuiI ⊆ ⋃ j : Fin N, (YuiSnoc x) '' Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro x N hN z hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hc : Set.Icc (0 : ℝ) 1 ⊆ ⋃ j : Fin N, Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N) := @yui_aux_0002 n E h_H002 h_T002 h_T003 h_T005 N hN
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hc ht)
  exact Set.mem_iUnion.mpr ⟨j, ⟨t, hj, rfl⟩⟩

theorem yui_aux_0007 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (x : YuiEucl n), Isometry (YuiSnoc x) → ∀ (a : ℝ), 1 < a → MeasureTheory.Measure.hausdorffMeasure a ((YuiSnoc x) '' YuiI) = 0" := by
  intro x hi a ha
  classical
  let U : ∀ N : ℕ, Fin N → Set (YuiEucl (n+1)) := fun N j =>
    (YuiSnoc x) '' Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
  have hd : ∀ N : ℕ, 0 < N → ∀ j : Fin N, Metric.ediam (U N j) = 1 / (N : ℝ≥0∞) := by
    intro N hN j
    exact @yui_aux_0003 n E h_H002 h_T002 h_T003 h_T005 x hi N hN j
  have hmesh : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ≥0∞)) Filter.atTop (nhds 0) := by
    simpa only [one_div] using ENNReal.tendsto_inv_nat_nhds_zero
  have hdiam : ∀ᶠ N : ℕ in Filter.atTop, ∀ j : Fin N, Metric.ediam (U N j) ≤ 1 / (N : ℝ≥0∞) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN j
    exact (hd N (by omega) j).le
  have hcover : ∀ᶠ N : ℕ in Filter.atTop, (YuiSnoc x) '' YuiI ⊆ ⋃ j : Fin N, U N j := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact @yui_aux_0006 n E h_H002 h_T002 h_T003 h_T005 x N (by omega)
  have hcost : Filter.Tendsto (fun N : ℕ => ∑ j : Fin N, (Metric.ediam (U N j)) ^ a) Filter.atTop (nhds 0) := by
    apply (@yui_aux_0005 n E h_H002 h_T002 h_T003 h_T005 a ha).congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    simp only [hd N (by omega), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_antisymm ?_ zero_le
  calc
    MeasureTheory.Measure.hausdorffMeasure a ((YuiSnoc x) '' YuiI) ≤
        Filter.liminf (fun N : ℕ => ∑ j : Fin N, (Metric.ediam (U N j)) ^ a) Filter.atTop :=
      MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum a _ _ hmesh U hdiam hcover
    _ = 0 := hcost.liminf_eq

theorem yui_aux_0008 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ ε : ℝ≥0, ENNReal.ofReal (1 + (ε : ℝ)) = 1 + (ε : ℝ≥0∞)" := by
  intro ε
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) ε.coe_nonneg]
  simp

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) :
    n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1 := by
  intro hn
  obtain ⟨x, hE, hi, hF, hD⟩ := @yui_aux_0001 n E h_H002 h_T002 h_T003 h_T005 hn
  rw [hD, zero_add]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
  have ha : 1 < 1 + (ε : ℝ) := by linarith
  have ha0 : 0 < 1 + (ε : ℝ) := by linarith
  have hnative : MeasureTheory.Measure.hausdorffMeasure (1 + (ε : ℝ)) (YuiCylinder E) = 0 := by
    rw [hF]
    exact @yui_aux_0007 n E h_H002 h_T002 h_T003 h_T005 x hi (1 + (ε : ℝ)) ha
  have hyui : YuiMeasure (1 + (ε : ℝ)) (YuiCylinder E) = 0 :=
    (h_T002.1 (n+1) (YuiCylinder E) (1 + (ε : ℝ)) ha0).1.trans hnative
  have hdim : dimH (YuiCylinder E) ≤ ENNReal.ofReal (1 + (ε : ℝ)) :=
    (h_T002.1 (n+1) (YuiCylinder E) (1 + (ε : ℝ)) ha0).2.2.2.1 hyui
  rwa [@yui_aux_0008 n E h_H002 h_T002 h_T003 h_T005 ε] at hdim

namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (a p : ℝ), 0 ≤ a → 0 ≤ p → (ENNReal.ofReal a) ^ p = ENNReal.ofReal (a ^ p)" := by
  intro a p ha hp
  exact ENNReal.ofReal_rpow_of_nonneg ha hp

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (hn : 1 ≤ n) (q r η : ℝ), 0 < q → 0 < r → 0 < η → ∀ x : YuiEucl n, ∃ B : Set (YuiEucl n), x ∈ B ∧ B.Nonempty ∧ 0 < Metric.ediam B ∧ Metric.ediam B ≤ ENNReal.ofReal r ∧ (Metric.ediam B) ^ q < ENNReal.ofReal η" := by
  intro hn q r η hq hr hη x
  letI : NeZero n := ⟨by omega⟩
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let ρ : ℝ := min r (η ^ q⁻¹) / 4
  have ha : 0 < η ^ q⁻¹ := Real.rpow_pos_of_pos hη _
  have hρ : 0 < ρ := div_pos (lt_min hr ha) (by norm_num)
  have hρr : 2 * ρ ≤ r := by dsimp [ρ]; linarith [min_le_left r (η ^ q⁻¹)]
  have hρa : 2 * ρ < η ^ q⁻¹ := by dsimp [ρ]; linarith [min_le_right r (η ^ q⁻¹)]
  have hd : Metric.ediam (Metric.closedBall x ρ) = ENNReal.ofReal (2 * ρ) := by
    calc
      _ = ENNReal.ofReal (Metric.diam (Metric.closedBall x ρ)) :=
        (ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top).symm
      _ = _ := by rw [Metric.diam_closedBall_eq x hρ.le]
  have hp : (2 * ρ) ^ q < η := by
    calc
      _ < (η ^ q⁻¹) ^ q := Real.rpow_lt_rpow (by positivity) hρa hq
      _ = η := Real.rpow_inv_rpow hη.le hq.ne'
  refine ⟨Metric.closedBall x ρ, Metric.mem_closedBall_self hρ.le,
    ⟨x, Metric.mem_closedBall_self hρ.le⟩, ?_, ?_, ?_⟩
  · rw [hd]; exact ENNReal.ofReal_pos.mpr (by positivity)
  · rw [hd]; exact ENNReal.ofReal_le_ofReal hρr
  · rw [hd, yui_aux_0001 n E h_H002 h_T002 h_T005 (2 * ρ) q (by positivity) hq.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hη).mpr hp

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (q r ε : ℝ), dimH E < ENNReal.ofReal q → 0 < r → 0 < ε → 0 < q ∧ ∃ V : ℕ → Set (YuiEucl n), YuiCover r E V ∧ YuiCost q V < ENNReal.ofReal ε" := by
  intro q r ε hD hr hε
  have hq : 0 < q := ENNReal.ofReal_pos.mp ((h_T005.1.1).trans_lt hD)
  have hm : YuiMeasure q E = 0 := (h_T002.1 n E q hq).2.1 hD
  have hc : YuiContent q r E = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ YuiMeasure q E := le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      _ = 0 := hm
  have hi : (⨅ (V : ℕ → Set (YuiEucl n)) (_ : YuiCover r E V), YuiCost q V) <
      ENNReal.ofReal ε := by
    change YuiContent q r E < _
    rw [hc]
    exact ENNReal.ofReal_pos.mpr hε
  rcases (iInf_lt_iff.mp hi) with ⟨V, hV⟩
  rcases (iInf_lt_iff.mp hV) with ⟨hcov, hcost⟩
  exact ⟨hq, V, hcov, hcost⟩

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (hn : 1 ≤ n) (q r ε : ℝ), 0 < q → 0 < r → 0 < ε → ∀ V : ℕ → Set (YuiEucl n), YuiCover r E V → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U ≤ YuiCost q V + ENNReal.ofReal (ε / 2)" := by
  classical
  intro hn q r ε hq hr hε V hV
  let T : Set ℕ := {i | (V i).Nonempty}
  let η : ℕ → ℝ := fun i => (ε / 2) / 2 / 2 ^ i
  have hη : ∀ i, 0 < η i := by intro i; dsimp [η]; positivity
  have hB : ∀ i : T, ∃ B : Set (YuiEucl n),
      i.property.choose ∈ B ∧ B.Nonempty ∧ 0 < Metric.ediam B ∧
        Metric.ediam B ≤ ENNReal.ofReal r ∧ Metric.ediam B ^ q < ENNReal.ofReal (η i) := by
    intro i
    exact yui_aux_0002 n E h_H002 h_T002 h_T005 hn q r (η i) hq hr (hη i) i.property.choose
  choose B hB using hB
  let U : T → Set (YuiEucl n) := fun i => if Metric.ediam (V i) = 0 then B i else V i
  have hsub : ∀ i : T, V i ⊆ U i := by
    intro i x hx
    dsimp [U]
    split_ifs with hd
    · have heq : x = i.property.choose :=
        (Metric.ediam_eq_zero_iff.mp hd) hx i.property.choose_spec
      rw [heq]
      exact (hB i).1
    · exact hx
  have hU : ∀ i : T, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r := by
    intro i
    dsimp [U]
    split_ifs with hd
    · exact ⟨(hB i).2.1, (hB i).2.2.1, (hB i).2.2.2.1⟩
    · exact ⟨i.property, pos_iff_ne_zero.mpr hd, hV.2 i⟩
  refine ⟨T, U, ?_, hU, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp (hV.1 hx) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨⟨i, x, hi⟩, hsub ⟨i, x, hi⟩ hi⟩
  · have hterm : ∀ i : T, (⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ q) ≤
        (⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ q) + ENNReal.ofReal (η i) := by
      intro i
      apply iSup_le
      intro _
      dsimp [U]
      split_ifs with hd
      · exact (hB i).2.2.2.2.le.trans (le_add_left le_rfl)
      · exact le_add_of_le_of_nonneg (le_iSup_of_le i.property le_rfl) zero_le
    have hsum : (∑' i : ℕ, ENNReal.ofReal (η i)) = ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hη i).le)]
      · exact congrArg ENNReal.ofReal (tsum_geometric_two' (ε / 2))
      · exact summable_geometric_two' (ε / 2)
    calc
      YuiCost q U ≤ ∑' i : T,
          ((⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ q) + ENNReal.ofReal (η i)) :=
        ENNReal.tsum_le_tsum hterm
      _ ≤ ∑' i : ℕ,
          ((⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ q) + ENNReal.ofReal (η i)) :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = YuiCost q V + ENNReal.ofReal (ε / 2) := by
        rw [ENNReal.tsum_add, hsum]
        rfl

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) :
    1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε := by
  intro hn q hD r ε hr _hr1 hε
  rcases yui_aux_0003 n E h_H002 h_T002 h_T005 q r (ε / 2) hD hr (half_pos hε) with
    ⟨hq, V, hV, hcost⟩
  rcases yui_aux_0004 n E h_H002 h_T002 h_T005 hn q r ε hq hr hε V hV with
    ⟨T, U, hcover, hU, hbound⟩
  refine ⟨T, U, hcover, hU, hbound.trans_lt ?_⟩
  calc
    YuiCost q V + ENNReal.ofReal (ε / 2) <
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hcost
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring

namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (N : ℕ) (t : ℝ), 0 < N → 0 ≤ t → t < 1 → ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro N t hN ht ht1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnon : 0 ≤ t * (N : ℝ) := mul_nonneg ht hNr.le
  have hprod : t * (N : ℝ) < N := by nlinarith
  have hj : ⌊t * (N : ℝ)⌋₊ < N := (Nat.floor_lt hnon).mpr hprod
  refine ⟨⟨⌊t * (N : ℝ)⌋₊, hj⟩, ?_, ?_⟩
  · exact (div_le_iff₀ hNr).mpr (Nat.floor_le hnon)
  · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one (t * N)).le

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ d : ℝ, 0 < d → d ≤ 1 → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ d ∧ (N : ℝ) * d ≤ 2 ∧ (∀ t ∈ YuiI, ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N))" := by
  intro d hd hd1
  refine ⟨⌈1 / d⌉₊, Nat.ceil_pos.mpr (by positivity), ?_, ?_, ?_⟩
  · have h := Nat.le_ceil (1 / d)
    have hN : (0 : ℝ) < (⌈1 / d⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr (by positivity : 0 < 1 / d)
    apply (div_le_iff₀ hN).mpr
    have := (div_le_iff₀ hd).mp h
    nlinarith
  · have h := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / d)).le
    have hmul := mul_le_mul_of_nonneg_right h hd.le
    rw [add_mul, div_mul_cancel₀ _ hd.ne'] at hmul
    nlinarith
  · intro t ht
    change 0 ≤ t ∧ t ≤ 1 at ht
    let N := ⌈1 / d⌉₊
    change ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    by_cases ht1 : t = 1
    · refine ⟨⟨N - 1, by omega⟩, ?_⟩
      change ((N - 1 : ℕ) : ℝ) / N ≤ t ∧ t ≤ (((N - 1 : ℕ) : ℝ) + 1) / N
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast, ht1]
      constructor
      · apply (div_le_iff₀ hNr).mpr; nlinarith
      · apply (le_div_iff₀ hNr).mpr; nlinarith
    · exact yui_aux_0001 n E h_T003 h_T007 N t hN ht.1 (lt_of_le_of_ne ht.2 ht1)

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (a b d : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ d → a ≤ d → b ≤ d → Real.sqrt (a^2+b^2) ≤ Real.sqrt 2*d" := by
  intro a b d ha hb hd had hbd
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq1 : a^2 ≤ d^2 := by nlinarith
  have hsq2 : b^2 ≤ d^2 := by nlinarith
  nlinarith

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (U : Set (YuiEucl n)) (d a b : ℝ), 0 ≤ d → Metric.ediam U ≤ ENNReal.ofReal d → b - a ≤ d → Metric.ediam {z : YuiEucl (n+1) | YuiHead z ∈ U ∧ YuiLast z ∈ Set.Icc a b} ≤ ENNReal.ofReal (Real.sqrt 2 * d)" := by
  intro U d a b hd hU hab
  apply Metric.ediam_le_of_forall_dist_le
  intro z hz w hw
  have hdist : dist (YuiHead z) (YuiHead w) ≤ d := by
    have h := Metric.edist_le_ediam_of_mem hz.1 hw.1
    rw [edist_dist] at h
    exact (ENNReal.ofReal_le_ofReal_iff hd).mp (h.trans hU)
  have hlast : |YuiLast z - YuiLast w| ≤ d := by
    apply abs_le.mpr
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  have hformula : dist z w = Real.sqrt ((dist (YuiHead z) (YuiHead w))^2 + |YuiLast z - YuiLast w|^2) := by
    conv_lhs => rw [← (h_T003 n).2.1 z, ← (h_T003 n).2.1 w]
    exact (h_T003 n).2.2.1 _ _ _ _
  rw [hformula]
  exact yui_aux_0003 n E h_T003 h_T007 _ _ _ dist_nonneg (abs_nonneg _) hd hdist hlast

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (U : Set (YuiEucl n)) (r : ℝ), 0 < Metric.ediam U → Metric.ediam U ≤ ENNReal.ofReal r → 0 < Metric.diam U ∧ Metric.diam U ≤ r ∧ ENNReal.ofReal (Metric.diam U) = Metric.ediam U" := by
  intro U r hpos hle
  have hfin : Metric.ediam U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hr : 0 ≤ r := le_of_lt (ENNReal.ofReal_pos.mp (lt_of_lt_of_le hpos hle))
  refine ⟨?_, ENNReal.toReal_le_of_le_ofReal hr hle, ?_⟩
  · exact ENNReal.toReal_pos hpos.ne' hfin
  · exact ENNReal.ofReal_toReal hfin

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (d c q : ℝ) (N : ℕ), 0 < d → 0 < c → (N : ℝ) * d ≤ 2 → (N : ℝ≥0∞) * (ENNReal.ofReal (c*d)) ^ (q+1) ≤ ENNReal.ofReal (2*c^(q+1)) * (ENNReal.ofReal d)^q" := by
  intro d c q N hd hc hN
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos hc hd), ENNReal.ofReal_rpow_of_pos hd]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * c^(q+1))]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.mul_rpow hc.le hd.le, Real.rpow_add hd, Real.rpow_one]
  calc
    (N : ℝ) * (c ^ (q+1) * (d^q*d)) = ((N : ℝ)*d) * (c^(q+1)*d^q) := by ring
    _ ≤ 2 * (c^(q+1)*d^q) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

theorem yui_aux_0007 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (q : ℝ) (U : Set (YuiEucl n)) (d : ℝ), 0 < q → 0 < d → d ≤ 1 → ENNReal.ofReal d = Metric.ediam U → ∃ (N : ℕ) (V : Fin N → Set (YuiEucl (n+1))), {z : YuiEucl (n+1) | YuiHead z ∈ U ∧ YuiLast z ∈ YuiI} ⊆ ⋃ j, V j ∧ (∀ j, Metric.ediam (V j) ≤ ENNReal.ofReal (Real.sqrt 2*d)) ∧ YuiCost (q+1) V ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * (Metric.ediam U)^q" := by
  intro q U d hq hd hd1 heq
  obtain ⟨N, hN, hlen, hmult, hcover⟩ := yui_aux_0002 n E h_T003 h_T007 d hd hd1
  let V : Fin N → Set (YuiEucl (n+1)) := fun j => {z | YuiHead z ∈ U ∧ YuiLast z ∈ Set.Icc ((j : ℝ)/N) (((j : ℝ)+1)/N)}
  have hdiam : ∀ j, Metric.ediam (V j) ≤ ENNReal.ofReal (Real.sqrt 2*d) := by
    intro j
    apply yui_aux_0004 n E h_T003 h_T007 U d _ _ hd.le heq.ge
    calc
      ((j : ℝ)+1)/N - (j : ℝ)/N = 1/(N : ℝ) := by ring
      _ ≤ d := hlen
  refine ⟨N, V, ?_, hdiam, ?_⟩
  · intro z hz
    obtain ⟨j, hj⟩ := hcover (YuiLast z) hz.2
    exact Set.mem_iUnion.mpr ⟨j, hz.1, hj⟩
  · calc
      YuiCost (q+1) V ≤ ∑' j : Fin N, (ENNReal.ofReal (Real.sqrt 2*d))^(q+1) := by
        apply ENNReal.tsum_le_tsum
        intro j
        apply iSup_le
        intro _
        exact ENNReal.rpow_le_rpow (hdiam j) (by linarith)
      _ = (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2*d))^(q+1) := by
        simp [tsum_fintype]
      _ ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * (ENNReal.ofReal d)^q :=
        yui_aux_0006 n E h_T003 h_T007 d (Real.sqrt 2) q N hd (by positivity) hmult
      _ = _ := by rw [heq]

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) :
    1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := by
  classical
  intro hn q hq r ε hr hr1 hε
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hq)
  obtain ⟨T, U, hcover, hU, hcost⟩ := h_T007 hn q hq r ε hr hr1 hε
  have hd : ∀ i : T, 0 < Metric.diam (U i) ∧ Metric.diam (U i) ≤ r ∧
      ENNReal.ofReal (Metric.diam (U i)) = Metric.ediam (U i) := by
    intro i
    exact yui_aux_0005 n E h_T003 h_T007 (U i) r (hU i).2.1 (hU i).2.2
  have hi := fun i : T => yui_aux_0007 n E h_T003 h_T007 q (U i) (Metric.diam (U i))
    hqpos (hd i).1 ((hd i).2.1.trans hr1) (hd i).2.2
  choose N V hVcover hVdiam hVcost using hi
  let K := Σ i : T, Fin (N i)
  let F : K → Set (YuiEucl (n+1)) := fun p => V p.1 p.2
  let W : ℕ → Set (YuiEucl (n+1)) := fun j => ⋃ p ∈ Encodable.decode₂ K j, F p
  have hFcover : YuiCylinder E ⊆ ⋃ p : K, F p := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hz.1)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hVcover i ⟨hi, hz.2⟩)
    exact Set.mem_iUnion.mpr ⟨⟨i,j⟩, hj⟩
  have hFdiam : ∀ p : K, Metric.ediam (F p) ≤ ENNReal.ofReal (Real.sqrt 2*r) := by
    intro p
    exact (hVdiam p.1 p.2).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hd p.1).2.1 (Real.sqrt_nonneg 2)))
  have hWcost : YuiCost (q+1) W = YuiCost (q+1) F := by
    exact tsum_iUnion_decode₂
      (fun A : Set (YuiEucl (n+1)) => ⨆ _ : A.Nonempty, (Metric.ediam A)^(q+1))
      (by simp) F
  have hbase : (∑' i : T, (Metric.ediam (U i))^q) = YuiCost q U := by
    unfold YuiCost
    apply tsum_congr
    intro i
    simp [(hU i).1]
  have hFcost : YuiCost (q+1) F ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * YuiCost q U := by
    calc
      YuiCost (q+1) F = ∑' i : T, YuiCost (q+1) (V i) := by
        unfold YuiCost
        exact ENNReal.tsum_sigma' _
      _ ≤ ∑' i : T, ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * (Metric.ediam (U i))^q :=
        ENNReal.tsum_le_tsum hVcost
      _ = _ := by rw [ENNReal.tsum_mul_left, hbase]
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · change YuiCylinder E ⊆ ⋃ (j : ℕ) (p ∈ Encodable.decode₂ K j), F p
    rw [Encodable.iUnion_decode₂]
    exact hFcover
  · intro j
    change Metric.ediam (⋃ p ∈ Encodable.decode₂ K j, F p) ≤ _
    rw [Metric.ediam_iUnion_mem_option]
    exact iSup₂_le fun p _ => hFdiam p
  · rw [hWcost]
    have hcpos : 0 < 2*(Real.sqrt 2)^(q+1) := by positivity
    calc
      YuiCost (q+1) F ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * YuiCost q U := hFcost
      _ < ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * ENNReal.ofReal ε :=
        ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)) ENNReal.ofReal_ne_top hcost
      _ = _ := (ENNReal.ofReal_mul hcpos.le).symm

namespace Local_T009
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "ENNReal.ofReal ((dimH E).toReal) = dimH E ∧ ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1" := by
  have hfin : dimH E ≠ ⊤ := ne_of_lt h_T005.1.2.2
  have hD : ENNReal.ofReal ((dimH E).toReal) = dimH E := ENNReal.ofReal_toReal hfin
  refine ⟨hD, ?_⟩
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1), hD]
  simp

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "∀ (s δ : ℝ) (W : ℕ → Set (YuiEucl (n + 1))), YuiCover δ (YuiCylinder E) W → YuiContent s δ (YuiCylinder E) ≤ YuiCost s W" := by
  intro s δ W hW
  unfold YuiContent
  exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "∀ C : ℝ, Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (C * (1 / ((j : ℝ) + 1)))) Filter.atTop (nhds (0 : ℝ≥0∞))" := by
  intro C
  have hlimR : Filter.Tendsto (fun j : ℕ => C * (1 / ((j : ℝ) + 1))) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := C)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlimR

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ δ : ℝ, 0 < δ → YuiContent (q + 1) δ (YuiCylinder E) = 0" := by
  intro hn q hq δ hδ
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  let r : ℝ := min 1 (δ / Real.sqrt 2)
  have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hs)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrs : Real.sqrt 2 * r ≤ δ := by
    have h : r ≤ δ / Real.sqrt 2 := min_le_right _ _
    have := (le_div_iff₀ hs).1 h
    nlinarith
  let C : ℝ := 2 * (Real.sqrt 2) ^ (q + 1)
  have hC : 0 < C := mul_pos (by norm_num) (Real.rpow_pos_of_pos hs _)
  have hbound : ∀ j : ℕ,
      YuiContent (q + 1) δ (YuiCylinder E) ≤
        ENNReal.ofReal (C * (1 / ((j : ℝ) + 1))) := by
    intro j
    obtain ⟨W, hW, hcost⟩ := h_T008 hn q hq r (1 / ((j : ℝ) + 1)) hr hr1 (by positivity)
    have hcover : YuiCover δ (YuiCylinder E) W := by
      refine ⟨hW.1, fun i => (hW.2 i).trans ?_⟩
      exact ENNReal.ofReal_le_ofReal hrs
    exact (@yui_aux_0002 n E h_T002 h_T005 h_T006 h_T008 (q + 1) δ W hcover).trans hcost.le
  have hlim := @yui_aux_0003 n E h_T002 h_T005 h_T006 h_T008 C
  exact le_antisymm (ge_of_tendsto' hlim hbound) (by positivity)

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → dimH (YuiCylinder E) ≤ ENNReal.ofReal (q + 1)" := by
  intro hn q hq
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (by positivity) hq)
  have hmeasure : YuiMeasure (q + 1) (YuiCylinder E) = 0 := by
    apply le_antisymm _ (by positivity)
    unfold YuiMeasure
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact le_of_eq (@yui_aux_0004 n E h_T002 h_T005 h_T006 h_T008 hn q hq δ hδ)
  exact (h_T002.1 (n + 1) (YuiCylinder E) (q + 1) (by linarith)).2.2.2.1 hmeasure

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "∀ j : ℕ, dimH E < ENNReal.ofReal ((dimH E).toReal + 1 / ((j : ℝ) + 1))" := by
  intro j
  have hD := (@yui_aux_0001 n E h_T002 h_T005 h_T006 h_T008).1
  have hj : 0 < (1 : ℝ) / ((j : ℝ) + 1) := by positivity
  have hqpos : 0 < (dimH E).toReal + 1 / ((j : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hj
  calc
    dimH E = ENNReal.ofReal ((dimH E).toReal) := hD.symm
    _ < ENNReal.ofReal ((dimH E).toReal + 1 / ((j : ℝ) + 1)) :=
      (ENNReal.ofReal_lt_ofReal_iff hqpos).2 (lt_add_of_pos_right _ hj)

end Local_T009
open Local_T009 in
theorem T009 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) :
    dimH (YuiCylinder E) ≤ dimH E + 1 := by
  by_cases hn0 : n = 0
  · exact h_T006 hn0
  have hn : 1 ≤ n := by omega
  have hD1 := (@yui_aux_0001 n E h_T002 h_T005 h_T006 h_T008).2
  have hbound : ∀ j : ℕ, dimH (YuiCylinder E) ≤
      ENNReal.ofReal (((dimH E).toReal + 1 / ((j : ℝ) + 1)) + 1) := by
    intro j
    exact @yui_aux_0005 n E h_T002 h_T005 h_T006 h_T008 hn
      ((dimH E).toReal + 1 / ((j : ℝ) + 1))
      (@yui_aux_0006 n E h_T002 h_T005 h_T006 h_T008 j)
  have hlimR : Filter.Tendsto
      (fun j : ℕ => ((dimH E).toReal + 1 / ((j : ℝ) + 1)) + 1)
      Filter.atTop (nhds ((dimH E).toReal + 1)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := (dimH E).toReal)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).add
        (tendsto_const_nhds (x := (1 : ℝ)))
  have hlim : Filter.Tendsto
      (fun j : ℕ => ENNReal.ofReal (((dimH E).toReal + 1 / ((j : ℝ) + 1)) + 1))
      Filter.atTop (nhds (ENNReal.ofReal ((dimH E).toReal + 1))) := by
    simpa only [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto ((dimH E).toReal + 1)).comp hlimR
  rw [← hD1]
  exact ge_of_tendsto' hlim hbound

namespace Local_T010
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → 0 < η → Metric.ediam B ≤ ENNReal.ofReal ρ → ∃ J : Set ℝ, MeasurableSet J ∧ B ⊆ J ∧ MeasureTheory.volume J ≤ ENNReal.ofReal (ρ + η)" := by
  intro B ρ η hB hρ hη hd
  have hb : Bornology.IsBounded B :=
    Metric.isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd)
  have hspan : sSup B - sInf B ≤ ρ := by
    rw [Real.ediam_eq hb] at hd
    exact (ENNReal.ofReal_le_ofReal_iff hρ).mp hd
  refine ⟨Set.Ioo (sInf B - η / 2) (sSup B + η / 2), measurableSet_Ioo, ?_, ?_⟩
  · intro t ht
    have h := hb.subset_Icc_sInf_sSup ht
    constructor <;> linarith [h.1, h.2]
  · rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    linarith

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (a : ℕ → ℝ) (ε : ℝ), (∀ i, 0 ≤ a i) → 0 < ε → (∑' i : ℕ, ENNReal.ofReal (a i * ((ε / 2 / (2 : ℝ)^i) / (1 + a i)))) ≤ ENNReal.ofReal ε" := by
  intro a ε ha hε
  calc
    (∑' i : ℕ, ENNReal.ofReal (a i * ((ε / 2 / (2 : ℝ)^i) / (1 + a i)))) ≤
        ∑' i : ℕ, ENNReal.ofReal (ε / 2 / (2 : ℝ)^i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      apply ENNReal.ofReal_le_ofReal
      have hpos : 0 < 1 + a i := by linarith [ha i]
      have hw : 0 ≤ ε / 2 / (2 : ℝ)^i := by positivity
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' ε),
        tsum_geometric_two' ε]

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → ∀ (V : ℕ → Set (YuiEucl (n + 1))), YuiCover δ (YuiCylinder E) V → ∀ (J : ℕ → Set ℝ), (∀ i, YuiLast '' V i ⊆ J i) → ∀ t ∈ YuiI, YuiContent s δ E ≤ ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (V i)) ^ s) t" := by
  classical
  intro s δ hs V hV J hJ t ht
  let W : ℕ → Set (YuiEucl n) := fun i => if t ∈ J i then YuiHead '' V i else ∅
  have hd (i : ℕ) : Metric.ediam (YuiHead '' V i) ≤ Metric.ediam (V i) := by
    simpa using (h_T003 n).2.2.2.1.ediam_image_le (V i)
  have hc : YuiCover δ E W := by
    constructor
    · intro x hx
      have hxt : YuiSnoc x t ∈ YuiCylinder E := by
        change YuiHead (YuiSnoc x t) ∈ E ∧ YuiLast (YuiSnoc x t) ∈ YuiI
        rw [(h_T003 n).1 x t |>.1, (h_T003 n).1 x t |>.2]
        exact ⟨hx, ht⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hxt)
      have hj : t ∈ J i := by
        have := hJ i (Set.mem_image_of_mem YuiLast hi)
        simpa only [(h_T003 n).1 x t |>.2] using this
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      dsimp [W]
      rw [if_pos hj]
      exact ⟨YuiSnoc x t, hi, (h_T003 n).1 x t |>.1⟩
    · intro i
      dsimp [W]
      split_ifs with h
      · exact (hd i).trans (hV.2 i)
      · simpa using (zero_le (ENNReal.ofReal δ))
  calc
    YuiContent s δ E ≤ YuiCost s W := iInf_le_of_le W (iInf_le_of_le hc le_rfl)
    _ ≤ ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (V i)) ^ s) t := by
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : t ∈ J i
      · simp only [Set.indicator_of_mem hi]
        apply iSup_le
        intro hne
        dsimp [W]
        rw [if_pos hi]
        exact ENNReal.rpow_le_rpow (hd i) hs.le
      · simp [W, hi]

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ t ∈ YuiI, c ≤ ∑' i, (J i).indicator (fun _ : ℝ => a i) t) → c ≤ ∑' i, a i * MeasureTheory.volume (J i)" := by
  intro c a J hJ hc
  have hI : MeasurableSet YuiI := measurableSet_Icc
  have hm (i : ℕ) : Measurable ((J i).indicator (fun _ : ℝ => a i)) :=
    measurable_const.indicator (hJ i)
  calc
    c = ∫⁻ _ : ℝ in YuiI, c := by
      simp [MeasureTheory.lintegral_const, YuiI, Real.volume_Icc]
    _ ≤ ∫⁻ t : ℝ in YuiI, ∑' i, (J i).indicator (fun _ : ℝ => a i) t := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hI] with t ht
      exact hc t ht
    _ = ∑' i, ∫⁻ t : ℝ in YuiI, (J i).indicator (fun _ : ℝ => a i) t :=
      MeasureTheory.lintegral_tsum (fun i => (hm i).aemeasurable)
    _ ≤ ∑' i, a i * MeasureTheory.volume (J i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [MeasureTheory.setLIntegral_indicator (hJ i), MeasureTheory.setLIntegral_const]
      exact mul_le_mul_left' (MeasureTheory.measure_mono Set.inter_subset_left) _

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (p : ℝ), 0 < p → ∀ V : ℕ → Set (YuiEucl (n + 1)), (∑' i, (Metric.ediam (V i)) ^ p) = YuiCost p V" := by
  classical
  intro p hp V
  apply tsum_congr
  intro i
  by_cases hi : (V i).Nonempty
  · simp [hi]
  · have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp [he, ENNReal.zero_rpow_of_pos hp]

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (C : ℝ≥0∞) (a : ℕ → ℝ) (ε : ℝ), (∀ i, 0 ≤ a i) → 0 < ε → C + (∑' i : ℕ, ENNReal.ofReal (a i * ((ε / 2 / (2 : ℝ)^i) / (1 + a i)))) ≤ C + ENNReal.ofReal ε" := by
  intro C a ε ha hε
  exact add_le_add (le_refl C) (yui_aux_0002 n E h_T003 h_T005 a ε ha hε)

theorem yui_aux_0007 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (P : ℕ → Prop) (f : ℕ → ℝ≥0∞), (∀ i, ¬ P i → f i = 0) → (∑' i, f i) = ∑' i : {i // P i}, f i" := by
  classical
  intro P f hf
  symm
  exact tsum_subtype_eq_of_support_subset (by
    intro i hi
    by_contra h
    exact hi (hf i h))

theorem yui_aux_0008 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (P : ℕ → Prop) (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ i, ¬ P i → a i = 0) → (∀ t ∈ YuiI, c ≤ ∑' i, (J i).indicator (fun _ : ℝ => a i) t) → c ≤ ∑' i, a i * MeasureTheory.volume (J i)" := by
  classical
  intro P c a J hJ hzero hc
  have hI : MeasurableSet YuiI := measurableSet_Icc
  have hsums (t : ℝ) : (∑' i, (J i).indicator (fun _ : ℝ => a i) t) =
      ∑' i : {i // P i}, (J i).indicator (fun _ : ℝ => a i) t := by
    apply yui_aux_0007 n E h_T003 h_T005 P
    intro i hi
    simp [hzero i hi]
  have hsumint : (∑' i, a i * MeasureTheory.volume (J i)) =
      ∑' i : {i // P i}, a i * MeasureTheory.volume (J i) := by
    apply yui_aux_0007 n E h_T003 h_T005 P
    intro i hi
    simp [hzero i hi]
  rw [hsumint]
  calc
    c = ∫⁻ _ : ℝ in YuiI, c := by
      simp [MeasureTheory.lintegral_const, YuiI, Real.volume_Icc]
    _ ≤ ∫⁻ t : ℝ in YuiI, ∑' i : {i // P i}, (J i).indicator (fun _ : ℝ => a i) t := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hI] with t ht
      rw [← hsums t]
      exact hc t ht
    _ = ∑' i : {i // P i}, ∫⁻ t : ℝ in YuiI, (J i).indicator (fun _ : ℝ => a i) t :=
      MeasureTheory.lintegral_tsum (fun i =>
        (measurable_const.indicator (hJ i)).aemeasurable)
    _ ≤ ∑' i : {i // P i}, a i * MeasureTheory.volume (J i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [MeasureTheory.setLIntegral_indicator (hJ i), MeasureTheory.setLIntegral_const]
      exact mul_le_mul_left' (MeasureTheory.measure_mono Set.inter_subset_left) _

end Local_T010
open Local_T010 in
theorem T010 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) :
    ∀ s δ : ℝ, 0 < s → 0 < δ → ∀ V : ℕ → Set (YuiEucl (n + 1)), YuiCover δ (YuiCylinder E) V → ∀ ε : ℝ, 0 < ε → YuiContent s δ E ≤ YuiCost (s + 1) V + ENNReal.ofReal ε := by
  classical
  intro s δ hs hδ V hV ε hε
  have hcfinite : YuiContent s δ E < ⊤ := h_T005.2 s δ hs hδ
  have hfinite (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  let ρ : ℕ → ℝ := fun i => (Metric.ediam (V i)).toReal
  have hρ (i : ℕ) : 0 ≤ ρ i := ENNReal.toReal_nonneg
  have hr (i : ℕ) : ENNReal.ofReal (ρ i) = Metric.ediam (V i) :=
    ENNReal.ofReal_toReal (hfinite i)
  let a : ℕ → ℝ := fun i => (ρ i) ^ s
  have ha (i : ℕ) : 0 ≤ a i := Real.rpow_nonneg (hρ i) s
  have hpow (i : ℕ) : ENNReal.ofReal (a i) = (Metric.ediam (V i)) ^ s := by
    dsimp [a]
    rw [← ENNReal.ofReal_rpow_of_nonneg (hρ i) hs.le, hr i]
  let η : ℕ → ℝ := fun i => (ε / 2 / (2 : ℝ)^i) / (1 + a i)
  have hη (i : ℕ) : 0 < η i := by
    dsimp [η]
    have : 0 < 1 + a i := by linarith [ha i]
    positivity
  have hex (i : ℕ) : ∃ J : Set ℝ, MeasurableSet J ∧
      YuiLast '' V i ⊆ J ∧ MeasureTheory.volume J ≤ ENNReal.ofReal (ρ i + η i) := by
    by_cases hi : (V i).Nonempty
    · apply yui_aux_0001 n E h_T003 h_T005 (YuiLast '' V i) (ρ i) (η i)
        (hi.image YuiLast) (hρ i) (hη i)
      rw [hr i]
      simpa using (h_T003 n).2.2.2.2.ediam_image_le (V i)
    · have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      exact ⟨∅, MeasurableSet.empty, by simp [he], by simp⟩
  choose J hJm hJsub hJvol using hex
  have hslice := yui_aux_0003 n E h_T003 h_T005 s δ hs V hV J hJsub
  have hzero (i : ℕ) (hi : ¬ (V i).Nonempty) : (Metric.ediam (V i)) ^ s = 0 := by
    have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp [he, ENNReal.zero_rpow_of_pos hs]
  have hint := yui_aux_0008 n E h_T003 h_T005 (fun i => (V i).Nonempty)
    (YuiContent s δ E) (fun i => (Metric.ediam (V i)) ^ s) J hJm hzero hslice
  have hterm (i : ℕ) :
      (Metric.ediam (V i)) ^ s * MeasureTheory.volume (J i) ≤
      (Metric.ediam (V i)) ^ (s + 1) + ENNReal.ofReal (a i * η i) := by
    calc
      (Metric.ediam (V i)) ^ s * MeasureTheory.volume (J i) ≤
          (Metric.ediam (V i)) ^ s * ENNReal.ofReal (ρ i + η i) :=
        mul_le_mul_left' (hJvol i) _
      _ = (Metric.ediam (V i)) ^ (s + 1) + ENNReal.ofReal (a i * η i) := by
        rw [ENNReal.ofReal_add (hρ i) (hη i).le, mul_add, hr i,
          ENNReal.rpow_add_of_nonneg s 1 hs.le zero_le_one, ENNReal.rpow_one,
          ENNReal.ofReal_mul (ha i), hpow i]
  calc
    YuiContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * MeasureTheory.volume (J i) := hint
    _ ≤ ∑' i, ((Metric.ediam (V i)) ^ (s + 1) + ENNReal.ofReal (a i * η i)) :=
      ENNReal.tsum_le_tsum hterm
    _ = (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ∑' i, ENNReal.ofReal (a i * η i) :=
      ENNReal.tsum_add
    _ ≤ YuiCost (s + 1) V + ENNReal.ofReal ε := by
      rw [yui_aux_0005 n E h_T003 h_T005 (s + 1) (by linarith) V]
      exact yui_aux_0006 n E h_T003 h_T005 (YuiCost (s + 1) V) a ε ha hε

namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T010 : ∀ s δ : ℝ, 0 < s → 0 < δ → ∀ V : ℕ → Set (YuiEucl (n + 1)), YuiCover δ (YuiCylinder E) V → ∀ ε : ℝ, 0 < ε → YuiContent s δ E ≤ YuiCost (s + 1) V + ENNReal.ofReal ε) : yui_aux_type% "∀ (a b : ℝ≥0∞), (∀ ε : ℝ, 0 < ε → a ≤ b + ENNReal.ofReal ε) → a ≤ b" := by
  intro a b h
  apply ENNReal.le_of_forall_pos_le_add (a := a) (b := b)
  intro ε hε hb
  have hεreal : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hcoe : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  simpa only [hcoe] using h (ε : ℝ) hεreal

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (E : Set (YuiEucl n)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T010 : ∀ s δ : ℝ, 0 < s → 0 < δ → ∀ V : ℕ → Set (YuiEucl (n + 1)), YuiCover δ (YuiCylinder E) V → ∀ ε : ℝ, 0 < ε → YuiContent s δ E ≤ YuiCost (s + 1) V + ENNReal.ofReal ε) :
    ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E) := by
  intro s δ hs hδ
  unfold YuiContent
  refine le_iInf fun V => le_iInf fun hV => ?_
  exact yui_aux_0001 n E h_T005 h_T010 (YuiContent s δ E) (YuiCost (s + 1) V)
    (fun ε hε => h_T010 s δ hs hδ V hV ε hε)

namespace Local_T012
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) : yui_aux_type% "∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E → ENNReal.ofReal (s + 1) ≤ dimH (YuiCylinder E)" := by
  intro s hs hsD
  have hE : YuiMeasure s E = ⊤ := (h_T002.1 n E s hs).2.2.1 hsD
  have hle : YuiMeasure s E ≤ YuiMeasure (s + 1) (YuiCylinder E) := by
    unfold YuiMeasure
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (h_T011 s δ hs hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hF : YuiMeasure (s + 1) (YuiCylinder E) = ⊤ := top_unique (hE ▸ hle)
  exact (h_T002.1 (n + 1) (YuiCylinder E) (s + 1) (by linarith)).2.2.2.2 hF

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < (dimH E).toReal → ENNReal.ofReal s < dimH E" := by
  intro s hs hsD
  have hd : 0 < (dimH E).toReal := hs.trans hsD
  have hc : ENNReal.ofReal s < ENNReal.ofReal (dimH E).toReal :=
    ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hsD, hd⟩
  exact hc.trans_eq (ENNReal.ofReal_toReal h_T005.1.2.2.ne)

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) : yui_aux_type% "0 < dimH E → (∀ j : ℕ, 2 ≤ j → 0 < (dimH E).toReal * (1 - 1 / (j : ℝ)) ∧ ENNReal.ofReal ((dimH E).toReal * (1 - 1 / (j : ℝ))) < dimH E) ∧ Filter.Tendsto (fun j : ℕ => ENNReal.ofReal ((dimH E).toReal * (1 - 1 / (j : ℝ)) + 1)) Filter.atTop (nhds (dimH E + 1))" := by
  intro hD
  have hfin : dimH E ≠ ⊤ := h_T005.1.2.2.ne
  have hd : 0 < (dimH E).toReal := ENNReal.toReal_pos hD.ne' hfin
  have hconv : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add hd.le (by norm_num), ENNReal.ofReal_toReal hfin, ENNReal.ofReal_one]
  constructor
  · intro j hj
    have hj' : (1 : ℝ) < (j : ℝ) := by exact_mod_cast (show 1 < j by omega)
    have hjpos : (0 : ℝ) < j := by linarith
    have hi : 0 < 1 / (j : ℝ) := div_pos (by norm_num) hjpos
    have hi' : 1 / (j : ℝ) < 1 := (div_lt_iff₀ hjpos).2 (by linarith)
    have hs : 0 < (dimH E).toReal * (1 - 1 / (j : ℝ)) := mul_pos hd (by linarith)
    refine ⟨hs, @yui_aux_0002 n E h_T002 h_T005 h_T011 _ hs ?_⟩
    nlinarith [mul_pos hd hi]
  · have ht : Filter.Tendsto (fun j : ℕ => (dimH E).toReal * (1 - 1 / (j : ℝ)) + 1) Filter.atTop (nhds ((dimH E).toReal + 1)) := by
      convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))).add tendsto_const_nhds using 1 <;> simp
    rw [← hconv]
    exact ENNReal.tendsto_ofReal ht

end Local_T012
open Local_T012 in
theorem T012 (n : ℕ) (E : Set (YuiEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (YuiCylinder E) := by
  intro hD
  obtain ⟨hseq, hlim⟩ := @yui_aux_0003 n E h_T002 h_T005 h_T011 hD
  apply le_of_tendsto hlim
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro j hj
  obtain ⟨hs, hsD⟩ := hseq j hj
  exact @yui_aux_0001 n E h_T002 h_T005 h_T011
    ((dimH E).toReal * (1 - 1 / (j : ℝ))) hs hsD

namespace Local_T013
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (N : ℕ) (d : ℝ), 0 < N → 0 ≤ d → ∀ x ∈ Set.Icc (0 : ℝ) ((N : ℝ) * d), ∃ i : ℕ, i < N ∧ x ∈ Set.Icc ((i : ℝ) * d) (((i : ℝ) + 1) * d)" := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    intro d hN hd x hx
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, by simpa using hx⟩
    · by_cases hle : x ≤ (N : ℝ) * d
      · obtain ⟨i, hi, hxi⟩ := ih d (Nat.pos_of_ne_zero hzero) hd x ⟨hx.1, hle⟩
        exact ⟨i, by omega, hxi⟩
      · refine ⟨N, by omega, le_of_lt (lt_of_not_ge hle), ?_⟩
        simpa only [Nat.cast_succ] using hx.2

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (a : ℝ) (N : ℕ), 1 < a → 0 < N → (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a = ENNReal.ofReal ((N : ℝ) ^ (1 - a))" := by
  intro a N ha hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hconv : (ENNReal.ofReal (1 / (N : ℝ))) ^ a = ENNReal.ofReal ((1 / (N : ℝ)) ^ a) :=
    ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNp)
  rw [hconv, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNp.le]
  congr 1
  rw [Real.rpow_sub hNp, Real.rpow_one, one_div, Real.inv_rpow hNp.le]
  rfl

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (a : ℝ) (N : ℕ), 1 < a → 0 < N → ∃ U : ℕ → Set ℝ, YuiCover (1 / (N : ℝ)) YuiI U ∧ YuiCost a U ≤ ENNReal.ofReal ((N : ℝ) ^ (1 - a))" := by
  classical
  intro a N ha hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let U : ℕ → Set ℝ := fun i => if i < N then Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) else ∅
  have hdiam (i : ℕ) (hi : i < N) : Metric.ediam (U i) = ENNReal.ofReal (1 / (N : ℝ)) := by
    simp only [U, if_pos hi, Real.ediam_Icc]
    congr 1
    ring
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) ((N : ℝ) * (1 / (N : ℝ))) := by
      simpa [YuiI, hNp.ne'] using hx
    obtain ⟨i, hi, hxi⟩ := (@yui_aux_0001 n E) N (1 / (N : ℝ)) hN (by positivity) x hx'
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    simpa [U, hi, div_eq_mul_inv] using hxi
  · intro i
    by_cases hi : i < N
    · exact le_of_eq (hdiam i hi)
    · simp [U, hi]
  · calc
      YuiCost a U = ∑ i ∈ Finset.range N, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ a := by
        unfold YuiCost
        apply tsum_eq_sum
        intro i hi
        have hi' : ¬ i < N := by simpa using hi
        simp [U, hi']
      _ ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by
        apply Finset.sum_le_sum
        intro i hi
        apply iSup_le
        intro hne
        exact le_of_eq (congrArg (fun d : ℝ≥0∞ => d ^ a) (hdiam i (Finset.mem_range.mp hi)))
      _ = (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by simp [nsmul_eq_mul]
      _ = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := (@yui_aux_0002 n E) a N ha hN

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ a : ℝ, 1 < a → Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds (0 : ℝ)) ∧ Filter.Tendsto (fun N : ℕ => ENNReal.ofReal ((N : ℝ) ^ (1 - a))) Filter.atTop (nhds (0 : ℝ≥0∞))" := by
  intro a ha
  have hmesh : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_neg_one, one_div] using
      (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)
  have hpow : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (show 0 < a - 1 by linarith)).comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)
  refine ⟨hmesh, ?_⟩
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hpow

end Local_T013
open Local_T013 in
theorem T013 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0 := by
  intro a ha
  obtain ⟨hmesh, hcost⟩ := (@yui_aux_0004 n E) a ha
  apply le_antisymm _ bot_le
  unfold YuiMeasure
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  apply ge_of_tendsto hcost
  filter_upwards [(tendsto_order.mp hmesh).2 δ hδ, Filter.eventually_gt_atTop 0] with N hmeshN hN
  obtain ⟨U, hU, hc⟩ := (@yui_aux_0003 n E) a N ha hN
  have hcover : YuiCover δ YuiI U :=
    ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hmeshN.le)⟩
  calc
    YuiContent a δ YuiI ≤ YuiCost a U := by
      unfold YuiContent
      exact iInf_le_of_le U (iInf_le_of_le hcover le_rfl)
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := hc

namespace Local_T014
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (S : Set ℝ), Bornology.IsBounded S → S.Nonempty → ∀ (ε : ℝ), 0 < ε → ∀ i : ℕ, S ⊆ Set.Ioo (sInf S - ε / 4 / 2 ^ i) (sSup S + ε / 4 / 2 ^ i) ∧ MeasureTheory.volume (Set.Ioo (sInf S - ε / 4 / 2 ^ i) (sSup S + ε / 4 / 2 ^ i)) = Metric.ediam S + ENNReal.ofReal (ε / 2 / 2 ^ i)" := by
  intro S hb hn ε hε i
  have hh : 0 < ε / 4 / (2 : ℝ) ^ i := by positivity
  have hend : 0 ≤ sSup S - sInf S := sub_nonneg.mpr (Real.sInf_le_sSup S hb.bddBelow hb.bddAbove)
  constructor
  · intro x hx
    have hx' := hb.subset_Icc_sInf_sSup hx
    constructor <;> linarith [hx'.1, hx'.2]
  · rw [Real.volume_Ioo, Real.ediam_eq hb, ← ENNReal.ofReal_add hend (by positivity : 0 ≤ ε / 2 / (2 : ℝ) ^ i)]
    congr 1
    ring

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (ε : ℝ), 0 ≤ ε → (∑' i : ℕ, ENNReal.ofReal (ε / 2 / (2 : ℝ) ^ i)) = ENNReal.ofReal ε" := by
  intro ε hε
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i : ℕ => by positivity) (summable_geometric_two' ε), tsum_geometric_two' ε]

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ V : ℕ → Set ℝ, (∑' i : {i : ℕ // (V i).Nonempty}, Metric.ediam (V i.val)) = ∑' i : ℕ, Metric.ediam (V i)" := by
  classical
  intro V
  calc
    (∑' i : {i : ℕ // (V i).Nonempty}, Metric.ediam (V i.val)) = ∑' i : ℕ, ({i : ℕ | (V i).Nonempty}).indicator (fun i => Metric.ediam (V i)) i := tsum_subtype {i : ℕ | (V i).Nonempty} (fun i => Metric.ediam (V i))
    _ = _ := by
      apply tsum_congr
      intro i
      by_cases hi : (V i).Nonempty
      · simp [hi]
      · have hz : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
        simp [hi, hz]

end Local_T014
open Local_T014 in
theorem T014 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) := by
  classical
  intro δ hδ V hV
  have hb : ∀ i, Bornology.IsBounded (V i) := by
    intro i
    apply Metric.isBounded_iff_ediam_ne_top.mpr
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  by_cases hinf : (∑' i, Metric.ediam (V i)) = ⊤
  · rw [hinf]
    exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
    let T := {i : ℕ // (V i).Nonempty}
    let J : T → Set ℝ := fun i => Set.Ioo (sInf (V i.val) - (ε : ℝ) / 4 / 2 ^ i.val) (sSup (V i.val) + (ε : ℝ) / 4 / 2 ^ i.val)
    have hJ : ∀ i : T, V i.val ⊆ J i ∧ MeasureTheory.volume (J i) = Metric.ediam (V i.val) + ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val) := by
      intro i
      exact (@yui_aux_0001 n E) (V i.val) (hb i.val) i.property (ε : ℝ) hεr i.val
    have hcov : YuiI ⊆ ⋃ i : T, J i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hx)
      exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, (hJ ⟨i, ⟨x, hi⟩⟩).1 hi⟩
    have herr : (∑' i : T, ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val)) ≤ ENNReal.ofReal (ε : ℝ) := by
      calc
        _ ≤ ∑' i : ℕ, ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i) := ENNReal.tsum_comp_le_tsum_of_injective (f := fun i : T => i.val) Subtype.val_injective _
        _ = _ := (@yui_aux_0002 n E) (ε : ℝ) hεr.le
    calc
      (1 : ℝ≥0∞) = MeasureTheory.volume YuiI := by simp [YuiI, Real.volume_Icc]
      _ ≤ MeasureTheory.volume (⋃ i : T, J i) := MeasureTheory.measure_mono hcov
      _ ≤ ∑' i : T, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
      _ = ∑' i : T, (Metric.ediam (V i.val) + ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val)) := tsum_congr (fun i => (hJ i).2)
      _ = (∑' i : T, Metric.ediam (V i.val)) + ∑' i : T, ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val) := ENNReal.tsum_add
      _ ≤ (∑' i : ℕ, Metric.ediam (V i)) + ENNReal.ofReal (ε : ℝ) := add_le_add (le_of_eq ((@yui_aux_0003 n E) V)) herr
      _ = (∑' i : ℕ, Metric.ediam (V i)) + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]

namespace Local_T015
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T014 : ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)) : yui_aux_type% "∀ (a b : ℝ≥0∞), a ≤ b → b⁻¹ ≤ a⁻¹" := by
  intro a b h
  exact ENNReal.inv_le_inv' h

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T014 : ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)) : yui_aux_type% "∀ (s δ : ℝ) (ρ : ℝ≥0∞), 0 < s → s < 1 → 0 < δ → ρ ≤ ENNReal.ofReal δ → (ENNReal.ofReal δ) ^ (s - 1) * ρ ≤ ρ ^ s" := by
  intro s δ ρ hs hs1 hδ hρ
  by_cases hzero : ρ = 0
  · simp [hzero, ENNReal.zero_rpow_of_pos hs]
  have hfinite : ρ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hρ
  have hneg : (ENNReal.ofReal δ) ^ (s - 1) ≤ ρ ^ (s - 1) := by
    have hp : ρ ^ (1 - s) ≤ (ENNReal.ofReal δ) ^ (1 - s) :=
      ENNReal.rpow_le_rpow hρ (by linarith)
    have hi := (@yui_aux_0001 n E h_T014) _ _ hp
    simpa only [← ENNReal.rpow_neg, neg_sub] using hi
  calc
    (ENNReal.ofReal δ) ^ (s - 1) * ρ ≤ ρ ^ (s - 1) * ρ := mul_le_mul_right' hneg ρ
    _ = ρ ^ s := by
      have heq : s - 1 + 1 = s := by ring
      simpa only [ENNReal.rpow_one, heq] using (ENNReal.rpow_add (s - 1) 1 hzero hfinite).symm

end Local_T015
open Local_T015 in
theorem T015 (n : ℕ) (E : Set (YuiEucl n)) (h_T014 : ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)) :
    ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → (ENNReal.ofReal δ) ^ (s - 1) ≤ YuiContent s δ YuiI := by
  intro s δ hs hs1 hδ
  unfold YuiContent
  refine le_iInf fun V => le_iInf fun hV => ?_
  calc
    (ENNReal.ofReal δ) ^ (s - 1) = (ENNReal.ofReal δ) ^ (s - 1) * 1 := (mul_one _).symm
    _ ≤ (ENNReal.ofReal δ) ^ (s - 1) * ∑' i, Metric.ediam (V i) :=
      mul_le_mul_left' (h_T014 δ hδ V hV) _
    _ = ∑' i, (ENNReal.ofReal δ) ^ (s - 1) * Metric.ediam (V i) := ENNReal.tsum_mul_left.symm
    _ ≤ YuiCost s V := by
      unfold YuiCost
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : (V i).Nonempty
      · exact ((@yui_aux_0002 n E h_T014) s δ (Metric.ediam (V i)) hs hs1 hδ (hV.2 i)).trans
          (le_iSup (fun _ : (V i).Nonempty => Metric.ediam (V i) ^ s) hi)
      · have hempty : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
        simp [hempty]

namespace Local_T016
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T013 : ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0) (h_T015 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → (ENNReal.ofReal δ) ^ (s - 1) ≤ YuiContent s δ YuiI) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → YuiMeasure s YuiI = ⊤" := by
  intro s hs hs1
  have h0 : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have ht : Filter.Tendsto (fun δ : ℝ => (ENNReal.ofReal δ) ^ (s - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((0 : ℝ≥0∞) ^ (s - 1))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h0
  rw [ENNReal.zero_rpow_of_neg (sub_neg.mpr hs1)] at ht
  apply top_unique
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (h_T015 s δ hs hs1 hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T013 : ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0) (h_T015 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → (ENNReal.ofReal δ) ^ (s - 1) ≤ YuiContent s δ YuiI) : yui_aux_type% "∀ a : ℝ≥0, 1 < (a : ℝ) → dimH YuiI ≤ (a : ℝ≥0∞)" := by
  intro a ha
  have ha0 : 0 < (a : ℝ) := lt_trans zero_lt_one ha
  have hm : MeasureTheory.Measure.hausdorffMeasure (a : ℝ) YuiI = 0 :=
    (h_T001 ℝ YuiI (a : ℝ) ha0).symm.trans (h_T013 (a : ℝ) ha)
  exact dimH_le_of_hausdorffMeasure_ne_top (d := a) (by simp [hm])

end Local_T016
open Local_T016 in
theorem T016 (n : ℕ) (E : Set (YuiEucl n)) (h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T013 : ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0) (h_T015 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → (ENNReal.ofReal δ) ^ (s - 1) ≤ YuiContent s δ YuiI) :
    dimH YuiI = 1 := by
  apply le_antisymm
  · by_contra h
    have hd : (1 : ℝ≥0∞) < dimH YuiI := lt_of_not_ge h
    obtain ⟨a, ha1, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hd
    have ha : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
    exact had.not_ge (@yui_aux_0002 n E h_T001 h_T002 h_T013 h_T015 a ha)
  · refine ENNReal.le_of_forall_pos_nnreal_lt fun s hs hs1 => ?_
    have hs0 : 0 < (s : ℝ) := by exact_mod_cast hs
    have hsreal1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    have hm : MeasureTheory.Measure.hausdorffMeasure (s : ℝ) YuiI = ⊤ :=
      (h_T001 ℝ YuiI (s : ℝ) hs0).symm.trans
        (@yui_aux_0001 n E h_T001 h_T002 h_T013 h_T015 (s : ℝ) hs0 hsreal1)
    exact le_dimH_of_hausdorffMeasure_eq_top (d := s) hm

theorem T017 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T016 : dimH YuiI = 1) :
    dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YuiCylinder E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hD
  obtain ⟨x0, hx0⟩ := h_H002
  let g : ℝ → YuiEucl (n + 1) := fun t => YuiSnoc x0 t
  have hg : Isometry g := by
    apply isometry_iff_dist_eq.mpr
    intro t u
    change dist (YuiSnoc x0 t) (YuiSnoc x0 u) = dist t u
    rw [(h_T003 n).2.2.1 x0 x0 t u]
    simp [Real.sqrt_sq_eq_abs, Real.dist_eq]
  have hsub : g '' YuiI ⊆ YuiCylinder E := by
    rintro z ⟨t, ht, rfl⟩
    change YuiHead (YuiSnoc x0 t) ∈ E ∧ YuiLast (YuiSnoc x0 t) ∈ YuiI
    rw [(h_T003 n).1 x0 t |>.1, (h_T003 n).1 x0 t |>.2]
    exact ⟨hx0, ht⟩
  constructor
  · calc
      (1 : ℝ≥0∞) = dimH YuiI := h_T016.symm
      _ = dimH (g '' YuiI) := (hg.dimH_image YuiI).symm
      _ ≤ dimH (YuiCylinder E) := dimH_mono hsub
  · simp [hD]

theorem T018 (n : ℕ) (E : Set (YuiEucl n)) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) (h_T009 : dimH (YuiCylinder E) ≤ dimH E + 1) (h_T012 : 0 < dimH E → dimH E + 1 ≤ dimH (YuiCylinder E)) (h_T017 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YuiCylinder E) ∧ (1 : ℝ≥0∞) = dimH E + 1) :
    dimH (YuiCylinder E) = dimH E + 1 := by
  apply le_antisymm h_T009
  by_cases hD : dimH E = 0
  · obtain ⟨hLower, hEq⟩ := h_T017 hD
    exact hEq ▸ hLower
  · exact h_T012 (lt_of_le_of_ne h_T005.1.1 (Ne.symm hD))

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) :
    dimH (YuiCylinder E) = dimH E + 1 := by
  have h_T001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A := @T001 n E 
  have h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A) := @T002 n E h_T001
  have h_T004 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ := @T004 n E h_H001 h_H002 h_H003 h_T002
  have h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤) := @T005 n E h_H003 h_T004
  have h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k)) := @T003 n E 
  have h_T006 : n = 0 → dimH (YuiCylinder E) ≤ dimH E + 1 := @T006 n E h_H002 h_T002 h_T003 h_T005
  have h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε := @T007 n E h_H002 h_T002 h_T005
  have h_T008 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := @T008 n E h_T003 h_T007
  have h_T009 : dimH (YuiCylinder E) ≤ dimH E + 1 := @T009 n E h_T002 h_T005 h_T006 h_T008
  have h_T010 : ∀ s δ : ℝ, 0 < s → 0 < δ → ∀ V : ℕ → Set (YuiEucl (n + 1)), YuiCover δ (YuiCylinder E) V → ∀ ε : ℝ, 0 < ε → YuiContent s δ E ≤ YuiCost (s + 1) V + ENNReal.ofReal ε := @T010 n E h_T003 h_T005
  have h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ → YuiContent s δ E ≤ YuiContent (s + 1) δ (YuiCylinder E) := @T011 n E h_T005 h_T010
  have h_T012 : 0 < dimH E → dimH E + 1 ≤ dimH (YuiCylinder E) := @T012 n E h_T002 h_T005 h_T011
  have h_T013 : ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0 := @T013 n E 
  have h_T014 : ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) := @T014 n E 
  have h_T015 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ → (ENNReal.ofReal δ) ^ (s - 1) ≤ YuiContent s δ YuiI := @T015 n E h_T014
  have h_T016 : dimH YuiI = 1 := @T016 n E h_T001 h_T002 h_T013 h_T015
  have h_T017 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YuiCylinder E) ∧ (1 : ℝ≥0∞) = dimH E + 1 := @T017 n E h_H002 h_T002 h_T003 h_T016
  have h_T018 : dimH (YuiCylinder E) = dimH E + 1 := @T018 n E h_T005 h_T009 h_T012 h_T017
  exact h_T018

#check @P
#print axioms P

end Translation
