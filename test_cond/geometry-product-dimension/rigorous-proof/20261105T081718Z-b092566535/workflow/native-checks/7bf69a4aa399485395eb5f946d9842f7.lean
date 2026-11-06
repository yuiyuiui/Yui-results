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

#check @T002
#print axioms T002

end Translation
