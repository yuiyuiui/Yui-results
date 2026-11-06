import Mathlib
open scoped ENNReal NNReal Topology
open Set MeasureTheory
namespace BasisObjects
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def content {X : Type*} [EMetricSpace X]
    (s : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def euclideanLift (n : ℕ) : Rn n × ℝ → WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2
end BasisObjects

namespace IntervalProduct
abbrev Rn := BasisObjects.Rn
def I : Set ℝ := Set.Icc 0 1
def F (n : ℕ) (E : Set (Rn n)) : Set (Rn n × ℝ) := E ×ˢ I
def j (n : ℕ) (p : WithLp 2 (Rn n × ℝ)) : Rn (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => p.fst i) p.snd)
def unj (n : ℕ) (v : Rn (n + 1)) : WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun i : Fin n => v i.castSucc), v (Fin.last n))
def G (n : ℕ) (E : Set (Rn n)) : Set (Rn (n + 1)) :=
  j n '' (BasisObjects.euclideanLift n '' F n E)
noncomputable def H {X : Type*} [MetricSpace X] (a : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  MeasureTheory.Measure.hausdorffMeasure a A
noncomputable def cost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ a
noncomputable def realCost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, (ENNReal.ofReal (Metric.diam (U i))) ^ a
def Cover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def RealCover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ (∀ i, Bornology.IsBounded (U i)) ∧ ∀ i, Metric.diam (U i) ≤ δ
end IntervalProduct
open IntervalProduct

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (S : Set (X × ℝ)), Bornology.IsBounded S → ∃ J : Set ℝ, MeasurableSet J ∧ Prod.snd '' S ⊆ J ∧ volume J ≤ Metric.ediam S" := by
  intro X _ S hS
  classical
  by_cases he : S = ∅
  · subst S
    exact ⟨∅, MeasurableSet.empty, by simp, by simp⟩
  · have hB : Bornology.IsBounded (Prod.snd '' S) := LipschitzWith.prod_snd.isBounded_image hS
    refine ⟨Set.Icc (sInf (Prod.snd '' S)) (sSup (Prod.snd '' S)), measurableSet_Icc, hB.subset_Icc_sInf_sSup, ?_⟩
    rw [Real.volume_Icc, ← Real.ediam_eq hB]
    simpa using (LipschitzWith.prod_snd.ediam_image_le S)

theorem yui_aux_0002 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (a δ : ℝ) (U : ℕ → Set X), Cover δ A U → BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U" := by
  intro X _ A a δ U hU
  unfold BasisObjects.content cost
  exact iInf_le_of_le U (iInf_le_of_le hU.1 (iInf_le_of_le hU.2 le_rfl))

theorem yui_aux_0003 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (s δ : ℝ) (V : ℕ → Set (X × ℝ)), 0 < s → 0 < δ → Cover δ (A ×ˢ I) V → ∀ J : ℕ → Set ℝ, (∀ i, Prod.snd '' V i ⊆ J i) → ∀ t ∈ I, BasisObjects.content s (ENNReal.ofReal δ) A ≤ ∑' i, (I ∩ J i).indicator (fun _ : ℝ => (Metric.ediam (V i)) ^ s) t" := by
  intro X _ A s δ V hs hδ hV J hJ t ht
  classical
  let U : ℕ → Set X := fun i => if t ∈ J i then Prod.fst '' V i else ∅
  have hproj (i : ℕ) : Metric.ediam (Prod.fst '' V i) ≤ Metric.ediam (V i) := by
    simpa only [ENNReal.coe_one, one_mul] using LipschitzWith.prod_fst.ediam_image_le (V i)
  have hU : Cover δ A U := by
    constructor
    · intro x hx
      have hxt : (x,t) ∈ A ×ˢ I := ⟨hx, ht⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hxt)
      have htJ : t ∈ J i := hJ i ⟨(x,t), hi, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, by simp only [U, if_pos htJ]; exact ⟨(x,t), hi, rfl⟩⟩
    · intro i
      by_cases hi : t ∈ J i
      · simpa only [U, if_pos hi] using (hproj i).trans (hV.2 i)
      · simp [U, hi]
  have hc : BasisObjects.content s (ENNReal.ofReal δ) A ≤ cost s U :=
    @yui_aux_0002 n E h_T001 X _ A s δ U hU
  refine hc.trans (ENNReal.tsum_le_tsum fun i => ?_)
  change (⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s) ≤ _
  by_cases hi : t ∈ J i
  · have hti : t ∈ I ∩ J i := ⟨ht, hi⟩
    rw [Set.indicator_of_mem hti]
    apply iSup_le
    intro _
    apply ENNReal.rpow_le_rpow _ hs.le
    simpa only [U, if_pos hi] using hproj i
  · simp [U, hi]

theorem yui_aux_0004 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (c : ℝ≥0∞) (s : ℝ) (r : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ i, volume (J i) ≤ r i) → (∀ t ∈ I, c ≤ ∑' i, (I ∩ J i).indicator (fun _ : ℝ => r i ^ s) t) → c ≤ ∑' i, r i ^ s * r i" := by
  intro c s r J hJ hvol hf
  have hI : MeasurableSet I := measurableSet_Icc
  have hvI : volume I = 1 := by simp [I, Real.volume_Icc]
  let f : ℕ → ℝ → ℝ≥0∞ := fun i => (I ∩ J i).indicator (fun _ : ℝ => r i ^ s)
  have hm (i : ℕ) : AEMeasurable (f i) volume :=
    (measurable_const.indicator (hI.inter (hJ i))).aemeasurable
  have hp : I.indicator (fun _ : ℝ => c) ≤ fun t => ∑' i, f i t := by
    intro t
    by_cases ht : t ∈ I
    · simpa only [Set.indicator_of_mem ht] using hf t ht
    · simp only [Set.indicator_of_notMem ht]
      exact zero_le
  have hg : (∫⁻ t : ℝ, I.indicator (fun _ => c) t) = c := by
    rw [lintegral_indicator_const hI, hvI, mul_one]
  calc
    c = ∫⁻ t : ℝ, I.indicator (fun _ => c) t := hg.symm
    _ ≤ ∫⁻ t : ℝ, ∑' i, f i t := lintegral_mono hp
    _ = ∑' i, ∫⁻ t : ℝ, f i t := lintegral_tsum hm
    _ = ∑' i, r i ^ s * volume (I ∩ J i) := by
      congr 1
      funext i
      exact lintegral_indicator_const (hI.inter (hJ i)) _
    _ ≤ ∑' i, r i ^ s * r i := ENNReal.tsum_le_tsum fun i =>
      mul_le_mul_left' ((measure_mono Set.inter_subset_right).trans (hvol i)) _

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) :
    ∀ (X : Type*) [MetricSpace X] (A : Set X) (s δ : ℝ),
  0 < s → 0 < δ → ∀ V : ℕ → Set (X × ℝ), Cover δ (A ×ˢ I) V →
    BasisObjects.content s (ENNReal.ofReal δ) A ≤ cost (s + 1) V := by
  intro X _ A s δ hs hδ V hV
  classical
  have hb (i : ℕ) : Bornology.IsBounded (V i) :=
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i))
  choose J hm hcontains hvol using fun i => @yui_aux_0001 n E h_T001 X _ (V i) (hb i)
  have hf : ∀ t ∈ I, BasisObjects.content s (ENNReal.ofReal δ) A ≤
      ∑' i, (I ∩ J i).indicator (fun _ : ℝ => Metric.ediam (V i) ^ s) t :=
    @yui_aux_0003 n E h_T001 X _ A s δ V hs hδ hV J hcontains
  have hc : BasisObjects.content s (ENNReal.ofReal δ) A ≤
      ∑' i, Metric.ediam (V i) ^ s * Metric.ediam (V i) :=
    @yui_aux_0004 n E h_T001 (BasisObjects.content s (ENNReal.ofReal δ) A)
      s (fun i => Metric.ediam (V i)) J hm hvol hf
  refine hc.trans ?_
  unfold cost
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : (V i).Nonempty
  · have hp : Metric.ediam (V i) ^ s * Metric.ediam (V i) =
        Metric.ediam (V i) ^ (s + 1) := by
      rw [ENNReal.rpow_add_of_nonneg s 1 hs.le zero_le_one, ENNReal.rpow_one]
    rw [hp]
    exact le_iSup_of_le hi le_rfl
  · have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp [he, ENNReal.zero_rpow_of_pos hs]

#check @T004
#print axioms T004

end Translation
