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

namespace YuiAuxiliary
set_option autoImplicit false
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

theorem checked (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
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
  have hU : Cover δ A U := by
    constructor
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 ⟨hx, ht⟩)
      have htJ : t ∈ J i := hJ i ⟨(x,t), hi, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, by simp only [U, if_pos htJ]; exact ⟨(x,t), hi, rfl⟩⟩
    · intro i
      by_cases hi : t ∈ J i
      · simp only [U, if_pos hi]
        exact (by simpa using LipschitzWith.prod_fst.ediam_image_le (V i)).trans (hV.2 i)
      · simp [U, hi]
  have hc : BasisObjects.content s (ENNReal.ofReal δ) A ≤ cost s U :=
    (h_T001 X A s hs).2.2.2.1 δ U hδ hU
  refine hc.trans (ENNReal.tsum_le_tsum fun i => ?_)
  change (⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s) ≤ _
  by_cases hi : t ∈ J i
  · rw [Set.indicator_of_mem ⟨ht, hi⟩]
    apply iSup_le
    intro _
    apply ENNReal.rpow_le_rpow _ hs.le
    simpa only [U, if_pos hi, ENNReal.coe_one, one_mul] using LipschitzWith.prod_fst.ediam_image_le (V i)
  · simp [U, hi, Set.indicator_of_notMem (show t ∉ I ∩ J i from fun h => hi h.2)]
#check @checked
#print axioms checked
end YuiAuxiliary
