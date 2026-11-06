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
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (S : Set X) (δ : ℝ), 0 < δ → (Metric.ediam S ≤ ENNReal.ofReal δ ↔ Bornology.IsBounded S ∧ Metric.diam S ≤ δ)" := by
  intro X _ S δ hδ
  constructor
  · intro h
    have hf : Metric.ediam S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    exact ⟨Metric.isBounded_iff_ediam_ne_top.mpr hf, ENNReal.toReal_le_of_le_ofReal hδ.le h⟩
  · rintro ⟨hb, hd⟩
    have he : ENNReal.ofReal (Metric.diam S) = Metric.ediam S := ENNReal.ofReal_toReal hb.ediam_ne_top
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hd

theorem yui_aux_0002 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (ι : Type*) (a : ℝ), 0 < a → ∀ U : ι → Set X, (∀ i, Bornology.IsBounded (U i)) → cost a U = realCost a U" := by
  intro X _ ι a ha U hb
  classical
  unfold cost realCost
  apply tsum_congr
  intro i
  have he : ENNReal.ofReal (Metric.diam (U i)) = Metric.ediam (U i) := ENNReal.ofReal_toReal (hb i).ediam_ne_top
  rw [he]
  by_cases hn : (U i).Nonempty
  · simp [hn]
  · have hz : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hz, ENNReal.zero_rpow_of_pos ha]

theorem checked (n : ℕ) (E : Set (BasisObjects.Rn n))  : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), (∀ r s : ℝ≥0∞, r ≤ s → BasisObjects.content a s A ≤ BasisObjects.content a r A) ∧ (∀ (r : ℝ≥0∞) (U : ℕ → Set X), A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → BasisObjects.content a r A ≤ cost a U) ∧ (∀ (r b : ℝ≥0∞), (∀ U : ℕ → Set X, A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → b ≤ cost a U) → b ≤ BasisObjects.content a r A)" := by
  intro X _ A a
  have upper : ∀ (r : ℝ≥0∞) (U : ℕ → Set X), A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → BasisObjects.content a r A ≤ cost a U := by
    intro r U hc hd
    exact iInf_le_of_le U (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))
  have lower : ∀ (r b : ℝ≥0∞), (∀ U : ℕ → Set X, A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → b ≤ cost a U) → b ≤ BasisObjects.content a r A := by
    intro r b h
    exact le_iInf fun U => le_iInf fun hc => le_iInf fun hd => h U hc hd
  refine ⟨?_, upper, lower⟩
  intro r s hrs
  apply lower
  intro U hc hd
  exact upper s U hc (fun i => (hd i).trans hrs)
#check @checked
#print axioms checked
end YuiAuxiliary
