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

set_option autoImplicit false
def __probe_0 :=
  (fun (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
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
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) => (∀ (X : ((fun {S : Type*} {Q : S → Prop} (h : ∀ x, Q x) => S) h_T001)), X = X))
