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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (V n)) (h_T017 : ∀ (s δ ε : ℝ) (W : ℕ → Set (V (n+1))), 0 < s → 0 < δ → 0 < ε → scaleCover δ (cylinder E) W → ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i) ∧ height '' W i ⊆ J i ∧ (volume (J i ∩ unitI) : ℝ≥0∞) ≤ ENNReal.ofReal (Metric.diam (W i) + padding ε s W i)) ∧ (∀ t ∈ unitI, content s δ E ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => (Metric.ediam (W i)) ^ s) t)) (h_T018 : ∀ (c : ℝ≥0∞) (w : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ t ∈ unitI, c ≤ ∑' i, Set.indicator (J i) (fun t0 : ℝ => w i) t) → ((∀ i, Measurable (Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i))) ∧ (∀ t : ℝ, Set.indicator unitI (fun t0 : ℝ => c) t ≤ ∑' i, Set.indicator (J i ∩ unitI) (fun t0 : ℝ => w i) t) ∧ c ≤ ∑' i, w i * volume (J i ∩ unitI))) (h_T016 : LipschitzWith 1 (base : V (n+1) → V n) ∧ LipschitzWith 1 (height : V (n+1) → ℝ) ∧ (∀ (δ : ℝ) (W : ℕ → Set (V (n+1))), 0 < δ → scaleCover δ (cylinder E) W → ∀ i, Metric.ediam (W i) = ENNReal.ofReal (Metric.diam (W i)) ∧ 0 ≤ Metric.diam (W i) ∧ Metric.diam (W i) ≤ δ ∧ Metric.ediam (base '' W i) ≤ Metric.ediam (W i) ∧ Metric.ediam (height '' W i) ≤ Metric.ediam (W i))) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) : yui_aux_type% "∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → b / (1+a) * a ≤ b" := by
  intro a b ha hb
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0 < 1+a)).2
  nlinarith
#check @checked
#print axioms checked
end YuiAuxiliary
