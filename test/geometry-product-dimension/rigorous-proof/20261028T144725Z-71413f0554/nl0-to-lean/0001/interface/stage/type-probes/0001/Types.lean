import Mathlib
open scoped ENNReal NNReal
open Set MeasureTheory
abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def base {n : ℕ} (z : V (n+1)) : V n := WithLp.toLp 2 (fun i => z i.castSucc)
def height {n : ℕ} (z : V (n+1)) : ℝ := z (Fin.last n)
noncomputable def join {n : ℕ} (x : V n) (t : ℝ) : V (n+1) := WithLp.toLp 2 (Fin.lastCases t (fun i => x i))
def unitI : Set ℝ := Set.Icc 0 1
def cylinder {n : ℕ} (E : Set (V n)) : Set (V (n+1)) := {z | base z ∈ E ∧ height z ∈ unitI}
noncomputable def content {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ := ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def haus {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ := ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A

set_option autoImplicit false
#check (fun (n : ℕ) (E : Set (V n)) => dimH (cylinder E) = dimH E + 1)
#check (fun (n : ℕ) (E : Set (V n)) => Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2))
#check (fun (n : ℕ) (E : Set (V n)) => ∀ {X Y : Type} [MetricSpace X] [MetricSpace Y] (A : Set X) (f : A → Y), Isometry f → dimH (Set.range f) = dimH A)
#check (fun (n : ℕ) (E : Set (V n)) => ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (s : ℝ), 0 < s → haus s A = MeasureTheory.Measure.hausdorffMeasure s A)
