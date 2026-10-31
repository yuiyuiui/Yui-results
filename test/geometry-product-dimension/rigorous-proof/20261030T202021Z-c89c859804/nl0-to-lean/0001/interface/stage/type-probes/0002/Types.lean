import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

set_option autoImplicit false
#check (fun (n : ℕ) (E : Set (GPEucl n)) => ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s → GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)
#check (fun (n : ℕ) (E : Set (GPEucl n)) => ∀ (s δ : ℝ), 0 < s → 0 < δ → ∃ (T : Finset (GPEucl n)), E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2) ∧ (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧ (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal))
#check (fun (n : ℕ) (E : Set (GPEucl n)) => ∀ (k : ℕ) (A : Set (GPEucl k)) (e : GPI → GPEucl k), (∀ t, e t ∈ A) → (∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)|) → (1 : ENNReal) ≤ dimH A)
