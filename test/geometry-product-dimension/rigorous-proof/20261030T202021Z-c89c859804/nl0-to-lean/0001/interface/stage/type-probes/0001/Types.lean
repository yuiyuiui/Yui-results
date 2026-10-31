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
    (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

set_option autoImplicit false
#check (fun (n : ℕ) (E : Set (GPEucl n)) => GPappend (0 : GPEucl n) (0 : ℝ))
#check (fun (n : ℕ) (E : Set (GPEucl n)) => ∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ), dist (GPappend x t) (GPappend y u) = Real.sqrt (dist x y ^ 2 + |t - u| ^ 2))
#check (fun (n : ℕ) (E : Set (GPEucl n)) => ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s → GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)
#check (fun (n : ℕ) (E : Set (GPEucl n)) => ∀ (B : Set ℝ), B.Nonempty → IsLUB B (sSup B))
#check (fun (n : ℕ) (E : Set (GPEucl n)) => EuclideanSpace.dist_eq)
#check (fun (n : ℕ) (E : Set (GPEucl n)) => ENNReal.ofReal)
#check (fun (n : ℕ) (E : Set (GPEucl n)) => Fin.snoc)
