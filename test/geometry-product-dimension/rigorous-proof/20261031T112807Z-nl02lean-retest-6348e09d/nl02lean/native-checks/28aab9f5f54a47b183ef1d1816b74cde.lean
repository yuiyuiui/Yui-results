import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

namespace Translation
set_option autoImplicit false

theorem T011 (n : ℕ) (E : Set (YEuclid n)) (h_T010 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEuclid (n+1)), yCover δ (yProd E) V → ∀ ε : ℝ, 0 < ε → yContent s δ E ≤ yCost (s+1) V + ENNReal.ofReal ε) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E ≤ yContent (s+1) δ (yProd E) := by
  intro s δ hs hδ
  refine le_iInf fun V => le_iInf fun hcov => le_iInf fun hdiam => ?_
  change yContent s δ E ≤ yCost (s + 1) V
  by_cases htop : yCost (s + 1) V = ⊤
  · rw [htop]
    exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    have hεreal : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.mpr hε
    have hεcoe : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) :=
      ENNReal.ofReal_coe_nnreal
    simpa only [hεcoe] using
      h_T010 s δ hs hδ V ⟨hcov, hdiam⟩ (ε : ℝ) hεreal

#check @T011
#print axioms T011

end Translation
