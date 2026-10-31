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

def __signature_T001 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)), ((∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ))
def __signature_T002 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ), (dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)))
def __signature_T003 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ), (dimH yI ≤ 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0)))
def __signature_T004 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)), (∀ (δ : ℝ), 0 < δ → ∀ V : ℕ → Set ℝ, yCover δ yI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)))
def __signature_T005 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T003 : dimH yI ≤ 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0)) (h_T004 : ∀ (δ : ℝ), 0 < δ → ∀ V : ℕ → Set ℝ, yCover δ yI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i)), (dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤)))
def __signature_T006 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T005 : dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤)), (n = 0 → dimH (yProd E) ≤ dimH E + 1))
def __signature_T007 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)), (1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε))
def __signature_T008 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T007 : 1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε), (1 ≤ n → dimH (yProd E) ≤ dimH E + 1))
def __signature_T009 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T006 : n = 0 → dimH (yProd E) ≤ dimH E + 1) (h_T008 : 1 ≤ n → dimH (yProd E) ≤ dimH E + 1), (dimH (yProd E) ≤ dimH E + 1 ∧ dimH (yProd E) < ⊤))
def __signature_T010 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)), (∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEuclid (n+1)), yCover δ (yProd E) V → ∀ ε : ℝ, 0 < ε → yContent s δ E ≤ yCost (s+1) V + ENNReal.ofReal ε))
def __signature_T011 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T010 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEuclid (n+1)), yCover δ (yProd E) V → ∀ ε : ℝ, 0 < ε → yContent s δ E ≤ yCost (s+1) V + ENNReal.ofReal ε), (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E ≤ yContent (s+1) δ (yProd E)))
def __signature_T012 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T011 : ∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E ≤ yContent (s+1) δ (yProd E)), (0 < dimH E → dimH E + 1 ≤ dimH (yProd E)))
def __signature_T013 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_H002 : E.Nonempty) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T005 : dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤)), (dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (yProd E) ∧ (1 : ℝ≥0∞) = dimH E + 1))
def __signature_T014 : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T009 : dimH (yProd E) ≤ dimH E + 1 ∧ dimH (yProd E) < ⊤) (h_T012 : 0 < dimH E → dimH E + 1 ≤ dimH (yProd E)) (h_T013 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (yProd E) ∧ (1 : ℝ≥0∞) = dimH E + 1), (dimH (yProd E) = dimH E + 1))
def __signature_P : Prop :=
  (∀ (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E), (dimH (yProd E) = dimH E + 1))

end Translation
