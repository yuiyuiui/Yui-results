import Mathlib
open scoped ENNReal NNReal BigOperators
noncomputable section

abbrev GDVec (m : ℕ) := EuclideanSpace ℝ (Fin m)

def GDLine (t : ℝ) : GDVec 1 :=
  WithLp.toLp 2 (fun _ => t)

def GDInterval : Set ℝ := Set.Icc 0 1

def GDPoint {m : ℕ} (x : GDVec m) (t : ℝ) : GDVec (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)

def GDProduct {m : ℕ} (A : Set (GDVec m)) : Set (GDVec (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ GDInterval, z = GDPoint x t}

def GDCost {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (_ : A.Nonempty), (Metric.ediam A) ^ s

def GDContent {X : Type*} [PseudoEMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, GDCost s (U i)

def GDMeasure {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GDContent s δ A

def GDPositiveCover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (q r ε : ℝ) : Prop :=
  ∃ (K : Set ℕ) (U : K → Set X),
    A ⊆ ⋃ i, U i ∧
    (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧
    (∑' i, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal ε

namespace Translation
set_option autoImplicit false

def __signature_T001 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)), (∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A))
def __signature_T002 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T001 : ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A), (∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)))
def __signature_T003 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)), (Bornology.IsBounded E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)))
def __signature_T004 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_H002 : IsCompact E) (h_T003 : Bornology.IsBounded E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)), (Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)))
def __signature_T018 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)), (Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)))
def __signature_T005 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)), ((∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1))
def __signature_T006 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)), (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval))
def __signature_T007 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)), (dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)))
def __signature_T008 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)), (1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε))
def __signature_T009 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)), ((∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)))
def __signature_T010 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)), (dimH (GDProduct E) ≤ dimH E + 1 ∧ dimH (GDProduct E) < ⊤))
def __signature_T011 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)), (∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε))
def __signature_T012 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε), (∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ E ≤ GDContent (s + 1) δ (GDProduct E)))
def __signature_T013 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T012 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ E ≤ GDContent (s + 1) δ (GDProduct E)), (∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤))
def __signature_T014 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤), (0 < dimH E → dimH E + 1 ≤ dimH (GDProduct E)))
def __signature_T015 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)), (dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E)))
def __signature_T016 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T015 : dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E)), (dimH E = 0 →
  (1 : ℝ≥0∞) ≤ dimH (GDProduct E) ∧
  (1 : ℝ≥0∞) = dimH E + 1))
def __signature_T017 : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T010 : dimH (GDProduct E) ≤ dimH E + 1 ∧ dimH (GDProduct E) < ⊤) (h_T014 : 0 < dimH E → dimH E + 1 ≤ dimH (GDProduct E)) (h_T016 : dimH E = 0 →
  (1 : ℝ≥0∞) ≤ dimH (GDProduct E) ∧
  (1 : ℝ≥0∞) = dimH E + 1), (dimH (GDProduct E) = dimH E + 1))
def __signature_P : Prop :=
  (∀ (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E), (dimH (GDProduct E) = dimH E + 1))

end Translation
