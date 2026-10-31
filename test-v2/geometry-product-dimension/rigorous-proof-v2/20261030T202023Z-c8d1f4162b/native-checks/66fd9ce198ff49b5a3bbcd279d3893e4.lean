import Mathlib
open scoped ENNReal NNReal
noncomputable section
abbrev YEucl (m : ℕ) := EuclideanSpace ℝ (Fin m)
def YI : Set ℝ := Set.Icc 0 1
def YJoin {m : ℕ} (x : YEucl m) (t : ℝ) : YEucl (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YBase {m : ℕ} (z : YEucl (m + 1)) : YEucl m :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def YLast {m : ℕ} (z : YEucl (m + 1)) : ℝ := z (Fin.last m)
def YF {m : ℕ} (A : Set (YEucl m)) : Set (YEucl (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ YI, z = YJoin x t}
def YLine (t : ℝ) : YEucl 1 := WithLp.toLp 2 (fun _ => t)
def YCover {X : Type*} [PseudoEMetricSpace X]
    (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def YCost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s
def YContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YCover δ A U), YCost s U
def YHaus {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A
def YCritical {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) : Prop :=
  0 ≤ dimH A ∧ ∀ s : ℝ, 0 < s →
    YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → YHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → YHaus s A = ⊤) ∧
    (YHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (YHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)

namespace Translation
set_option autoImplicit false

#check (∀ (n : ℕ) (E : Set (YEucl n)) , ∀ (m : ℕ) (A : Set (YEucl m)) (s : ℝ), 0 < s → YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T001 : ∀ (m : ℕ) (A : Set (YEucl m)) (s : ℝ), 0 < s → YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A), ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_H002 : IsCompact E), (∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, |x i| ≤ L) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T005 : (∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, |x i| ≤ L) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)), (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤))
#check (∀ (n : ℕ) (E : Set (YEucl n)) , (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine), (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ YI = YContent s δ (YLine '' YI)) ∧ (∀ s : ℝ, 0 < s → YHaus s YI = YHaus s (YLine '' YI)) ∧ dimH YI = dimH (YLine '' YI))
#check (∀ (n : ℕ) (E : Set (YEucl n)) , ∀ a : ℝ, 1 < a → YHaus a YI = 0)
#check (∀ (n : ℕ) (E : Set (YEucl n)) , ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T008 : ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)), (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T004 : (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ YI = YContent s δ (YLine '' YI)) ∧ (∀ s : ℝ, 0 < s → YHaus s YI = YHaus s (YLine '' YI)) ∧ dimH YI = dimH (YLine '' YI)) (h_T007 : ∀ a : ℝ, 1 < a → YHaus a YI = 0) (h_T008 : ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)) (h_T009 : (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)), dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T010 : dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)), n = 0 → dimH (YF E) ≤ dimH E + 1)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A), 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set (YEucl n), YCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ YCost q U < ENNReal.ofReal ε)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T012 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set (YEucl n), YCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ YCost q U < ENNReal.ofReal ε), 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ V : ℕ → Set (YEucl (n+1)), YCover (Real.sqrt 2 * r) (YF E) V ∧ YCost (q+1) V < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T013 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ V : ℕ → Set (YEucl (n+1)), YCover (Real.sqrt 2 * r) (YF E) V ∧ YCost (q+1) V < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε)), 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → YHaus (q+1) (YF E) = 0 ∧ dimH (YF E) ≤ ENNReal.ofReal (q+1))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T011 : n = 0 → dimH (YF E) ≤ dimH E + 1) (h_T014 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → YHaus (q+1) (YF E) = 0 ∧ dimH (YF E) ≤ ENNReal.ofReal (q+1)), dimH (YF E) ≤ dimH E + 1)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine), ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ, (∀ i, IsOpen (J i)) ∧ (∀ i, YLast '' (V i) ⊆ J i) ∧ (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s))) ∧ (∀ t ∈ YI, YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T016 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ, (∀ i, IsOpen (J i)) ∧ (∀ i, YLast '' (V i) ⊆ J i) ∧ (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s))) ∧ (∀ t ∈ YI, YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t)), ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → YContent s δ E ≤ YCost (s+1) V)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T017 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → YContent s δ E ≤ YCost (s+1) V), ∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E ≤ YContent (s+1) δ (YF E))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T018 : ∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E ≤ YContent (s+1) δ (YF E)), 0 < dimH E → dimH E + 1 ≤ dimH (YF E))
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_H001 : E.Nonempty) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T010 : dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)), dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YF E) ∧ (1 : ℝ≥0∞) = dimH E + 1)
#check (∀ (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T015 : dimH (YF E) ≤ dimH E + 1) (h_T019 : 0 < dimH E → dimH E + 1 ≤ dimH (YF E)) (h_T020 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (YF E) ∧ (1 : ℝ≥0∞) = dimH E + 1), dimH (YF E) = dimH E + 1)

end Translation
