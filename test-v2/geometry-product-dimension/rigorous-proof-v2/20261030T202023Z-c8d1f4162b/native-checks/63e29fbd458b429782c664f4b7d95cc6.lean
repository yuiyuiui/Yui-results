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

theorem T015 (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T011 : n = 0 → dimH (YF E) ≤ dimH E + 1) (h_T014 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → YHaus (q+1) (YF E) = 0 ∧ dimH (YF E) ≤ ENNReal.ofReal (q+1)) :
    dimH (YF E) ≤ dimH E + 1 := by
  by_cases hn : n = 0
  · exact h_T011 hn
  · have hn1 : 1 ≤ n := by omega
    have hD : dimH E ≠ ⊤ := ne_of_lt h_T006.1.2.2
    have hconv : ENNReal.ofReal (dimH E).toReal = dimH E := ENNReal.ofReal_toReal hD
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hlt : ENNReal.ofReal (dimH E).toReal < ENNReal.ofReal ((dimH E).toReal + (ε : ℝ)) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    have hq : dimH E < ENNReal.ofReal ((dimH E).toReal + (ε : ℝ)) :=
      hconv.symm.trans_lt hlt
    have hbound := (h_T014 hn1 ((dimH E).toReal + (ε : ℝ)) hq).2
    have heq : ENNReal.ofReal (((dimH E).toReal + (ε : ℝ)) + 1) = (dimH E + 1) + (ε : ℝ≥0∞) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg, hconv]
      simp only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one]
      ac_rfl
    exact hbound.trans_eq heq

#check @T015
#print axioms T015

end Translation
