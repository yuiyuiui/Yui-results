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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEucl n)) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T012 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set (YEucl n), YCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ YCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (d : ℝ), 0 < d → d ≤ 1 → let N := ⌈1 / d⌉₊; 0 < N ∧ 1 / (N : ℝ) ≤ d ∧ (N : ℝ) ≤ 2 / d ∧ ∀ t ∈ YI, ∃ j : ℕ, j < N ∧ t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro d hd hd1 N
  have hc : 1 / d ≤ (N : ℝ) := Nat.le_ceil _
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨hN, (div_le_iff₀ hNr).2 ?_, ?_, ?_⟩
  · have := (div_le_iff₀ hd).1 hc
    nlinarith
  · have h := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / d)).le
    change (N : ℝ) ≤ 2 / d
    apply (le_div_iff₀ hd).2
    have hh : (N : ℝ) * d ≤ (1 / d + 1) * d := mul_le_mul_of_nonneg_right h hd.le
    field_simp at hh
    nlinarith
  · intro t ht
    change 0 ≤ t ∧ t ≤ 1 at ht
    by_cases ht1 : t = 1
    · refine ⟨N-1, by omega, ?_⟩
      have he : ((N-1 : ℕ) : ℝ) + 1 = N := by
        exact_mod_cast (Nat.sub_add_cancel hN)
      subst t
      constructor
      · apply (div_le_iff₀ hNr).2
        linarith
      · apply (le_div_iff₀ hNr).2
        linarith
    · refine ⟨⌊t * N⌋₊, ?_, ?_⟩
      · apply (Nat.floor_lt (by positivity : 0 ≤ t * (N : ℝ))).2
        nlinarith
      · constructor
        · apply (div_le_iff₀ hNr).2
          exact Nat.floor_le (by positivity)
        · apply (le_div_iff₀ hNr).2
          exact (Nat.lt_floor_add_one _).le
#check @checked
#print axioms checked
end YuiAuxiliary
