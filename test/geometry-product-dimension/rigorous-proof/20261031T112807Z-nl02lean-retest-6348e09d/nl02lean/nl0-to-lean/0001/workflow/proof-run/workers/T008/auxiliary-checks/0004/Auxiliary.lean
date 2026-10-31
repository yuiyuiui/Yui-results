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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T007 : 1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ a : ℝ, 0 < a → a ≤ 1 → ∃ (N : ℕ) (J : Fin N → Set ℝ), 0 < N ∧ (N : ℝ) ≤ 2 / a ∧ (∀ t ∈ yI, ∃ j, t ∈ J j) ∧ ∀ j s, s ∈ J j → ∀ t, t ∈ J j → dist s t ≤ a" := by
  intro a ha ha1
  let N : ℕ := ⌈1 / a⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNa : (N : ℝ) ≤ 2 / a := by
    have hc : (N : ℝ) < 1 / a + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : (1 : ℝ) ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha1)
    rw [show 2 / a = 1 / a + 1 / a by ring]
    linarith
  have hlen : 1 / (N : ℝ) ≤ a := by
    have hc : 1 / a ≤ (N : ℝ) := Nat.le_ceil _
    apply (div_le_iff₀ hNr).mpr
    have := (div_le_iff₀ ha).mp hc
    nlinarith
  let J : Fin N → Set ℝ := fun j => Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
  refine ⟨N, J, hN, hNa, ?_, ?_⟩
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    by_cases ht : t = 1
    · let j : Fin N := ⟨N-1, by omega⟩
      refine ⟨j, ?_⟩
      change (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N
      have hj : (j : ℝ) + 1 = (N : ℝ) := by
        dsimp [j]
        norm_cast
        omega
      rw [ht]
      constructor
      · apply (div_le_iff₀ hNr).mpr
        linarith
      · rw [hj, div_self (ne_of_gt hNr)]
    · have htlt : t < 1 := lt_of_le_of_ne ht1 ht
      let j : Fin N := ⟨⌊t * N⌋₊, (Nat.floor_lt (mul_nonneg ht0 hNr.le)).mpr (by nlinarith)⟩
      refine ⟨j, ?_⟩
      change (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N
      constructor
      · apply (div_le_iff₀ hNr).mpr
        exact Nat.floor_le (mul_nonneg ht0 hNr.le)
      · apply (le_div_iff₀ hNr).mpr
        exact (Nat.lt_floor_add_one (t * N)).le
  · intro j s hs t ht
    have hst : |s-t| ≤ 1 / (N : ℝ) := by
      change _ ≤ s ∧ s ≤ _ at hs
      change _ ≤ t ∧ t ≤ _ at ht
      simp only [add_div] at hs ht
      rw [abs_le]
      constructor <;> linarith
    exact (by simpa [Real.dist_eq] using hst : dist s t ≤ 1 / (N : ℝ)).trans hlen
#check @checked
#print axioms checked
end YuiAuxiliary
