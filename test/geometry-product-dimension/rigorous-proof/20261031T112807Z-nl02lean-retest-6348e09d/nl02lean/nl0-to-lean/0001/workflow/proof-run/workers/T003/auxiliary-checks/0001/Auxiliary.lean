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
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) : yui_aux_type% "∀ N : ℕ, 0 < N → ∃ U : ℕ → Set ℝ, yCover (1 / (N : ℝ)) yI U ∧ (∀ k, Metric.ediam (U k) = if k < N then ENNReal.ofReal (1 / (N : ℝ)) else 0)" := by
  intro N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let U : ℕ → Set ℝ := fun k => if k < N then Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N) else ∅
  have hd : ∀ k, Metric.ediam (U k) = if k < N then ENNReal.ofReal (1 / (N : ℝ)) else 0 := by
    intro k
    by_cases hk : k < N
    · simp only [U, if_pos hk, Real.ediam_Icc]
      congr 1
      ring
    · simp [U, hk]
  refine ⟨U, ⟨?_, ?_⟩, hd⟩
  · intro x hx
    change 0 ≤ x ∧ x ≤ 1 at hx
    apply Set.mem_iUnion.mpr
    by_cases hx1 : x = 1
    · refine ⟨N - 1, ?_⟩
      have hk : N - 1 < N := Nat.sub_lt hN (by omega)
      simp only [U, if_pos hk, mem_Icc, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      subst x
      constructor
      · apply (div_le_iff₀ hNr).mpr
        linarith
      · apply (le_div_iff₀ hNr).mpr
        linarith
    · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
      let k := ⌊x * (N : ℝ)⌋₊
      have hmul : 0 ≤ x * (N : ℝ) := mul_nonneg hx.1 hNr.le
      have hk : k < N := (Nat.floor_lt hmul).mpr (by nlinarith)
      refine ⟨k, ?_⟩
      simp only [U, if_pos hk, mem_Icc]
      constructor
      · exact (div_le_iff₀ hNr).mpr (Nat.floor_le hmul)
      · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one (x * (N : ℝ))).le
  · intro k
    rw [hd k]
    split_ifs <;> simp
#check @checked
#print axioms checked
end YuiAuxiliary
