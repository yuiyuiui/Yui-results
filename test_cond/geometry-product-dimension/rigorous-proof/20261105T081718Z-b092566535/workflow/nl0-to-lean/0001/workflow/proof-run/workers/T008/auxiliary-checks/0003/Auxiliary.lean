import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (N : ℕ) (t : ℝ), 0 < N → 0 ≤ t → t < 1 → ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro N t hN ht ht1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnon : 0 ≤ t * (N : ℝ) := mul_nonneg ht hNr.le
  have hprod : t * (N : ℝ) < N := by nlinarith
  have hj : ⌊t * (N : ℝ)⌋₊ < N := (Nat.floor_lt hnon).mpr hprod
  refine ⟨⟨⌊t * (N : ℝ)⌋₊, hj⟩, ?_, ?_⟩
  · exact (div_le_iff₀ hNr).mpr (Nat.floor_le hnon)
  · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one (t * N)).le

theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ d : ℝ, 0 < d → d ≤ 1 → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ d ∧ (N : ℝ) * d ≤ 2 ∧ (∀ t ∈ YuiI, ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N))" := by
  intro d hd hd1
  refine ⟨⌈1 / d⌉₊, Nat.ceil_pos.mpr (by positivity), ?_, ?_, ?_⟩
  · have h := Nat.le_ceil (1 / d)
    have hN : (0 : ℝ) < (⌈1 / d⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr (by positivity : 0 < 1 / d)
    apply (div_le_iff₀ hN).mpr
    have := (div_le_iff₀ hd).mp h
    nlinarith
  · have h := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / d)).le
    have hmul := mul_le_mul_of_nonneg_right h hd.le
    rw [add_mul, div_mul_cancel₀ _ hd.ne'] at hmul
    nlinarith
  · intro t ht
    change 0 ≤ t ∧ t ≤ 1 at ht
    let N := ⌈1 / d⌉₊
    change ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    by_cases ht1 : t = 1
    · refine ⟨⟨N - 1, by omega⟩, ?_⟩
      change ((N - 1 : ℕ) : ℝ) / N ≤ t ∧ t ≤ (((N - 1 : ℕ) : ℝ) + 1) / N
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast, ht1]
      constructor
      · apply (div_le_iff₀ hNr).mpr; nlinarith
      · apply (le_div_iff₀ hNr).mpr; nlinarith
    · exact yui_aux_0001 n E h_T003 h_T007 N t hN ht.1 (lt_of_le_of_ne ht.2 ht1)
#check @checked
#print axioms checked
end YuiAuxiliary
