import Mathlib
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
namespace YuiBasis
noncomputable def Content {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ δ),
    ∑' i, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ s
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
noncomputable def appendCoord (n : ℕ) (p : Ambient n × ℝ) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
end YuiBasis

open YuiBasis
namespace YuiPlan
noncomputable def H {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  hausdorffMeasure s A
noncomputable def C {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  YuiBasis.Content s (ENNReal.ofReal δ) A
end YuiPlan
open YuiPlan
namespace YuiPortTypes
abbrev T004.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧
  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →
    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧
      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)
end YuiPortTypes
universe u

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (N : ℕ), 0 < N → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro N hN t ht
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases ht1 : t = 1
  · refine ⟨⟨N - 1, Nat.sub_lt hN (by omega)⟩, ?_⟩
    have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [Fin.val_mk, ht1, Set.mem_Icc]
    rw [hc]
    constructor
    · apply (div_le_iff₀ hn).mpr
      linarith
    · apply (le_div_iff₀ hn).mpr
      linarith
  · have htt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hnon : 0 ≤ t * N := mul_nonneg ht.1 hn.le
    have hj : ⌊t * N⌋₊ < N := (Nat.floor_lt hnon).mpr (by nlinarith)
    refine ⟨⟨⌊t * N⌋₊, hj⟩, ?_⟩
    change (⌊t * N⌋₊ : ℝ) / N ≤ t ∧ t ≤ ((⌊t * N⌋₊ : ℝ) + 1) / N
    exact ⟨(div_le_iff₀ hn).mpr (Nat.floor_le hnon),
      (le_div_iff₀ hn).mpr (Nat.lt_floor_add_one _).le⟩

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (a : ℝ), 0 < a → a ≤ 1 → let N := ⌈1 / a⌉₊; 0 < N ∧ 1 / (N : ℝ) ≤ a ∧ (N : ℝ) * a ≤ 2" := by
  intro a ha ha1
  dsimp
  have hN : 0 < ⌈1 / a⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hNr : (0 : ℝ) < ⌈1 / a⌉₊ := by exact_mod_cast hN
  have hlo : 1 / a ≤ (⌈1 / a⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈1 / a⌉₊ : ℝ) < 1 / a + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨hN, ?_, ?_⟩
  · apply (div_le_iff₀ hNr).mpr
    have := (div_le_iff₀ ha).mp hlo
    nlinarith
  · have hh := mul_lt_mul_of_pos_right hhi ha
    have he : (1 / a + 1) * a = 1 + a := by field_simp
    rw [he] at hh
    linarith

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (U : Set X) (a : ℝ) (N : ℕ), 0 < N → Metric.ediam U ≤ ENNReal.ofReal a → 1 / (N : ℝ) ≤ a → ∀ j : Fin N, Metric.ediam (U ×ˢ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) ≤ ENNReal.ofReal a" := by
  intro X inst U a N hN hU hNa j
  apply Metric.ediam_le_iff.mpr
  intro x hx y hy
  rw [Prod.edist_eq]
  apply max_le
  · exact Metric.edist_le_of_ediam_le hx.1 hy.1 hU
  · have hJ : Metric.ediam (Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) ≤ ENNReal.ofReal a := by
      rw [Real.ediam_Icc]
      apply ENNReal.ofReal_le_ofReal
      convert hNa using 1 <;> ring
    exact Metric.edist_le_of_ediam_le hx.2 hy.2 hJ

theorem checked (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (N : ℕ) (b : ℝ), 0 ≤ b → (∑' j : Fin N, ENNReal.ofReal b) = ENNReal.ofReal ((N : ℝ) * b)" := by
  intro N b hb
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  simp
#check @checked
#print axioms checked
end YuiAuxiliary
