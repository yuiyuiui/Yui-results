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
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (N : ℕ) (d : ℝ), 0 < N → 0 ≤ d → ∀ x ∈ Set.Icc (0 : ℝ) ((N : ℝ) * d), ∃ i : ℕ, i < N ∧ x ∈ Set.Icc ((i : ℝ) * d) (((i : ℝ) + 1) * d)" := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    intro d hN hd x hx
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, by simpa using hx⟩
    · by_cases hle : x ≤ (N : ℝ) * d
      · obtain ⟨i, hi, hxi⟩ := ih d (Nat.pos_of_ne_zero hzero) hd x ⟨hx.1, hle⟩
        exact ⟨i, by omega, hxi⟩
      · refine ⟨N, by omega, le_of_lt (lt_of_not_ge hle), ?_⟩
        simpa only [Nat.cast_succ] using hx.2

theorem checked (n : ℕ) (E : Set (YuiEucl n))  : yui_aux_type% "∀ (a : ℝ) (N : ℕ), 1 < a → 0 < N → (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a = ENNReal.ofReal ((N : ℝ) ^ (1 - a))" := by
  intro a N ha hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hconv : ENNReal.ofReal ((1 / (N : ℝ)) ^ a) = (ENNReal.ofReal (1 / (N : ℝ))) ^ a :=
    ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNp)
  rw [← hconv, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNp.le]
  congr 1
  rw [Real.rpow_sub hNp, Real.rpow_one, one_div, Real.inv_rpow hNp.le]
  rfl
#check @checked
#print axioms checked
end YuiAuxiliary
