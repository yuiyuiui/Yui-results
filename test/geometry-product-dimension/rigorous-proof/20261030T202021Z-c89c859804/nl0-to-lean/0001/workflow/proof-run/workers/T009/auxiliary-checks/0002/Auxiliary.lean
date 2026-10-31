import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T008 : 1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ U : ℕ → Set (GPEucl n),
    GPcover E r U ∧
    (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧
    GPcost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (d : ℝ), 0 < d → d ≤ 1 →\n  let N := ⌈1 / d⌉₊\n  0 < N ∧ 1 / (N : ℝ) ≤ d ∧ (N : ℝ) * d ≤ 2 ∧\n  ∀ t ∈ GPI, ∃ j : ℕ, j < N ∧ (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N" := by
  intro d hd hd1 N
  have hceil : 1 / d ≤ (N : ℝ) := Nat.le_ceil _
  have hNreal : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity) hceil
  have hN : 0 < N := by exact_mod_cast hNreal
  refine ⟨hN, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hNreal).2
    have := (div_le_iff₀ hd).1 hceil
    nlinarith
  · have hlt : (N : ℝ) < 1 / d + 1 := Nat.ceil_lt_add_one (by positivity)
    have hmul := (mul_lt_mul_of_pos_right hlt hd)
    have heq : (1 / d + 1) * d = 1 + d := by field_simp
    rw [heq] at hmul
    linarith
  · intro t ht
    change 0 ≤ t ∧ t ≤ 1 at ht
    by_cases ht0 : t = 0
    · refine ⟨0, hN, ?_, ?_⟩ <;> simp [ht0, hNreal.le]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      let m := ⌈t * (N : ℝ)⌉₊
      have hmlo : t * (N : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
      have hmhi : (m : ℝ) < t * (N : ℝ) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hmpos : 0 < m := by
        have : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hmlo
        exact_mod_cast this
      have hmN : m ≤ N := by
        dsimp [m]
        exact Nat.ceil_le.2 (by nlinarith [ht.2])
      refine ⟨m - 1, by omega, ?_, ?_⟩
      · apply (div_le_iff₀ hNreal).2
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
        linarith
      · apply (le_div_iff₀ hNreal).2
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
        linarith
#check @checked
#print axioms checked
end YuiAuxiliary
