import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ (r : ℝ), 0 < r → r ≤ 1 →\n  ∃ (N : ℕ) (J : Fin N → Set ℝ), 0 < N ∧\n    (↑N : ℝ) ≤ 2 / r ∧\n    GP.unitInterval ⊆ ⋃ j, J j ∧\n    (∀ j, Metric.ediam (J j) ≤ ENNReal.ofReal r)" := by
  intro r hr hr1
  let N : ℕ := ⌈1 / r⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (one_div_pos.mpr hr)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hceil : 1 / r ≤ (N : ℝ) := Nat.le_ceil _
  have hsize : (N : ℝ) ≤ 2 / r := by
    have h := (Nat.ceil_lt_add_one (le_of_lt (one_div_pos.mpr hr))).le
    have h1 : 1 ≤ 1 / r := (le_div_iff₀ hr).mpr (by simpa using hr1)
    dsimp [N]
    calc _ ≤ 1 / r + 1 := h
         _ ≤ 1 / r + 1 / r := add_le_add_right h1 _
         _ = 2 / r := by ring
  have hinv : 1 / (N : ℝ) ≤ r := by
    apply (div_le_iff₀ hNr).mpr
    have h := (div_le_iff₀ hr).mp hceil
    nlinarith
  let J : Fin N → Set ℝ := fun j => Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
  refine ⟨N, J, hN, hsize, ?_, ?_⟩
  · have cov : ∀ k : ℕ, k ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ (k : ℝ) / N →
        ∃ j : Fin N, t ∈ J j := by
      intro k
      induction k with
      | zero =>
        intro _ t ht ht'
        have ht0 : t ≤ 0 := by simpa using ht'
        have ht0 : t = 0 := le_antisymm ht0 ht
        subst t
        refine ⟨⟨0, hN⟩, ?_⟩
        simp [J, le_of_lt (one_div_pos.mpr hNr)]
      | succ k ih =>
        intro hk t ht ht'
        by_cases htk : t ≤ (k : ℝ) / N
        · exact ih (by omega) t ht htk
        · refine ⟨⟨k, by omega⟩, ?_, ?_⟩
          · exact (lt_of_not_ge htk).le
          · simpa [Nat.cast_add, Nat.cast_one] using ht'
    intro t ht
    obtain ⟨j, hj⟩ := cov N le_rfl t ht.1 (by simpa [ne_of_gt hNr] using ht.2)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  · intro j
    dsimp [J]
    rw [Real.ediam_Icc]
    apply ENNReal.ofReal_le_ofReal
    calc ((j : ℝ) + 1) / N - (j : ℝ) / N = 1 / N := by ring
         _ ≤ r := hinv
#check @checked
#print axioms checked
end YuiAuxiliary
