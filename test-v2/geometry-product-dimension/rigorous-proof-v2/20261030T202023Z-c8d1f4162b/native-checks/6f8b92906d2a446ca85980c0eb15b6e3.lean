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
theorem checked (n : ℕ) (E : Set (YEucl n))  : yui_aux_type% "∀ k : ℕ, 0 < k → YI ⊆ ⋃ j : ℕ, (if j < k then Set.Icc ((j : ℝ) / k) (((j : ℝ) + 1) / k) else ∅)" := by
  intro k hk x hx
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  simp only [Set.mem_iUnion]
  by_cases h : x < 1
  · let j := ⌊x * k⌋₊
    have hj : j < k := by
      dsimp [j]
      apply (Nat.floor_lt (by positivity : (0 : ℝ) ≤ k)).mpr
      nlinarith
    refine ⟨j, ?_⟩
    simp only [if_pos hj, Set.mem_Icc]
    constructor
    · apply (div_le_iff₀ hkR).mpr
      exact Nat.floor_le (mul_nonneg hx0 hkR.le)
    · apply (le_div_iff₀ hkR).mpr
      exact (Nat.lt_floor_add_one (x * k)).le
  · have hxE : x = 1 := le_antisymm hx1 (le_of_not_gt h)
    refine ⟨k - 1, ?_⟩
    rw [if_pos (Nat.sub_lt hk (by omega))]
    have hc : ((k - 1 : ℕ) : ℝ) + 1 = k := by
      exact_mod_cast Nat.sub_add_cancel hk
    simp only [Set.mem_Icc]
    rw [hxE]
    constructor
    · apply (div_le_iff₀ hkR).mpr
      nlinarith
    · rw [hc, div_self hkR.ne']
#check @checked
#print axioms checked
end YuiAuxiliary
