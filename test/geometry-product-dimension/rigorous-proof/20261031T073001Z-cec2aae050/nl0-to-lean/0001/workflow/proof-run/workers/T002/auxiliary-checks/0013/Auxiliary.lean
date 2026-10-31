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
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ (K a : ℝ), 0 ≤ K → (n : ℝ) < a → (∀ k : ℕ, 0 < k → (k : ℝ≥0∞) ^ n * (ENNReal.ofReal (K / k)) ^ a = ENNReal.ofReal (K ^ a / (k : ℝ) ^ (a - n))) ∧ Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (K ^ a / (k : ℝ) ^ (a - n))) Filter.atTop (nhds 0)" := by
  intro K a hK ha
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
  constructor
  · intro k hk
    have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    have he : (k : ℝ) ^ n * (K / k) ^ a = K ^ a / (k : ℝ) ^ (a - n) := by
      rw [Real.div_rpow hK hkR.le, Real.rpow_sub hkR a (n : ℝ), Real.rpow_natCast]
      have hnz : (k : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hkR a).ne'
      field_simp
    rw [← ENNReal.ofReal_rpow_of_nonneg (div_nonneg hK hkR.le) ha0.le]
    rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_pow hkR.le, ← ENNReal.ofReal_mul (pow_nonneg hkR.le n), he]
  · have ht : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (a - n)) Filter.atTop Filter.atTop :=
      (Real.tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
    have hz : Filter.Tendsto (fun k : ℕ => K ^ a / (k : ℝ) ^ (a - n)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop ht
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hz
#check @checked
#print axioms checked
end YuiAuxiliary
