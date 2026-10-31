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
theorem checked (n : ℕ) (E : Set (YEucl n)) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T016 : ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEucl (n+1)), YCover δ (YF E) V → ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ, (∀ i, IsOpen (J i)) ∧ (∀ i, YLast '' (V i) ⊆ J i) ∧ (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (ε * (2 : ℝ) ^ (-(i : ℤ)-1) / (1 + (Metric.ediam (V i)).toReal ^ s))) ∧ (∀ t ∈ YI, YContent s δ E ≤ ∑' i, (Metric.ediam (V i)) ^ s * (J i).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t)) : yui_aux_type% "∀ (r : ℝ≥0∞) (s a : ℝ), r ≠ ⊤ → 0 < s → 0 ≤ a → r ^ s * ENNReal.ofReal (a / (1 + r.toReal ^ s)) ≤ ENNReal.ofReal a" := by
  intro r s a hr hs ha
  have hc : ENNReal.ofReal (r.toReal ^ s) = r ^ s := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le,
      ENNReal.ofReal_toReal hr]
  rw [← hc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg s)]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ r.toReal ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg s
  have hd : 0 < 1 + r.toReal ^ s := by positivity
  apply (le_div_iff₀ hd).mp
  convert (mul_le_mul_of_nonneg_left (show r.toReal ^ s ≤ 1 + r.toReal ^ s by linarith) ha) using 1 <;> field_simp <;> ring
#check @checked
#print axioms checked
end YuiAuxiliary
