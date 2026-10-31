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
theorem checked (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) : yui_aux_type% "∀ (hn : 1 ≤ n) (q r η : ℝ), 0 < q → 0 < r → 0 < η → ∀ x : YEucl n, ∃ a : ℝ, 0 < a ∧ Metric.ediam (Metric.ball x a) ≤ ENNReal.ofReal r ∧ 0 < Metric.ediam (Metric.ball x a) ∧ (Metric.ediam (Metric.ball x a)) ^ q < ENNReal.ofReal η" := by
  intro hn q r η hq hr hη x
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let b : ℝ := min r (η ^ q⁻¹) / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbr : b ≤ r := by
    have := min_le_left r (η ^ q⁻¹)
    dsimp [b]
    linarith [lt_min hr (Real.rpow_pos_of_pos hη q⁻¹)]
  have hbη : b < η ^ q⁻¹ := by
    have := min_le_right r (η ^ q⁻¹)
    dsimp [b]
    linarith [lt_min hr (Real.rpow_pos_of_pos hη q⁻¹)]
  have hd : Metric.ediam (Metric.ball x (b / 2)) = ENNReal.ofReal b := by
    have hh := Metric.diam_ball_eq x (show 0 ≤ b / 2 by positivity)
    have he : Metric.ediam (Metric.ball x (b / 2)) ≠ ⊤ :=
      Metric.isBounded_ball.ediam_ne_top
    calc
      Metric.ediam (Metric.ball x (b / 2)) =
        ENNReal.ofReal (Metric.diam (Metric.ball x (b / 2))) :=
          (ENNReal.ofReal_toReal he).symm
      _ = ENNReal.ofReal b := by rw [hh]; congr 1; ring
  refine ⟨b / 2, by positivity, ?_, ?_, ?_⟩
  · rw [hd]; exact ENNReal.ofReal_le_ofReal hbr
  · rw [hd]; exact ENNReal.ofReal_pos.mpr hb
  · rw [hd, ENNReal.ofReal_rpow_of_pos hb]
    apply (ENNReal.ofReal_lt_ofReal_iff hη).mpr
    calc b ^ q < (η ^ q⁻¹) ^ q := Real.rpow_lt_rpow hb.le hbη hq
         _ = η := Real.rpow_inv_rpow hη.le hq.ne'
#check @checked
#print axioms checked
end YuiAuxiliary
