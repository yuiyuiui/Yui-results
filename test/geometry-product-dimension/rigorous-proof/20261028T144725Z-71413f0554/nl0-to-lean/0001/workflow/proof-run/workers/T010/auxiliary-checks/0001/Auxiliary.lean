import Mathlib
open scoped ENNReal NNReal
open Set MeasureTheory
abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def base {n : ℕ} (z : V (n+1)) : V n := WithLp.toLp 2 (fun i => z i.castSucc)
def height {n : ℕ} (z : V (n+1)) : ℝ := z (Fin.last n)
noncomputable def join {n : ℕ} (x : V n) (t : ℝ) : V (n+1) := WithLp.toLp 2 (Fin.lastCases t (fun i => x i))
def unitI : Set ℝ := Set.Icc 0 1
def cylinder {n : ℕ} (E : Set (V n)) : Set (V (n+1)) := {z | base z ∈ E ∧ height z ∈ unitI}
def scaleCover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop := A ⊆ (⋃ i, U i) ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [MetricSpace X] {K : Type*} (s : ℝ) (U : K → Set X) : ℝ≥0∞ := ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ := ⨅ (U : ℕ → Set X) (_ : scaleCover δ A U), cost s U
noncomputable def haus {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ := ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
noncomputable def padding {X : Type*} [MetricSpace X] (ε s : ℝ) (W : ℕ → Set X) (i : ℕ) : ℝ := ε * (2 : ℝ) ^ (-(i : ℝ)-1) / (1 + (Metric.diam (W i)) ^ s)
structure ScaleLaws : Prop where
  native_eq : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (s : ℝ), 0 < s → haus s A = MeasureTheory.Measure.hausdorffMeasure s A
  antitone : ∀ {X : Type} [MetricSpace X] (A : Set X) (s δ r : ℝ), 0 < s → 0 < δ → δ ≤ r → content s r A ≤ content s δ A
  supremum : ∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ), haus s A = ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
  unbounded : ∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ), 0 < s → haus s A = ⊤ → ∀ B : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ ≤ r → ENNReal.ofReal B < content s δ A
structure CriticalLaws : Prop where
  nonneg : ∀ {X : Type} [MetricSpace X] (A : Set X), 0 ≤ dimH A
  critical : ∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ), 0 < s → ((ENNReal.ofReal s < dimH A → haus s A = ⊤) ∧ (dimH A < ENNReal.ofReal s → haus s A = 0) ∧ (haus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧ (haus s A = ⊤ → ENNReal.ofReal s ≤ dimH A))
structure InvarianceLaws : Prop where
  mono : ∀ {X : Type} [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B
  isometry : ∀ {X Y : Type} [MetricSpace X] [MetricSpace Y] (A : Set X) (f : A → Y), Isometry f → (dimH (Set.range f) = dimH A ∧ ∀ s : ℝ, 0 < s → haus s (Set.range f) = haus s A)
structure PowerLaws : Prop where
  positive_limit : ∀ a : ℝ, 0 < a → Filter.Tendsto (fun h : ℝ => h ^ a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  negative_limit : ∀ b : ℝ, b < 0 → Filter.Tendsto (fun h : ℝ => h ^ b) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop
  series_one : (∑' i : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ)-1))) = 1
  series_half : (∑' i : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ)-2))) = (1/2 : ℝ≥0∞)

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (V n)) (h_T009 : 1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (V n), scaleCover r E W ∧ cost q W < ENNReal.ofReal (ε/2)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) : yui_aux_type% "∀ (hn : 1 ≤ n) (q r a : ℝ), 0 < q → 0 < r → 0 < a → ∀ c : V n, ∃ B : Set (V n), c ∈ B ∧ B.Nonempty ∧ 0 < Metric.ediam B ∧ Metric.ediam B ≤ ENNReal.ofReal r ∧ (Metric.ediam B)^q ≤ ENNReal.ofReal a" := by
  intro hn q r a hq hr ha c
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let d : ℝ := min (r / 2) (a ^ q⁻¹)
  have hd : 0 < d := lt_min (by positivity) (Real.rpow_pos_of_pos ha _)
  have hdiam : Metric.diam (Metric.closedBall c (d / 2)) = d := by
    rw [Metric.diam_closedBall_eq c (by positivity)]
    ring
  have hediam : Metric.ediam (Metric.closedBall c (d / 2)) = ENNReal.ofReal d := by
    rw [← hdiam, Metric.diam, ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top]
  have hpow : d ^ q ≤ a := by
    calc
      d ^ q ≤ (a ^ q⁻¹) ^ q := Real.rpow_le_rpow hd.le (min_le_right _ _) hq.le
      _ = a := Real.rpow_inv_rpow ha.le hq.ne'
  refine ⟨Metric.closedBall c (d/2), Metric.mem_closedBall_self (by positivity), ⟨c, Metric.mem_closedBall_self (by positivity)⟩, ?_, ?_, ?_⟩
  · rw [hediam]; exact ENNReal.ofReal_pos.mpr hd
  · rw [hediam]; exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (by linarith))
  · rw [hediam, ← ENNReal.ofReal_rpow_of_nonneg hd.le hq.le]
    exact ENNReal.ofReal_le_ofReal hpow
#check @checked
#print axioms checked
end YuiAuxiliary
