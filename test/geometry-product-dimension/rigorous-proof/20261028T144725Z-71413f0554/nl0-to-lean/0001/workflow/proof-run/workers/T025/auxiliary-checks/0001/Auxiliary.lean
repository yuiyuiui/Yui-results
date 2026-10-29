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
theorem checked (n : ℕ) (E : Set (V n)) (h_T024 : ∀ (δ : ℝ) (W : ℕ → Set ℝ), 0 < δ → scaleCover δ unitI W → (1 : ℝ≥0∞) ≤ cost 1 W) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) : yui_aux_type% "∀ (s δ : ℝ) (r : ℝ≥0∞), 0 < s → s < 1 → 0 < δ → r ≤ ENNReal.ofReal δ → ENNReal.ofReal (δ ^ (s-1)) * r ≤ r ^ s" := by
  intro s δ r hs hs1 hd hr
  have hrfin : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr
  have hrδ : r.toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hd.le hr
  have hre : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrfin
  have hreal : δ ^ (s-1) * r.toReal ≤ r.toReal ^ s := by
    by_cases hz : r.toReal = 0
    · simp [hz, Real.zero_rpow (ne_of_gt hs)]
    · have hp : 0 < r.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
      have hpow := Real.rpow_le_rpow_of_nonpos hp hrδ (by linarith : s-1 ≤ 0)
      calc
        δ ^ (s-1) * r.toReal ≤ r.toReal ^ (s-1) * r.toReal := mul_le_mul_of_nonneg_right hpow hp.le
        _ = r.toReal ^ s := by rw [Real.rpow_sub_one hz, div_mul_cancel₀ _ hz]
  calc
    ENNReal.ofReal (δ ^ (s-1)) * r = ENNReal.ofReal (δ ^ (s-1) * r.toReal) := by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), hre]
    _ ≤ ENNReal.ofReal (r.toReal ^ s) := ENNReal.ofReal_le_ofReal hreal
    _ = r ^ s := by rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le, hre]
#check @checked
#print axioms checked
end YuiAuxiliary
