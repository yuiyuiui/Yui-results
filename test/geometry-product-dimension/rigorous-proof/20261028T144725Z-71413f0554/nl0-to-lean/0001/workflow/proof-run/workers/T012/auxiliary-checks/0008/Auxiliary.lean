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
theorem checked (n : ℕ) (E : Set (V n)) (h_T010 : 1 ≤ n → ∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ K : Set ℕ, ∃ U : K → Set (V n), E ⊆ (⋃ i, U i) ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ cost q U < ENNReal.ofReal ε) (h_T008 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ ∧ Bornology.IsBounded E ∧ (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤) ∧ (n = 0 → E = Set.univ ∧ dimH E = 0) ∧ Function.Bijective (fun p : V n × ℝ => join p.1 p.2) ∧ (∀ (x : V n) (t : ℝ), base (join x t) = x ∧ height (join x t) = t) ∧ (∀ z : V (n+1), join (base z) (height z) = z) ∧ (∀ (x y : V n) (t u : ℝ), dist (join x t) (join y u) ^ 2 = dist x y ^ 2 + dist t u ^ 2)) : yui_aux_type% "∀ (U : Set (V n)) (d : ℝ) (N : ℕ) (j : Fin N), 0 < d → Metric.ediam U ≠ ⊤ → Metric.diam U ≤ d → 0 < N → 1/(N : ℝ) ≤ d → Metric.ediam {z : V (n+1) | base z ∈ U ∧ height z ∈ Set.Icc ((j : ℕ)/(N : ℝ)) (((j : ℕ)+1 : ℝ)/N)} ≤ ENNReal.ofReal (Real.sqrt 2 * d)" := by
  intro U d N j hd hU hdiam hN hNd
  rcases h_T008 with ⟨_, _, _, _, _, _, _, _, hinv, hsq⟩
  apply Metric.ediam_le_of_forall_dist_le
  intro z hz w hw
  have hbase : dist (base z) (base w) ≤ d := (Metric.dist_le_diam_of_mem' hU hz.1 hw.1).trans hdiam
  have ht : dist (height z) (height w) ≤ 1/(N : ℝ) := by
    rw [Real.dist_eq, abs_le]
    constructor <;> dsimp only [Set.mem_Icc] at hz hw <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  have ht' := ht.trans hNd
  have hsq' : dist z w ^ 2 = dist (base z) (base w) ^ 2 + dist (height z) (height w) ^ 2 := by
    simpa only [hinv] using hsq (base z) (base w) (height z) (height w)
  have hb2 := mul_self_le_mul_self dist_nonneg hbase
  have ht2 := mul_self_le_mul_self dist_nonneg ht'
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : 0 ≤ Real.sqrt 2 * d := by positivity
  nlinarith [dist_nonneg (x := z) (y := w)]
#check @checked
#print axioms checked
end YuiAuxiliary
