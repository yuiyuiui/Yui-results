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
theorem checked (n : ℕ) (E : Set (V n)) (h_H002 : E.Nonempty) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) (h_T005 : (∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ R) ∧ Bornology.IsBounded E ∧ (∀ s δ : ℝ, 0 < s → 0 < δ → content s δ E < ⊤)) : yui_aux_type% "∀ (R h : ℝ), (∀ x ∈ E, ∀ j : Fin n, |x j| < R) → 0 < R → 0 < h → let m := ⌈2*R/h⌉₊; let t : (Fin n → Fin m) → Set (V n) := fun f => {x | ∀ j, x j ∈ Set.Icc (-R + (f j : ℕ)*h) (-R + ((f j : ℕ)+1)*h)}; E ⊆ ⋃ f, t f ∧ ∀ f, Metric.ediam (t f) ≤ ENNReal.ofReal (Real.sqrt n * h)" := by
  intro R h hR hRp hh m t
  constructor
  · intro x hx
    let f : Fin n → Fin m := fun j => ⟨⌊(x j + R)/h⌋₊, by
      apply Nat.floor_lt_ceil_of_lt_of_pos
      · exact (div_lt_div_iff_of_pos_right hh).2 (by linarith [(abs_lt.1 (hR x hx j)).2])
      · positivity⟩
    refine Set.mem_iUnion.2 ⟨f, ?_⟩
    intro j
    have hnon : 0 ≤ (x j + R)/h := div_nonneg (by linarith [(abs_lt.1 (hR x hx j)).1]) hh.le
    have hlo := Nat.floor_le hnon
    have hhi := Nat.lt_floor_add_one ((x j + R)/h)
    dsimp [t, f]
    constructor
    · have := (le_div_iff₀ hh).1 hlo
      linarith
    · have := (div_lt_iff₀ hh).1 hhi
      linarith
  · intro f
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    rw [EuclideanSpace.dist_eq]
    calc
      Real.sqrt (∑ j, dist (x j) (y j) ^ 2) ≤ Real.sqrt (∑ _j : Fin n, h^2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro j _
        have hxy : dist (x j) (y j) ≤ h := by
          rw [Real.dist_eq, abs_le]
          have hxj := hx j
          have hyj := hy j
          constructor <;> linarith
        exact pow_le_pow_left₀ dist_nonneg hxy 2
      _ = Real.sqrt n * h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hh.le]
#check @checked
#print axioms checked
end YuiAuxiliary
