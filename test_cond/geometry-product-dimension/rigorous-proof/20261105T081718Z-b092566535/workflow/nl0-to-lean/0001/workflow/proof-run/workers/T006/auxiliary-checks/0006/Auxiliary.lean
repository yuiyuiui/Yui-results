import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "n = 0 → ∃ x : YuiEucl n, E = {x} ∧ Isometry (YuiSnoc x) ∧ YuiCylinder E = (YuiSnoc x) '' YuiI ∧ dimH E = 0" := by
  intro hn
  subst n
  obtain ⟨x, hx⟩ := h_H002
  have hE : E = {x} := by
    ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · intro _; exact Subsingleton.elim _ _
    · rintro rfl; exact hx
  refine ⟨x, hE, ?_, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro t u
    rw [(h_T003 0).2.2.1 x x t u]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  · ext z
    constructor
    · intro hz
      refine ⟨YuiLast z, hz.2, ?_⟩
      have hh : YuiHead z = x := Subsingleton.elim _ _
      simpa only [hh] using (h_T003 0).2.1 z
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(h_T003 0).1 x t |>.1 ▸ hx, (h_T003 0).1 x t |>.2 ▸ ht⟩
  · have h0 : dimH E ≤ 0 := by simpa only [Nat.cast_zero] using h_T005.1.2.1
    exact le_antisymm h0 zero_le

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (N : ℕ), 0 < N → (Set.Icc (0 : ℝ) 1) ⊆ ⋃ j : Fin N, Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro N hN t ht
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  by_cases ht1 : t = 1
  · subst t
    refine Set.mem_iUnion.mpr ⟨⟨N-1, by omega⟩, ?_⟩
    have hc : ((N-1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast (Nat.sub_add_cancel hN)
    constructor
    · apply (div_le_iff₀ hNr).mpr
      nlinarith
    · apply (le_div_iff₀ hNr).mpr
      nlinarith
  · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hfloor : ⌊t * N⌋₊ < N := by
      apply (Nat.floor_lt (mul_nonneg ht.1 hNr.le)).mpr
      nlinarith
    refine Set.mem_iUnion.mpr ⟨⟨⌊t * N⌋₊, hfloor⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ hNr).mpr
      exact Nat.floor_le (mul_nonneg ht.1 hNr.le)
    · apply (le_div_iff₀ hNr).mpr
      exact (Nat.lt_floor_add_one (t*N)).le

theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_H002 : E.Nonempty) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (x : YuiEucl n), Isometry (YuiSnoc x) → ∀ (N : ℕ), 0 < N → ∀ j : Fin N, Metric.ediam ((YuiSnoc x) '' Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) = 1 / (N : ℝ≥0∞)" := by
  intro x hi N hN j
  rw [hi.ediam_image, Real.ediam_Icc]
  have hlen : (((j : ℝ) + 1) / N) - ((j : ℝ) / N) = 1 / (N : ℝ) := by ring
  rw [hlen, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hN)]
  simp
#check @checked
#print axioms checked
end YuiAuxiliary
