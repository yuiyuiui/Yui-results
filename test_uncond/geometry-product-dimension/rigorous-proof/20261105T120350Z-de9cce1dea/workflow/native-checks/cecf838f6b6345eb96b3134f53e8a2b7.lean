import Mathlib
open scoped ENNReal NNReal Topology
open Set MeasureTheory
namespace BasisObjects
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def content {X : Type*} [EMetricSpace X]
    (s : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def euclideanLift (n : ℕ) : Rn n × ℝ → WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2
end BasisObjects

namespace IntervalProduct
abbrev Rn := BasisObjects.Rn
def I : Set ℝ := Set.Icc 0 1
def F (n : ℕ) (E : Set (Rn n)) : Set (Rn n × ℝ) := E ×ˢ I
def j (n : ℕ) (p : WithLp 2 (Rn n × ℝ)) : Rn (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => p.fst i) p.snd)
def unj (n : ℕ) (v : Rn (n + 1)) : WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun i : Fin n => v i.castSucc), v (Fin.last n))
def G (n : ℕ) (E : Set (Rn n)) : Set (Rn (n + 1)) :=
  j n '' (BasisObjects.euclideanLift n '' F n E)
noncomputable def H {X : Type*} [MetricSpace X] (a : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  MeasureTheory.Measure.hausdorffMeasure a A
noncomputable def cost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ a
noncomputable def realCost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, (ENNReal.ofReal (Metric.diam (U i))) ^ a
def Cover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def RealCover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ (∀ i, Bornology.IsBounded (U i)) ∧ ∀ i, Metric.diam (U i) ≤ δ
end IntervalProduct
open IntervalProduct

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (a : ℝ) (V : ℕ → Set X), 0 < a → cost a V = ∑' i, (Metric.ediam (V i)) ^ a" := by
  intro X _ a V ha
  unfold cost
  apply tsum_congr
  intro i
  by_cases hi : (V i).Nonempty
  · simp [hi]
  · have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp [he, ENNReal.zero_rpow_of_pos ha]

theorem yui_aux_0002 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (a q : ℝ), 0 ≤ a → 0 ≤ q → (ENNReal.ofReal a) ^ q = ENNReal.ofReal (a ^ q)" := by
  intro a q ha hq
  exact ENNReal.ofReal_rpow_of_nonneg ha hq

theorem yui_aux_0003 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (q r ε : ℝ) (d : ℕ → ℝ), 0 < q → 0 < r → 0 < ε → (∀ i, 0 ≤ d i ∧ d i ≤ r) → (∑' i, (ENNReal.ofReal (d i)) ^ q) < ENNReal.ofReal (ε / 4) → ∃ t : ℕ → ℝ, (∀ i, 0 < t i ∧ d i ≤ t i ∧ t i ≤ r) ∧ (∑' i, (ENNReal.ofReal (t i)) ^ q) < ENNReal.ofReal (ε / 2)" := by
  intro q r ε d hq hr hε hd hsum
  let b : ℕ → ℝ := fun i => (ε / 4) / 2 / 2 ^ i
  have hb : ∀ i, 0 < b i := fun i => by dsimp [b]; positivity
  let a : ℕ → ℝ := fun i => min r ((b i) ^ q⁻¹)
  have ha : ∀ i, 0 < a i := fun i => lt_min hr (Real.rpow_pos_of_pos (hb i) _)
  have haq : ∀ i, (ENNReal.ofReal (a i)) ^ q ≤ ENNReal.ofReal (b i) := by
    intro i
    rw [@yui_aux_0002 n E h_T001 (a i) q (ha i).le hq.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      (a i) ^ q ≤ ((b i) ^ q⁻¹) ^ q :=
        Real.rpow_le_rpow (ha i).le (min_le_right _ _) hq.le
      _ = b i := Real.rpow_inv_rpow (hb i).le hq.ne'
  have hbsum : (∑' i, ENNReal.ofReal (b i)) = ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hb i).le) (summable_geometric_two' (ε / 4))]
    congr 1
    exact tsum_geometric_two' (ε / 4)
  let t : ℕ → ℝ := fun i => max (d i) (a i)
  refine ⟨t, ?_, ?_⟩
  · intro i
    exact ⟨(ha i).trans_le (le_max_right _ _), le_max_left _ _,
      max_le (hd i).2 (min_le_left _ _)⟩
  · have ht : ∀ i, (ENNReal.ofReal (t i)) ^ q ≤
        (ENNReal.ofReal (d i)) ^ q + (ENNReal.ofReal (a i)) ^ q := by
      intro i
      dsimp [t]
      rw [ENNReal.ofReal_max, ENNReal.max_rpow hq.le]
      exact max_le (le_add_right le_rfl) (le_add_left le_rfl)
    calc
      (∑' i, (ENNReal.ofReal (t i)) ^ q) ≤
          ∑' i, ((ENNReal.ofReal (d i)) ^ q + (ENNReal.ofReal (a i)) ^ q) := ENNReal.tsum_le_tsum ht
      _ = (∑' i, (ENNReal.ofReal (d i)) ^ q) + ∑' i, (ENNReal.ofReal (a i)) ^ q := ENNReal.tsum_add
      _ ≤ (∑' i, (ENNReal.ofReal (d i)) ^ q) + ENNReal.ofReal (ε / 4) := by
        exact add_le_add le_rfl ((ENNReal.tsum_le_tsum haq).trans_eq hbsum)
      _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hsum
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem yui_aux_0004 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (N : ℕ), 0 < N → ∀ x : ℝ, x ∈ I → ∃ h : Fin N, x ∈ Set.Icc ((h : ℝ) / N) (((h : ℝ) + 1) / N)" := by
  intro N hN x hx
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  by_cases hlt : x < 1
  · have hprod : 0 ≤ (N : ℝ) * x := mul_nonneg hNR.le hx0
    have hk : ⌊(N : ℝ) * x⌋₊ < N := (Nat.floor_lt hprod).mpr (by nlinarith)
    refine ⟨⟨_, hk⟩, ?_, ?_⟩
    · exact (div_le_iff₀ hNR).mpr (by simpa [mul_comm] using Nat.floor_le hprod)
    · exact (le_div_iff₀ hNR).mpr (by simpa [mul_comm] using (Nat.lt_floor_add_one ((N : ℝ) * x)).le)
  · have hxE : x = 1 := le_antisymm hx1 (le_of_not_gt hlt)
    have hk : N - 1 < N := by omega
    refine ⟨⟨N - 1, hk⟩, ?_, ?_⟩
    · rw [hxE]
      apply (div_le_iff₀ hNR).mpr
      have : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
      simpa using this
    · rw [hxE]
      apply (le_div_iff₀ hNR).mpr
      have : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel hN : N - 1 + 1 = N)
      simp only [Fin.val_mk, one_mul]
      exact this.ge

theorem yui_aux_0005 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ t : ℝ, 0 < t → t ≤ 1 → let N := ⌈1 / t⌉₊; 0 < N ∧ 1 / (N : ℝ) ≤ t ∧ (N : ℝ) * t ≤ 2" := by
  intro t ht ht1
  dsimp
  have hi : 0 < 1 / t := by positivity
  have hn : 0 < ⌈1 / t⌉₊ := Nat.ceil_pos.mpr hi
  have hnR : 0 < (⌈1 / t⌉₊ : ℝ) := by exact_mod_cast hn
  have hle : 1 / t ≤ (⌈1 / t⌉₊ : ℝ) := Nat.le_ceil _
  have hmul : 1 ≤ (⌈1 / t⌉₊ : ℝ) * t := (div_le_iff₀ ht).mp hle
  refine ⟨hn, (div_le_iff₀ hnR).mpr (by nlinarith), ?_⟩
  have hlt := Nat.ceil_lt_add_one hi.le
  have hupper : (⌈1 / t⌉₊ : ℝ) * t < (1 / t + 1) * t := mul_lt_mul_of_pos_right hlt ht
  have heq : (1 / t + 1) * t = 1 + t := by field_simp
  rw [heq] at hupper
  linarith

theorem yui_aux_0006 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (V : Set X) (t : ℝ) (N : ℕ) (h : Fin N), 0 ≤ t → 0 < N → Metric.ediam V ≤ ENNReal.ofReal t → 1 / (N : ℝ) ≤ t → Metric.ediam (V ×ˢ Set.Icc ((h : ℝ) / N) (((h : ℝ) + 1) / N)) ≤ ENNReal.ofReal t" := by
  intro X _ V t N h ht hN hd hstep
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  apply Metric.ediam_le
  intro x hx y hy
  apply (edist_le_ofReal ht).mpr
  rw [Prod.dist_eq]
  apply max_le
  · exact (edist_le_ofReal ht).mp (Metric.edist_le_of_ediam_le hx.1 hy.1 hd)
  · rw [Real.dist_eq, abs_sub_le_iff]
    have hlen : (((h : ℝ) + 1) / N) - ((h : ℝ) / N) = 1 / (N : ℝ) := by ring
    constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]

theorem yui_aux_0007 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (q t : ℝ) (N : ℕ), 0 ≤ q → 0 < t → (N : ℝ) * t ≤ 2 → (N : ℝ≥0∞) * (ENNReal.ofReal t) ^ (q + 1) ≤ 2 * (ENNReal.ofReal t) ^ q" := by
  intro q t N hq ht hN
  rw [ENNReal.rpow_add_of_nonneg q 1 hq zero_le_one, ENNReal.rpow_one]
  calc
    (N : ℝ≥0∞) * (ENNReal.ofReal t ^ q * ENNReal.ofReal t) =
        ((N : ℝ≥0∞) * ENNReal.ofReal t) * ENNReal.ofReal t ^ q := by ring
    _ ≤ 2 * ENNReal.ofReal t ^ q := by
      apply mul_le_mul' _ le_rfl
      have hc : (N : ℝ≥0∞) * ENNReal.ofReal t = ENNReal.ofReal ((N : ℝ) * t) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
        simp
      rw [hc]
      exact_mod_cast ENNReal.ofReal_le_ofReal hN

theorem checked (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T001 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (q δ : ℝ)\n    (V : ℕ → Set X) (t : ℕ → ℝ), 0 < q →\n    A ⊆ ⋃ i, V i →\n    (∀ i, 0 < t i ∧ t i ≤ 1 ∧ t i ≤ δ ∧ Metric.ediam (V i) ≤ ENNReal.ofReal (t i)) →\n    ∃ U : ℕ → Set (X × ℝ), Cover δ (A ×ˢ I) U ∧\n      cost (q + 1) U ≤ 2 * ∑' i, (ENNReal.ofReal (t i)) ^ q" := by
  intro X _ A q δ V t hq hcover ht
  classical
  have hq1 : 0 < q + 1 := by linarith
  let N : ℕ → ℕ := fun i => ⌈1 / t i⌉₊
  have hN : ∀ i, 0 < N i ∧ 1 / (N i : ℝ) ≤ t i ∧ (N i : ℝ) * t i ≤ 2 :=
    fun i => @yui_aux_0005 n E h_T001 (t i) (ht i).1 (ht i).2.1
  let W : (Σ i : ℕ, Fin (N i)) → Set (X × ℝ) := fun k =>
    V k.1 ×ˢ Set.Icc ((k.2 : ℝ) / N k.1) (((k.2 : ℝ) + 1) / N k.1)
  have hWdiam : ∀ k, Metric.ediam (W k) ≤ ENNReal.ofReal (t k.1) := by
    intro k
    exact @yui_aux_0006 n E h_T001 X _ (V k.1) (t k.1) (N k.1) k.2
      (ht k.1).1.le (hN k.1).1 (ht k.1).2.2.2 (hN k.1).2.1
  have hWcover : A ×ˢ I ⊆ ⋃ k, W k := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx.1)
    obtain ⟨h, hh⟩ := @yui_aux_0004 n E h_T001 (N i) (hN i).1 x.2 hx.2
    exact Set.mem_iUnion.mpr ⟨⟨i, h⟩, hi, hh⟩
  have hWcost : cost (q + 1) W ≤ 2 * ∑' i, (ENNReal.ofReal (t i)) ^ q := by
    unfold cost
    calc
      (∑' k, ⨆ (_ : (W k).Nonempty), Metric.ediam (W k) ^ (q + 1)) ≤
          ∑' k : (Σ i : ℕ, Fin (N i)), (ENNReal.ofReal (t k.1)) ^ (q + 1) := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact iSup_le fun _ => ENNReal.rpow_le_rpow (hWdiam k) hq1.le
      _ = ∑' i, (N i : ℝ≥0∞) * (ENNReal.ofReal (t i)) ^ (q + 1) := by
        rw [ENNReal.tsum_sigma]
        congr 1
        funext i
        simp [tsum_fintype, nsmul_eq_mul]
      _ ≤ ∑' i, 2 * (ENNReal.ofReal (t i)) ^ q :=
        ENNReal.tsum_le_tsum fun i => @yui_aux_0007 n E h_T001 q (t i) (N i)
          hq.le (ht i).1 (hN i).2.2
      _ = 2 * ∑' i, (ENNReal.ofReal (t i)) ^ q := ENNReal.tsum_mul_left
  obtain ⟨e, U, he, hempty, hunion, hcost, _⟩ :=
    (h_T001 (X × ℝ) (A ×ˢ I) (q + 1) hq1).2.1 (Σ i : ℕ, Fin (N i)) W
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · rw [hunion]
    exact hWcover
  · intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hi
      rw [he k]
      exact (hWdiam k).trans (ENNReal.ofReal_le_ofReal (ht k.1).2.2.1)
    · rw [hempty i hi]
      simp
  · rw [hcost]
    exact hWcost
#check @checked
#print axioms checked
end YuiAuxiliary
