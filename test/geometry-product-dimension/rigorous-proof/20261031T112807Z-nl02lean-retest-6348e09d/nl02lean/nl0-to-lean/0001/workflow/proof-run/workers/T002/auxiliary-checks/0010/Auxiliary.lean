import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (YEuclid n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) : yui_aux_type% "∀ B : ℕ, 0 < B → MeasureTheory.Measure.hausdorffMeasure (n : ℝ) (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(B : ℝ)) B)) < ⊤" := by
  classical
  intro B hB
  open Filter in
    let γ := fun m : ℕ => Fin n → Fin (2 * B * m)
    let t : ∀ m : ℕ, γ m → Set (Fin n → ℝ) := fun m f =>
      Set.pi Set.univ (fun i => Set.Icc (-(B : ℝ) + f i / m) (-(B : ℝ) + (f i + 1) / m))
    have hd : ∀ᶠ m : ℕ in Filter.atTop, ∀ f : γ m, Metric.ediam (t m f) ≤ 1 / (m : ℝ≥0∞) := by
      refine Filter.eventually_atTop.mpr ⟨1, fun m hm f => ?_⟩
      refine Metric.ediam_pi_le_of_le fun i => ?_
      simp only [t, Real.ediam_Icc, add_div, add_sub_add_left_eq_sub, add_sub_cancel_left,
        ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hm), ENNReal.ofReal_one,
        ENNReal.ofReal_natCast, le_refl]
    have hc : ∀ᶠ m : ℕ in Filter.atTop,
        (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(B : ℝ)) B)) ⊆ ⋃ f : γ m, t m f := by
      refine Filter.eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
      have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      intro x hx
      simp only [Set.mem_univ_pi, Set.mem_Ioo] at hx
      let f : γ m := fun i => ⟨⌊(x i + B) * m⌋₊, by
        apply (Nat.floor_lt (mul_nonneg (by linarith [(hx i).1]) hmpos.le)).mpr
        push_cast
        nlinarith [(hx i).2]⟩
      refine Set.mem_iUnion.mpr ⟨f, ?_⟩
      change ∀ i ∈ Set.univ, x i ∈ Set.Icc _ _
      intro i _
      constructor
      · have hfloor := Nat.floor_le (mul_nonneg (by linarith [(hx i).1] : 0 ≤ x i + B) hmpos.le)
        dsimp [f]
        have := (div_le_iff₀ hmpos).mpr hfloor
        nlinarith
      · have hfloor := (Nat.lt_floor_add_one ((x i + B) * m)).le
        dsimp [f]
        have := (le_div_iff₀ hmpos).mpr hfloor
        nlinarith
    have hcost : ∀ᶠ m : ℕ in Filter.atTop,
        (∑ f : γ m, Metric.ediam (t m f) ^ (n : ℝ)) ≤ ((2 * B : ℕ) : ℝ≥0∞) ^ n := by
      filter_upwards [hd, Filter.eventually_ge_atTop 1] with m hdm hm
      calc
        (∑ f : γ m, Metric.ediam (t m f) ^ (n : ℝ))
            ≤ ∑ _f : γ m, (1 / (m : ℝ≥0∞)) ^ n := by
          apply Finset.sum_le_sum
          intro f _
          rw [ENNReal.rpow_natCast]
          exact pow_le_pow_left' (hdm f) n
        _ = ((2 * B : ℕ) : ℝ≥0∞) ^ n := by
          simp only [Finset.sum_const, Finset.card_univ, γ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_pow, Nat.cast_mul]
          rw [← mul_pow]
          have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
          rw [mul_one_div, ENNReal.mul_div_cancel_right hm0 (ENNReal.natCast_ne_top m)]
    have hlim : Filter.Tendsto (fun m : ℕ => 1 / (m : ℝ≥0∞)) Filter.atTop (nhds 0) := by
      simpa only [one_div] using ENNReal.tendsto_inv_nat_nhds_zero
    have hmes := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (n : ℝ)
      (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(B : ℝ)) B))
      (fun m : ℕ => 1 / (m : ℝ≥0∞)) hlim t hd hc
    apply lt_of_le_of_lt hmes
    have hl : Filter.liminf (fun m : ℕ => ∑ f : γ m, Metric.ediam (t m f) ^ (n : ℝ)) Filter.atTop ≤
        ((2 * B : ℕ) : ℝ≥0∞) ^ n := by
      calc
        _ ≤ Filter.liminf (fun _ : ℕ => ((2 * B : ℕ) : ℝ≥0∞) ^ n) Filter.atTop :=
          Filter.liminf_le_liminf hcost
        _ = _ := Filter.liminf_const _
    exact hl.trans_lt (by finiteness)
#check @checked
#print axioms checked
end YuiAuxiliary
