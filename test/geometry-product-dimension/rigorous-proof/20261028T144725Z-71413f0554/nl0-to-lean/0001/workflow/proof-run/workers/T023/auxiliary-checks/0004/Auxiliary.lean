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
theorem checked (n : ℕ) (E : Set (V n)) (h_T004 : ScaleLaws ∧ CriticalLaws ∧ InvarianceLaws ∧ PowerLaws) : yui_aux_type% "∀ (a : ℝ), 1 < a → ∀ (m : ℕ), 0 < m → ∀ δ : ℝ, 1 / (m : ℝ) ≤ δ → content a δ unitI ≤ ENNReal.ofReal ((1 / (m : ℝ)) ^ (a - 1))" := by
  intro a ha m hm δ hδ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrec : 0 < 1 / (m : ℝ) := by positivity
  let U : ℕ → Set ℝ := fun j => if j < m then Icc ((j : ℝ) / m) (((j : ℝ) + 1) / m) else ∅
  have hcov : scaleCover δ unitI U := by
    constructor
    · intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2
      apply Set.mem_iUnion.mpr
      by_cases hx : x = 1
      · refine ⟨m - 1, ?_⟩
        have hj : m - 1 < m := by omega
        have hjR : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
        simp only [U, if_pos hj, mem_Icc, hx, hjR]
        constructor
        · apply (div_le_iff₀ hmR).2; linarith
        · apply (le_div_iff₀ hmR).2; linarith
      · have hxl : x < 1 := lt_of_le_of_ne hx1 hx
        have hxm : x * m < (m : ℝ) := by nlinarith
        have hj : ⌊x * m⌋₊ < m := (Nat.floor_lt (by positivity)).2 hxm
        refine ⟨⌊x * m⌋₊, ?_⟩
        simp only [U, if_pos hj, mem_Icc]
        constructor
        · exact (div_le_iff₀ hmR).2 (Nat.floor_le (by positivity))
        · exact (le_div_iff₀ hmR).2 (Nat.lt_floor_add_one (x * m)).le
    · intro j
      dsimp [U]
      split_ifs with hj
      · rw [Real.ediam_Icc]
        have heq : ((j : ℝ) + 1) / m - (j : ℝ) / m = 1 / (m : ℝ) := by ring
        rw [heq]
        exact ENNReal.ofReal_le_ofReal hδ
      · simp
  have hcost : cost a U = ENNReal.ofReal ((1 / (m : ℝ)) ^ (a - 1)) := by
    unfold cost
    rw [tsum_eq_sum (s := Finset.range m)]
    · have hd : ∀ j ∈ Finset.range m, Metric.ediam (U j) = ENNReal.ofReal (1 / (m : ℝ)) := by
        intro j hj
        simp only [U, if_pos (Finset.mem_range.mp hj), Real.ediam_Icc]
        congr 1
        ring
      rw [Finset.sum_congr rfl (fun j hj => congrArg (fun d : ℝ≥0∞ => d ^ a) (hd j hj))]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_rpow_of_pos hrec]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hmR.le]
      congr 1
      rw [Real.rpow_sub_one (ne_of_gt hrec)]
      field_simp
    · intro j hj
      have hj' : ¬ j < m := by simpa using hj
      simp [U, hj', ENNReal.zero_rpow_of_pos (show 0 < a by linarith)]
  change (⨅ (W : ℕ → Set ℝ) (_ : scaleCover δ unitI W), cost a W) ≤ _
  exact (iInf_le_of_le U (iInf_le_of_le hcov le_rfl)).trans_eq hcost
#check @checked
#print axioms checked
end YuiAuxiliary
