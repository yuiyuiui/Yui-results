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

namespace Translation
set_option autoImplicit false

namespace Local_T013
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (N : ℕ) (d : ℝ), 0 < N → 0 ≤ d → ∀ x ∈ Set.Icc (0 : ℝ) ((N : ℝ) * d), ∃ i : ℕ, i < N ∧ x ∈ Set.Icc ((i : ℝ) * d) (((i : ℝ) + 1) * d)" := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    intro d hN hd x hx
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, by simpa using hx⟩
    · by_cases hle : x ≤ (N : ℝ) * d
      · obtain ⟨i, hi, hxi⟩ := ih d (Nat.pos_of_ne_zero hzero) hd x ⟨hx.1, hle⟩
        exact ⟨i, by omega, hxi⟩
      · refine ⟨N, by omega, le_of_lt (lt_of_not_ge hle), ?_⟩
        simpa only [Nat.cast_succ] using hx.2

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (a : ℝ) (N : ℕ), 1 < a → 0 < N → (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a = ENNReal.ofReal ((N : ℝ) ^ (1 - a))" := by
  intro a N ha hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hconv : (ENNReal.ofReal (1 / (N : ℝ))) ^ a = ENNReal.ofReal ((1 / (N : ℝ)) ^ a) :=
    ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNp)
  rw [hconv, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNp.le]
  congr 1
  rw [Real.rpow_sub hNp, Real.rpow_one, one_div, Real.inv_rpow hNp.le]
  rfl

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (a : ℝ) (N : ℕ), 1 < a → 0 < N → ∃ U : ℕ → Set ℝ, YuiCover (1 / (N : ℝ)) YuiI U ∧ YuiCost a U ≤ ENNReal.ofReal ((N : ℝ) ^ (1 - a))" := by
  classical
  intro a N ha hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let U : ℕ → Set ℝ := fun i => if i < N then Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) else ∅
  have hdiam (i : ℕ) (hi : i < N) : Metric.ediam (U i) = ENNReal.ofReal (1 / (N : ℝ)) := by
    simp only [U, if_pos hi, Real.ediam_Icc]
    congr 1
    ring
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) ((N : ℝ) * (1 / (N : ℝ))) := by
      simpa [YuiI, hNp.ne'] using hx
    obtain ⟨i, hi, hxi⟩ := (@yui_aux_0001 n E) N (1 / (N : ℝ)) hN (by positivity) x hx'
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    simpa [U, hi, div_eq_mul_inv] using hxi
  · intro i
    by_cases hi : i < N
    · exact le_of_eq (hdiam i hi)
    · simp [U, hi]
  · calc
      YuiCost a U = ∑ i ∈ Finset.range N, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ a := by
        unfold YuiCost
        apply tsum_eq_sum
        intro i hi
        have hi' : ¬ i < N := by simpa using hi
        simp [U, hi']
      _ ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by
        apply Finset.sum_le_sum
        intro i hi
        apply iSup_le
        intro hne
        exact le_of_eq (congrArg (fun d : ℝ≥0∞ => d ^ a) (hdiam i (Finset.mem_range.mp hi)))
      _ = (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by simp [nsmul_eq_mul]
      _ = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := (@yui_aux_0002 n E) a N ha hN

end Local_T013
open Local_T013 in
theorem T013 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ a : ℝ, 1 < a → YuiMeasure a YuiI = 0 := by
  intro a ha
  have hmesh : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Real.rpow_neg_one, one_div] using
      (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)
  have hpow : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (show 0 < a - 1 by linarith)).comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)
  have hcost : Filter.Tendsto (fun N : ℕ => ENNReal.ofReal ((N : ℝ) ^ (1 - a))) Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hpow
  apply le_antisymm _ bot_le
  unfold YuiMeasure
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  apply ge_of_tendsto hcost
  filter_upwards [(tendsto_order.mp hmesh).2 δ hδ, Filter.eventually_gt_atTop 0] with N hmeshN hN
  obtain ⟨U, hU, hc⟩ := (@yui_aux_0003 n E) a N ha hN
  have hcover : YuiCover δ YuiI U :=
    ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hmeshN.le)⟩
  calc
    YuiContent a δ YuiI ≤ YuiCost a U := by
      unfold YuiContent
      exact iInf_le_of_le U (iInf_le_of_le hcover le_rfl)
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := hc

#check @T013
#print axioms T013

end Translation
