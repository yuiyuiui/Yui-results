import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ a : ℝ, 1 < a → GPmass a GPI = 0" := by
  have hcov : ∀ a : ℝ, 1 < a → ∀ N : ℕ, 0 < N →
      ∃ U : ℕ → Set ℝ, GPcover GPI (1 / (N : ℝ)) U ∧
        GPcost a U = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
    classical
    have hpart : ∀ N : ℕ, 0 < N → ∀ x : ℝ, 0 ≤ x → x ≤ N →
        ∃ i : ℕ, i < N ∧ (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        intro hn x hx hxN
        by_cases hN : N = 0
        · subst N
          exact ⟨0, by omega, by simpa using hx, by simpa using hxN⟩
        · by_cases h : x ≤ N
          · obtain ⟨i, hi, hix, hxi⟩ := ih (Nat.pos_of_ne_zero hN) x hx h
            exact ⟨i, by omega, hix, hxi⟩
          · exact ⟨N, Nat.lt_succ_self N, le_of_not_ge h, by exact_mod_cast hxN⟩
    intro a ha N hN
    have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let U : ℕ → Set ℝ := fun i =>
      if i < N then Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) else ∅
    have hd : ∀ i, Metric.ediam (U i) =
        if i < N then ENNReal.ofReal (1 / (N : ℝ)) else 0 := by
      intro i
      by_cases hi : i < N
      · simp only [U, if_pos hi, Real.ediam_Icc]
        congr 1
        ring
      · simp [U, hi]
    have hc : GPcover GPI (1 / (N : ℝ)) U := by
      constructor
      · intro x hx
        obtain ⟨i, hi, hil, hiu⟩ := hpart N hN (x * N)
          (mul_nonneg hx.1 hNp.le) (by nlinarith [hx.2])
        apply Set.mem_iUnion.mpr
        refine ⟨i, ?_⟩
        simp only [U, if_pos hi, Set.mem_Icc]
        exact ⟨(div_le_iff₀ hNp).mpr hil, (le_div_iff₀ hNp).mpr hiu⟩
      · intro i
        rw [hd]
        split_ifs <;> simp
    have hcost : GPcost a U = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
      unfold GPcost
      rw [tsum_eq_sum (s := Finset.range N) (fun i hi => ?_)]
      · calc
          ∑ i ∈ Finset.range N, Metric.ediam (U i) ^ a =
              ∑ i ∈ Finset.range N, (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hd, if_pos (Finset.mem_range.mp hi)]
          _ = (N : ENNReal) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by simp
          _ = ENNReal.ofReal ((N : ℝ) * (1 / (N : ℝ)) ^ a) := by
            rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNp),
              ENNReal.ofReal_mul hNp.le, ENNReal.ofReal_natCast]
          _ = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
            congr 1
            rw [sub_eq_add_neg, Real.rpow_add hNp, Real.rpow_one,
              Real.rpow_neg_eq_inv_rpow, one_div]
      · rw [hd, if_neg (by simpa using hi)]
        exact ENNReal.zero_rpow_of_pos (by linarith)
    exact ⟨U, hc, hcost⟩
  intro a ha
  have hlimR : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a))
      Filter.atTop (nhds 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal ((N : ℝ) ^ (1 - a)))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hlimR
  have hscale : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply le_antisymm _ zero_le
  unfold GPmass
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  apply ge_of_tendsto hlim
  have hs : ∀ᶠ N : ℕ in Filter.atTop, 1 / (N : ℝ) ≤ δ :=
    hscale.eventually (eventually_le_nhds hδ)
  filter_upwards [hs, Filter.eventually_gt_atTop (0 : ℕ)] with N hNδ hN
  obtain ⟨U, hU, hcost⟩ := hcov a ha N hN
  have hUd : GPcover GPI δ U :=
    ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hNδ)⟩
  calc
    GPcontent a δ GPI ≤ GPcost a U := iInf_le_of_le U (iInf_le _ hUd)
    _ = _ := hcost
#check @checked
#print axioms checked
end YuiAuxiliary
