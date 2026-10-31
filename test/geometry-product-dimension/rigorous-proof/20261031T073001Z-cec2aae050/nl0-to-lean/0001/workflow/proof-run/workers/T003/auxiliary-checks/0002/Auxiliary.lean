import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ a : ℝ, 1 < a → MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval = 0" := by
  classical
  intro a ha
  have subdiv : ∀ (N : ℕ), 0 < N → ∀ (d x : ℝ), 0 ≤ x → x ≤ (N : ℝ) * d →
      ∃ k : ℕ, k < N ∧ (k : ℝ) * d ≤ x ∧ x ≤ ((k : ℝ) + 1) * d := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro hN d x hx hxd
      by_cases h : N = 0
      · subst N
        exact ⟨0, by omega, by simpa using hx, by simpa using hxd⟩
      · by_cases hle : x ≤ (N : ℝ) * d
        · obtain ⟨k, hk, hkx⟩ := ih (Nat.pos_of_ne_zero h) d x hx hle
          exact ⟨k, Nat.lt_succ_of_lt hk, hkx⟩
        · exact ⟨N, Nat.lt_succ_self N, (lt_of_not_ge hle).le, by exact_mod_cast hxd⟩
  let d : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ)⁻¹
  let t : (k : ℕ) → Fin (k + 1) → Set ℝ :=
    fun k i => Set.Icc ((i : ℝ) * d k) (((i : ℝ) + 1) * d k)
  have hd (k : ℕ) : 0 < d k := by dsimp [d]; positivity
  have hdiam (k : ℕ) (i : Fin (k+1)) :
      Metric.ediam (t k i) = ENNReal.ofReal (d k) := by
    dsimp [t]
    rw [Real.ediam_Icc]
    congr 1
    ring
  have hcover (k : ℕ) : GP.unitInterval ⊆ ⋃ i, t k i := by
    intro x hx
    obtain ⟨i, hi, hix, hxi⟩ := subdiv (k+1) (by omega) (d k) x hx.1 (by
      simpa [d, ne_of_gt (show (0 : ℝ) < (k+1 : ℕ) by positivity)] using hx.2)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hix, hxi⟩
  have hNat : Filter.Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hdlim : Filter.Tendsto d Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hNat
  have hrlim : Filter.Tendsto (fun k => ENNReal.ofReal (d k)) Filter.atTop (nhds 0) := by
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdlim
  have hcost (k : ℕ) :
      (∑ i : Fin (k+1), (Metric.ediam (t k i)) ^ a) =
        ENNReal.ofReal (((k+1 : ℕ) : ℝ) ^ (1-a)) := by
    simp_rw [hdiam]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_rpow_of_pos (hd k)]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [d]
    rw [Real.inv_rpow (by positivity), Real.rpow_sub (by positivity),
      Real.rpow_one, div_eq_mul_inv]
  have hcostlim : Filter.Tendsto
      (fun k : ℕ => ∑ i : Fin (k+1), (Metric.ediam (t k i)) ^ a)
      Filter.atTop (nhds 0) := by
    simp_rw [hcost]
    have hh : Filter.Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ) ^ (1-a))
        Filter.atTop (nhds 0) := by
      convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp hNat using 1 <;>
        simp [neg_sub]
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  apply le_antisymm _ (zero_le _)
  calc
    MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval ≤
        Filter.liminf (fun k : ℕ => ∑ i : Fin (k+1), Metric.ediam (t k i) ^ a)
          Filter.atTop :=
      MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum a GP.unitInterval
        (fun k => ENNReal.ofReal (d k)) hrlim t
        (Filter.Eventually.of_forall fun k i => (hdiam k i).le)
        (Filter.Eventually.of_forall hcover)
    _ = 0 := hcostlim.liminf_eq
#check @checked
#print axioms checked
end YuiAuxiliary
