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
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ (U : Set (GP.Space n)) (J : Set ℝ) (r : ℝ), 0 ≤ r →\n  Metric.ediam U ≤ ENNReal.ofReal r → Metric.ediam J ≤ ENNReal.ofReal r →\n  Metric.ediam {z : GP.Space (n+1) | GP.horizontal z ∈ U ∧ GP.vertical z ∈ J}\n    ≤ ENNReal.ofReal (Real.sqrt 2 * r)" := by
  intro U J r hr hU hJ
  apply Metric.ediam_le
  intro z hz w hw
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  have hdU : dist (GP.horizontal z) (GP.horizontal w) ≤ r := by
    have h := Metric.edist_le_of_ediam_le hz.1 hw.1 hU
    rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at h
  have hdJ : dist (GP.vertical z) (GP.vertical w) ≤ r := by
    have h := Metric.edist_le_of_ediam_le hz.2 hw.2 hJ
    rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at h
  have hsq : dist z w ^ 2 =
      dist (GP.horizontal z) (GP.horizontal w) ^ 2 +
        dist (GP.vertical z) (GP.vertical w) ^ 2 := by
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc,
      GP.horizontal, GP.vertical, PiLp.toLp_apply]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnon : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr
  nlinarith [dist_nonneg (x := z) (y := w),
    dist_nonneg (x := GP.horizontal z) (y := GP.horizontal w),
    dist_nonneg (x := GP.vertical z) (y := GP.vertical w),
    sq_nonneg (r - dist (GP.horizontal z) (GP.horizontal w)),
    sq_nonneg (r - dist (GP.vertical z) (GP.vertical w))]
#check @checked
#print axioms checked
end YuiAuxiliary
