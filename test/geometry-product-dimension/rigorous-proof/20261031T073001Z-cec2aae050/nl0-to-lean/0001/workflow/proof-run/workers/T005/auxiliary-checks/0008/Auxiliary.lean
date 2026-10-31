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
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "1 ≤ n → ∀ (q r ε : ℝ) (W : ℕ → Set (GP.Space n)),\n  0 < q → 0 < r → 0 < ε → GP.Cover E r W →\n  GP.cost q W < ENNReal.ofReal (ε/2) →\n  ∃ (U : {i : ℕ // (W i).Nonempty} → Set (GP.Space n))\n    (d : {i : ℕ // (W i).Nonempty} → ℝ),\n    (E ⊆ ⋃ i, U i) ∧\n    (∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i)) ∧\n    (∑' i, ENNReal.ofReal ((d i)^q)) < ENNReal.ofReal ε" := by
  classical
  have betas : ∀ (q r ε : ℝ), 0 < q → 0 < r → 0 < ε →
    ∃ b : ℕ → ℝ, (∀ i, 0 < b i ∧ b i ≤ r ∧ (b i) ^ q ≤ ε / 8 * ((1:ℝ)/2)^i) ∧
      (∑' i, ENNReal.ofReal (ε / 8 * ((1:ℝ)/2)^i)) = ENNReal.ofReal (ε / 4) := by
    intro q r ε hq hr hε
    let a : ℕ → ℝ := fun i => ε / 8 * ((1:ℝ)/2)^i
    let b : ℕ → ℝ := fun i => min (r/2) ((a i) ^ q⁻¹)
    have ha : ∀ i, 0 < a i := fun i => by dsimp [a]; positivity
    refine ⟨b, ?_, ?_⟩
    · intro i
      have hb : 0 < b i := lt_min (half_pos hr) (Real.rpow_pos_of_pos (ha i) _)
      refine ⟨hb, (min_le_left _ _).trans (by linarith), ?_⟩
      calc (b i) ^ q ≤ ((a i) ^ q⁻¹) ^ q :=
            Real.rpow_le_rpow hb.le (min_le_right _ _) hq.le
           _ = a i := Real.rpow_inv_rpow (ha i).le hq.ne'
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (ha i).le)
        (summable_geometric_two.mul_left (ε/8)), tsum_mul_left, tsum_geometric_two]
      congr 1
      ring
  intro hn q r ε W hq hr hε hW hcost
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (GP.Space n) := inferInstance
  obtain ⟨b, hb, hsum⟩ := betas q r ε hq hr hε
  let K := {i : ℕ // (W i).Nonempty}
  let x : K → GP.Space n := fun i => i.property.choose
  let U : K → Set (GP.Space n) := fun i =>
    if Metric.ediam (W i) = 0 then Metric.ball (x i) (b i / 2) else W i
  let d : K → ℝ := fun i =>
    if Metric.ediam (W i) = 0 then b i else Metric.diam (W i)
  have hd : ∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i) := by
    intro i
    have ht : Metric.ediam (W i) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW.2 i)
    dsimp [U, d]
    split_ifs with hi
    · refine ⟨(hb i).1, (hb i).2.1, ?_⟩
      have heq : Metric.diam (Metric.ball (x i) (b i / 2)) = b i := by
        rw [Metric.diam_ball_eq _ (by linarith [(hb i).1])]
        ring
      rw [← heq]
      exact (ENNReal.ofReal_toReal Metric.isBounded_ball.ediam_ne_top).symm
    · exact ⟨ENNReal.toReal_pos hi ht,
        ENNReal.toReal_le_of_le_ofReal hr.le (hW.2 i), (ENNReal.ofReal_toReal ht).symm⟩
  have hsub : ∀ i : K, W i ⊆ U i := by
    intro i y hy
    dsimp [U]
    split_ifs with hi
    · have hxy : y = x i := (Metric.ediam_eq_zero_iff.mp hi) hy i.property.choose_spec
      rw [hxy]
      exact Metric.mem_ball_self (half_pos (hb i).1)
    · exact hy
  refine ⟨U, d, ?_, hd, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hy)
    exact Set.mem_iUnion.mpr ⟨⟨i, y, hi⟩, hsub ⟨i, y, hi⟩ hi⟩
  · have hpoint : ∀ i : K, ENNReal.ofReal ((d i)^q) ≤
        (⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q) +
          ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^(i:ℕ)) := by
      intro i
      dsimp [d]
      split_ifs with hi
      · exact (ENNReal.ofReal_le_ofReal (hb i).2.2).trans (le_add_left le_rfl)
      · have heq : ENNReal.ofReal (Metric.diam (W i)^q) = Metric.ediam (W i)^q := by
          rw [← ENNReal.ofReal_rpow_of_nonneg Metric.diam_nonneg hq.le]
          congr 1
          exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW.2 i))
        rw [heq]
        exact (le_iSup_of_le i.property le_rfl).trans (le_self_add)
    calc
      (∑' i, ENNReal.ofReal ((d i)^q)) ≤
          ∑' i : K, ((⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q) +
            ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^(i:ℕ))) := ENNReal.tsum_le_tsum hpoint
      _ ≤ GP.cost q W + ENNReal.ofReal (ε/4) := by
        rw [ENNReal.tsum_add]
        exact add_le_add
          (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun i => ⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q))
          ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun i => ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^i))).trans_eq hsum)
      _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/4) := add_le_add_right hcost.le _
      _ = ENNReal.ofReal (ε/2+ε/4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
#check @checked
#print axioms checked
end YuiAuxiliary
