import Mathlib
open scoped ENNReal NNReal BigOperators
noncomputable section

abbrev GDVec (m : ℕ) := EuclideanSpace ℝ (Fin m)

def GDLine (t : ℝ) : GDVec 1 :=
  WithLp.toLp 2 (fun _ => t)

def GDInterval : Set ℝ := Set.Icc 0 1

def GDPoint {m : ℕ} (x : GDVec m) (t : ℝ) : GDVec (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)

def GDProduct {m : ℕ} (A : Set (GDVec m)) : Set (GDVec (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ GDInterval, z = GDPoint x t}

def GDCost {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (_ : A.Nonempty), (Metric.ediam A) ^ s

def GDContent {X : Type*} [PseudoEMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, GDCost s (U i)

def GDMeasure {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GDContent s δ A

def GDPositiveCover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (q r ε : ℝ) : Prop :=
  ∃ (K : Set ℕ) (U : K → Set X),
    A ⊆ ⋃ i, U i ∧
    (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧
    (∑' i, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal ε

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (l : Fin n → ℝ) (h : ℝ), 0 ≤ h → Metric.ediam {x : GDVec n | ∀ j, l j ≤ x j ∧ x j ≤ l j + h} ≤ (n : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal h" := by
  intro l h hh
  apply Metric.ediam_le
  intro x hx y hy
  rw [PiLp.edist_eq_sum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  norm_num only [ENNReal.toReal_ofNat]
  calc
    (∑ i : Fin n, edist (x i) (y i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∑ i : Fin n, (ENNReal.ofReal h) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      gcongr with i
      rw [edist_dist, Real.dist_eq]
      apply ENNReal.ofReal_le_ofReal
      exact abs_le.mpr ⟨by linarith [(hx i).1, (hy i).2], by linarith [(hy i).1, (hx i).2]⟩
    _ = (n : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal h := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.rpow_mul]
      norm_num

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (x : ℝ) (m : ℕ), 0 ≤ x → x < m → ⌊x⌋₊ < m" := by
  intro x m hx hxm
  exact (Nat.floor_lt hx).mpr hxm

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (B : ℕ), (∀ x ∈ E, ∀ j : Fin n, |x j| ≤ B) → ∀ (k : ℕ), 0 < k → ∃ t : (Fin n → Fin ((2 * B + 2) * k)) → Set (GDVec n), E ⊆ ⋃ i, t i ∧ ∀ i, Metric.ediam (t i) ≤ (n : ℝ≥0∞) ^ (1 / 2 : ℝ) * (1 / (k : ℝ≥0∞))" := by
  intro B hB k hk
  have kp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let t : (Fin n → Fin ((2 * B + 2) * k)) → Set (GDVec n) := fun f =>
    {x | ∀ j, -(B : ℝ) + (f j : ℝ) / k ≤ x j ∧ x j ≤ -(B : ℝ) + (f j : ℝ) / k + 1 / k}
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    have bounds : ∀ j, -(B : ℝ) ≤ x j ∧ x j ≤ B := fun j => abs_le.mp (hB x hx j)
    have nonneg : ∀ j, 0 ≤ (x j + B) * k := fun j => mul_nonneg (by linarith [(bounds j).1]) kp.le
    let f : Fin n → Fin ((2 * B + 2) * k) := fun j =>
      ⟨⌊(x j + B) * k⌋₊, by
        apply (@yui_aux_0002 n E h_H001 h_H002 h_T002) _ _ (nonneg j)
        push_cast
        nlinarith [(bounds j).2]⟩
    apply Set.mem_iUnion.mpr
    refine ⟨f, fun j => ⟨?_, ?_⟩⟩
    · have hf := Nat.floor_le (nonneg j)
      change -(B : ℝ) + (⌊(x j + B) * k⌋₊ : ℝ) / k ≤ x j
      apply (le_sub_iff_add_le.mp ?_)
      have hdiv : (⌊(x j + B) * k⌋₊ : ℝ) / k ≤ x j + B := (div_le_iff₀ kp).mpr hf
      linarith
    · have hf := (Nat.lt_floor_add_one ((x j + B) * k)).le
      change x j ≤ -(B : ℝ) + (⌊(x j + B) * k⌋₊ : ℝ) / k + 1 / k
      have hdiv : x j + B ≤ ((⌊(x j + B) * k⌋₊ : ℝ) + 1) / k := (le_div_iff₀ kp).mpr hf
      rw [add_div] at hdiv
      linarith
  · intro f
    have hd := (@yui_aux_0001 n E h_H001 h_H002 h_T002) (fun j => -(B : ℝ) + (f j : ℝ) / k) (1 / (k : ℝ)) (by positivity)
    simpa only [ENNReal.ofReal_div_of_pos kp, ENNReal.ofReal_one, ENNReal.ofReal_natCast] using hd

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∃ B : ℕ, 1 ≤ B ∧ ∀ x ∈ E, ∀ j : Fin n, |x j| ≤ B" := by
  obtain ⟨R, hR⟩ := h_H002.isBounded.exists_norm_le
  obtain ⟨B, hB⟩ := exists_nat_gt (max R 1)
  refine ⟨B, ?_, ?_⟩
  · exact_mod_cast (le_max_right R 1).trans hB.le
  · intro x hx j
    calc
      |x j| = ‖x j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := PiLp.norm_apply_le x j
      _ ≤ R := hR x hx
      _ ≤ B := (le_max_left R 1).trans hB.le

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (k d : ℕ), (((k : ℝ≥0∞)⁻¹) ^ d)⁻¹ = (k : ℝ≥0∞) ^ d" := by
  intro k d
  rw [ENNReal.inv_pow, inv_inv]

theorem yui_aux_0006 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (B k : ℕ) (a : ℝ), 0 < k → (n : ℝ) < a → (∑ _ : (Fin n → Fin ((2 * B + 2) * k)), ((n : ℝ≥0∞) ^ (1 / 2 : ℝ) * (1 / (k : ℝ≥0∞))) ^ a) = ((2 * B + 2 : ℕ) : ℝ≥0∞) ^ n * (n : ℝ≥0∞) ^ (a / 2) * (1 / (k : ℝ≥0∞)) ^ (a - n)" := by
  intro B k a hk ha
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg n) ha.le
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hki0 : (1 / (k : ℝ≥0∞)) ≠ 0 := by simp
  have hkit : (1 / (k : ℝ≥0∞)) ≠ ⊤ := by simp [hk0]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_mul, mul_pow,
    ENNReal.mul_rpow_of_nonneg _ _ ha0, ← ENNReal.rpow_mul]
  rw [show (1 / 2 : ℝ) * a = a / 2 by ring,
    ENNReal.rpow_sub a (n : ℝ) hki0 hkit]
  simp only [one_div, ENNReal.inv_rpow, inv_inv, ENNReal.rpow_natCast, div_eq_mul_inv]
  simp only [one_mul]
  rw [(@yui_aux_0005 n E h_H001 h_H002 h_T002) k n]
  ac_rfl

theorem yui_aux_0007 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "Filter.Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ≥0∞)) Filter.atTop (nhds 0)" := by
  simpa only [one_div, Function.comp_def] using ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)

theorem yui_aux_0008 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (B : ℕ) (a : ℝ), 0 ≤ a → (((2 * B + 2 : ℕ) : ℝ≥0∞) ^ n * (n : ℝ≥0∞) ^ (a / 2)) ≠ ⊤" := by
  intro B a ha
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _))

theorem yui_aux_0009 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ (u v : ℕ → ℝ≥0∞), (∀ k, u k ≤ v k) → Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop" := by
  intro u v huv
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall huv)

theorem yui_aux_0010 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "∀ a : ℝ, (n : ℝ) < a → GDMeasure a E = 0" := by
  classical
  intro a ha
  have hu := @yui_aux_0007 n E h_H001 h_H002 h_T002
  have ha0 : 0 ≤ a := (Nat.cast_nonneg n).trans ha.le
  have hnfin : (n : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)
  have hr : Filter.Tendsto (fun k : ℕ => (n : ℝ≥0∞) ^ (1 / 2 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ≥0∞))) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hu (Or.inr hnfin)
  obtain ⟨B, hBpos, hB⟩ := @yui_aux_0004 n E h_H001 h_H002 h_T002
  have hcovers := fun k : ℕ => (@yui_aux_0003 n E h_H001 h_H002 h_T002) B hB (k+1) (by omega)
  choose t ht hd using hcovers
  let C : ℝ≥0∞ := ((2 * B + 2 : ℕ) : ℝ≥0∞) ^ n * (n : ℝ≥0∞) ^ (a / 2)
  have hC : C ≠ ⊤ := (@yui_aux_0008 n E h_H001 h_H002 h_T002) B a ha0
  have hcost : Filter.Tendsto (fun k : ℕ => C * (1 / ((k+1 : ℕ) : ℝ≥0∞)) ^ (a - n)) Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC (sub_pos.mpr ha)).comp hu
  have hle := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum a E
    (fun k : ℕ => (n : ℝ≥0∞) ^ (1/2 : ℝ) * (1 / ((k+1 : ℕ) : ℝ≥0∞)))
    hr t (Filter.Eventually.of_forall hd) (Filter.Eventually.of_forall ht)
  have hlim : Filter.liminf (fun k : ℕ => ∑ i, Metric.ediam (t k i) ^ a) Filter.atTop ≤ 0 := by
    calc
      _ ≤ Filter.liminf (fun k : ℕ => C * (1 / ((k+1 : ℕ) : ℝ≥0∞)) ^ (a - n)) Filter.atTop := by
        apply (@yui_aux_0009 n E h_H001 h_H002 h_T002)
        intro k
        calc
          _ ≤ ∑ _ : (Fin n → Fin ((2 * B + 2) * (k+1))), ((n : ℝ≥0∞) ^ (1/2 : ℝ) * (1 / ((k+1 : ℕ) : ℝ≥0∞))) ^ a :=
            Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hd k i) ha0
          _ = _ := (@yui_aux_0006 n E h_H001 h_H002 h_T002) B (k+1) a (by omega) ha
      _ = 0 := hcost.liminf_eq
  rw [(h_T002 n E).2 a (lt_of_le_of_lt (Nat.cast_nonneg n) ha) |>.1]
  exact le_antisymm (hle.trans hlim) bot_le

theorem yui_aux_0011 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "E.Subsingleton → ∀ a : ℝ, 0 < a → GDMeasure a E = 0" := by
  intro hs a ha
  classical
  have he : Metric.ediam E = 0 := Metric.ediam_eq_zero_iff.mpr hs
  let U : ℕ → Set (GDVec n) := fun i => if i = 0 then E else ∅
  have hcover : E ⊆ ⋃ i, U i := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, by simpa [U] using hx⟩
  have hd : ∀ i, Metric.ediam (U i) = 0 := by
    intro i
    by_cases hi : i = 0 <;> simp [U, hi, he]
  have hc : ∀ i, GDCost a (U i) = 0 := by
    intro i
    simp [GDCost, hd i, ENNReal.zero_rpow_of_pos ha]
  apply le_antisymm ?_ bot_le
  unfold GDMeasure
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  unfold GDContent
  refine iInf_le_of_le U (iInf_le_of_le hcover (iInf_le_of_le ?_ ?_))
  · intro i
    rw [hd i]
    exact bot_le
  · simp only [hc, tsum_zero]
    exact le_rfl

theorem yui_aux_0012 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "(∀ a : ℝ, (n : ℝ) < a → GDMeasure a E = 0) → dimH E ≤ (n : ℝ≥0∞)" := by
  intro hz
  by_contra! h
  obtain ⟨a, ha0, hna, had⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  have hnreal : (n : ℝ) < a := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg n)).mp
    simpa only [ENNReal.ofReal_natCast] using hna
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) hnreal
  have hd : dimH E ≤ ENNReal.ofReal a :=
    ((h_T002 n E).2 a ha).2.2.2.2.1 (hz a hnreal)
  exact had.not_ge hd

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) :
    Bornology.IsBounded E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0) := by
  classical
  refine ⟨h_H002.isBounded, ?_⟩
  by_cases hn : n = 0
  · subst n
    have hs : E.Subsingleton := by
      intro x hx y hy
      apply PiLp.ext
      intro i
      exact Fin.elim0 i
    have hE : E = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      obtain ⟨x, hx⟩ := h_H001
      have hyx : y = x := by
        apply PiLp.ext
        intro i
        exact Fin.elim0 i
      simpa only [hyx] using hx
    have hz : ∀ a : ℝ, 0 < a → GDMeasure a E = 0 :=
      (@yui_aux_0011 0 E h_H001 h_H002 h_T002) hs
    have hd : dimH E ≤ (0 : ℝ≥0∞) := by
      apply (@yui_aux_0012 0 E h_H001 h_H002 h_T002)
      simpa only [Nat.cast_zero] using hz
    have heqdim : dimH E = 0 := le_antisymm hd bot_le
    exact ⟨by simpa using hd, fun _ => ⟨hE, heqdim⟩⟩
  · refine ⟨(@yui_aux_0012 n E h_H001 h_H002 h_T002)
      (@yui_aux_0010 n E h_H001 h_H002 h_T002), ?_⟩
    intro hzero
    exact (hn hzero).elim

#check @T003
#print axioms T003

end Translation
