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

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ r : ℝ≥0∞, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r" := by
  intro r hr
  by_cases ht : r = ⊤
  · exact ⟨1, zero_lt_one, by simp [ht]⟩
  · exact ⟨r.toReal, ENNReal.toReal_pos (ne_of_gt hr) ht, ENNReal.ofReal_toReal_le⟩

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (E : Set (GDVec n))  :
    ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A := by
  intro m A s hs
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  let C : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (U : ℕ → Set (GDVec m)) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, GDCost s (U i)
  have hC : Antitone C := by
    intro r t hrt
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    exact iInf_le_of_le U (iInf_le_of_le hU
      (iInf_le_of_le (fun i => (hd i).trans hrt) le_rfl))
  change (⨆ δ : ℝ, ⨆ _ : 0 < δ, C (ENNReal.ofReal δ)) =
    ⨆ r : ℝ≥0∞, ⨆ _ : 0 < r, C r
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨δ, hδ, hδr⟩ := yui_aux_0001 n E r hr
    exact (hC hδr).trans (le_iSup₂_of_le δ hδ le_rfl)

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T001 : ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A) : yui_aux_type% "∀ (s : ℝ) (hs : 0 < s), (let d : NNReal := ⟨s, hs.le⟩; (d : ENNReal) = ENNReal.ofReal s)" := by
  intro s hs
  exact ENNReal.coe_nnreal_eq (⟨s, hs.le⟩ : NNReal)

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (E : Set (GDVec n)) (h_T001 : ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A) :
    ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A) := by
  intro m A
  refine ⟨bot_le, ?_⟩
  intro s hs
  let d : NNReal := ⟨s, hs.le⟩
  have hd : (d : ENNReal) = ENNReal.ofReal s := @yui_aux_0001 n E h_T001 s hs
  rw [h_T001 m A s hs]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : (d : ENNReal) < dimH A := by rw [hd]; exact h
    exact hausdorffMeasure_of_lt_dimH (s := A) (d := d) h'
  · intro h
    have h' : dimH A < (d : ENNReal) := by rw [hd]; exact h
    exact hausdorffMeasure_of_dimH_lt (s := A) (d := d) h'
  · intro h
    have h' : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ := ne_of_lt h
    have hdim := dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := d) h'
    simpa only [hd] using hdim
  · intro h
    have h' : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ := by
      rw [show (d : ℝ) = s from rfl, h]
      exact ENNReal.zero_ne_top
    have hdim := dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := d) h'
    simpa only [hd] using hdim
  · intro h
    have h' : MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ := h
    have hdim := le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := d) h'
    simpa only [hd] using hdim

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

theorem yui_aux_0013 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) : yui_aux_type% "n = 0 → E.Subsingleton → dimH E = 0" := by
  intro hn hs
  subst n
  have hz : ∀ a : ℝ, 0 < a → GDMeasure a E = 0 :=
    (@yui_aux_0011 0 E h_H001 h_H002 h_T002) hs
  have hzero : ∀ a : ℝ, ((0 : ℕ) : ℝ) < a → GDMeasure a E = 0 := by
    simpa only [Nat.cast_zero] using hz
  have hd : dimH E ≤ ((0 : ℕ) : ℝ≥0∞) :=
    (@yui_aux_0012 0 E h_H001 h_H002 h_T002) hzero
  have hd0 : dimH E ≤ (0 : ℝ≥0∞) := by simpa only [Nat.cast_zero] using hd
  exact le_antisymm hd0 bot_le

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
    have heqdim : dimH E = 0 :=
      (@yui_aux_0013 0 E h_H001 h_H002 h_T002) rfl hs
    exact ⟨by simpa only [heqdim, Nat.cast_zero, le_refl], fun _ => ⟨hE, heqdim⟩⟩
  · refine ⟨(@yui_aux_0012 n E h_H001 h_H002 h_T002)
      (@yui_aux_0010 n E h_H001 h_H002 h_T002), ?_⟩
    intro hzero
    exact (hn hzero).elim

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_H002 : IsCompact E) (h_T003 : Bornology.IsBounded E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤" := by
  classical
  intro s δ hs hδ
  have hcover : E ⊆ ⋃ x : E, Metric.ball (x : GDVec n) (δ / 2) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using (half_pos hδ)⟩
  obtain ⟨t, ht⟩ := h_H002.elim_finite_subcover
    (fun x : E => Metric.ball (x : GDVec n) (δ / 2))
    (fun _ => Metric.isOpen_ball) hcover
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let U : ℕ → Set (GDVec n) := fun i =>
    if hi : i < Fintype.card t then
      Metric.ball (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) (δ / 2)
    else ∅
  have hUcover : E ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    let j : t := ⟨y, hy⟩
    refine Set.mem_iUnion.mpr ⟨(e j).val, ?_⟩
    dsimp only [U]
    rw [dif_pos (e j).isLt]
    simpa only [Fin.eta, Equiv.symm_apply_apply] using hxy
  have hUdiam : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ := by
    intro i
    dsimp only [U]
    split_ifs with hi
    · apply Metric.ediam_le_of_forall_dist_le
      intro x hx y hy
      have hx' : dist x (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) < δ / 2 := hx
      have hy' : dist y (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) < δ / 2 := hy
      calc
        dist x y ≤ dist x (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) +
          dist y (((e.symm ⟨i, hi⟩ : t) : E) : GDVec n) := dist_triangle_right _ _ _
        _ ≤ δ := by linarith
    · simp
  have hcost : ∀ i, GDCost s (U i) < ⊤ := by
    intro i
    have hd : Metric.ediam (U i) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hUdiam i)
    by_cases hi : (U i).Nonempty
    · simpa [GDCost, hi] using ENNReal.rpow_lt_top_of_nonneg hs.le hd
    · simp [GDCost, hi]
  have hsum : (∑' i, GDCost s (U i)) < ⊤ := by
    rw [tsum_eq_sum (s := Finset.range (Fintype.card t)) (fun i hi => ?_)]
    · exact ENNReal.sum_lt_top.mpr (fun i _ => hcost i)
    · have hi' : ¬ i < Fintype.card t := by simpa only [Finset.mem_range] using hi
      have hUi : U i = ∅ := by
        dsimp only [U]
        exact dif_neg hi'
      simp [hUi, GDCost]
  exact lt_of_le_of_lt
    (iInf_le_of_le U (iInf_le_of_le hUcover (iInf_le_of_le hUdiam le_rfl))) hsum

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (E : Set (GDVec n)) (h_H002 : IsCompact E) (h_T003 : Bornology.IsBounded E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) :
    Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0) := by
  exact ⟨h_T003.1, bot_le, h_T003.2.1,
    lt_of_le_of_lt h_T003.2.1 (by simp),
    @yui_aux_0001 n E h_H002 h_T003, h_T003.2.2⟩

namespace Local_T018
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ z : GDVec 1, GDLine (z 0) = z" := by
  intro z
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "Isometry GDLine ∧ Function.Bijective GDLine" := by
  constructor
  · apply isometry_iff_dist_eq.mpr
    intro x y
    simp [GDLine, EuclideanSpace.dist_eq, Real.sqrt_sq (dist_nonneg : 0 ≤ dist x y)]
  · constructor
    · intro x y h
      have h0 := congrArg (fun z : GDVec 1 => z 0) h
      simpa [GDLine] using h0
    · intro z
      exact ⟨z 0, @yui_aux_0001 n E z⟩

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ {X Y : Type} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (f : X → Y), Isometry f → ∀ (s : ℝ) (B : Set X), GDCost s (f '' B) = GDCost s B" := by
  intro X Y _ _ f hf s B
  simp only [GDCost, Set.image_nonempty, hf.ediam_image]

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ {X : Type} [PseudoEMetricSpace X] (s δ : ℝ) (B : Set X) (U : ℕ → Set X) (hU : B ⊆ ⋃ i, U i) (hδ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), GDContent s δ B ≤ ∑' i, GDCost s (U i)" := by
  intro X _ s δ B U hU hδ
  unfold GDContent
  exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le hδ le_rfl))

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ {X Y : Type} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (f : X → Y), Isometry f → ∀ (s δ : ℝ) (B : Set X), GDContent s δ (f '' B) ≤ GDContent s δ B" := by
  intro X Y _ _ f hf s δ B
  unfold GDContent
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hδ => ?_
  have hcover : f '' B ⊆ ⋃ i, f '' U i := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi, rfl⟩⟩
  have hdiam : ∀ i, Metric.ediam (f '' U i) ≤ ENNReal.ofReal δ := by
    intro i
    rw [hf.ediam_image]
    exact hδ i
  have hb : GDContent s δ (f '' B) ≤ ∑' i, GDCost s (f '' U i) :=
    @yui_aux_0004 n E Y _ s δ (f '' B) (fun i => f '' U i) hcover hdiam
  have hc : (∑' i, GDCost s (f '' U i)) = ∑' i, GDCost s (U i) :=
    tsum_congr fun i => @yui_aux_0003 n E X Y _ _ f hf s (U i)
  exact hb.trans_eq hc

end Local_T018
open Local_T018 in
theorem T018 (n : ℕ) (E : Set (GDVec n))  :
    Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A) := by
  have hline := @yui_aux_0002 n E
  have hiso : Isometry GDLine := hline.1
  let g : GDVec 1 → ℝ := fun z => z 0
  have hg : Isometry g := hiso.right_inv (@yui_aux_0001 n E)
  refine ⟨hiso, hline.2, ?_⟩
  intro A
  have hback : g '' (GDLine '' A) = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      exact ht
    · intro x hx
      exact ⟨GDLine x, ⟨x, hx, rfl⟩, rfl⟩
  have hcontent : ∀ s δ : ℝ, GDContent s δ (GDLine '' A) = GDContent s δ A := by
    intro s δ
    apply le_antisymm
    · exact @yui_aux_0005 n E ℝ (GDVec 1) _ _ GDLine hiso s δ A
    · have hb := @yui_aux_0005 n E (GDVec 1) ℝ _ _ g hg s δ (GDLine '' A)
      rw [hback] at hb
      exact hb
  refine ⟨hiso.dimH_image A, ?_, ?_⟩
  · intro s δ _ _
    exact hcontent s δ
  · intro s _
    simp only [GDMeasure, hcontent]

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ N : ℕ, GDInterval ⊆ ⋃ i : Fin (N + 1), Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ))" := by
  intro N x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hN : (0 : ℝ) < N + 1 := by positivity
  apply Set.mem_iUnion.mpr
  by_cases he : x = 1
  · refine ⟨⟨N, Nat.lt_succ_self N⟩, ?_⟩
    simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
    subst x
    constructor
    · apply (div_le_iff₀ hN).mpr
      linarith
    · rw [div_self (ne_of_gt hN)]
  · have hlt : x < 1 := lt_of_le_of_ne hx1 he
    have hmul : 0 ≤ x * (N + 1 : ℝ) := mul_nonneg hx0 hN.le
    have hf : ⌊x * (N + 1 : ℝ)⌋₊ < N + 1 := by
      apply (Nat.floor_lt hmul).mpr
      push_cast
      nlinarith
    refine ⟨⟨⌊x * (N + 1 : ℝ)⌋₊, hf⟩, ?_⟩
    constructor
    · apply (div_le_iff₀ hN).mpr
      exact Nat.floor_le hmul
    · apply (le_div_iff₀ hN).mpr
      exact (Nat.lt_floor_add_one _).le

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ (a : ℝ) (N : ℕ), (∑ i : Fin (N + 1), (Metric.ediam (Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ)))) ^ a) = ENNReal.ofReal ((N + 1 : ℝ) ^ (1 - a))" := by
  intro a N
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hd : ∀ i : Fin (N + 1), Metric.ediam (Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ))) = ENNReal.ofReal (1 / (N + 1 : ℝ)) := by
    intro i
    rw [Real.ediam_Icc]
    congr 1
    ring
  simp_rw [hd, ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hN)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (N + 1))]
  congr 1
  push_cast
  rw [Real.rpow_sub hN, Real.rpow_one, Real.div_rpow zero_le_one hN.le, Real.one_rpow]
  ring

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "Filter.Tendsto (fun N : ℕ => (N + 1 : ℝ)) Filter.atTop Filter.atTop" := by
  have ht : Filter.Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  simpa only [Nat.cast_add, Nat.cast_one] using ht

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ a : ℝ, 1 < a → Filter.Tendsto (fun N : ℕ => ENNReal.ofReal ((N + 1 : ℝ) ^ (1 - a))) Filter.atTop (nhds 0)" := by
  intro a ha
  have hr : Filter.Tendsto (fun N : ℕ => (N + 1 : ℝ) ^ (1 - a)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_sub] using (tendsto_rpow_neg_atTop (by linarith : 0 < a - 1)).comp (@yui_aux_0003 n E h_T002 h_T018)
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hr

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ (a : ℝ) (r : ℕ → ℝ≥0∞) (t : (N : ℕ) → Fin (N + 1) → Set (GDVec 1)), Filter.Tendsto r Filter.atTop (nhds 0) → (∀ᶠ N : ℕ in Filter.atTop, ∀ i, Metric.ediam (t N i) ≤ r N) → (∀ᶠ N : ℕ in Filter.atTop, GDLine '' GDInterval ⊆ ⋃ i, t N i) → MeasureTheory.Measure.hausdorffMeasure a (GDLine '' GDInterval) ≤ Filter.liminf (fun N => ∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) Filter.atTop" := by
  intro a r t hr ht hc
  exact MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum a (GDLine '' GDInterval) r hr t ht hc

theorem yui_aux_0006 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ a : ℝ, 1 < a → MeasureTheory.Measure.hausdorffMeasure a (GDLine '' GDInterval) = 0" := by
  intro a ha
  let t : (N : ℕ) → Fin (N + 1) → Set (GDVec 1) := fun N i => GDLine '' Set.Icc ((i : ℝ) / (N + 1 : ℝ)) (((i : ℝ) + 1) / (N + 1 : ℝ))
  have hd : ∀ N (i : Fin (N + 1)), Metric.ediam (t N i) = ENNReal.ofReal (1 / (N + 1 : ℝ)) := by
    intro N i
    dsimp only [t]
    rw [h_T018.1.ediam_image, Real.ediam_Icc]
    congr 1
    ring
  have hrR : Filter.Tendsto (fun N : ℕ => 1 / (N + 1 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp (@yui_aux_0003 n E h_T002 h_T018)
  have hr : Filter.Tendsto (fun N : ℕ => ENNReal.ofReal (1 / (N + 1 : ℝ))) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hrR
  have ht : ∀ᶠ N : ℕ in Filter.atTop, ∀ i, Metric.ediam (t N i) ≤ ENNReal.ofReal (1 / (N + 1 : ℝ)) := Filter.Eventually.of_forall (fun N i => (hd N i).le)
  have hcover : ∀ᶠ N : ℕ in Filter.atTop, GDLine '' GDInterval ⊆ ⋃ i, t N i := by
    apply Filter.Eventually.of_forall
    intro N z hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp ((@yui_aux_0001 n E h_T002 h_T018 N) hx) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi, rfl⟩⟩
  have hcost : ∀ N, (∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) = ENNReal.ofReal ((N + 1 : ℝ) ^ (1 - a)) := by
    intro N
    dsimp only [t]
    simp_rw [h_T018.1.ediam_image]
    exact @yui_aux_0002 n E h_T002 h_T018 a N
  have hlim : Filter.Tendsto (fun N => ∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) Filter.atTop (nhds 0) := by
    simp_rw [hcost]
    exact @yui_aux_0004 n E h_T002 h_T018 a ha
  apply le_antisymm _ bot_le
  calc
    MeasureTheory.Measure.hausdorffMeasure a (GDLine '' GDInterval) ≤ Filter.liminf (fun N => ∑ i : Fin (N + 1), Metric.ediam (t N i) ^ a) Filter.atTop := @yui_aux_0005 n E h_T002 h_T018 a _ t hr ht hcover
    _ = 0 := hlim.liminf_eq

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) :
    (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1 := by
  have hz : ∀ a : ℝ, 1 < a → GDMeasure a (GDLine '' GDInterval) = 0 := by
    intro a ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    exact ((h_T002 1 (GDLine '' GDInterval)).2 a ha0).1.trans (@yui_aux_0006 n E h_T002 h_T018 a ha)
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    rw [← (h_T018.2.2 GDInterval).2.2 a ha0]
    exact hz a ha
  · have hd : ∀ a : ℝ, 1 < a → dimH GDInterval ≤ ENNReal.ofReal a := by
      intro a ha
      have ha0 : 0 < a := lt_trans zero_lt_one ha
      rw [← (h_T018.2.2 GDInterval).1]
      exact ((h_T002 1 (GDLine '' GDInterval)).2 a ha0).2.2.2.2.1 (hz a ha)
    by_contra h
    have hlt : (1 : ℝ≥0∞) < dimH GDInterval := lt_of_not_ge h
    obtain ⟨a, ha0, ha1, had⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
    have ha : (1 : ℝ) < a := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa only [ENNReal.ofReal_one] using ha1)
    exact (not_lt_of_ge (hd a ha)) had

namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ (V : Set ℝ), Bornology.IsBounded V → V.Nonempty → ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ V ⊆ J ∧ MeasureTheory.volume J = Metric.ediam V + ENNReal.ofReal (2 * η)" := by
  intro V hV hne η hη
  refine ⟨Set.Ioo (sInf V - η) (sSup V + η), isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    have hx' := hV.subset_Icc_sInf_sSup hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  · rw [Real.volume_Ioo, Real.ediam_eq hV]
    have hnonneg : 0 ≤ sSup V - sInf V := sub_nonneg.mpr (Real.sInf_le_sSup V hV.bddBelow hV.bddAbove)
    rw [← ENNReal.ofReal_add hnonneg (by positivity)]
    congr 1
    ring

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ ε : ℝ≥0, (∑' i : ℕ, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i))) = (ε : ℝ≥0∞)" := by
  intro ε
  have heq (i : ℕ) : 2 * ((ε : ℝ) / 4 / 2 ^ i) = (ε : ℝ) / 2 / 2 ^ i := by ring
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' (ε : ℝ)), tsum_geometric_two']
  simp

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ U : ℕ → Set ℝ, GDInterval ⊆ ⋃ i, U i → (∀ i, Bornology.IsBounded (U i)) → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)" := by
  classical
  intro U hcover hbdd
  let K : Set ℕ := {i | (U i).Nonempty}
  have hcoverK : GDInterval ⊆ ⋃ i : K, U i.val := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
  have hsum : (1 : ℝ≥0∞) ≤ ∑' i : K, Metric.ediam (U i.val) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
    have hJ : ∀ i : K, ∃ J : Set ℝ, IsOpen J ∧ U i.val ⊆ J ∧
        MeasureTheory.volume J = Metric.ediam (U i.val) +
          ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i.val)) := by
      intro i
      exact yui_aux_0001 n E (U i.val) (hbdd i.val) i.property
        ((ε : ℝ) / 4 / 2 ^ i.val) (by positivity)
    choose J hJopen hJU hJvol using hJ
    have hcoverJ : GDInterval ⊆ ⋃ i : K, J i := by
      exact hcoverK.trans (Set.iUnion_mono fun i => hJU i)
    have herror : (∑' i : K, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i.val))) ≤
        (ε : ℝ≥0∞) := by
      calc
        _ ≤ ∑' i : ℕ, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i)) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
        _ = _ := yui_aux_0002 n E ε
    calc
      (1 : ℝ≥0∞) = MeasureTheory.volume GDInterval := by simp [GDInterval]
      _ ≤ MeasureTheory.volume (⋃ i : K, J i) := MeasureTheory.measure_mono hcoverJ
      _ ≤ ∑' i : K, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
      _ = (∑' i : K, Metric.ediam (U i.val)) +
            ∑' i : K, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i.val)) := by
        simp_rw [hJvol]
        exact ENNReal.tsum_add
      _ ≤ (∑' i : K, Metric.ediam (U i.val)) + (ε : ℝ≥0∞) :=
        add_le_add le_rfl herror
  exact hsum.trans (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
    (fun i : ℕ => Metric.ediam (U i)))

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ (ρ : ℝ≥0∞) (s : ℝ), ρ ≠ ⊤ → 0 ≤ s → ρ ^ s = ENNReal.ofReal (ρ.toReal ^ s)" := by
  intro ρ s hfin hs
  calc
    ρ ^ s = (ENNReal.ofReal ρ.toReal) ^ s :=
      congrArg (fun x : ℝ≥0∞ => x ^ s) (ENNReal.ofReal_toReal hfin).symm
    _ = ENNReal.ofReal (ρ.toReal ^ s) :=
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ ρ : ℝ≥0∞, ρ ≤ ENNReal.ofReal δ → ENNReal.ofReal (δ ^ (s - 1)) * ρ ≤ ρ ^ s" := by
  intro s δ hs hs1 hδ ρ hρ
  have hfin : ρ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hρ
  have hconv : ENNReal.ofReal ρ.toReal = ρ := ENNReal.ofReal_toReal hfin
  have hpowconv : ρ ^ s = ENNReal.ofReal (ρ.toReal ^ s) :=
    yui_aux_0004 n E ρ s hfin hs.le
  have hrδ : ρ.toReal ≤ δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hρ
    simpa [ENNReal.toReal_ofReal hδ.le] using h
  by_cases hzero : ρ = 0
  · simp [hzero, ENNReal.zero_rpow_of_pos hs]
  · have hrpos : 0 < ρ.toReal := ENNReal.toReal_pos hzero hfin
    have hreal : δ ^ (s - 1) * ρ.toReal ≤ ρ.toReal ^ s := by
      calc
        _ ≤ ρ.toReal ^ (s - 1) * ρ.toReal :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hrpos hrδ (by linarith)) hrpos.le
        _ = ρ.toReal ^ (s - 1) * ρ.toReal ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ρ.toReal ^ s := by
          rw [← Real.rpow_add hrpos]
          congr 1
          ring
    calc
      ENNReal.ofReal (δ ^ (s - 1)) * ρ =
          ENNReal.ofReal (δ ^ (s - 1)) * ENNReal.ofReal ρ.toReal := by rw [hconv]
      _ = ENNReal.ofReal (δ ^ (s - 1) * ρ.toReal) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)).symm
      _ ≤ ENNReal.ofReal (ρ.toReal ^ s) := ENNReal.ofReal_le_ofReal hreal
      _ = ρ ^ s := hpowconv.symm

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (E : Set (GDVec n))  :
    ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval := by
  classical
  intro s δ hs hs1 hδ
  unfold GDContent
  refine le_iInf fun U => le_iInf fun hcover => le_iInf fun hscale => ?_
  have hbdd : ∀ i, Bornology.IsBounded (U i) := by
    intro i
    exact Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hscale i))
  have hsum : (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) :=
    yui_aux_0003 n E U hcover hbdd
  have hcost : ∀ i, (Metric.ediam (U i)) ^ s ≤ GDCost s (U i) := by
    intro i
    by_cases hne : (U i).Nonempty
    · exact le_iSup_of_le hne le_rfl
    · have hempty : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, ENNReal.zero_rpow_of_pos hs]
  calc
    ENNReal.ofReal (δ ^ (s - 1)) = ENNReal.ofReal (δ ^ (s - 1)) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (δ ^ (s - 1)) * ∑' i, Metric.ediam (U i) :=
      mul_le_mul' le_rfl hsum
    _ = ∑' i, ENNReal.ofReal (δ ^ (s - 1)) * Metric.ediam (U i) :=
      ENNReal.tsum_mul_left.symm
    _ ≤ ∑' i, GDCost s (U i) := by
      exact ENNReal.tsum_le_tsum fun i =>
        (yui_aux_0005 n E s δ hs hs1 hδ (Metric.ediam (U i)) (hscale i)).trans (hcost i)

namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ M < δ ^ (s - 1)" := by
  intro s hs hs1 M
  have ht : Filter.Tendsto (fun δ : ℝ => δ ^ (s - 1)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hlarge : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), M < δ ^ (s - 1) := ht.eventually (Filter.eventually_gt_atTop M)
  have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  exact (hpos.and hlarge).exists

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤" := by
  intro s hs hs1
  by_contra hfinite
  obtain ⟨δ, hδ, hlarge⟩ := (@yui_aux_0001 n E h_T002 h_T005 h_T006 h_T018) s hs hs1 (GDMeasure s GDInterval).toReal
  have hstrict : GDMeasure s GDInterval < ENNReal.ofReal (δ ^ (s - 1)) := (ENNReal.lt_ofReal_iff_toReal_lt hfinite).2 hlarge
  have hbound : ENNReal.ofReal (δ ^ (s - 1)) ≤ GDMeasure s GDInterval := by
    exact (h_T006 s δ hs hs1 hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  exact (not_lt_of_ge hbound) hstrict

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH GDInterval" := by
  intro s hs hs1
  have hm : GDMeasure s (GDLine '' GDInterval) = ⊤ := by
    rw [(h_T018.2.2 GDInterval).2.2 s hs]
    exact (@yui_aux_0002 n E h_T002 h_T005 h_T006 h_T018) s hs hs1
  have hd : ENNReal.ofReal s ≤ dimH (GDLine '' GDInterval) := ((h_T002 1 (GDLine '' GDInterval)).2 s hs).2.2.2.2.2 hm
  rwa [(h_T018.2.2 GDInterval).1] at hd

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1) (h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) (h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A)) :
    dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤) := by
  have hfinite : dimH GDInterval ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h_T005.2
  have hlowerReal : (1 : ℝ) ≤ (dimH GDInterval).toReal := by
    by_contra h
    have ht : (dimH GDInterval).toReal < 1 := lt_of_not_ge h
    have hn : 0 ≤ (dimH GDInterval).toReal := ENNReal.toReal_nonneg
    let s : ℝ := ((dimH GDInterval).toReal + 1) / 2
    have hs : 0 < s := by dsimp [s]; linarith
    have hs1 : s < 1 := by dsimp [s]; linarith
    have hsd : ENNReal.ofReal s ≤ dimH GDInterval := (@yui_aux_0003 n E h_T002 h_T005 h_T006 h_T018) s hs hs1
    have hsr : s ≤ (dimH GDInterval).toReal := (ENNReal.ofReal_le_iff_le_toReal hfinite).1 hsd
    dsimp [s] at hsr
    linarith
  have hlower : (1 : ℝ≥0∞) ≤ dimH GDInterval := by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_iff_le_toReal hfinite).2 hlowerReal
  exact ⟨le_antisymm h_T005.2 hlower, h_T005.1, h_T006, @yui_aux_0002 n E h_T002 h_T005 h_T006 h_T018⟩

namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ q r ε : ℝ, dimH E < ENNReal.ofReal q → 0 < r → 0 < ε → 0 < q ∧ ∃ W : ℕ → Set (GDVec n), E ⊆ ⋃ i, W i ∧ (∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal r) ∧ (∑' i, GDCost q (W i)) < ENNReal.ofReal (ε / 2)" := by
  intro q r ε hq hr hε
  have hqp : 0 < q := by
    by_contra h
    have : ENNReal.ofReal q = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h)
    rw [this] at hq
    exact (not_lt_of_ge bot_le hq)
  have hm : GDMeasure q E = 0 := ((h_T002 n E).2 q hqp).2.2.1 hq
  have hc : GDContent q r E = 0 := by
    apply le_antisymm _ bot_le
    calc
      GDContent q r E ≤ GDMeasure q E := le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      _ = 0 := hm
  have ht : GDContent q r E < ENNReal.ofReal (ε / 2) := by rw [hc]; positivity
  simp only [GDContent, iInf_lt_iff] at ht
  rcases ht with ⟨W, hW, hd, hs⟩
  exact ⟨hqp, W, hW, hd, hs⟩

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "1 ≤ n → ∀ (x : GDVec n) (d : ℝ), 0 < d → (Metric.ball x (d / 2)).Nonempty ∧ Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal d" := by
  intro hn x d hd
  letI : NeZero n := ⟨by omega⟩
  constructor
  · exact ⟨x, Metric.mem_ball_self (by positivity)⟩
  · have hb : Metric.ediam (Metric.ball x (d / 2)) ≠ ⊤ := Metric.isBounded_ball.ediam_ne_top
    calc
      Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal (Metric.diam (Metric.ball x (d / 2))) := (ENNReal.ofReal_toReal hb).symm
      _ = ENNReal.ofReal d := by rw [Metric.diam_ball_eq x (by positivity)]; congr 1; ring

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ q r a : ℝ, 0 < q → 0 < r → 0 < a → 0 < min r (a ^ (1 / q)) ∧ min r (a ^ (1 / q)) ≤ r ∧ (ENNReal.ofReal (min r (a ^ (1 / q)))) ^ q ≤ ENNReal.ofReal a" := by
  intro q r a hq hr ha
  have hp : 0 < a ^ (1 / q) := Real.rpow_pos_of_pos ha _
  have hd : 0 < min r (a ^ (1 / q)) := lt_min hr hp
  refine ⟨hd, min_le_left _ _, ?_⟩
  rw [ENNReal.ofReal_rpow_of_pos hd]
  apply ENNReal.ofReal_le_ofReal
  calc
    (min r (a ^ (1 / q))) ^ q ≤ (a ^ (1 / q)) ^ q := Real.rpow_le_rpow hd.le (min_le_right _ _) hq.le
    _ = a := by rw [one_div, Real.rpow_inv_rpow ha.le hq.ne']

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ ε : ℝ, 0 < ε → (∀ i : ℕ, 0 < ε / 4 / 2 / (2 : ℝ) ^ i) ∧ (∑' i : ℕ, ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ i)) = ENNReal.ofReal (ε / 4)" := by
  intro ε hε
  constructor
  · intro i; positivity
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' (ε / 4)), tsum_geometric_two']

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "1 ≤ n → ∀ (q r a : ℝ) (W : Set (GDVec n)), 0 < q → 0 < r → 0 < a → W.Nonempty → Metric.ediam W ≤ ENNReal.ofReal r → ∃ U : Set (GDVec n), W ⊆ U ∧ U.Nonempty ∧ 0 < Metric.ediam U ∧ Metric.ediam U ≤ ENNReal.ofReal r ∧ (Metric.ediam U) ^ q ≤ GDCost q W + ENNReal.ofReal a" := by
  intro hn q r a W hq hr ha hW hWr
  classical
  by_cases hz : Metric.ediam W = 0
  · obtain ⟨x, hx⟩ := hW
    let d : ℝ := min r (a ^ (1 / q))
    have hd := @yui_aux_0003 n E h_T002 h_T004 q r a hq hr ha
    have hb := @yui_aux_0002 n E h_T002 h_T004 hn x d hd.1
    refine ⟨Metric.ball x (d / 2), ?_, hb.1, ?_, ?_, ?_⟩
    · intro y hy
      have hyx : y = x := (Metric.ediam_eq_zero_iff.mp hz) hy hx
      subst y
      exact Metric.mem_ball_self (by dsimp [d]; positivity)
    · rw [hb.2]; exact ENNReal.ofReal_pos.mpr hd.1
    · rw [hb.2]; exact ENNReal.ofReal_le_ofReal hd.2.1
    · rw [hb.2]
      exact hd.2.2.trans (le_add_left le_rfl)
  · refine ⟨W, Set.Subset.rfl, hW, pos_iff_ne_zero.mpr hz, hWr, ?_⟩
    have hc : GDCost q W = (Metric.ediam W) ^ q := by simp [GDCost, hW]
    rw [hc]
    exact le_add_right le_rfl

theorem yui_aux_0006 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ a b c : ℝ≥0∞, a ≤ b → a + c ≤ b + c" := by
  intro a b c h
  exact add_le_add h le_rfl

theorem yui_aux_0007 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) : yui_aux_type% "∀ (ε : ℝ) (K : Set ℕ) (a : ℕ → ℝ≥0∞) (b : K → ℝ≥0∞), 0 < ε → (∑' i, a i) < ENNReal.ofReal (ε / 2) → (∀ i, b i ≤ a i + ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ (i : ℕ))) → (∑' i, b i) < ENNReal.ofReal ε" := by
  intro ε K a b hε ha hb
  have hsum := (@yui_aux_0004 n E h_T002 h_T004 ε hε).2
  calc
    (∑' i, b i) ≤ ∑' i : K, (a i + ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ (i : ℕ))) := ENNReal.tsum_le_tsum hb
    _ ≤ ∑' i : ℕ, (a i + ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ i)) := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = (∑' i, a i) + ENNReal.ofReal (ε / 4) := by rw [ENNReal.tsum_add, hsum]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) := @yui_aux_0006 n E h_T002 h_T004 _ _ _ ha.le
    _ = ENNReal.ofReal (ε / 2 + ε / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) :
    1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε := by
  classical
  intro hn q r ε hq hr hr1 hε
  obtain ⟨hqp, W, hWE, hWr, hWs⟩ := @yui_aux_0001 n E h_T002 h_T004 q r ε hq hr hε
  let K : Set ℕ := {i | (W i).Nonempty}
  have hchoose : ∀ i : K, ∃ U : Set (GDVec n), W i ⊆ U ∧ U.Nonempty ∧ 0 < Metric.ediam U ∧ Metric.ediam U ≤ ENNReal.ofReal r ∧ (Metric.ediam U) ^ q ≤ GDCost q (W i) + ENNReal.ofReal (ε / 4 / 2 / (2 : ℝ) ^ (i : ℕ)) := by
    intro i
    exact @yui_aux_0005 n E h_T002 h_T004 hn q r (ε / 4 / 2 / (2 : ℝ) ^ (i : ℕ)) (W i) hqp hr ((@yui_aux_0004 n E h_T002 h_T004 ε hε).1 i) i.property (hWr i)
  choose U hU using hchoose
  refine ⟨K, U, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hWE hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, (hU ⟨i, ⟨x, hi⟩⟩).1 hi⟩
  · intro i
    exact ⟨(hU i).2.1, (hU i).2.2.1, (hU i).2.2.2.1⟩
  · exact @yui_aux_0007 n E h_T002 h_T004 ε K (fun i => GDCost q (W i)) (fun i => (Metric.ediam (U i)) ^ q) hε hWs (fun i => (hU i).2.2.2.2)

namespace Local_T009
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ (x y : GDVec n), dist x y ^ 2 = ∑ i : Fin n, dist (x i) (y i) ^ 2" := by
  intro x y
  exact PiLp.dist_sq_eq_of_L2 x y

end Local_T009
open Local_T009 in
theorem T009 (n : ℕ) (E : Set (GDVec n))  :
    (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t) := by
  constructor
  · intro x y t u
    rw [PiLp.dist_eq_of_L2, Fin.sum_univ_castSucc, yui_aux_0001 n E x y]
    simp [GDPoint, Real.dist_eq]
  · intro z
    refine ⟨WithLp.toLp 2 (fun i : Fin n => z i.castSucc), z (Fin.last n), ?_⟩
    ext i
    cases i using Fin.lastCases <;> simp [GDPoint]

namespace Local_T010
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ {X : Type} [PseudoEMetricSpace X] {ι : Type} [Countable ι] (A : Set X) (s δ : ℝ) (V : ι → Set X), A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → GDContent s δ A ≤ ∑' i, GDCost s (V i)" := by
  intro X _ ι _ A s δ V hV hd
  classical
  letI : Encodable ι := Encodable.ofCountable ι
  let W : ℕ → Set X := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
  unfold GDContent
  refine iInf_le_of_le W (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_))
  · simpa only [W, Encodable.iUnion_decode₂] using hV
  · intro j
    dsimp [W]
    rw [Metric.ediam_iUnion_mem_option]
    exact iSup₂_le fun b _ => hd b
  · exact le_of_eq (tsum_iUnion_decode₂ (GDCost s) (by simp [GDCost]) V)

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ {X Y : Type} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (f : X → Y), Isometry f → ∀ (s : ℝ) (A : Set X), GDMeasure s (f '' A) ≤ GDMeasure s A" := by
  intro X Y _ _ f hf s A
  have hc : ∀ δ : ℝ, GDContent s δ (f '' A) ≤ GDContent s δ A := by
    intro δ
    unfold GDContent
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    refine iInf_le_of_le (fun i => f '' U i) (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_))
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem f hi⟩
    · simpa only [hf.ediam_image] using hd
    · apply le_of_eq
      congr 1
      funext i
      simp only [GDCost, hf.ediam_image, Set.image_nonempty]
  unfold GDMeasure
  exact iSup₂_mono fun δ _ => hc δ

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ ρ ∧ (N : ℝ) ≤ 2 / ρ ∧ ∀ t ∈ GDInterval, ∃ j : Fin N, t ∈ Set.Icc ((j : ℕ) / (N : ℝ)) (((j : ℕ) + 1) / (N : ℝ))" := by
  intro ρ hρ hρ1
  let N : ℕ := ⌈1 / ρ⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hceil : 1 / ρ ≤ (N : ℝ) := Nat.le_ceil _
  have hlen : 1 / (N : ℝ) ≤ ρ := (div_le_iff₀ hNr).mpr (by nlinarith [(div_le_iff₀ hρ).mp hceil])
  refine ⟨N, hN, hlen, ?_, ?_⟩
  · have hc : (N : ℝ) < 1 / ρ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hh : 1 ≤ 1 / ρ := (le_div_iff₀ hρ).mpr (by simpa using hρ1)
    calc (N : ℝ) ≤ 1 / ρ + 1 := hc.le
      _ ≤ 1 / ρ + 1 / ρ := add_le_add_right hh _
      _ = 2 / ρ := by ring
  · intro t ht
    change 0 ≤ t ∧ t ≤ 1 at ht
    by_cases ht1 : t = 1
    · refine ⟨⟨N - 1, Nat.sub_lt hN (by omega)⟩, ?_⟩
      have hncast : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast (Nat.sub_add_cancel hN)
      dsimp
      rw [ht1]
      constructor
      · apply (div_le_iff₀ hNr).mpr
        linarith
      · rw [hncast, div_self (ne_of_gt hNr)]
    · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have htn : t * N < (N : ℝ) := by nlinarith
      have htn0 : 0 ≤ t * N := mul_nonneg ht.1 hNr.le
      have hj : ⌊t * (N : ℝ)⌋₊ < N := (Nat.floor_lt htn0).mpr htn
      refine ⟨⟨⌊t * (N : ℝ)⌋₊, hj⟩, ?_⟩
      constructor
      · exact (div_le_iff₀ hNr).mpr (Nat.floor_le htn0)
      · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one _).le

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (U : Set (GDVec n)) (ρ a b : ℝ), 0 ≤ ρ → Metric.ediam U ≤ ENNReal.ofReal ρ → b - a ≤ ρ → Metric.ediam {z | ∃ x ∈ U, ∃ t ∈ Set.Icc a b, z = GDPoint x t} ≤ ENNReal.ofReal (Real.sqrt 2 * ρ)" := by
  intro U ρ a b hρ hU hab
  apply Metric.ediam_le_of_forall_dist_le
  rintro _ ⟨x, hx, t, ht, rfl⟩ _ ⟨y, hy, u, hu, rfl⟩
  have hxy : dist x y ≤ ρ := by
    have he : edist x y ≤ ENNReal.ofReal ρ := (Metric.edist_le_ediam_of_mem hx hy).trans hU
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hρ] at he
    exact he
  have htu : |t - u| ≤ ρ := abs_le.mpr ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
  rw [h_T009.1]
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow, hs]
    have hx2 : dist x y ^ 2 ≤ ρ ^ 2 := by gcongr
    have ht2 : |t - u| ^ 2 ≤ ρ ^ 2 := by gcongr
    linarith

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (q ρ : ℝ) (N : ℕ), 0 < ρ → (N : ℝ) ≤ 2 / ρ → (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * ρ)) ^ (q + 1) ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * (ENNReal.ofReal ρ) ^ q" := by
  intro q ρ N hρ hN
  have hs : 0 < Real.sqrt 2 := by positivity
  have hid : (2 / ρ) * (Real.sqrt 2 * ρ) ^ (q + 1) = (2 * (Real.sqrt 2) ^ (q + 1)) * ρ ^ q := by
    rw [Real.mul_rpow hs.le hρ.le, Real.rpow_add_one (ne_of_gt hρ)]
    field_simp
    <;> ring
  have hr : (N : ℝ) * (Real.sqrt 2 * ρ) ^ (q + 1) ≤ (2 * (Real.sqrt 2) ^ (q + 1)) * ρ ^ q := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (by positivity) _)
  have he := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (Real.sqrt 2) ^ (q + 1)), ENNReal.ofReal_rpow_of_pos (mul_pos hs hρ), ENNReal.ofReal_rpow_of_pos hρ] using he

theorem yui_aux_0006 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (K : Set ℕ) (N : K → ℕ) (c : K → ℝ≥0∞), (∑' p : Σ i : K, Fin (N i), c p.1) = ∑' i : K, (N i : ℝ≥0∞) * c i" := by
  intro K N c
  rw [ENNReal.tsum_sigma' (fun p : Σ i : K, Fin (N i) => c p.1)]
  apply tsum_congr
  intro i
  simp [tsum_fintype]

theorem yui_aux_0007 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (K : Set ℕ) (N : K → ℕ) (ρ : K → ℝ) (q : ℝ), (∑' p : Σ i : K, Fin (N i), (ENNReal.ofReal (Real.sqrt 2 * ρ p.1)) ^ (q + 1)) = ∑' i : K, (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * ρ i)) ^ (q + 1)" := by
  intro K N ρ q
  exact @yui_aux_0006 n E h_T002 h_T004 h_T007 h_T008 h_T009 K N (fun i : K => (ENNReal.ofReal (Real.sqrt 2 * ρ i)) ^ (q + 1))

theorem yui_aux_0008 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ q δ r ε : ℝ, 0 < q → 0 < δ → 0 < r → r ≤ 1 → Real.sqrt 2 * r ≤ δ → GDPositiveCover E q r ε → GDContent (q + 1) δ (GDProduct E) < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * ENNReal.ofReal ε" := by
  intro q δ r ε hq hδ hr hr1 hscale hcover
  classical
  obtain ⟨K, U, hU, hUd, hsum⟩ := hcover
  let ρ : K → ℝ := fun i => (Metric.ediam (U i)).toReal
  have hfin (i : K) : Metric.ediam (U i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hUd i).2.2
  have hρpos (i : K) : 0 < ρ i :=
    ENNReal.toReal_pos_iff.mpr ⟨(hUd i).2.1, lt_top_iff_ne_top.mpr (hfin i)⟩
  have hρle (i : K) : ρ i ≤ r :=
    ENNReal.toReal_le_of_le_ofReal hr.le (hUd i).2.2
  have hρeq (i : K) : ENNReal.ofReal (ρ i) = Metric.ediam (U i) :=
    ENNReal.ofReal_toReal (hfin i)
  have hparts (i : K) := @yui_aux_0003 n E h_T002 h_T004 h_T007 h_T008 h_T009 (ρ i) (hρpos i) ((hρle i).trans hr1)
  choose N hNp hNl hNc hNcov using hparts
  let V : (Σ i : K, Fin (N i)) → Set (GDVec (n + 1)) := fun p =>
    {z | ∃ x ∈ U p.1, ∃ t ∈ Set.Icc ((p.2 : ℕ) / (N p.1 : ℝ)) (((p.2 : ℕ) + 1) / (N p.1 : ℝ)), z = GDPoint x t}
  have hV : GDProduct E ⊆ ⋃ p, V p := by
    rintro z ⟨x, hx, t, ht, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
    obtain ⟨j, hj⟩ := hNcov i t ht
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, x, hi, t, hj, rfl⟩
  have hdV (p : Σ i : K, Fin (N i)) :
      Metric.ediam (V p) ≤ ENNReal.ofReal (Real.sqrt 2 * ρ p.1) := by
    apply @yui_aux_0004 n E h_T002 h_T004 h_T007 h_T008 h_T009
      (U p.1) (ρ p.1) _ _ (hρpos p.1).le
    · exact (hρeq p.1).ge
    · calc
        ((p.2 : ℕ) + 1) / (N p.1 : ℝ) - (p.2 : ℕ) / (N p.1 : ℝ) = 1 / (N p.1 : ℝ) := by ring
        _ ≤ ρ p.1 := hNl p.1
  have hdδ (p : Σ i : K, Fin (N i)) : Metric.ediam (V p) ≤ ENNReal.ofReal δ := by
    apply (hdV p).trans
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left (hρle p.1) (Real.sqrt_nonneg 2)).trans hscale
  have hcost (p : Σ i : K, Fin (N i)) :
      GDCost (q + 1) (V p) ≤ (ENNReal.ofReal (Real.sqrt 2 * ρ p.1)) ^ (q + 1) := by
    unfold GDCost
    exact iSup_le fun _ => ENNReal.rpow_le_rpow (hdV p) (by linarith)
  have htotal : (∑' p, GDCost (q + 1) (V p)) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * ∑' i, (Metric.ediam (U i)) ^ q := by
    calc
      (∑' p, GDCost (q + 1) (V p)) ≤ ∑' p : Σ i : K, Fin (N i), (ENNReal.ofReal (Real.sqrt 2 * ρ p.1)) ^ (q + 1) :=
        ENNReal.tsum_le_tsum hcost
      _ = ∑' i : K, (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * ρ i)) ^ (q + 1) := @yui_aux_0007 n E h_T002 h_T004 h_T007 h_T008 h_T009 K N ρ q
      _ ≤ ∑' i : K, ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * (Metric.ediam (U i)) ^ q := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [← hρeq i]
        exact @yui_aux_0005 n E h_T002 h_T004 h_T007 h_T008 h_T009 q (ρ i) (N i) (hρpos i) (hNc i)
      _ = _ := ENNReal.tsum_mul_left
  have hcpos : 0 < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) := by positivity
  exact lt_of_le_of_lt
    ((@yui_aux_0001 n E h_T002 h_T004 h_T007 h_T008 h_T009
      (GDVec (n + 1)) _ (Σ i : K, Fin (N i)) _ (GDProduct E) (q + 1) δ V hV hdδ).trans htotal)
    (ENNReal.mul_lt_mul_right (ne_of_gt hcpos) ENNReal.ofReal_ne_top hsum)

theorem yui_aux_0009 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (x : ℝ≥0∞) (C : ℝ), 0 < C → (∀ ε : ℝ, 0 < ε → x < ENNReal.ofReal C * ENNReal.ofReal ε) → x = 0" := by
  intro x C hC h
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hh := h ((ε : ℝ) / C) (div_pos hεr hC)
  have heq : ENNReal.ofReal C * ENNReal.ofReal ((ε : ℝ) / C) = (ε : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ (ne_of_gt hC)]
    exact ENNReal.ofReal_coe_nnreal
  simpa only [zero_add, heq] using hh.le

theorem yui_aux_0010 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → GDMeasure (q + 1) (GDProduct E) = 0" := by
  intro hn q hqD
  have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hqD)
  have hc : ∀ δ : ℝ, 0 < δ → GDContent (q + 1) δ (GDProduct E) = 0 := by
    intro δ hδ
    have hs : 0 < Real.sqrt 2 := by positivity
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hr : 0 < r := lt_min zero_lt_one (div_pos hδ hs)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hscale : Real.sqrt 2 * r ≤ δ := by
      have hh : r ≤ δ / Real.sqrt 2 := min_le_right _ _
      simpa only [mul_comm] using (le_div_iff₀ hs).mp hh
    apply @yui_aux_0009 n E h_T002 h_T004 h_T007 h_T008 h_T009
      (GDContent (q + 1) δ (GDProduct E)) (2 * (Real.sqrt 2) ^ (q + 1)) (by positivity)
    intro ε hε
    exact @yui_aux_0008 n E h_T002 h_T004 h_T007 h_T008 h_T009 q δ r ε hq hδ hr hr1 hscale
      (h_T008 hn q r ε hqD hr hr1 hε)
  unfold GDMeasure
  apply le_antisymm _ zero_le
  exact iSup₂_le fun δ hδ => (hc δ hδ).le

theorem yui_aux_0011 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "n = 0 → ∀ a : ℝ, 1 < a → GDMeasure a (GDProduct E) = 0" := by
  intro hn a ha
  have he : E = Set.univ := (h_T004.2.2.2.2.2 hn).1
  haveI : Subsingleton (GDVec n) := by subst n; infer_instance
  let f : ℝ → GDVec (n + 1) := fun t => GDPoint (0 : GDVec n) t
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    dsimp [f]
    rw [h_T009.1, dist_self]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have himage : GDProduct E = f '' GDInterval := by
    ext z
    constructor
    · rintro ⟨x, hx, t, ht, hz⟩
      refine ⟨t, ht, ?_⟩
      dsimp [f]
      rw [Subsingleton.elim x (0 : GDVec n)] at hz
      exact hz.symm
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, by rw [he]; trivial, t, ht, rfl⟩
  rw [himage]
  apply le_antisymm _ zero_le
  exact (@yui_aux_0002 n E h_T002 h_T004 h_T007 h_T008 h_T009
    ℝ (GDVec (n + 1)) _ _ f hf a GDInterval).trans (h_T007.2.1 a ha).le

theorem yui_aux_0012 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ b D : ℝ≥0∞, D < ⊤ → (∀ q : ℝ, D < ENNReal.ofReal q → b ≤ ENNReal.ofReal (q + 1)) → b ≤ D + 1" := by
  intro b D hD h
  by_contra hb
  have hDb : D + 1 < b := lt_of_not_ge hb
  obtain ⟨a, ha0, ha, hab⟩ := ENNReal.lt_iff_exists_real_btwn.mp hDb
  have hplus : ENNReal.ofReal (D.toReal + 1) = D + 1 := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hD.ne, ENNReal.ofReal_one]
  have haR : D.toReal + 1 < a := by
    rw [← hplus] at ha
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp ha
  have hq : D < ENNReal.ofReal (a - 1) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hD.ne).mpr (by linarith)
  have hb' := h (a - 1) hq
  have heq : a - 1 + 1 = a := by ring
  rw [heq] at hb'
  exact (not_lt_of_ge hb') hab

end Local_T010
open Local_T010 in
theorem T010 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) :
    dimH (GDProduct E) ≤ dimH E + 1 ∧ dimH (GDProduct E) < ⊤ := by
  have hm : ∀ q : ℝ, dimH E < ENNReal.ofReal q →
      GDMeasure (q + 1) (GDProduct E) = 0 := by
    intro q hqD
    by_cases hn : n = 0
    · have hD0 : dimH E = 0 := (h_T004.2.2.2.2.2 hn).2
      have hq : 0 < q := by
        rw [hD0] at hqD
        exact ENNReal.ofReal_pos.mp hqD
      exact @yui_aux_0011 n E h_T002 h_T004 h_T007 h_T008 h_T009 hn (q + 1) (by linarith)
    · exact @yui_aux_0010 n E h_T002 h_T004 h_T007 h_T008 h_T009 (by omega) q hqD
  have hb : dimH (GDProduct E) ≤ dimH E + 1 := by
    apply @yui_aux_0012 n E h_T002 h_T004 h_T007 h_T008 h_T009
      (dimH (GDProduct E)) (dimH E) h_T004.2.2.2.1
    intro q hqD
    have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hqD)
    exact ((h_T002 (n + 1) (GDProduct E)).2 (q + 1) (by linarith)).2.2.2.2.1 (hm q hqD)
  exact ⟨hb, lt_of_le_of_lt hb (ENNReal.add_lt_top.mpr ⟨h_T004.2.2.2.1, by norm_num⟩)⟩

namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∃ (p : GDVec (n + 1) → GDVec n) (q : GDVec (n + 1) → ℝ), (∀ x t, p (GDPoint x t) = x ∧ q (GDPoint x t) = t) ∧ LipschitzWith 1 p ∧ LipschitzWith 1 q" := by
  classical
    let p : GDVec (n + 1) → GDVec n := fun z => Classical.choose (h_T009.2 z)
    let q : GDVec (n + 1) → ℝ := fun z => Classical.choose (Classical.choose_spec (h_T009.2 z))
    have hd (z) : z = GDPoint (p z) (q z) := Classical.choose_spec (Classical.choose_spec (h_T009.2 z))
    have hinj {x y : GDVec n} {t u : ℝ} (h : GDPoint x t = GDPoint y u) : x = y ∧ t = u := by
      have hz : dist (GDPoint x t) (GDPoint y u) = 0 := by rw [h, dist_self]
      rw [h_T009.1] at hz
      have ha : dist x y ^ 2 + |t - u| ^ 2 = 0 :=
        (Real.sqrt_eq_zero (by positivity)).mp hz
      have hxy : dist x y = 0 := by nlinarith [sq_nonneg (dist x y), sq_nonneg |t-u|]
      have htu : t - u = 0 := by nlinarith [sq_abs (t-u), sq_nonneg (t-u), sq_nonneg (dist x y)]
      exact ⟨dist_eq_zero.mp hxy, sub_eq_zero.mp htu⟩
    refine ⟨p, q, ?_, ?_, ?_⟩
    · intro x t
      exact hinj (hd (GDPoint x t)).symm
    · apply LipschitzWith.of_dist_le_mul
      intro z w
      have h := h_T009.1 (p z) (p w) (q z) (q w)
      rw [← hd z, ← hd w] at h
      simp only [NNReal.coe_one, one_mul]
      rw [h]
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg |q z - q w|])
    · apply LipschitzWith.of_dist_le_mul
      intro z w
      have h := h_T009.1 (p z) (p w) (q z) (q w)
      rw [← hd z, ← hd w] at h
      simp only [NNReal.coe_one, one_mul, Real.dist_eq]
      rw [h]
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (dist (p z) (p w))])

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (s δ : ℝ) (K : Set ℕ) (U : K → Set (GDVec n)) (w : K → ℝ≥0∞),\n E ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ) →\n (∀ i, GDCost s (U i) ≤ w i) → GDContent s δ E ≤ ∑' i, w i" := by
  classical
    intro s δ K U w hcov hdiam hcost
    let W : ℕ → Set (GDVec n) := fun j => if h : j ∈ K then U ⟨j,h⟩ else ∅
    have hc : E ⊆ ⋃ j, W j := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
      exact Set.mem_iUnion.mpr ⟨i.val, by simpa [W, i.property] using hi⟩
    have hd : ∀ j, Metric.ediam (W j) ≤ ENNReal.ofReal δ := by
      intro j
      by_cases hj : j ∈ K
      · simpa [W, hj] using hdiam ⟨j,hj⟩
      · simp [W, hj]
    have heq : (∑' j, GDCost s (W j)) = ∑' i : K, GDCost s (U i) := by
      have hsub := tsum_subtype K (fun j => GDCost s (W j))
      have hind : K.indicator (fun j => GDCost s (W j)) = (fun j => GDCost s (W j)) := by
        funext j
        by_cases hj : j ∈ K <;> simp [Set.indicator, W, hj, GDCost]
      rw [hind] at hsub
      simpa [W] using hsub.symm
    calc
      GDContent s δ E ≤ ∑' j, GDCost s (W j) :=
        iInf_le_of_le W (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))
      _ = ∑' i : K, GDCost s (U i) := heq
      _ ≤ ∑' i, w i := ENNReal.tsum_le_tsum hcost

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → 0 < η →\n  Metric.ediam B ≤ ENNReal.ofReal ρ →\n  ∃ J : Set ℝ, IsOpen J ∧ B ⊆ J ∧ MeasureTheory.volume J ≤ ENNReal.ofReal (ρ + η)" := by
  classical
    intro B ρ η hB hρ hη hd
    have hb : Bornology.IsBounded B := Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd)
    let a := sInf B
    let b := sSup B
    have hlen : b - a ≤ ρ := by
      rw [← Real.diam_eq hb]
      exact ENNReal.toReal_le_of_le_ofReal hρ hd
    refine ⟨Set.Ioo (a - η/2) (b + η/2), isOpen_Ioo, ?_, ?_⟩
    · intro x hx
      have hx' := hb.subset_Icc_sInf_sSup hx
      constructor <;> dsimp [a,b] at * <;> linarith [hx'.1,hx'.2]
    · rw [Real.volume_Ioo]
      apply ENNReal.ofReal_le_ofReal
      linarith

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) ∧\n (∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1)) = 1" := by
  classical
    constructor
    · simp [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
    · rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (K : Set ℕ) (a : K → ℝ) (ε : ℝ), (∀ i, 0 ≤ a i) → 0 < ε →\n ∃ η : K → ℝ, (∀ i, 0 < η i) ∧\n   (∑' i, ENNReal.ofReal (a i) * ENNReal.ofReal (η i)) ≤ ENNReal.ofReal ε" := by
  classical
    intro K a ε ha hε
    let η : K → ℝ := fun i => ε * (1/2 : ℝ) ^ (i.val + 1) / (1 + a i)
    have hη (i : K) : 0 < η i := by
      dsimp [η]
      exact div_pos (mul_pos hε (pow_pos (by norm_num) _)) (by linarith [ha i])
    refine ⟨η, hη, ?_⟩
    have hterm (i : K) : ENNReal.ofReal (a i) * ENNReal.ofReal (η i) ≤
        ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (i.val + 1) := by
      have hr : η i * a i ≤ ε * (1/2 : ℝ) ^ (i.val + 1) := by
        dsimp [η]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by linarith [ha i])).mpr
        have hp : 0 ≤ ε * (1/2 : ℝ) ^ (i.val + 1) := by positivity
        nlinarith
      calc
        ENNReal.ofReal (a i) * ENNReal.ofReal (η i) = ENNReal.ofReal (η i * a i) := by
          rw [ENNReal.ofReal_mul (hη i).le, mul_comm]
        _ ≤ ENNReal.ofReal (ε * (1/2 : ℝ) ^ (i.val + 1)) := ENNReal.ofReal_le_ofReal hr
        _ = ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (i.val + 1) := by
          rw [ENNReal.ofReal_mul hε.le, ENNReal.ofReal_pow (by norm_num)]
          rw [(@yui_aux_0004 n E h_T004 h_T009).1]
    calc
      (∑' i, ENNReal.ofReal (a i) * ENNReal.ofReal (η i)) ≤
          ∑' i : K, ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (i.val + 1) :=
        ENNReal.tsum_le_tsum hterm
      _ ≤ ∑' j : ℕ, ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (j + 1) :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ENNReal.ofReal ε := by
        rw [ENNReal.tsum_mul_left, (@yui_aux_0004 n E h_T004 h_T009).2, mul_one]

theorem yui_aux_0006 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (K : Set ℕ) (c : ℝ≥0∞) (w L : K → ℝ≥0∞) (J : K → Set ℝ),\n (∀ i, IsOpen (J i)) → (∀ i, MeasureTheory.volume (J i) ≤ L i) →\n (∀ t ∈ GDInterval, c ≤ ∑' i, (J i).indicator (fun _ => w i) t) →\n c ≤ ∑' i, w i * L i" := by
  classical
    intro K c w L J hopen hlen hpoint
    have hm (i : K) : Measurable ((J i).indicator (fun _ : ℝ => w i)) :=
      measurable_const.indicator (hopen i).measurableSet
    have hc : (∫⁻ _ : ℝ, c ∂(MeasureTheory.volume.restrict GDInterval)) = c := by
      simp [MeasureTheory.lintegral_const, GDInterval]
    calc
      c = ∫⁻ _ : ℝ, c ∂(MeasureTheory.volume.restrict GDInterval) := hc.symm
      _ ≤ ∫⁻ t : ℝ, ∑' i, (J i).indicator (fun _ => w i) t
          ∂(MeasureTheory.volume.restrict GDInterval) := by
        apply MeasureTheory.lintegral_mono_ae
        exact (MeasureTheory.ae_restrict_mem (show MeasurableSet GDInterval from measurableSet_Icc)).mono hpoint
      _ = ∑' i, ∫⁻ t : ℝ, (J i).indicator (fun _ => w i) t
          ∂(MeasureTheory.volume.restrict GDInterval) :=
        MeasureTheory.lintegral_tsum (fun i => (hm i).aemeasurable)
      _ ≤ ∑' i, w i * L i := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [MeasureTheory.lintegral_indicator_const (hopen i).measurableSet]
        exact mul_le_mul_left' ((MeasureTheory.Measure.restrict_apply_le GDInterval (J i)).trans (hlen i)) _

theorem yui_aux_0007 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (d : ℝ≥0∞) (s : ℝ), d ≠ ⊤ → 0 < s →\n ENNReal.ofReal d.toReal = d ∧\n ENNReal.ofReal (d.toReal ^ s) = d ^ s ∧\n d ^ s * d = d ^ (s + 1)" := by
  classical
    intro d s hd hs
    have he : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hd
    refine ⟨he, ?_, ?_⟩
    · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le, he]
    · rw [ENNReal.rpow_add_of_add_pos hd s 1 (by linarith), ENNReal.rpow_one]

theorem yui_aux_0008 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (s δ : ℝ), 0 < s →\n ∀ (p : GDVec (n + 1) → GDVec n) (q : GDVec (n + 1) → ℝ),\n (∀ x t, p (GDPoint x t) = x ∧ q (GDPoint x t) = t) →\n LipschitzWith 1 p →\n ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))) (J : K → Set ℝ),\n GDProduct E ⊆ ⋃ i, V i →\n (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →\n (∀ i, q '' V i ⊆ J i) →\n ∀ t ∈ GDInterval, GDContent s δ E ≤\n   ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t" := by
  classical
    intro s δ hs p q hinv hp K V J hcov hd hJ t ht
    let U : K → Set (GDVec n) := fun i => if t ∈ J i then p '' V i else ∅
    have hproj (i : K) : Metric.ediam (p '' V i) ≤ Metric.ediam (V i) := by
      simpa using hp.ediam_image_le (V i)
    apply @yui_aux_0002 n E h_T004 h_T009 s δ K U
      (fun i => (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t)
    · intro x hx
      have hxt : GDPoint x t ∈ GDProduct E := ⟨x, hx, t, ht, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hxt)
      have hti : t ∈ J i := hJ i ⟨GDPoint x t, hi, (hinv x t).2⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simp only [U, if_pos hti]
      exact ⟨GDPoint x t, hi, (hinv x t).1⟩
    · intro i
      by_cases hti : t ∈ J i
      · simpa [U, hti] using (hproj i).trans (hd i)
      · simp [U, hti]
    · intro i
      by_cases hti : t ∈ J i
      · simp only [U, if_pos hti, Set.indicator_of_mem hti]
        exact iSup_le fun _ => ENNReal.rpow_le_rpow (hproj i) hs.le
      · simp [U, hti, Set.indicator_of_notMem, GDCost]

theorem yui_aux_0009 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (a b c : ℝ≥0∞), b ≤ c → a + b ≤ a + c" := by
  classical
    intro a b c h
    exact add_le_add (le_refl a) h

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) :
    ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε := by
  classical
    intro s δ hs hδ K V hcov hV ε hε
    have hcfinite : GDContent s δ E < ⊤ := h_T004.2.2.2.2.1 s δ hs hδ
    obtain ⟨p, q, hinv, hp, hq⟩ := @yui_aux_0001 n E h_T004 h_T009
    let ρ : K → ℝ := fun i => (Metric.ediam (V i)).toReal
    have hfinite (i : K) : Metric.ediam (V i) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV i).2
    have hconv (i : K) :
        ENNReal.ofReal (ρ i) = Metric.ediam (V i) ∧
        ENNReal.ofReal (ρ i ^ s) = Metric.ediam (V i) ^ s ∧
        Metric.ediam (V i) ^ s * Metric.ediam (V i) = Metric.ediam (V i) ^ (s + 1) :=
      @yui_aux_0007 n E h_T004 h_T009 (Metric.ediam (V i)) s (hfinite i) hs
    obtain ⟨η, hη, herr⟩ := @yui_aux_0005 n E h_T004 h_T009 K
      (fun i => ρ i ^ s) ε (fun i => Real.rpow_nonneg ENNReal.toReal_nonneg s) hε
    have hex (i : K) : ∃ J : Set ℝ, IsOpen J ∧ q '' V i ⊆ J ∧
        MeasureTheory.volume J ≤ ENNReal.ofReal (ρ i + η i) := by
      apply @yui_aux_0003 n E h_T004 h_T009 (q '' V i) (ρ i) (η i)
        ((hV i).1.image q) ENNReal.toReal_nonneg (hη i)
      rw [(hconv i).1]
      simpa using hq.ediam_image_le (V i)
    choose J hopen hinc hlen using hex
    have hpoint : ∀ t ∈ GDInterval, GDContent s δ E ≤
        ∑' i, (J i).indicator (fun _ => Metric.ediam (V i) ^ s) t :=
      @yui_aux_0008 n E h_T004 h_T009 s δ hs p q hinv hp K V J hcov
        (fun i => (hV i).2) hinc
    have hint : GDContent s δ E ≤
        ∑' i, Metric.ediam (V i) ^ s * ENNReal.ofReal (ρ i + η i) :=
      @yui_aux_0006 n E h_T004 h_T009 K (GDContent s δ E)
        (fun i => Metric.ediam (V i) ^ s)
        (fun i => ENNReal.ofReal (ρ i + η i)) J hopen hlen hpoint
    have herr' : (∑' i, Metric.ediam (V i) ^ s * ENNReal.ofReal (η i)) ≤
        ENNReal.ofReal ε := by
      simpa only [(hconv _).2.1] using herr
    calc
      GDContent s δ E ≤ ∑' i, Metric.ediam (V i) ^ s * ENNReal.ofReal (ρ i + η i) := hint
      _ = ∑' i, (Metric.ediam (V i) ^ (s + 1) +
          Metric.ediam (V i) ^ s * ENNReal.ofReal (η i)) := by
        apply tsum_congr
        intro i
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (hη i).le, mul_add,
          (hconv i).1, (hconv i).2.2]
      _ = (∑' i, Metric.ediam (V i) ^ (s + 1)) +
          ∑' i, Metric.ediam (V i) ^ s * ENNReal.ofReal (η i) := ENNReal.tsum_add
      _ ≤ (∑' i, Metric.ediam (V i) ^ (s + 1)) + ENNReal.ofReal ε :=
        @yui_aux_0009 n E h_T004 h_T009 _ _ _ herr'

namespace Local_T012
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (ε : ℝ≥0), 0 < ε → 0 < (ε : ℝ) ∧ ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞)" := by
  intro ε hε
  exact ⟨by exact_mod_cast hε, ENNReal.ofReal_coe_nnreal⟩

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (q : ℝ) (U : ℕ → Set (GDVec (n + 1))), (∑' i : {j : ℕ | (U j).Nonempty}, GDCost q (U i)) = ∑' i, GDCost q (U i)" := by
  classical
  intro q U
  refine tsum_subtype_eq_of_support_subset (f := fun i : ℕ => GDCost q (U i)) (s := {j : ℕ | (U j).Nonempty}) ?_
  intro i hi
  change (U i).Nonempty
  by_contra hempty
  have hz : GDCost q (U i) = 0 := by simp [GDCost, hempty]
  exact hi hz

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (q : ℝ) (A : Set (GDVec (n + 1))), A.Nonempty → GDCost q A = (Metric.ediam A) ^ q" := by
  intro q A hA
  unfold GDCost
  exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup_of_le hA le_rfl)

end Local_T012
open Local_T012 in
theorem T012 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) :
    ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ E ≤ GDContent (s + 1) δ (GDProduct E) := by
  classical
  intro s δ hs hδ
  conv_rhs => unfold GDContent
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
  let K : Set ℕ := {i | (U i).Nonempty}
  let V : K → Set (GDVec (n + 1)) := fun i => U i
  have hcover : GDProduct E ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
  have hdiam : ∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ := by
    intro i
    exact ⟨i.property, hd i⟩
  have hsum : (∑' i : K, (Metric.ediam (V i)) ^ (s + 1)) =
      ∑' i, GDCost (s + 1) (U i) := by
    calc
      (∑' i : K, (Metric.ediam (V i)) ^ (s + 1)) =
          ∑' i : K, GDCost (s + 1) (U i) := by
        apply tsum_congr
        intro i
        exact (@yui_aux_0003 n E h_T011 (s + 1) (U i) i.property).symm
      _ = ∑' i, GDCost (s + 1) (U i) :=
        @yui_aux_0002 n E h_T011 (s + 1) U
  by_cases hinf : (∑' i, GDCost (s + 1) (U i)) = ⊤
  · rw [hinf]
    exact le_top
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨hεreal, hεcoe⟩ := @yui_aux_0001 n E h_T011 ε hε
    have h := h_T011 s δ hs hδ K V hcover hdiam (ε : ℝ) hεreal
    rw [hsum, hεcoe] at h
    exact h

theorem T013 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T012 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ E ≤ GDContent (s + 1) δ (GDProduct E)) :
    ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤ := by
  intro s hs hsd
  have hE : GDMeasure s E = ⊤ := (h_T002 n E).2 s hs |>.2.1 hsd
  unfold GDMeasure at hE ⊢
  apply iSup_eq_top.mpr
  intro M hM
  have hbound : M < ⨆ δ : ℝ, ⨆ (_ : 0 < δ), GDContent s δ E := by
    rw [hE]
    exact hM
  obtain ⟨δ, hδ⟩ := lt_iSup_iff.mp hbound
  obtain ⟨hδpos, hδbound⟩ := lt_iSup_iff.mp hδ
  refine ⟨δ, ?_⟩
  apply lt_iSup_iff.mpr
  exact ⟨hδpos, lt_of_lt_of_le hδbound (h_T012 s δ hs hδpos)⟩

namespace Local_T014
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤) : yui_aux_type% "∀ (d : ℝ) (Q : ℝ≥0∞), 0 < d → (∀ s : ℝ, 0 < s → s < d → ENNReal.ofReal (s + 1) ≤ Q) → ENNReal.ofReal (d + 1) ≤ Q" := by
  intro d Q hd h
  by_cases hQ : Q = ⊤
  · simp [hQ]
  by_contra hn
  have hlt : Q.toReal < d + 1 := by
    by_contra hh
    exact hn (ENNReal.ofReal_le_of_le_toReal (le_of_not_gt hh))
  let a : ℝ := max 0 (Q.toReal - 1)
  have had : a < d := max_lt hd (by linarith)
  let s : ℝ := (a + d) / 2
  have ha0 : 0 ≤ a := le_max_left _ _
  have has : a < s := by dsimp [s]; linarith
  have hs0 : 0 < s := lt_of_le_of_lt ha0 has
  have hsd : s < d := by dsimp [s]; linarith
  have hb : ENNReal.ofReal (s + 1) ≤ Q := h s hs0 hsd
  have hb' : s + 1 ≤ Q.toReal := by
    have ht := ENNReal.toReal_mono hQ hb
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ s + 1)] using ht
  have hqa : Q.toReal - 1 ≤ a := le_max_right _ _
  linarith

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤) : yui_aux_type% "∀ s : ℝ, 0 ≤ s → s < (dimH E).toReal → ENNReal.ofReal s < dimH E" := by
  intro s hs hsd
  have hD : dimH E ≠ ⊤ := h_T004.2.2.2.1.ne
  apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hD).mp
  simpa only [ENNReal.toReal_ofReal hs] using hsd

end Local_T014
open Local_T014 in
theorem T014 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤) :
    0 < dimH E → dimH E + 1 ≤ dimH (GDProduct E) := by
  intro hpos
  have hfinite : dimH E < ⊤ := h_T004.2.2.2.1
  have hdpos : 0 < (dimH E).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hpos, hfinite⟩
  have hend : ENNReal.ofReal ((dimH E).toReal + 1) ≤ dimH (GDProduct E) := by
    apply (@yui_aux_0001 n E h_T002 h_T004 h_T013) (dimH E).toReal (dimH (GDProduct E)) hdpos
    intro s hs hsd
    have hsD : ENNReal.ofReal s < dimH E :=
      (@yui_aux_0002 n E h_T002 h_T004 h_T013) s hs.le hsd
    have hsp : 0 < s + 1 := by linarith
    exact (h_T002 (n + 1) (GDProduct E)).2 (s + 1) hsp |>.2.2.2.2.2 (h_T013 s hs hsD)
  have hconvert : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add hdpos.le (by norm_num), ENNReal.ofReal_toReal hfinite.ne]
    simp
  rw [hconvert] at hend
  exact hend

namespace Local_T015
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ x0 : GDVec n, Isometry (fun t : ℝ => GDPoint x0 t)" := by
  intro x0
  apply Isometry.of_dist_eq
  intro t u
  rw [h_T009.1 x0 x0 t u, dist_self]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_sq_eq_abs, abs_abs]
  exact Real.dist_eq t u |>.symm

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (x0 : GDVec n) (U : Set (GDVec (n + 1))), Metric.ediam (GDInterval ∩ (fun t : ℝ => GDPoint x0 t) ⁻¹' U) ≤ Metric.ediam U" := by
  intro x0 U
  have hf : Isometry (fun t : ℝ => GDPoint x0 t) := yui_aux_0001 n E h_H001 h_T009 x0
  rw [← hf.ediam_image (GDInterval ∩ (fun t : ℝ => GDPoint x0 t) ⁻¹' U)]
  apply Metric.ediam_mono
  rintro z ⟨t, ht, rfl⟩
  exact ht.2

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (s : ℝ) (a b : ℝ≥0∞), 0 ≤ s → a ≤ b → a ^ s ≤ b ^ s" := by
  intro s a b hs hab
  exact ENNReal.rpow_le_rpow hab hs

end Local_T015
open Local_T015 in
theorem T015 (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) :
    dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E) := by
  intro hD s δ hs hδ
  obtain ⟨x0, hx0⟩ := h_H001
  have hE : E.Nonempty := ⟨x0, hx0⟩
  unfold GDContent
  refine le_iInf fun U => le_iInf fun hcover => le_iInf fun hscale => ?_
  let V : ℕ → Set ℝ := fun i => GDInterval ∩ (fun t : ℝ => GDPoint x0 t) ⁻¹' U i
  have hVcover : GDInterval ⊆ ⋃ i, V i := by
    intro t ht
    have hpt : GDPoint x0 t ∈ GDProduct E := ⟨x0, hx0, t, ht, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hpt)
    exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩
  have hVdiam : ∀ i, Metric.ediam (V i) ≤ Metric.ediam (U i) := by
    intro i
    exact yui_aux_0002 n E hE h_T009 x0 (U i)
  have hVscale : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ :=
    fun i => (hVdiam i).trans (hscale i)
  refine le_trans (iInf_le_of_le V (iInf_le_of_le hVcover (iInf_le_of_le hVscale le_rfl))) ?_
  apply ENNReal.tsum_le_tsum
  intro i
  unfold GDCost
  refine iSup_le fun hVi => ?_
  have hUi : (U i).Nonempty := by
    obtain ⟨t, ht⟩ := hVi
    exact ⟨GDPoint x0 t, ht.2⟩
  refine le_iSup_of_le hUi ?_
  exact yui_aux_0003 n E hE h_T009 s (Metric.ediam (V i)) (Metric.ediam (U i)) hs.le (hVdiam i)

namespace Local_T016
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T015 : dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E)) : yui_aux_type% "∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < 1 → 0 < (q : ℝ) ∧ (q : ℝ) < 1 ∧ ENNReal.ofReal (q : ℝ) = (q : ℝ≥0∞)" := by
  intro q hq hq1
  constructor
  · exact_mod_cast hq
  constructor
  · exact_mod_cast hq1
  · simp

end Local_T016
open Local_T016 in
theorem T016 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T015 : dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E)) :
    dimH E = 0 →
  (1 : ℝ≥0∞) ≤ dimH (GDProduct E) ∧
  (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hE
  have hdim : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal s ≤ dimH (GDProduct E) := by
    intro s hs hs1
    have hm : GDMeasure s GDInterval ≤ GDMeasure s (GDProduct E) := by
      unfold GDMeasure
      exact iSup_mono fun δ => iSup_mono fun hδ => h_T015 hE s δ hs hδ
    have hi : GDMeasure s GDInterval = ⊤ := h_T007.2.2.2 s hs hs1
    have hp : GDMeasure s (GDProduct E) = ⊤ := by
      rw [hi] at hm
      exact top_unique hm
    exact ((h_T002 (n + 1) (GDProduct E)).2 s hs).2.2.2.2.2 hp
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro q hq hq1
    obtain ⟨hqpos, hqone, hqcoe⟩ := (@yui_aux_0001 n E h_T002 h_T007 h_T015) q hq hq1
    rw [← hqcoe]
    exact hdim (q : ℝ) hqpos hqone
  · simp [hE]

theorem T017 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T010 : dimH (GDProduct E) ≤ dimH E + 1 ∧ dimH (GDProduct E) < ⊤) (h_T014 : 0 < dimH E → dimH E + 1 ≤ dimH (GDProduct E)) (h_T016 : dimH E = 0 →
  (1 : ℝ≥0∞) ≤ dimH (GDProduct E) ∧
  (1 : ℝ≥0∞) = dimH E + 1) :
    dimH (GDProduct E) = dimH E + 1 := by
  apply le_antisymm h_T010.1
  by_cases hD : dimH E = 0
  · have h := h_T016 hD
    calc
      dimH E + 1 = 1 := h.2.symm
      _ ≤ dimH (GDProduct E) := h.1
  · exact h_T014 (lt_of_le_of_ne h_T004.2.1 (Ne.symm hD))

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) :
    dimH (GDProduct E) = dimH E + 1 := by
  have h_T001 : ∀ (m : ℕ) (A : Set (GDVec m)) (s : ℝ), 0 < s → GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A := @T001 n E 
  have h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A) := @T002 n E h_T001
  have h_T003 : Bornology.IsBounded E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0) := @T003 n E h_H001 h_H002 h_T002
  have h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0) := @T004 n E h_H002 h_T003
  have h_T018 : Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A) := @T018 n E 
  have h_T005 : (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  dimH GDInterval ≤ 1 := @T005 n E h_T002 h_T018
  have h_T006 : ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval := @T006 n E 
  have h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤) := @T007 n E h_T002 h_T005 h_T006 h_T018
  have h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε := @T008 n E h_T002 h_T004
  have h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t) := @T009 n E 
  have h_T010 : dimH (GDProduct E) ≤ dimH E + 1 ∧ dimH (GDProduct E) < ⊤ := @T010 n E h_T002 h_T004 h_T007 h_T008 h_T009
  have h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε := @T011 n E h_T004 h_T009
  have h_T012 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ E ≤ GDContent (s + 1) δ (GDProduct E) := @T012 n E h_T011
  have h_T013 : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
  GDMeasure (s + 1) (GDProduct E) = ⊤ := @T013 n E h_T002 h_T012
  have h_T014 : 0 < dimH E → dimH E + 1 ≤ dimH (GDProduct E) := @T014 n E h_T002 h_T004 h_T013
  have h_T015 : dimH E = 0 → ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ GDInterval ≤ GDContent s δ (GDProduct E) := @T015 n E h_H001 h_T009
  have h_T016 : dimH E = 0 →
  (1 : ℝ≥0∞) ≤ dimH (GDProduct E) ∧
  (1 : ℝ≥0∞) = dimH E + 1 := @T016 n E h_T002 h_T007 h_T015
  have h_T017 : dimH (GDProduct E) = dimH E + 1 := @T017 n E h_T004 h_T010 h_T014 h_T016
  exact h_T017

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) : dimH (GDProduct E) = dimH E + 1 := by
  exact @Translation.P n E h_H001 h_H002

#check @P
#print axioms P
end AuditBExport

/- Trusted inspector appended after the generated proof, never a worker tool.
   Its only substitution is an array of escaped (id, selector, expected type) strings. -/
namespace NL2LeanAuditProbe
open Lean Meta Elab Command Term

private def nameOf (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def showType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def binderInventory (type : Expr) : MetaM Json :=
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    for x in xs do
      let d ← getFVarLocalDecl x
      rows := rows.push <| Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← showType d.type)), ("proof_valued", toJson (← isProp d.type))]
    return Json.mkObj [("binders", toJson rows), ("result", toJson (← showType body))]

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
    ("type", toJson (← showType info.type)),
    ("signature", ← binderInventory info.type),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("direct_constants", toJson ((info.getUsedConstantsAsSet.toArray.qsort Name.lt).map Name.toString)),
    ("axioms", toJson ((← collectAxioms name).map Name.toString))]

private def inspect (roots : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    rows := rows.push (← record name)
    if !(← getEnv).isImportedConst name then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
  return Json.mkObj [("declarations", toJson rows), ("truncated", toJson (!pending.isEmpty))]

private def actualType (selector : String) (parts : Array String) : TermElabM Expr := do
  if selector.startsWith "decl:" then
    return (← getConstInfo (nameOf parts)).type
  if selector.startsWith "premise:" then
    let wanted := "h_" ++ (selector.drop 8).toString
    let root ← getConstInfo `AuditBExport.P
    return ← forallTelescope root.type fun xs _ => do
      let mut context : Array Expr := #[]
      for x in xs do
        let binder ← getFVarLocalDecl x
        if binder.userName.toString == wanted then
          return ← mkForallFVars context binder.type
        context := context.push x
      throwError "Missing actual root premise {wanted}"
  throwError "Unsupported selector {selector}"

/- Universe parameter names belong to each declaration's binder scope.
   Rename them bijectively, retaining repetitions and all level expressions.
   This is alpha-equivalence, not a proof of logical equivalence. -/
private def sameSignature (actual expected : Expr) : MetaM (Bool × String) := do
  if ← withoutModifyingState <| isDefEq actual expected then
    return (true, "definitional")
  let actualParams := (collectLevelParams {} actual).params.toList
  let expectedParams := (collectLevelParams {} expected).params.toList
  if actualParams.length != expectedParams.length then
    return (false, "different_universe_binders")
  let levels := (List.range actualParams.length).map fun i =>
    Level.param (Name.mkSimple ("_yuiAuditLevel" ++ toString i))
  let equal ← withoutModifyingState <| isDefEq
    (actual.instantiateLevelParams actualParams levels)
    (expected.instantiateLevelParams expectedParams levels)
  return (equal, "bijective_universe_renaming")

elab "#nl2lean_audit_probe" : command => do
  let result ← liftTermElabM <| withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
    let checks : Array (String × String × String × Array String) := #[("P", "decl:AuditBExport.P", "∀ (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E), dimH (GDProduct E) = dimH E + 1", #["AuditBExport", "P"]), ("__frozen__P", "decl:AuditBExport.P", "∀ (n : ℕ) (E : Set (GDVec n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E), dimH (GDProduct E) = dimH E + 1", #["AuditBExport", "P"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`AuditBExport.P]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      let row := Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if id.startsWith "__frozen__" then
        frozenComparisons := frozenComparisons.push row
      else
        comparisons := comparisons.push row
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons),
      ("frozen_comparisons", toJson frozenComparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

#nl2lean_audit_probe
end NL2LeanAuditProbe
