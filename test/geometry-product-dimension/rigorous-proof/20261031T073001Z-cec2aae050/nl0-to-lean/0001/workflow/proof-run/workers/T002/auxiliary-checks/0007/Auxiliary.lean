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
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ (b : ℝ), 0 < b → (∀ x ∈ E, ∀ i : Fin n, -b < x i ∧ x i < b) → ∀ k : ℕ, 0 < k → ∃ V : (Fin n → Fin k) → Set (GP.Space n), E ⊆ ⋃ f, V f ∧ ∀ f, Metric.ediam (V f) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ) * (2 * b / k))" := by
  classical
  intro b hb hbox k hk
  let h : ℝ := 2 * b / k
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hh : 0 < h := div_pos (by linarith) hkR
  let Q : (Fin n → Fin k) → Set (Fin n → ℝ) := fun f =>
    Set.pi Set.univ fun i => Set.Icc (-b + (f i : ℝ) * h) (-b + ((f i : ℝ) + 1) * h)
  let V : (Fin n → Fin k) → Set (GP.Space n) := fun f => WithLp.toLp 2 '' Q f
  have hcov : E ⊆ ⋃ f, V f := by
    intro x hx
    have hpos : ∀ i, 0 ≤ (x i + b) / h := fun i => div_nonneg (by linarith [(hbox x hx i).1]) hh.le
    have hlt : ∀ i, (x i + b) / h < k := by
      intro i
      apply (div_lt_iff₀ hh).mpr
      have he : (k : ℝ) * h = 2 * b := by dsimp [h]; field_simp; ring
      rw [he]
      linarith [(hbox x hx i).2]
    let f : Fin n → Fin k := fun i => ⟨⌊(x i + b) / h⌋₊, (Nat.floor_lt (hpos i)).mpr (hlt i)⟩
    apply Set.mem_iUnion.mpr
    refine ⟨f, ?_⟩
    refine ⟨WithLp.ofLp x, ?_, by simp⟩
    rw [Set.mem_univ_pi]
    intro i
    have hl : (f i : ℝ) * h ≤ x i + b :=
      (le_div_iff₀ hh).mp (Nat.floor_le (hpos i))
    have hu : x i + b < ((f i : ℝ) + 1) * h :=
      (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((x i + b) / h))
    exact ⟨by dsimp; linarith, by dsimp; linarith⟩
  have hLip : LipschitzWith ⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩
      (WithLp.toLp 2 : (Fin n → ℝ) → GP.Space n) := by
    have hL := PiLp.lipschitzWith_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n => ℝ)
    have heq : ((Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) =
        (⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩ : ℝ≥0) := by
      apply NNReal.eq
      simp only [NNReal.coe_rpow, NNReal.coe_natCast, Fintype.card_fin]
      norm_num
      exact (Real.sqrt_eq_rpow _).symm
    rwa [heq] at hL
  refine ⟨V, hcov, fun f => ?_⟩
  have hQ : Metric.ediam (Q f) ≤ ENNReal.ofReal h := by
    apply Metric.ediam_pi_le_of_le
    intro i
    rw [Real.ediam_Icc]
    apply ENNReal.ofReal_le_ofReal
    ring_nf
    exact le_rfl
  calc
    Metric.ediam (V f) ≤ (⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩ : ℝ≥0) * Metric.ediam (Q f) := hLip.ediam_image_le (Q f)
    _ ≤ (⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩ : ℝ≥0) * ENNReal.ofReal h := mul_le_mul_left' hQ _
    _ = ENNReal.ofReal (Real.sqrt (n : ℝ) * (2 * b / k)) := by
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      rfl
#check @checked
#print axioms checked
end YuiAuxiliary
