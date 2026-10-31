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
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0" := by
  classical
  intro hn
  subst n
  obtain ⟨x, hx⟩ := h_H002
  have huniq : ∀ y : GP.Space 0, y = x := by
    intro y
    ext i
    exact Fin.elim0 i
  have he : E = {x} := by
    ext y
    simp only [Set.mem_singleton_iff]
    exact ⟨fun _ => huniq y, fun hy => hy ▸ hx⟩
  have hu : E = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    exact (huniq y) ▸ hx
  have hz : ∀ s : ℝ, 0 < s → GP.hausdorff s E = 0 := by
    intro s hs
    let U : ℕ → Set (GP.Space 0) := fun j => if j = 0 then {x} else ∅
    have hc : GP.cost s U = 0 := by
      unfold GP.cost
      apply ENNReal.tsum_eq_zero.mpr
      intro j
      by_cases hj : j = 0 <;> simp [U, hj, ENNReal.zero_rpow_of_pos hs]
    apply bot_unique
    unfold GP.hausdorff
    refine iSup₂_le fun δ hδ => ?_
    have hcover : GP.Cover E δ U := by
      constructor
      · intro y hy
        exact Set.mem_iUnion.mpr ⟨0, by simpa [U, he] using hy⟩
      · intro j
        by_cases hj : j = 0 <;> simp [U, hj]
    exact (iInf₂_le U hcover).trans_eq hc
  have hd : dimH E = 0 := by
    apply bot_unique
    by_contra! h
    obtain ⟨a, ha, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have haR : 0 < (a : ℝ) := by
      change (0 : ℝ≥0∞) < a at ha
      exact_mod_cast ha
    have hb := (h_T001.1 0 E).2 (a : ℝ) haR
    have hb' : dimH E ≤ (a : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using hb.2.2.2.1 (hz a haR)
    exact had.not_ge hb'
  exact ⟨hu, ⟨x, he⟩, hd⟩
#check @checked
#print axioms checked
end YuiAuxiliary
