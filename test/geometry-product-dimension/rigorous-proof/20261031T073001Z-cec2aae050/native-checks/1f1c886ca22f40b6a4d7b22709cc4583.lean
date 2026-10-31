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
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ (hv : LipschitzWith 1 (@GP.vertical n)) (V : Set (GP.Space (n+1))), Bornology.IsBounded V → ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ GP.vertical '' V ⊆ J ∧ MeasureTheory.volume J ≤ Metric.ediam V + ENNReal.ofReal η" := by
  intro hv
  classical
  intro V hV η hη
  let B : Set ℝ := GP.vertical '' V
  have hB : Bornology.IsBounded B := hv.isBounded_image hV
  have hd : Metric.diam B ≤ Metric.diam V := by
    simpa only [NNReal.coe_one, one_mul] using hv.diam_image_le V hV
  have hconv : ENNReal.ofReal (Metric.diam V) = Metric.ediam V :=
    ENNReal.ofReal_toReal hV.ediam_ne_top
  by_cases hne : V.Nonempty
  · refine ⟨Set.Ioo (sInf B - η / 2) (sSup B + η / 2), isOpen_Ioo, ?_, ?_⟩
    · intro t ht
      have ht' := hB.subset_Icc_sInf_sSup ht
      constructor <;> linarith [ht'.1, ht'.2]
    · rw [Real.volume_Ioo]
      have hh : sSup B + η / 2 - (sInf B - η / 2) = Metric.diam B + η := by
        rw [Real.diam_eq hB]
        ring
      rw [hh]
      calc
        ENNReal.ofReal (Metric.diam B + η) ≤ ENNReal.ofReal (Metric.diam V + η) :=
          ENNReal.ofReal_le_ofReal (by linarith)
        _ = Metric.ediam V + ENNReal.ofReal η := by
          rw [ENNReal.ofReal_add Metric.diam_nonneg hη.le, hconv]
  · have hem : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, isOpen_empty, ?_, ?_⟩ <;> simp [hem]
#check @checked
#print axioms checked
end YuiAuxiliary
