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
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ {ι : Type} [Fintype ι] (s δ : ℝ) (V : ι → Set (GP.Space n)), (E ⊆ ⋃ i, V i) → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → GP.content s δ E ≤ ∑ i, ⨆ (_ : (V i).Nonempty), (Metric.ediam (V i)) ^ s" := by
  classical
  intro ι _ s δ V hV hd
  letI : Encodable ι := Encodable.ofCountable ι
  let U : ℕ → Set (GP.Space n) := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
  have hc : GP.Cover E δ U := by
    constructor
    · simpa only [U, Encodable.iUnion_decode₂] using hV
    · intro j
      dsimp [U]
      rw [Metric.ediam_iUnion_mem_option]
      exact iSup₂_le fun b hb => hd b
  unfold GP.content
  refine (iInf_le_of_le U (iInf_le_of_le hc le_rfl)).trans ?_
  change (∑' j, ⨆ (_ : (U j).Nonempty), Metric.ediam (U j) ^ s) ≤ _
  rw [show (∑' j, ⨆ (_ : (U j).Nonempty), Metric.ediam (U j) ^ s) = ∑' i, ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s from tsum_iUnion_decode₂ (fun A : Set (GP.Space n) => ⨆ (_ : A.Nonempty), Metric.ediam A ^ s) (by simp) V]
  rw [tsum_fintype]
#check @checked
#print axioms checked
end YuiAuxiliary
