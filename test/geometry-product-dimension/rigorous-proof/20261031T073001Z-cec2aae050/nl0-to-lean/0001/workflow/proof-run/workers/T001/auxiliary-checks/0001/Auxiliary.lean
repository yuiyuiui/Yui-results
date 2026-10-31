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
theorem checked (n : ℕ) (E : Set (GP.Space n))  : yui_aux_type% "∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (s : ℝ) (A : Set X), GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A" := by
  intro X _ _ _ s A
  have hc (δ : ℝ) :
      GP.content s δ A =
        ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
          (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), GP.cost s U := by
    simp only [GP.content, GP.Cover, iInf_and]
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  apply le_antisymm
  · unfold GP.hausdorff
    refine iSup₂_le fun δ hδ => ?_
    rw [hc]
    exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl
  · refine iSup₂_le fun r hr => ?_
    have hb (δ : ℝ) (hδ : 0 < δ) (hdr : ENNReal.ofReal δ ≤ r) :
        (⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
          (_ : ∀ i, Metric.ediam (U i) ≤ r), GP.cost s U) ≤ GP.hausdorff s A := by
      apply le_trans ?_ (le_iSup₂_of_le δ hδ (le_refl (GP.content s δ A)))
      rw [hc]
      refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
      exact iInf_le_of_le U (iInf_le_of_le hU
        (iInf_le_of_le (fun i => (hd i).trans hdr) le_rfl))
    by_cases ht : r = ⊤
    · subst r
      exact hb 1 zero_lt_one le_top
    · exact hb r.toReal (ENNReal.toReal_pos_iff.mpr ⟨hr, lt_top_iff_ne_top.mpr ht⟩)
        (ENNReal.ofReal_toReal ht).le
#check @checked
#print axioms checked
end YuiAuxiliary
