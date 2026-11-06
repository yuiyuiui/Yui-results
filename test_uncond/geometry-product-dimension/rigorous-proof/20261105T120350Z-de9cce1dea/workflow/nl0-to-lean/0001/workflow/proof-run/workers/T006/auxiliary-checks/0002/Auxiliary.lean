import Mathlib
open scoped ENNReal NNReal Topology
open Set MeasureTheory
namespace BasisObjects
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def content {X : Type*} [EMetricSpace X]
    (s : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def euclideanLift (n : ℕ) : Rn n × ℝ → WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2
end BasisObjects

namespace IntervalProduct
abbrev Rn := BasisObjects.Rn
def I : Set ℝ := Set.Icc 0 1
def F (n : ℕ) (E : Set (Rn n)) : Set (Rn n × ℝ) := E ×ˢ I
def j (n : ℕ) (p : WithLp 2 (Rn n × ℝ)) : Rn (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => p.fst i) p.snd)
def unj (n : ℕ) (v : Rn (n + 1)) : WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun i : Fin n => v i.castSucc), v (Fin.last n))
def G (n : ℕ) (E : Set (Rn n)) : Set (Rn (n + 1)) :=
  j n '' (BasisObjects.euclideanLift n '' F n E)
noncomputable def H {X : Type*} [MetricSpace X] (a : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  MeasureTheory.Measure.hausdorffMeasure a A
noncomputable def cost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ a
noncomputable def realCost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, (ENNReal.ofReal (Metric.diam (U i))) ^ a
def Cover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def RealCover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ (∀ i, Bornology.IsBounded (U i)) ∧ ∀ i, Metric.diam (U i) ≤ δ
end IntervalProduct
open IntervalProduct

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_H001 : E.Nonempty) : yui_aux_type% "dimH E ≤ (n : ℝ≥0∞) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧ dimH I = 1" := by
  have hD : dimH E ≤ (n : ℝ≥0∞) := by
    calc
      dimH E ≤ dimH (Set.univ : Set (BasisObjects.Rn n)) := dimH_mono (Set.subset_univ E)
      _ = (n : ℝ≥0∞) := by
        rw [Real.dimH_univ_eq_finrank]
        simp [BasisObjects.Rn]
  have hT : dimH (F n E) ≤ (n : ℝ≥0∞) + 1 := by
    calc
      dimH (F n E) ≤ dimH (Set.univ : Set (BasisObjects.Rn n × ℝ)) := dimH_mono (Set.subset_univ _)
      _ = (n : ℝ≥0∞) + 1 := by
        rw [Real.dimH_univ_eq_finrank]
        simp [Module.finrank_prod, BasisObjects.Rn]
  have hI : dimH I = 1 := by
    have hi : (interior I).Nonempty := by
      simpa [IntervalProduct.I, interior_Icc] using (Set.nonempty_Ioo.mpr (zero_lt_one : (0 : ℝ) < 1))
    simpa using (Real.dimH_of_nonempty_interior hi)
  exact ⟨hD, hT, hI⟩

theorem checked (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_H001 : E.Nonempty) : yui_aux_type% "1 ≤ dimH (F n E)" := by
  rcases h_H001 with ⟨x, hx⟩
  have hf : Isometry (fun t : ℝ => (x, t)) := by
    apply isometry_iff_dist_eq.mpr
    intro t u
    simp [Prod.dist_eq]
  have hsub : (fun t : ℝ => (x, t)) '' I ⊆ F n E := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨hx, ht⟩
  have hI : dimH I = 1 := (@yui_aux_0001 n E ⟨x, hx⟩).2.2
  calc
    1 = dimH ((fun t : ℝ => (x, t)) '' I) := by rw [hf.dimH_image I, hI]
    _ ≤ dimH (F n E) := dimH_mono hsub
#check @checked
#print axioms checked
end YuiAuxiliary
