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

namespace Translation
set_option autoImplicit false

namespace Local_T009
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ p q : WithLp 2 (Rn n × ℝ), (dist p q) ^ 2 = (∑ h : Fin n, |p.fst h - q.fst h| ^ 2) + |p.snd - q.snd| ^ 2" := by
  intro p q
  rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.sub_fst, WithLp.sub_snd, PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, Real.norm_eq_abs]

theorem yui_aux_0002 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ p q : WithLp 2 (Rn n × ℝ), (dist (j n p) (j n q)) ^ 2 = (∑ h : Fin n, |p.fst h - q.fst h| ^ 2) + |p.snd - q.snd| ^ 2" := by
  intro p q
  rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_castSucc]
  simp [j, Real.dist_eq]

theorem yui_aux_0003 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ p : WithLp 2 (Rn n × ℝ), unj n (j n p) = p" := by
  intro p
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change Fin.snoc (α := fun _ : Fin (n+1) => ℝ) (fun h : Fin n => p.fst h) p.snd i.castSucc = p.fst i
    exact Fin.snoc_castSucc _ _ _
  · change Fin.snoc (α := fun _ : Fin (n+1) => ℝ) (fun h : Fin n => p.fst h) p.snd (Fin.last n) = p.snd
    exact Fin.snoc_last _ _

end Local_T009
open Local_T009 in
theorem T009 (n : ℕ) (E : Set (BasisObjects.Rn n))  :
    Isometry (j n) ∧ Function.Bijective (j n) ∧
  Function.LeftInverse (unj n) (j n) ∧ Function.RightInverse (unj n) (j n) ∧
  j n '' (BasisObjects.euclideanLift n '' F n E) = G n E ∧
  ∀ (x y : Rn n) (t u : ℝ),
    (dist (j n (BasisObjects.euclideanLift n (x,t)))
      (j n (BasisObjects.euclideanLift n (y,u)))) ^ 2 =
      (∑ h : Fin n, |x h - y h| ^ 2) + |t - u| ^ 2 ∧
    (dist (BasisObjects.euclideanLift n (x,t))
      (BasisObjects.euclideanLift n (y,u))) ^ 2 =
      (∑ h : Fin n, |x h - y h| ^ 2) + |t - u| ^ 2 := by
  have hleft : Function.LeftInverse (unj n) (j n) := @yui_aux_0003 n E
  have hright : Function.RightInverse (unj n) (j n) := by
    intro v
    apply PiLp.ext
    intro i
    change Fin.snoc (α := fun _ : Fin (n+1) => ℝ) (fun h : Fin n => v h.castSucc) (v (Fin.last n)) i = v i
    exact congrFun (Fin.snoc_init_self v.ofLp) i
  have hisom : Isometry (j n) := by
    apply Isometry.of_dist_eq
    intro p q
    have hsq : dist (j n p) (j n q) ^ 2 = dist p q ^ 2 :=
      (@yui_aux_0002 n E p q).trans (@yui_aux_0001 n E p q).symm
    nlinarith [dist_nonneg (j n p) (j n q), dist_nonneg p q]
  refine ⟨hisom, ⟨hleft.injective, ?_⟩, hleft, hright, rfl, ?_⟩
  · intro v
    exact ⟨unj n v, hright v⟩
  · intro x y t u
    constructor
    · exact @yui_aux_0002 n E (BasisObjects.euclideanLift n (x,t)) (BasisObjects.euclideanLift n (y,u))
    · exact @yui_aux_0001 n E (BasisObjects.euclideanLift n (x,t)) (BasisObjects.euclideanLift n (y,u))

#check @T009
#print axioms T009

end Translation
