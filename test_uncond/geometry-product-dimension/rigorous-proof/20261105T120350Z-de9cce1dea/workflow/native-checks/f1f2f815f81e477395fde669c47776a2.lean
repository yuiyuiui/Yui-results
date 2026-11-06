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

namespace Translation
set_option autoImplicit false

theorem T010 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T008 : dimH (F n E) = dimH E + 1 ∧ dimH E < ⊤ ∧
  dimH (F n E) < ⊤ ∧ dimH E + 1 < ⊤) (h_T009 : Isometry (j n) ∧ Function.Bijective (j n) ∧
  Function.LeftInverse (unj n) (j n) ∧ Function.RightInverse (unj n) (j n) ∧
  j n '' (BasisObjects.euclideanLift n '' F n E) = G n E ∧
  ∀ (x y : Rn n) (t u : ℝ),
    (dist (j n (BasisObjects.euclideanLift n (x,t)))
      (j n (BasisObjects.euclideanLift n (y,u)))) ^ 2 =
      (∑ h : Fin n, |x h - y h| ^ 2) + |t - u| ^ 2 ∧
    (dist (BasisObjects.euclideanLift n (x,t))
      (BasisObjects.euclideanLift n (y,u))) ^ 2 =
      (∑ h : Fin n, |x h - y h| ^ 2) + |t - u| ^ 2) (h_E001 : ∀ (n : ℕ) (S : Set (BasisObjects.Rn n × ℝ)),
  dimH (BasisObjects.euclideanLift n '' S) = dimH S) :
    dimH (G n E) = dimH E + 1 ∧ dimH E < ⊤ ∧ dimH (G n E) < ⊤ := by
  have hLift : dimH (BasisObjects.euclideanLift n '' F n E) = dimH (F n E) :=
    h_E001 n (F n E)
  have hImage : j n '' (BasisObjects.euclideanLift n '' F n E) = G n E :=
    h_T009.2.2.2.2.1
  have hG : dimH (G n E) = dimH (F n E) := calc
    dimH (G n E) = dimH (j n '' (BasisObjects.euclideanLift n '' F n E)) :=
      congrArg dimH hImage.symm
    _ = dimH (BasisObjects.euclideanLift n '' F n E) :=
      h_T009.1.dimH_image (BasisObjects.euclideanLift n '' F n E)
    _ = dimH (F n E) := hLift
  refine ⟨hG.trans h_T008.1, h_T008.2.1, ?_⟩
  rw [hG]
  exact h_T008.2.2.1

#check @T010
#print axioms T010

end Translation
