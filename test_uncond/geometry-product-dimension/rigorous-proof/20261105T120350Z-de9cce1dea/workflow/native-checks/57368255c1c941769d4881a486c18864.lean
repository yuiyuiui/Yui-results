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

namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T005 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content s (ENNReal.ofReal δ) A ≤
      BasisObjects.content (s + 1) (ENNReal.ofReal δ) (A ×ˢ I)) ∧
  H s A ≤ H (s + 1) (A ×ˢ I)) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) (h_T007 : dimH (F n E) ≤ dimH E + 1 ∧ dimH E < ⊤ ∧ dimH (F n E) < ⊤) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ≥0), ((a : ℝ≥0∞) < dimH A → H (a : ℝ) A = ⊤) ∧ (H (a : ℝ) A = ⊤ → (a : ℝ≥0∞) ≤ dimH A)" := by
  intro X inst A a
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  constructor
  · intro h
    exact hausdorffMeasure_of_lt_dimH h
  · intro h
    exact le_dimH_of_hausdorffMeasure_eq_top h

theorem yui_aux_0002 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T005 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content s (ENNReal.ofReal δ) A ≤
      BasisObjects.content (s + 1) (ENNReal.ofReal δ) (A ×ˢ I)) ∧
  H s A ≤ H (s + 1) (A ×ˢ I)) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) (h_T007 : dimH (F n E) ≤ dimH E + 1 ∧ dimH E < ⊤ ∧ dimH (F n E) < ⊤) : yui_aux_type% "∀ d k : ℝ≥0, ((d : ℝ≥0∞) ≤ (k : ℝ≥0∞) ↔ (d : ℝ) ≤ (k : ℝ)) ∧ ((d : ℝ≥0∞) < (k : ℝ≥0∞) ↔ (d : ℝ) < (k : ℝ)) ∧ (((d + 1 : ℝ≥0) : ℝ≥0∞) = (d : ℝ≥0∞) + 1)" := by
  intro d k
  constructor
  · norm_cast
  constructor
  · norm_cast
  · norm_cast

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T005 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content s (ENNReal.ofReal δ) A ≤
      BasisObjects.content (s + 1) (ENNReal.ofReal δ) (A ×ˢ I)) ∧
  H s A ≤ H (s + 1) (A ×ˢ I)) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) (h_T007 : dimH (F n E) ≤ dimH E + 1 ∧ dimH E < ⊤ ∧ dimH (F n E) < ⊤) :
    dimH (F n E) = dimH E + 1 ∧ dimH E < ⊤ ∧
  dimH (F n E) < ⊤ ∧ dimH E + 1 < ⊤ := by
  have hmeasure := @yui_aux_0001 n E h_T005 h_T006 h_T007
  have hconv := @yui_aux_0002 n E h_T005 h_T006 h_T007
  obtain ⟨d, k, hd, hk, hk1⟩ := h_T006.2.2.2.2.2.2.2.2
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlowerReal : (d : ℝ) + 1 ≤ (k : ℝ) := by
    by_cases hz : (d : ℝ) = 0
    · linarith
    · have hdpos : 0 < (d : ℝ) := lt_of_le_of_ne d.property (Ne.symm hz)
      by_contra! hlt
      let s : ℝ := ((k : ℝ) - 1 + (d : ℝ)) / 2
      have hspos : 0 < s := by dsimp [s]; linarith
      have hsd : s < (d : ℝ) := by dsimp [s]; linarith
      have hks : (k : ℝ) < s + 1 := by dsimp [s]; linarith
      let a : ℝ≥0 := ⟨s, hspos.le⟩
      have ha : (a : ℝ≥0∞) < dimH E := by
        rw [← hd]
        exact (hconv a d).2.1.mpr hsd
      have hE : H s E = ⊤ := (hmeasure (BasisObjects.Rn n) E a).1 ha
      have htrans : H s E ≤ H (s + 1) (F n E) :=
        (h_T005 (BasisObjects.Rn n) E s hspos).2
      have hF : H (s + 1) (F n E) = ⊤ := top_unique (hE ▸ htrans)
      let b : ℝ≥0 := ⟨s + 1, by linarith⟩
      have hb : (b : ℝ≥0∞) ≤ dimH (F n E) :=
        (hmeasure (BasisObjects.Rn n × ℝ) (F n E) b).2 hF
      rw [← hk] at hb
      have hbReal : s + 1 ≤ (k : ℝ) := (hconv b k).1.mp hb
      linarith
  have hlower : dimH E + 1 ≤ dimH (F n E) := by
    rw [← hd, ← hk, ← (hconv d k).2.2]
    apply (hconv (d + 1) k).1.mpr
    simpa only [NNReal.coe_add, NNReal.coe_one] using hlowerReal
  have heq : dimH (F n E) = dimH E + 1 := le_antisymm h_T007.1 hlower
  refine ⟨heq, h_T007.2.1, h_T007.2.2, ?_⟩
  rw [← heq]
  exact h_T007.2.2

#check @T008
#print axioms T008

end Translation
