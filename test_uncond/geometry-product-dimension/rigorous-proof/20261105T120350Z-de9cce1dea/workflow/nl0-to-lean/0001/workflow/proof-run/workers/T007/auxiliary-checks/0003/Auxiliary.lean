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
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T003 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ I) = 0 ∧
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ U : ℕ → Set (X × ℝ), Cover δ (A ×ˢ I) U ∧ cost (q + 1) U < ENNReal.ofReal ε) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) : yui_aux_type% "∀ (q : ℝ≥0), dimH E < (q : ℝ≥0∞) → H (q : ℝ) E = 0" := by
  intro q hq
  letI : MeasurableSpace (BasisObjects.Rn n) := borel (BasisObjects.Rn n)
  letI : BorelSpace (BasisObjects.Rn n) := ⟨rfl⟩
  exact hausdorffMeasure_of_dimH_lt hq

theorem yui_aux_0002 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T003 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ I) = 0 ∧
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ U : ℕ → Set (X × ℝ), Cover δ (A ×ˢ I) U ∧ cost (q + 1) U < ENNReal.ofReal ε) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) : yui_aux_type% "∀ (q : ℝ≥0), H (q : ℝ) (F n E) = 0 → dimH (F n E) ≤ (q : ℝ≥0∞)" := by
  intro q hq
  letI : MeasurableSpace (BasisObjects.Rn n × ℝ) := borel (BasisObjects.Rn n × ℝ)
  letI : BorelSpace (BasisObjects.Rn n × ℝ) := ⟨rfl⟩
  apply dimH_le_of_hausdorffMeasure_ne_top (d := q)
  change H (q : ℝ) (F n E) ≠ ⊤
  rw [hq]
  exact ENNReal.zero_ne_top

theorem checked (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T003 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ I) = 0 ∧
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ U : ℕ → Set (X × ℝ), Cover δ (A ×ˢ I) U ∧ cost (q + 1) U < ENNReal.ofReal ε) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) : yui_aux_type% "∀ (d k : ℝ≥0), (d : ℝ≥0∞) = dimH E → (k : ℝ≥0∞) = dimH (F n E) → ∀ q : ℝ, (d : ℝ) < q → (k : ℝ) ≤ q + 1" := by
  intro d k hd hk q hdq
  have hq0 : 0 < q := lt_of_le_of_lt d.coe_nonneg hdq
  let qNN : ℝ≥0 := ⟨q, hq0.le⟩
  have hdqNN : d < qNN := hdq
  have hdim : dimH E < (qNN : ℝ≥0∞) := by
    rw [← hd]
    exact ENNReal.coe_lt_coe.mpr hdqNN
  have hz : H q E = 0 := @yui_aux_0001 n E h_T003 h_T006 qNN hdim
  have hzprod : H (q + 1) (F n E) = 0 :=
    (h_T003 (BasisObjects.Rn n) E q hq0 hz).1
  let rNN : ℝ≥0 := ⟨q + 1, by linarith⟩
  have hbound : dimH (F n E) ≤ (rNN : ℝ≥0∞) :=
    @yui_aux_0002 n E h_T003 h_T006 rNN hzprod
  have hkr : k ≤ rNN := ENNReal.coe_le_coe.mp (hk.symm ▸ hbound)
  have hreal : (k : ℝ) ≤ (rNN : ℝ) := by exact_mod_cast hkr
  exact hreal
#check @checked
#print axioms checked
end YuiAuxiliary
