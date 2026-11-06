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

theorem yui_aux_0003 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T003 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ I) = 0 ∧
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ U : ℕ → Set (X × ℝ), Cover δ (A ×ˢ I) U ∧ cost (q + 1) U < ENNReal.ofReal ε) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) : yui_aux_type% "∀ (X Y : Type*) [MetricSpace X] [MetricSpace Y] (f : X → Y), Isometry f → ∀ (q : ℝ), 0 ≤ q → ∀ A : Set X, H q (f '' A) = H q A" := by
  intro X Y _ _ f hf q hq A
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  exact hf.hausdorffMeasure_image (Or.inl hq) A

theorem yui_aux_0004 (n : ℕ) (E : Set (BasisObjects.Rn n)) (h_T003 : ∀ (X : Type*) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ I) = 0 ∧
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ U : ℕ → Set (X × ℝ), Cover δ (A ×ˢ I) U ∧ cost (q + 1) U < ENNReal.ofReal ε) (h_T006 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ⊤ ∧
  1 ≤ dimH (F n E) ∧ dimH (F n E) ≤ (n : ℝ≥0∞) + 1 ∧
  dimH E < ⊤ ∧ dimH (F n E) < ⊤ ∧ dimH I = 1 ∧
  ∃ d k : ℝ≥0, (d : ℝ≥0∞) = dimH E ∧ (k : ℝ≥0∞) = dimH (F n E) ∧ 1 ≤ k) : yui_aux_type% "∀ q : ℝ, 0 < q → H q E = 0 → H (q + 1) (F n E) = 0" := by
  intro q hq hz
  let X := ULift.{_} (BasisObjects.Rn n)
  let up : BasisObjects.Rn n → X := ULift.up
  let downProd : X × ℝ → BasisObjects.Rn n × ℝ := fun p => (p.1.down, p.2)
  have hiup : Isometry up := fun _ _ => rfl
  have hidown : Isometry downProd := fun _ _ => rfl
  have hueq : H q (up '' E) = H q E :=
    @yui_aux_0003 n E h_T003 h_T006 _ _ _ _ up hiup q hq.le E
  have hzu : H q (up '' E) = 0 := hueq.trans hz
  have huProd : H (q + 1) ((up '' E) ×ˢ I) = 0 :=
    (h_T003 X (up '' E) q hq hzu).1
  have hdeq : H (q + 1) (downProd '' ((up '' E) ×ˢ I)) = H (q + 1) ((up '' E) ×ˢ I) :=
    @yui_aux_0003 n E h_T003 h_T006 _ _ _ _ downProd hidown (q + 1) (by linarith) _
  have himage : downProd '' ((up '' E) ×ˢ I) = F n E := by
    ext p
    constructor
    · rintro ⟨⟨x, t⟩, ⟨⟨a, ha, rfl⟩, ht⟩, rfl⟩
      exact ⟨ha, ht⟩
    · intro hp
      exact ⟨(up p.1, p.2), ⟨⟨p.1, hp.1, rfl⟩, hp.2⟩, rfl⟩
  rw [himage] at hdeq
  exact hdeq.trans huProd

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
    @yui_aux_0004 n E h_T003 h_T006 q hq0 hz
  let rNN : ℝ≥0 := ⟨q + 1, by linarith⟩
  have hbound : dimH (F n E) ≤ (rNN : ℝ≥0∞) :=
    @yui_aux_0002 n E h_T003 h_T006 rNN hzprod
  have hkr : k ≤ rNN := ENNReal.coe_le_coe.mp (hk.symm ▸ hbound)
  have hreal : (k : ℝ) ≤ (rNN : ℝ) := by exact_mod_cast hkr
  exact hreal
#check @checked
#print axioms checked
end YuiAuxiliary
