import Mathlib
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
namespace YuiBasis
noncomputable def Content {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ δ),
    ∑' i, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ s
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
noncomputable def appendCoord (n : ℕ) (p : Ambient n × ℝ) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
end YuiBasis

open YuiBasis
namespace YuiPlan
noncomputable def H {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  hausdorffMeasure s A
noncomputable def C {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  YuiBasis.Content s (ENNReal.ofReal δ) A
end YuiPlan
open YuiPlan
namespace YuiPortTypes
abbrev T008.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε))
abbrev T009.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

section
universe u
namespace Local_T010
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), dimH A ≠ ⊤ → (dimH A).toReal < q → dimH (A ×ˢ YuiBasis.unitInterval) ≤ ENNReal.ofReal (q + 1)" := by
  intro X instX A q hfin hq
  have hqpos : 0 < q := lt_of_le_of_lt ENNReal.toReal_nonneg hq
  let d : ℝ≥0 := ⟨q, hqpos.le⟩
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal q := (ENNReal.ofReal_eq_coe_nnreal hqpos.le).symm
  have hlt : dimH A < (d : ℝ≥0∞) := by
    rw [hd, ← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hqpos).2 hq
  have hz : H q A = 0 := by
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    exact hausdorffMeasure_of_dimH_lt (s := A) (d := d) hlt
  have hgz : H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 := (h_T008 X A q hqpos hz).1
  have hq1 : 0 ≤ q + 1 := by linarith
  let e : ℝ≥0 := ⟨q + 1, hq1⟩
  have he : (e : ℝ≥0∞) = ENNReal.ofReal (q + 1) := (ENNReal.ofReal_eq_coe_nnreal hq1).symm
  rw [← he]
  letI : MeasurableSpace (X × ℝ) := borel (X × ℝ)
  letI : BorelSpace (X × ℝ) := ⟨rfl⟩
  apply dimH_le_of_hausdorffMeasure_ne_top (s := A ×ˢ YuiBasis.unitInterval) (d := e)
  change H (q + 1) (A ×ˢ YuiBasis.unitInterval) ≠ ⊤
  rw [hgz]
  exact ENNReal.zero_ne_top

end Local_T010
open Local_T010 in
theorem T010 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  intro X instX A hA hAfin
  let D : ℝ := (dimH A).toReal
  let G : Set (X × ℝ) := A ×ˢ YuiBasis.unitInterval
  have hDnonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hD : ENNReal.ofReal D = dimH A := ENNReal.ofReal_toReal hAfin
  have hb : ∀ q : ℝ, D < q → dimH G ≤ ENNReal.ofReal (q + 1) := by
    intro q hq
    exact yui_aux_0001 n E h_T008 h_T009 X A q hAfin hq
  have hq0 : D < D + 1 := by linarith
  have hGfin : dimH G ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (hb (D + 1) hq0) ENNReal.ofReal_lt_top)
  let T : ℝ := (dimH G).toReal
  have hTnonneg : 0 ≤ T := ENNReal.toReal_nonneg
  have hT : ENNReal.ofReal T = dimH G := ENNReal.ofReal_toReal hGfin
  have hsharp : T ≤ D + 1 := by
    by_contra hn
    have hgt : D + 1 < T := lt_of_not_ge hn
    let qmid : ℝ := D + (T - D - 1) / 2
    have hmid : D < qmid := by dsimp [qmid]; linarith
    have hmidpos : 0 ≤ qmid + 1 := by linarith
    have hmidlt : qmid + 1 < T := by dsimp [qmid]; linarith
    have hbound : dimH G ≤ ENNReal.ofReal (qmid + 1) := hb qmid hmid
    have hreal : T ≤ qmid + 1 := by
      have hc := (ENNReal.toReal_le_toReal hGfin ENNReal.ofReal_ne_top).2 hbound
      simpa only [ENNReal.toReal_ofReal hmidpos] using hc
    linarith
  have hupper : dimH G ≤ dimH A + 1 := by
    rw [← hT, ← hD, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hDnonneg (by norm_num : (0 : ℝ) ≤ 1)]
    exact ENNReal.ofReal_le_ofReal hsharp
  exact ⟨hGfin, hupper, h_T009 X A hA⟩

end
#check @T010
#print axioms T010

end Translation
