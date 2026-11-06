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
abbrev T006.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval)
abbrev T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

section
universe u
namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ) (hs : 0 ≤ s), ENNReal.ofReal s < dimH A → H s A = ⊤" := by
  intro X instX A s hs hc
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let d : ℝ≥0 := ⟨s, hs⟩
  have hcoe : (d : ℝ≥0∞) = ENNReal.ofReal s := ENNReal.coe_nnreal_eq d
  have hd : (d : ℝ≥0∞) < dimH A := by rw [hcoe]; exact hc
  have hm := hausdorffMeasure_of_lt_dimH (s := A) hd
  change hausdorffMeasure s A = ⊤
  exact hm

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 ≤ s → H s A = ⊤ → ENNReal.ofReal s ≤ dimH A" := by
  intro X instX A s hs hm
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let d : ℝ≥0 := ⟨s, hs⟩
  have hcoe : (d : ℝ≥0∞) = ENNReal.ofReal s := ENNReal.coe_nnreal_eq d
  have hm' : hausdorffMeasure (d : ℝ) A = ⊤ := hm
  have hd : (d : ℝ≥0∞) ≤ dimH A := le_dimH_of_hausdorffMeasure_eq_top hm'
  rw [hcoe] at hd
  exact hd

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ := by
  intro X instX A hA hfinite
  obtain ⟨hGfinite, hupper, hone⟩ := h_T010 X A hA hfinite
  let D : ℝ := (dimH A).toReal
  let T : ℝ := (dimH (A ×ˢ YuiBasis.unitInterval)).toReal
  have hDnonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hTone : 1 ≤ T := by
    have h := ENNReal.toReal_mono hGfinite hone
    simpa only [ENNReal.toReal_one] using h
  have hupperR : T ≤ D + 1 := by
    have hsum : dimH A + 1 ≠ ⊤ := by simp [hfinite]
    have h := ENNReal.toReal_mono hsum hupper
    simpa only [ENNReal.toReal_add hfinite (by norm_num), ENNReal.toReal_one] using h
  have hbelow : ∀ s : ℝ, 0 < s → s < D → s + 1 ≤ T := by
    intro s hs hsD
    have hc : ENNReal.ofReal s < dimH A :=
      (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfinite).2 hsD
    have hmA : H s A = ⊤ :=
      @yui_aux_0001 n E h_T006 h_T010 X instX A s hs.le hc
    have hmG : H (s + 1) (A ×ˢ YuiBasis.unitInterval) = ⊤ := by
      apply top_unique
      rw [← hmA]
      exact (h_T006 X A s hs).2
    have hd : ENNReal.ofReal (s + 1) ≤ dimH (A ×ˢ YuiBasis.unitInterval) :=
      @yui_aux_0002 n E h_T006 h_T010 (X × ℝ) inferInstance
        (A ×ˢ YuiBasis.unitInterval) (s + 1) (by linarith) hmG
    exact (ENNReal.ofReal_le_iff_le_toReal hGfinite).1 hd
  have hlowerR : D + 1 ≤ T := by
    rcases eq_or_lt_of_le hDnonneg with hzero | hpos
    · linarith
    · by_contra hnot
      have hlt : T < D + 1 := lt_of_not_ge hnot
      let smid : ℝ := (max 0 (T - 1) + D) / 2
      have hmD : max 0 (T - 1) < D := max_lt hpos (by linarith)
      have hms : max 0 (T - 1) < smid := by dsimp [smid]; linarith
      have hsD : smid < D := by dsimp [smid]; linarith
      have hspos : 0 < smid := lt_of_le_of_lt (le_max_left _ _) hms
      have hTs : T < smid + 1 := by
        have hm := le_max_right (0 : ℝ) (T - 1)
        linarith
      have hcontra := hbelow smid hspos hsD
      linarith
  have heqR : T = D + 1 := le_antisymm hupperR hlowerR
  have hconvD : ENNReal.ofReal D = dimH A := ENNReal.ofReal_toReal hfinite
  have hconvT : ENNReal.ofReal T = dimH (A ×ˢ YuiBasis.unitInterval) :=
    ENNReal.ofReal_toReal hGfinite
  constructor
  · calc
      dimH (A ×ˢ YuiBasis.unitInterval) = ENNReal.ofReal T := hconvT.symm
      _ = ENNReal.ofReal (D + 1) := congrArg ENNReal.ofReal heqR
      _ = ENNReal.ofReal D + ENNReal.ofReal 1 := ENNReal.ofReal_add hDnonneg (by norm_num)
      _ = dimH A + 1 := by rw [hconvD]; norm_num
  · exact hGfinite

end
#check @T011
#print axioms T011

end Translation
