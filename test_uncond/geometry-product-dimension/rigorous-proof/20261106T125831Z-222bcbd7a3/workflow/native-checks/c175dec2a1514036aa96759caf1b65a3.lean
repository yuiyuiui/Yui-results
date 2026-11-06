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
abbrev T004.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧
  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →
    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧
      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)
abbrev T007.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

section
universe u
namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) : yui_aux_type% "∀ z : ℝ≥0∞, (∀ ε : ℝ, 0 < ε → z ≤ ENNReal.ofReal (2 * ε)) → z = 0" := by
  intro z hz
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεreal : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hhalf : 0 < (ε : ℝ) / 2 := by positivity
  have hconvert : ENNReal.ofReal (2 * ((ε : ℝ) / 2)) = (ε : ℝ≥0∞) := by
    rw [show 2 * ((ε : ℝ) / 2) = (ε : ℝ) by ring]
    exact ENNReal.ofReal_coe_nnreal
  simpa only [zero_add, hconvert] using hz ((ε : ℝ) / 2) hhalf

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s δ : ℝ) (V : ℕ → Set X), A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → (⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ≤ ∑' i, Metric.ediam (V i) ^ s" := by
  intro X instX A s δ V hcov hdiam
  apply iInf_le_of_le V
  apply iInf_le_of_le hcov
  apply iInf_le_of_le hdiam
  exact le_rfl

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)) := by
  intro X instX A q hq hqzero
  have hcover := h_T007 X A q hq hqzero
  have hcontent := h_T004 (X × ℝ) (A ×ˢ YuiBasis.unitInterval) (q + 1) (add_pos hq zero_lt_one)
  have hzero : ∀ δ : ℝ, 0 < δ → C (q + 1) δ (A ×ˢ YuiBasis.unitInterval) = 0 := by
    intro δ hδ
    apply (@yui_aux_0001 n E h_T004 h_T007)
    intro ε hε
    obtain ⟨V, hVcover, hVdiam, hVcost⟩ := hcover δ ε hδ hε
    rw [hcontent.1 δ hδ]
    exact (@yui_aux_0002 n E h_T004 h_T007 (X × ℝ) inferInstance
      (A ×ˢ YuiBasis.unitInterval) (q + 1) δ V hVcover hVdiam).trans hVcost.le
  constructor
  · rw [hcontent.2.2.1]
    apply le_antisymm _ zero_le
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    rw [hzero δ hδ]
  · exact hcover

end
#check @T008
#print axioms T008

end Translation
