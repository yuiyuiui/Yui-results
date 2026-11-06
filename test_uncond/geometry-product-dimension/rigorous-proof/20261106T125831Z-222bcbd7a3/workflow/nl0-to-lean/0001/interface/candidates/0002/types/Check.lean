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
abbrev T001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤
abbrev T002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  dimH unitInterval = 1
abbrev T003.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A
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
abbrev T005.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i))
abbrev T006.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ unitInterval)
abbrev T007.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)
abbrev T008.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε))
abbrev T009.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ unitInterval)
abbrev T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ unitInterval)
abbrev T011.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ unitInterval) ≠ ⊤
abbrev T012 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n)
abbrev T013 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S
end YuiPortTypes

open Lean Elab Term
elab "yui_use_term% " text:str : term <= expectedType => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  let located := parsed.rewriteBottomUp fun node => node.setInfo text.raw.getHeadInfo
  Term.elabTerm located expectedType

open Lean Elab Command in
run_cmd do
  let specs : List (Name × List String × String) := [(`YuiPortTypes.T001, [], "T014 <- T001"), (`YuiPortTypes.T002, [], "T009 <- T002"), (`YuiPortTypes.T003, ["u"], "T004 <- T003"), (`YuiPortTypes.T004, ["u"], "T006, T007, T008 <- T004"), (`YuiPortTypes.T005, ["u"], "T006 <- T005"), (`YuiPortTypes.T006, ["u"], "T011 <- T006"), (`YuiPortTypes.T007, ["u"], "T008 <- T007"), (`YuiPortTypes.T008, ["u"], "T010 <- T008"), (`YuiPortTypes.T009, ["u"], "T010 <- T009"), (`YuiPortTypes.T010, ["u"], "T011 <- T010"), (`YuiPortTypes.T011, ["u"], "T014 <- T011"), (`YuiPortTypes.T012, [], "T013 <- T012"), (`YuiPortTypes.T013, [], "T014 <- T013")]
  for (name, declared, label) in specs do
    let info ← getConstInfo name
    let publicLevels := (collectLevelParams {} info.type).params.toList
    let missing := info.levelParams.filter fun l => !publicLevels.contains l && !declared.contains l.toString
    unless missing.isEmpty do
      throwError "{label}: undeclared internal universes {missing}; name them in universe_params and supply input_instances"

namespace Translation
set_option autoImplicit false

def __signature_T001 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)), ((0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤))
private theorem __preflight_T001 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ := False.elim __yui_preflight
section
universe u
def __signature_T003 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)), (∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A))
private theorem __preflight_T003 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := False.elim __yui_preflight
end
section
universe u
def __signature_T004 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧
  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →
    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧
      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)))
-- YUI-USE T004 <- T003 (h_T003, use 1)
noncomputable def __use_T004_h_T003_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) => ((h_T003 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →\n  (∀ δ : ℝ, 0 < δ →\n    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)\n      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧\n  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧\n  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A"))))
-- YUI-END-USE
private theorem __preflight_T004 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) (__yui_preflight : False) :
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
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε) := False.elim __yui_preflight
end
section
universe u
def __signature_T005 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)), (∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i))))
private theorem __preflight_T005 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i)) := False.elim __yui_preflight
end
section
universe u
def __signature_T006 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ unitInterval)))
-- YUI-USE T006 <- T004 (h_T004, use 1)
noncomputable def __use_T006_h_T004_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) => ((h_T004 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →\n  (∀ δ : ℝ, 0 < δ →\n    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)\n      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧\n  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧\n  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧\n  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →\n    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),\n      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧\n      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧\n      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)"))))
-- YUI-END-USE
-- YUI-USE T006 <- T005 (h_T005, use 1)
noncomputable def __use_T006_h_T005_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) => ((h_T005 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →\n  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →\n  ∃ J : ℕ → Set ℝ,\n    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧\n    (∀ i, IsClosed (J i)) ∧\n    (∀ i, volume (J i) ≤ Metric.ediam (V i))"))))
-- YUI-END-USE
private theorem __preflight_T006 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ unitInterval) := False.elim __yui_preflight
end
section
universe u
def __signature_T007 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)))
-- YUI-USE T007 <- T004 (h_T004, use 1)
noncomputable def __use_T007_h_T004_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) => ((h_T004 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →\n  (∀ δ : ℝ, 0 < δ →\n    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)\n      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧\n  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧\n  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧\n  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →\n    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),\n      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧\n      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧\n      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)"))))
-- YUI-END-USE
private theorem __preflight_T007 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε) := False.elim __yui_preflight
end
section
universe u
def __signature_T008 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε))))
-- YUI-USE T008 <- T004 (h_T004, use 1)
noncomputable def __use_T008_h_T004_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) => ((h_T004 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →\n  (∀ δ : ℝ, 0 < δ →\n    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)\n      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧\n  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧\n  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧\n  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →\n    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),\n      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧\n      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧\n      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)"))))
-- YUI-END-USE
-- YUI-USE T008 <- T007 (h_T007, use 1)
noncomputable def __use_T008_h_T007_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) => ((h_T007 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →\n  ∀ δ ε : ℝ, 0 < δ → 0 < ε →\n    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧\n      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧\n      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)"))))
-- YUI-END-USE
private theorem __preflight_T008 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)) := False.elim __yui_preflight
end
def __signature_T002 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)), (dimH unitInterval = 1))
private theorem __preflight_T002 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    dimH unitInterval = 1 := False.elim __yui_preflight
section
universe u
def __signature_T009 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T002 : dimH unitInterval = 1), (∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ unitInterval)))
private theorem __preflight_T009 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T002 : dimH unitInterval = 1) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ unitInterval) := False.elim __yui_preflight
end
section
universe u
def __signature_T010 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ unitInterval)))
-- YUI-USE T010 <- T008 (h_T008, use 1)
noncomputable def __use_T010_h_T008_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) => ((h_T008 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →\n  H (q + 1) (A ×ˢ unitInterval) = 0 ∧\n  (∀ δ ε : ℝ, 0 < δ → 0 < ε →\n    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧\n      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧\n      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε))"))))
-- YUI-END-USE
-- YUI-USE T010 <- T009 (h_T009, use 1)
noncomputable def __use_T010_h_T009_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) => ((h_T009 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ unitInterval)"))))
-- YUI-END-USE
private theorem __preflight_T010 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ unitInterval) := False.elim __yui_preflight
end
section
universe u
def __signature_T011 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ unitInterval) ≠ ⊤))
-- YUI-USE T011 <- T006 (h_T006, use 1)
noncomputable def __use_T011_h_T006_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) => ((h_T006 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →\n  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ unitInterval)) ∧\n  H s A ≤ H (s + 1) (A ×ˢ unitInterval)"))))
-- YUI-END-USE
-- YUI-USE T011 <- T010 (h_T010, use 1)
noncomputable def __use_T011_h_T010_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) => ((h_T010 : (yui_use_term% "∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →\n  dimH (A ×ˢ unitInterval) ≠ ⊤ ∧\n  dimH (A ×ˢ unitInterval) ≤ dimH A + 1 ∧\n  1 ≤ dimH (A ×ˢ unitInterval)"))))
-- YUI-END-USE
private theorem __preflight_T011 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ unitInterval) ≠ ⊤ := False.elim __yui_preflight
end
def __signature_T012 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)), (Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n)))
private theorem __preflight_T012 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) := False.elim __yui_preflight
def __signature_T013 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T012 : Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n)), (Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S))
private theorem __preflight_T013 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T012 : Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n)) (__yui_preflight : False) :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S := False.elim __yui_preflight
def __signature_T014 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S), (dimH (appendCoord n '' (E ×ˢ unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ unitInterval)) ≠ ⊤))
-- YUI-USE T014 <- T011 (h_T011, use 1)
noncomputable def __use_T014_h_T011_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S) => ((h_T011 : (yui_use_term% "∀ (X : Type 0) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →\n  dimH (A ×ˢ unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ unitInterval) ≠ ⊤"))))
-- YUI-END-USE
private theorem __preflight_T014 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S) (__yui_preflight : False) :
    dimH (appendCoord n '' (E ×ˢ unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ unitInterval)) ≠ ⊤ := False.elim __yui_preflight
def __signature_P : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E), (dimH (appendCoord n '' (E ×ˢ unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ unitInterval)) ≠ ⊤))
private theorem __connected_T001 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ := by
  exact @__preflight_T001 n E __yui_preflight

private theorem __connected_T003.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := by
  exact @__preflight_T003 n E __yui_preflight

private theorem __connected_T004.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
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
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε) := by
  exact @__preflight_T004 n E (@__connected_T003.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T005.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i)) := by
  exact @__preflight_T005 n E __yui_preflight

private theorem __connected_T006.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ unitInterval) := by
  exact @__preflight_T006 n E (@__connected_T004.{u} n E __yui_preflight) (@__connected_T005.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T007.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε) := by
  exact @__preflight_T007 n E (@__connected_T004.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T008.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)) := by
  exact @__preflight_T008 n E (@__connected_T004.{u} n E __yui_preflight) (@__connected_T007.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T002 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    dimH unitInterval = 1 := by
  exact @__preflight_T002 n E __yui_preflight

private theorem __connected_T009.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ unitInterval) := by
  exact @__preflight_T009 n E (@__connected_T002 n E __yui_preflight) __yui_preflight

private theorem __connected_T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ unitInterval) := by
  exact @__preflight_T010 n E (@__connected_T008.{u} n E __yui_preflight) (@__connected_T009.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T011.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ unitInterval) ≠ ⊤ := by
  exact @__preflight_T011 n E (@__connected_T006.{u} n E __yui_preflight) (@__connected_T010.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T012 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) := by
  exact @__preflight_T012 n E __yui_preflight

private theorem __connected_T013 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S := by
  exact @__preflight_T013 n E (@__connected_T012 n E __yui_preflight) __yui_preflight

private theorem __connected_T014 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (__yui_preflight : False) :
    dimH (appendCoord n '' (E ×ˢ unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ unitInterval)) ≠ ⊤ := by
  exact @__preflight_T014 n E h_H001 (@__connected_T001 n E __yui_preflight) (@__connected_T011.{0} n E __yui_preflight) (@__connected_T013 n E __yui_preflight) __yui_preflight

private theorem __preflight_P (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (__yui_preflight : False) : dimH (appendCoord n '' (E ×ˢ unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ unitInterval)) ≠ ⊤ := by
  exact @__connected_T014 n E h_H001 __yui_preflight

end Translation
