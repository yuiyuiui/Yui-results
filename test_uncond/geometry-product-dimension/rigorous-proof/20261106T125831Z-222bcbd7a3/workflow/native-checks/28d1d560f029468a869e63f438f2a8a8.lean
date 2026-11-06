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
  dimH YuiBasis.unitInterval = 1
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
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval)
abbrev T007.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)
abbrev T008.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε))
abbrev T009.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)
abbrev T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)
abbrev T011.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤
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
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (s : (yui_use_term% "ℝ")) (hs : (yui_use_term% "0 < s")) => ((((((h_T003 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "s")) (yui_use_term% "hs")) : (yui_use_term% "  (∀ delta : ℝ, 0 < delta →\n    C s delta A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)\n      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal delta), ∑' i, Metric.ediam (U i) ^ s) ∧\n  (∀ delta₁ delta₂ : ℝ, 0 < delta₁ → delta₁ ≤ delta₂ → C s delta₂ A ≤ C s delta₁ A) ∧\n  H s A = ⨆ (delta : ℝ) (_ : 0 < delta), C s delta A"))))
-- YUI-END-USE
-- YUI-USE T004 <- T003 (h_T003, use 2)
noncomputable def __use_T004_h_T003_2 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (s : (yui_use_term% "ℝ")) (hs : (yui_use_term% "0 < s")) (r : (yui_use_term% "ℝ")) (hr : (yui_use_term% "0 < r")) => (((((((((h_T003 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "s")) (yui_use_term% "hs"))).1 (yui_use_term% "r / 2")) (yui_use_term% "half_pos hr")) : (yui_use_term% "C (s) (r / 2) (A) = ⨅ (U : ℕ → Set (X)) (_ : (A) ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (r / 2)), ∑' i, Metric.ediam (U i) ^ (s)"))))
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
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval)))
-- YUI-USE T006 <- T004 (h_T004, use 1)
noncomputable def __use_T006_h_T004_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (s : (yui_use_term% "ℝ")) (hs : (yui_use_term% "0 < s")) (delta : (yui_use_term% "ℝ")) (hdelta : (yui_use_term% "0 < delta")) => (((((((((h_T004 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "s")) (yui_use_term% "hs"))).1 (yui_use_term% "delta")) (yui_use_term% "hdelta")) : (yui_use_term% "C (s) (delta) (A) = ⨅ (U : ℕ → Set (X)) (_ : (A) ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (delta)), ∑' i, Metric.ediam (U i) ^ (s)"))))
-- YUI-END-USE
-- YUI-USE T006 <- T004 (h_T004, use 2)
noncomputable def __use_T006_h_T004_2 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (s : (yui_use_term% "ℝ")) (hs : (yui_use_term% "0 < s")) (delta : (yui_use_term% "ℝ")) (hdelta : (yui_use_term% "0 < delta")) => (((((((((h_T004 (yui_use_term% "X × ℝ")) (yui_use_term% "A ×ˢ YuiBasis.unitInterval")) (yui_use_term% "s + 1")) (yui_use_term% "add_pos hs zero_lt_one"))).1 (yui_use_term% "delta")) (yui_use_term% "hdelta")) : (yui_use_term% "C (s + 1) (delta) (A ×ˢ YuiBasis.unitInterval) = ⨅ (U : ℕ → Set (X × ℝ)) (_ : (A ×ˢ YuiBasis.unitInterval) ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (delta)), ∑' i, Metric.ediam (U i) ^ (s + 1)"))))
-- YUI-END-USE
-- YUI-USE T006 <- T004 (h_T004, use 3)
noncomputable def __use_T006_h_T004_3 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (s : (yui_use_term% "ℝ")) (hs : (yui_use_term% "0 < s")) => (((((((((h_T004 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "s")) (yui_use_term% "hs"))).2).2).1 : (yui_use_term% "H (s) (A) = ⨆ (delta : ℝ) (_ : 0 < delta), C (s) delta (A)"))))
-- YUI-END-USE
-- YUI-USE T006 <- T004 (h_T004, use 4)
noncomputable def __use_T006_h_T004_4 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (s : (yui_use_term% "ℝ")) (hs : (yui_use_term% "0 < s")) => (((((((((h_T004 (yui_use_term% "X × ℝ")) (yui_use_term% "A ×ˢ YuiBasis.unitInterval")) (yui_use_term% "s + 1")) (yui_use_term% "add_pos hs zero_lt_one"))).2).2).1 : (yui_use_term% "H (s + 1) (A ×ˢ YuiBasis.unitInterval) = ⨆ (delta : ℝ) (_ : 0 < delta), C (s + 1) delta (A ×ˢ YuiBasis.unitInterval)"))))
-- YUI-END-USE
-- YUI-USE T006 <- T005 (h_T005, use 1)
noncomputable def __use_T006_h_T005_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (V : (yui_use_term% "ℕ → Set (X × ℝ)")) (delta : (yui_use_term% "ℝ")) (hdelta : (yui_use_term% "0 < delta")) (hV : (yui_use_term% "∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal delta")) => (((((((h_T005 (yui_use_term% "X")) (yui_use_term% "V")) (yui_use_term% "delta")) (yui_use_term% "hdelta")) (yui_use_term% "hV")) : (yui_use_term% "  ∃ J : ℕ → Set ℝ,\n    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧\n    (∀ i, IsClosed (J i)) ∧\n    (∀ i, volume (J i) ≤ Metric.ediam (V i))"))))
-- YUI-END-USE
private theorem __preflight_T006 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval) := False.elim __yui_preflight
end
section
universe u
def __signature_T007 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)))
-- YUI-USE T007 <- T004 (h_T004, use 1)
noncomputable def __use_T007_h_T004_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (q : (yui_use_term% "ℝ")) (hq : (yui_use_term% "0 < q")) (hqzero : (yui_use_term% "H q A = 0")) (delta : (yui_use_term% "ℝ")) (hdelta : (yui_use_term% "0 < delta")) (eps : (yui_use_term% "ℝ")) (heps : (yui_use_term% "0 < eps")) => ((((((((((((((h_T004 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "q")) (yui_use_term% "hq"))).2).2).2 (yui_use_term% "hqzero")) (yui_use_term% "min 1 delta")) (yui_use_term% "eps")) (yui_use_term% "lt_min zero_lt_one hdelta")) (yui_use_term% "heps")) : (yui_use_term% "∃ (U : ℕ → Set X) (a : ℕ → ℝ), ((A) ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ (min 1 delta)) ∧ (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧ (∑' i, ENNReal.ofReal ((a i) ^ (q))) < ENNReal.ofReal (eps)"))))
-- YUI-END-USE
private theorem __preflight_T007 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε) := False.elim __yui_preflight
end
section
universe u
def __signature_T008 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε))))
-- YUI-USE T008 <- T004 (h_T004, use 1)
noncomputable def __use_T008_h_T004_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (q : (yui_use_term% "ℝ")) (hq : (yui_use_term% "0 < q")) (hqzero : (yui_use_term% "H q A = 0")) (delta : (yui_use_term% "ℝ")) (hdelta : (yui_use_term% "0 < delta")) => (((((((((h_T004 (yui_use_term% "X × ℝ")) (yui_use_term% "A ×ˢ YuiBasis.unitInterval")) (yui_use_term% "q + 1")) (yui_use_term% "add_pos hq zero_lt_one"))).1 (yui_use_term% "delta")) (yui_use_term% "hdelta")) : (yui_use_term% "C (q + 1) (delta) (A ×ˢ YuiBasis.unitInterval) = ⨅ (U : ℕ → Set (X × ℝ)) (_ : (A ×ˢ YuiBasis.unitInterval) ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (delta)), ∑' i, Metric.ediam (U i) ^ (q + 1)"))))
-- YUI-END-USE
-- YUI-USE T008 <- T004 (h_T004, use 2)
noncomputable def __use_T008_h_T004_2 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (q : (yui_use_term% "ℝ")) (hq : (yui_use_term% "0 < q")) (hqzero : (yui_use_term% "H q A = 0")) => (((((((((h_T004 (yui_use_term% "X × ℝ")) (yui_use_term% "A ×ˢ YuiBasis.unitInterval")) (yui_use_term% "q + 1")) (yui_use_term% "add_pos hq zero_lt_one"))).2).2).1 : (yui_use_term% "H (q + 1) (A ×ˢ YuiBasis.unitInterval) = ⨆ (delta : ℝ) (_ : 0 < delta), C (q + 1) delta (A ×ˢ YuiBasis.unitInterval)"))))
-- YUI-END-USE
-- YUI-USE T008 <- T007 (h_T007, use 1)
noncomputable def __use_T008_h_T007_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (q : (yui_use_term% "ℝ")) (hq : (yui_use_term% "0 < q")) (hqzero : (yui_use_term% "H q A = 0")) (delta : (yui_use_term% "ℝ")) (hdelta : (yui_use_term% "0 < delta")) (eps : (yui_use_term% "ℝ")) (heps : (yui_use_term% "0 < eps")) => (((((((((((h_T007 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "q")) (yui_use_term% "hq")) (yui_use_term% "hqzero")) (yui_use_term% "delta")) (yui_use_term% "eps")) (yui_use_term% "hdelta")) (yui_use_term% "heps")) : (yui_use_term% "∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧ (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal (delta)) ∧ (∑' i, Metric.ediam (V i) ^ ((q) + 1)) < ENNReal.ofReal (2 * (eps))"))))
-- YUI-END-USE
private theorem __preflight_T008 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)) := False.elim __yui_preflight
end
def __signature_T002 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)), (dimH YuiBasis.unitInterval = 1))
private theorem __preflight_T002 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    dimH YuiBasis.unitInterval = 1 := False.elim __yui_preflight
section
universe u
def __signature_T009 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T002 : dimH YuiBasis.unitInterval = 1), (∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)))
private theorem __preflight_T009 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T002 : dimH YuiBasis.unitInterval = 1) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := False.elim __yui_preflight
end
section
universe u
def __signature_T010 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)))
-- YUI-USE T010 <- T008 (h_T008, use 1)
noncomputable def __use_T010_h_T008_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (q : (yui_use_term% "ℝ")) (hq_gt : (yui_use_term% "(dimH A).toReal < q")) (hqzero : (yui_use_term% "H q A = 0")) => ((((((((h_T008 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "q")) (yui_use_term% "lt_of_le_of_lt ENNReal.toReal_nonneg hq_gt")) (yui_use_term% "hqzero"))).1 : (yui_use_term% "H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0"))))
-- YUI-END-USE
-- YUI-USE T010 <- T009 (h_T009, use 1)
noncomputable def __use_T010_h_T009_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (hA : (yui_use_term% "A.Nonempty")) => (((((h_T009 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "hA")) : (yui_use_term% "1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)"))))
-- YUI-END-USE
private theorem __preflight_T010 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := False.elim __yui_preflight
end
section
universe u
def __signature_T011 : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E), (∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤))
-- YUI-USE T011 <- T006 (h_T006, use 1)
noncomputable def __use_T011_h_T006_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (s : (yui_use_term% "ℝ")) (hs : (yui_use_term% "0 < s")) (hsD : (yui_use_term% "s < (dimH A).toReal")) => (((((((h_T006 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "s")) (yui_use_term% "hs"))).2 : (yui_use_term% "H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval)"))))
-- YUI-END-USE
-- YUI-USE T011 <- T010 (h_T010, use 1)
noncomputable def __use_T011_h_T010_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) (X : (yui_use_term% "Type u")) [instX : (yui_use_term% "MetricSpace X")] (A : (yui_use_term% "Set X")) (hA : (yui_use_term% "A.Nonempty")) (hfinite : (yui_use_term% "dimH A ≠ ⊤")) => ((((((h_T010 (yui_use_term% "X")) (yui_use_term% "A")) (yui_use_term% "hA")) (yui_use_term% "hfinite")) : (yui_use_term% "  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧\n  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧\n  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)"))))
-- YUI-END-USE
private theorem __preflight_T011 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ := False.elim __yui_preflight
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
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : @YuiPortTypes.T013 n E), (dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤))
-- YUI-USE T014 <- T011 (h_T011, use 1)
noncomputable def __use_T014_h_T011_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : @YuiPortTypes.T013 n E) => (((((((h_T011 (yui_use_term% "YuiBasis.Ambient n")) (yui_use_term% "E")) (yui_use_term% "h_H001")) (yui_use_term% "h_T001.2"))).1 : (yui_use_term% "dimH (E ×ˢ YuiBasis.unitInterval) = dimH E + 1"))))
-- YUI-END-USE
-- YUI-USE T014 <- T011 (h_T011, use 2)
noncomputable def __use_T014_h_T011_2 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : @YuiPortTypes.T013 n E) => (((((((h_T011 (yui_use_term% "YuiBasis.Ambient n")) (yui_use_term% "E")) (yui_use_term% "h_H001")) (yui_use_term% "h_T001.2"))).2 : (yui_use_term% "dimH (E ×ˢ YuiBasis.unitInterval) ≠ ⊤"))))
-- YUI-END-USE
-- YUI-USE T014 <- T013 (h_T013, use 1)
noncomputable def __use_T014_h_T013_1 :=
  (fun (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : @YuiPortTypes.T013 n E) => (((((((h_T013).2).2).2).2 (yui_use_term% "E ×ˢ YuiBasis.unitInterval")) : (yui_use_term% "dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH (E ×ˢ YuiBasis.unitInterval)"))))
-- YUI-END-USE
private theorem __preflight_T014 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : @YuiPortTypes.T013 n E) (__yui_preflight : False) :
    dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := False.elim __yui_preflight
def __signature_P : Prop :=
  (∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E), (dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤))
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
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval) := by
  exact @__preflight_T006 n E (@__connected_T004.{u} n E __yui_preflight) (@__connected_T005.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T007.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε) := by
  exact @__preflight_T007 n E (@__connected_T004.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T008.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)) := by
  exact @__preflight_T008 n E (@__connected_T004.{u} n E __yui_preflight) (@__connected_T007.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T002 (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    dimH YuiBasis.unitInterval = 1 := by
  exact @__preflight_T002 n E __yui_preflight

private theorem __connected_T009.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  exact @__preflight_T009 n E (@__connected_T002 n E __yui_preflight) __yui_preflight

private theorem __connected_T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  exact @__preflight_T010 n E (@__connected_T008.{u} n E __yui_preflight) (@__connected_T009.{u} n E __yui_preflight) __yui_preflight

private theorem __connected_T011.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  (__yui_preflight : False) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ := by
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
    dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  exact @__preflight_T014 n E h_H001 (@__connected_T001 n E __yui_preflight) (@__connected_T011.{0} n E __yui_preflight) (@__connected_T013 n E __yui_preflight) __yui_preflight

private theorem __preflight_P (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) (__yui_preflight : False) : dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  exact @__connected_T014 n E h_H001 __yui_preflight

end Translation
