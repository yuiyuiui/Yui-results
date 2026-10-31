import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T007 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ,
    (∀ i, IsOpen (J i)) ∧
    (∀ i, GP.vertical '' (V i) ⊆ J i) ∧
    (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) +
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + (Metric.diam (V i)) ^ s))) ∧
    (∀ t ∈ GP.unitInterval,
      GP.content s δ E ≤
        ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t)) : yui_aux_type% "∀ (r : ℝ≥0∞) (s b : ℝ), r ≠ ⊤ → 0 ≤ s → 0 ≤ b → ENNReal.ofReal (b / (1 + r.toReal ^ s)) * r ^ s ≤ ENNReal.ofReal b" := by
  intro r s b hr hs hb
  have hd : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  have hp : 0 ≤ r.toReal ^ s := Real.rpow_nonneg hd s
  have hconv : ENNReal.ofReal (r.toReal ^ s) = r ^ s := by
    rw [ENNReal.ofReal_rpow_of_nonneg hd hs, ENNReal.ofReal_toReal hr]
  rw [← hconv, ← ENNReal.ofReal_mul (div_nonneg hb (by positivity))]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by positivity : 0 < 1 + r.toReal ^ s)).2
  nlinarith [mul_nonneg hb hp]
#check @checked
#print axioms checked
end YuiAuxiliary
