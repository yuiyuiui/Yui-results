import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T006 : ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η)) : yui_aux_type% "∀ ε : NNReal, (∑' i : ℕ, ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i)) = (ε : ENNReal)" := by
  intro ε
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' (ε : ℝ)), tsum_geometric_two']
  simp
#check @checked
#print axioms checked
end YuiAuxiliary
