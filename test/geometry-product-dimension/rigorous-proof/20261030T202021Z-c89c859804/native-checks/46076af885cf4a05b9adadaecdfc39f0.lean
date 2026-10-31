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
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T011 : ∀ (s δ ε : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → 0 < ε → GPcover (GPproduct E) δ V →
  (∀ i, Metric.ediam (GPhead '' V i) ≤ Metric.ediam (V i)) ∧
  ∃ a b : ℕ → ℝ, ∀ i, (V i).Nonempty →
    a i < b i ∧
    (∀ z ∈ V i, z (Fin.last n) ∈ Set.Ioo (a i) (b i)) ∧
    b i - a i ≤ (Metric.ediam (V i)).toReal +
      ε * (2 : ℝ) ^ (-(i : ℝ) - 1) /
        (1 + (Metric.ediam (V i)).toReal ^ s)) : yui_aux_type% "(∑' i : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ) - 1))) = 1" := by
  have hw (i : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ (-(i : ℝ) - 1)) = (2 : ENNReal) ^ (-1 - (i : ℤ)) := by
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [← ENNReal.rpow_intCast]
    congr 1
    push_cast
    ring
  simpa only [hw] using ENNReal.tsum_two_zpow_neg_add_one
#check @checked
#print axioms checked
end YuiAuxiliary
