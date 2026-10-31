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
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T008 : 1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ U : ℕ → Set (GPEucl n),
    GPcover E r U ∧
    (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧
    GPcost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (A : Set (GPEucl n)) (d : ℝ), 0 ≤ d →\n  Metric.ediam A ≤ ENNReal.ofReal d →\n  ∀ (N : ℕ), 0 < N → 1 / (N : ℝ) ≤ d → ∀ j : ℕ,\n  Metric.ediam {z : GPEucl (n + 1) | GPhead z ∈ A ∧\n    (j : ℝ) / N ≤ z (Fin.last n) ∧ z (Fin.last n) ≤ ((j : ℝ) + 1) / N}\n    ≤ ENNReal.ofReal (Real.sqrt 2 * d)" := by
  intro A d hd hA N hN hNd j
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply Metric.ediam_le_of_forall_dist_le
  intro z hz w hw
  have hhor : dist (GPhead z) (GPhead w) ≤ d :=
    (edist_le_ofReal hd).1 (Metric.edist_le_of_ediam_le hz.1 hw.1 hA)
  have hvert : |z (Fin.last n) - w (Fin.last n)| ≤ d := by
    apply le_trans _ hNd
    rw [abs_le]
    change _ ∧ _ ∧ _ at hz hw
    rw [add_div] at hz hw
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  have hdist : dist z w = Real.sqrt
    (dist (GPhead z) (GPhead w) ^ 2 + |z (Fin.last n) - w (Fin.last n)| ^ 2) := by
    calc
      dist z w = dist (GPappend (GPhead z) (z (Fin.last n)))
        (GPappend (GPhead w) (w (Fin.last n))) := by
          rw [h_T001.2.1 n z, h_T001.2.1 n w]
      _ = _ := h_T001.2.2.1 _ _ _ _ _
  rw [hdist]
  have hh2 : dist (GPhead z) (GPhead w) ^ 2 ≤ d ^ 2 :=
    pow_le_pow_left₀ (dist_nonneg) hhor 2
  have hv2 : |z (Fin.last n) - w (Fin.last n)| ^ 2 ≤ d ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hvert 2
  have hs : 0 ≤ Real.sqrt 2 * d := mul_nonneg (Real.sqrt_nonneg _) hd
  apply (Real.sqrt_le_iff).2
  refine ⟨hs, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  linarith
#check @checked
#print axioms checked
end YuiAuxiliary
