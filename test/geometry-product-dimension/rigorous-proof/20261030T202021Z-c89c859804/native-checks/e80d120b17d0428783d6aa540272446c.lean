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
    GPcost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (q d : ℝ) (N : ℕ), 0 < d → (N : ℝ) * d ≤ 2 →\n  (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * d)) ^ (q + 1) ≤\n    ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * (ENNReal.ofReal d) ^ q" := by
  intro q d N hd hNd
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hreal : (N : ℝ) * (Real.sqrt 2 * d) ^ (q + 1) ≤
      (2 * (Real.sqrt 2) ^ (q + 1)) * d ^ q := by
    rw [Real.mul_rpow hs.le hd.le, Real.rpow_add hd, Real.rpow_one]
    calc
      (N : ℝ) * (Real.sqrt 2 ^ (q + 1) * (d ^ q * d)) =
        ((N : ℝ) * d) * (Real.sqrt 2 ^ (q + 1) * d ^ q) := by ring
      _ ≤ 2 * (Real.sqrt 2 ^ (q + 1) * d ^ q) :=
        mul_le_mul_of_nonneg_right hNd (by positivity)
      _ = _ := by ring
  calc
    (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * d)) ^ (q + 1) =
      ENNReal.ofReal ((N : ℝ) * (Real.sqrt 2 * d) ^ (q + 1)) := by
        rw [ENNReal.ofReal_rpow_of_pos (mul_pos hs hd),
          ENNReal.ofReal_mul (Nat.cast_nonneg N)]
        simp
    _ ≤ ENNReal.ofReal ((2 * (Real.sqrt 2) ^ (q + 1)) * d ^ q) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_pos hd]
#check @checked
#print axioms checked
end YuiAuxiliary
