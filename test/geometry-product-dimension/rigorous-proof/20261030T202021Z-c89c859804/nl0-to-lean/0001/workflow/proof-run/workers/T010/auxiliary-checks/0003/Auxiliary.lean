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
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T007 : n = 0 →
  dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧ GPmass (q + 1) (GPproduct E) = 0) (h_T009 : 1 ≤ n → ∀ (q r ε : ℝ),
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  ∃ W : ℕ → Set (GPEucl (n + 1)),
    GPcover (GPproduct E) (Real.sqrt 2 * r) W ∧
    GPcost (q + 1) W <
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) : yui_aux_type% "∀ (q δ : ℝ), 1 ≤ n → dimH E < ENNReal.ofReal q → 0 < δ → GPcontent (q + 1) δ (GPproduct E) = 0" := by
  intro q δ hn hq hδ
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  let r : ℝ := min 1 (δ / Real.sqrt 2)
  have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hsqrt)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : Real.sqrt 2 * r ≤ δ := by
    have hh : r ≤ δ / Real.sqrt 2 := min_le_right _ _
    simpa only [mul_comm] using (le_div_iff₀ hsqrt).1 hh
  let C : ℝ := 2 * (Real.sqrt 2) ^ (q + 1)
  have hC : 0 < C := mul_pos (by norm_num) (Real.rpow_pos_of_pos hsqrt _)
  apply le_antisymm ?_ (by positivity)
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  have hηreal : 0 < (η : ℝ) := hη
  obtain ⟨W, hW, hcost⟩ := h_T009 hn q r ((η : ℝ) / C) hq hr hr1 (div_pos hηreal hC)
  have hcover : GPcover (GPproduct E) δ W := by
    exact ⟨hW.1, fun i => (hW.2 i).trans (ENNReal.ofReal_le_ofReal hrδ)⟩
  have hinf : GPcontent (q + 1) δ (GPproduct E) ≤ GPcost (q + 1) W :=
    iInf_le_of_le W (iInf_le _ hcover)
  have hsmall : GPcost (q + 1) W < ENNReal.ofReal (η : ℝ) := by
    convert hcost using 1
    dsimp [C] at *
    congr 1
    field_simp
  simpa using (hinf.trans hsmall.le)
#check @checked
#print axioms checked
end YuiAuxiliary
