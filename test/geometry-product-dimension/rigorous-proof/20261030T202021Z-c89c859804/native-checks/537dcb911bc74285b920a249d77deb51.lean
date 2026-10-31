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
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) : yui_aux_type% "∀ (hn : 1 ≤ n) (q r b : ℝ), 0 < q → 0 < r → 0 < b → ∀ x : GPEucl n, ∃ V : Set (GPEucl n), x ∈ V ∧ 0 < Metric.ediam V ∧ Metric.ediam V ≤ ENNReal.ofReal r ∧ (Metric.ediam V) ^ q < ENNReal.ofReal b" := by
  intro hn q r b hq hr hb x
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : Nontrivial (GPEucl n) := inferInstance
  let ρ : ℝ := min r (b ^ q⁻¹) / 4
  have hp : 0 < ρ := div_pos (lt_min hr (Real.rpow_pos_of_pos hb _)) (by norm_num)
  have hd : Metric.ediam (Metric.ball x ρ) = ENNReal.ofReal (2 * ρ) := by
    rw [← Metric.diam_ball_eq x hp.le]
    exact (ENNReal.ofReal_toReal Metric.isBounded_ball.ediam_ne_top).symm
  refine ⟨Metric.ball x ρ, Metric.mem_ball_self hp, ?_, ?_, ?_⟩
  · rw [hd]; exact ENNReal.ofReal_pos.mpr (by positivity)
  · rw [hd]
    apply ENNReal.ofReal_le_ofReal
    have := min_le_left r (b ^ q⁻¹)
    dsimp [ρ]; linarith
  · rw [hd, ENNReal.ofReal_rpow_of_pos (by positivity)]
    apply (ENNReal.ofReal_lt_ofReal_iff hb).mpr
    have hlt : 2 * ρ < b ^ q⁻¹ := by
      have := min_le_right r (b ^ q⁻¹)
      have := Real.rpow_pos_of_pos hb q⁻¹
      dsimp [ρ]; linarith
    simpa only [Real.rpow_inv_rpow hb.le hq.ne'] using Real.rpow_lt_rpow (by positivity : 0 ≤ 2 * ρ) hlt hq
#check @checked
#print axioms checked
end YuiAuxiliary
