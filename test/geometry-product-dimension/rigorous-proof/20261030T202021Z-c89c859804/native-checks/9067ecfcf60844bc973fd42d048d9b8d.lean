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

namespace Translation
set_option autoImplicit false

theorem T010 (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
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
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) :
    dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧
    GPmass (q + 1) (GPproduct E) = 0 := by
  classical
  by_cases hn0 : n = 0
  · exact h_T007 hn0
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hcontent : ∀ (q δ : ℝ), 1 ≤ n → dimH E < ENNReal.ofReal q →
      0 < δ → GPcontent (q + 1) δ (GPproduct E) = 0 := by
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
  have hmass : ∀ q : ℝ, dimH E < ENNReal.ofReal q →
      GPmass (q + 1) (GPproduct E) = 0 := by
    intro q hq
    apply le_antisymm ?_ (by positivity)
    unfold GPmass
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    rw [hcontent q δ hn hq hδ]
  have hbound : ∀ q : ℝ, dimH E < ENNReal.ofReal q →
      dimH (GPproduct E) ≤ ENNReal.ofReal (q + 1) := by
    intro q hq
    have hqpos : 0 < q := ENNReal.ofReal_pos.1 (lt_of_le_of_lt (by positivity) hq)
    have hs : 0 < q + 1 := by linarith
    exact (h_T003 (n + 1) (GPproduct E) (q + 1) hs).2.2.2.2.1 (hmass q hq)
  have hendpoint : ∀ (D F : ENNReal), D < ⊤ →
      (∀ q : ℝ, D < ENNReal.ofReal q → F ≤ ENNReal.ofReal (q + 1)) →
      F ≤ D + 1 := by
    intro D F hD hb
    have hq₀ : D < ENNReal.ofReal (D.toReal + 1) :=
      (ENNReal.lt_ofReal_iff_toReal_lt hD.ne).2 (by linarith)
    have hF : F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb _ hq₀)
    have hsum : ENNReal.ofReal (D.toReal + 1) = D + 1 := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
        ENNReal.ofReal_toReal hD.ne, ENNReal.ofReal_one]
    by_contra hh
    have hgap : D.toReal + 1 < F.toReal := by
      apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hF).1
      rw [hsum]
      exact lt_of_not_ge hh
    obtain ⟨q, hqD, hqF⟩ := exists_between (show D.toReal < F.toReal - 1 by linarith)
    have hq : D < ENNReal.ofReal q := (ENNReal.lt_ofReal_iff_toReal_lt hD.ne).2 hqD
    have hqpos : 0 < q := lt_of_le_of_lt ENNReal.toReal_nonneg hqD
    have hbq : F.toReal ≤ q + 1 :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) (hb q hq)
    linarith
  refine ⟨hendpoint (dimH E) (dimH (GPproduct E)) h_T005.2.2.2.2.1.2.2 hbound, ?_⟩
  intro q δ hq hδ
  exact ⟨hcontent q δ hn hq hδ, hmass q hq⟩

#check @T010
#print axioms T010

end Translation
