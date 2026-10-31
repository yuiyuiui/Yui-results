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

theorem T018 (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
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
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) (h_T013 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GPcontent s δ E ≤ GPcontent (s + 1) δ (GPproduct E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (GPproduct E) := by
  intro hDpos
  have hDfin : dimH E ≠ ⊤ := h_T005.2.2.2.2.1.2.2.ne
  have hbound : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
      ENNReal.ofReal (s + 1) ≤ dimH (GPproduct E) := by
    intro s hs hsD
    have hEinfty : GPmass s E = ⊤ := (h_T003 n E s hs).2.2.2.1 hsD
    have hmassle : GPmass s E ≤ GPmass (s + 1) (GPproduct E) := by
      unfold GPmass
      exact iSup_mono fun δ => iSup_mono fun hδ => h_T013 s δ hs hδ
    have hFinfty : GPmass (s + 1) (GPproduct E) = ⊤ := by
      rw [hEinfty] at hmassle
      exact top_unique hmassle
    exact (h_T003 (n + 1) (GPproduct E) (s + 1) (by linarith)).2.2.2.2.2.1 hFinfty
  by_contra hnot
  have hlt : dimH (GPproduct E) < dimH E + 1 := lt_of_not_ge hnot
  have hdfin : dimH (GPproduct E) ≠ ⊤ := (lt_of_lt_of_le hlt le_top).ne
  have hD1fin : dimH E + 1 ≠ ⊤ := by simp [hDfin]
  have hDreal : 0 < (dimH E).toReal := ENNReal.toReal_pos hDpos.ne' hDfin
  have hdreal : (dimH (GPproduct E)).toReal < (dimH E).toReal + 1 := by
    have h := (ENNReal.toReal_lt_toReal hdfin hD1fin).2 hlt
    simpa only [ENNReal.toReal_add hDfin (by simp : (1 : ENNReal) ≠ ⊤), ENNReal.toReal_one] using h
  have hmax : max 0 ((dimH (GPproduct E)).toReal - 1) < (dimH E).toReal :=
    max_lt hDreal (by linarith)
  obtain ⟨s, hsmax, hsD⟩ := exists_between hmax
  have hs : 0 < s := lt_of_le_of_lt (le_max_left _ _) hsmax
  have hds : (dimH (GPproduct E)).toReal < s + 1 := by
    have := lt_of_le_of_lt (le_max_right 0 ((dimH (GPproduct E)).toReal - 1)) hsmax
    linarith
  have hsDE : ENNReal.ofReal s < dimH E := by
    rw [← ENNReal.ofReal_toReal hDfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hDreal).2 hsD
  have hdF : dimH (GPproduct E) < ENNReal.ofReal (s + 1) := by
    rw [← ENNReal.ofReal_toReal hdfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < s + 1)).2 hds
  exact (not_lt_of_ge (hbound s hs hsDE)) hdF

#check @T018
#print axioms T018

end Translation
