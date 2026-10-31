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

theorem T003 (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) :
    ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
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
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A) := by
  intro k A s hs
  have hr : (s.toNNReal : ℝ) = s := by
    rw [Real.toNNReal_of_nonneg hs.le]
    rfl
  have he : (s.toNNReal : ENNReal) = ENNReal.ofReal s := rfl
  have hEq := h_T002.1 k A s hs
  have hn : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) A = GPmass s A := by
    rw [hr, hEq]
  have hmono : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
      GPcontent s δ₂ A ≤ GPcontent s δ₁ A := by
    intro δ₁ δ₂ hδ₁ hδ₂ hδ
    unfold GPcontent
    refine le_iInf fun U => le_iInf fun hU => ?_
    have hU₂ : GPcover A δ₂ U :=
      ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hδ)⟩
    exact iInf_le_of_le U (iInf_le_of_le hU₂ le_rfl)
  refine ⟨hEq, bot_le, ?_, ?_, ?_, ?_, hmono, ?_, ?_⟩
  · intro h
    have hd : dimH A < (s.toNNReal : ENNReal) := by simpa only [he] using h
    simpa only [hn] using (hausdorffMeasure_of_dimH_lt (s := A) (d := s.toNNReal) hd)
  · intro h
    have hd : (s.toNNReal : ENNReal) < dimH A := by simpa only [he] using h
    simpa only [hn] using (hausdorffMeasure_of_lt_dimH (s := A) (d := s.toNNReal) hd)
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) A ≠ ⊤ := by
      rw [hn, h]
      exact ENNReal.zero_ne_top
    simpa only [he] using
      (dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := s.toNNReal) hm)
  · intro h
    have hm : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) A = ⊤ := by
      rw [hn, h]
    simpa only [he] using
      (le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := s.toNNReal) hm)
  · intro hm δ ε hδ hε
    have hc : GPcontent s δ A = 0 := by
      apply le_antisymm _ bot_le
      calc
        GPcontent s δ A ≤ GPmass s A := by
          unfold GPmass
          exact le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)
        _ = 0 := hm
    have hcε : GPcontent s δ A < ENNReal.ofReal ε := by
      rw [hc]
      exact ENNReal.ofReal_pos.mpr hε
    simpa only [GPcontent, iInf_lt_iff, exists_prop] using hcε
  · intro hm L δ₀ hL hδ₀
    have hlarge : ENNReal.ofReal L < GPmass s A := by
      rw [hm]
      exact ENNReal.ofReal_lt_top
    obtain ⟨δ, hδ, hbig⟩ : ∃ δ : ℝ, ∃ hδ : 0 < δ,
        ENNReal.ofReal L < GPcontent s δ A := by
      simpa only [GPmass, lt_iSup_iff] using hlarge
    refine ⟨min δ δ₀, lt_min hδ hδ₀, min_le_right _ _, ?_⟩
    exact hbig.trans_le (hmono (min δ δ₀) δ (lt_min hδ hδ₀) hδ (min_le_left _ _))

#check @T003
#print axioms T003

end Translation
