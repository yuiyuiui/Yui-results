import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

namespace Translation
set_option autoImplicit false

theorem T012 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T011 : ∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E ≤ yContent (s+1) δ (yProd E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (yProd E) := by
  intro hDpos
  have hDfin : dimH E ≠ ⊤ := h_T002.1.ne
  have hDrealpos : 0 < (dimH E).toReal :=
    ENNReal.toReal_pos hDpos.ne' hDfin
  have hDrepr : ENNReal.ofReal (dimH E).toReal = dimH E :=
    ENNReal.ofReal_toReal hDfin
  have hmono : ∀ (s δ δ' : ℝ), δ' ≤ δ →
      yContent s δ E ≤ yContent s δ' E := by
    intro s δ δ' hδ
    unfold yContent
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    exact iInf_le_of_le U (iInf_le_of_le hU
      (iInf_le_of_le (fun i => (hd i).trans (ENNReal.ofReal_le_ofReal hδ)) le_rfl))
  have F003 : ∀ s : ℝ, 0 < s → s < (dimH E).toReal →
      ENNReal.ofReal (s + 1) ≤ dimH (yProd E) := by
    intro s hs hsD
    have hsD' : ENNReal.ofReal s < dimH E :=
      (ENNReal.ofReal_lt_iff_lt_toReal hs.le hDfin).2 hsD
    have htopE : yHaus s E = ⊤ :=
      ((h_T001.1 n).2 E s hs).2.2.1 hsD'
    have F001 : ∀ (T ε : ℝ), 0 < T → 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ENNReal.ofReal T < yContent s δ E := by
      intro T ε hT hε
      have hlarge : ENNReal.ofReal T < yHaus s E := by
        rw [htopE]
        exact ENNReal.ofReal_lt_top
      change ENNReal.ofReal T < ⨆ δ : ℝ, ⨆ (_ : 0 < δ), yContent s δ E at hlarge
      obtain ⟨δ, hδ⟩ := lt_iSup_iff.mp hlarge
      obtain ⟨hδpos, hδlarge⟩ := lt_iSup_iff.mp hδ
      refine ⟨min δ ε, lt_min hδpos hε, min_le_right _ _, ?_⟩
      exact hδlarge.trans_le (hmono s δ (min δ ε) (min_le_left _ _))
    have F002 : ∀ T : ℝ, 0 < T →
        ENNReal.ofReal T < yHaus (s + 1) (yProd E) := by
      intro T hT
      obtain ⟨δ, hδpos, _, hδlarge⟩ := F001 T 1 hT zero_lt_one
      have hbound : yContent (s + 1) δ (yProd E) ≤ yHaus (s + 1) (yProd E) := by
        unfold yHaus
        exact le_iSup_of_le δ (le_iSup_of_le hδpos le_rfl)
      exact hδlarge.trans_le ((h_T011 s δ hs hδpos).trans hbound)
    have htopF : yHaus (s + 1) (yProd E) = ⊤ := by
      by_contra hfinite
      have hTpos : 0 < (yHaus (s + 1) (yProd E)).toReal + 1 :=
        by positivity
      have hlt := F002 ((yHaus (s + 1) (yProd E)).toReal + 1) hTpos
      have hlt' := (ENNReal.ofReal_lt_iff_lt_toReal hTpos.le hfinite).1 hlt
      linarith
    have hsp : 0 < s + 1 := by linarith
    exact ((h_T001.1 (n + 1)).2 (yProd E) (s + 1) hsp).2.2.2.2 htopF
  have hrepr : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add (le_of_lt hDrealpos) (by norm_num), hDrepr]
    norm_num
  rw [← hrepr]
  by_cases hQtop : dimH (yProd E) = ⊤
  · rw [hQtop]
    exact le_top
  · apply (ENNReal.ofReal_le_iff_le_toReal hQtop).2
    by_contra hnot
    have hQlt : (dimH (yProd E)).toReal < (dimH E).toReal + 1 :=
      lt_of_not_ge hnot
    have hmax : max 0 ((dimH (yProd E)).toReal - 1) < (dimH E).toReal := by
      apply max_lt hDrealpos
      linarith
    obtain ⟨s, hslo, hsD⟩ := exists_between hmax
    have hs : 0 < s := (le_max_left _ _).trans_lt hslo
    have hsQ : (dimH (yProd E)).toReal - 1 < s :=
      (le_max_right _ _).trans_lt hslo
    have hbound := (ENNReal.ofReal_le_iff_le_toReal hQtop).1 (F003 s hs hsD)
    linarith

#check @T012
#print axioms T012

end Translation
