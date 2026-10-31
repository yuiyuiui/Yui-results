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

theorem T017 (n : ℕ) (E : Set (GPEucl n)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
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
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T016 : dimH GPI = 1 ∧
  ∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤) :
    dimH GPI = 1 ∧
  (∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤) ∧
  (∀ (k : ℕ) (A : Set (GPEucl k)) (e : GPI → GPEucl k),
    (∀ t, e t ∈ A) →
    (∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)|) →
    (1 : ENNReal) ≤ dimH A ∧
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
      GPcontent s δ GPI ≤ GPcontent s δ A) := by
  classical
  refine ⟨h_T016.1, h_T016.2, ?_⟩
  intro k A e heA he
  have hed : ∀ t u : GPI, edist (t : ℝ) (u : ℝ) = edist (e t) (e u) := by
    intro t u
    rw [edist_dist, edist_dist, he, Real.dist_eq]
  have hc : ∀ (s δ : ℝ), 0 < s → 0 < δ →
      GPcontent s δ GPI ≤ GPcontent s δ A := by
    intro s δ hs hδ
    unfold GPcontent
    refine le_iInf fun V => le_iInf fun hV => ?_
    let P : ℕ → Set ℝ := fun i => {t | ∃ ht : t ∈ GPI, e ⟨t, ht⟩ ∈ V i}
    have hd : ∀ i, Metric.ediam (P i) ≤ Metric.ediam (V i) := by
      intro i
      apply Metric.ediam_le
      intro t ht u hu
      rcases ht with ⟨ht, hte⟩
      rcases hu with ⟨hu, hue⟩
      rw [hed ⟨t, ht⟩ ⟨u, hu⟩]
      exact Metric.edist_le_ediam_of_mem hte hue
    have hp : GPcover GPI δ P := by
      constructor
      · intro t ht
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 (heA ⟨t, ht⟩))
        exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩
      · intro i
        exact (hd i).trans (hV.2 i)
    calc
      (⨅ (U : ℕ → Set ℝ) (_ : GPcover GPI δ U), GPcost s U) ≤ GPcost s P :=
        iInf_le_of_le P (iInf_le_of_le hp le_rfl)
      _ ≤ GPcost s V := by
        unfold GPcost
        exact ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hd i) hs.le
  have hm : ∀ s : ℝ, 0 < s → GPmass s GPI ≤ GPmass s A := by
    intro s hs
    unfold GPmass
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hc s δ hs hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  refine ⟨?_, hc⟩
  by_contra hn
  have hlt : dimH A < (1 : ENNReal) := lt_of_not_ge hn
  obtain ⟨s, hs0, hds, hs1⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hs : 0 < s := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hds)
  have hsone : s < 1 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 1 by norm_num)).mp
    simpa using hs1
  have htop : GPmass s A = ⊤ := by
    apply top_unique
    calc
      ⊤ = GPmass s GPI := (h_T016.2 s hs hsone).symm
      _ ≤ GPmass s A := hm s hs
  have hdims : ENNReal.ofReal s ≤ dimH A := (h_T003 k A s hs).2.2.2.2.2.1 htop
  exact (not_lt_of_ge hdims) hds

#check @T017
#print axioms T017

end Translation
