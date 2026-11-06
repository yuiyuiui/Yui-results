import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → 0 < η → Metric.ediam B ≤ ENNReal.ofReal ρ → ∃ J : Set ℝ, MeasurableSet J ∧ B ⊆ J ∧ MeasureTheory.volume J ≤ ENNReal.ofReal (ρ + η)" := by
  intro B ρ η hB hρ hη hd
  have hb : Bornology.IsBounded B :=
    Metric.isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd)
  have hspan : sSup B - sInf B ≤ ρ := by
    rw [Real.ediam_eq hb] at hd
    exact (ENNReal.ofReal_le_ofReal_iff hρ).mp hd
  refine ⟨Set.Ioo (sInf B - η / 2) (sSup B + η / 2), measurableSet_Ioo, ?_, ?_⟩
  · intro t ht
    have h := hb.subset_Icc_sInf_sSup ht
    constructor <;> linarith [h.1, h.2]
  · rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    linarith

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (a : ℕ → ℝ) (ε : ℝ), (∀ i, 0 ≤ a i) → 0 < ε → (∑' i : ℕ, ENNReal.ofReal (a i * ((ε / 2 / (2 : ℝ)^i) / (1 + a i)))) ≤ ENNReal.ofReal ε" := by
  intro a ε ha hε
  calc
    (∑' i : ℕ, ENNReal.ofReal (a i * ((ε / 2 / (2 : ℝ)^i) / (1 + a i)))) ≤
        ∑' i : ℕ, ENNReal.ofReal (ε / 2 / (2 : ℝ)^i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      apply ENNReal.ofReal_le_ofReal
      have hpos : 0 < 1 + a i := by linarith [ha i]
      have hw : 0 ≤ ε / 2 / (2 : ℝ)^i := by positivity
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' ε),
        tsum_geometric_two' ε]

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → ∀ (V : ℕ → Set (YuiEucl (n + 1))), YuiCover δ (YuiCylinder E) V → ∀ (J : ℕ → Set ℝ), (∀ i, YuiLast '' V i ⊆ J i) → ∀ t ∈ YuiI, YuiContent s δ E ≤ ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (V i)) ^ s) t" := by
  classical
  intro s δ hs V hV J hJ t ht
  let W : ℕ → Set (YuiEucl n) := fun i => if t ∈ J i then YuiHead '' V i else ∅
  have hd (i : ℕ) : Metric.ediam (YuiHead '' V i) ≤ Metric.ediam (V i) := by
    simpa using (h_T003 n).2.2.2.1.ediam_image_le (V i)
  have hc : YuiCover δ E W := by
    constructor
    · intro x hx
      have hxt : YuiSnoc x t ∈ YuiCylinder E := by
        change YuiHead (YuiSnoc x t) ∈ E ∧ YuiLast (YuiSnoc x t) ∈ YuiI
        rw [(h_T003 n).1 x t |>.1, (h_T003 n).1 x t |>.2]
        exact ⟨hx, ht⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hxt)
      have hj : t ∈ J i := by
        have := hJ i (Set.mem_image_of_mem YuiLast hi)
        simpa only [(h_T003 n).1 x t |>.2] using this
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      dsimp [W]
      rw [if_pos hj]
      exact ⟨YuiSnoc x t, hi, (h_T003 n).1 x t |>.1⟩
    · intro i
      dsimp [W]
      split_ifs with h
      · exact (hd i).trans (hV.2 i)
      · simpa using (zero_le (ENNReal.ofReal δ))
  calc
    YuiContent s δ E ≤ YuiCost s W := iInf_le_of_le W (iInf_le_of_le hc le_rfl)
    _ ≤ ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (V i)) ^ s) t := by
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : t ∈ J i
      · simp only [Set.indicator_of_mem hi]
        apply iSup_le
        intro hne
        dsimp [W]
        rw [if_pos hi]
        exact ENNReal.rpow_le_rpow (hd i) hs.le
      · simp [W, hi]

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) (J : ℕ → Set ℝ), (∀ i, MeasurableSet (J i)) → (∀ t ∈ YuiI, c ≤ ∑' i, (J i).indicator (fun _ : ℝ => a i) t) → c ≤ ∑' i, a i * MeasureTheory.volume (J i)" := by
  intro c a J hJ hc
  have hI : MeasurableSet YuiI := measurableSet_Icc
  have hm (i : ℕ) : Measurable ((J i).indicator (fun _ : ℝ => a i)) :=
    measurable_const.indicator (hJ i)
  calc
    c = ∫⁻ _ : ℝ in YuiI, c := by
      simp [MeasureTheory.lintegral_const, YuiI, Real.volume_Icc]
    _ ≤ ∫⁻ t : ℝ in YuiI, ∑' i, (J i).indicator (fun _ : ℝ => a i) t := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hI] with t ht
      exact hc t ht
    _ = ∑' i, ∫⁻ t : ℝ in YuiI, (J i).indicator (fun _ : ℝ => a i) t :=
      MeasureTheory.lintegral_tsum (fun i => (hm i).aemeasurable)
    _ ≤ ∑' i, a i * MeasureTheory.volume (J i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [MeasureTheory.setLIntegral_indicator (hJ i), MeasureTheory.setLIntegral_const]
      exact mul_le_mul_left' (MeasureTheory.measure_mono Set.inter_subset_left) _

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (p : ℝ), 0 < p → ∀ V : ℕ → Set (YuiEucl (n + 1)), (∑' i, (Metric.ediam (V i)) ^ p) = YuiCost p V" := by
  classical
  intro p hp V
  apply tsum_congr
  intro i
  by_cases hi : (V i).Nonempty
  · simp [hi]
  · have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp [he, ENNReal.zero_rpow_of_pos hp]

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (C : ℝ≥0∞) (a : ℕ → ℝ) (ε : ℝ), (∀ i, 0 ≤ a i) → 0 < ε → C + (∑' i : ℕ, ENNReal.ofReal (a i * ((ε / 2 / (2 : ℝ)^i) / (1 + a i)))) ≤ C + ENNReal.ofReal ε" := by
  intro C a ε ha hε
  exact add_le_add (le_refl C) (yui_aux_0002 n E h_T003 h_T005 a ε ha hε)

theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T005 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YuiContent s δ E < ⊤)) : yui_aux_type% "∀ (P : ℕ → Prop) (f : ℕ → ℝ≥0∞), (∀ i, ¬ P i → f i = 0) → (∑' i, f i) = ∑' i : {i // P i}, f i" := by
  classical
  intro P f hf
  symm
  exact tsum_subtype_eq_of_support_subset (by
    intro i hi
    by_contra h
    exact hi (hf i h))
#check @checked
#print axioms checked
end YuiAuxiliary
