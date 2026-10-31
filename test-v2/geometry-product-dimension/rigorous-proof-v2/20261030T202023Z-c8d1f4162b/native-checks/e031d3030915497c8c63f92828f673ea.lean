import Mathlib
open scoped ENNReal NNReal
noncomputable section
abbrev YEucl (m : ℕ) := EuclideanSpace ℝ (Fin m)
def YI : Set ℝ := Set.Icc 0 1
def YJoin {m : ℕ} (x : YEucl m) (t : ℝ) : YEucl (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YBase {m : ℕ} (z : YEucl (m + 1)) : YEucl m :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def YLast {m : ℕ} (z : YEucl (m + 1)) : ℝ := z (Fin.last m)
def YF {m : ℕ} (A : Set (YEucl m)) : Set (YEucl (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ YI, z = YJoin x t}
def YLine (t : ℝ) : YEucl 1 := WithLp.toLp 2 (fun _ => t)
def YCover {X : Type*} [PseudoEMetricSpace X]
    (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def YCost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s
def YContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YCover δ A U), YCost s U
def YHaus {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A
def YCritical {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) : Prop :=
  0 ≤ dimH A ∧ ∀ s : ℝ, 0 < s →
    YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → YHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → YHaus s A = ⊤) ∧
    (YHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (YHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)

namespace Translation
set_option autoImplicit false

theorem T014 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T013 : 1 ≤ n → ∀ q : ℝ, 0 < q → dimH E < ENNReal.ofReal q → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ V : ℕ → Set (YEucl (n+1)), YCover (Real.sqrt 2 * r) (YF E) V ∧ YCost (q+1) V < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε)) :
    1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → YHaus (q+1) (YF E) = 0 ∧ dimH (YF E) ≤ ENNReal.ofReal (q+1) := by
  intro hn q hq
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt h_T006.1.1 hq)
  have hqone : 0 < q + 1 := by linarith
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hC : 0 < 2 * (Real.sqrt 2) ^ (q+1) := by positivity
  have hcontent : ∀ δ : ℝ, 0 < δ → YContent (q+1) δ (YF E) = 0 := by
    intro δ hδ
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hrpos : 0 < r := lt_min (by norm_num) (div_pos hδ hsqrt)
    have hrone : r ≤ 1 := min_le_left _ _
    have hrscale : Real.sqrt 2 * r ≤ δ := by
      have h : r * Real.sqrt 2 ≤ δ := (le_div_iff₀ hsqrt).mp (min_le_right _ _)
      simpa only [mul_comm] using h
    have hsmall : ∀ e : ℝ, 0 < e → YContent (q+1) δ (YF E) < ENNReal.ofReal e := by
      intro e he
      let ε : ℝ := e / (2 * (Real.sqrt 2) ^ (q+1))
      have hε : 0 < ε := div_pos he hC
      have hconvert : ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) = ENNReal.ofReal e := by
        congr 1
        exact mul_div_cancel₀ e (ne_of_gt hC)
      obtain ⟨V, hV, hcost⟩ := h_T013 hn q hqpos hq r hrpos hrone ε hε
      have hVδ : YCover δ (YF E) V := by
        refine ⟨hV.1, fun i => (hV.2 i).trans (ENNReal.ofReal_le_ofReal hrscale)⟩
      have hle : YContent (q+1) δ (YF E) ≤ YCost (q+1) V := by
        exact iInf_le_of_le V (iInf_le_of_le hVδ le_rfl)
      exact hle.trans_lt (hconvert ▸ hcost)
    by_contra hne
    have hpos : 0 < YContent (q+1) δ (YF E) := bot_lt_iff_ne_bot.mpr hne
    obtain ⟨e, he0, hepos, helt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
    exact (lt_irrefl (YContent (q+1) δ (YF E))) ((hsmall e (ENNReal.ofReal_pos.mp hepos)).trans helt)
  have hhaus : YHaus (q+1) (YF E) = 0 := by
    apply le_antisymm _ zero_le
    exact iSup_le fun δ => iSup_le fun hδ => le_of_eq (hcontent δ hδ)
  refine ⟨hhaus, ?_⟩
  exact ((h_T002 (n+1) (YF E)).2 (q+1) hqone).2.2.2.1 hhaus

#check @T014
#print axioms T014

end Translation
