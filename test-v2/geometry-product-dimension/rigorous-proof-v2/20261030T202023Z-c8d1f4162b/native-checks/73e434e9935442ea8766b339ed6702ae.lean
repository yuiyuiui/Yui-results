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

theorem T019 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T018 : ∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E ≤ YContent (s+1) δ (YF E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (YF E) := by
  intro hD
  have hDfin : dimH E < ⊤ := h_T006.1.2.2
  have hDpos : 0 < (dimH E).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hD, hDfin⟩
  have hDeq : ENNReal.ofReal (dimH E).toReal = dimH E :=
    ENNReal.ofReal_toReal hDfin.ne
  have hbelow : ∀ s : ℝ, s < (dimH E).toReal → ENNReal.ofReal s < dimH E := by
    intro s hs
    rw [← hDeq]
    exact (ENNReal.ofReal_lt_ofReal_iff hDpos).2 hs
  have hbound : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < dimH E →
      ENNReal.ofReal (s + 1) ≤ dimH (YF E) := by
    intro s hs hsD
    have hEinf : YHaus s E = ⊤ := ((h_T002 n E).2 s hs).2.2.1 hsD
    have hcomp : YHaus s E ≤ YHaus (s + 1) (YF E) := by
      unfold YHaus
      exact iSup_mono fun δ => iSup_mono fun hδ => h_T018 s δ hs hδ
    have hFinf : YHaus (s + 1) (YF E) = ⊤ := by
      apply top_unique
      rw [← hEinf]
      exact hcomp
    exact ((h_T002 (n + 1) (YF E)).2 (s + 1) (by linarith)).2.2.2.2 hFinf
  by_cases hFtop : dimH (YF E) = ⊤
  · rw [hFtop]
    exact le_top
  · have hreal : (dimH E).toReal + 1 ≤ (dimH (YF E)).toReal := by
      apply le_of_forall_lt_imp_le_of_dense
      intro r hr
      have hm : max 0 (r - 1) < (dimH E).toReal :=
        max_lt hDpos (by linarith)
      obtain ⟨s, hslo, hshi⟩ := exists_between hm
      have hspos : 0 < s := lt_of_le_of_lt (le_max_left _ _) hslo
      have hb : s + 1 ≤ (dimH (YF E)).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hFtop).mp (hbound s hspos (hbelow s hshi))
      have hrs : r - 1 < s := lt_of_le_of_lt (le_max_right _ _) hslo
      linarith
    have heq : ENNReal.ofReal ((dimH E).toReal + 1) = dimH E + 1 := by
      rw [ENNReal.ofReal_add hDpos.le (by norm_num), hDeq, ENNReal.ofReal_one]
    rw [← heq]
    exact ENNReal.ofReal_le_of_le_toReal hreal

#check @T019
#print axioms T019

end Translation
