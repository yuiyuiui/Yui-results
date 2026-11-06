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

namespace Translation
set_option autoImplicit false

namespace Local_T014
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (S : Set ℝ), Bornology.IsBounded S → S.Nonempty → ∀ (ε : ℝ), 0 < ε → ∀ i : ℕ, S ⊆ Set.Ioo (sInf S - ε / 4 / 2 ^ i) (sSup S + ε / 4 / 2 ^ i) ∧ MeasureTheory.volume (Set.Ioo (sInf S - ε / 4 / 2 ^ i) (sSup S + ε / 4 / 2 ^ i)) = Metric.ediam S + ENNReal.ofReal (ε / 2 / 2 ^ i)" := by
  intro S hb hn ε hε i
  have hh : 0 < ε / 4 / (2 : ℝ) ^ i := by positivity
  have hend : 0 ≤ sSup S - sInf S := sub_nonneg.mpr (Real.sInf_le_sSup S hb.bddBelow hb.bddAbove)
  constructor
  · intro x hx
    have hx' := hb.subset_Icc_sInf_sSup hx
    constructor <;> linarith [hx'.1, hx'.2]
  · rw [Real.volume_Ioo, Real.ediam_eq hb, ← ENNReal.ofReal_add hend (by positivity : 0 ≤ ε / 2 / (2 : ℝ) ^ i)]
    congr 1
    ring

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ (ε : ℝ), 0 ≤ ε → (∑' i : ℕ, ENNReal.ofReal (ε / 2 / (2 : ℝ) ^ i)) = ENNReal.ofReal ε" := by
  intro ε hε
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i : ℕ => by positivity) (summable_geometric_two' ε), tsum_geometric_two' ε]

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) : yui_aux_type% "∀ V : ℕ → Set ℝ, (∑' i : {i : ℕ // (V i).Nonempty}, Metric.ediam (V i.val)) = ∑' i : ℕ, Metric.ediam (V i)" := by
  classical
  intro V
  calc
    (∑' i : {i : ℕ // (V i).Nonempty}, Metric.ediam (V i.val)) = ∑' i : ℕ, ({i : ℕ | (V i).Nonempty}).indicator (fun i => Metric.ediam (V i)) i := tsum_subtype {i : ℕ | (V i).Nonempty} (fun i => Metric.ediam (V i))
    _ = _ := by
      apply tsum_congr
      intro i
      by_cases hi : (V i).Nonempty
      · simp [hi]
      · have hz : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
        simp [hi, hz]

end Local_T014
open Local_T014 in
theorem T014 (n : ℕ) (E : Set (YuiEucl n))  :
    ∀ δ : ℝ, 0 < δ → ∀ V : ℕ → Set ℝ, YuiCover δ YuiI V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) := by
  classical
  intro δ hδ V hV
  have hb : ∀ i, Bornology.IsBounded (V i) := by
    intro i
    apply Metric.isBounded_iff_ediam_ne_top.mpr
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  by_cases hinf : (∑' i, Metric.ediam (V i)) = ⊤
  · rw [hinf]
    exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
    let T := {i : ℕ // (V i).Nonempty}
    let J : T → Set ℝ := fun i => Set.Ioo (sInf (V i.val) - (ε : ℝ) / 4 / 2 ^ i.val) (sSup (V i.val) + (ε : ℝ) / 4 / 2 ^ i.val)
    have hJ : ∀ i : T, V i.val ⊆ J i ∧ MeasureTheory.volume (J i) = Metric.ediam (V i.val) + ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val) := by
      intro i
      exact (@yui_aux_0001 n E) (V i.val) (hb i.val) i.property (ε : ℝ) hεr i.val
    have hcov : YuiI ⊆ ⋃ i : T, J i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hx)
      exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, (hJ ⟨i, ⟨x, hi⟩⟩).1 hi⟩
    have herr : (∑' i : T, ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val)) ≤ ENNReal.ofReal (ε : ℝ) := by
      calc
        _ ≤ ∑' i : ℕ, ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i) := ENNReal.tsum_comp_le_tsum_of_injective (f := fun i : T => i.val) Subtype.val_injective _
        _ = _ := (@yui_aux_0002 n E) (ε : ℝ) hεr.le
    calc
      (1 : ℝ≥0∞) = MeasureTheory.volume YuiI := by simp [YuiI, Real.volume_Icc]
      _ ≤ MeasureTheory.volume (⋃ i : T, J i) := MeasureTheory.measure_mono hcov
      _ ≤ ∑' i : T, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
      _ = ∑' i : T, (Metric.ediam (V i.val) + ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val)) := tsum_congr (fun i => (hJ i).2)
      _ = (∑' i : T, Metric.ediam (V i.val)) + ∑' i : T, ENNReal.ofReal ((ε : ℝ) / 2 / 2 ^ i.val) := ENNReal.tsum_add
      _ ≤ (∑' i : ℕ, Metric.ediam (V i)) + ENNReal.ofReal (ε : ℝ) := add_le_add (le_of_eq ((@yui_aux_0003 n E) V)) herr
      _ = (∑' i : ℕ, Metric.ediam (V i)) + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]

#check @T014
#print axioms T014

end Translation
