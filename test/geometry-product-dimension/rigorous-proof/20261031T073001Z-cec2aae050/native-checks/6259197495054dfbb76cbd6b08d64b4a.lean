import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤" := by
  classical
  have content_lower : ∀ (s : ℝ), 0 < s → s < 1 → ∀ (δ : ℝ), 0 < δ →
      ENNReal.ofReal (δ ^ (s-1)) ≤ GP.content s δ GP.unitInterval := by
    classical
    have length : ∀ (δ : ℝ), 0 < δ → ∀ (V : ℕ → Set ℝ),
        GP.Cover GP.unitInterval δ V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) := by
      classical
      intro δ hδ V hV
      have hb (i : ℕ) : Bornology.IsBounded (V i) :=
        Metric.isBounded_iff_ediam_ne_top.mpr
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i))
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      let w : ℕ → ℝ := fun i => (ε : ℝ) / 2 / 2 ^ i
      let h : ℕ → ℝ := fun i => w i / 2
      have hw (i : ℕ) : 0 < w i := by dsimp [w]; positivity
      have hh (i : ℕ) : 0 < h i := half_pos (hw i)
      let J : ℕ → Set ℝ := fun i =>
        if (V i).Nonempty then Set.Ioo (sInf (V i) - h i) (sSup (V i) + h i) else ∅
      have hsub (i : ℕ) : V i ⊆ J i := by
        intro x hx
        have hne : (V i).Nonempty := ⟨x, hx⟩
        simp only [J, if_pos hne]
        obtain ⟨hl, hu⟩ := (hb i).subset_Icc_sInf_sSup hx
        constructor <;> linarith [hh i]
      have hopen (i : ℕ) : IsOpen (J i) := by
        dsimp [J]
        split_ifs <;> simp only [isOpen_Ioo, isOpen_empty]
      have hJ (i : ℕ) :
          MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (w i) := by
        by_cases hne : (V i).Nonempty
        · simp only [J, if_pos hne, Real.volume_Ioo, Real.ediam_eq (hb i)]
          calc
            ENNReal.ofReal (sSup (V i) + h i - (sInf (V i) - h i)) =
                ENNReal.ofReal ((sSup (V i) - sInf (V i)) + w i) := by
              congr 1
              dsimp [h]
              ring
            _ ≤ _ := ENNReal.ofReal_add_le
        · simp only [J, if_neg hne, MeasureTheory.measure_empty, zero_le]
      have hcover : GP.unitInterval ⊆ ⋃ i, J i :=
        hV.1.trans (Set.iUnion_mono hsub)
      have hsum : (∑' i, ENNReal.ofReal (w i)) = (ε : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hw i).le)
          (summable_geometric_two' (ε : ℝ))]
        simp only [w, tsum_geometric_two', ENNReal.ofReal_coe_nnreal]
      calc
        (1 : ℝ≥0∞) = MeasureTheory.volume GP.unitInterval := by
          simp [GP.unitInterval, Real.volume_Icc]
        _ ≤ MeasureTheory.volume (⋃ i, J i) := MeasureTheory.measure_mono hcover
        _ ≤ ∑' i, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le _
        _ ≤ ∑' i, (Metric.ediam (V i) + ENNReal.ofReal (w i)) :=
          ENNReal.tsum_le_tsum hJ
        _ = (∑' i, Metric.ediam (V i)) + ε := by rw [ENNReal.tsum_add, hsum]
    have point : ∀ (s δ r : ℝ), 0 < s → s < 1 → 0 < δ → 0 ≤ r → r ≤ δ →
        ENNReal.ofReal (δ ^ (s-1)) * ENNReal.ofReal r ≤ ENNReal.ofReal r ^ s := by
      intro s δ r hs hs1 hδ hr hrδ
      by_cases hr0 : r = 0
      · subst r
        simp [ENNReal.zero_rpow_of_pos hs]
      · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
        rw [ENNReal.ofReal_rpow_of_nonneg hr hs.le,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        apply ENNReal.ofReal_le_ofReal
        calc
          δ ^ (s-1) * r ≤ r ^ (s-1) * r :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_nonpos hrp hrδ (by linarith)) hr
          _ = r ^ s := by
            conv_rhs => rw [show s = (s-1)+1 by ring, Real.rpow_add hrp, Real.rpow_one]
    intro s hs hs1 δ hδ
    unfold GP.content
    refine le_iInf fun V => le_iInf fun hV => ?_
    have hfin (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
    have hrepr (i : ℕ) :
        ENNReal.ofReal ((Metric.ediam (V i)).toReal) = Metric.ediam (V i) :=
      ENNReal.ofReal_toReal (hfin i)
    have hp (i : ℕ) :
        ENNReal.ofReal (δ ^ (s-1)) * Metric.ediam (V i) ≤
          ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s := by
      by_cases hne : (V i).Nonempty
      · have H := point s δ (Metric.ediam (V i)).toReal hs hs1 hδ
          ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hδ.le (hV.2 i))
        rw [hrepr i] at H
        exact H.trans (le_iSup (fun _ : (V i).Nonempty => Metric.ediam (V i) ^ s) hne)
      · have hempty : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        simp [hempty]
    calc
      ENNReal.ofReal (δ ^ (s-1)) = ENNReal.ofReal (δ ^ (s-1)) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (δ ^ (s-1)) * ∑' i, Metric.ediam (V i) :=
        mul_le_mul_left' (length δ hδ V hV) _
      _ = ∑' i, ENNReal.ofReal (δ ^ (s-1)) * Metric.ediam (V i) :=
        ENNReal.tsum_mul_left.symm
      _ ≤ GP.cost s V := ENNReal.tsum_le_tsum hp
  intro s hs hs1
  by_contra htop
  have hbound (δ : ℝ) (hδ : 0 < δ) :
      ENNReal.ofReal (δ ^ (s-1)) ≤ GP.hausdorff s GP.unitInterval :=
    (content_lower s hs hs1 δ hδ).trans
      (le_iSup₂ (f := fun δ (_ : 0 < δ) => GP.content s δ GP.unitInterval) δ hδ)
  have he : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (GP.hausdorff s GP.unitInterval).toReal + 1 ≤ δ ^ (s-1) :=
    (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hs1)).eventually
      (Filter.eventually_ge_atTop _)
  obtain ⟨δ, hδ, hlarge⟩ := (self_mem_nhdsWithin.and he).exists
  have hsmall : δ ^ (s-1) ≤ (GP.hausdorff s GP.unitInterval).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).mp (hbound δ hδ)
  linarith
#check @checked
#print axioms checked
end YuiAuxiliary
