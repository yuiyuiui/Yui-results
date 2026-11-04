import Mathlib
open scoped ENNReal NNReal BigOperators
noncomputable section

abbrev GDVec (m : ℕ) := EuclideanSpace ℝ (Fin m)

def GDLine (t : ℝ) : GDVec 1 :=
  WithLp.toLp 2 (fun _ => t)

def GDInterval : Set ℝ := Set.Icc 0 1

def GDPoint {m : ℕ} (x : GDVec m) (t : ℝ) : GDVec (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)

def GDProduct {m : ℕ} (A : Set (GDVec m)) : Set (GDVec (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ GDInterval, z = GDPoint x t}

def GDCost {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (_ : A.Nonempty), (Metric.ediam A) ^ s

def GDContent {X : Type*} [PseudoEMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, GDCost s (U i)

def GDMeasure {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GDContent s δ A

def GDPositiveCover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (q r ε : ℝ) : Prop :=
  ∃ (K : Set ℕ) (U : K → Set X),
    A ⊆ ⋃ i, U i ∧
    (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧
    (∑' i, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal ε

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ (V : Set ℝ), Bornology.IsBounded V → V.Nonempty → ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ V ⊆ J ∧ MeasureTheory.volume J = Metric.ediam V + ENNReal.ofReal (2 * η)" := by
  intro V hV hne η hη
  refine ⟨Set.Ioo (sInf V - η) (sSup V + η), isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    have hx' := hV.subset_Icc_sInf_sSup hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  · rw [Real.volume_Ioo, Real.ediam_eq hV]
    have hnonneg : 0 ≤ sSup V - sInf V := sub_nonneg.mpr (Real.sInf_le_sSup V hV.bddBelow hV.bddAbove)
    rw [← ENNReal.ofReal_add hnonneg (by positivity)]
    congr 1
    ring

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ ε : ℝ≥0, (∑' i : ℕ, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i))) = (ε : ℝ≥0∞)" := by
  intro ε
  have heq (i : ℕ) : 2 * ((ε : ℝ) / 4 / 2 ^ i) = (ε : ℝ) / 2 / 2 ^ i := by ring
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' (ε : ℝ)), tsum_geometric_two']
  simp

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ U : ℕ → Set ℝ, GDInterval ⊆ ⋃ i, U i → (∀ i, Bornology.IsBounded (U i)) → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i)" := by
  classical
  intro U hcover hbdd
  let K : Set ℕ := {i | (U i).Nonempty}
  have hcoverK : GDInterval ⊆ ⋃ i : K, U i.val := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
  have hsum : (1 : ℝ≥0∞) ≤ ∑' i : K, Metric.ediam (U i.val) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
    have hJ : ∀ i : K, ∃ J : Set ℝ, IsOpen J ∧ U i.val ⊆ J ∧
        MeasureTheory.volume J = Metric.ediam (U i.val) +
          ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i.val)) := by
      intro i
      exact yui_aux_0001 n E (U i.val) (hbdd i.val) i.property
        ((ε : ℝ) / 4 / 2 ^ i.val) (by positivity)
    choose J hJopen hJU hJvol using hJ
    have hcoverJ : GDInterval ⊆ ⋃ i : K, J i := by
      exact hcoverK.trans (Set.iUnion_mono fun i => hJU i)
    have herror : (∑' i : K, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i.val))) ≤
        (ε : ℝ≥0∞) := by
      calc
        _ ≤ ∑' i : ℕ, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i)) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
        _ = _ := yui_aux_0002 n E ε
    calc
      (1 : ℝ≥0∞) = MeasureTheory.volume GDInterval := by simp [GDInterval]
      _ ≤ MeasureTheory.volume (⋃ i : K, J i) := MeasureTheory.measure_mono hcoverJ
      _ ≤ ∑' i : K, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
      _ = (∑' i : K, Metric.ediam (U i.val)) +
            ∑' i : K, ENNReal.ofReal (2 * ((ε : ℝ) / 4 / 2 ^ i.val)) := by
        simp_rw [hJvol]
        exact ENNReal.tsum_add
      _ ≤ (∑' i : K, Metric.ediam (U i.val)) + (ε : ℝ≥0∞) :=
        add_le_add le_rfl herror
  exact hsum.trans (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
    (fun i : ℕ => Metric.ediam (U i)))

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ (ρ : ℝ≥0∞) (s : ℝ), ρ ≠ ⊤ → 0 ≤ s → ρ ^ s = ENNReal.ofReal (ρ.toReal ^ s)" := by
  intro ρ s hfin hs
  calc
    ρ ^ s = (ENNReal.ofReal ρ.toReal) ^ s :=
      congrArg (fun x : ℝ≥0∞ => x ^ s) (ENNReal.ofReal_toReal hfin).symm
    _ = ENNReal.ofReal (ρ.toReal ^ s) :=
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ ρ : ℝ≥0∞, ρ ≤ ENNReal.ofReal δ → ENNReal.ofReal (δ ^ (s - 1)) * ρ ≤ ρ ^ s" := by
  intro s δ hs hs1 hδ ρ hρ
  have hfin : ρ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hρ
  have hconv : ENNReal.ofReal ρ.toReal = ρ := ENNReal.ofReal_toReal hfin
  have hpowconv : ρ ^ s = ENNReal.ofReal (ρ.toReal ^ s) :=
    yui_aux_0004 n E ρ s hfin hs.le
  have hrδ : ρ.toReal ≤ δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hρ
    simpa [ENNReal.toReal_ofReal hδ.le] using h
  by_cases hzero : ρ = 0
  · simp [hzero, ENNReal.zero_rpow_of_pos hs]
  · have hrpos : 0 < ρ.toReal := ENNReal.toReal_pos hzero hfin
    have hreal : δ ^ (s - 1) * ρ.toReal ≤ ρ.toReal ^ s := by
      calc
        _ ≤ ρ.toReal ^ (s - 1) * ρ.toReal :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hrpos hrδ (by linarith)) hrpos.le
        _ = ρ.toReal ^ (s - 1) * ρ.toReal ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ρ.toReal ^ s := by
          rw [← Real.rpow_add hrpos]
          congr 1
          ring
    calc
      ENNReal.ofReal (δ ^ (s - 1)) * ρ =
          ENNReal.ofReal (δ ^ (s - 1)) * ENNReal.ofReal ρ.toReal := by rw [hconv]
      _ = ENNReal.ofReal (δ ^ (s - 1) * ρ.toReal) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)).symm
      _ ≤ ENNReal.ofReal (ρ.toReal ^ s) := ENNReal.ofReal_le_ofReal hreal
      _ = ρ ^ s := hpowconv.symm

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (E : Set (GDVec n))  :
    ∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
  ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval := by
  classical
  intro s δ hs hs1 hδ
  unfold GDContent
  refine le_iInf fun U => le_iInf fun hcover => le_iInf fun hscale => ?_
  have hbdd : ∀ i, Bornology.IsBounded (U i) := by
    intro i
    exact Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hscale i))
  have hsum : (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) :=
    yui_aux_0003 n E U hcover hbdd
  have hcost : ∀ i, (Metric.ediam (U i)) ^ s ≤ GDCost s (U i) := by
    intro i
    by_cases hne : (U i).Nonempty
    · exact le_iSup_of_le hne le_rfl
    · have hempty : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, ENNReal.zero_rpow_of_pos hs]
  calc
    ENNReal.ofReal (δ ^ (s - 1)) = ENNReal.ofReal (δ ^ (s - 1)) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (δ ^ (s - 1)) * ∑' i, Metric.ediam (U i) :=
      mul_le_mul' le_rfl hsum
    _ = ∑' i, ENNReal.ofReal (δ ^ (s - 1)) * Metric.ediam (U i) :=
      ENNReal.tsum_mul_left.symm
    _ ≤ ∑' i, GDCost s (U i) := by
      exact ENNReal.tsum_le_tsum fun i =>
        (yui_aux_0005 n E s δ hs hs1 hδ (Metric.ediam (U i)) (hscale i)).trans (hcost i)

#check @T006
#print axioms T006

end Translation
