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

namespace Local_T012
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (ε : ℝ≥0), 0 < ε → 0 < (ε : ℝ) ∧ ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞)" := by
  intro ε hε
  exact ⟨by exact_mod_cast hε, ENNReal.ofReal_coe_nnreal⟩

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (q : ℝ) (U : ℕ → Set (GDVec (n + 1))), (∑' i : {j : ℕ | (U j).Nonempty}, GDCost q (U i)) = ∑' i, GDCost q (U i)" := by
  classical
  intro q U
  refine tsum_subtype_eq_of_support_subset (f := fun i : ℕ => GDCost q (U i)) (s := {j : ℕ | (U j).Nonempty}) ?_
  intro i hi
  change (U i).Nonempty
  by_contra hempty
  have hz : GDCost q (U i) = 0 := by simp [GDCost, hempty]
  exact hi hz

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) : yui_aux_type% "∀ (q : ℝ) (A : Set (GDVec (n + 1))), A.Nonempty → GDCost q A = (Metric.ediam A) ^ q" := by
  intro q A hA
  unfold GDCost
  exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup_of_le hA le_rfl)

end Local_T012
open Local_T012 in
theorem T012 (n : ℕ) (E : Set (GDVec n)) (h_T011 : ∀ s δ : ℝ, 0 < s → 0 < δ →
  ∀ (K : Set ℕ) (V : K → Set (GDVec (n + 1))),
    GDProduct E ⊆ ⋃ i, V i →
    (∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
    ∀ ε : ℝ, 0 < ε →
      GDContent s δ E ≤
        (∑' i, (Metric.ediam (V i)) ^ (s + 1)) + ENNReal.ofReal ε) :
    ∀ s δ : ℝ, 0 < s → 0 < δ →
  GDContent s δ E ≤ GDContent (s + 1) δ (GDProduct E) := by
  classical
  intro s δ hs hδ
  conv_rhs => unfold GDContent
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
  let K : Set ℕ := {i | (U i).Nonempty}
  let V : K → Set (GDVec (n + 1)) := fun i => U i
  have hcover : GDProduct E ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
  have hdiam : ∀ i, (V i).Nonempty ∧ Metric.ediam (V i) ≤ ENNReal.ofReal δ := by
    intro i
    exact ⟨i.property, hd i⟩
  have hsum : (∑' i : K, (Metric.ediam (V i)) ^ (s + 1)) =
      ∑' i, GDCost (s + 1) (U i) := by
    calc
      (∑' i : K, (Metric.ediam (V i)) ^ (s + 1)) =
          ∑' i : K, GDCost (s + 1) (U i) := by
        apply tsum_congr
        intro i
        exact (@yui_aux_0003 n E h_T011 (s + 1) (U i) i.property).symm
      _ = ∑' i, GDCost (s + 1) (U i) :=
        @yui_aux_0002 n E h_T011 (s + 1) U
  by_cases hinf : (∑' i, GDCost (s + 1) (U i)) = ⊤
  · rw [hinf]
    exact le_top
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨hεreal, hεcoe⟩ := @yui_aux_0001 n E h_T011 ε hε
    have h := h_T011 s δ hs hδ K V hcover hdiam (ε : ℝ) hεreal
    rw [hsum, hεcoe] at h
    exact h

#check @T012
#print axioms T012

end Translation
