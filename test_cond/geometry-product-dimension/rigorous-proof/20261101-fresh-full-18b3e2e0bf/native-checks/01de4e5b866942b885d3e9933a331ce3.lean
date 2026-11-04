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

namespace Local_T018
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ z : GDVec 1, GDLine (z 0) = z" := by
  intro z
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "Isometry GDLine ∧ Function.Bijective GDLine" := by
  constructor
  · apply isometry_iff_dist_eq.mpr
    intro x y
    simp [GDLine, EuclideanSpace.dist_eq, Real.sqrt_sq (dist_nonneg : 0 ≤ dist x y)]
  · constructor
    · intro x y h
      have h0 := congrArg (fun z : GDVec 1 => z 0) h
      simpa [GDLine] using h0
    · intro z
      exact ⟨z 0, @yui_aux_0001 n E z⟩

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ {X Y : Type} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (f : X → Y), Isometry f → ∀ (s : ℝ) (B : Set X), GDCost s (f '' B) = GDCost s B" := by
  intro X Y _ _ f hf s B
  simp only [GDCost, Set.image_nonempty, hf.ediam_image]

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ {X : Type} [PseudoEMetricSpace X] (s δ : ℝ) (B : Set X) (U : ℕ → Set X) (hU : B ⊆ ⋃ i, U i) (hδ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), GDContent s δ B ≤ ∑' i, GDCost s (U i)" := by
  intro X _ s δ B U hU hδ
  unfold GDContent
  exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le hδ le_rfl))

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) : yui_aux_type% "∀ {X Y : Type} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (f : X → Y), Isometry f → ∀ (s δ : ℝ) (B : Set X), GDContent s δ (f '' B) ≤ GDContent s δ B" := by
  intro X Y _ _ f hf s δ B
  unfold GDContent
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hδ => ?_
  have hcover : f '' B ⊆ ⋃ i, f '' U i := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi, rfl⟩⟩
  have hdiam : ∀ i, Metric.ediam (f '' U i) ≤ ENNReal.ofReal δ := by
    intro i
    rw [hf.ediam_image]
    exact hδ i
  have hb : GDContent s δ (f '' B) ≤ ∑' i, GDCost s (f '' U i) :=
    @yui_aux_0004 n E Y _ s δ (f '' B) (fun i => f '' U i) hcover hdiam
  have hc : (∑' i, GDCost s (f '' U i)) = ∑' i, GDCost s (U i) :=
    tsum_congr fun i => @yui_aux_0003 n E X Y _ _ f hf s (U i)
  exact hb.trans_eq hc

end Local_T018
open Local_T018 in
theorem T018 (n : ℕ) (E : Set (GDVec n))  :
    Isometry GDLine ∧ Function.Bijective GDLine ∧
  ∀ A : Set ℝ,
    dimH (GDLine '' A) = dimH A ∧
    (∀ s δ : ℝ, 0 < s → 0 < δ →
      GDContent s δ (GDLine '' A) = GDContent s δ A) ∧
    (∀ s : ℝ, 0 < s → GDMeasure s (GDLine '' A) = GDMeasure s A) := by
  have hline := @yui_aux_0002 n E
  have hiso : Isometry GDLine := hline.1
  let g : GDVec 1 → ℝ := fun z => z 0
  have hg : Isometry g := hiso.right_inv (@yui_aux_0001 n E)
  refine ⟨hiso, hline.2, ?_⟩
  intro A
  have hback : g '' (GDLine '' A) = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      exact ht
    · intro x hx
      exact ⟨GDLine x, ⟨x, hx, rfl⟩, rfl⟩
  have hcontent : ∀ s δ : ℝ, GDContent s δ (GDLine '' A) = GDContent s δ A := by
    intro s δ
    apply le_antisymm
    · exact @yui_aux_0005 n E ℝ (GDVec 1) _ _ GDLine hiso s δ A
    · have hb := @yui_aux_0005 n E (GDVec 1) ℝ _ _ g hg s δ (GDLine '' A)
      rw [hback] at hb
      exact hb
  refine ⟨hiso.dimH_image A, ?_, ?_⟩
  · intro s δ _ _
    exact hcontent s δ
  · intro s _
    simp only [GDMeasure, hcontent]

#check @T018
#print axioms T018

end Translation
