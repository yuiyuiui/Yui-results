import Mathlib

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace WaveMap

abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)

def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)
def openBox (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-R) R)
def slab (t : ℝ) : Set ℝ := Set.Icc (t / 2) (3 * t / 2)

noncomputable def dt {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => deriv (fun r : ℝ => u (p.1, r)) p.2
noncomputable def dx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → V m :=
  fun p => fderiv ℝ (fun x : X n => u (x, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => deriv (fun r : ℝ => density u (p.1, r)) p.2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t)
noncomputable def timeProduct {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixedProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx u j p)
noncomputable def fluxDx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => fderiv ℝ (fun x : X n => flux u j (x, p.2)) p.1 (Pi.single j 1)

def sectionGood {n : ℕ} (C : Set (X n)) (R : ℝ) (f : X n → ℝ) : Prop :=
  Continuous f ∧ (∀ x, x ∉ C → f x = 0) ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box n R, |f x| ≤ B) ∧ Integrable f

def supportGeometry {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  IsCompact C ∧ 0 < R ∧ C ⊆ openBox n R ∧
  (∀ x, x ∉ C → ∀ r ∈ slab t, u (x, r) = q) ∧
  volume (box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
  volume (box n R) < ⊤ ∧
  (∀ k : ℕ, ∀ x, x ∉ C → ∀ r ∈ interior (slab t),
    iteratedFDeriv ℝ (k + 1) u (x, r) = 0)

def supportSections {n m : ℕ} (u : X n × ℝ → V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  ∀ r ∈ interior (slab t),
    sectionGood C R (fun x => density u (x, r)) ∧
    sectionGood C R (fun x => densityT u (x, r)) ∧
    sectionGood C R (fun x => timeProduct u (x, r)) ∧
    (∀ j : Fin n,
      sectionGood C R (fun x => mixedProduct u j (x, r)) ∧
      sectionGood C R (fun x => lapProduct u j (x, r)) ∧
      sectionGood C R (fun x => fluxDx u j (x, r)))

noncomputable def quotient {n m : ℕ} (u : X n × ℝ → V m)
    (t h : ℝ) (x : X n) : ℝ :=
  (density u (x, t + h) - density u (x, t)) / h

abbrev Other {n : ℕ} (j : Fin n) := {i : Fin n // i ≠ j}
def insertCoord {n : ℕ} (j : Fin n) (y : Other j → ℝ) (z : ℝ) : X n :=
  fun i => if h : i = j then z else y ⟨i, h⟩
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other j → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)

end WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n), MeasurePreserving (fun w : ({i : Fin n // ¬ i ≠ j} → ℝ) => w ⟨j, by simp⟩) volume volume" := by
  classical
  intro j
  let U : Unique {i : Fin n // ¬ i ≠ j} :=
    { default := ⟨j, by simp⟩
      uniq := fun i => Subtype.ext (not_ne_iff.mp i.property) }
  letI := U
  have hfin : (@Unique.fintype {i : Fin n // ¬ i ≠ j} U) =
      (Subtype.fintype (fun i : Fin n => ¬ i ≠ j)) := Subsingleton.elim _ _
  have h := volume_preserving_funUnique {i : Fin n // ¬ i ≠ j} ℝ
  rw [hfin] at h
  exact h

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n), ∃ e : WaveMap.X n ≃ᵐ ((WaveMap.Other j → ℝ) × ℝ), MeasurePreserving e ∧ ∀ (y : WaveMap.Other j → ℝ) (z : ℝ), e.symm (y, z) = WaveMap.insertCoord j y z" := by
  classical
  intro j
  letI : Unique {i : Fin n // ¬ i ≠ j} :=
    { default := ⟨j, by simp⟩
      uniq := fun i => Subtype.ext (not_ne_iff.mp i.property) }
  let e₁ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ≠ j)
  let e₂ := (MeasurableEquiv.refl (WaveMap.Other j → ℝ)).prodCongr
    (MeasurableEquiv.funUnique {i : Fin n // ¬ i ≠ j} ℝ)
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · exact (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ≠ j)).trans
      ((MeasurePreserving.id (volume : Measure (WaveMap.Other j → ℝ))).prod
        (@yui_aux_0001 n m u q j))
  · intro y z
    ext i
    change (if h : i ≠ j then y ⟨i, h⟩ else z) =
      (if h : i = j then z else y ⟨i, h⟩)
    by_cases h : i = j <;> simp [h]

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n) (R : ℝ) (y : WaveMap.Other j → ℝ) (z : ℝ), WaveMap.insertCoord j y z ∈ WaveMap.box n R ↔ y ∈ WaveMap.otherBox j R ∧ z ∈ Set.Icc (-R) R" := by
  classical
  intro j R y z
  simp only [WaveMap.box, WaveMap.otherBox, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [WaveMap.insertCoord, dif_neg i.property] using h i.val
    · simpa [WaveMap.insertCoord] using h j
  · rintro ⟨hy, hz⟩ i
    by_cases hij : i = j
    · simpa only [WaveMap.insertCoord, dif_pos hij] using hz
    · simpa only [WaveMap.insertCoord, dif_neg hij] using hy ⟨i, hij⟩

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n), (volume : Measure ((WaveMap.Other j → ℝ) × ℝ)) = (volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)" := by
  intro j
  exact Measure.volume_eq_prod (WaveMap.Other j → ℝ) ℝ

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m)  :
    ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z) := by
  classical
  intro j R hR f hf
  obtain ⟨e, he, hinv⟩ := @yui_aux_0002 n m u q j
  have hpre : e.symm ⁻¹' WaveMap.box n R =
      WaveMap.otherBox j R ×ˢ Set.Icc (-R) R := by
    ext ⟨y, z⟩
    change e.symm (y, z) ∈ WaveMap.box n R ↔ _
    rw [hinv]
    exact @yui_aux_0003 n m u q j R y z
  have hmp : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e he
  have hi : IntegrableOn (fun p => f (e.symm p))
      (WaveMap.otherBox j R ×ˢ Set.Icc (-R) R)
      ((volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)) := by
    have ht := (hmp.restrict_preimage_emb e.symm.measurableEmbedding
      (WaveMap.box n R)).integrable_comp_of_integrable hf
    simpa only [hpre, Function.comp_def, @yui_aux_0004 n m u q j] using ht
  calc
    (∫ x in WaveMap.box n R, f x) =
        ∫ p in WaveMap.otherBox j R ×ˢ Set.Icc (-R) R, f (e.symm p)
          ∂((volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)) := by
      symm
      simpa only [hpre, @yui_aux_0004 n m u q j] using
        hmp.setIntegral_preimage_emb e.symm.measurableEmbedding f (WaveMap.box n R)
    _ = ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R,
        f (e.symm (y, z)) := setIntegral_prod _ hi
    _ = ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R,
        f (WaveMap.insertCoord j y z) := by simp only [hinv]

#check @T008
#print axioms T008

end Translation
