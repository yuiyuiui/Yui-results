import Mathlib
open scoped BigOperators ContDiff Topology
open MeasureTheory
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def timeDomain (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
noncomputable def dt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (u x) t
noncomputable def dtt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => dt u x r) t
noncomputable def dx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (EuclideanSpace.single j 1)
noncomputable def du {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => u y t) j x
noncomputable def duu {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => du u j y t) j x
noncomputable def dut {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => dt u y t) j x
noncomputable def lap {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, duu u j x t
noncomputable def density {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖dt u x t‖ ^ 2 + ∑ j, ‖du u j x t‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
noncomputable def energy {n m : ℕ} (u : Space n → ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
noncomputable def flux {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (dt u x t) (du u j x t)
def box {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Icc (-R) R}
def openBox {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Ioo (-R) R}
def sectionGood {n : ℕ} (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ) : Prop :=
  Continuous f ∧ (∃ B : ℝ, ∀ x ∈ box (n := n) R, |f x| ≤ B) ∧
  (∀ x ∉ C, f x = 0) ∧ Integrable f
end WaveMap

open WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) : yui_aux_type% "∀ j : Fin n, ∃ e : (Fin n → ℝ) ≃ᵐ (({i : Fin n // i ≠ j} → ℝ) × ℝ), (∀ x : Fin n → ℝ, e x = ((fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Fin n → ℝ)) ((volume : Measure ({i : Fin n // i ≠ j} → ℝ)).prod (volume : Measure ℝ))" := by
  classical
  intro j
  letI : Unique {i : Fin n // ¬i ≠ j} :=
    { default := ⟨j, by simp⟩
      uniq := fun i => Subtype.ext (not_ne_iff.mp i.property) }
  let a := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ≠ j)
  let b := (MeasurableEquiv.refl ({i : Fin n // i ≠ j} → ℝ)).prodCongr
    (MeasurableEquiv.piUnique (fun _ : {i : Fin n // ¬i ≠ j} => ℝ))
  refine ⟨a.trans b, ?_, ?_⟩
  · intro x
    rfl
  · have ha : MeasurePreserving a (volume : Measure (Fin n → ℝ))
        ((volume : Measure ({i : Fin n // i ≠ j} → ℝ)).prod
          (volume : Measure ({i : Fin n // ¬i ≠ j} → ℝ))) :=
      volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ≠ j)
    have hb : MeasurePreserving b
        ((volume : Measure ({i : Fin n // i ≠ j} → ℝ)).prod
          (volume : Measure ({i : Fin n // ¬i ≠ j} → ℝ)))
        ((volume : Measure ({i : Fin n // i ≠ j} → ℝ)).prod (volume : Measure ℝ)) :=
      (MeasurePreserving.id (volume : Measure ({i : Fin n // i ≠ j} → ℝ))).prod
        (volume_preserving_piUnique (fun _ : {i : Fin n // ¬i ≠ j} => ℝ))
    exact hb.comp ha

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) :
    ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ)) := by
  classical
  intro j
  obtain ⟨s, hs, hμs⟩ := (@yui_aux_0001 n m u q h_H001) j
  let a : Space n ≃ᵐ (Fin n → ℝ) := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  let b : (({i : Fin n // i ≠ j} → ℝ) × ℝ) ≃ᵐ
      ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ) :=
    (MeasurableEquiv.toLp 2 ({i : Fin n // i ≠ j} → ℝ)).prodCongr
      (MeasurableEquiv.refl ℝ)
  refine ⟨a.trans (s.trans b), ?_, ?_⟩
  · intro x
    change (WithLp.toLp 2 (s (WithLp.ofLp x)).1, (s (WithLp.ofLp x)).2) = _
    rw [hs (WithLp.ofLp x)]
  · have ha : MeasurePreserving a (volume : Measure (Space n))
        (volume : Measure (Fin n → ℝ)) := PiLp.volume_preserving_ofLp (Fin n)
    have hb : MeasurePreserving b
        ((volume : Measure ({i : Fin n // i ≠ j} → ℝ)).prod (volume : Measure ℝ))
        ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod
          (volume : Measure ℝ)) :=
      (PiLp.volume_preserving_toLp {i : Fin n // i ≠ j}).prod
        (MeasurePreserving.id (volume : Measure ℝ))
    exact hb.comp (hμs.comp ha)

#check @T006
#print axioms T006

end Translation
