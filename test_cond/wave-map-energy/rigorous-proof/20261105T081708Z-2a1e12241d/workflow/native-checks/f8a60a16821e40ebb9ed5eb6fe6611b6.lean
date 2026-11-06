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

namespace Local_T009
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T008 : ∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) : yui_aux_type% "∀ r : ℝ, 0 < r → HasDerivAt (fun x : ℝ => if 0 < x then energy u x else 0) 0 r" := by
  intro r hr
  have heq : (fun x : ℝ => if 0 < x then energy u x else 0) =ᶠ[𝓝 r] energy u := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
    exact if_pos hx
  have hd : HasDerivAt (energy u) 0 r := by
    simpa only [(h_T008 r hr).2.2] using (h_T008 r hr).2.1.hasDerivAt
  exact hd.congr_of_eventuallyEq heq

end Local_T009
open Local_T009 in
theorem T009 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T008 : ∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) :
    (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧ (∀ s t : ℝ, 0 < s → 0 < t → energy u t = energy u s) := by
  refine ⟨h_T008, ?_⟩
  let f : ℝ → ℝ := fun r => if 0 < r then energy u r else 0
  have hd : ∀ r : ℝ, 0 < r → HasDerivAt f 0 r :=
    @yui_aux_0001 n m u q h_T008
  have hinterval : ∀ a b : ℝ, 0 < a → a < b → energy u b = energy u a := by
    intro a b ha hab
    have hc : ContinuousOn f (Set.Icc a b) := by
      intro r hr
      exact (hd r (lt_of_lt_of_le ha hr.1)).continuousAt.continuousWithinAt
    have hi : ∀ r ∈ Set.Ioo a b, HasDerivAt f ((fun _ : ℝ => (0 : ℝ)) r) r := by
      intro r hr
      exact hd r (lt_trans ha hr.1)
    obtain ⟨c, hc_mem, hslope⟩ :=
      exists_hasDerivAt_eq_slope f (fun _ : ℝ => (0 : ℝ)) hab hc hi
    have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    have hdiff : f b - f a = 0 := by
      have hmul := (eq_div_iff hden).mp hslope
      simpa only [zero_mul] using hmul.symm
    have heq : f b = f a := sub_eq_zero.mp hdiff
    simpa only [f, if_pos ha, if_pos (lt_trans ha hab)] using heq
  intro s t hs ht
  rcases lt_trichotomy s t with hst | hst | hts
  · exact hinterval s t hs hst
  · subst t
    rfl
  · exact (hinterval t s ht hts).symm

#check @T009
#print axioms T009

end Translation
