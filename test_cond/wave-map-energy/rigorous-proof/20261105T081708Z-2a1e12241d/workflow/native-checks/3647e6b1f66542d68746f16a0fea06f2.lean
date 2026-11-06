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

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) : yui_aux_type% "∀ (x : Space n) (t : ℝ), 0 < t → DifferentiableAt ℝ (u x) t" := by
  intro x t ht
  have hopen : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hjoint : DifferentiableAt ℝ (Function.uncurry u) (x, t) :=
    (h_H002.contDiffAt (hopen.mem_nhds ht)).differentiableAt (by simp)
  have hcurve : DifferentiableAt ℝ (fun r : ℝ => (x, r)) t :=
    (differentiableAt_const (c := x)).prodMk differentiableAt_id
  exact hjoint.comp t hcurve

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) :
    ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0 := by
  intro x t ht
  have hd : HasDerivAt (u x) (dt u x t) t :=
    (yui_aux_0001 n m u q h_H002 h_H004 h_H005 x t ht).hasDerivAt
  have hp : HasDerivAt (fun r => inner ℝ (u x r) (u x r))
      (inner ℝ (u x t) (dt u x t) + inner ℝ (dt u x t) (u x t)) t :=
    hd.inner ℝ hd
  have heq : (fun r => inner ℝ (u x r) (u x r)) =ᶠ[nhds t] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr
    rw [real_inner_self_eq_norm_sq, h_H004 x r hr]
    norm_num
  have hc : HasDerivAt (fun r => inner ℝ (u x r) (u x r)) 0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq
  have hz : inner ℝ (u x t) (dt u x t) + inner ℝ (dt u x t) (u x t) = 0 :=
    hp.unique hc
  have horth : inner ℝ (u x t) (dt u x t) = 0 := by
    rw [real_inner_comm (dt u x t) (u x t)] at hz
    linarith
  refine ⟨horth, ?_⟩
  obtain ⟨a, ha⟩ := h_H005 x t ht
  rw [ha, inner_smul_right, real_inner_comm (dt u x t) (u x t), horth, mul_zero]

#check @T001
#print axioms T001

end Translation
