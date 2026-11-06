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

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_T001 : ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) : yui_aux_type% "∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → Space m) (x : E), DifferentiableAt ℝ f x → ∀ e : E, fderiv ℝ (fun y => inner ℝ (f y) (f y)) x e = inner ℝ (f x) (fderiv ℝ f x e) + inner ℝ (fderiv ℝ f x e) (f x)" := by
  intro E _ _ f x hf e
  exact fderiv_inner_apply ℝ hf hf e

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_T001 : ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) : yui_aux_type% "∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → Space m) (x e : E), ContDiffAt ℝ 2 f x → (∀ᶠ y in 𝓝 x, ‖f y‖ = 1) → inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ f y e) x e) = -(‖fderiv ℝ f x e‖ ^ 2)" := by
  intro E _ _ f x e hf hu
  have first : (fun y => inner ℝ (f y) (fderiv ℝ f y e)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hf.eventually (by norm_num), hu.eventually_nhds] with y hy hunit
    have heq : (fun z => inner ℝ (f z) (f z)) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
      filter_upwards [hunit] with z hz
      simp [hz]
    have hd := congrArg (fun L : E →L[ℝ] ℝ => L e) heq.fderiv_eq
    rw [yui_aux_0001 n m u q h_H002 h_H004 h_H005 h_T001 f y (hy.differentiableAt (by norm_num)) e] at hd
    simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply] at hd
    have hc := real_inner_comm (fderiv ℝ f y e) (f y)
    linarith
  have hg : DifferentiableAt ℝ (fun y => fderiv ℝ f y e) x := by
    exact ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L e) first.fderiv_eq
  rw [fderiv_inner_apply ℝ (hf.differentiableAt (by norm_num)) hg] at hd
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hd
  linarith

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_T001 : ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) : yui_aux_type% "(2 : WithTop ℕ∞) ≤ ∞" := by
  change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_T001 : ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) : yui_aux_type% "∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dtt u x t) = -(‖dt u x t‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u x t) (duu u j x t) = -(‖du u j x t‖ ^ 2))" := by
  intro x t ht
  have hopen : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hjoint : ContDiffAt ℝ 2 (Function.uncurry u) (x,t) :=
    (h_H002.contDiffAt (hopen.mem_nhds ht)).of_le (yui_aux_0003 n m u q h_H002 h_H004 h_H005 h_T001)
  have htime : ContDiffAt ℝ 2 (u x) t := by
    exact hjoint.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have hspace : ContDiffAt ℝ 2 (fun y => u y t) x := by
    exact hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
  constructor
  · have hu : ∀ᶠ r in 𝓝 t, ‖u x r‖ = 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr
      exact h_H004 x r hr
    have h := yui_aux_0002 n m u q h_H002 h_H004 h_H005 h_T001 (u x) t 1 htime hu
    simpa only [fderiv_apply_one_eq_deriv, dt, dtt] using h
  · intro j
    have hu : ∀ᶠ y in 𝓝 x, ‖u y t‖ = 1 := Filter.Eventually.of_forall (fun y => h_H004 y t ht)
    exact yui_aux_0002 n m u q h_H002 h_H004 h_H005 h_T001 (fun y => u y t) x (EuclideanSpace.single j 1) hspace hu

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_T001 : ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) :
    ∀ (x : Space n) (t : ℝ), 0 < t → (inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) ∧ inner ℝ (u x t) (dtt u x t) = -(‖dt u x t‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u x t) (duu u j x t) = -(‖du u j x t‖ ^ 2)) ∧ (∀ a : ℝ, dtt u x t - lap u x t = a • u x t → a = (∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) ∧ dtt u x t - lap u x t = ((∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) • u x t := by
  intro x t ht
  obtain ⟨htt, hxx⟩ := yui_aux_0004 n m u q h_H002 h_H004 h_H005 h_T001 x t ht
  have identify : ∀ a : ℝ, dtt u x t - lap u x t = a • u x t → a = (∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2 := by
    intro a ha
    have hdot := congrArg (fun v : Space m => inner ℝ (u x t) v) ha
    rw [inner_sub_right, htt, lap, inner_sum] at hdot
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, h_H004 x t ht, one_pow, mul_one] at hdot
    simp_rw [hxx] at hdot
    rw [Finset.sum_neg_distrib] at hdot
    linarith
  refine ⟨h_T001 x t ht, htt, hxx, identify, ?_⟩
  obtain ⟨a, ha⟩ := h_H005 x t ht
  rw [ha, identify a ha]

#check @T002
#print axioms T002

end Translation
