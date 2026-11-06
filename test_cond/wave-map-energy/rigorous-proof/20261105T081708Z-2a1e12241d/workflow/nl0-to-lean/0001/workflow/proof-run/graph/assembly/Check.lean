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

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) : yui_aux_type% "∀ (v w : Space m), inner ℝ w v = inner ℝ v w" := by
  intro v w
  exact real_inner_comm _ _

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
  have hsym : inner ℝ (dt u x t) (u x t) = inner ℝ (u x t) (dt u x t) :=
    yui_aux_0002 n m u q h_H002 h_H004 h_H005 (u x t) (dt u x t)
  have horth : inner ℝ (u x t) (dt u x t) = 0 := by
    rw [hsym] at hz
    linarith
  refine ⟨horth, ?_⟩
  obtain ⟨a, ha⟩ := h_H005 x t ht
  rw [ha, inner_smul_right, hsym, horth, mul_zero]

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

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space n → ℝ → F), ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n) → ContDiffOn ℝ ∞ (fun p : Space n × ℝ => deriv (f p.1) p.2) (timeDomain n) ∧ ∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => dx (fun y => f y p.2) j p.1) (timeDomain n)" := by
  intro F _ _ f hf
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hat (x : Space n) (t : ℝ) (ht : 0 < t) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (x,t) :=
    (hf (x,t) ht).contDiffAt (ho.mem_nhds ht)
  constructor
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    have hh : ContDiffAt ℝ ∞ (fun z : (Space n × ℝ) × ℝ => f z.1.1 z.2) (p, p.2) :=
      (hat p.1 p.2 hp).comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun z : Space n × ℝ => fderiv ℝ (f z.1) z.2) p :=
      hh.fderiv contDiffAt_snd (by simp)
    simpa only [deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  · intro j p hp
    apply ContDiffAt.contDiffWithinAt
    have hh : ContDiffAt ℝ ∞ (fun z : (Space n × ℝ) × Space n => f z.2 z.1.2) (p, p.1) :=
      (hat p.1 p.2 hp).comp (p,p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    have hd : ContDiffAt ℝ ∞ (fun z : Space n × ℝ => fderiv ℝ (fun y => f y z.2) z.1) p :=
      hh.fderiv contDiffAt_fst (by simp)
    exact hd.clm_apply contDiffAt_const

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (f : Fin n → Space n × ℝ → ℝ), (∀ j, ContDiffOn ℝ ∞ (f j) (timeDomain n)) → ContDiffOn ℝ ∞ (fun p => ∑ j, f j p) (timeDomain n)" := by
  intro f hf
  exact ContDiffOn.sum (fun j _ => hf j)

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (f : Space n × ℝ → Space m), ContDiffOn ℝ ∞ f (timeDomain n) → ContDiffOn ℝ ∞ (fun p => ‖f p‖ ^ 2) (timeDomain n)" := by
  intro f hf
  have h : ContDiffOn ℝ ∞ (fun p => inner ℝ (f p) (f p)) (timeDomain n) := hf.inner ℝ hf
  simpa only [real_inner_self_eq_norm_sq] using h

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ r : ℝ, 0 < r →\nContinuous (fun x => density u x r) ∧\nContinuous (fun x => densityT u x r) ∧\nContinuous (fun x => inner ℝ (dt u x r) (dtt u x r)) ∧\n∀ j : Fin n, Continuous (flux u j r) ∧\nContinuous (fun x => inner ℝ (dut u j x r) (du u j x r)) ∧\nContinuous (fun x => inner ℝ (dt u x r) (duu u j x r)) ∧\nContinuous (fun x => dx (flux u j r) j x)" := by
  have ht : ContDiffOn ℝ ∞ (Function.uncurry (dt u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 u h_H002).1
  have htt : ContDiffOn ℝ ∞ (Function.uncurry (dtt u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (dt u) ht).1
  have hx (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (du u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 u h_H002).2 j
  have hxt (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (dut u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (dt u) ht).2 j
  have hxx (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (duu u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (du u j) (hx j)).2 j
  have he : ContDiffOn ℝ ∞ (Function.uncurry (density u)) (timeDomain n) := by
    exact (yui_aux_0003 n m u q h_H001 h_H002 h_H006 _ ht).add
      (yui_aux_0002 n m u q h_H001 h_H002 h_H006 _ (fun j =>
        yui_aux_0003 n m u q h_H001 h_H002 h_H006 _ (hx j)))
  have het : ContDiffOn ℝ ∞ (Function.uncurry (densityT u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (density u) he).1
  have hf (j : Fin n) : ContDiffOn ℝ ∞ (fun p : Space n × ℝ => flux u j p.2 p.1) (timeDomain n) :=
    ht.inner ℝ (hx j)
  have hfx (j : Fin n) : ContDiffOn ℝ ∞ (fun p : Space n × ℝ => dx (flux u j p.2) j p.1) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (fun x t => flux u j t x) (hf j)).2 j
  intro r hr
  have sec (f : Space n × ℝ → ℝ) (h : ContDiffOn ℝ ∞ f (timeDomain n)) :
      Continuous (fun x => f (x,r)) :=
    h.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) (fun x => hr)
  refine ⟨sec _ he, sec _ het, sec _ (ht.inner ℝ htt), ?_⟩
  intro j
  exact ⟨sec _ (hf j), sec _ ((hxt j).inner ℝ (hx j)),
    sec _ (ht.inner ℝ (hxx j)), sec _ (hfx j)⟩

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ R : ℝ, volume ((@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' (Set.Icc (fun _ : Fin n => -R) (fun _ : Fin n => R))) = volume (Set.Icc (fun _ : Fin n => -R) (fun _ : Fin n => R))" := by
  intro R
  exact (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet

theorem yui_aux_0006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ R : ℝ, 0 < R → IsCompact (box (n := n) R) ∧\nvolume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤" := by
  intro R hR
  let B : Set (Fin n → ℝ) := Set.Icc (fun _ => -R) (fun _ => R)
  have him : WithLp.toLp 2 '' B = box (n := n) R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact fun j => ⟨hy.1 j, hy.2 j⟩
    · intro hx
      exact ⟨WithLp.ofLp x, ⟨fun j => (hx j).1, fun j => (hx j).2⟩, rfl⟩
  have hc : IsCompact (box (n := n) R) := by
    rw [← him]
    exact isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
  have hv : volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) := by
    have hp : WithLp.ofLp ⁻¹' B = box (n := n) R := by
      ext x
      exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
    rw [← hp, yui_aux_0005 n m u q h_H001 h_H002 h_H006 R]
    simp only [B, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) _).symm
  exact ⟨hc, hv, hv ▸ ENNReal.ofReal_lt_top⟩

theorem yui_aux_0007 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F) (x : Space n), fderiv ℝ (fun _ : Space n => c) x = 0" := by
  intro F _ _ c x
  simp

theorem yui_aux_0008 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]\n(f : Space n → ℝ → F) (c : F) (S : Set (Space n × ℝ)),\nIsOpen S → Set.EqOn (Function.uncurry f) (fun _ => c) S →\n(∀ p ∈ S, deriv (f p.1) p.2 = 0) ∧\n(∀ j : Fin n, ∀ p ∈ S, dx (fun y => f y p.2) j p.1 = 0)" := by
  intro F _ _ f c S hS hf
  constructor
  · intro p hp
    have he : f p.1 =ᶠ[𝓝 p.2] (fun _ => c) := by
      have ht : Filter.Tendsto (fun r : ℝ => (p.1,r)) (𝓝 p.2) (𝓝 p) :=
        (continuous_const.prodMk continuous_id).continuousAt
      exact (ht.eventually (hS.mem_nhds hp)).mono (fun r hr => hf hr)
    simpa only [deriv_const] using he.deriv_eq
  · intro j p hp
    have he : (fun y => f y p.2) =ᶠ[𝓝 p.1] (fun _ => c) := by
      have ht : Filter.Tendsto (fun y : Space n => (y,p.2)) (𝓝 p.1) (𝓝 p) :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact (ht.eventually (hS.mem_nhds hp)).mono (fun y hy => hf hy)
    unfold dx
    rw [he.fderiv_eq, yui_aux_0007 n m u q h_H001 h_H002 h_H006 c p.1]
    rfl

theorem yui_aux_0009 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (S : Set (Space n × ℝ)), IsOpen S →\nSet.EqOn (Function.uncurry u) (fun _ => q) S →\n∀ p ∈ S, Function.uncurry u =ᶠ[𝓝 p] (fun _ => q)" := by
  intro S hS hu p hp
  exact Filter.eventually_of_mem (hS.mem_nhds hp) (fun z hz => hu hz)

theorem yui_aux_0010 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (S : Set (Space n × ℝ)), IsOpen S →\nSet.EqOn (Function.uncurry u) (fun _ => q) S →\n∀ (k : ℕ) (p : Space n × ℝ), 0 < k → p ∈ S →\niteratedFDeriv ℝ k (Function.uncurry u) p = 0" := by
  intro S hS hu k p hk hp
  have he : Function.uncurry u =ᶠ[𝓝 p] (fun _ => q) :=
    yui_aux_0009 n m u q h_H001 h_H002 h_H006 S hS hu p hp
  have hd := (he.iteratedFDeriv ℝ k).eq_of_nhds
  rw [hd, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk)]
  rfl

theorem yui_aux_0011 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (S : Set (Space n × ℝ)), IsOpen S →\nSet.EqOn (Function.uncurry u) (fun _ => q) S →\n∀ p ∈ S, density u p.1 p.2 = 0 ∧ densityT u p.1 p.2 = 0 ∧\ninner ℝ (dt u p.1 p.2) (dtt u p.1 p.2) = 0 ∧\n∀ j : Fin n, flux u j p.2 p.1 = 0 ∧\ninner ℝ (dut u j p.1 p.2) (du u j p.1 p.2) = 0 ∧\ninner ℝ (dt u p.1 p.2) (duu u j p.1 p.2) = 0 ∧\ndx (flux u j p.2) j p.1 = 0" := by
  intro S hS hu
  have hpart := yui_aux_0008 n m u q h_H001 h_H002 h_H006 u q S hS hu
  have ht (p : Space n × ℝ) (hp : p ∈ S) : dt u p.1 p.2 = 0 := hpart.1 p hp
  have hx (j : Fin n) (p : Space n × ℝ) (hp : p ∈ S) : du u j p.1 p.2 = 0 := hpart.2 j p hp
  have he : Set.EqOn (Function.uncurry (density u)) (fun _ => (0 : ℝ)) S := by
    intro p hp
    simp [Function.uncurry, density, ht p hp, fun j => hx j p hp]
  have hf (j : Fin n) : Set.EqOn (Function.uncurry (fun x t => flux u j t x)) (fun _ => (0 : ℝ)) S := by
    intro p hp
    simp [Function.uncurry, flux, ht p hp]
  have het := (yui_aux_0008 n m u q h_H001 h_H002 h_H006 (density u) 0 S hS he).1
  have hfx (j : Fin n) :=
    (yui_aux_0008 n m u q h_H001 h_H002 h_H006 (fun x t => flux u j t x) 0 S hS (hf j)).2 j
  intro p hp
  refine ⟨he hp, het p hp, ?_, ?_⟩
  · simp [ht p hp]
  · intro j
    exact ⟨hf j hp, by simp [hx j p hp], by simp [ht p hp], hfx j p hp⟩

theorem yui_aux_0012 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (C : Set (Space n)) (R : ℝ), 0 < R → C ⊆ openBox (n := n) R →\n∀ (f : Space n → ℝ), Continuous f → (∀ x ∉ C, f x = 0) → sectionGood f C R" := by
  intro C R hR hC f hf hz
  obtain ⟨hQ, hvol, hfin⟩ := yui_aux_0006 n m u q h_H001 h_H002 h_H006 R hR
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ x ∈ box (n := n) R, |f x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB
  have hi : IntegrableOn f (box (n := n) R) := by
    apply Measure.integrableOn_of_bounded hfin.ne hf.aestronglyMeasurable
    exact ae_restrict_of_forall_mem hQ.isClosed.measurableSet hB
  have hglobal : Integrable f := hi.integrable_of_forall_notMem_eq_zero (fun x hx =>
    hz x (fun hxc => hx (fun j => ⟨(hC hxc j).1.le, (hC hxc j).2.le⟩)))
  exact ⟨hf, ⟨B, hb⟩, hz, hglobal⟩

theorem yui_aux_0013 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ C : Set (Space n), IsCompact C → ∃ R : ℝ, 0 < R ∧ C ⊆ openBox (n := n) R" := by
  intro C hC
  obtain ⟨R, hR, hb⟩ := hC.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, ?_⟩
  intro x hx j
  apply abs_lt.mp
  exact lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j) (hb x hx)

theorem yui_aux_0014 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ,\nIsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧\n(∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧\nvolume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧\nvolume (box (n := n) R) < ⊤ ∧\n(∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C →\n r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧\n(∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2),\nsectionGood (fun x => density u x r) C R ∧\nsectionGood (fun x => densityT u x r) C R ∧\nsectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧\n∀ j : Fin n, sectionGood (flux u j r) C R ∧\nsectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧\nsectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧\nsectionGood (fun x => dx (flux u j r) j x) C R)" := by
  intro t0 ht0
  obtain ⟨C, hC, hsupp⟩ := h_H006 (t0 / 2) (3 * t0 / 2) (by linarith) (by linarith)
  obtain ⟨R, hR, hCR⟩ := yui_aux_0013 n m u q h_H001 h_H002 h_H006 C hC
  have hQ := yui_aux_0006 n m u q h_H001 h_H002 h_H006 R hR
  let S : Set (Space n × ℝ) := Cᶜ ×ˢ Set.Ioo (t0 / 2) (3 * t0 / 2)
  have hS : IsOpen S := hC.isClosed.isOpen_compl.prod isOpen_Ioo
  have hu : Set.EqOn (Function.uncurry u) (fun _ => q) S := by
    intro p hp
    exact hsupp p.1 p.2 hp.1 ⟨hp.2.1.le, hp.2.2.le⟩
  have hz := yui_aux_0011 n m u q h_H001 h_H002 h_H006 S hS hu
  have hder := yui_aux_0010 n m u q h_H001 h_H002 h_H006 S hS hu
  refine ⟨C, R, hC, hR, hCR, hsupp, hQ.2.1, hQ.2.2, ?_, ?_⟩
  · intro k x r hk hx hr
    exact hder k (x,r) hk ⟨hx,hr⟩
  · intro r hr
    have hpos : 0 < r := by linarith [hr.1]
    have hc := yui_aux_0004 n m u q h_H001 h_H002 h_H006 r hpos
    have hzr (x : Space n) (hx : x ∉ C) := hz (x,r) ⟨hx,hr⟩
    have good (f : Space n → ℝ) (hf : Continuous f) (hzf : ∀ x ∉ C, f x = 0) :
        sectionGood f C R :=
      yui_aux_0012 n m u q h_H001 h_H002 h_H006 C R hR hCR f hf hzf
    refine ⟨good _ hc.1 (fun x hx => (hzr x hx).1),
      good _ hc.2.1 (fun x hx => (hzr x hx).2.1),
      good _ hc.2.2.1 (fun x hx => (hzr x hx).2.2.1), ?_⟩
    intro j
    exact ⟨good _ (hc.2.2.2 j).1 (fun x hx => ((hzr x hx).2.2.2 j).1),
      good _ (hc.2.2.2 j).2.1 (fun x hx => ((hzr x hx).2.2.2 j).2.1),
      good _ (hc.2.2.2 j).2.2.1 (fun x hx => ((hzr x hx).2.2.2 j).2.2.1),
      good _ (hc.2.2.2 j).2.2.2 (fun x hx => ((hzr x hx).2.2.2 j).2.2.2)⟩

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) :
    (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t)) := by
  have hw := yui_aux_0014 n m u q h_H001 h_H002 h_H006
  refine ⟨hw, ?_⟩
  intro t ht
  obtain ⟨C, R, hC, hR, hCR, hsupp, hvol, hfinite, hder, hsecs⟩ := hw t ht
  exact (hsecs t ⟨by linarith, by linarith⟩).1.2.2.2

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (f : Space n → ℝ → Space m), ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n) → (∀ (x : Space n) (t : ℝ), 0 < t → dt f x t = fderiv ℝ (Function.uncurry f) (x,t) (0,1) ∧ ∀ j : Fin n, du f j x t = fderiv ℝ (Function.uncurry f) (x,t) (EuclideanSpace.single j 1,0))" := by
  intro f hf x t ht
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hc : ContDiffAt ℝ ∞ (Function.uncurry f) (x,t) := (hf (x,t) ht).contDiffAt (ho.mem_nhds ht)
  have hd := hc.differentiableAt (by simp)
  constructor
  · have h := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
    exact h.deriv
  · intro j
    have hi : HasFDerivAt (fun y : Space n => (y,t)) ((ContinuousLinearMap.id ℝ (Space n)).prod 0) x := (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
    have h := hd.hasFDerivAt.comp x hi
    simpa [du, dx, Function.comp_def] using congrArg (fun L : Space n →L[ℝ] Space m => L (EuclideanSpace.single j 1)) h.fderiv

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (f : Space n → ℝ → Space m), ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n) → ContDiffOn ℝ ∞ (Function.uncurry (dt f)) (timeDomain n) ∧ ∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => du f j p.1 p.2) (timeDomain n)" := by
  intro f hf
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry f)) (timeDomain n) := hf.fderiv_of_isOpen ho (by simp)
  have hdir (v : Space n × ℝ) : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (Function.uncurry f) p v) (timeDomain n) := hD.clm_apply contDiffOn_const
  constructor
  · apply (hdir (0,1)).congr
    intro p hp
    exact (yui_aux_0001 n m u q h_H002 f hf p.1 p.2 hp).1
  · intro j
    apply (hdir (EuclideanSpace.single j 1,0)).congr
    intro p hp
    exact (yui_aux_0001 n m u q h_H002 f hf p.1 p.2 hp).2 j

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (f : Space n → ℝ → Space m) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n)) (p : Space n × ℝ), p ∈ timeDomain n → ∀ v w : Space n × ℝ, fderiv ℝ (fun z => fderiv ℝ (Function.uncurry f) z v) p w = fderiv ℝ (fderiv ℝ (Function.uncurry f)) p w v" := by
  intro f hf p hp v w
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry f)) (timeDomain n) := hf.fderiv_of_isOpen ho (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) p := ((hD p hp).contDiffAt (ho.mem_nhds hp)).differentiableAt (by simp)
  have he := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  simpa using congrArg (fun L : (Space n × ℝ) →L[ℝ] Space m => L w) he.fderiv

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω)" := by
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (x : Space n) (t : ℝ), 0 < t → ∀ j : Fin n, deriv (fun r => du u j x r) t = dut u j x t" := by
  intro x t ht j
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hs := yui_aux_0002 n m u q h_H002 u h_H002
  have he (v : Space n × ℝ) (g : Space n × ℝ → Space m) (hg : ∀ p ∈ timeDomain n, g p = fderiv ℝ (Function.uncurry u) p v) :
      fderiv ℝ g (x,t) = fderiv ℝ (fun p => fderiv ℝ (Function.uncurry u) p v) (x,t) := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [ho.mem_nhds ht] with p hp
    exact hg p hp
  have hj := he (EuclideanSpace.single j 1,0) (Function.uncurry (fun y r => du u j y r)) (fun p hp => (yui_aux_0001 n m u q h_H002 u h_H002 p.1 p.2 hp).2 j)
  have ht' := he (0,1) (Function.uncurry (dt u)) (fun p hp => (yui_aux_0001 n m u q h_H002 u h_H002 p.1 p.2 hp).1)
  have hc : ContDiffAt ℝ ∞ (Function.uncurry u) (x,t) := (h_H002 (x,t) ht).contDiffAt (ho.mem_nhds ht)
  have sym := hc.isSymmSndFDerivAt (yui_aux_0004 n m u q h_H002)
  change dt (fun y r => du u j y r) x t = du (dt u) j x t
  rw [(yui_aux_0001 n m u q h_H002 (fun y r => du u j y r) (hs.2 j) x t ht).1,
      (yui_aux_0001 n m u q h_H002 (dt u) hs.1 x t ht).2 j]
  rw [hj, ht']
  rw [yui_aux_0003 n m u q h_H002 u h_H002 (x,t) ht,
      yui_aux_0003 n m u q h_H002 u h_H002 (x,t) ht]
  exact sym (0,1) (EuclideanSpace.single j 1,0)

theorem yui_aux_0006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (dt u x) (dtt u x t) t ∧ ∀ j : Fin n, HasDerivAt (fun r => du u j x r) (dut u j x t) t" := by
  intro x t ht
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hs := yui_aux_0002 n m u q h_H002 u h_H002
  have hslice (f : Space n × ℝ → Space m) (hf : ContDiffOn ℝ ∞ f (timeDomain n)) : DifferentiableAt ℝ (fun r => f (x,r)) t := by
    have hd : DifferentiableAt ℝ f (x,t) := ((hf (x,t) ht).contDiffAt (ho.mem_nhds ht)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).differentiableAt
  constructor
  · exact (hslice (Function.uncurry (dt u)) hs.1).hasDerivAt
  · intro j
    rw [← yui_aux_0005 n m u q h_H002 x t ht j]
    exact (hslice (fun p => du u j p.1 p.2) (hs.2 j)).hasDerivAt

theorem yui_aux_0007 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => ‖dt u x r‖ ^ 2) (2 * inner ℝ (dt u x t) (dtt u x t)) t" := by
  intro x t ht
  exact (yui_aux_0006 n m u q h_H002 x t ht).1.norm_sq

theorem yui_aux_0008 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t" := by
  intro x t ht
  have hd := yui_aux_0006 n m u q h_H002 x t ht
  have h0 := yui_aux_0007 n m u q h_H002 x t ht
  have hj (j : Fin n) : HasDerivAt (fun r => ‖du u j x r‖ ^ 2) (2 * inner ℝ (du u j x t) (dut u j x t)) t := (hd.2 j).norm_sq
  have hsum : HasDerivAt (fun r => ∑ j : Fin n, ‖du u j x r‖ ^ 2) (∑ j : Fin n, 2 * inner ℝ (du u j x t) (dut u j x t)) t := HasDerivAt.fun_sum (fun j _ => hj j)
  change HasDerivAt (fun r => ‖dt u x r‖ ^ 2 + ∑ j : Fin n, ‖du u j x r‖ ^ 2) _ t
  simpa only [Finset.mul_sum] using h0.fun_add hsum

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) :
    (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n) := by
  classical
  have hs := yui_aux_0002 n m u q h_H002 u h_H002
  have hss := yui_aux_0002 n m u q h_H002 (dt u) hs.1
  have hpoint := yui_aux_0008 n m u q h_H002
  constructor
  · intro x t ht
    exact ⟨hpoint x t ht, (hpoint x t ht).deriv⟩
  · have hc : ContinuousOn (fun p : Space n × ℝ => 2 * inner ℝ (dt u p.1 p.2) (dtt u p.1 p.2) + 2 * ∑ j : Fin n, inner ℝ (du u j p.1 p.2) (dut u j p.1 p.2)) (timeDomain n) := by
      apply ContinuousOn.add
      · exact (hs.1.continuousOn.inner hss.1.continuousOn).const_mul 2
      · apply ContinuousOn.const_mul
        exact continuousOn_finsetSum _ (fun j _ => (hs.2 j).continuousOn.inner (hss.2 j).continuousOn)
    apply hc.congr
    intro p hp
    exact (hpoint p.1 p.2 hp).deriv

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ R : ℝ, IsCompact (box (n := n) R)" := by
  intro R
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-R) R)) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have he : box (n := n) R = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-R) R)) := by
    ext x
    simp [box, PiLp.homeomorph, Pi.le_def, forall_and]
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr hc

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ (t : ℝ), 0 < t → ∀ R : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box (n := n) R, ∀ r ∈ Set.Icc (t - t / 4) (t + t / 4), ‖densityT u x r‖ ≤ B" := by
  intro t ht R
  have hc : IsCompact ((box (n := n) R) ×ˢ Set.Icc (t-t/4) (t+t/4)) :=
    (@yui_aux_0001 n m u q h_H002 h_T003 h_T004 R).prod isCompact_Icc
  have hsub : (box (n := n) R) ×ˢ Set.Icc (t-t/4) (t+t/4) ⊆ timeDomain n := by
    intro p hp
    change 0 < p.2
    have := hp.2.1
    linarith
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (h_T004.2.mono hsub)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx r hr
  exact (hB (x,r) ⟨hx,hr⟩).trans (le_max_left _ _)

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ (t R B : ℝ), 0 < t → (∀ x ∈ box (n := n) R, ∀ r ∈ Set.Icc (t-t/4) (t+t/4), ‖densityT u x r‖ ≤ B) → ∀ (h : ℝ), h ≠ 0 → |h| < t/4 → ∀ x ∈ box (n := n) R, ‖(density u x (t+h) - density u x t) / h‖ ≤ B" := by
  intro t R B ht hB h hn hh x hx
  have hd : ∀ r ∈ Set.Icc (t-t/4) (t+t/4), HasDerivWithinAt (density u x) (densityT u x r) (Set.Icc (t-t/4) (t+t/4)) r := by
    intro r hr
    have hr0 : 0 < r := by linarith [hr.1]
    rw [(h_T004.1 x r hr0).2]
    exact (h_T004.1 x r hr0).1.hasDerivWithinAt
  have htmem : t ∈ Set.Icc (t-t/4) (t+t/4) := by constructor <;> linarith
  have hhmem : t+h ∈ Set.Icc (t-t/4) (t+t/4) := by
    rw [abs_lt] at hh
    constructor <;> linarith [hh.1, hh.2]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd (hB x hx) (convex_Icc _ _) htmem hhmem
  have hnabs : 0 < |h| := abs_pos.mpr hn
  rw [norm_div, Real.norm_eq_abs h, div_le_iff₀ hnabs]
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using hm

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ (t h : ℝ), 0 < t → 0 < t+h → AEStronglyMeasurable (fun x => (density u x (t+h) - density u x t) / h) volume" := by
  intro t h ht hh
  exact ((h_T003.2 (t+h) hh).sub (h_T003.2 t ht)).div_const h |>.aestronglyMeasurable

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ t : ℝ, 0 < t → HasDerivAt (energy u) (∫ x, densityT u x t) t" := by
  intro t ht
  classical
  obtain ⟨C, R, hC, hR, hCQ, hconst, hvol, hfin, hvan, hg⟩ := h_T003.1 t ht
  have htJ : t ∈ Set.Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hsmall : ∀ h : ℝ, |h| < t/4 → t+h ∈ Set.Ioo (t/2) (3*t/2) := by
    intro h hh
    rw [abs_lt] at hh
    constructor <;> linarith [hh.1, hh.2]
  have hCQ' : C ⊆ box (n := n) R := by
    intro x hx j
    exact ⟨(hCQ hx j).1.le, (hCQ hx j).2.le⟩
  obtain ⟨B, hB0, hB⟩ := @yui_aux_0002 n m u q h_H002 h_T003 h_T004 t ht R
  let bnd : Space n → ℝ := (box (n := n) R).indicator (fun _ => B)
  have hQmeas : MeasurableSet (box (n := n) R) :=
    (@yui_aux_0001 n m u q h_H002 h_T003 h_T004 R).measurableSet
  have hbnd : Integrable bnd := by
    exact (integrableOn_const hfin.ne).integrable_indicator hQmeas
  let v : ℝ → Space n → ℝ := fun h x =>
    if h ≠ 0 ∧ |h| < t/4 then (density u x (t+h) - density u x t) / h else 0
  have hevent : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 ∧ |h| < t/4 := by
    have hs : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |h| < t/4 := by
      have hb := Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < t/4)
      filter_upwards [hb] with h hh
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
    filter_upwards [self_mem_nhdsWithin, hs.filter_mono nhdsWithin_le_nhds] with h hn hh
    exact ⟨hn, hh⟩
  have hmeas : ∀ᶠ h : ℝ in 𝓝[≠] 0, AEStronglyMeasurable (v h) volume := by
    filter_upwards [hevent] with h hh
    have hc := ((hg (t+h) (hsmall h hh.2)).1.1.sub (hg t htJ).1.1).div_const h
    have hp : 0 < t+h := by linarith [(hsmall h hh.2).1]
    simpa only [v, if_pos hh] using
      (@yui_aux_0004 n m u q h_H002 h_T003 h_T004 t h ht hp)
  have hdom : ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ᵐ x ∂volume, ‖v h x‖ ≤ bnd x := by
    filter_upwards [hevent] with h hh
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ box (n := n) R
    · simpa only [v, if_pos hh, bnd, Set.indicator_of_mem hx] using
        (@yui_aux_0003 n m u q h_H002 h_T003 h_T004 t R B ht hB h hh.1 hh.2 x hx)
    · have hxc : x ∉ C := fun hc => hx (hCQ' hc)
      have hz1 := (hg (t+h) (hsmall h hh.2)).1.2.2.1 x hxc
      have hz0 := (hg t htJ).1.2.2.1 x hxc
      simp [v, hh, bnd, hx, hz1, hz0]
  have hlim : ∀ᵐ x ∂volume, Filter.Tendsto (fun h => v h x) (𝓝[≠] 0) (𝓝 (densityT u x t)) := by
    apply Filter.Eventually.of_forall
    intro x
    have hd : HasDerivAt (density u x) (densityT u x t) t := by
      rw [(h_T004.1 x t ht).2]
      exact (h_T004.1 x t ht).1
    apply hd.tendsto_slope_zero.congr'
    filter_upwards [hevent] with h hh
    dsimp only [v]
    rw [if_pos hh]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hDCT := tendsto_integral_filter_of_dominated_convergence bnd hmeas hdom hbnd hlim
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply hDCT.congr'
  filter_upwards [hevent] with h hh
  have hp : 0 < t+h := by linarith [(hsmall h hh.2).1]
  dsimp only [v]
  simp only [if_pos hh]
  rw [integral_div, integral_sub (h_T003.2 (t+h) hp) (h_T003.2 t ht)]
  simp only [energy, smul_eq_mul, div_eq_mul_inv, mul_comm]

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) :
    ∀ t : ℝ, 0 < t → (∀ x : Space n, densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => densityT u x t) ∧ Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) ∧ (∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t))) ∧ HasDerivAt (energy u) (∫ x, densityT u x t) t ∧ deriv (energy u) t = (∫ x, densityT u x t) ∧ deriv (energy u) t = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) + 2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t)) := by
  intro t ht
  classical
  obtain ⟨C, R, hC, hR, hCQ, hconst, hvol, hfin, hvan, hg⟩ := h_T003.1 t ht
  have htJ : t ∈ Set.Ioo (t/2) (3*t/2) := by constructor <;> linarith
  rcases hg t htJ with ⟨he, het, ha, hj⟩
  have hA : Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) := ha.2.2.2
  have hJ : ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) := by
    intro j
    exact ((hj j).2.1.2.2.2).congr (Filter.Eventually.of_forall (fun x => real_inner_comm _ _))
  have hD := @yui_aux_0005 n m u q h_H002 h_T003 h_T004 t ht
  refine ⟨(fun x => (h_T004.1 x t ht).2), het.2.2.2, hA, hJ, hD, hD.deriv, ?_⟩
  rw [hD.deriv]
  have hS : Integrable (fun x => ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hJ j)
  calc
    (∫ x, densityT u x t) =
        ∫ x, 2 * inner ℝ (dt u x t) (dtt u x t) +
          2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun x => (h_T004.1 x t ht).2)
    _ = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) +
        2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t)) := by
          rw [integral_add (hA.const_mul 2) (hS.const_mul 2)]
          simp only [integral_const_mul]
          rw [integral_finsetSum Finset.univ (fun j _ => hJ j)]

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

namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ t : ℝ, 0 < t → ContDiff ℝ ∞ (fun x => dt u x t) ∧ ContDiff ℝ ∞ (fun x => u x t) ∧ ∀ j : Fin n, ContDiff ℝ ∞ (fun x => du u j x t)" := by
  intro t ht
  have hopen : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hslice : ContDiff ℝ ∞ (fun x => u x t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (h_H002.contDiffAt (hopen.mem_nhds ht)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  have hdt : ContDiff ℝ ∞ (fun x => dt u x t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have H : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (u y) t) x :=
      (h_H002.contDiffAt (hopen.mem_nhds ht)).fderiv contDiffAt_const (by simp)
    change ContDiffAt ℝ ∞ (fun y => fderiv ℝ (u y) t 1) x
    exact H.clm_apply contDiffAt_const
  refine ⟨hdt, hslice, ?_⟩
  intro j
  exact (hslice.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ)),\n(∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) →\n∀ (y : EuclideanSpace ℝ {i : Fin n // i ≠ j}) (s : ℝ),\ne.symm (y,s) = e.symm (y,0) + s • EuclideanSpace.single j 1" := by
  intro j e he y s
  have coord (p : (EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ) :
      (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => (e.symm p) i.val), (e.symm p) j) = p := by
    rw [← he, e.apply_symm_apply]
  have hj (p : (EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ) :
      (e.symm p) j = p.2 := congrArg Prod.snd (coord p)
  have hi (p : (EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ) (i : {i : Fin n // i ≠ j}) :
      (e.symm p) i.val = p.1 i := congrArg (fun z => z.1 i) (coord p)
  ext i
  by_cases h : i = j
  · subst i
    simp [hj, EuclideanSpace.single_apply]
  · simp [hi (y,s) ⟨i,h⟩, hi (y,0) ⟨i,h⟩, EuclideanSpace.single_apply, h, Ne.symm h]

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ (j : Fin n), ContDiff ℝ ∞ (flux u j t) ∧ ∀ x : Space n,\ndx (flux u j t) j x = inner ℝ (dut u j x t) (du u j x t) + inner ℝ (dt u x t) (duu u j x t)" := by
  intro t ht j
  obtain ⟨hdt, hu, hdu⟩ := (@yui_aux_0001 n m u q h_H001 h_H002 h_T003 h_T006) t ht
  refine ⟨hdt.inner ℝ (hdu j), ?_⟩
  intro x
  have hd := hdt.differentiable (by simp) x
  have he := (hdu j).differentiable (by simp) x
  unfold dx flux dut duu
  rw [(hd.hasFDerivAt.inner ℝ he.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
  rw [add_comm]
  rfl

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (a v : Space n) (s : ℝ), HasDerivAt (fun r : ℝ => a + r • v) v s" := by
  intro a v s
  simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const v).const_add a

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ)),\n(∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) →\n∀ (f : Space n → ℝ), Differentiable ℝ f →\n∀ (y : EuclideanSpace ℝ {i : Fin n // i ≠ j}) (s : ℝ),\nHasDerivAt (fun r => f (e.symm (y,r))) (dx f j (e.symm (y,s))) s" := by
  intro j e he f hf y s
  have ha := (@yui_aux_0002 n m u q h_H001 h_H002 h_T003 h_T006) j e he y
  have hline : HasDerivAt (fun r : ℝ => e.symm (y,r)) (EuclideanSpace.single j 1) s := by
    rw [show (fun r : ℝ => e.symm (y,r)) = (fun r => e.symm (y,0) + r • EuclideanSpace.single j 1) from funext ha]
    exact (@yui_aux_0004 n m u q h_H001 h_H002 h_T003 h_T006) _ _ s
  exact (hf (e.symm (y,s))).hasFDerivAt.comp_hasDerivAt s hline

theorem yui_aux_0006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ)),\n(∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) →\n∀ (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ),\nDifferentiable ℝ f → Continuous (fun x => dx f j x) → 0 < R → C ⊆ openBox (n := n) R →\n(∀ x ∉ C, f x = 0) →\n∀ y : EuclideanSpace ℝ {i : Fin n // i ≠ j},\n(∫ s in Set.Icc (-R) R, dx f j (e.symm (y,s))) = 0" := by
  intro j e he f C R hf hd hR hC hz y
  have ha := (@yui_aux_0002 n m u q h_H001 h_H002 h_T003 h_T006) j e he y
  have hc : Continuous (fun s : ℝ => e.symm (y,s)) := by
    rw [show (fun s : ℝ => e.symm (y,s)) = (fun s => e.symm (y,0) + s • EuclideanSpace.single j 1) from funext ha]
    fun_prop
  have hder := (@yui_aux_0005 n m u q h_H001 h_H002 h_T003 h_T006) j e he f hf y
  have hj (s : ℝ) : (e.symm (y,s)) j = s := by
    exact congrArg Prod.snd ((he (e.symm (y,s))).symm.trans (e.apply_symm_apply (y,s)))
  have hend (s : ℝ) (hs : s = -R ∨ s = R) : f (e.symm (y,s)) = 0 := by
    apply hz
    intro hmem
    have hbounds := hC hmem j
    rw [hj] at hbounds
    rcases hs with hs | hs
    · rw [hs] at hbounds
      exact (lt_irrefl (-R)) hbounds.1
    · rw [hs] at hbounds
      exact (lt_irrefl R) hbounds.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -R) (b := R) (fun s _ => hder s) ((hd.comp hc).intervalIntegrable _ _)
  rw [hend R (Or.inr rfl), hend (-R) (Or.inl rfl), sub_self] at hFTC
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  exact hFTC

theorem yui_aux_0007 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ),\nsectionGood (fun x => dx f j x) C R →\nIntegrable (fun x => dx f j x) (volume.restrict (box (n := n) R))" := by
  intro j f C R hdgood
  have hi : IntegrableOn (fun x : Space n => dx f j x) (box (n := n) R) volume :=
    hdgood.2.2.2.integrableOn
  exact hi

theorem yui_aux_0008 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ),\n0 < R → C ⊆ openBox (n := n) R → Differentiable ℝ f →\nsectionGood f C R → sectionGood (fun x => dx f j x) C R →\n(∫ x, dx f j x) = 0" := by
  intro j f C R hR hC hf hgood hdgood
  obtain ⟨e, he, hmp⟩ := h_T006 j
  let Y := EuclideanSpace ℝ {i : Fin n // i ≠ j}
  let Qother : Set Y := {y | ∀ i, y i ∈ Set.Icc (-R) R}
  let P : Set (Y × ℝ) := Qother ×ˢ Set.Icc (-R) R
  have hebox : e ⁻¹' P = box (n := n) R := by
    ext x
    change e x ∈ P ↔ ∀ i, x i ∈ Set.Icc (-R) R
    rw [he]
    change ((∀ i : {i : Fin n // i ≠ j}, x i.val ∈ Set.Icc (-R) R) ∧ x j ∈ Set.Icc (-R) R) ↔ _
    constructor
    · rintro ⟨hother,hj⟩ i
      by_cases hi : i = j
      · simpa only [hi] using hj
      · exact hother ⟨i,hi⟩
    · intro hx
      exact ⟨fun i => hx i.val, hx j⟩
  have hmpR : MeasurePreserving e (volume.restrict (box (n := n) R))
      ((volume : Measure Y).prod volume |>.restrict P) := by
    rw [← hebox]
    exact hmp.restrict_preimage_emb e.measurableEmbedding P
  let w : Y × ℝ → ℝ := fun p => dx f j (e.symm p)
  have hw : IntegrableOn w P ((volume : Measure Y).prod volume) := by
    apply (hmpR.integrable_comp_emb e.measurableEmbedding).mp
    simpa only [Function.comp_def, w, e.symm_apply_apply] using ((@yui_aux_0007 n m u q h_H001 h_H002 h_T003 h_T006) j f C R hdgood)
  have hchange : (∫ x in box (n := n) R, dx f j x) =
      ∫ p in P, w p ∂((volume : Measure Y).prod volume) := by
    simpa only [w, e.symm_apply_apply] using hmpR.integral_comp' w
  have hslices := (@yui_aux_0006 n m u q h_H001 h_H002 h_T003 h_T006)
    j e he f C R hf hdgood.1 hR hC hgood.2.2.1
  have hbox : (∫ x in box (n := n) R, dx f j x) = 0 := by
    rw [hchange, setIntegral_prod w hw]
    change (∫ y in Qother, ∫ s in Set.Icc (-R) R, dx f j (e.symm (y,s))) = 0
    simp only [hslices, integral_zero]
  have hCbox : C ⊆ box (n := n) R := by
    intro x hx i
    exact ⟨(hC hx i).1.le, (hC hx i).2.le⟩
  have hextend : (∫ x in box (n := n) R, dx f j x) = ∫ x, dx f j x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hdgood.2.2.1 x (fun hc => hx (hCbox hc)))
  exact hextend.symm.trans hbox

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) ∧ (∫ x, inner ℝ (du u j x t) (dut u j x t)) = -(∫ x, inner ℝ (dt u x t) (duu u j x t)) := by
  intro t ht j
  obtain ⟨C, R, hcompact, hR, hC, hconst, hvol, hfinite, hiter, hgood⟩ := h_T003.1 t ht
  have htI : t ∈ Set.Ioo (t / 2) (3 * t / 2) := ⟨by linarith, by linarith⟩
  obtain ⟨hg, hA, hB, hd⟩ := (hgood t htI).2.2.2 j
  obtain ⟨hsmooth, hproduct⟩ :=
    (@yui_aux_0003 n m u q h_H001 h_H002 h_T003 h_T006) t ht j
  have hzero : (∫ x, dx (flux u j t) j x) = 0 :=
    (@yui_aux_0008 n m u q h_H001 h_H002 h_T003 h_T006)
      j (flux u j t) C R hR hC (hsmooth.differentiable (by simp)) hg hd
  have hsym : (fun x => inner ℝ (du u j x t) (dut u j x t)) =
      (fun x => inner ℝ (dut u j x t) (du u j x t)) :=
    funext fun x => real_inner_comm _ _
  have hAI : Integrable (fun x => inner ℝ (dut u j x t) (du u j x t)) := hA.2.2.2
  have hBI : Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) := hB.2.2.2
  refine ⟨?_, hBI, ?_⟩
  · rw [hsym]
    exact hAI
  · rw [hsym]
    have hsum : (∫ x, dx (flux u j t) j x) =
        (∫ x, inner ℝ (dut u j x t) (du u j x t)) +
        (∫ x, inner ℝ (dt u x t) (duu u j x t)) := by
      calc
        (∫ x, dx (flux u j t) j x) =
            ∫ x, inner ℝ (dut u j x t) (du u j x t) +
              inner ℝ (dt u x t) (duu u j x t) :=
          integral_congr_ae (Filter.Eventually.of_forall hproduct)
        _ = _ := integral_add hAI hBI
    linarith

theorem T008 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T002 : ∀ (x : Space n) (t : ℝ), 0 < t → (inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) ∧ inner ℝ (u x t) (dtt u x t) = -(‖dt u x t‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u x t) (duu u j x t) = -(‖du u j x t‖ ^ 2)) ∧ (∀ a : ℝ, dtt u x t - lap u x t = a • u x t → a = (∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) ∧ dtt u x t - lap u x t = ((∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) • u x t) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T005 : ∀ t : ℝ, 0 < t → (∀ x : Space n, densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => densityT u x t) ∧ Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) ∧ (∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t))) ∧ HasDerivAt (energy u) (∫ x, densityT u x t) t ∧ deriv (energy u) t = (∫ x, densityT u x t) ∧ deriv (energy u) t = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) + 2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t))) (h_T007 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) ∧ (∫ x, inner ℝ (du u j x t) (dut u j x t)) = -(∫ x, inner ℝ (dt u x t) (duu u j x t))) :
    ∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0 := by
  intro t ht
  rcases h_T005 t ht with ⟨hpoint, hint, ha, hc, hderiv, hvalue, hformula⟩
  refine ⟨h_T003.2 t ht, hderiv.differentiableAt, ?_⟩
  have hb : ∀ j : Fin n, Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) :=
    fun j => (h_T007 t ht j).2.1
  have hsum : Integrable (fun x => ∑ j : Fin n,
      inner ℝ (dt u x t) (duu u j x t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hb j)
  have hlin : (∫ x, inner ℝ (dt u x t) (dtt u x t) -
      ∑ j : Fin n, inner ℝ (dt u x t) (duu u j x t)) =
      (∫ x, inner ℝ (dt u x t) (dtt u x t)) -
      ∑ j : Fin n, (∫ x, inner ℝ (dt u x t) (duu u j x t)) := by
    rw [integral_sub ha hsum, integral_finsetSum Finset.univ (fun j _ => hb j)]
  have hz : (∫ x, inner ℝ (dt u x t) (dtt u x t) -
      ∑ j : Fin n, inner ℝ (dt u x t) (duu u j x t)) = 0 := by
    have hp : ∀ x : Space n, inner ℝ (dt u x t) (dtt u x t) -
        ∑ j : Fin n, inner ℝ (dt u x t) (duu u j x t) = 0 := by
      intro x
      have hzero := (h_T002 x t ht).1.2
      simpa only [lap, inner_sub_right, inner_sum] using hzero
    simp_rw [hp]
    simp
  rw [hformula]
  simp_rw [(h_T007 t ht _).2.2]
  rw [Finset.sum_neg_distrib]
  have hcancel := hlin.symm.trans hz
  linarith

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

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) :
    (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧ (∀ s t : ℝ, 0 < s → 0 < t → energy u t = energy u s) := by
  have h_T001 : ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0 := @T001 n m u q h_H002 h_H004 h_H005
  have h_T002 : ∀ (x : Space n) (t : ℝ), 0 < t → (inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) ∧ inner ℝ (u x t) (dtt u x t) = -(‖dt u x t‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u x t) (duu u j x t) = -(‖du u j x t‖ ^ 2)) ∧ (∀ a : ℝ, dtt u x t - lap u x t = a • u x t → a = (∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) ∧ dtt u x t - lap u x t = ((∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) • u x t := @T002 n m u q h_H002 h_H004 h_H005 h_T001
  have h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t)) := @T003 n m u q h_H001 h_H002 h_H006
  have h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n) := @T004 n m u q h_H002
  have h_T005 : ∀ t : ℝ, 0 < t → (∀ x : Space n, densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => densityT u x t) ∧ Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) ∧ (∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t))) ∧ HasDerivAt (energy u) (∫ x, densityT u x t) t ∧ deriv (energy u) t = (∫ x, densityT u x t) ∧ deriv (energy u) t = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) + 2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t)) := @T005 n m u q h_H002 h_T003 h_T004
  have h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ)) := @T006 n m u q h_H001
  have h_T007 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) ∧ (∫ x, inner ℝ (du u j x t) (dut u j x t)) = -(∫ x, inner ℝ (dt u x t) (duu u j x t)) := @T007 n m u q h_H001 h_H002 h_T003 h_T006
  have h_T008 : ∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0 := @T008 n m u q h_T002 h_T003 h_T005 h_T007
  have h_T009 : (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧ (∀ s t : ℝ, 0 < s → 0 < t → energy u t = energy u s) := @T009 n m u q h_T008
  exact h_T009

#check @P
#print axioms P

end Translation
