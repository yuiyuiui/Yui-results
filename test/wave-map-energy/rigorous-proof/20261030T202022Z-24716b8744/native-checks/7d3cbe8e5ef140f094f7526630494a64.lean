import Mathlib
open scoped ContDiff Topology BigOperators
open Set MeasureTheory
noncomputable section
namespace WaveMap
abbrev V (n : ℕ) := Fin n → ℝ
abbrev W (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (V n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (V n) := Set.Icc (fun _ => -R) (fun _ => R)
def innerBox (n : ℕ) (R : ℝ) : Set (V n) := {x | ∀ j, -R < x j ∧ x j < R}
def ut {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => u (x,s)) t
def utt {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => ut u x s) t
def ux {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => u (y,t)) x (Pi.single j 1)
def uxx {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ux u j y t) x (Pi.single j 1)
def uxt {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ut u y t) x (Pi.single j 1)
def lap {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  ∑ j, uxx u j x t
def e {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def et {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  deriv (fun s => e u x s) t
def A {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def B {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ux u j x t) (uxt u j x t)
def T {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def g {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def dg {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y => g u j y t) x (Pi.single j 1)
def energy {n m : ℕ} (u : V n × ℝ → W m) (t : ℝ) : ℝ :=
  ∫ x, e u x t
def fields {n m : ℕ} (u : V n × ℝ → W m) : Set ((V n × ℝ) → ℝ) :=
  {f | f = (fun p => e u p.1 p.2) ∨ f = (fun p => et u p.1 p.2) ∨
    f = (fun p => A u p.1 p.2) ∨
    (∃ j, f = (fun p => B u j p.1 p.2)) ∨
    (∃ j, f = (fun p => T u j p.1 p.2)) ∨
    (∃ j, f = (fun p => g u j p.1 p.2)) ∨
    (∃ j, f = (fun p => dg u j p.1 p.2))}
end WaveMap
open WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x t, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x t, 0 < t → ∃ a : ℝ, utt u x t - lap u x t = a • u (x,t)) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]\n  (f : E → W m) (s : Set E), IsOpen s →\n  (∀ y ∈ s, ContDiffAt ℝ 2 f y) →\n  (∀ y ∈ s, ‖f y‖ = 1) →\n  ∀ z ∈ s, ∀ v : E,\n    inner ℝ (f z) (fderiv ℝ f z v) = 0 ∧\n    inner ℝ (f z) (fderiv ℝ (fun y => fderiv ℝ f y v) z v) =\n      -(‖fderiv ℝ f z v‖ ^ 2)" := by
  intro E _ _ f s hs hf hn
  have first : ∀ z ∈ s, ∀ v : E, inner ℝ (f z) (fderiv ℝ f z v) = 0 := by
    intro z hz v
    have heq : (fun y => inner ℝ (f y) (f y)) =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
      filter_upwards [hs.mem_nhds hz] with y hy
      rw [real_inner_self_eq_norm_sq, hn y hy]
      norm_num
    have hd := ((hasFDerivAt_const z (1 : ℝ)).congr_of_eventuallyEq heq).fderiv
    have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
    rw [fderiv_inner_apply ℝ (hf z hz |>.differentiableAt (by norm_num))
      (hf z hz |>.differentiableAt (by norm_num)) v] at he
    simp only [ContinuousLinearMap.zero_apply, real_inner_comm (fderiv ℝ f z v) (f z)] at he
    linarith
  intro z hz v
  refine ⟨first z hz v, ?_⟩
  have hdf : DifferentiableAt ℝ f z := (hf z hz).differentiableAt (by norm_num)
  have hcd : ContDiffAt ℝ 1 (fun y => fderiv ℝ f y v) z :=
    ((hf z hz).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have heq : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hz] with y hy
    exact first y hy v
  have hd := ((hasFDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq heq).fderiv
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
  rw [fderiv_inner_apply ℝ hdf hcd.differentiableAt_one v] at he
  simp only [ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at he
  linarith
#check @checked
#print axioms checked
end YuiAuxiliary
