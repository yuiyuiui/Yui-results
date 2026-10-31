import Mathlib
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
noncomputable section
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def positive (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Icc (-R) R}
def openBox (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Ioo (-R) R}
def timeInterval (t : ℝ) : Set ℝ := Icc (t / 2) (3 * t / 2)
def timeInterior (t : ℝ) : Set ℝ := Ioo (t / 2) (3 * t / 2)
def spatial {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (PiLp.single 2 j 1)
def ut {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => u (x, r)) t
def utt {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (ut u x) t
def ux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => u (y, t)) j x
def uxx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ux u j y t) j x
def utx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ut u y t) j x
def laplace {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, uxx u j x t
def density {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def densityTime {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
def energy {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
def kineticProduct {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def gradientProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ux u j x t) (utx u j x t)
def laplaceProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def flux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def terms {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (j : Fin n) : List (Space n → ℝ) :=
  [fun x => density u x t, fun x => densityTime u x t, kineticProduct u t,
   gradientProduct u j t, laplaceProduct u j t, flux u j t, spatial (flux u j t) j]
def quotient {n m : ℕ} (u : Space n × ℝ → Space m) (t h : ℝ) (x : Space n) : ℝ :=
  (density u x (t + h) - density u x t) / h
def bound (n : ℕ) (R B : ℝ) : Space n → ℝ :=
  (box n R).indicator (fun _ => B)
end WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ∃ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t)) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]\n    (f : E → WaveMap.Space m) (s : Set E),\n    IsOpen s → ContDiffOn ℝ (∞ : ℕ∞ω) f s →\n    (∀ y ∈ s, ‖f y‖ = 1) →\n    ∀ x ∈ s, ∀ v : E,\n      inner ℝ (f x) (fderiv ℝ f x v) = 0 ∧\n      inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ f y v) x v) =\n        -(‖fderiv ℝ f x v‖ ^ 2)" := by
  intro E _ _ f s hs hf hn
  have hd : ∀ x ∈ s, DifferentiableAt ℝ f x := by
    intro x hx
    exact (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hfirst : ∀ x ∈ s, ∀ v : E, inner ℝ (f x) (fderiv ℝ f x v) = 0 := by
    intro x hx v
    have he : (fun y => inner ℝ (f y) (f y)) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      simp [real_inner_self_eq_norm_sq, hn y hy]
    have hz : fderiv ℝ (fun y => inner ℝ (f y) (f y)) x v = 0 := by
      rw [he.fderiv_eq]
      simp
    rw [fderiv_inner_apply ℝ (hd x hx) (hd x hx), real_inner_comm (fderiv ℝ f x v) (f x)] at hz
    linarith
  intro x hx v
  refine ⟨hfirst x hx v, ?_⟩
  have hdf : ContDiffOn ℝ (1 : ℕ∞ω) (fun y => fderiv ℝ f y v) s :=
    (hf.fderiv_of_isOpen (m := 1) hs (by decide)).clm_apply contDiffOn_const
  have hdd : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    (hdf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hfirst y hy v
  have hz : fderiv ℝ (fun y => inner ℝ (f y) (fderiv ℝ f y v)) x v = 0 := by
    rw [he.fderiv_eq]
    simp
  rw [fderiv_inner_apply ℝ (hd x hx) hdd, real_inner_self_eq_norm_sq] at hz
  linarith
#check @checked
#print axioms checked
end YuiAuxiliary
