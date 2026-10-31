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
theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
  ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.density u p.1 p.2) (WaveMap.positive n) ∧
  ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) ∧
  ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R η B : ℝ),
    IsCompact C ∧ 0 < R ∧ 0 < η ∧ 0 ≤ B ∧
    C ⊆ WaveMap.openBox n R ∧ IsCompact (WaveMap.box n R) ∧
    volume (WaveMap.box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
    volume (WaveMap.box n R) ≠ ⊤ ∧
    Icc (t0 - η) (t0 + η) ⊆ WaveMap.timeInterior t0 ∧
    (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
    (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
      r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0) ∧
    (∀ r ∈ WaveMap.timeInterior t0, ∀ (j : Fin n) (f : WaveMap.Space n → ℝ),
      f ∈ WaveMap.terms u r j →
      Continuous f ∧ Function.support f ⊆ C ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ WaveMap.box n R, |f x| ≤ K) ∧
      Measurable f ∧ Integrable f) ∧
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T007 : ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) ∧ HasCompactSupport (WaveMap.flux u j t) ∧
  (∀ x : WaveMap.Space n, WaveMap.spatial (WaveMap.flux u j t) j x =
    WaveMap.gradientProduct u j t x + WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.spatial (WaveMap.flux u j t) j) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t)) : yui_aux_type% "∀ (k : ℕ) (j : Fin (k+1)) (R : ℝ),\nlet e : (ℝ × (Fin k → ℝ)) ≃ᵐ WaveMap.Space (k+1) :=\n  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm.trans\n    (MeasurableEquiv.toLp 2 (Fin (k+1) → ℝ))\ne ⁻¹' WaveMap.box (k+1) R = Icc (-R) R ×ˢ (Set.univ.pi (fun _ : Fin k => Icc (-R) R))" := by
  intro k j R e
  ext p
  rcases p with ⟨r,y⟩
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_const]
  change (∀ i, Fin.insertNth (α := fun _ => ℝ) j r y i ∈ Icc (-R) R) ↔
    (r ∈ Icc (-R) R ∧ ∀ a, y a ∈ Icc (-R) R)
  simp only [j.forall_iff_succAbove, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
#check @checked
#print axioms checked
end YuiAuxiliary
