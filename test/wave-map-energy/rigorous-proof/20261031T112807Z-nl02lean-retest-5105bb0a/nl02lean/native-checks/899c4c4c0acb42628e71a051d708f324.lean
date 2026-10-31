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
theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T002 : ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R : ℝ),
  IsCompact C ∧ 0 < R ∧ C ⊆ WaveMap.openBox n R ∧
  (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
  (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
    r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0)) : yui_aux_type% "∀ (C : Set (WaveMap.Space n)) (t0 : ℝ), IsCompact C → (∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) → ∀ r ∈ WaveMap.timeInterior t0, ∀ (j : Fin n) (f : WaveMap.Space n → ℝ), f ∈ WaveMap.terms u r j → Function.support f ⊆ C" := by
  classical
  have zeroD : ∀ (C : Set (WaveMap.Space n)) (t0 : ℝ), IsCompact C → ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WaveMap.Space n × ℝ → F) (c : F), (∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, f (x,r) = c) → (∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, deriv (fun s => f (x,s)) r = 0) ∧ (∀ j : Fin n, ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.spatial (fun y => f (y,r)) j x = 0) := by
    intro C t0 hc F _ _ f c hf
    constructor
    · intro x hx r hr
      have hh : (fun s => f (x,s)) =ᶠ[nhds r] (fun _ => c) :=
        Filter.Eventually.mono (isOpen_Ioo.mem_nhds hr) (fun s hs => hf x hx s hs)
      simpa using hh.deriv_eq
    · intro j x hx r hr
      have hh : (fun y => f (y,r)) =ᶠ[nhds x] (fun _ => c) :=
        Filter.Eventually.mono (hc.isClosed.isOpen_compl.mem_nhds hx) (fun y hy => hf y hy r hr)
      simp [WaveMap.spatial, hh.fderiv_eq]

  have termsupport : ∀ (C : Set (WaveMap.Space n)) (t0 : ℝ), IsCompact C → (∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) → ∀ r ∈ WaveMap.timeInterior t0, ∀ (j : Fin n) (f : WaveMap.Space n → ℝ), f ∈ WaveMap.terms u r j → Function.support f ⊆ C := by
    intro C t0 hc hu
    have hu' : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, u (x,r) = q := by
      intro x hx r hr
      exact hu x hx r ⟨hr.1.le,hr.2.le⟩
    have zu := zeroD C t0 hc _ u q hu'
    have zut : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.ut u x r = 0 := zu.1
    have zux : ∀ j, ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.ux u j x r = 0 := zu.2
    have ze : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.density u x r = 0 := by
      intro x hx r hr
      simp [WaveMap.density, zut x hx r hr, fun j => zux j x hx r hr]
    have zet : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.densityTime u x r = 0 :=
      (zeroD C t0 hc ℝ (fun p => WaveMap.density u p.1 p.2) 0 ze).1
    have zf (j : Fin n) : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.flux u j r x = 0 := by
      intro x hx r hr
      simp [WaveMap.flux, zut x hx r hr]
    have zdf (j : Fin n) : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.spatial (WaveMap.flux u j r) j x = 0 :=
      (zeroD C t0 hc ℝ (fun p => WaveMap.flux u j p.2 p.1) 0 (zf j)).2 j
    intro r hr j f hf x hx
    by_contra hxc
    have heq : f x = 0 := by
      simp only [WaveMap.terms, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ze x hxc r hr
      · exact zet x hxc r hr
      · simp [WaveMap.kineticProduct, zut x hxc r hr]
      · simp [WaveMap.gradientProduct, zux j x hxc r hr]
      · simp [WaveMap.laplaceProduct, zut x hxc r hr]
      · exact zf j x hxc r hr
      · exact zdf j x hxc r hr
    exact hx heq

  exact termsupport
#check @checked
#print axioms checked
end YuiAuxiliary
