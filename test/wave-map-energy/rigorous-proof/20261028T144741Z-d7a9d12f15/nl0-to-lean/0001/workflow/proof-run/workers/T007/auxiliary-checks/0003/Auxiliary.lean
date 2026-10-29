import Mathlib
open MeasureTheory Set Filter
open scoped ContDiff
noncomputable abbrev WSpace (n : ℕ) := Fin n → ℝ
noncomputable abbrev WTarget (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def wDx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n → F) (j : Fin n) (x : WSpace n) : F := fderiv ℝ f x (Pi.single j 1)
noncomputable def wT {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (p : WSpace n × ℝ) : F := deriv (fun r => f (p.1,r)) p.2
noncomputable def wX {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (j : Fin n) (p : WSpace n × ℝ) : F := wDx (fun x => f (x,p.2)) j p.1
noncomputable def wLap {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : WTarget m := ∑ j : Fin n, wX (wX u j) j p
noncomputable def wDensity {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : ℝ := ‖wT u p‖^2 + ∑ j : Fin n, ‖wX u j p‖^2
noncomputable def wEnergy {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (t : ℝ) : ℝ := ∫ x : WSpace n, wDensity u (x,t)
noncomputable def wA {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : ℝ := inner ℝ (wT u p) (wT (wT u) p)
noncomputable def wB {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (j : Fin n) (p : WSpace n × ℝ) : ℝ := inner ℝ (wX u j p) (wX (wT u) j p)
noncomputable def wC {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (j : Fin n) (p : WSpace n × ℝ) : ℝ := inner ℝ (wT u p) (wX (wX u j) j p)
noncomputable def wG {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (j : Fin n) (p : WSpace n × ℝ) : ℝ := inner ℝ (wT u p) (wX u j p)
def wDomain (n : ℕ) : Set (WSpace n × ℝ) := {p | 0 < p.2}
def wBox (n : ℕ) (R : ℝ) : Set (WSpace n) := Set.Icc (fun _ => -R) (fun _ => R)
def wOpenBox (n : ℕ) (R : ℝ) : Set (WSpace n) := {x | ∀ j, -R < x j ∧ x j < R}
noncomputable def wTerms {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (r : ℝ) : Set (WSpace n → ℝ) := {f | f = (fun x => wDensity u (x,r)) ∨ f = (fun x => wT (wDensity u) (x,r)) ∨ f = (fun x => wA u (x,r)) ∨ ∃ j : Fin n, f = (fun x => wB u j (x,r)) ∨ f = (fun x => wC u j (x,r)) ∨ f = (fun x => wG u j (x,r)) ∨ f = (fun x => wX (wG u j) j (x,r))}
def wNice {n : ℕ} (C : Set (WSpace n)) (f : WSpace n → ℝ) : Prop := Continuous f ∧ (∀ x, x ∉ C → f x = 0) ∧ Integrable f
noncomputable def wGeometry {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (t : ℝ) (C : Set (WSpace n)) (R : ℝ) : Prop := IsCompact C ∧ 0 < R ∧ C ⊆ wOpenBox n R ∧ (∀ x r, x ∉ C → r ∈ Set.Icc (t/2) (3*t/2) → u (x,r) = q) ∧ (∀ (k : ℕ) x r, 0 < k → x ∉ C → r ∈ Set.Ioo (t/2) (3*t/2) → iteratedFDeriv ℝ k u (x,r) = 0) ∧ volume (wBox n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (wBox n R) < ⊤
noncomputable def wLocal {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (t : ℝ) (C : Set (WSpace n)) (R B : ℝ) : Prop := wGeometry u q t C R ∧ 0 ≤ B ∧ (∀ r ∈ Set.Ioo (t/2) (3*t/2), ∀ f ∈ wTerms u r, wNice C f) ∧ (∀ x ∈ wBox n R, ∀ r ∈ Set.Icc (3*t/4) (5*t/4), |wT (wDensity u) (x,r)| ≤ B)

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T003 : ContDiffOn ℝ ∞ (wDensity u) (wDomain n) ∧ ContinuousOn (wT (wDensity u)) (wDomain n) ∧ ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) ∧ (∀ j : Fin n, wT (wX u j) (x,t) = wX (wT u) j (x,t)) ∧ wT (wDensity u) (x,t) = 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) (h_T006 : ∀ t : ℝ, 0 < t → ∀ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B → Integrable ((wBox n R).indicator (fun _ => B)) ∧ ∀ h : ℝ, 0 < |h| → |h| < t/4 → ∀ x : WSpace n, |(wDensity u (x,t+h) - wDensity u (x,t))/h| ≤ (wBox n R).indicator (fun _ => B) x) : yui_aux_type% "∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), h ≠ 0" := by
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact hh
#check @checked
#print axioms checked
end YuiAuxiliary
